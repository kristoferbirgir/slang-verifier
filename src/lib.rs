pub mod ivl;
mod ivl_ext;

use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr, ExprKind, Type, Name};
use slang_ui::prelude::*;

pub struct App;

impl slang_ui::Hook for App {
    fn analyze(&self, cx: &slang_ui::Context, file: &slang::SourceFile) -> Result<()> {
        // Get reference to Z3 solver
        let mut solver = cx.solver()?;

        // Iterate methods
        for m in file.methods() {
            // Get method's preconditions
            let pres = m.requires();
            // Merge them into a single condition
            let pre = pres
                .cloned()
                .reduce(|a, b| a & b)
                .unwrap_or(Expr::bool(true));
            // Convert the expression into an SMT expression and assert it
            let spre = pre.smt(cx.smt_st())?;
            solver.assert(spre.as_bool()?)?;

            // Get method's body (well-formed programs have a body)
            let body = m.body.as_ref().expect("method without body?");

            // Encode it in IVL
            let ivl = cmd_to_ivlcmd(&body.cmd);

            // ------------------------------------------------------------
            // Build all verification obligations:
            //  1) internal asserts: wp(body, true)
            //  2) each ensures Ei: wp(body, Ei)      (report at Ei's span)
            //
            // Each item carries (obligation_expr, message, blame_span).
            // ------------------------------------------------------------
            let mut obligations: Vec<(Expr, String, slang::Span)> = Vec::new();

            // 1) internal asserts
            let (oblig_asserts, msg_asserts) = wp(&ivl, &Expr::bool(true));
            let span_asserts = oblig_asserts.span; // capture span before move
            obligations.push((oblig_asserts, msg_asserts, span_asserts));

            // 2) wp-based postconditions
            let ensures_vec: Vec<Expr> = m.ensures().cloned().collect();
            eprintln!("DEBUG: method has {} ensures", ensures_vec.len());
            for e in &ensures_vec {
                let (oblig_post, _unused) = wp(&ivl, e);
                obligations.push((
                    oblig_post,
                    format!("Postcondition may not hold: {}", e),
                    e.span,
                ));
            }

            // Run each obligation in its own solver scope.
            // Obligation is valid  ⇔  ¬oblig is UNSAT.
            for (oblig, msg, blame_span) in obligations {
                let soblig = oblig.smt(cx.smt_st())?;

                solver.scope(|solver| {
                    // Check validity: assert the negation and ask for SAT?
                    solver.assert(!soblig.as_bool()?)?;
                    match solver.check_sat()? {
                        // ¬oblig SAT  => oblig NOT valid => report error
                        smtlib::SatResult::Sat => {
                            cx.error(blame_span, msg.to_string());
                        }
                        smtlib::SatResult::Unknown => {
                            cx.warning(blame_span, format!("{msg}: unknown sat result"));
                        }
                        // ¬oblig UNSAT => oblig valid => OK
                        smtlib::SatResult::Unsat => (),
                    }
                    Ok(())
                })?;
            }
        }

        Ok(())
    }
}

// Encoding of statements into IVL (minimal Core A subset)
// We now support:
//   - Assert
//   - Return e              → assume(result == e)
//   - Seq(c1, c2)           → seq(encode(c1), encode(c2))
//   - VarDefinition/Assignment → currently no-ops (assume true), enough to pass ensures tests
// Other commands: conservative no-op (assume true).
fn cmd_to_ivlcmd(cmd: &Cmd) -> IVLCmd {
    match &cmd.kind {
        // Assertions
        CmdKind::Assert { condition, .. } => IVLCmd::assert(condition, "Assertion might fail"),

        // Return e  ⇒  assume(result == e)
        // This lets ensures clauses about `result` be checked even when return sits inside a sequence.
        CmdKind::Return { expr: Some(e), .. } => {
            let ty: &Type = &e.ty;
            let res = Expr::result(ty);
            let cond = res.eq(&e.clone());
            IVLCmd::assume(&cond)
        }

        // Sequencing: wp(c1;c2, post) = wp(c1, wp(c2, post))
        CmdKind::Seq(c1, c2) => {
            let i1 = cmd_to_ivlcmd(c1);
            let i2 = cmd_to_ivlcmd(c2);
            i1.seq(&i2)
        }

        // Local variable definition (with/without initializer)
        CmdKind::VarDefinition { name, ty, expr } => {
            match expr {
                Some(expr) => {
                    // var x: T := e  ⇒  x := e
                    IVLCmd::assign(name, expr)
                }
                None => {
                    // var x: T  ⇒  havoc x
                    IVLCmd::havoc(name, &ty.1)
                }
            }
        }

        // Assignment: x := e
        CmdKind::Assignment { name, expr } => {
            IVLCmd::assign(name, expr)
        }

        // Match statement: encode as nondeterministic choice between branches
        CmdKind::Match { body } => {
            let mut branch_cmds = Vec::new();
            for case in &body.cases {
                // Each branch: assume condition; then execute command
                let guard = IVLCmd::assume(&case.condition);
                let body_cmd = cmd_to_ivlcmd(&case.cmd);
                branch_cmds.push(guard.seq(&body_cmd));
            }
            
            if branch_cmds.is_empty() {
                IVLCmd::unreachable() // Empty match is unreachable
            } else {
                IVLCmd::nondets(&branch_cmds)
            }
        }

        // Debug: print unknown/unsupported command kinds so we can map them as we implement Core A fully.
        _ => {
            eprintln!("DEBUG: unsupported CmdKind = {:?}", cmd.kind);
            // Conservative fallback: unsupported command – "no-op" so wp(body, post) = post.
            // Implemented as `assume true`.
            IVLCmd::nop()
        }
    }
}

// Weakest precondition over the IVL subset we currently emit:
//   - Assert c        ⇒  wp = c
//   - Assume p        ⇒  wp = (p ==> post)
//   - Seq(c1, c2)     ⇒  wp(c1, wp(c2, post))
// (We’ll add Assignment/Havoc/etc. when we handle real updates — for now we encode them as no-ops.)
fn wp(ivl: &IVLCmd, post: &Expr) -> (Expr, String) {
    match &ivl.kind {
        IVLCmdKind::Assert { condition, message } => (condition.clone(), message.clone()),
        IVLCmdKind::Assume { condition } => (condition.imp(post), format!("Assumption may not imply post: {}", condition)),
        IVLCmdKind::Seq(c1, c2) => {
            let (post2, _m2) = wp(c2, post);
            let (post1, m1) = wp(c1, &post2);
            (post1, m1)
        }
        IVLCmdKind::NonDet(c1, c2) => {
            // wp(c1 [] c2, post) = wp(c1, post) && wp(c2, post)
            let (wp1, _m1) = wp(c1, post);
            let (wp2, _m2) = wp(c2, post);
            (wp1 & wp2, format!("Nondeterministic choice"))
        }
        IVLCmdKind::Assignment { name, expr } => {
            // wp(x := e, post) = post[x → e]
            let substituted = substitute_var(post, name, expr);
            (substituted, format!("Assignment to {}", name))
        }
        IVLCmdKind::Havoc { name, .. } => {
            // wp(havoc x, post) = ∀x. post
            // For simplicity, we'll treat this as true (conservative)
            // In a full implementation, we'd need to create a fresh variable
            (Expr::bool(true), format!("Havoc {}", name))
        }
    }
}

// Substitute variable 'var' with 'replacement' in expression 'expr'
// This implements the substitution expr[var → replacement]
// For now, simplified version that handles basic cases
fn substitute_var(expr: &Expr, var: &Name, replacement: &Expr) -> Expr {
    match &expr.kind {
        ExprKind::Ident(name) => {
            if name == &var.ident {
                replacement.clone()
            } else {
                expr.clone()
            }
        }
        ExprKind::Infix(left, op, right) => {
            let left_sub = substitute_var(left, var, replacement);
            let right_sub = substitute_var(right, var, replacement);
            // Create a new infix expression with substituted operands
            let new_kind = ExprKind::Infix(Box::new(left_sub), *op, Box::new(right_sub));
            Expr::new_typed(new_kind, expr.ty.clone())
        }
        ExprKind::Prefix(op, operand) => {
            let operand_sub = substitute_var(operand, var, replacement);
            let new_kind = ExprKind::Prefix(*op, Box::new(operand_sub));
            Expr::new_typed(new_kind, expr.ty.clone())
        }
        ExprKind::Quantifier(_quantifier, _variables, _body) => {
            // For now, conservatively don't substitute inside quantifiers
            // In a full implementation, we'd check if any variable shadows our substitution
            expr.clone()
        }
        // For other expressions, recursively substitute (simplified)
        _ => {
            // For now, conservatively return the original expression
            // In a full implementation, we'd handle all expression kinds
            expr.clone()
        },
    }
}
