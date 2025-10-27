pub mod ivl;
mod ivl_ext;

use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr, Type};
use slang_ui::prelude::*;

pub struct App;

impl slang_ui::Hook for App {
    fn analyze(&self, cx: &slang_ui::Context, file: &slang::SourceFile) -> Result<()> {
        // Z3 solver
        let mut solver = cx.solver()?;

        for m in file.methods() {
            // === Preconditions ===
            let pre = m
                .requires()
                .cloned()
                .reduce(|a, b| a & b)
                .unwrap_or(Expr::bool(true));
            let spre = pre.smt(cx.smt_st())?;
            solver.assert(spre.as_bool()?)?;

            // Body (assume well-formed method has a body)
            let body = m.body.clone().expect("well-formed method should have a body");
            let cmd: &Cmd = &body.cmd;

            // Encode to IVL
            let ivl = cmd_to_ivlcmd(cmd);

            // Collect ensures once
            let ensures_vec: Vec<Expr> = m.ensures().cloned().collect();
            eprintln!("DEBUG: method has {} ensures", ensures_vec.len());

            // ------------------------------------------------------------
            // Build obligations:
            //  1) Internal asserts: wp(body, true) — blame at assert span
            //  2) For each ensures E:
            //       (a) wp(body, E)                 — blame at E.span
            //       (b) if `return r`: (result==r) ==> E — blame at E.span
            // ------------------------------------------------------------
            let mut obligations: Vec<(Expr, String, slang::Span)> = Vec::new();

            // (1) Asserts
            let (oblig_asserts, msg_asserts) = wp(&ivl, &Expr::bool(true));
            let span_asserts = oblig_asserts.span;
            obligations.push((oblig_asserts, msg_asserts, span_asserts));

            // (2a) wp-based postconditions
            for e in &ensures_vec {
                let (oblig_post, _unused) = wp(&ivl, e);
                obligations.push((
                    oblig_post,
                    format!("Postcondition may not hold: {}", e),
                    e.span, // blame at ensures line
                ));
            }

            // (2b) direct: if body is `return r`, check (result == r) ==> E
            if let CmdKind::Return { expr: Some(ret), .. } = &cmd.kind {
                let ty: &Type = &ret.ty;
                let res = Expr::result(ty);
                let ret_semantics = res.eq(&ret.clone()); // result == r
                for e in &ensures_vec {
                    let direct_valid = ret_semantics.imp(e);
                    obligations.push((
                        direct_valid,
                        format!("Postcondition may not hold (direct): {}", e),
                        e.span, // blame at ensures line
                    ));
                }
            }

            // === Discharge ===
            for (oblig, msg, blame_span) in obligations {
                let soblig = oblig.smt(cx.smt_st())?;
                solver.scope(|solver| {
                    solver.assert(!soblig.as_bool()?)?;
                    match solver.check_sat()? {
                        smtlib::SatResult::Sat => cx.error(blame_span, msg.to_string()),
                        smtlib::SatResult::Unknown => {
                            cx.warning(blame_span, format!("{msg}: unknown sat result"))
                        }
                        smtlib::SatResult::Unsat => (),
                    }
                    Ok(())
                })?;
            }
        }

        Ok(())
    }
}

// Encode a tiny IVL subset sufficient for Core A.
fn cmd_to_ivlcmd(cmd: &Cmd) -> IVLCmd {
    match &cmd.kind {
        // Core A: assert
        CmdKind::Assert { condition, .. } => IVLCmd::assert(condition, "Assert might fail!"),

        // Minimal support for `return e`: assume result == e
        CmdKind::Return { expr: Some(e), .. } => {
            let ty: &Type = &e.ty;
            let res = Expr::result(ty);
            IVLCmd::assume(&res.eq(&e.clone()))
        }

        // Fallback: unknown command -> no-op
        _ => {
            eprintln!("DEBUG: unsupported CmdKind = {:?}", cmd.kind);
            IVLCmd::nop()
        }
    }
}

// Weakest precondition for our small IVL subset:
//   Assert c      ->  c
//   Assume p      ->  p ==> post
fn wp(ivl: &IVLCmd, post: &Expr) -> (Expr, String) {
    match &ivl.kind {
        IVLCmdKind::Assert { condition, message } => (condition.clone(), message.clone()),
        IVLCmdKind::Assume { condition } => (
            condition.imp(post),
            format!("Assumption may not imply post: {}", condition),
        ),
        _ => (
            post.clone(),
            "/* unsupported IVL case: conservatively kept post */".to_string(),
        ),
    }
}
