The goal of this project is to develop an automated verification tool for *slang*, a language similar to a fragment of Viper and the languages explored throughout the first half of the course.

We start by discussing the project *Guidelines*, before going over an overview of the *slang* language. We then present the individual tasks (referred to as *Features*), and finish with a short introduction of a useful *library* that you may use in your project. 

# Guidelines
We split the task of developing a slang verifier into core features and extension features. Generally speaking, your solution should support all core features and some extension features.

We provide a number of stars for each feature to indicate a rough estimate of the required effort and difficulty.

In total, there are 27 stars. We expect you to work on the three core features, which are worth 6 stars.
To obtain a grade of (Danish/German grading scale)
- 12/1.0, you should aim for at least 20 stars;
- 10/2.0, you should aim for at least 15 stars;
- 4-7/3.0, you should aim for at least 10 stars;
- 2/4.0, you should aim for at least 6 stars.

To gain all stars for a feature, it must be fully supported in the following sense:
- The feature has been implemented in your verifier.
- Your implementation works as expected on least two (non-trivial) examples of your choice (one that should verify and one that should not verify unless stated otherwise).

We encourage you to reasonably document what you are doing in your implementation. You do not have to write a report of any kind. Please also notice that parts of the weekly assignments cover the foundations underlying the design of your verifier. You should those work on those assignments first and consult your solutions before you starting to implement a feature.

Solutions that satisfy some of the above criteria, but not all of them, will be awarded a reduced number of stars. Generally speaking, your solution must be sound but not necessarily complete. However, you should aim to be as complete as possible.

You are not allowed to share code with other groups. However, you may share examples for testing your verifier with others.


# slang
The *slang* language supports similar programming features to the ones seen in the course, but not always identical ones. *slang* features global variables, methods, functions, domains, multi-branch loops (`loop` and `for`), and conditionals (`match`). Moreover, it supports verification oriented commands and annotations such as `assume`, `assert`, `requires`, `ensures`, `invariant`, `decreases` and `modifies`. *slang* also features goto-like commands such as `break`, `continue` and `return`. 

The following example program showcases most features of *slang*:

```
global counter: Int

domain Pair {
  function pair(x: Int, y: Int): Pair
  function fst(x: Pair): Int
  function snd(x: Pair): Int

  axiom forall x: Int :: forall y: Int :: fst(pair(x,y)) == x
  axiom forall x: Int :: forall y: Int :: snd(pair(x,y)) == y
}

method swap(p: Pair): Pair
  ensures fst(result) == snd(p)
  ensures snd(result) == fst(p)
{
  var f: Int := fst(p);
  var s: Int := snd(p);

  return pair(s,f)
}

method sumn(n: Int): Int
  ensures result == n * (n + 1) / 2
{
  match {
    n == 0 => 
      return 0,
    true => 
      var res: Int;
      res := sumn(n - 1);
      return res + n
  }
}

method sumn_iter(n: Int): Int 
  requires n >= 0
  ensures result == n * (n + 1) / 2
{
  var acc: Int := 0;
  var i: Int := 0;
  loop 
    invariant i >= 0 && i <= n
    invariant acc == i * (i + 1) / 2
    invariant broke ==> i == 5 && n == 5
  {
    n == 5 => i := 5; acc := 15; break,
    i < n => 
      i := i + 1;
      acc := acc + i
  };
  return acc
}

function fib(n: Int): Int
  requires n >= 0
{
  n <= 1 ? 1 : fib(n - 1) + fib(n - 2)
}

method fib_iter(n: Int): Int
  requires n >= 2
  ensures result == fib(n)
{
  match {
    n == 0 => return 1,
    n == 1 => return 1,
  };

  var pprev: Int := 1;
  var prev: Int := 1;
  var i: Int := 1;

  for i in 1..(n + 1) 
    invariant fib(i - 1) == pprev
    invariant fib(i) == prev 
  {
      var tmp: Int;
      tmp := pprev;
      pprev := prev;
      prev := tmp + pprev
  };
  return prev
}
```

### *slang* grammar
*slang* programs are given by the grammar below. The grammar uses extended syntax inspired by regular expressions: `A*` denotes zero or more repetitions of `A`; `A?` denotes that `A` is optional, that is, zero or one appearances of `A`.

You can find the precise grammar used in our implementation [here](https://github.com/oembo-sse/slang/blob/6f979d504a9d40b49fab352978d001ce7bf172e5/crates/slang/src/parse/grammar.lalrpop).

An identifier `Ident` is any non-empty string that
1. is not a keyword used in the grammar and
2. starts with a letter or `_` followed by arbitrary many letters, `_` or digits, that is, it is matched by the regular expression `[a-zA-Z_][a-zA-Z_0-9]*`.

In the following grammar for slang, a program is called a `File`.
```
File ::= Item*

Item ::=
    | Global
    | Function
    | Domain
    | Method

Global ::=
    "global" Var

Type ::= "Bool" | "Int" | Ident

Vars ::= Var | Var "," Vars
Var ::= Ident ":" Type

Function ::= 
    "function" Ident "(" Vars ")" ":" Type
    Specification*
    "{" Expr "}"

Specification ::=
    | "requires" Expr
    | "ensures" Expr
    | "modifies" Expr

Exprs ::= Expr | Expr "," Exprs
Expr ::=
    | "(" Expr ")"
    | "true" | "false"
    | Integer | Ident
    | Ident "(" Exprs ")"
    | Uop Expr
    | Expr BinOp Expr
    | Quantifier Var "::" Expr
    | "old" "(" Expr ")"
    | "broke" | "result"
    
Quantifier ::= "forall" | "exists"
Uop ::= "-" | "!"
BinOp ::= 
    | "*" | "/" | "%" 
    | "+" | "-" 
    | "<<" | ">>"
    | "<" | "<=" | ">" | ">="
    | "==" | "!="
    | "&&" | "||"
    | "==>"

Domain ::=
    "domain" Ident "{" DomainItem* "}"

DomainItem ::=
    | Function
    | Axiom

Axiom ::= "axiom" Expr

Method ::= 
    "method" Ident "(" Var* ")" (":" Type)?
    Specification* Decreases?
    "{" Stmt "}"?

Decreases ::= "decreases" Expr

Stmt ::=
    | "var" Ident ":" Type (":=" Expr)?
    | Ident ":=" Expr
    | "break" | "continue" 
    | "return" Expr
    | "assume" Expr | "assert" Expr
    | Stmt ";" Stmt
    | (Ident ":=" )? Ident "(" Exprs ")"
    | "match" "{" Cases "}"
    | "loop" Invariant* Decreases? "{" Cases "}"
    | "for" Ident "in" Expr ".." Expr Invariant* Decreases? "{" Stmt "}"

Cases := Case | Case "," Cases
Case := Expr "=>" Stmt

Invariant ::= "invariant" Expr
```

We impose a few additional rules to ensure that *slang* programs are well-formed. A selection of those rules is listed below. These rules are already checked by the provided project library.

* We only admit well-typed expressions in *slang* programs. For example, if `x` and `y` are of type `Int`, then `17 / x + 3 * y` is well-typed, whereas `x ==> y + 3` is not.
* Every expression of type `Bool` is a logical formula. If the expression does not contain any quantifiers (`exists` or `forall`), it is a Boolean expression. Logical formulas may only appear in `assert` or `assume` commands as well as in the annotations `requires`, `ensures`, and `invariant`. Boolean expressions can also appear in assignments and as guards of conditionals and loops.
* The commands `break` and `continue` may only appear inside of a loop.
* The `result` expression may only appear in `ensures` specifications.
* Methods allow `requires`, `ensures`, `modifies`, and `decreases` specifications; user-defined functions only allow `requires` and `ensures` specifications.
* Function calls *are expressions* and can appear in expressions.
* Method calls *are commands* and cannot appear in expressions. If the return value of a method call is to be used, then a method call must assign its output to a variable.
* A method’s input parameters (first list `Vars` in the grammar) are read-only.
 
# Features

Generally speaking, your implementation should support **all core features** and some extension features as outlined in the guidelines.
You can implement extension features in any order, and you can work on any subset of your choice (but be careful: different features may interact with each other).

## Core Feature A: single loop-free method (★★)
Support verification of *slang* programs that consist of a *single* method, where
* the method's body does not contain any kind of iteration (no `loop` or `for` commands) and contains no method calls,
* all expressions are built-in (i.e. no user-defined functions), and
* if the method returns a value, the return command must be at the end of the method's body.

*Hints:*
- Remember that `assert`s and `ensure`s are not the only ways in which a program can fail.
- When it comes to conditionals, ordering matters.

**Passing example:**
```
method m(x: Int) {
    var y: Int := x + 15;
    match {
      x > 0 => 
        assert y/x > 0,
      true => 
        y := 5
    };
    assert y > 0
}
```
**Failing example:**
```
method m(x: Int): Int 
    requires x >= 0
    ensures result >= 0
    // false: (consider execution when x = 1)
    ensures result == 3 * x 
{
    var acc: Int := 0;
    acc := x / 2;
    acc := acc * 6;
    
    return acc
}
```
## Core Feature B: partial correctness of loops (★★)
Support verification of *partial correctness* of unbounded `loop` commands.

**Passing example:**
```
method sumn(n: Int): Int
    requires n >= 0
    ensures result == n * (n + 1) / 2
{
    var acc: Int := 0;
    var i: Int := 0;
    loop 
        invariant i >= 0
        invariant i <= n
        invariant acc == i * (i + 1) / 2
    {
        i < n =>
            i := i + 1;
            acc := acc + i
    };
    assert i == n;
    assert acc == n * (n + 1) / 2;
    
    return acc
}
```
**Failure example:**
```
method iter(n: Int): Int
    requires n >= 0
{
    var i: Int := 0;
    loop 
        // false: when the loop terminates, i == n + 1
        invariant i <= n 
    {
        i <= n => i := i + 1
    }
}
```
## Core Feature C: error reporting (★★)

If a program cannot be verified, your verification tool should correctly point to *where* and *why* verification fails. When reporting an error
* signal the correct position in the program in which verification fails, and
* specify why the program fails (e.g. does the invariant not hold at the beginning, or after some iteration of the loop? On which branch?)

*Hint:* Use the infrastructure for reporting errors of the provided library.

*Remark:* For this feature, you do not have to provide examples that verify. Instead, provide examples that illustrate the different kinds of errors that your implementation can report. 

**Example:**
```
method sumn(n: Int): Int
    requires n >= 0
{
    var acc: Int := 0;
    var i: Int := 0;
    loop 
        // Error: Invariant may not be preserved
        invariant i <= n 
    {
        i <= n =>
            acc := acc + i;
            i := i + 1
    };   
    return acc
}
```
## Extension Feature 1: bounded for-loops (★)
Support reasoning about *bounded loops* in the form of `for` commands. That is, instances of `for` loops in which the range is comprised of a constant start and end.

**Example:**
```
method client() {
    var acc: Int := 0;
    for i in 0..10 {
        acc := acc + i
    };
    assert acc == 9 * 10 / 2
}
```
## Extension Feature 2: verification of mutually recursive methods (★)

Support *partial correctness* verification of *multiple* (*and possibly mutually recursive*) methods. 

**Example:**
```
method sumn(n: Int): Int
    requires n >= 0
    ensures result == n * (n + 1)/2
{
    match {
        n == 0 => 
            return 0,
        true => 
            var res: Int;
            res := sumn(n - 1);
            return res + n
    }
}
```

## Extension Feature 3: efficient assignments (★)

Implement efficient verification of assignments by transforming commands into dynamic single assignment form (DSA) before computing weakest preconditions. That is, finish with a subset of `IVL0` comprised only of `Assert`, `Assume`, `Seq` and `NonDet`.

*Hint:* You may want to encode to other commands before reaching the final encoding.

## Extension Feature 4: unbounded for-loops (★★)
Extend verification of `for` loops such that ranges can contain variables, not just constants.

*Hint:* Some invariants may hold for any `for` loop.

**Example:**
```
method client(n: Int): Int
    ensures acc == n * (n + 1) / 2
{
    var acc: Int := 0;
    for i in 1..(n + 1)
       // invariant ...
    {
        acc := acc + i
    };
    return acc
}
```
## Extension Feature 5: custom type definitions (★★)
Support verification of slang programs that involve the declaration, axiomatisation, and use of custom types in the form of domains. 

*Hint:* Recall that domain functions do not have a body and do not allow for attaching annotations like pre- and postconditions.

**Example:**
```
domain Pair {
  function pair(x: Int, y: Int): Pair
  function fst(x: Pair): Int
  function snd(x: Pair): Int

  axiom forall x: Int :: forall y: Int :: fst(pair(x,y)) == x
  axiom forall x: Int :: forall y: Int :: snd(pair(x,y)) == y
}

method client(x: Int, y: Int)
{
  var xy: Pair := pair(x,y);

  assert fst(xy) == x;
  assert snd(xy) == y
}
```
## Extension Feature 6: user-defined functions (★★★)

Support user-defined functions that can be defined by providing the function body, pre- and post- conditions, or both. 

*Hint:* If a function body and a specification is provided, remember to check that the body indeed satisfies the specification.

**Passing example:**
```
function fac(n: Int): Int 
    requires n >= 0
    ensures result > 0
{
    n == 0 ? 1 : n * fac(n - 1)
}

method client() {
    assert fac(0) == 1
}
```
**Failing example:**
```
function fac(n: Int): Int 
    requires n >= 0
    ensures result > 0 // Postcondition may not hold
{
    n == 0 ? 0 : n * fac(n + 1) // Precondition not satisfied
}
```
## Extension Feature 7: total correctness for methods (★)
Support *total correctness* verification of recursive methods. 

**Example:**
```
method sumn(n: Int): Int
    requires n >= 0
    ensures result == n * (n + 1)/2
    decreases n
{
    var ret: Int;
    match {
        n == 0 => 
            ret := 0,
        true => 
            var res: Int;
            res := sumn(n - 1);
            ret := res + n
    };
    return ret
}
```
## Extension Feature 8: total correctness of loops (★★)
Support *total correctness* verification of loops.

**Example:**
```
method sumn(n: Int): Int
    requires n >= 0
    ensures result == n * (n + 1)/2
{
    var acc: Int := 0;
    var i: Int := 0;
    loop 
        invariant i >= 0
        invariant i <= n
        invariant acc == i * (i + 1) / 2
        decreases n - i
    {
        i < n =>
            i := i + 1;
            acc := acc + i
    };
    assert i == n;
    
    return acc
}
```
## Extension Feature 9: global variable (★★)
After supporting verification of multiple methods, extend your verifier such that one can support verification about programs that encode *global variables*. 

*Hints:*
- Global variables have consequences for how you deal with method calls.
- Note that *slang* supports `old` expressions, as well as `modifies` specifications.

**Example:**
```
global counter: Int

method inc()
    modifies counter
    ensures counter == old(counter) + 1
{
    counter := counter + 1
}


method client() 
    modifies counter
{
    counter := 0;
    
    assert counter == 0;
    inc(); // modifies counter without returning a value
    assert counter == 1;
    inc();
    assert counter == 2;
    inc();
    assert counter == 3
}
```

## Extension Feature 10: early return (★★)
Support the use of (multiple) `return` commands in the middle of the method's body.

*Hint:* the code after a `return` command *is not* executed.

**Example:**
```
method sumn(n: Int): Int
    requires n >= 0
    ensures result == n * (n + 1)/2
    decreases n
{
    match {
        n == 0 => 
            return 0,
        true => 
            var res: Int;
            res := sumn(n - 1);
            return res + n
    };
    assert false // not reachable, passes
}
```

## Extension Feature 11: breaking loops (★★★★)
Support the use of `break` and `continue` commands in `loop` commands. The intuitive behaviour of those commands is as in common mainstream languages like Java or C/C++.

*Hints:*
- This feature can be implemented in *many* different ways, and some of these will have different advantages over others.
- You may want to not only write an encoding for `break` and `continue` commands, but also modify the encoding of `loop`s.
- Remember that invariants need to hold after *any* loop iteration.
- Note that you can now quit the loop without falsifying any condition.
- Not all loops will break; programs that could be verified previously should still verify.

**Passing example:**
```
method client(): Int
{
    var i: Int := 0;
    loop 
        // invariant ...
    { true => 
        i := i + 1;
        match { i == 15 => 
            // The loop is interrupted. Execution resumes
            // from the first line after the loop.
            break 
        }
    };

    assert i == 15
}
```

## Extension Feature 12?

Feel free to suggest additional extension features. However, approach us first to check if your suggestion merits additional stars.

# Rust Template
We provide a [Rust](https://doc.rust-lang.org/book/) [library](https://github.com/oembo-sse/slang) for your project which takes care of parsing, type-checking, error reporting and of providing a web interface for your verification infrastructure. 
This repository contains a [template](https://github.com/oembo-sse/slang-template) for using this library. The template already supports verification of programs comprised of a single assertion.

You are free to implement the project in a programming language of your choice.
However, if you do not use the provided library, you have to implement the corresponding support structure yourself. The implementation effort for such infrastructure (e.g. a parser) does not contribute to your final grade.

In your project, you will mainly interface with two main components of the crate: [`ast`](https://oembo-sse.github.io/slang/slang/ast/index.html) and [`Context`](https://oembo-sse.github.io/slang/slang_ui/struct.Context.html).
* The `ast` module provides access to the abstract syntax tree of the *slang* language and to utilities that you can use to create commands, terms, formulae, etc. Notice that the library refers to both terms and formulae as [expressions](https://oembo-sse.github.io/slang/slang/ast/struct.Expr.html). Moreover, we already provide a function for converting expressions to their SMT counterpart (e.g. for [expressions](https://oembo-sse.github.io/slang/slang/ast/struct.Expr.html#method.smt)) such that they can be supplied to the [SMT solver API](https://oembo-sse.github.io/slang/smtlib/struct.Solver.html).
* the `Context` will allow you to both interface with the SMT solver (`cx.solver()`), and to report errors to the user (e.g. `cx.error(location, error_message)`). 

The template also provides a possible abstract syntax tree for a low level intermediate verification language, called `IVL`. 
It also demonstrates how to use the [SourceFile](https://oembo-sse.github.io/slang/slang/struct.SourceFile.html), in which we store all methods, functions, domains, and so on after parsing. 

An implementation of the project will mostly work as follows:
1. In a series of steps, transform the `AST` of the program into simpler programs in `IVL`;
2. Transform the `IVL` programs into [expressions](https://oembo-sse.github.io/slang/slang/ast/struct.Expr.html) that can be verified with an [SMT solver](https://oembo-sse.github.io/slang/smtlib/struct.Solver.html); and
3. [report errors](https://oembo-sse.github.io/slang/slang_ui/struct.Context.html) to the user, making sure that the *location* and *message* of the error are fitting.

## Getting Started

First, make sure that you have [Rust](https://doc.rust-lang.org/book/) and `z3` installed on your machine and available in your `PATH`. 

After that, you can use the template in the `project1` folder of your project repository.
To start your verification tool, execute `cargo run` (and then open [`http://localhost:3000/`](http://localhost:3000) in your web browser). The tool will run until you close it with CTRL + C.

To run all tests in the `tests` folder, you can run `cargo test`. 
We strongly recommend that you add your own tests for each feature.
By default, the tests attempt to verify every file in the `tests` folder and fail if the file cannot be verified. To test cases where verification *should* fail, you can add the comment `// @CheckError` to indicate the position at which verification is supposed to fail.

For example, the following test passes if the given method verifies:

```rust
method client() {
    assert 2 + 2 == 4
}
```

By contrast, the following test passes if the assertion fails:

```rust
method client() {
    // @CheckError
    assert 1 + 2 == 4
}
```

Notice that `// @CheckError` only works correctly if you have properly implemented error reporting.
If you do not plan to do so, please use a different comment to indicate where you expect an error to happen.
````

---

# Slang Verifier — Project 1

This project implements an automated verification tool for the *slang* language, based on the official template provided by course staff:
https://github.com/oembo-sse/slang-template

We extend the template to support all core and extension features of the assignment.

---

## 👥 Group Members (2 students)

| Name | Student |
|------|---------|
| Kristófer Birgir Hjörleifsson | DTU |
| Mikael Máni Eyfeld Clarke | DTU |

**Group size: 2 → grading expectation: 27 stars - 1 = 26 ⭐ target**  
(20+ stars expected for grade **12 / 1.0**)

---

## ⭐ Feature Progress Tracking

✅ = Finished | 🔄 = In Progress | ⏳ = Planned

| Feature | Stars | Status | Notes |
|--------|------:|--------|------|
| Core A: Single loop-free method | ⭐⭐ | ✅ Finished | Match statements, assignments, variable definitions |
| Core B: Partial correctness of loops | ⭐⭐ | ✅ Finished | Loop invariants, invariant preservation checking |
| Core C: Error reporting | ⭐⭐ | ✅ Finished | Enhanced error messages, proper error reporting for assertions and loops |

| Extension Feature | Stars | Status | Notes |
|------------------|------:|--------|------|
| 1: Bounded for-loops | ⭐ | ✅ Finished | Loop unrolling for constant ranges, variable substitution |
| 2: Mutually recursive methods | ⭐ | ✅ Finished | Multiple methods, method calls, basic recursion support |
| 3: Efficient assignments (DSA) | ⭐ | ✅ Finished | DSA principles via WP substitution, eliminates Assignment/Havoc |
| 4: Unbounded for-loops | ⭐⭐ | ⏳ Planned |
| 5: Custom type definitions | ⭐⭐ | ⏳ Planned |
| 6: User-defined functions | ⭐⭐⭐ | ⏳ Planned |
| 7: Total correctness for methods | ⭐ | ⏳ Planned |
| 8: Total correctness for loops | ⭐⭐ | ⏳ Planned |
| 9: Global variables | ⭐⭐ | ⏳ Planned |
| 10: Early return support | ⭐⭐ | ⏳ Planned |
| 11: Break/continue in loops | ⭐⭐⭐⭐ | ⏳ Planned |

✅ Stars Completed: **9 / 27**  
🎯 Stars Planned: **27 / 27**

> ✔ This table will be continually updated as we complete each feature with proper tests.

---

## 🧪 Test Usage

To run the verifier:
```bash
cargo run
# Open http://localhost:3000
```

To run the verification tests:
```bash
cargo test
```