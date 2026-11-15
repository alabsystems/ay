// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The spellings AY's command parser normalizes and pinned Carcara refuses,
//! read from one command's exact source text.
//!
//! * A problem command Carcara's `parse_problem` does not know is skipped
//!   token by token, although AY reads it into an ordinary command:
//!   `(assert-not t)` becomes an `assert` (Carcara's premise is missing), and
//!   `(define-const c Int 1)` a `define-fun`. Carcara never defines `c`, so
//!   the problem parses until it uses `c` (`identifier 'c' is not defined`):
//!   the parsed command that follows is marked skipped instead of refused.
//! * The legacy Z3 form `(declare-datatypes () ((T A B)))`: Carcara expects a
//!   non-empty `((T 0) ...)` sort list (`expected non-empty sequence`).
//! * A bare-symbol constructor `A` where SMT-LIB writes `(A)`: Carcara's
//!   `parse_constructor` expects `(` (`unexpected token: 'A'`).
//! * `(declare-sort S)` without the arity numeral Z3 lets an author omit.
//!
//! AY reads each into the same command as a standard spelling, so the command
//! alone cannot show them.

use ay_frontend::SExpr;

/// How pinned Carcara reads an authored command whose text shows no gap.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum TextReading {
    /// As the command AY parsed from it.
    AsParsed,
    /// It skips the whole command, which AY reads into one that defines a
    /// symbol (`define-const`).
    SkippedWhole,
}

/// How pinned Carcara reads the authored command whose exact source text is
/// `source`, or why it cannot parse it, as far as the text alone shows.
pub(super) fn read_source_text(source: &str) -> Result<TextReading, String> {
    if let Some(gap) = super::lexer::lexer_gap(source) {
        return Err(gap);
    }
    let gap = match leading_keyword(source) {
        Some("define-const") => return Ok(TextReading::SkippedWhole),
        Some(keyword) => keyword_gap(keyword, source),
        None => None,
    };
    gap.map_or(Ok(TextReading::AsParsed), Err)
}

fn keyword_gap(keyword: &str, source: &str) -> Option<String> {
    match keyword {
        "declare-datatype" | "declare-datatypes" => datatype_gap(source),
        "declare-sort" => declare_sort_gap(source),
        // Commands Carcara's `parse_problem` reads.
        "set-logic" | "define-sort" | "declare-fun" | "declare-const" | "define-fun"
        | "define-fun-rec" | "define-funs-rec" | "assert" | "check-sat-assuming" => None,
        // Commands it skips that carry no problem content.
        "set-option"
        | "set-info"
        | "check-sat"
        | "check-sat-using"
        | "get-model"
        | "get-value"
        | "get-assignment"
        | "get-assertions"
        | "get-proof"
        | "get-unsat-core"
        | "get-unsat-assumptions"
        | "get-info"
        | "get-option"
        | "get-objectives"
        | "get-objective-certificates"
        | "get-consequences"
        | "get-interpolant"
        | "compute-interpolant"
        | "get-abduct"
        | "eval"
        | "simplify"
        | "display"
        | "echo"
        | "labels"
        | "help"
        | "help-simplifier"
        | "help-tactic"
        | "apply"
        | "push"
        | "pop"
        | "reset"
        | "reset-assertions"
        | "exit"
        | "assert-soft"
        | "maximize"
        | "minimize" => None,
        other if other.starts_with("dbg-") => None,
        other => Some(format!(
            "the problem uses the command `{other}`, which pinned Carcara 1.1.0's problem \
             parser skips although AY reads it into the problem"
        )),
    }
}

/// The symbol after a command's opening parenthesis, past leading whitespace
/// and `;` comments.
fn leading_keyword(source: &str) -> Option<&str> {
    let mut rest = source;
    loop {
        rest = rest.trim_start();
        match rest.strip_prefix(';') {
            Some(comment) => rest = comment.split_once('\n').map_or("", |(_, after)| after),
            None => break,
        }
    }
    let body = rest.strip_prefix('(')?.trim_start();
    let end = body
        .find(|c: char| c.is_whitespace() || matches!(c, '(' | ')' | ';' | '"' | '|'))
        .unwrap_or(body.len());
    Some(&body[..end]).filter(|keyword| !keyword.is_empty())
}

/// `parse_declare_sort` requires the arity numeral that Z3 lets an author
/// leave out: `(declare-sort S)` stops Carcara (`unexpected token: ')'`).
fn declare_sort_gap(source: &str) -> Option<String> {
    match &ay_frontend::sexp::parse_sexp(source) {
        Ok(SExpr::List(items))
            if matches!(items.as_slice(), [SExpr::Symbol(_), _, SExpr::Numeral(_)]) =>
        {
            None
        }
        _ => Some(
            "the problem declares a sort without its arity numeral, which pinned Carcara \
             1.1.0 does not parse"
                .to_string(),
        ),
    }
}

fn datatype_gap(source: &str) -> Option<String> {
    let parsed = ay_frontend::sexp::parse_sexp(source);
    let Ok(SExpr::List(items)) = &parsed else {
        return Some(
            "a datatype declaration's source text does not re-read as one command, so \
             its spelling is undetermined"
                .to_string(),
        );
    };
    let declarations = match items.as_slice() {
        [SExpr::Symbol(head), SExpr::List(sorts), SExpr::List(declarations)]
            if head == "declare-datatypes" =>
        {
            if sorts.is_empty() && !declarations.is_empty() {
                return Some(
                    "the problem uses the legacy `(declare-datatypes () ...)` spelling, which \
                     pinned Carcara 1.1.0 does not parse (it requires `((<name> <arity>) ...)`)"
                        .to_string(),
                );
            }
            declarations.iter().collect::<Vec<_>>()
        }
        [SExpr::Symbol(head), _, declaration] if head == "declare-datatype" => vec![declaration],
        _ => return None,
    };
    declarations.into_iter().find_map(bare_constructor)
}

/// The first constructor of one datatype declaration (`(<ctor>+)` or
/// `(par (<param>+) (<ctor>+))`) spelled as a bare symbol.
fn bare_constructor(declaration: &SExpr) -> Option<String> {
    let SExpr::List(items) = declaration else {
        return None;
    };
    let constructors = match items.as_slice() {
        [SExpr::Symbol(par), _, SExpr::List(constructors)] if par == "par" => constructors,
        _ => items,
    };
    constructors
        .iter()
        .find_map(|constructor| match constructor {
            SExpr::Symbol(name) => Some(format!(
                "the problem declares constructor `{name}` as a bare symbol, which pinned Carcara \
             1.1.0 does not parse (it requires `({name})`)"
            )),
            _ => None,
        })
}
