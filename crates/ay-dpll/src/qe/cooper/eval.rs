// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A small, self-contained ground evaluator for quantifier-free LIA terms.
//!
//! This is the independent oracle used by the bounded differential check. It is
//! deliberately separate from the production theory solver: keeping the checker
//! independent of the procedure it validates is what makes the gate meaningful.
//!
//! The evaluator understands exactly the term shapes that the Cooper output and
//! the in-fragment input can produce: integer/boolean constants, integer
//! variables (looked up in a provided assignment), `+ - * div mod` over
//! integers, the comparisons `= < <= > >= distinct`, and the boolean
//! connectives `and or not =>` and `ite`. Anything else makes evaluation return
//! [`EvalResult::Unknown`], which the differential check treats as a failure (so an
//! unrecognized shape can never be silently accepted).

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{TermId, TermStore};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{Signed, Zero};
use std::collections::HashMap;

/// Result of evaluating a term on a ground assignment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum EvalResult {
    /// An integer value (for arithmetic subterms).
    Int(BigInt),
    /// A boolean value (for formula nodes).
    Bool(bool),
    /// The term used a shape this evaluator does not model. The self-check
    /// treats this as a verification failure (fail-closed).
    Unknown,
}

/// Evaluate `term` under the integer `assignment` (keyed by variable `TermId`).
///
/// Variables not present in the assignment evaluate to [`EvalResult::Unknown`].
/// SMT-LIB Euclidean `div`/`mod` semantics are used; division by zero yields
/// `Unknown` (the fragment never produces it, and treating it as Unknown keeps
/// the checker conservative).
pub(super) fn eval(
    terms: &TermStore,
    term: TermId,
    assignment: &HashMap<TermId, BigInt>,
) -> EvalResult {
    match terms.get(term) {
        TermData::Const(Constant::Int(n)) => EvalResult::Int(n.clone()),
        TermData::Const(Constant::Bool(b)) => EvalResult::Bool(*b),
        TermData::Var(_, _) => match assignment.get(&term) {
            Some(v) => EvalResult::Int(v.clone()),
            None => EvalResult::Unknown,
        },
        TermData::Not(inner) => match eval(terms, *inner, assignment) {
            EvalResult::Bool(b) => EvalResult::Bool(!b),
            _ => EvalResult::Unknown,
        },
        TermData::Ite(c, t, e) => match eval(terms, *c, assignment) {
            EvalResult::Bool(true) => eval(terms, *t, assignment),
            EvalResult::Bool(false) => eval(terms, *e, assignment),
            _ => EvalResult::Unknown,
        },
        TermData::App(Symbol::Named(name), args) => eval_app(terms, name, args, assignment),
        _ => EvalResult::Unknown,
    }
}

fn eval_app(
    terms: &TermStore,
    name: &str,
    args: &[TermId],
    assignment: &HashMap<TermId, BigInt>,
) -> EvalResult {
    // Helper closures to evaluate children.
    let int_args = |args: &[TermId]| -> Option<Vec<BigInt>> {
        let mut out = Vec::with_capacity(args.len());
        for &a in args {
            match eval(terms, a, assignment) {
                EvalResult::Int(n) => out.push(n),
                _ => return None,
            }
        }
        Some(out)
    };
    let bool_args = |args: &[TermId]| -> Option<Vec<bool>> {
        let mut out = Vec::with_capacity(args.len());
        for &a in args {
            match eval(terms, a, assignment) {
                EvalResult::Bool(b) => out.push(b),
                _ => return None,
            }
        }
        Some(out)
    };

    match name {
        "+" => match int_args(args) {
            Some(vs) => EvalResult::Int(vs.into_iter().fold(BigInt::zero(), |a, b| a + b)),
            None => EvalResult::Unknown,
        },
        "*" => match int_args(args) {
            Some(vs) => EvalResult::Int(vs.into_iter().fold(BigInt::from(1), |a, b| a * b)),
            None => EvalResult::Unknown,
        },
        "-" => match int_args(args) {
            Some(vs) if vs.len() == 1 => EvalResult::Int(-vs[0].clone()),
            Some(vs) if vs.len() >= 2 => {
                let mut acc = vs[0].clone();
                for v in &vs[1..] {
                    acc -= v;
                }
                EvalResult::Int(acc)
            }
            _ => EvalResult::Unknown,
        },
        "div" => match int_args(args) {
            Some(vs) if vs.len() == 2 => {
                if vs[1].is_zero() {
                    EvalResult::Unknown
                } else {
                    EvalResult::Int(smt_euclid_div(&vs[0], &vs[1]))
                }
            }
            _ => EvalResult::Unknown,
        },
        "mod" => match int_args(args) {
            Some(vs) if vs.len() == 2 => {
                if vs[1].is_zero() {
                    EvalResult::Unknown
                } else {
                    EvalResult::Int(smt_euclid_mod(&vs[0], &vs[1]))
                }
            }
            _ => EvalResult::Unknown,
        },
        "=" => {
            // `=` may be over ints or bools.
            if let Some(vs) = int_args(args) {
                if vs.len() == 2 {
                    return EvalResult::Bool(vs[0] == vs[1]);
                }
                return EvalResult::Unknown;
            }
            if let Some(vs) = bool_args(args) {
                if vs.len() == 2 {
                    return EvalResult::Bool(vs[0] == vs[1]);
                }
            }
            EvalResult::Unknown
        }
        "distinct" => {
            if let Some(vs) = int_args(args) {
                if vs.len() == 2 {
                    return EvalResult::Bool(vs[0] != vs[1]);
                }
            }
            EvalResult::Unknown
        }
        "<" => cmp(int_args(args), |a, b| a < b),
        "<=" => cmp(int_args(args), |a, b| a <= b),
        ">" => cmp(int_args(args), |a, b| a > b),
        ">=" => cmp(int_args(args), |a, b| a >= b),
        "and" => match bool_args(args) {
            Some(vs) => EvalResult::Bool(vs.into_iter().all(|b| b)),
            None => EvalResult::Unknown,
        },
        "or" => match bool_args(args) {
            Some(vs) => EvalResult::Bool(vs.into_iter().any(|b| b)),
            None => EvalResult::Unknown,
        },
        "=>" => match bool_args(args) {
            Some(vs) if vs.len() == 2 => EvalResult::Bool(!vs[0] || vs[1]),
            _ => EvalResult::Unknown,
        },
        "ite" => {
            // ite expressed as an App (rather than TermData::Ite) — handle too.
            if args.len() == 3 {
                match eval(terms, args[0], assignment) {
                    EvalResult::Bool(true) => return eval(terms, args[1], assignment),
                    EvalResult::Bool(false) => return eval(terms, args[2], assignment),
                    _ => return EvalResult::Unknown,
                }
            }
            EvalResult::Unknown
        }
        _ => EvalResult::Unknown,
    }
}

fn cmp(args: Option<Vec<BigInt>>, f: impl Fn(&BigInt, &BigInt) -> bool) -> EvalResult {
    match args {
        Some(vs) if vs.len() == 2 => EvalResult::Bool(f(&vs[0], &vs[1])),
        _ => EvalResult::Unknown,
    }
}

/// SMT-LIB Euclidean remainder: `0 ≤ (mod a b) < |b|`.
fn smt_euclid_mod(a: &BigInt, b: &BigInt) -> BigInt {
    let r = a.mod_floor(&b.abs());
    // mod_floor with positive modulus already yields a value in [0, |b|).
    debug_assert!(!r.is_negative());
    r
}

/// SMT-LIB Euclidean division consistent with [`smt_euclid_mod`]:
/// `a = b * (div a b) + (mod a b)`, with `0 ≤ (mod a b) < |b|`.
fn smt_euclid_div(a: &BigInt, b: &BigInt) -> BigInt {
    let r = smt_euclid_mod(a, b);
    (a - &r) / b
}
