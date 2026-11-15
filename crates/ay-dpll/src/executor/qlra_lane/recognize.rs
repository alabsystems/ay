// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Whole-problem recognizer `qlra_problem_shape` (plan §5).
//!
//! Admits exactly: Boolean combinations (`and`, `or`, `not`, `=>`, `xor`,
//! Bool `=`/`distinct`, Bool `ite`) of linear Real atoms (`<`, `<=`, `>`,
//! `>=`, Real `=`/`distinct`) over Real/Bool constants and Real/Bool binders,
//! with at least one quantifier. Refuses Int anywhere, uninterpreted
//! functions of any arity ≥ 1, arithmetic `ite`, `to_real`/`is_int`/`to_int`,
//! nonlinear products, division by a non-constant, and `let`. Anything the
//! recognizer admits, the selection can parse (Risk R8); the selection still
//! re-checks and declines on a parse failure.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId, TermStore};

use crate::qe::linrat::{parse_lin, rat_const};

/// Node budget for one recognition walk.
const MAX_RECOGNIZE_WORK: usize = 200_000;

fn is_real_or_bool(sort: &Sort) -> bool {
    matches!(sort, Sort::Real | Sort::Bool)
}

/// A numeral (possibly negated), whatever sort the frontend gave it: an
/// `(- 2)` coefficient can stay Int-sorted inside a Real product.
fn is_numeral(terms: &TermStore, term: TermId) -> bool {
    rat_const(terms, term).is_some()
}

/// A Real-valued linear argument (a numeral counts as Real).
fn real_linear(terms: &TermStore, term: TermId) -> bool {
    (matches!(terms.sort(term), Sort::Real) || is_numeral(terms, term))
        && parse_lin(terms, term).is_some()
}

fn app_admissible(terms: &TermStore, name: &str, args: &[TermId], sort: &Sort) -> bool {
    match name {
        "and" | "or" | "=>" | "xor" | "not" => matches!(sort, Sort::Bool),
        "=" | "distinct" => {
            args.len() >= 2
                && (args.iter().all(|&a| matches!(terms.sort(a), Sort::Bool))
                    || args.iter().all(|&a| real_linear(terms, a)))
        }
        "<" | "<=" | ">" | ">=" => args.len() >= 2 && args.iter().all(|&a| real_linear(terms, a)),
        // Arithmetic operators are admitted only inside an atom, where the
        // atom arm above has already required the whole argument to parse
        // linearly; here only the result sort is checked.
        "+" | "-" | "*" | "/" => matches!(sort, Sort::Real),
        _ => false,
    }
}

/// Whether the authored `roots` are a pure quantified-LRA problem.
pub(super) fn qlra_problem_shape(terms: &TermStore, roots: &[TermId]) -> bool {
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<TermId> = roots.to_vec();
    let mut quantified = false;
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if seen.len() > MAX_RECOGNIZE_WORK {
            return false;
        }
        if is_numeral(terms, term) {
            continue;
        }
        let sort = terms.sort(term);
        if !is_real_or_bool(sort) {
            return false;
        }
        match terms.get(term) {
            TermData::Const(Constant::Bool(_) | Constant::Int(_) | Constant::Rational(_)) => {}
            TermData::Const(_) => return false,
            TermData::Var(..) => {}
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => {
                if !matches!(sort, Sort::Bool) {
                    return false;
                }
                stack.extend([*c, *a, *b]);
            }
            TermData::App(symbol, args) => {
                if !app_admissible(terms, symbol.name(), args, sort) {
                    return false;
                }
                stack.extend(args.iter().copied());
            }
            TermData::Forall(binders, body, _) | TermData::Exists(binders, body, _) => {
                if binders.is_empty() || !binders.iter().all(|(_, s)| is_real_or_bool(s)) {
                    return false;
                }
                quantified = true;
                stack.push(*body);
            }
            _ => return false,
        }
    }
    quantified
}
