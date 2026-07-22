// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Arithmetic term evaluation helpers for Nelson-Oppen interface bridge.
//!
//! These free functions evaluate arithmetic expressions under theory models,
//! collecting tight-bound reasons from all variable leaves. Used by
//! `InterfaceBridge::evaluate_and_propagate` (Int) and
//! `InterfaceBridge::evaluate_and_propagate_real` (Real).

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{TermId, TermStore, TheoryLit};
use ay_lia::LiaSolver;
use ay_lra::LraSolver;
use num_bigint::BigInt;
use num_rational::BigRational;

/// Evaluate an arithmetic term, collecting LIA bound reasons from all
/// variable leaves (#4068).
///
/// When a variable's value is looked up via `get_int_value_with_reasons`,
/// the returned reasons (tight-bound `TheoryLit`s) are appended to `reasons`.
/// This ensures the caller has a complete proof justification for the
/// evaluated value of the entire arithmetic expression.
pub(super) fn evaluate_arith_term_with_reasons(
    terms: &TermStore,
    get_int_value_with_reasons: &impl Fn(TermId) -> Option<(BigInt, Vec<TheoryLit>)>,
    term: TermId,
    reasons: &mut Vec<TheoryLit>,
) -> Option<BigInt> {
    use num_traits::Zero;

    match terms.get(term) {
        TermData::Const(Constant::Int(n)) => Some(n.clone()),
        TermData::Var(_, _) => {
            let (value, var_reasons) = get_int_value_with_reasons(term)?;
            reasons.extend(var_reasons);
            Some(value)
        }
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" => {
                let mut sum = BigInt::zero();
                for &arg in args {
                    sum += evaluate_arith_term_with_reasons(
                        terms,
                        get_int_value_with_reasons,
                        arg,
                        reasons,
                    )?;
                }
                Some(sum)
            }
            "-" if args.len() == 1 => Some(-evaluate_arith_term_with_reasons(
                terms,
                get_int_value_with_reasons,
                args[0],
                reasons,
            )?),
            "-" if args.len() >= 2 => {
                let mut result = evaluate_arith_term_with_reasons(
                    terms,
                    get_int_value_with_reasons,
                    args[0],
                    reasons,
                )?;
                for &arg in &args[1..] {
                    result -= evaluate_arith_term_with_reasons(
                        terms,
                        get_int_value_with_reasons,
                        arg,
                        reasons,
                    )?;
                }
                Some(result)
            }
            "*" => {
                let mut product = BigInt::from(1);
                for &arg in args {
                    product *= evaluate_arith_term_with_reasons(
                        terms,
                        get_int_value_with_reasons,
                        arg,
                        reasons,
                    )?;
                }
                Some(product)
            }
            _ => {
                // Unknown function (e.g., UF application like `g(x)`) — query LIA
                // for its value. LIA may know the value if the term was registered
                // via `assert_shared_equality` (#4767).
                let (value, var_reasons) = get_int_value_with_reasons(term)?;
                reasons.extend(var_reasons);
                Some(value)
            }
        },
        TermData::Ite(cond, then_t, else_t) => {
            // ITE evaluation: try to determine the condition's truth value by
            // evaluating it as an arithmetic predicate, then recurse into the
            // appropriate branch. Without this, compound expressions like
            // (+ Sum(Pred(x), Succ(y)) (ite (< v 5) v (- v 5))) cannot be
            // evaluated because LIA does not register ITE terms as simplex
            // variables. (#5081)
            let cond_val = evaluate_bool_term(terms, get_int_value_with_reasons, *cond, reasons);
            match cond_val {
                Some(true) => evaluate_arith_term_with_reasons(
                    terms,
                    get_int_value_with_reasons,
                    *then_t,
                    reasons,
                ),
                Some(false) => evaluate_arith_term_with_reasons(
                    terms,
                    get_int_value_with_reasons,
                    *else_t,
                    reasons,
                ),
                None => {
                    // Condition unknown — fall through to LIA query
                    let (value, var_reasons) = get_int_value_with_reasons(term)?;
                    reasons.extend(var_reasons);
                    Some(value)
                }
            }
        }
        _ => {
            // Unknown term — try querying LIA for its value (#4767).
            let (value, var_reasons) = get_int_value_with_reasons(term)?;
            reasons.extend(var_reasons);
            Some(value)
        }
    }
}

/// Evaluate a Boolean term by computing its arithmetic operands and comparing.
///
/// Handles comparison predicates (`<`, `<=`, `>`, `>=`), equality (`=`),
/// and negation (`not`). Returns `None` if the condition cannot be evaluated
/// (e.g., involves non-arithmetic Boolean variables). (#5081)
///
/// Exposed within `combined_solvers` so `has_unjustified_int_leaf` can mirror
/// the exact ITE-condition dispatch this evaluator performs (#w11-ite-sum).
pub(super) fn evaluate_bool_term(
    terms: &TermStore,
    get_int_value_with_reasons: &impl Fn(TermId) -> Option<(BigInt, Vec<TheoryLit>)>,
    term: TermId,
    reasons: &mut Vec<TheoryLit>,
) -> Option<bool> {
    match terms.get(term) {
        TermData::Const(Constant::Bool(b)) => Some(*b),
        TermData::Not(inner) => {
            evaluate_bool_term(terms, get_int_value_with_reasons, *inner, reasons).map(|b| !b)
        }
        TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
            let lhs = evaluate_arith_term_with_reasons(
                terms,
                get_int_value_with_reasons,
                args[0],
                reasons,
            )?;
            let rhs = evaluate_arith_term_with_reasons(
                terms,
                get_int_value_with_reasons,
                args[1],
                reasons,
            )?;
            match name.as_str() {
                "<" => Some(lhs < rhs),
                "<=" => Some(lhs <= rhs),
                ">" => Some(lhs > rhs),
                ">=" => Some(lhs >= rhs),
                "=" => Some(lhs == rhs),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Get integer value and tight-bound reasons from a LIA solver (#4068).
///
/// Returns `(value, reasons)` where `reasons` are the `TheoryLit`s from
/// the LRA solver's tight bounds that fix the variable to `value`. When
/// bounds are not tight, returns the value with empty reasons (the equality
/// is still valid under the current model assignment).
pub(super) fn lia_get_int_value_with_reasons(
    lia: &LiaSolver<'_>,
    term: TermId,
) -> Option<(BigInt, Vec<TheoryLit>)> {
    let (rational_value, reasons) = lia.lra_solver().get_value_with_reasons(term)?;
    if rational_value.is_integer() {
        Some((rational_value.to_integer(), reasons))
    } else {
        None
    }
}

/// Evaluate a Real arithmetic term, collecting LRA bound reasons from all
/// variable leaves (#4915).
///
/// Parallel to `evaluate_arith_term_with_reasons` but operates on `BigRational`
/// values and handles `Constant::Rational` leaves.
pub(super) fn evaluate_real_arith_term_with_reasons(
    terms: &TermStore,
    get_real_value_with_reasons: &impl Fn(TermId) -> Option<(BigRational, Vec<TheoryLit>)>,
    term: TermId,
    reasons: &mut Vec<TheoryLit>,
) -> Option<BigRational> {
    use num_traits::Zero;

    match terms.get(term) {
        TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
        TermData::Const(Constant::Int(n)) => Some(BigRational::from(n.clone())),
        TermData::Var(_, _) => {
            let (value, var_reasons) = get_real_value_with_reasons(term)?;
            reasons.extend(var_reasons);
            Some(value)
        }
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" => {
                let mut sum = BigRational::zero();
                for &arg in args {
                    sum += evaluate_real_arith_term_with_reasons(
                        terms,
                        get_real_value_with_reasons,
                        arg,
                        reasons,
                    )?;
                }
                Some(sum)
            }
            "-" if args.len() == 1 => Some(-evaluate_real_arith_term_with_reasons(
                terms,
                get_real_value_with_reasons,
                args[0],
                reasons,
            )?),
            "-" if args.len() >= 2 => {
                let mut result = evaluate_real_arith_term_with_reasons(
                    terms,
                    get_real_value_with_reasons,
                    args[0],
                    reasons,
                )?;
                for &arg in &args[1..] {
                    result -= evaluate_real_arith_term_with_reasons(
                        terms,
                        get_real_value_with_reasons,
                        arg,
                        reasons,
                    )?;
                }
                Some(result)
            }
            "*" => {
                let mut product = BigRational::from(BigInt::from(1));
                for &arg in args {
                    product *= evaluate_real_arith_term_with_reasons(
                        terms,
                        get_real_value_with_reasons,
                        arg,
                        reasons,
                    )?;
                }
                Some(product)
            }
            "/" if args.len() >= 2 => {
                let mut result = evaluate_real_arith_term_with_reasons(
                    terms,
                    get_real_value_with_reasons,
                    args[0],
                    reasons,
                )?;
                for &arg in &args[1..] {
                    let denom = evaluate_real_arith_term_with_reasons(
                        terms,
                        get_real_value_with_reasons,
                        arg,
                        reasons,
                    )?;
                    if denom.is_zero() {
                        return None;
                    }
                    result /= denom;
                }
                Some(result)
            }
            _ => {
                // Unknown function (e.g., UF application like `f(x)`) — query LRA
                // for its value. LRA may know the value if the term was registered
                // via `assert_shared_equality` (#4915).
                let (value, var_reasons) = get_real_value_with_reasons(term)?;
                reasons.extend(var_reasons);
                Some(value)
            }
        },
        TermData::Ite(cond, then_t, else_t) => {
            // ITE evaluation for Real-valued terms. Same logic as Int path. (#5081)
            let cond_val =
                evaluate_real_bool_term(terms, get_real_value_with_reasons, *cond, reasons);
            match cond_val {
                Some(true) => evaluate_real_arith_term_with_reasons(
                    terms,
                    get_real_value_with_reasons,
                    *then_t,
                    reasons,
                ),
                Some(false) => evaluate_real_arith_term_with_reasons(
                    terms,
                    get_real_value_with_reasons,
                    *else_t,
                    reasons,
                ),
                None => {
                    let (value, var_reasons) = get_real_value_with_reasons(term)?;
                    reasons.extend(var_reasons);
                    Some(value)
                }
            }
        }
        _ => {
            let (value, var_reasons) = get_real_value_with_reasons(term)?;
            reasons.extend(var_reasons);
            Some(value)
        }
    }
}

/// Get real value and tight-bound reasons from an LRA solver (#4915).
///
/// Returns `(value, reasons)` where `reasons` are the `TheoryLit`s from
/// the LRA solver's tight bounds that fix a variable to `value`.
pub(super) fn lra_get_real_value_with_reasons(
    lra: &LraSolver,
    term: TermId,
) -> Option<(BigRational, Vec<TheoryLit>)> {
    lra.get_value_with_reasons(term)
}

/// Evaluate a Boolean term by computing its Real arithmetic operands and comparing.
///
/// Parallel to `evaluate_bool_term` but operates on `BigRational` values. (#5081)
///
/// Exposed within `combined_solvers` so `has_unjustified_real_leaf` can mirror
/// the exact ITE-condition dispatch this evaluator performs (#w11-ite-sum).
pub(super) fn evaluate_real_bool_term(
    terms: &TermStore,
    get_real_value_with_reasons: &impl Fn(TermId) -> Option<(BigRational, Vec<TheoryLit>)>,
    term: TermId,
    reasons: &mut Vec<TheoryLit>,
) -> Option<bool> {
    match terms.get(term) {
        TermData::Const(Constant::Bool(b)) => Some(*b),
        TermData::Not(inner) => {
            evaluate_real_bool_term(terms, get_real_value_with_reasons, *inner, reasons).map(|b| !b)
        }
        TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
            let lhs = evaluate_real_arith_term_with_reasons(
                terms,
                get_real_value_with_reasons,
                args[0],
                reasons,
            )?;
            let rhs = evaluate_real_arith_term_with_reasons(
                terms,
                get_real_value_with_reasons,
                args[1],
                reasons,
            )?;
            match name.as_str() {
                "<" => Some(lhs < rhs),
                "<=" => Some(lhs <= rhs),
                ">" => Some(lhs > rhs),
                ">=" => Some(lhs >= rhs),
                "=" => Some(lhs == rhs),
                _ => None,
            }
        }
        _ => None,
    }
}
