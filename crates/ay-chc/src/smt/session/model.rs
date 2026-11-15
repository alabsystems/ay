// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT + theory model -> `FxHashMap<String, SmtValue>` (design §2.8; contract
//! C5; owner WP-3 / C).

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};
use num_rational::BigRational;
use num_traits::{One, Zero};

use super::{AssertId, ModelExtract, ModelView, UnknownReason};
use crate::smt::types::SmtValue;

/// Runs INSIDE the bridge guard (theory still at the final scope), over the
/// view the bridge lends (`TheoryBridge::model_view`). For every assertion in
/// `active`:
/// - Bool vars -> `sat_model[var_of_term]` (default `false` if no SAT var: the
///   var is a don't-care);
/// - Int/Real -> `view.theory.arith_value(term)`; Int must be integral for
///   `Lia` (else `Err(TheoryIncomplete)`); mapped via `SmtValue::int_from_bigint`
///   / `SmtValue::Real` following `smt/check_sat/theory_model.rs` conventions.
///
/// A var of an ACTIVE assertion with no theory value => `missing_assignment += 1`;
/// default 0 is applied ONLY when the var occurs in no theory atom of any
/// active assertion (a pure don't-care), else `Err(TheoryIncomplete)` — fail
/// closed on the "missing assignment" class.
///
/// Names: `view.own.var_original_names[qualified]` (keys are `{name}_{sort}`).
/// `sat_model` is the `AssumeResult::Sat(model)` vector returned by ay-sat
/// (truncated to `user_num_vars`, which includes every minted var, design F9);
/// `sat.value()` is never read after the solve.
///
/// Normalisation auxiliaries (`_ite_*`, `_mod_*`, `_div_*`, namespaced by the
/// structural key) are stripped: they never occur in the caller's expression,
/// and the router's strict verifier evaluates the ORIGINAL expression.
pub(crate) fn extract(
    view: &ModelView<'_>,
    sat_model: &[bool],
    active: &[AssertId],
) -> Result<ModelExtract, UnknownReason> {
    let terms = &view.own.terms;
    let mut model: FxHashMap<String, SmtValue> = FxHashMap::default();
    let mut seen: FxHashSet<TermId> = FxHashSet::default();
    let mut missing_assignment = 0u64;
    // Vars under some theory atom of an ACTIVE assertion; built lazily on the
    // first theory miss (misses are the rare path).
    let mut constrained: Option<FxHashSet<TermId>> = None;

    for &id in active {
        let Some(assertion) = view.assertions.get(id.0 as usize) else {
            continue;
        };
        for &t in &assertion.bool_vars {
            if !seen.insert(t) {
                continue;
            }
            let Some(name) = model_name(view, t) else {
                continue;
            };
            let value = view
                .tseitin
                .term_to_var
                .get(&t)
                .and_then(|&dimacs| sat_model.get((dimacs as usize).saturating_sub(1)))
                .copied()
                // No SAT var (or beyond the returned prefix): the var is a
                // don't-care of the encoding.
                .unwrap_or(false);
            model.insert(name, SmtValue::Bool(value));
        }
        for &t in &assertion.arith_vars {
            if !seen.insert(t) {
                continue;
            }
            let Some(name) = model_name(view, t) else {
                continue;
            };
            let sort = terms.sort(t).clone();
            match view.theory.arith_value(t) {
                Some(v) => model.insert(name, arith_smt_value(&sort, v)?),
                None => {
                    missing_assignment += 1;
                    let constrained =
                        constrained.get_or_insert_with(|| constrained_vars(terms, view, active));
                    if constrained.contains(&t) {
                        // The var occurs in a theory atom the theory was fed
                        // and still has no value: fail closed (the
                        // DIAGNOSIS_lra_lin "missing assignment" class).
                        return Err(UnknownReason::TheoryIncomplete);
                    }
                    // Pure don't-care: no active atom mentions it.
                    let zero = BigRational::zero();
                    model.insert(name, arith_smt_value(&sort, zero)?)
                }
            };
        }
    }

    Ok(ModelExtract {
        model,
        missing_assignment,
    })
}

/// Original CHC name of a variable term (`var_original_names[qualified]`,
/// falling back to the qualified name as the legacy extractor does); `None`
/// for a normalisation auxiliary (stripped) or a non-variable term.
fn model_name(view: &ModelView<'_>, t: TermId) -> Option<String> {
    let TermData::Var(qualified, _) = view.own.terms.get(t) else {
        return None;
    };
    let name = view
        .own
        .var_original_names
        .get(qualified)
        .map_or(qualified.as_str(), String::as_str);
    if is_normalisation_aux(name) {
        return None;
    }
    Some(name.to_owned())
}

/// The prefixes `SmtContext::rename_internal_aux_vars` namespaces
/// (`smt/context.rs`; mirrored by `smt/incremental/mod.rs::strip_namespace_suffix`).
fn is_normalisation_aux(name: &str) -> bool {
    name.starts_with("_ite_")
        || name.starts_with("_mod_q_")
        || name.starts_with("_mod_r_")
        || name.starts_with("_div_q_")
        || name.starts_with("_div_r_")
}

/// `SmtValue` for a theory value under the variable's sort: Real => `Real`;
/// Int => `int_from_bigint` (integral required — a fractional Int value is
/// theory incompleteness, never rounded).
fn arith_smt_value(sort: &Sort, v: BigRational) -> Result<SmtValue, UnknownReason> {
    match sort {
        Sort::Real => Ok(SmtValue::Real(v)),
        Sort::Int => {
            if v.denom().is_one() {
                Ok(SmtValue::int_from_bigint(v.numer().clone()))
            } else {
                // Under `Lra` an Int var cannot be active (eligibility rejects
                // it); under `Lia` a fractional value means B&B did not finish.
                Err(UnknownReason::TheoryIncomplete)
            }
        }
        _ => Err(UnknownReason::TheoryIncomplete),
    }
}

/// Every Int/Real variable reachable from a theory atom of an ACTIVE assertion.
fn constrained_vars(
    terms: &TermStore,
    view: &ModelView<'_>,
    active: &[AssertId],
) -> FxHashSet<TermId> {
    let mut out: FxHashSet<TermId> = FxHashSet::default();
    let mut seen: FxHashSet<TermId> = FxHashSet::default();
    let mut stack: Vec<TermId> = Vec::new();
    for &id in active {
        let Some(assertion) = view.assertions.get(id.0 as usize) else {
            continue;
        };
        stack.extend(assertion.atoms.iter().copied());
    }
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Var(..) => {
                if matches!(terms.sort(t), Sort::Int | Sort::Real) {
                    out.insert(t);
                }
            }
            TermData::Const(_) => {}
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Let(bindings, body) => {
                stack.extend(bindings.iter().map(|(_, t)| *t));
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            _ => {}
        }
    }
    out
}

/// Exposed for the unit tests: an integral rational maps to `Int`, a Real to
/// `Real`; a `BigInt` beyond `i128` takes the canonical escape.
#[cfg(test)]
pub(super) fn arith_smt_value_for_tests(
    sort: &Sort,
    v: BigRational,
) -> Result<SmtValue, UnknownReason> {
    arith_smt_value(sort, v)
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use num_bigint::BigInt;

    use super::*;

    #[test]
    fn integral_and_fractional_values_map_by_sort() {
        let two = BigRational::from_integer(BigInt::from(2));
        assert_eq!(
            arith_smt_value_for_tests(&Sort::Real, two.clone()).unwrap(),
            SmtValue::Real(two.clone())
        );
        assert_eq!(
            arith_smt_value_for_tests(&Sort::Int, two).unwrap(),
            SmtValue::Int(2)
        );
        let half = BigRational::new(BigInt::from(1), BigInt::from(2));
        assert!(matches!(
            arith_smt_value_for_tests(&Sort::Int, half.clone()),
            Err(UnknownReason::TheoryIncomplete)
        ));
        assert_eq!(
            arith_smt_value_for_tests(&Sort::Real, half.clone()).unwrap(),
            SmtValue::Real(half)
        );
        assert!(matches!(
            arith_smt_value_for_tests(&Sort::Bool, BigRational::zero()),
            Err(UnknownReason::TheoryIncomplete)
        ));
    }

    #[test]
    fn normalisation_auxiliaries_are_recognised() {
        assert!(is_normalisation_aux("_ite_0__s0123"));
        assert!(is_normalisation_aux("_mod_q_1"));
        assert!(is_normalisation_aux("_div_r_7__q3"));
        assert!(!is_normalisation_aux("x"));
        assert!(!is_normalisation_aux("ite_0"));
    }
}
