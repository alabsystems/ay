// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The bounded-subset searches behind
//! [`Executor::replace_with_exact_authored_linear_refutation`], and the
//! whole-pool model that decides one of them without enumerating it.
//!
//! ## `GUARD_MUTATION_LEDGER`
//!
//! Each guard was DELETED, the named test observed FAILING, and the guard
//! restored. The last row is honestly classified as a fail-closed DEFENCE
//! rather than a mutation-checked guard, with the measurement that stands in
//! for a falsifying unit input.
//!
//! | guard | mutation | test observed failing |
//! |---|---|---|
//! | the gate's `cardinality >= 2` floor | `>= 1` | `the_gated_search_matches_the_exhaustive_one_over_every_pool_of_the_alphabet` (the `1 <= 2q <= 1` pair is refuted only by `recognize_lia_divisibility`, at cardinality 1) |
//! | `RowDemand::Strict` evaluated with `<` | `<=` | `the_model_check_keeps_a_real_strict_row_strict` |
//! | congruence canonicalization before evaluation | dropped | `the_model_check_merges_congruent_opaque_terms_before_evaluating` |
//! | an unvalued atom fails closed | defaulted to `0` | `an_unvalued_atom_fails_the_model_check_closed` |
//! | the model is VERIFIED, not taken from the LRA verdict | return `true` on any non-`Unsat` verdict | NOT falsified by the unit alphabet: on every generated pool a non-`Unsat` verdict came with a model that verifies. Its evidence is production: on `dillig12_m_000.smt2` the verification rejects the solver's candidate on **95 of 2106** gated leaves (a fractional assignment against a row the verifier evaluates at `1/2`), and each of those falls back to the unpruned search instead of skipping it. |

use super::super::proof_farkas_validation::blocking_clause_negation_has_verified_model;
use super::*;

/// The widest authored numeric pool either search will consider.
pub(super) const MAX_LINEAR_ROOTS: usize = 12;

/// Which subset search [`derive_numeric_negation`] runs.
///
/// The two modes accept and reject exactly the same subsets — see
/// [`ModelGated`](SubsetSearch::ModelGated) for why — and
/// [`Exhaustive`](SubsetSearch::Exhaustive) exists so a differential test can
/// pin that, over generated pools, against the enumeration it replaced.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum SubsetSearch {
    /// Enumerate cardinality 0 and 1, then decide cardinality 2 and up with one
    /// whole-pool model instead of enumerating them.
    ModelGated,
    /// Enumerate every bounded-support subset. The pre-existing behaviour,
    /// compiled only under `cfg(test)` so production cannot select it and the
    /// differential test still has the exact code it must agree with.
    #[cfg(test)]
    Exhaustive,
}

pub(super) fn is_numeric_literal(terms: &TermStore, term: TermId) -> bool {
    let atom = match terms.get(term) {
        TermData::Not(inner) => *inner,
        _ => term,
    };
    let TermData::App(Symbol::Named(operator), args) = terms.get(atom) else {
        return false;
    };
    args.len() == 2
        && matches!(operator.as_str(), "=" | "<" | "<=" | ">" | ">=")
        && args
            .iter()
            .all(|&arg| matches!(terms.sort(arg), Sort::Int | Sort::Real))
}

/// Whether NO subset of cardinality 2 or more can be accepted, decided once.
///
/// The four acceptors in the loop below are: the LRA Farkas reconstruction, the
/// all-ones direct Farkas check, [`recognize_lia_bounds_gap`] and
/// [`recognize_lia_divisibility`]. The last two are the only ones that can
/// accept WITHOUT a Farkas certificate, and both are width-restricted — the
/// bounds gap takes exactly two literals, divisibility one or two — so a clause
/// of `cardinality + 1` literals can reach them only at cardinality 0 or 1,
/// which this gate never skips. From cardinality 2 up an accept therefore needs
/// a Farkas certificate over `{ not f : f in S } + { not target }`, and
/// [`blocking_clause_negation_has_verified_model`] refutes every certificate
/// over every sub-multiset of the pool at once when it holds.
///
/// So the gate removes `sum(C(n, 2..=6))` reconstruct-and-verify attempts and
/// replaces them with one solve and one row-evaluation pass, and it can only
/// fire where the enumeration was going to reject all of them.
fn pool_model_refutes_wider_subsets(
    terms: &mut TermStore,
    facts: &[ArithmeticFact],
    target: TermId,
    target_complement: TermId,
) -> bool {
    let mut pool_clause: Vec<TermId> = facts
        .iter()
        .filter(|fact| fact.term != target)
        .map(|fact| terms.mk_not_raw(fact.term))
        .collect();
    pool_clause.push(target_complement);
    blocking_clause_negation_has_verified_model(terms, &pool_clause)
}

#[derive(Clone, Copy)]
pub(super) struct ArithmeticFact {
    pub(super) term: TermId,
    pub(super) unit: ProofId,
}

/// Derive `not target` from a bounded subset of already-projected
/// numeric facts.  The producer does not decide validity: it asks the
/// rational Farkas reconstructor first, then the strict checker's exact
/// integer-gap recognizer.  A miss leaves the branch unsupported.
pub(super) fn derive_numeric_negation(
    terms: &mut TermStore,
    candidate: &mut Proof,
    facts: &[ArithmeticFact],
    target: TermId,
    search: SubsetSearch,
) -> Option<ProofId> {
    const MAX_SUPPORT: usize = 6;
    if facts.len() > MAX_LINEAR_ROOTS {
        return None;
    }
    let target_complement = terms.mk_not_raw(target);
    let limit = 1_u64 << facts.len();
    let mut wider_subsets_refuted = None;
    for cardinality in 0..=MAX_SUPPORT.min(facts.len()) {
        // Decided once, on entry to the first cardinality the model can speak
        // for, and only if the narrow sweeps have already declined.
        if cardinality >= 2 && search == SubsetSearch::ModelGated {
            let refuted = *wider_subsets_refuted.get_or_insert_with(|| {
                pool_model_refutes_wider_subsets(terms, facts, target, target_complement)
            });
            if refuted {
                return None;
            }
        }
        for mask in 0_u64..limit {
            if mask.count_ones() as usize != cardinality {
                continue;
            }
            let selected: Vec<ArithmeticFact> = facts
                .iter()
                .enumerate()
                .filter_map(|(index, fact)| {
                    ((mask & (1_u64 << index)) != 0 && fact.term != target).then_some(*fact)
                })
                .collect();
            if selected.len() != cardinality {
                continue;
            }
            let mut clause: Vec<TermId> = selected
                .iter()
                .map(|fact| terms.mk_not_raw(fact.term))
                .collect();
            clause.push(target_complement);

            let mut farkas = None;
            let mut inferred = TheoryLemmaKind::Generic;
            let rational = super::super::proof_farkas::try_lra_farkas_reconstruction(
                terms,
                &clause,
                &mut farkas,
                &mut inferred,
            );
            // The LRA engine can simplify a ground affine conflict
            // (e.g. `m <= m - 1`) before surfacing coefficients. Try
            // the smallest deterministic candidate, but grant it no
            // authority: the exact Farkas checker must replay it over
            // the final blocking clause before it can be emitted.
            let direct_farkas =
                FarkasAnnotation::new(vec![num_rational::Rational64::from(1); clause.len()]);
            let checked_direct =
                super::super::proof_farkas_validation::certificate_valid_for_blocking_clause(
                    terms,
                    &clause,
                    &direct_farkas,
                );
            let checked_farkas = if rational {
                farkas
            } else if checked_direct {
                Some(direct_farkas)
            } else {
                None
            };
            let mut current = if let Some(farkas) = checked_farkas {
                candidate.add_step(ProofStep::TheoryLemma {
                    theory: "LRA".to_string(),
                    clause: clause.clone(),
                    farkas: Some(farkas),
                    kind: TheoryLemmaKind::LraFarkas,
                    lia: None,
                })
            } else if ay_core::proof_validation::recognize_lia_bounds_gap(terms, &clause) {
                candidate.add_step(ProofStep::TheoryLemma {
                    theory: "LIA".to_string(),
                    clause: clause.clone(),
                    farkas: None,
                    kind: TheoryLemmaKind::LiaGeneric,
                    lia: Some(ay_core::LiaAnnotation::BoundsGap),
                })
            } else if ay_core::proof_validation::recognize_lia_divisibility(terms, &clause) {
                candidate.add_step(ProofStep::TheoryLemma {
                    theory: "LIA".to_string(),
                    clause: clause.clone(),
                    // The Divisibility validator re-derives the exact
                    // integer gap and intentionally ignores this wire
                    // compatibility vector.
                    farkas: Some(FarkasAnnotation::new(vec![
                        num_rational::Rational64::from(1);
                        clause.len()
                    ])),
                    kind: TheoryLemmaKind::LiaGeneric,
                    lia: Some(ay_core::LiaAnnotation::Divisibility),
                })
            } else {
                continue;
            };

            let mut residual = clause;
            let mut failed = false;
            for fact in &selected {
                let blocker = terms.mk_not_raw(fact.term);
                let Some(position) = residual.iter().position(|&lit| lit == blocker) else {
                    failed = true;
                    break;
                };
                let _ = residual.remove(position);
                current = candidate.add_resolution(residual.clone(), fact.term, current, fact.unit);
            }
            if !failed && residual == [target_complement] {
                return Some(current);
            }
        }
    }
    None
}

/// Recursively falsify a bounded Boolean formula. Arithmetic leaves are
/// discharged by `derive_numeric_negation`; `and` needs one false
/// child, while `or` needs all children false. Every connective step is
/// an independently checked Alethe tautology.
pub(super) fn derive_boolean_negation(
    terms: &mut TermStore,
    candidate: &mut Proof,
    facts: &[ArithmeticFact],
    target: TermId,
    work: &mut usize,
    depth: usize,
    search: SubsetSearch,
) -> Option<ProofId> {
    const MAX_BOOLEAN_WORK: usize = 64;
    const MAX_BOOLEAN_DEPTH: usize = 12;
    *work += 1;
    if *work > MAX_BOOLEAN_WORK || depth > MAX_BOOLEAN_DEPTH {
        return None;
    }
    if is_numeric_literal(terms, target) {
        return derive_numeric_negation(terms, candidate, facts, target, search);
    }
    let TermData::App(Symbol::Named(operator), children) = terms.get(target).clone() else {
        return None;
    };
    match operator.as_str() {
        "and" => {
            for (position, child) in children.into_iter().enumerate() {
                let Some(child_negation) = derive_boolean_negation(
                    terms,
                    candidate,
                    facts,
                    child,
                    work,
                    depth + 1,
                    search,
                ) else {
                    continue;
                };
                let target_complement = terms.mk_not_raw(target);
                let projection = candidate.add_rule_step(
                    AletheRule::AndPos(position as u32),
                    vec![target_complement, child],
                    Vec::new(),
                    vec![target],
                );
                return Some(candidate.add_resolution(
                    vec![target_complement],
                    child,
                    projection,
                    child_negation,
                ));
            }
            None
        }
        "or" => {
            let target_complement = terms.mk_not_raw(target);
            let mut clause = Vec::with_capacity(children.len() + 1);
            clause.push(target_complement);
            clause.extend(children.iter().copied());
            let mut current = candidate.add_rule_step(
                AletheRule::OrPos(0),
                clause.clone(),
                Vec::new(),
                vec![target],
            );
            let mut residual = clause;
            for child in children {
                let child_negation = derive_boolean_negation(
                    terms,
                    candidate,
                    facts,
                    child,
                    work,
                    depth + 1,
                    search,
                )?;
                let position = residual.iter().position(|&lit| lit == child)?;
                let _ = residual.remove(position);
                current =
                    candidate.add_resolution(residual.clone(), child, current, child_negation);
            }
            (residual == [target_complement]).then_some(current)
        }
        _ => None,
    }
}

#[cfg(test)]
#[path = "authored_linear_subset_tests.rs"]
mod tests;
