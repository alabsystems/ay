// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact finite-carrier symbolic-select expansion recognition.

use std::collections::BTreeSet;

use ay_core::kani_compat::DetHashSet;
use ay_core::{Sort, TermData, TermId, TermStore};

use super::{equality_sides, select_parts, DatatypeContext, DomainPoint, FiniteCarrier};

/// A select-expansion formula has one symbolic select. The limit is defensive:
/// valid schemas produce one candidate no matter how many domain points occur.
const MAX_SYMBOLIC_SELECT_CANDIDATES: usize = 16;

#[derive(Clone)]
struct SymbolicSelectCandidate {
    select: TermId,
    array: TermId,
    index: TermId,
    index_sort: Sort,
    element_sort: Sort,
    carrier: FiniteCarrier,
}

pub(super) fn matches_finite_select_expansion(
    terms: &TermStore,
    clause: &[TermId],
    datatype_context: Option<DatatypeContext<'_>>,
) -> bool {
    let [axiom] = clause else {
        return false;
    };
    if terms.sort(*axiom) != &Sort::Bool {
        return false;
    }

    let Some(candidates) = symbolic_select_candidates(terms, *axiom, datatype_context) else {
        return false;
    };
    candidates
        .iter()
        .any(|candidate| matches_select_expansion_for_candidate(terms, *axiom, candidate))
}

fn symbolic_select_candidates(
    terms: &TermStore,
    root: TermId,
    datatype_context: Option<DatatypeContext<'_>>,
) -> Option<Vec<SymbolicSelectCandidate>> {
    let mut pending = vec![root];
    let mut visited = DetHashSet::default();
    let mut candidate_terms = BTreeSet::new();
    let mut candidates = Vec::new();
    while let Some(term) = pending.pop() {
        if !visited.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::App(_, arguments) => {
                if let Some((array, index)) = select_parts(terms, term) {
                    let Sort::Array(array_sort) = terms.sort(array) else {
                        return None;
                    };
                    if let Some(carrier) = FiniteCarrier::for_sort(
                        terms,
                        &array_sort.index_sort,
                        false,
                        datatype_context,
                    ) {
                        if carrier
                            .point(terms, &array_sort.index_sort, index)
                            .is_none()
                            && candidate_terms.insert(term)
                        {
                            if candidates.len() == MAX_SYMBOLIC_SELECT_CANDIDATES {
                                return None;
                            }
                            candidates.push(SymbolicSelectCandidate {
                                select: term,
                                array,
                                index,
                                index_sort: array_sort.index_sort.clone(),
                                element_sort: array_sort.element_sort.clone(),
                                carrier,
                            });
                        }
                    }
                }
                pending.extend(arguments.iter().copied());
            }
            TermData::Not(inner) => pending.push(*inner),
            TermData::Ite(condition, then_term, else_term) => {
                pending.push(*condition);
                pending.push(*then_term);
                pending.push(*else_term);
            }
            TermData::Let(bindings, body) => {
                pending.extend(bindings.iter().map(|(_, value)| *value));
                pending.push(*body);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                pending.push(*body);
                pending.extend(triggers.iter().flatten().copied());
            }
            TermData::Const(_) | TermData::Var(_, _) => {}
            // `TermData` is non-exhaustive across the ay-core crate boundary.
            // Unknown future leaves cannot contain a select candidate, while
            // unknown compound terms must remain unclassified until traversal
            // support is added explicitly.
            _ => return None,
        }
    }
    Some(candidates)
}

fn matches_select_expansion_for_candidate(
    terms: &TermStore,
    axiom: TermId,
    candidate: &SymbolicSelectCandidate,
) -> bool {
    let mut points = BTreeSet::new();
    let mut current = axiom;

    // `mk_eq(select, ite(...))` distributes equality through at most three
    // non-Bool ITE levels. Consume any such exact normalized prefix first.
    while let TermData::Ite(condition, then_term, else_term) = terms.get(current) {
        if terms.sort(current) != &Sort::Bool
            || terms.sort(*condition) != &Sort::Bool
            || terms.sort(*then_term) != &Sort::Bool
            || terms.sort(*else_term) != &Sort::Bool
        {
            break;
        }
        let Some(condition_point) = condition_domain_point(terms, *condition, candidate) else {
            return false;
        };
        let Some(branch_point) = value_equality_domain_point(terms, *then_term, candidate) else {
            return false;
        };
        if condition_point != branch_point || !points.insert(condition_point) {
            return false;
        }
        current = *else_term;
    }

    // The remaining suffix is either the original surface equality or the
    // equality left when `mk_eq`'s bounded ITE-distribution depth is exhausted.
    let Some((left, right)) = equality_sides(terms, current) else {
        return false;
    };
    let value = if left == candidate.select {
        right
    } else if right == candidate.select {
        left
    } else {
        return false;
    };
    if !consume_value_chain(terms, value, candidate, &mut points) {
        return false;
    }
    candidate.carrier.is_complete(&points)
}

fn consume_value_chain(
    terms: &TermStore,
    mut value: TermId,
    candidate: &SymbolicSelectCandidate,
    points: &mut BTreeSet<DomainPoint>,
) -> bool {
    loop {
        match terms.get(value) {
            TermData::Ite(condition, then_term, else_term) => {
                if terms.sort(value) != &candidate.element_sort
                    || terms.sort(*condition) != &Sort::Bool
                    || terms.sort(*then_term) != &candidate.element_sort
                    || terms.sort(*else_term) != &candidate.element_sort
                {
                    return false;
                }
                let Some(condition_point) = condition_domain_point(terms, *condition, candidate)
                else {
                    return false;
                };
                let Some(branch_point) = value_select_domain_point(terms, *then_term, candidate)
                else {
                    return false;
                };
                if condition_point != branch_point || !points.insert(condition_point) {
                    return false;
                }
                value = *else_term;
            }
            _ => {
                let Some(final_point) = value_select_domain_point(terms, value, candidate) else {
                    return false;
                };
                return points.insert(final_point);
            }
        }
    }
}

fn condition_domain_point(
    terms: &TermStore,
    condition: TermId,
    candidate: &SymbolicSelectCandidate,
) -> Option<DomainPoint> {
    if terms.sort(condition) != &Sort::Bool {
        return None;
    }
    if let Some((left, right)) = equality_sides(terms, condition) {
        let domain_term = if left == candidate.index {
            right
        } else if right == candidate.index {
            left
        } else {
            return None;
        };
        return candidate
            .carrier
            .point(terms, &candidate.index_sort, domain_term);
    }

    // `mk_eq(i, true)` is `i`; `mk_eq(i, false)` is the canonical negation
    // of `i`. Cover the direct and double-negation forms without granting any
    // broader propositional equivalence to an untrusted proof term.
    if matches!(&candidate.carrier, FiniteCarrier::Bool) {
        if condition == candidate.index {
            return Some(DomainPoint::Bool(true));
        }
        if matches!(terms.get(condition), TermData::Not(inner) if *inner == candidate.index)
            || matches!(terms.get(candidate.index), TermData::Not(inner) if *inner == condition)
        {
            return Some(DomainPoint::Bool(false));
        }
    }
    None
}

fn value_equality_domain_point(
    terms: &TermStore,
    equality: TermId,
    candidate: &SymbolicSelectCandidate,
) -> Option<DomainPoint> {
    let (left, right) = equality_sides(terms, equality)?;
    let value = if left == candidate.select {
        right
    } else if right == candidate.select {
        left
    } else {
        return None;
    };
    value_select_domain_point(terms, value, candidate)
}

fn value_select_domain_point(
    terms: &TermStore,
    value: TermId,
    candidate: &SymbolicSelectCandidate,
) -> Option<DomainPoint> {
    let (array, index) = select_parts(terms, value)?;
    if array != candidate.array || terms.sort(value) != &candidate.element_sort {
        return None;
    }
    candidate.carrier.point(terms, &candidate.index_sort, index)
}
