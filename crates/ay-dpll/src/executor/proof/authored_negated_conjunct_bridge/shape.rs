// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded structural decoding and source/goal matching for the NIA bridge.

use ay_core::{AletheRule, ProofStep, Symbol, TermData, TermId, TermStore};

use super::{LiteralBridge, Relation, RelationKind, MAX_CONJUNCTS};

pub(super) fn packed_trust_unit(terms: &TermStore, step: &ProofStep) -> Option<TermId> {
    let ProofStep::Step {
        rule: AletheRule::Trust,
        clause,
        premises,
        args,
    } = step
    else {
        return None;
    };
    let [packed] = clause.as_slice() else {
        return None;
    };
    (premises.is_empty() && args.is_empty() && packed_children(terms, *packed).is_some())
        .then_some(*packed)
}

pub(super) fn packed_children(terms: &TermStore, packed: TermId) -> Option<Vec<TermId>> {
    match terms.get(packed) {
        TermData::App(Symbol::Named(name), children)
            if name == "or" && children.len() <= MAX_CONJUNCTS =>
        {
            Some(children.clone())
        }
        _ => None,
    }
}

pub(super) fn raw_negated_conjuncts(terms: &TermStore, root: TermId) -> Option<Vec<TermId>> {
    let TermData::Not(inner) = terms.get(root) else {
        return None;
    };
    match terms.get(*inner) {
        TermData::App(Symbol::Named(name), children)
            if name == "and" && children.len() <= MAX_CONJUNCTS =>
        {
            Some(children.clone())
        }
        _ => None,
    }
}

pub(super) fn decode_relation(terms: &TermStore, atom: TermId) -> Option<Relation> {
    let TermData::App(symbol @ Symbol::Named(name), args) = terms.get(atom) else {
        return None;
    };
    let [left, right] = args.as_slice() else {
        return None;
    };
    let (kind, semantic_args) = match name.as_str() {
        "=" => (RelationKind::Eq, [*left, *right]),
        "<=" => (RelationKind::Le, [*left, *right]),
        ">=" => (RelationKind::Le, [*right, *left]),
        "<" => (RelationKind::Lt, [*left, *right]),
        ">" => (RelationKind::Lt, [*right, *left]),
        _ => return None,
    };
    Some(Relation {
        kind,
        semantic_args,
        symbol: symbol.clone(),
    })
}

/// Match every real goal and every independently discharged source in one
/// bipartite graph.  Dummy rows may use only exact dischargeable equalities;
/// because rows and sources have equal cardinality, a perfect matching also
/// proves that no source conjunct was silently dropped.
pub(super) fn choose_sources_with_discharges(
    candidates: Vec<Vec<LiteralBridge>>,
    dischargeable_sources: &[usize],
    source_count: usize,
    discharge_count: usize,
) -> Option<(Vec<LiteralBridge>, Vec<usize>)> {
    if candidates.is_empty()
        || source_count > MAX_CONJUNCTS
        || candidates.len().checked_add(discharge_count)? != source_count
    {
        return None;
    }
    let mut candidate_sources: Vec<Vec<usize>> = candidates
        .iter()
        .map(|bridges| bridges.iter().map(|bridge| bridge.source_index).collect())
        .collect();
    for _ in 0..discharge_count {
        candidate_sources.push(dischargeable_sources.to_vec());
    }
    let assignment = distinct_source_assignment(&candidate_sources, source_count)?;
    let real_goal_count = candidates.len();
    let bridges = candidates
        .into_iter()
        .zip(assignment[..real_goal_count].iter().copied())
        .map(|(bridges, source)| {
            bridges
                .into_iter()
                .find(|bridge| bridge.source_index == source)
        })
        .collect::<Option<Vec<_>>>()?;
    Some((bridges, assignment[real_goal_count..].to_vec()))
}

/// Deterministic augmenting-path bipartite matching.  The caller caps both
/// partitions at 16, but this remains polynomial even on a Hall-deficient
/// adversarial graph instead of exploring every partial permutation.
fn distinct_source_assignment(
    candidates: &[Vec<usize>],
    source_count: usize,
) -> Option<Vec<usize>> {
    fn augment(
        goal: usize,
        candidates: &[Vec<usize>],
        seen_sources: &mut [bool],
        source_to_goal: &mut [Option<usize>],
        goal_to_source: &mut [Option<usize>],
    ) -> bool {
        for &source in &candidates[goal] {
            let Some(seen) = seen_sources.get_mut(source) else {
                return false;
            };
            if *seen {
                continue;
            }
            *seen = true;
            let previous = source_to_goal[source];
            if previous.is_some_and(|other| {
                !augment(
                    other,
                    candidates,
                    seen_sources,
                    source_to_goal,
                    goal_to_source,
                )
            }) {
                continue;
            }
            source_to_goal[source] = Some(goal);
            goal_to_source[goal] = Some(source);
            return true;
        }
        false
    }

    if candidates.is_empty() || candidates.iter().any(Vec::is_empty) {
        return None;
    }
    if candidates.len() > MAX_CONJUNCTS || source_count > MAX_CONJUNCTS {
        return None;
    }
    let mut source_to_goal = vec![None; source_count];
    let mut goal_to_source = vec![None; candidates.len()];
    for goal in 0..candidates.len() {
        let mut seen_sources = vec![false; source_count];
        if !augment(
            goal,
            candidates,
            &mut seen_sources,
            &mut source_to_goal,
            &mut goal_to_source,
        ) {
            return None;
        }
    }
    goal_to_source.into_iter().collect()
}

pub(super) fn has_duplicates(terms: &[TermId]) -> bool {
    terms
        .iter()
        .enumerate()
        .any(|(index, term)| terms[..index].contains(term))
}

pub(super) fn same_unique_set(left: &[TermId], right: &[TermId]) -> bool {
    left.len() == right.len()
        && !has_duplicates(left)
        && !has_duplicates(right)
        && left.iter().all(|term| right.contains(term))
}

#[cfg(test)]
mod tests {
    use ay_core::{Sort, Symbol, TermStore};

    use super::{
        distinct_source_assignment, packed_children, raw_negated_conjuncts, MAX_CONJUNCTS,
    };

    #[test]
    fn matching_reassigns_an_earlier_goal_deterministically() {
        assert_eq!(
            distinct_source_assignment(&[vec![0, 1], vec![0]], 2),
            Some(vec![1, 0])
        );
    }

    #[test]
    fn hall_deficient_candidate_graph_fails_closed() {
        let candidates: Vec<Vec<usize>> = (0..15).map(|_| (0..14).collect()).collect();
        assert_eq!(distinct_source_assignment(&candidates, 15), None);
    }

    #[test]
    fn oversized_packed_connectives_fail_closed() {
        let mut terms = TermStore::new();
        let children: Vec<_> = (0..=MAX_CONJUNCTS)
            .map(|index| terms.mk_var(format!("cap_{index}"), Sort::Bool))
            .collect();
        let packed = terms.mk_app(Symbol::named("or"), children.clone(), Sort::Bool);
        let conjunction = terms.mk_app(Symbol::named("and"), children, Sort::Bool);
        let negated = terms.mk_not_raw(conjunction);
        assert!(packed_children(&terms, packed).is_none());
        assert!(raw_negated_conjuncts(&terms, negated).is_none());
    }
}
