// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::collections::BTreeMap;

const MAX_STORE_PERMUTATION_PREMISES: usize = 512;
const MAX_GROUP_EQUALITIES: usize = MAX_STORE_PERMUTATION_PREMISES + 1;
const MAX_DIRECT_WORK: usize = (MAX_STORE_PERMUTATION_PREMISES + 1)
    * (MAX_STORE_PERMUTATION_PREMISES + 1)
    + MAX_GROUP_EQUALITIES;

type NegatedEquality = (TermId, TermId);

enum PremiseGroup {
    Equalities(Vec<NegatedEquality>),
    TooMany,
}

struct PremiseIndex(BTreeMap<Sort, PremiseGroup>);

impl PremiseIndex {
    fn build(terms: &TermStore, authored: &[TermId]) -> Self {
        let mut groups = BTreeMap::new();
        for &root in authored {
            let Some((_, equality)) = negated_equality(terms, root) else {
                continue;
            };
            let Some((left, right)) = decode_eq_local(terms, equality) else {
                continue;
            };
            if terms.sort(left) != terms.sort(right) {
                continue;
            }
            push_group(&mut groups, terms.sort(left).clone(), (root, equality));
        }
        Self(groups)
    }

    fn get(&self, sort: &Sort) -> Option<&[NegatedEquality]> {
        match self.0.get(sort) {
            Some(PremiseGroup::Equalities(equalities)) => Some(equalities),
            Some(PremiseGroup::TooMany) => None,
            None => Some(&[]),
        }
    }
}

pub(super) fn try_reconstruct(exec: &mut Executor, proof: &mut Proof, authored: &[TermId]) -> bool {
    let premise_index = PremiseIndex::build(&exec.ctx.terms, authored);
    let mut work = 0_usize;
    for &array_root in authored {
        let Some((_, array_equality)) = negated_equality(&exec.ctx.terms, array_root) else {
            continue;
        };
        let Some(index_sort) = array_index_sort(&exec.ctx.terms, array_equality) else {
            continue;
        };
        let Some(group) = premise_index.get(index_sort) else {
            continue;
        };
        if !charge_work(&mut work, group.len()) {
            return false;
        }
        let mut premises: Vec<_> = group
            .iter()
            .copied()
            .filter(|&(root, _)| root != array_root)
            .collect();
        if premises.len() > MAX_STORE_PERMUTATION_PREMISES
            || !charge_matcher_work(&mut work, premises.len())
        {
            if work > MAX_DIRECT_WORK {
                return false;
            }
            continue;
        }
        let Some(candidate) = candidate_for(exec, array_root, array_equality, &mut premises) else {
            continue;
        };
        if exec.commit_if_strictly_checked(proof, candidate, authored) {
            return true;
        }
    }
    false
}

fn negated_equality(terms: &TermStore, root: TermId) -> Option<NegatedEquality> {
    let TermData::Not(inner) = terms.get(root) else {
        return None;
    };
    decode_eq_local(terms, *inner).map(|_| (root, *inner))
}

fn array_index_sort(terms: &TermStore, equality: TermId) -> Option<&Sort> {
    let (left, right) = decode_eq_local(terms, equality)?;
    let Sort::Array(array_sort) = terms.sort(left) else {
        return None;
    };
    (terms.sort(left) == terms.sort(right)).then_some(&array_sort.index_sort)
}

fn charge_matcher_work(work: &mut usize, premises: usize) -> bool {
    let width = premises.saturating_add(1);
    let cost = width.saturating_mul(width);
    charge_work(work, cost)
}

fn charge_work(work: &mut usize, cost: usize) -> bool {
    *work = (*work).saturating_add(cost);
    *work <= MAX_DIRECT_WORK
}

fn candidate_for(
    exec: &mut Executor,
    array_root: TermId,
    array_equality: TermId,
    premises: &mut Vec<NegatedEquality>,
) -> Option<Proof> {
    shrink_to_schema(&exec.ctx.terms, premises, array_equality)?;
    Some(build_candidate(array_root, array_equality, premises))
}

fn clause_for(premises: &[NegatedEquality], array_equality: TermId) -> Vec<TermId> {
    let mut clause: Vec<_> = premises.iter().map(|&(_, equality)| equality).collect();
    clause.push(array_equality);
    clause
}

fn shrink_to_schema(
    terms: &TermStore,
    premises: &mut Vec<NegatedEquality>,
    array_equality: TermId,
) -> Option<()> {
    if ay_proof::recognize_array_theory_lemma(terms, &clause_for(premises, array_equality))
        != Some(TheoryLemmaKind::ArrayStorePermutation)
    {
        return None;
    }
    let mut position = 0;
    while position < premises.len() {
        let mut trimmed = premises.clone();
        let _ = trimmed.remove(position);
        if ay_proof::recognize_array_theory_lemma(terms, &clause_for(&trimmed, array_equality))
            == Some(TheoryLemmaKind::ArrayStorePermutation)
        {
            *premises = trimmed;
        } else {
            position += 1;
        }
    }
    Some(())
}

fn build_candidate(
    array_root: TermId,
    array_equality: TermId,
    premises: &[NegatedEquality],
) -> Proof {
    let clause = clause_for(premises, array_equality);
    let mut candidate = Proof::new();
    let index_assumes: Vec<_> = premises
        .iter()
        .map(|&(root, _)| candidate.add_assume(root, None))
        .collect();
    let array_assume = candidate.add_assume(array_root, None);
    let mut current = candidate.add_theory_lemma_with_kind(
        "array",
        clause.clone(),
        TheoryLemmaKind::ArrayStorePermutation,
    );
    let mut remaining = clause;
    for (&(_, equality), &assume) in premises.iter().zip(&index_assumes) {
        remaining.retain(|&literal| literal != equality);
        current = candidate.add_resolution(remaining.clone(), equality, current, assume);
    }
    candidate.add_resolution(Vec::new(), array_equality, current, array_assume);
    candidate
}

fn push_group(groups: &mut BTreeMap<Sort, PremiseGroup>, sort: Sort, equality: NegatedEquality) {
    let entry = groups
        .entry(sort)
        .or_insert_with(|| PremiseGroup::Equalities(Vec::new()));
    match entry {
        PremiseGroup::Equalities(equalities) if equalities.len() < MAX_GROUP_EQUALITIES => {
            equalities.push(equality);
        }
        PremiseGroup::Equalities(_) => *entry = PremiseGroup::TooMany,
        PremiseGroup::TooMany => {}
    }
}
