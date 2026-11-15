// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Frozen pre-inversion candidate algorithm: global constant class pairs,
//! followed by the existing index-block restriction and final sorted set.
//! Deliberately does not call the new add_pairs helper or its inverted index.

use super::*;

pub(super) fn pairs(solver: &ArraySolver<'_>) -> Vec<(TermId, TermId)> {
    let mut selects_by_class: HashMap<TermId, Vec<TermId>> = HashMap::default();
    for &select in solver.select_cache.keys() {
        selects_by_class
            .entry(solver.equiv_class_representative(select))
            .or_default()
            .push(select);
    }
    for selects in selects_by_class.values_mut() {
        selects.sort_unstable_by_key(|term| term.0);
        selects.dedup();
    }
    let mut class_pairs = HashSet::default();
    for &(lhs, rhs) in &solver.diseq_set {
        let left = solver.equiv_class_representative(lhs);
        let right = solver.equiv_class_representative(rhs);
        if selects_by_class.contains_key(&left) && selects_by_class.contains_key(&right) {
            class_pairs.insert(ArraySolver::ordered_pair(left, right));
        }
    }
    let mut constants = Vec::new();
    for (&class, selects) in &selects_by_class {
        let constant = solver
            .get_equiv_class(selects[0])
            .into_iter()
            .find_map(|term| match solver.terms.get(term) {
                TermData::Const(value) => Some(value.clone()),
                _ => None,
            });
        if let Some(value) = constant {
            constants.push((class, value));
        }
    }
    constants.sort_unstable_by_key(|(class, _)| class.0);
    for i in 0..constants.len() {
        for j in i + 1..constants.len() {
            if constants[i].1 != constants[j].1 {
                class_pairs.insert(ArraySolver::ordered_pair(constants[i].0, constants[j].0));
            }
        }
    }
    let mut indices: Vec<_> = solver
        .select_cache
        .values()
        .map(|&(_, index)| index)
        .collect();
    indices.sort_unstable_by_key(|term| term.0);
    indices.dedup();
    let partition = solver.index_conflict_partition(&indices);
    let mut class_groups: HashMap<TermId, HashMap<TermId, Vec<TermId>>> = HashMap::default();
    for (&class, selects) in &selects_by_class {
        let mut groups: HashMap<TermId, Vec<TermId>> = HashMap::default();
        for &select in selects {
            if let Some(&(_, index)) = solver.select_cache.get(&select) {
                if let Some(&block) = partition.get(&index) {
                    groups.entry(block).or_default().push(select);
                }
            }
        }
        class_groups.insert(class, groups);
    }
    let mut pairs = HashSet::default();
    for &(left, right) in &class_pairs {
        let (left, right) = (&class_groups[&left], &class_groups[&right]);
        let (small, large) = if left.len() <= right.len() {
            (left, right)
        } else {
            (right, left)
        };
        for (block, first) in small {
            let Some(second) = large.get(block) else {
                continue;
            };
            for &a in first {
                for &b in second {
                    if a != b {
                        pairs.insert(ArraySolver::ordered_pair(a, b));
                    }
                }
            }
        }
    }
    let mut pairs: Vec<_> = pairs.into_iter().collect();
    pairs.sort_unstable_by_key(|&(left, right)| (left.0, right.0));
    pairs
}
