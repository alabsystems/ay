// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constructor-binding propagation with sealed assertion premises.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::TermId;

use super::CtorBinding;

pub(super) fn find(parent: &mut HashMap<TermId, TermId>, mut term: TermId) -> TermId {
    let mut path = Vec::new();
    while let Some(&next) = parent.get(&term) {
        if next == term {
            break;
        }
        path.push(term);
        term = next;
    }
    for node in path {
        parent.insert(node, term);
    }
    term
}

pub(super) fn union(parent: &mut HashMap<TermId, TermId>, lhs: TermId, rhs: TermId) {
    let lhs_root = find(parent, lhs);
    let rhs_root = find(parent, rhs);
    if lhs_root != rhs_root {
        parent.insert(lhs_root, rhs_root);
    }
}

pub(super) fn propagate_ctor_bindings(
    asserted_equalities: &[(TermId, TermId, TermId)],
    var_to_ctor: &mut HashMap<TermId, CtorBinding>,
    binding_premises: &mut HashMap<TermId, Vec<TermId>>,
) -> HashMap<TermId, TermId> {
    let mut parent = HashMap::default();
    for &(lhs, rhs, _) in asserted_equalities {
        union(&mut parent, lhs, rhs);
    }
    let mut direct_mappings: Vec<_> = var_to_ctor
        .iter()
        .map(|(term, binding)| (*term, binding.clone()))
        .collect();
    direct_mappings.sort_by_key(|(term, _)| term.0);
    for (term, ctor_info) in direct_mappings {
        let root = find(&mut parent, term);
        let class_equalities: Vec<TermId> = asserted_equalities
            .iter()
            .filter(|(lhs, rhs, _)| {
                find(&mut parent, *lhs) == root && find(&mut parent, *rhs) == root
            })
            .map(|(_, _, equality)| *equality)
            .collect();
        let direct_premises = binding_premises.get(&term).cloned().unwrap_or_default();
        let equality_sides: Vec<(TermId, TermId)> = asserted_equalities
            .iter()
            .map(|(lhs, rhs, _)| (*lhs, *rhs))
            .collect();
        for (lhs, rhs) in equality_sides {
            for candidate in [lhs, rhs] {
                if candidate == term || find(&mut parent, candidate) != root {
                    continue;
                }
                var_to_ctor.entry(candidate).or_insert_with(|| {
                    let (ctor, args, selectors, _) = ctor_info.clone();
                    (ctor, args, selectors, None)
                });
                binding_premises.entry(candidate).or_insert_with(|| {
                    let mut premises = direct_premises.clone();
                    premises.extend(class_equalities.iter().copied());
                    premises.dedup();
                    premises
                });
            }
        }
    }
    parent
}
