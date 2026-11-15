// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn dirty_pending_and_incomplete_merge_state_terminally_refuse_without_replay() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let values = fixture.values();
    for kind in 0..4 {
        let mut solver = fixture.solver();
        match kind {
            0 => solver.dirty = true,
            1 => solver.var_layer_dirty = true,
            2 => solver
                .pending_registered_equalities
                .push(fixture.equalities[0]),
            _ => {
                solver.array_var_merge_undo.pop();
            }
        }
        let before = (
            solver.dirty,
            solver.var_layer_dirty,
            solver.pending_registered_equalities.len(),
        );
        let original = owner(end, 1_000_000, 128 << 20);
        assert!(original
            .with_work(|w| solver.try_extract_prepared_flat_model_with_budget(&values, w))
            .is_err());
        assert_eq!(
            (
                solver.dirty,
                solver.var_layer_dirty,
                solver.pending_registered_equalities.len()
            ),
            before
        );
        assert!(original.clone().check().is_err());
    }
}

#[test]
fn malformed_store_cache_dead_children_and_cycles_refuse_before_model_publication() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let values = fixture.values();
    for kind in 0..3 {
        let mut solver = fixture.solver();
        let data = match kind {
            0 => (fixture.bases[0], TermId(u32::MAX), fixture.writes[0]),
            1 => (fixture.stores[1], fixture.indices[0], fixture.writes[0]),
            _ => (fixture.bases[1], fixture.indices[0], fixture.writes[0]),
        };
        solver.store_cache.insert(fixture.stores[0], data);
        let original = owner(end, 1_000_000, 128 << 20);
        assert!(original
            .with_work(|w| solver.try_extract_prepared_flat_model_with_budget(&values, w))
            .is_err());
        assert!(original.clone().check().is_err());
    }
}

#[test]
fn unsupported_domains_nested_arrays_and_opaque_functions_have_no_legacy_fallback() {
    let end = Instant::now() + Duration::from_secs(20);
    for kind in 0..4 {
        let mut terms = TermStore::new();
        let bv = Sort::BitVec(ay_core::BitVecSort { width: 8 });
        match kind {
            0 => {
                terms.mk_var("integer", Sort::Int);
            }
            1 => {
                terms.mk_var(
                    "nested",
                    Sort::array(bv.clone(), Sort::array(bv.clone(), bv.clone())),
                );
            }
            2 => {
                let value = terms.mk_var("v", bv.clone());
                terms.mk_app(Symbol::named("user-function"), [value], bv.clone());
            }
            _ => {
                terms.mk_var("zero-width", Sort::BitVec(ay_core::BitVecSort { width: 0 }));
            }
        }
        let mut solver = ArraySolver::new(&terms);
        solver.populate_caches();
        solver.rebuild_assign_indices();
        let original = owner(end, 1_000_000, 128 << 20);
        assert!(original
            .with_work(
                |w| solver.try_extract_prepared_flat_model_with_budget(&HashMap::default(), w)
            )
            .is_err());
        assert!(original.clone().check().is_err());
    }
}

#[test]
fn stale_cached_class_duplicates_and_nonarray_members_are_not_consumed() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let values = fixture.values();
    for cached in [false, true] {
        let mut solver = fixture.solver();
        if cached {
            solver.build_equiv_class_cache();
            let member = solver.equiv_classes[0][0];
            solver.equiv_classes[0].push(member);
        } else {
            solver.eq_adj.insert(fixture.indices[0], Vec::new());
            solver.equiv_class_cache_version = None;
        }
        let original = owner(end, 1_000_000, 128 << 20);
        assert!(original
            .with_work(|w| solver.try_extract_prepared_flat_model_with_budget(&values, w))
            .is_err());
        assert!(original.clone().check().is_err());
    }
}
