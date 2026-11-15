// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn orphan_scalar_vertices_still_refuse_in_both_cache_states() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Pinned::new(Sort::bitvec(8));
    let values = fixture.values();
    for cached in [false, true] {
        let mut source = fixture.solver();
        source.eq_adj.insert(fixture.indices[0], Vec::new());
        if cached {
            source.build_equiv_class_cache();
        }
        refused(&source, &values, end);
        assert!(source.eq_adj[&fixture.indices[0]].is_empty());
    }
}

#[test]
fn dead_or_mixed_scalar_edges_and_dead_origins_never_publish_partial_data() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Pinned::new(Sort::bitvec(8));
    let values = fixture.values();
    for kind in 0..3 {
        let mut source = fixture.solver();
        let row = source
            .eq_adj
            .get_mut(&fixture.reads[0])
            .unwrap()
            .first_mut()
            .unwrap();
        match kind {
            0 => row.0 = TermId(u32::MAX),
            1 => row.0 = fixture.base,
            _ => row.1 = TermId(u32::MAX),
        }
        refused(&source, &values, end);
    }
}

#[test]
fn stale_false_assignment_or_forged_external_reason_is_terminal() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Pinned::new(Sort::Bool);
    let values = fixture.values();
    for external in [false, true] {
        let mut source = fixture.solver();
        if external {
            source.eq_adj.get_mut(&fixture.reads[0]).unwrap()[0].1 = TermId::SENTINEL;
            assert!(source.external_eqs.is_empty());
        } else {
            source.assigns.insert(fixture.roots[1], false);
            assert!(!source.assign_dirty); // Deliberately malformed current-origin fixture.
        }
        refused(&source, &values, end);
    }
}

#[test]
fn cached_extra_scalar_member_without_an_actual_vertex_refuses() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Pinned::new(Sort::bitvec(64));
    let values = fixture.values();
    let mut source = fixture.solver();
    source.build_equiv_class_cache();
    assert!(!source.eq_adj.contains_key(&fixture.indices[0]));
    let class = source
        .equiv_classes
        .iter_mut()
        .find(|class| class.contains(&fixture.value))
        .unwrap();
    class.push(fixture.indices[0]);
    refused(&source, &values, end);
}

#[test]
fn registered_scalar_endpoints_and_reasons_cannot_escape_the_current_scope() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Pinned::new(Sort::bitvec(8));
    let values = fixture.values();
    for term in [fixture.value, fixture.roots[1]] {
        let mut source = ArraySolver::new(&fixture.terms);
        source.enable_registered_atom_scope(true);
        for &root in &fixture.roots {
            source.register_atom(root);
            source.assert_literal(root, true);
        }
        source.populate_caches();
        source.rebuild_assign_indices();
        assert!(source.registered_term_scope.as_mut().unwrap().remove(&term));
        refused(&source, &values, end);
    }
}
