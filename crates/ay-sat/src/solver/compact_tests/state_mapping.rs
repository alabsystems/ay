// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::*;

#[test]
fn compact_remaps_proof_ids_for_surviving_variables() {
    let mut solver: Solver = Solver::new(4);

    // Force a non-identity remap: old vars 0, 2, 3 become new vars 0, 1, 2.
    solver.var_lifecycle.mark_eliminated(1);

    solver.record_unit_proof_id_for_lit(Literal::positive(Variable(1)), 11);
    solver.record_unit_proof_id_for_lit(Literal::positive(Variable(2)), 101);
    solver.record_level0_proof_id_for_lit(Literal::negative(Variable(1)), 22);
    solver.record_level0_proof_id_for_lit(Literal::negative(Variable(3)), 202);

    solver.compact();

    assert_eq!(solver.num_vars, 3);
    assert_eq!(
        solver.unit_proof_id,
        vec![0, 101, 0],
        "unit_proof_id must follow old var 2 -> new var 1 and drop eliminated var 1"
    );
    assert_eq!(
        solver.cold.level0_proof_id,
        vec![0, 0, 202],
        "level0_proof_id must follow old var 3 -> new var 2 and drop eliminated var 1"
    );
    assert_eq!(
        solver.unit_proof_sign,
        vec![0, 1, 0],
        "unit_proof_sign must follow unit_proof_id compaction"
    );
    assert_eq!(
        solver.cold.level0_proof_sign,
        vec![0, 0, -1],
        "level0_proof_sign must follow level0_proof_id compaction"
    );
}

/// Verify root_satisfied_saved is NOT remapped during compaction (#5250).
/// With external indices, conditioning saves entries in external space.
/// Compact does not remap them — they use stable external indices.
#[test]
fn compact_does_not_remap_root_satisfied_saved() {
    use crate::literal::{Literal, Variable};

    let mut solver: Solver = Solver::new(4);

    // Eliminate vars 1 and 3 → map: {0→0, 1→UNMAPPED, 2→1, 3→UNMAPPED}
    solver.var_lifecycle.mark_eliminated(1);
    solver.var_lifecycle.mark_substituted(3);

    // Simulate conditioning having saved a root-satisfied clause
    // in external space (as condition.rs now does via externalize_lits).
    // Before compaction, external = internal (identity), so these literals
    // represent external vars 0, 2, 1.
    let saved_clause = vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(2)),
        Literal::positive(Variable(1)), // eliminated external var
    ];
    solver.cold.root_satisfied_saved.push(saved_clause.clone());

    solver.compact();

    assert_eq!(solver.num_vars, 2);
    assert_eq!(solver.cold.root_satisfied_saved.len(), 1);

    // root_satisfied_saved should be UNCHANGED (external indices, not remapped)
    let unchanged = &solver.cold.root_satisfied_saved[0];
    assert_eq!(unchanged[0], saved_clause[0]);
    assert_eq!(unchanged[1], saved_clause[1]);
    assert_eq!(unchanged[2], saved_clause[2]);
}

/// Verify reconstruction entries are NOT remapped during compaction (#5250).
///
/// Old internal var 2 survives compaction as new internal var 1. The
/// reconstruction stack is in stable external space, so its witness and clause
/// must stay on external var 2 rather than being rewritten to internal var 1.
#[test]
fn compact_preserves_reconstruction_external_indices_after_internal_renumbering() {
    use crate::literal::{Literal, Variable};
    use crate::reconstruct::ReconstructionStep;

    let mut solver: Solver = Solver::new(4);
    let ext_witness = Literal::positive(Variable(2));
    let ext_guard = Literal::positive(Variable(0));

    solver
        .inproc
        .reconstruction
        .push_witness_clause(vec![ext_witness], vec![ext_witness, ext_guard]);

    // Eliminate vars 1 and 3 so old internal var 2 is compacted to internal var 1.
    solver.var_lifecycle.mark_eliminated(1);
    solver.var_lifecycle.mark_substituted(3);

    solver.compact();

    assert_eq!(solver.num_vars, 2);
    assert_eq!(
        solver.cold.e2i[2], 1,
        "external var 2 should now map to compacted internal var 1"
    );
    assert_eq!(
        solver.cold.i2e[1], 2,
        "compacted internal var 1 should round-trip to external var 2"
    );

    let steps = solver.inproc.reconstruction.steps_ref();
    assert_eq!(steps.len(), 1);
    let ReconstructionStep::Witness(wc) = &steps[0] else {
        panic!("expected witness reconstruction step");
    };
    assert_eq!(
        wc.witness[0], ext_witness,
        "witness literal must remain in external space across compaction"
    );
    assert_eq!(
        wc.clause[0], ext_witness,
        "clause literal must remain in external space across compaction"
    );

    let mut ext_model = vec![false; solver.cold.e2i.len()];
    solver.inproc.reconstruction.reconstruct(&mut ext_model);

    assert!(
        ext_model[2],
        "reconstruction must flip external var 2, not compacted internal var 1"
    );
    assert!(
        !ext_model[1],
        "internal var index 1 must not be interpreted as the reconstruction variable"
    );
}
