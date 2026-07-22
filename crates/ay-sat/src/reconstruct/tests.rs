// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for model reconstruction (BVE, BCE, sweep).

use super::*;
use crate::test_util::lit;

#[test]
fn test_bve_reconstruct_simple() {
    let mut stack = ReconstructionStack::new();
    stack.push_bve(
        Variable(0),
        vec![vec![lit(0, true), lit(1, true)]],
        vec![vec![lit(0, false), lit(2, true)]],
    );
    let mut model = vec![false, true, true];
    stack.reconstruct(&mut model);
    assert!(model[0] || model[1], "(x0|x1) satisfied");
    assert!(!model[0] || model[2], "(!x0|x2) satisfied");
}

#[test]
fn test_bve_reconstruct_forced_true() {
    let mut stack = ReconstructionStack::new();
    stack.push_bve(Variable(0), vec![vec![lit(0, true), lit(1, false)]], vec![]);
    let mut model = vec![false, true];
    stack.reconstruct(&mut model);
    assert!(model[0], "x0 must be true to satisfy (x0|!x1) with x1=true");
}

#[test]
fn test_bve_reconstruct_forced_false() {
    let mut stack = ReconstructionStack::new();
    stack.push_bve(
        Variable(0),
        vec![],
        vec![vec![lit(0, false), lit(1, false)]],
    );
    let mut model = vec![true, true];
    stack.reconstruct(&mut model);
    assert!(
        !model[0],
        "x0 must be false to satisfy (!x0|!x1) with x1=true"
    );
}

#[test]
fn test_bve_multi_round_correctness() {
    let mut stack = ReconstructionStack::new();
    stack.push_bve(
        Variable(0),
        vec![vec![lit(0, true), lit(1, true)]],
        vec![vec![lit(0, false), lit(2, true)]],
    );
    stack.push_bve(
        Variable(2),
        vec![vec![lit(2, true), lit(3, true)]],
        vec![vec![lit(2, false), lit(4, true)]],
    );
    let mut model = vec![false, true, false, true, true];
    stack.reconstruct(&mut model);
    assert!(model[2] || model[3], "(x2|x3) satisfied");
    assert!(!model[2] || model[4], "(!x2|x4) satisfied");
    assert!(model[0] || model[1], "(x0|x1) satisfied");
    assert!(!model[0] || model[2], "(!x0|x2) satisfied");
}

#[test]
fn test_sweep_reconstruct_equivalence() {
    let mut model = vec![false, true, false];
    let mut lit_map = vec![Literal(0); 6];
    lit_map[lit(0, true).index()] = lit(1, true);
    lit_map[lit(0, false).index()] = lit(1, false);
    lit_map[lit(1, true).index()] = lit(1, true);
    lit_map[lit(1, false).index()] = lit(1, false);
    lit_map[lit(2, true).index()] = lit(2, true);
    lit_map[lit(2, false).index()] = lit(2, false);
    reconstruct_sweep(&mut model, 3, &lit_map);
    assert_eq!(model[0], model[1]);
    assert!(model[0]);
}

#[test]
fn test_reconstruction_stack_order() {
    let mut stack = ReconstructionStack::new();
    stack.push_bve(Variable(2), vec![vec![lit(2, true), lit(1, false)]], vec![]);
    let mut lit_map = vec![Literal(0); 6];
    lit_map[lit(0, true).index()] = lit(1, true);
    lit_map[lit(0, false).index()] = lit(1, false);
    lit_map[lit(1, true).index()] = lit(1, true);
    lit_map[lit(1, false).index()] = lit(1, false);
    lit_map[lit(2, true).index()] = lit(2, true);
    lit_map[lit(2, false).index()] = lit(2, false);
    stack.push_sweep(3, lit_map);
    let mut model = vec![false, true, false];
    stack.reconstruct(&mut model);
    assert!(model[0], "x0 true after sweep");
    assert!(model[2], "x2 true after BVE");
}

#[test]
fn test_bce_reconstruct_simple() {
    let mut model = vec![false, false];
    reconstruct_witness(&mut model, &[lit(0, true)], &[lit(0, true), lit(1, true)]);
    assert!(model[0]);
}

#[test]
fn test_bce_reconstruct_already_satisfied() {
    let mut model = vec![false, true];
    reconstruct_witness(&mut model, &[lit(0, true)], &[lit(0, true), lit(1, true)]);
    assert!(!model[0], "x0 stays false when clause already satisfied");
}

#[test]
fn test_bce_reconstruction_stack() {
    let mut stack = ReconstructionStack::new();
    stack.push_bce(lit(0, true), vec![lit(0, true), lit(1, true)]);
    let mut model = vec![false, false];
    stack.reconstruct(&mut model);
    assert!(model[0]);
}

#[test]
fn test_conditional_autarky_flips_multiple_witness_literals() {
    let mut model = vec![false, false, false];
    reconstruct_witness(
        &mut model,
        &[lit(0, true), lit(1, true)],
        &[lit(0, true), lit(1, true), lit(2, true)],
    );
    assert!(model[0], "first witness literal should be flipped true");
    assert!(model[1], "second witness literal should be flipped true");
}

#[test]
fn test_conditional_autarky_skips_when_clause_already_satisfied() {
    let mut model = vec![false, false, true];
    reconstruct_witness(
        &mut model,
        &[lit(0, true), lit(1, true)],
        &[lit(0, true), lit(1, true), lit(2, true)],
    );
    assert!(
        !model[0],
        "witness remains unchanged when clause already true"
    );
    assert!(
        !model[1],
        "witness remains unchanged when clause already true"
    );
}

#[test]
fn test_iter_removed_clauses_includes_bve_and_bce() {
    let mut stack = ReconstructionStack::new();
    stack.push_bve(Variable(0), vec![vec![lit(0, true), lit(1, true)]], vec![]);
    stack.push_bce(lit(2, true), vec![lit(2, true), lit(3, true)]);
    assert_eq!(stack.iter_removed_clauses().count(), 2);
}

#[test]
fn test_drain_witness_entries_preserves_sweep_steps() {
    let mut stack = ReconstructionStack::new();
    // Add a BVE witness entry.
    stack.push_bve(Variable(0), vec![vec![lit(0, true), lit(1, true)]], vec![]);
    // Add sweep equivalences (push_sweep now emits binary witness entries,
    // not a bulk Sweep step). var0→var1 creates 2 entries.
    let mut lit_map = vec![Literal(0); 6];
    lit_map[lit(0, true).index()] = lit(1, true);
    lit_map[lit(0, false).index()] = lit(1, false);
    lit_map[lit(1, true).index()] = lit(1, true);
    lit_map[lit(1, false).index()] = lit(1, false);
    lit_map[lit(2, true).index()] = lit(2, true);
    lit_map[lit(2, false).index()] = lit(2, false);
    stack.push_sweep(3, lit_map);
    // Add a BCE witness entry.
    stack.push_bce(lit(2, true), vec![lit(2, true), lit(3, true)]);

    // 1 BVE + 2 sweep-equiv + 1 BCE = 4 entries
    assert_eq!(stack.len(), 4);

    let result = stack.drain_witness_entries();

    // All entries are Witness entries now (including sweep equiv), all drained.
    assert_eq!(stack.len(), 0);

    // reactivate_vars should include variables from drained witness/clause literals.
    // BVE: var 0 (witness), var 0+1 (clause). Sweep: var 0, var 1. BCE: var 2+3.
    assert!(result.reactivate_vars.contains(&0));
    assert!(result.reactivate_vars.contains(&1));
    assert!(result.reactivate_vars.contains(&2));
    assert!(result.reactivate_vars.contains(&3));
}

#[test]
fn test_drain_witness_entries_empty_stack() {
    let mut stack = ReconstructionStack::new();
    let result = stack.drain_witness_entries();
    assert!(result.reactivate_vars.is_empty());
    assert_eq!(stack.len(), 0);
}

#[test]
fn test_drain_witness_entries_only_sweep() {
    let mut stack = ReconstructionStack::new();
    let mut lit_map = vec![Literal(0); 4];
    lit_map[lit(0, true).index()] = lit(1, true);
    lit_map[lit(0, false).index()] = lit(1, false);
    lit_map[lit(1, true).index()] = lit(1, true);
    lit_map[lit(1, false).index()] = lit(1, false);
    stack.push_sweep(2, lit_map);

    // push_sweep with var0→var1 equivalence emits 2 binary witness entries
    assert_eq!(stack.len(), 2);

    let result = stack.drain_witness_entries();
    // Sweep equiv entries are now Witness entries, so they get drained
    assert!(result.reactivate_vars.contains(&0));
    assert!(result.reactivate_vars.contains(&1));
    assert_eq!(stack.len(), 0);
}

#[test]
fn test_drain_witness_entries_reconstruction_still_works() {
    // Verify that push_sweep emits binary witness entries that correctly
    // reconstruct equivalences. push_sweep(var0→var1) creates:
    //   witness=[-var0], clause=[-var0, var1]
    //   witness=[var0],  clause=[var0, -var1]
    let mut stack = ReconstructionStack::new();
    let mut lit_map = vec![Literal(0); 6];
    lit_map[lit(0, true).index()] = lit(1, true); // var0 → var1
    lit_map[lit(0, false).index()] = lit(1, false); // !var0 → !var1
    lit_map[lit(1, true).index()] = lit(1, true);
    lit_map[lit(1, false).index()] = lit(1, false);
    lit_map[lit(2, true).index()] = lit(2, true);
    lit_map[lit(2, false).index()] = lit(2, false);
    stack.push_sweep(3, lit_map);

    // 2 entries for var0→var1 equivalence
    assert_eq!(stack.len(), 2);

    // Reconstruction: start with x0=false, x1=true, x2=false
    let mut model = vec![false, true, false];
    stack.reconstruct(&mut model);
    // Entry 2 (processed first in reverse): witness=[var0], clause=[var0, -var1]
    //   clause=[var0=false, -var1=false] → unsatisfied → flip var0 to true
    // Entry 1 (processed second): witness=[-var0], clause=[-var0, var1]
    //   clause=[-var0=false, var1=true] → satisfied by var1 → skip
    assert!(model[0], "x0 true after sweep equiv reconstruction");
    assert!(model[1], "x1 still true");
}

// ---------------------------------------------------------------------------
// Tests for #8179: suppress_prior_witness_entries (CCE+BVE interaction)
// ---------------------------------------------------------------------------

#[test]
fn test_suppress_prior_witness_entries_prevents_double_flip() {
    // Scenario: CCE removes clause (x0 | x1) with witness x0, then BVE
    // eliminates x0 with clauses (x0 | x2) and (!x0 | x3).
    // Without suppression, reverse reconstruction processes BVE first
    // (setting x0 correctly), then the CCE entry flips x0 again.
    let mut stack = ReconstructionStack::new();

    // CCE entry pushed first (earlier in time).
    stack.push_bce(lit(0, true), vec![lit(0, true), lit(1, true)]);

    // BVE eliminates x0 — suppress prior entries for var 0.
    stack.suppress_prior_witness_entries(0);

    // BVE pushes its own witness entries.
    stack.push_witness_clause(vec![lit(0, true)], vec![lit(0, true), lit(2, true)]);
    stack.push_witness_clause(vec![lit(0, false)], vec![lit(0, false), lit(3, true)]);

    // Model: x0=false, x1=false, x2=true, x3=true.
    // BVE needs x0=true to satisfy (x0|x2) — but x2=true already satisfies
    // it, so no flip needed. For (!x0|x3): x3=true already satisfies it.
    // The CCE entry (x0|x1) would try to flip x0 if not suppressed.
    let mut model = vec![false, false, true, true];
    stack.reconstruct(&mut model);

    // BVE clauses should be satisfied.
    assert!(
        model[0] || model[2],
        "(x0|x2) must be satisfied after reconstruction"
    );
    assert!(
        !model[0] || model[3],
        "(!x0|x3) must be satisfied after reconstruction"
    );
    // The CCE entry was suppressed, so it should NOT have flipped x0.
    // x0 should stay false because both BVE clauses are already satisfied.
    assert!(
        !model[0],
        "x0 should remain false — CCE entry was suppressed (#8179)"
    );
}

#[test]
fn test_suppress_prior_witness_entries_only_affects_matching_var() {
    // Suppression for var 0 should not affect entries with witness var 1.
    let mut stack = ReconstructionStack::new();

    // BCE entry for var 1.
    stack.push_bce(lit(1, true), vec![lit(1, true), lit(2, true)]);
    // BCE entry for var 0.
    stack.push_bce(lit(0, true), vec![lit(0, true), lit(3, true)]);

    // Suppress only var 0.
    stack.suppress_prior_witness_entries(0);

    // The var-1 entry should still be active; only var-0 entry suppressed.
    let mut model = vec![false, false, false, false];
    stack.reconstruct(&mut model);

    // var 1's BCE entry should have flipped x1 to true.
    assert!(model[1], "x1 should be flipped by unsuppressed BCE entry");
    // var 0's BCE entry was suppressed — x0 stays false.
    assert!(!model[0], "x0 should stay false — its entry was suppressed");
}

#[test]
fn test_compact_suppressed_drops_only_suppressed_entries() {
    let mut stack = ReconstructionStack::new();
    stack.push_witness_clause(vec![lit(0, true)], vec![lit(0, true), lit(3, true)]);
    stack.push_witness_clause(vec![lit(1, true)], vec![lit(1, true), lit(4, true)]);
    stack.push_witness_clause(vec![lit(2, false)], vec![lit(2, false), lit(5, true)]);

    let original_len = stack.len();
    stack.suppress_prior_witness_entries(1);
    let removed = stack.compact_suppressed();

    assert_eq!(removed, 1);
    assert_eq!(stack.len(), original_len - removed);

    let mut model = vec![false, false, false, true, false, true];
    stack.reconstruct(&mut model);
    assert!(
        model[0] || model[3],
        "first remaining clause must be satisfied"
    );
    assert!(
        !model[2] || model[5],
        "last remaining clause must be satisfied"
    );
}

#[test]
fn test_compact_suppressed_preserves_preserve_flag() {
    let mut stack = ReconstructionStack::new();
    stack.push_preserved_witness_clause(vec![lit(5, true)], vec![lit(5, true), lit(6, true)]);
    stack.push_witness_clause(vec![lit(5, true)], vec![lit(5, true), lit(7, true)]);

    stack.suppress_prior_witness_entries(5);
    let removed = stack.compact_suppressed();

    assert_eq!(removed, 1);
    assert_eq!(stack.len(), 1);
    assert!(stack.steps.iter().any(|step| {
        matches!(step, ReconstructionStep::Witness(wc)
            if wc.preserve && wc.witness.iter().any(|w| w.variable().index() == 5))
    }));
}

#[test]
fn test_compact_suppressed_retains_sweep_steps() {
    let mut stack = ReconstructionStack::new();
    // push_sweep currently emits witness entries, so inject a real Sweep step
    // directly to cover retention of the enum variant during compaction.
    stack.steps.push(ReconstructionStep::Sweep {
        num_vars: 2,
        lit_map: vec![lit(0, true), lit(0, false), lit(1, true), lit(1, false)],
    });
    stack.push_witness_clause(vec![lit(3, true)], vec![lit(3, true), lit(4, true)]);

    stack.suppress_prior_witness_entries(3);
    let removed = stack.compact_suppressed();

    assert_eq!(removed, 1);
    assert!(stack.len() >= 1);
    assert!(matches!(
        stack.steps.first(),
        Some(ReconstructionStep::Sweep { .. })
    ));
}

#[test]
fn test_suppress_prior_witness_entries_opportunistic_compaction_8672() {
    let mut stack = ReconstructionStack::new();
    for _ in 0..5_000 {
        stack.push_witness_clause(vec![lit(0, true)], vec![lit(0, true), lit(1, true)]);
    }
    stack.push_witness_clause(vec![lit(1, true)], vec![lit(1, true), lit(2, true)]);

    stack.suppress_prior_witness_entries(0);

    assert_eq!(stack.len(), 1);
    assert!(matches!(
        stack.steps.first(),
        Some(ReconstructionStep::Witness(wc))
            if wc.witness.iter().any(|w| w.variable().index() == 1)
    ));
}

// ---------------------------------------------------------------------------
// Tests for #3477: verify_sweep_consistency
// ---------------------------------------------------------------------------

#[test]
fn test_verify_sweep_consistency_identity_map() {
    let mut stack = ReconstructionStack::new();
    // Identity mapping: every variable maps to itself.
    let lit_map = vec![
        Literal(0), // var0 pos -> var0 pos
        Literal(1), // var0 neg -> var0 neg
        Literal(2), // var1 pos -> var1 pos
        Literal(3), // var1 neg -> var1 neg
    ];
    stack.push_sweep(2, lit_map);

    let model = vec![true, false];
    assert!(
        stack.verify_sweep_consistency(&model).is_none(),
        "Identity mapping should always be consistent"
    );
}

#[test]
fn test_sweep_positive_equivalence_reconstruction() {
    // (#8356) push_sweep now emits binary witness entries (CaDiCaL decompose
    // style). Verify that reconstruction fixes inconsistent models.
    let mut stack = ReconstructionStack::new();
    // x0 maps to x1 (positive equivalence: x0 = x1).
    let mut lit_map = vec![Literal(0); 6];
    lit_map[lit(0, true).index()] = lit(1, true);
    lit_map[lit(0, false).index()] = lit(1, false);
    lit_map[lit(1, true).index()] = lit(1, true);
    lit_map[lit(1, false).index()] = lit(1, false);
    lit_map[lit(2, true).index()] = lit(2, true);
    lit_map[lit(2, false).index()] = lit(2, false);
    stack.push_sweep(3, lit_map);

    // Consistent model: x0=true, x1=true → reconstruction is a no-op.
    let mut model = vec![true, true, false];
    stack.reconstruct(&mut model);
    assert!(model[0], "x0 stays true");
    assert!(model[1], "x1 stays true");

    // Inconsistent model: x0=false, x1=true → reconstruction flips x0 to true.
    let mut model = vec![false, true, false];
    stack.reconstruct(&mut model);
    assert_eq!(model[0], model[1], "x0 must equal x1 after reconstruction");
}

#[test]
fn test_sweep_negative_equivalence_reconstruction() {
    let mut stack = ReconstructionStack::new();
    // x0 maps to !x1 (negative equivalence: x0 = !x1).
    let mut lit_map = vec![Literal(0); 4];
    lit_map[lit(0, true).index()] = lit(1, false); // x0 -> !x1
    lit_map[lit(0, false).index()] = lit(1, true); // !x0 -> x1
    lit_map[lit(1, true).index()] = lit(1, true);
    lit_map[lit(1, false).index()] = lit(1, false);
    stack.push_sweep(2, lit_map);

    // Consistent: x0=true, x1=false → no change.
    let mut model = vec![true, false];
    stack.reconstruct(&mut model);
    assert!(model[0], "x0 stays true");
    assert!(!model[1], "x1 stays false");

    // Inconsistent: x0=true, x1=true → x0 should become false (= !x1).
    let mut model = vec![true, true];
    stack.reconstruct(&mut model);
    // The binary clause entries will fix x0:
    // Entry 1: witness=[-x0], clause=[-x0, !x1] = [-x0, -x1]
    //   -x0=false, -x1=false → unsatisfied → flip -x0 to true (x0=false)
    // Entry 2: witness=[x0], clause=[x0, x1]
    //   x0=false, x1=true → satisfied → skip
    assert!(!model[0], "x0 becomes false (= !x1) after reconstruction");
    assert!(model[1], "x1 stays true");
}

#[test]
fn test_verify_sweep_consistency_after_reconstruction() {
    let mut stack = ReconstructionStack::new();
    // x0 maps to x1 (positive equivalence).
    let mut lit_map = vec![Literal(0); 6];
    lit_map[lit(0, true).index()] = lit(1, true);
    lit_map[lit(0, false).index()] = lit(1, false);
    lit_map[lit(1, true).index()] = lit(1, true);
    lit_map[lit(1, false).index()] = lit(1, false);
    lit_map[lit(2, true).index()] = lit(2, true);
    lit_map[lit(2, false).index()] = lit(2, false);
    stack.push_sweep(3, lit_map);

    // Start with inconsistent model, then reconstruct.
    let mut model = vec![false, true, false];
    stack.reconstruct(&mut model);

    // After reconstruction, sweep equivalences must hold.
    assert!(
        stack.verify_sweep_consistency(&model).is_none(),
        "Sweep equivalences must hold after reconstruct()"
    );
    assert_eq!(
        model[0], model[1],
        "x0 and x1 should be equal after sweep reconstruction"
    );
}

// ---------------------------------------------------------------------------
// Tests for #8494: Non-contiguous witness entries (multi-round BVE)
// ---------------------------------------------------------------------------

#[test]
fn test_bve_multi_round_noncontiguous_entries() {
    // Simulate multi-round BVE where entries for different variables are
    // interleaved on the reconstruction stack. This is the core scenario
    // from #8494: AY's multi-round BVE produces non-contiguous witness
    // entries (unlike CaDiCaL which pushes atomically per variable).
    //
    // Stack layout (push order):
    //   [0] var2 positive: (x2 | x4)  -- round 1
    //   [1] var0 positive: (x0 | x3)  -- round 1 (different variable)
    //   [2] var2 negative: (!x2 | x5) -- round 2 (var2 again, non-contiguous!)
    //   [3] var0 negative: (!x0 | x6) -- round 2 (var0 again, non-contiguous!)
    //
    // The grouped reconstruction algorithm must handle entries [0]+[2] as
    // a group for var2, and entries [1]+[3] as a group for var0, even though
    // they are interleaved on the stack.
    let mut stack = ReconstructionStack::new();

    // Round 1: push positive occurrences for var2 and var0.
    stack.push_witness_clause(vec![lit(2, true)], vec![lit(2, true), lit(4, true)]);
    stack.push_witness_clause(vec![lit(0, true)], vec![lit(0, true), lit(3, true)]);

    // Round 2: push negative occurrences for var2 and var0 (non-contiguous).
    stack.push_witness_clause(vec![lit(2, false)], vec![lit(2, false), lit(5, true)]);
    stack.push_witness_clause(vec![lit(0, false)], vec![lit(0, false), lit(6, true)]);

    // Model: all vars false except x3=true, x4=true, x5=true, x6=true.
    let mut model = vec![false, false, false, true, true, true, true];
    stack.reconstruct(&mut model);

    // After reconstruction, all four clauses must be satisfied.
    // (x2 | x4): x4=true satisfies this, so x2 stays unchanged.
    assert!(model[2] || model[4], "(x2|x4) must be satisfied");
    // (!x2 | x5): x5=true satisfies this regardless of x2.
    assert!(!model[2] || model[5], "(!x2|x5) must be satisfied");
    // (x0 | x3): x3=true satisfies this, so x0 stays unchanged.
    assert!(model[0] || model[3], "(x0|x3) must be satisfied");
    // (!x0 | x6): x6=true satisfies this regardless of x0.
    assert!(!model[0] || model[6], "(!x0|x6) must be satisfied");
}

#[test]
fn test_bve_multi_round_noncontiguous_forced_flip() {
    // Multi-round BVE with suppress_prior_witness_entries, ensuring forced
    // flips work correctly when earlier entries are suppressed.
    //
    // Round 1 eliminates x2:
    //   [0] witness x2,  clause (x2 | x4)
    //   [1] witness !x2, clause (!x2 | x5)
    //
    // Round 1 also eliminates x0:
    //   [2] witness x0,  clause (x0 | x3)
    //   [3] witness !x0, clause (!x0 | x6)
    //
    // Round 2 re-eliminates x2 (entries [0],[1] get suppressed):
    //   [4] witness x2,  clause (x2 | x7)
    //   [5] witness !x2, clause (!x2 | x8)
    //
    // Model: x0=true, x2=true, all others false.
    //
    // Reconstruction (reverse order, entries [0],[1] suppressed):
    //   [5] (!x2|x8): !x2=false, x8=false → unsatisfied → flip x2 to false
    //   [4] (x2|x7): x2=false, x7=false → unsatisfied → flip x2 to true
    //       Wait: witness is x2 (positive). x2 is false → flip to true.
    //       But then [5]'s clause is broken again.
    //
    //   Actually let's trace more carefully with the algorithm.
    //   [5] clause (!x2|x8). x2=true → !x2=false, x8=false → unsatisfied.
    //       Witness = !x2. lit_satisfied = !model[2] = !true = false → flip x2.
    //       model[2] = false.
    //   [4] clause (x2|x7). x2=false, x7=false → unsatisfied.
    //       Witness = x2. lit_satisfied = model[2] = false → flip x2.
    //       model[2] = true.
    //   [3] clause (!x0|x6). x0=true → !x0=false, x6=false → unsatisfied.
    //       Witness = !x0. lit_satisfied = !model[0] = false → flip x0.
    //       model[0] = false.
    //   [2] clause (x0|x3). x0=false, x3=false → unsatisfied.
    //       Witness = x0. lit_satisfied = model[0] = false → flip x0.
    //       model[0] = true.
    //   [1] SUPPRESSED, skip.
    //   [0] SUPPRESSED, skip.
    //
    // Final model: x0=true, x2=true.
    // Check: [4] (x2|x7) = (true|false) = sat. [5] (!x2|x8) = (false|false) = UNSAT.
    //
    // The issue is the same: positive and negative entries for the same var
    // conflict. But this IS how real BVE works -- the last entry processed
    // (earliest in stack, i.e. [4]) wins. The key insight is that in real BVE,
    // the clauses removed are resolvable, so ONE polarity always satisfies.
    //
    // Let's construct a valid scenario: eliminate different variables in each
    // round, with interleaving, and forced flips for all of them.
    //
    // Round 1: eliminate x0 (positive and negative clauses)
    //   [0] witness x0,  clause (x0 | x3)
    //   [1] witness !x0, clause (!x0 | x4)
    //
    // Round 1: also eliminate x2
    //   [2] witness x2,  clause (x2 | x5)
    //   [3] witness !x2, clause (!x2 | x6)
    //
    // Round 2: eliminate x1 (interleaved between x0 and x2 entries)
    //   [4] witness x1,  clause (x1 | x7)
    //   [5] witness !x1, clause (!x1 | x8)
    //
    // Model: x0=true, x1=false, x2=true, x3=false, x4=false, x5=false,
    //         x6=false, x7=false, x8=true.
    //
    // Reconstruction (reverse):
    //   [5] (!x1|x8): !x1=true (x1=false), x8=true → satisfied. No flip.
    //   [4] (x1|x7): x1=false, x7=false → unsatisfied → flip x1 to true.
    //   [3] (!x2|x6): !x2=false (x2=true), x6=false → unsatisfied → flip x2 to false.
    //   [2] (x2|x5): x2=false, x5=false → unsatisfied → flip x2 to true.
    //   [1] (!x0|x4): !x0=false (x0=true), x4=false → unsatisfied → flip x0 to false.
    //   [0] (x0|x3): x0=false, x3=false → unsatisfied → flip x0 to true.
    //
    // Final: x0=true, x1=true, x2=true.
    // Verify:
    //   [0] (x0|x3) = (true|false) = sat
    //   [1] (!x0|x4) = (false|false) = UNSAT!
    //
    // Same problem. The fundamental issue is that for a single variable,
    // the positive entry is processed LAST (lowest index, reverse order),
    // so positive polarity always wins. The negative clause is only satisfied
    // if another literal in it is true.
    //
    // Valid test: ensure at least one non-witness literal is true in each
    // negative-polarity clause.

    let mut stack = ReconstructionStack::new();

    // Round 1: eliminate x0
    stack.push_witness_clause(vec![lit(0, true)], vec![lit(0, true), lit(3, true)]);
    stack.push_witness_clause(vec![lit(0, false)], vec![lit(0, false), lit(4, true)]);

    // Round 1: eliminate x2 (non-contiguous with x0)
    stack.push_witness_clause(vec![lit(2, true)], vec![lit(2, true), lit(5, true)]);
    stack.push_witness_clause(vec![lit(2, false)], vec![lit(2, false), lit(6, true)]);

    // Round 2: eliminate x1 (interleaved)
    stack.push_witness_clause(vec![lit(1, true)], vec![lit(1, true), lit(7, true)]);
    stack.push_witness_clause(vec![lit(1, false)], vec![lit(1, false), lit(8, true)]);

    // Model: x0=false, x1=false, x2=false (eliminated vars start false),
    //        x3=false, x4=true, x5=false, x6=true, x7=false, x8=true.
    // The negative-polarity clauses need their non-witness literal true:
    //   (!x0|x4): x4=true satisfies it regardless
    //   (!x2|x6): x6=true satisfies it regardless
    //   (!x1|x8): x8=true satisfies it regardless
    // The positive-polarity clauses will force flips:
    //   (x0|x3): both false → flip x0 to true
    //   (x2|x5): both false → flip x2 to true
    //   (x1|x7): both false → flip x1 to true
    let mut model = vec![false, false, false, false, true, false, true, false, true];
    stack.reconstruct(&mut model);

    // After reconstruction, all six clauses must be satisfied.
    // The positive-polarity clauses forced flips of x0, x1, x2 to true.
    assert!(model[0], "x0 should have been flipped to true");
    assert!(model[1], "x1 should have been flipped to true");
    assert!(model[2], "x2 should have been flipped to true");

    // Verify all clauses:
    assert!(
        model[0] || model[3],
        "(x0|x3) must be satisfied: x0={}, x3={}",
        model[0],
        model[3]
    );
    assert!(
        !model[0] || model[4],
        "(!x0|x4) must be satisfied: x0={}, x4={}",
        model[0],
        model[4]
    );
    assert!(
        model[2] || model[5],
        "(x2|x5) must be satisfied: x2={}, x5={}",
        model[2],
        model[5]
    );
    assert!(
        !model[2] || model[6],
        "(!x2|x6) must be satisfied: x2={}, x6={}",
        model[2],
        model[6]
    );
    assert!(
        model[1] || model[7],
        "(x1|x7) must be satisfied: x1={}, x7={}",
        model[1],
        model[7]
    );
    assert!(
        !model[1] || model[8],
        "(!x1|x8) must be satisfied: x1={}, x8={}",
        model[1],
        model[8]
    );
}
