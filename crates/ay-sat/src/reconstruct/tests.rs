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
// BCE followed by BVE on the same variable.
// ---------------------------------------------------------------------------

#[test]
fn test_bce_then_bve_witnesses_compose() {
    let mut stack = ReconstructionStack::new();

    // BCE first removes C=(x0|x1), blocked on x0. The only remaining clause
    // with -x0 is Dn=(-x0|-x1), so their resolvent is tautological.
    let bce_clause = vec![lit(0, true), lit(1, true)];
    stack.push_bce(lit(0, true), bce_clause.clone());

    // BVE later eliminates x0 from Dp=(x0|x2) and Dn. CaDiCaL retains all
    // three extension entries; reverse chronological replay composes the
    // transformations without dropping C's sole reconstruction obligation.
    let bve_pos = vec![lit(0, true), lit(2, true)];
    let bve_neg = vec![lit(0, false), lit(1, false)];
    stack.push_witness_clause(vec![lit(0, true)], bve_pos.clone());
    stack.push_witness_clause(vec![lit(0, false)], bve_neg.clone());

    // This satisfies the BVE resolvent (x2|-x1). BVE needs no pivot flip,
    // then BCE must set x0=true to restore C. The blocking property guarantees
    // that this final flip cannot break Dn.
    let mut model = vec![false, false, true];
    stack.reconstruct(&mut model);

    for clause in [&bce_clause, &bve_pos, &bve_neg] {
        assert!(
            clause
                .iter()
                .any(|lit| model[lit.variable().index()] == lit.is_positive()),
            "reconstructed model must satisfy {clause:?}"
        );
    }
    assert!(model[0], "the retained BCE witness must restore C");
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
fn test_bve_multiple_eliminations_forced_flip() {
    // Independent BVE groups are replayed in reverse chronological order.
    // Each negative-polarity parent is satisfied by a non-pivot literal,
    // while each positive-polarity parent forces its pivot true.
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
