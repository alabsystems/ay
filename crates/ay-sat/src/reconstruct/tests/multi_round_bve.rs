// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Multi-round BVE reconstruction regressions.

use super::*;

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
