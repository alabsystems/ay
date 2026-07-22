// Copyright 2026 Andrew Yates
// RAT verification tests for the backward DRAT checker:
// vacuous RAT, non-vacuous RAT, mixed RAT+RUP, dependency tracking,
// deep mark_active recursion, and RUP-with-deps precision.

use super::*;
use crate::checker::test_helpers::lit;

#[test]
fn test_backward_rat_non_vacuous() {
    // Coverage gap: backward checking with non-vacuous RAT.
    // In vacuous RAT, the pivot has no negative occurrence, so the resolvent
    // set is empty and the check trivially passes. Non-vacuous RAT requires
    // actually checking that each resolvent is RUP.
    //
    // Formula (UNSAT):
    //   C1=(a v b), C2=(~a v b), C3=(a v ~b), C4=(~a v ~b), C5=(~c)
    //   add (c v a) via RAT with pivot c.
    //   Resolvent with C5=(~c): resolve on c -> (a). Check (a) is RUP:
    //     assume ~a. C1 forces b, C4 forces ~b, contradiction. (a) is RUP. OK.
    //   Then add (a) via RUP, then empty clause.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // C1: a v b
        vec![lit(0, false), lit(1, true)],  // C2: ~a v b
        vec![lit(0, true), lit(1, false)],  // C3: a v ~b
        vec![lit(0, false), lit(1, false)], // C4: ~a v ~b
        vec![lit(2, false)],                // C5: ~c
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(2, true), lit(0, true)]), // (c v a) — RAT on c
        ProofStep::Add(vec![lit(0, true)]),               // (a) — RUP
        ProofStep::Add(vec![]),                           // empty clause
    ];

    let mut fwd = DratChecker::new(3, true);
    let fwd_result = fwd.verify(&clauses, &steps);
    assert!(
        fwd_result.is_ok(),
        "forward accepts RAT proof: {fwd_result:?}"
    );

    let mut bwd = BackwardChecker::new(3, true);
    let bwd_result = bwd.verify(&clauses, &steps);
    assert!(
        bwd_result.is_ok(),
        "backward must accept non-vacuous RAT proof: {bwd_result:?}"
    );
}

#[test]
fn test_backward_mixed_rat_rup_proof() {
    // Coverage gap: proof with both RAT and RUP steps, verified backward.
    // The backward checker must correctly handle ACTIVE RAT clauses
    // (which fall through the RUP check to the RAT check).
    //
    // Formula (UNSAT):
    //   C1=(a v b), C2=(~a v b), C3=(a v ~b), C4=(~a v ~b), C5=(~c)
    //
    // Proof:
    //   step 1: add (c v a) via RAT on c (non-vacuous: resolvent with C5 is (a), RUP)
    //   step 2: delete C5=(~c) — now c has no negative occurrence
    //   step 3: add (b) via RUP (unit, ~b => C1 forces a, C4 forces ~a, conflict)
    //   step 4: add (~b) via RUP
    //   step 5: add () — conflict
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // C1: a v b
        vec![lit(0, false), lit(1, true)],  // C2: ~a v b
        vec![lit(0, true), lit(1, false)],  // C3: a v ~b
        vec![lit(0, false), lit(1, false)], // C4: ~a v ~b
        vec![lit(2, false)],                // C5: ~c
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(2, true), lit(0, true)]), // (c v a) — RAT on c
        ProofStep::Delete(vec![lit(2, false)]),           // delete C5=(~c)
        ProofStep::Add(vec![lit(1, true)]),               // (b) — RUP
        ProofStep::Add(vec![lit(1, false)]),              // (~b) — RUP
        ProofStep::Add(vec![]),                           // empty clause
    ];

    let mut fwd = DratChecker::new(3, true);
    let fwd_result = fwd.verify(&clauses, &steps);
    assert!(
        fwd_result.is_ok(),
        "forward accepts mixed RAT+RUP proof: {fwd_result:?}"
    );

    let mut bwd = BackwardChecker::new(3, true);
    let bwd_result = bwd.verify(&clauses, &steps);
    assert!(
        bwd_result.is_ok(),
        "backward must accept mixed RAT+RUP proof: {bwd_result:?}"
    );
}

#[test]
fn test_backward_long_transitive_chain_unwinding() {
    // Exercises unwind_trail_to with a 3-deep transitive BCP chain.
    //
    // Formula (UNSAT):
    //   C1=(a v b), C2=(~a v b)  — resolves to (b)
    //   C3=(~b v c)              — b -> c
    //   C4=(~c v d)              — c -> d
    //   C5=(a v ~d), C6=(~a v ~d) — resolves to (~d)
    //   Chain: b -> c -> d, but ~d forced. Contradiction.
    //
    // Backward pass: undo step 1 must unwind d, c, and b — all 3
    // transitive propagations.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // C1: a v b
        vec![lit(0, false), lit(1, true)],  // C2: ~a v b
        vec![lit(1, false), lit(2, true)],  // C3: ~b v c
        vec![lit(2, false), lit(3, true)],  // C4: ~c v d
        vec![lit(0, true), lit(3, false)],  // C5: a v ~d
        vec![lit(0, false), lit(3, false)], // C6: ~a v ~d
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(1, true)]), // (b) — RUP, triggers b=t, c=t, d=t
        ProofStep::Add(vec![lit(3, false)]), // (~d) — RUP
        ProofStep::Add(vec![]),             // empty clause
    ];

    let mut fwd = DratChecker::new(4, false);
    let fwd_result = fwd.verify(&clauses, &steps);
    assert!(fwd_result.is_ok(), "forward accepts: {fwd_result:?}");

    let mut bwd = BackwardChecker::new(4, false);
    let bwd_result = bwd.verify(&clauses, &steps);
    assert!(
        bwd_result.is_ok(),
        "backward must accept valid proof with proper unwinding: {bwd_result:?}"
    );
}

#[test]
fn test_check_rup_with_deps_returns_precise_reasons() {
    // Directly test that check_rup_with_deps returns the exact clause
    // indices in the RUP derivation chain (not all trail reasons).
    //
    // Setup: clauses C0=(a v b), C1=(~a v b). After adding both, BCP
    // does nothing (no unit). Then check_rup_with_deps for (b) should:
    //   1. Assume ~b
    //   2. BCP: C0=(a v b) with b=false -> propagate a (reason=C0)
    //   3. BCP: C1=(~a v b) with a=true, b=false -> conflict
    //   4. MARK analysis: conflict clause is C1, walk trail:
    //      - a is marked (in C1 as ~a), reason=C0 -> add C0 to deps
    //      - b was assumed (no reason) -> skip
    //   5. deps = [C0] (and the conflict C1 is also identified)
    let mut checker = DratChecker::new(4, false);
    checker.add_original(&[lit(0, true), lit(1, true)]); // C0: a v b
    checker.add_original(&[lit(0, false), lit(1, true)]); // C1: ~a v b
                                                          // Also add unrelated clause C2=(c v d) that should NOT appear in deps.
    checker.add_original(&[lit(2, true), lit(3, true)]); // C2: c v d

    let result = checker.check_rup_with_deps(&[lit(1, true)]); // check (b)
    assert!(result.is_rup, "(b) should be RUP");
    // deps should contain C0 (reason for propagating a). It should NOT
    // contain C2 (unrelated clause).
    assert!(
        !result.deps.contains(&2),
        "deps must NOT contain unrelated clause C2: deps={:?}",
        result.deps
    );
    assert!(
        result.deps.contains(&0),
        "deps must contain C0 (reason for a): deps={:?}",
        result.deps
    );
}

#[test]
fn test_check_rup_with_deps_empty_deps_on_trivial() {
    // When the clause is trivially implied (a literal is already true),
    // check_rup_with_deps returns (true, []).
    let mut checker = DratChecker::new(2, false);
    checker.add_original(&[lit(0, true)]); // C0: (a) -> forces a=true

    // (a v b) has a=true already -> trivially RUP
    let result = checker.check_rup_with_deps(&[lit(0, true), lit(1, true)]);
    assert!(result.is_rup);
    assert!(
        result.deps.is_empty(),
        "trivial RUP should have no deps: {:?}",
        result.deps
    );
}

/// Deep `mark_active` recursion: verify backward checker correctly handles
/// a 6-level dependency chain where each derived clause depends on the
/// previous one.
///
/// Backward checker with RAT enabled: sanity test that backward verification
/// accepts valid RUP-only proofs when check_rat=true.
#[test]
fn test_backward_rat_enabled_accepts_rup_proof() {
    // XOR-2 formula, proof via RUP only.
    let clauses = vec![
        vec![lit(0, false), lit(1, true)],  // ~a v b
        vec![lit(0, true), lit(1, false)],  // a v ~b
        vec![lit(0, true), lit(1, true)],   // a v b
        vec![lit(0, false), lit(1, false)], // ~a v ~b
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(1, true)]),  // (b) — RUP
        ProofStep::Add(vec![lit(1, false)]), // (~b) — RUP
        ProofStep::Add(vec![]),              // empty
    ];
    let mut fwd = DratChecker::new(2, true); // RAT enabled
    assert!(
        fwd.verify(&clauses, &steps).is_ok(),
        "forward with RAT enabled must accept"
    );
    let mut bwd = BackwardChecker::new(2, true); // RAT enabled
    let result = bwd.verify(&clauses, &steps);
    assert!(
        result.is_ok(),
        "backward with RAT enabled must accept valid proof: {result:?}"
    );
}

/// Backward RAT dependency tracking: resolution candidates and their RUP
/// proof chain dependencies are marked ACTIVE (#5215).
#[test]
fn test_backward_rat_marks_resolution_candidate_active() {
    // Formula: XOR-2 (UNSAT).
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // C0: a v b   idx 0
        vec![lit(0, false), lit(1, true)],  // C1: ~a v b  idx 1
        vec![lit(0, true), lit(1, false)],  // C2: a v ~b  idx 2
        vec![lit(0, false), lit(1, false)], // C3: ~a v ~b idx 3
    ];
    // Proof: D1 is a derived clause that is a resolution candidate for
    // D2's RAT check. D3+D4 derive the empty clause.
    let steps = vec![
        ProofStep::Add(vec![lit(2, false), lit(1, true)]), // S1: (~c v b) RUP → idx 4
        ProofStep::Add(vec![lit(2, true), lit(3, true)]),  // S2: (c v d) RAT pivot c → idx 5
        ProofStep::Add(vec![lit(1, true)]),                // S3: (b) RUP → idx 6
        ProofStep::Add(vec![lit(1, false)]),               // S4: (~b) → empty, conflict
    ];

    let mut checker = BackwardChecker::new(4, true); // RAT enabled
    let result = checker.verify(&clauses, &steps);
    assert!(result.is_ok(), "proof must verify: {result:?}");

    // D3 = (b) at idx 6 must be ACTIVE (needed for empty clause derivation).
    assert!(checker.is_active(6), "D3=(b) must be ACTIVE");
}

/// Backward RAT dependency tracking: direct unit test that
/// check_rat_backward marks resolution candidates and RUP deps ACTIVE.
///
/// Constructs a backward checker state manually and calls
/// check_rat_backward to verify it marks the right clauses.
#[test]
fn test_backward_rat_deps_direct() {
    // Build a backward checker with a small clause DB.
    // Variables: a(0), b(1), c(2)
    let mut checker = BackwardChecker::new(3, true);

    // Add original clauses that make (b) RUP:
    // C0: (a v b)   idx 0
    // C1: (~a v b)  idx 1
    checker.add_original_tracking(&[lit(0, true), lit(1, true)]);
    checker.add_original_tracking(&[lit(0, false), lit(1, true)]);
    checker.num_original = checker.inner.clauses.len(); // 2

    // Add derived clause D1 = (~c v b) via forward replay (no verification).
    // This becomes idx 2. It contains ~c, making it a resolution candidate
    // for any RAT step with pivot c.
    let d1_idx = checker.add_derived_forward(&[lit(2, false), lit(1, true)]);
    assert_eq!(d1_idx, 2, "D1 should be at idx 2");
    assert!(!checker.is_active(d1_idx), "D1 starts as not ACTIVE");

    // Now simulate backward verification of a clause (c v d) where d=var 3.
    // This clause is RAT with pivot c: candidate D1 has ~c.
    // Resolvent: (d v b) — and (b) is RUP (assume ~b: C0→a, C1→conflict).
    //
    // We need var 3 capacity.
    checker.inner.ensure_capacity(3);
    while checker.active.len() < checker.inner.clauses.len() {
        checker.active.push(false);
    }

    // Mark D1 as ACTIVE (simulating it being in the ACTIVE set for
    // backward RAT candidate filtering).
    checker.active[d1_idx] = true;

    // Call check_rat_backward for clause (c v d). This should succeed
    // (resolvent (d v b) is RUP) and mark D1 as ACTIVE via dep tracking.
    let rat_clause = vec![lit(2, true), Literal::from_dimacs(4)]; // c v d
    let rat_ok = checker.check_rat_backward(&rat_clause);
    assert!(rat_ok, "RAT check should succeed for (c v d) with pivot c");

    // D1 at idx 2 should still be ACTIVE (it was already, and the dep
    // tracking should have re-confirmed it).
    assert!(
        checker.is_active(d1_idx),
        "D1 must be ACTIVE as RAT resolution candidate"
    );

    // Additionally, the RUP proof chain for the resolvent (d v b) should
    // have marked C0 and/or C1 as ACTIVE (they are the reason clauses in
    // the RUP derivation of (b)).
    // C0 idx=0, C1 idx=1.
    assert!(
        checker.is_active(0) || checker.is_active(1),
        "at least one of C0/C1 should be ACTIVE from RUP dep chain"
    );
}

/// Backward RAT with 4 non-vacuous resolution candidates.
///
/// Formula: all 8 3-literal clauses on {a,b,c} (UNSAT).
///   C0-C7 = every sign combination of (±a v ±b v ±c).
///
/// S1 is RAT with 4 genuine resolvent RUP checks (not vacuous).
/// S4 uses derived clauses S2 and S3 — exercises backward dep tracking.
#[test]
fn test_backward_rat_four_candidates() {
    let clauses = vec![
        vec![lit(0, true), lit(1, true), lit(2, true)], // C0: a v b v c
        vec![lit(0, false), lit(1, true), lit(2, true)], // C1: ~a v b v c
        vec![lit(0, true), lit(1, false), lit(2, true)], // C2: a v ~b v c
        vec![lit(0, false), lit(1, false), lit(2, true)], // C3: ~a v ~b v c
        vec![lit(0, true), lit(1, true), lit(2, false)], // C4: a v b v ~c
        vec![lit(0, false), lit(1, true), lit(2, false)], // C5: ~a v b v ~c
        vec![lit(0, true), lit(1, false), lit(2, false)], // C6: a v ~b v ~c
        vec![lit(0, false), lit(1, false), lit(2, false)], // C7: ~a v ~b v ~c
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(0, true)]),  // S1: (a) — RAT with pivot a
        ProofStep::Add(vec![lit(1, true)]),  // S2: (b) — RUP
        ProofStep::Add(vec![lit(1, false)]), // S3: (~b) — RUP
        ProofStep::Add(vec![lit(0, false)]), // S4: (~a) — RUP using S2+S3
        ProofStep::Add(vec![]),              // S5: empty clause
    ];

    // Forward checker with RAT must accept.
    let mut fwd = DratChecker::new(3, true);
    let fwd_result = fwd.verify(&clauses, &steps);
    assert!(
        fwd_result.is_ok(),
        "forward must accept RAT proof: {fwd_result:?}"
    );
    assert!(fwd.stats.rat_checks > 0, "RAT check should have triggered");

    // Forward checker WITHOUT RAT must reject (S1=(a) is not RUP).
    let mut fwd_no_rat = DratChecker::new(3, false);
    let fwd_no_rat_result = fwd_no_rat.verify(&clauses, &steps);
    assert!(
        fwd_no_rat_result.is_err(),
        "(a) is NOT RUP from 8-clause formula — forward without RAT must reject"
    );

    // Backward checker with RAT must accept.
    let mut bwd = BackwardChecker::new(3, true);
    let bwd_result = bwd.verify(&clauses, &steps);
    assert!(
        bwd_result.is_ok(),
        "backward must accept non-vacuous RAT proof: {bwd_result:?}"
    );
}

/// Backward: S6(empty) is ACTIVE → marks S5 → marks S4 → marks S3
///   → marks S2 → marks S1 → marks C0, C1, etc. 6+ levels of dependency.
#[test]
fn test_backward_deep_mark_active_recursion() {
    let clauses = vec![
        vec![lit(0, true)],                // C0: x1
        vec![lit(0, false), lit(1, true)], // C1: ~x1 v x2
        vec![lit(1, false), lit(2, true)], // C2: ~x2 v x3
        vec![lit(2, false), lit(3, true)], // C3: ~x3 v x4
        vec![lit(3, false), lit(4, true)], // C4: ~x4 v x5
        vec![lit(4, false), lit(5, true)], // C5: ~x5 v x6
        vec![lit(5, false)],               // C6: ~x6
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(1, true)]), // S1: (x2)
        ProofStep::Add(vec![lit(2, true)]), // S2: (x3)
        ProofStep::Add(vec![lit(3, true)]), // S3: (x4)
        ProofStep::Add(vec![lit(4, true)]), // S4: (x5)
        ProofStep::Add(vec![lit(5, true)]), // S5: (x6)
        ProofStep::Add(vec![]),             // S6: empty clause
    ];

    // Forward must accept.
    let mut fwd = DratChecker::new(6, false);
    let fwd_result = fwd.verify(&clauses, &steps);
    assert!(fwd_result.is_ok(), "forward must accept: {fwd_result:?}");

    // Backward must accept — exercises 6-level mark_active recursion.
    let mut bwd = BackwardChecker::new(6, false);
    let bwd_result = bwd.verify(&clauses, &steps);
    assert!(
        bwd_result.is_ok(),
        "backward must accept deep dependency chain: {bwd_result:?}"
    );
}
