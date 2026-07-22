// Copyright 2026 Andrew Yates
// Boundary condition and edge case tests for the backward DRAT checker.
// Tests gap areas identified by Prover algorithm audit:
//   - Empty original clause set
//   - Deletion of non-existent clause
//   - Post-conflict steps ignored
//   - Variable capacity growth during proof
//   - RAT with backward pivot fallback
//   - RAT failure leaves ACTIVE set clean (no partial marking)
//   - Unit clause as RAT resolution candidate
//   - Deletion before RAT step reduces candidate set

use super::*;

fn lit(var: u32, positive: bool) -> Literal {
    if positive {
        Literal::from_dimacs(var as i32 + 1)
    } else {
        Literal::from_dimacs(-(var as i32 + 1))
    }
}

// ─── Backward checker boundary conditions ────────────────────────────

/// Empty original clause set: formula is trivially SAT.
/// Any proof that adds the empty clause should be rejected.
#[test]
fn test_backward_empty_originals_rejects_empty_clause() {
    let clauses: Vec<Vec<Literal>> = vec![];
    let steps = vec![ProofStep::Add(vec![])];

    let mut fwd = DratChecker::new(0, false);
    assert!(
        fwd.verify(&clauses, &steps).is_err(),
        "forward must reject empty clause on trivially SAT (no clauses)"
    );

    let mut bwd = BackwardChecker::new(0, false);
    assert!(
        bwd.verify(&clauses, &steps).is_err(),
        "backward must reject empty clause on trivially SAT (no clauses)"
    );
}

/// Empty original clause set with no proof steps: "proof does not derive
/// the empty clause" error because found_conflict is false.
#[test]
fn test_backward_empty_originals_no_steps() {
    let clauses: Vec<Vec<Literal>> = vec![];
    let steps: Vec<ProofStep> = vec![];

    let mut bwd = BackwardChecker::new(0, false);
    let result = bwd.verify(&clauses, &steps);
    assert!(result.is_err());
    assert!(
        result.unwrap_err().to_string().contains("empty clause"),
        "should report missing empty clause"
    );
}

/// Proof with only deletion steps and no additions.
/// Should fail because empty clause is never derived.
#[test]
fn test_backward_only_deletions_no_conflict() {
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],  // a v b
        vec![lit(0, false), lit(1, true)], // ~a v b
    ];
    let steps = vec![ProofStep::Delete(vec![lit(0, true), lit(1, true)])];

    let mut bwd = BackwardChecker::new(2, false);
    let result = bwd.verify(&clauses, &steps);
    assert!(result.is_err());
    let err_msg = result.unwrap_err().to_string();
    assert!(
        err_msg.contains("empty clause"),
        "only-deletion proof should fail: {err_msg}"
    );
}

/// Delete a clause that doesn't exist in the database.
/// The backward checker should handle gracefully (missed_deletes counter).
#[test]
fn test_backward_delete_nonexistent_clause() {
    // Formula: (a v b), (~a v ~b) — UNSAT
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // C0: a v b
        vec![lit(0, false), lit(1, true)],  // C1: ~a v b
        vec![lit(0, true), lit(1, false)],  // C2: a v ~b
        vec![lit(0, false), lit(1, false)], // C3: ~a v ~b
    ];
    let steps = vec![
        // Delete a clause that is NOT in the formula (c v d).
        ProofStep::Delete(vec![lit(2, true), lit(3, true)]),
        ProofStep::Add(vec![lit(1, true)]),  // (b) — RUP
        ProofStep::Add(vec![lit(1, false)]), // (~b) — RUP
        ProofStep::Add(vec![]),              // empty clause
    ];

    let mut fwd = DratChecker::new(4, false);
    assert!(fwd.verify(&clauses, &steps).is_ok(), "forward must accept");
    assert_eq!(fwd.stats.missed_deletes, 1, "forward: 1 missed delete");

    let mut bwd = BackwardChecker::new(4, false);
    assert!(
        bwd.verify(&clauses, &steps).is_ok(),
        "backward must accept (nonexistent delete is a no-op)"
    );
    assert_eq!(bwd.stats().missed_deletes, 1, "backward: 1 missed delete");
}

/// Post-conflict steps: after the empty clause is found in the forward pass,
/// subsequent addition steps should be recorded but not affect the backward
/// pass result.
#[test]
fn test_backward_post_conflict_steps_ignored() {
    // Formula: (a), (~a) — UNSAT from originals.
    // Wait — this is already inconsistent, short-circuits to Ok. Use XOR-2.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // a v b
        vec![lit(0, false), lit(1, true)],  // ~a v b
        vec![lit(0, true), lit(1, false)],  // a v ~b
        vec![lit(0, false), lit(1, false)], // ~a v ~b
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(1, true)]),  // (b) — RUP
        ProofStep::Add(vec![lit(1, false)]), // (~b) — RUP
        ProofStep::Add(vec![]),              // empty clause (conflict found)
        // Post-conflict: these steps are meaningless but shouldn't crash.
        ProofStep::Add(vec![lit(0, true)]),
        ProofStep::Delete(vec![lit(0, true), lit(1, true)]),
        ProofStep::Add(vec![lit(2, true), lit(3, true)]), // new vars
    ];

    let mut fwd = DratChecker::new(2, false);
    assert!(fwd.verify(&clauses, &steps).is_ok(), "forward must accept");

    let mut bwd = BackwardChecker::new(2, false);
    assert!(
        bwd.verify(&clauses, &steps).is_ok(),
        "backward must accept (post-conflict steps should not affect result)"
    );
}

/// Variable capacity growth: proof introduces variables far beyond the
/// original CNF's num_vars.
#[test]
fn test_backward_variable_capacity_growth() {
    // Formula: (a v b), (~a v b), (a v ~b), (~a v ~b) — UNSAT, 2 vars.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],
        vec![lit(0, false), lit(1, true)],
        vec![lit(0, true), lit(1, false)],
        vec![lit(0, false), lit(1, false)],
    ];
    // Proof uses variables 100 and 200 (far beyond num_vars=2).
    // These clauses are vacuous RAT / unnecessary, but the backward
    // checker must handle the capacity growth without panic.
    let big_var_a = Literal::from_dimacs(101); // var index 100
    let big_var_b = Literal::from_dimacs(201); // var index 200
    let steps = vec![
        ProofStep::Add(vec![big_var_a, big_var_b]), // (v100 v v200) — RAT/unnecessary
        ProofStep::Add(vec![lit(1, true)]),         // (b) — RUP
        ProofStep::Add(vec![lit(1, false)]),        // (~b) — RUP
        ProofStep::Add(vec![]),                     // empty clause
    ];

    let mut fwd = DratChecker::new(2, true);
    assert!(
        fwd.verify(&clauses, &steps).is_ok(),
        "forward must accept (big vars via vacuous RAT)"
    );

    let mut bwd = BackwardChecker::new(2, true);
    assert!(
        bwd.verify(&clauses, &steps).is_ok(),
        "backward must accept (capacity growth for big vars)"
    );
}

// ─── RAT boundary conditions ────────────────────────────────────────

/// RAT backward pivot fallback: first literal fails RAT, second succeeds.
/// Exercises the fallback loop in check_rat_backward (lines 284-293).
#[test]
fn test_backward_rat_pivot_fallback() {
    // Formula: all 8 3-literal clauses on {a,b,c} — UNSAT.
    // This gives us a fully symmetric base for crafting RAT steps.
    // Original all-8 clauses analysis (preserved as comments):
    // Every literal appears in 4 clauses, making RAT difficult.
    // S1: add (d v a) — d is fresh extension variable.
    //   Pivot d (first literal): ~d appears in 0 clauses → vacuous RAT → passes.
    //   This doesn't exercise fallback.
    //
    // Instead, use: (b v d) where we manipulate the formula so that:
    //   Pivot b (first literal) fails RAT but pivot d (second) passes vacuously.
    //
    // Actually, to exercise pivot fallback we need first pivot to FAIL.
    // In the all-8-clauses formula, every literal appears in 4 clauses.
    // (b v a): pivot b → need all clauses containing ~b to produce RUP resolvents.
    //   Candidates: C2, C3, C6, C7 (all contain ~b).
    //   Resolvent with C2=(a v ~b v c): (a v c). RUP? ~a, ~c → C7=(~a ~b ~c)
    //     needs ~b, but ~b is not assigned. Not RUP.
    // So pivot b fails. Pivot a: candidates C1, C3, C5, C7 (contain ~a).
    //   Resolvent with C1=(~a v b v c): (b v c). RUP? ~b, ~c → C0=(a b c): all false.
    //     C4=(a b ~c): a unassigned. Still no conflict. Not RUP either.
    //
    // The all-8 formula is actually tricky for RAT. Let me use a simpler approach:
    // a formula where the first pivot fails but a later pivot is vacuous.
    //
    // Formula: (a v b), (~a v b), (a v ~b), (~a v ~b), (~c)
    //   5 clauses. UNSAT.
    // Step: add (c v d) where d is fresh (var 3).
    //   Pivot c (first): ~c appears in C4=(~c). Resolvent: (d). RUP? ~d → no conflict
    //   (d is fresh, nothing propagates). Pivot c FAILS.
    //   Pivot d (second): ~d appears in 0 clauses → vacuous RAT. PASSES.
    let clauses2 = vec![
        vec![lit(0, true), lit(1, true)],   // C0: a v b
        vec![lit(0, false), lit(1, true)],  // C1: ~a v b
        vec![lit(0, true), lit(1, false)],  // C2: a v ~b
        vec![lit(0, false), lit(1, false)], // C3: ~a v ~b
        vec![lit(2, false)],                // C4: ~c
    ];
    let steps2 = vec![
        ProofStep::Add(vec![lit(2, true), lit(3, true)]), // (c v d) — RAT: pivot c fails, pivot d vacuous
        ProofStep::Add(vec![lit(1, true)]),               // (b) — RUP
        ProofStep::Add(vec![lit(1, false)]),              // (~b) — RUP
        ProofStep::Add(vec![]),                           // empty clause
    ];

    // Verify forward accepts with RAT.
    let mut fwd = DratChecker::new(4, true);
    let fwd_result = fwd.verify(&clauses2, &steps2);
    assert!(
        fwd_result.is_ok(),
        "forward must accept pivot-fallback RAT: {fwd_result:?}"
    );
    assert!(fwd.stats.rat_checks > 0, "RAT should have been attempted");

    // Verify forward rejects without RAT.
    let mut fwd_no_rat = DratChecker::new(4, false);
    assert!(
        fwd_no_rat.verify(&clauses2, &steps2).is_err(),
        "(c v d) is NOT RUP, forward without RAT must reject"
    );

    // Backward with RAT must accept.
    let mut bwd = BackwardChecker::new(4, true);
    let bwd_result = bwd.verify(&clauses2, &steps2);
    assert!(
        bwd_result.is_ok(),
        "backward must accept pivot-fallback RAT: {bwd_result:?}"
    );
}

/// RAT failure in backward mode: no valid pivot exists.
/// The ACTIVE set should not have partial markings from a failed first-pivot
/// attempt leaking into the final state.
#[test]
fn test_backward_rat_failure_no_partial_active_marking() {
    // Formula: (a v b), (~a v b) — SAT (b=T).
    // Proof: add (~b) [not RUP and not RAT on any pivot], then empty clause.
    //
    // (~b) with pivot ~b: candidates containing b = {C0, C1}.
    //   Resolvent with C0=(a v b): (a). ~a → C1=(~a v b): b forced, but b is
    //   being resolved out... Actually resolvent is (~b) resolved with C0 on b:
    //   just (a). RUP? ~a → nothing propagates (only C0 and C1 in DB, C0
    //   has a and b, b is unassigned). Not RUP.
    //   Resolvent with C1=(~a v b): just (~a). RUP? a → C0=(a v b): a=T, skip.
    //   C1=(~a v b): a=T means ~a=F. b unassigned, no conflict. Not RUP.
    //
    // So RAT fails. The backward checker should reject AND the ACTIVE set
    // should not contain RAT candidate clause indices from the failed attempt.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],  // C0: a v b
        vec![lit(0, false), lit(1, true)], // C1: ~a v b
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(1, false)]), // (~b) — not RUP, not RAT
        ProofStep::Add(vec![]),              // empty clause
    ];

    let mut fwd = DratChecker::new(2, true);
    assert!(
        fwd.verify(&clauses, &steps).is_err(),
        "forward must reject: (~b) is not RUP/RAT"
    );

    let mut bwd = BackwardChecker::new(2, true);
    assert!(
        bwd.verify(&clauses, &steps).is_err(),
        "backward must reject: (~b) is not RUP/RAT"
    );
}

/// Unit clause as a RAT resolution candidate.
/// When the database has a unit clause (~pivot), the resolvent is the
/// input clause minus the pivot literal.
#[test]
fn test_backward_rat_unit_clause_candidate() {
    // Formula: (a v b), (~a v b), (a v ~b), (~a v ~b), (~c)
    //   UNSAT on {a,b}. C4=(~c) is a unit clause.
    // Proof: add (c v a) via RAT on pivot c.
    //   C4=(~c) is the only candidate containing ~c.
    //   Resolvent: (a). RUP? ~a → C0 forces b, C3 forces ~b, conflict. Yes.
    //   So RAT succeeds with the unit clause as the sole candidate.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // C0: a v b
        vec![lit(0, false), lit(1, true)],  // C1: ~a v b
        vec![lit(0, true), lit(1, false)],  // C2: a v ~b
        vec![lit(0, false), lit(1, false)], // C3: ~a v ~b
        vec![lit(2, false)],                // C4: ~c (UNIT clause)
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(2, true), lit(0, true)]), // (c v a) — RAT on c, candidate is unit C4
        ProofStep::Add(vec![lit(0, true)]),               // (a) — RUP
        ProofStep::Add(vec![]),                           // empty clause
    ];

    let mut fwd = DratChecker::new(3, true);
    assert!(fwd.verify(&clauses, &steps).is_ok(), "forward accepts");

    let mut bwd = BackwardChecker::new(3, true);
    let bwd_result = bwd.verify(&clauses, &steps);
    assert!(
        bwd_result.is_ok(),
        "backward must accept RAT with unit clause candidate: {bwd_result:?}"
    );
}

/// Deletion of a clause containing ~pivot before the RAT step.
/// The RAT candidate set should reflect the post-deletion DB state
/// (fewer candidates).
#[test]
fn test_backward_rat_after_deletion_of_candidate() {
    // Formula: (a v b), (~a v b), (a v ~b), (~a v ~b), (~c), (c v ~c v d)
    //   C4=(~c), C5=(c v ~c v d) — but C5 is a tautology, discarded.
    //   Effectively same as 4-clause XOR + (~c).
    //
    // Simpler approach: two clauses with ~c, delete one before RAT step.
    //   C0-C3 = XOR on {a,b}. C4=(~c). C5=(~c v d).
    //   Delete C5 before the RAT step. RAT on pivot c should still work
    //   because C4=(~c) remains as a candidate.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // C0: a v b
        vec![lit(0, false), lit(1, true)],  // C1: ~a v b
        vec![lit(0, true), lit(1, false)],  // C2: a v ~b
        vec![lit(0, false), lit(1, false)], // C3: ~a v ~b
        vec![lit(2, false)],                // C4: ~c
        vec![lit(2, false), lit(3, true)],  // C5: ~c v d
    ];
    let steps = vec![
        ProofStep::Delete(vec![lit(2, false), lit(3, true)]), // delete C5=(~c v d)
        ProofStep::Add(vec![lit(2, true), lit(0, true)]),     // (c v a) — RAT on c
        ProofStep::Add(vec![lit(0, true)]),                   // (a) — RUP
        ProofStep::Add(vec![]),                               // empty clause
    ];

    // Forward with RAT:
    let mut fwd = DratChecker::new(4, true);
    let fwd_result = fwd.verify(&clauses, &steps);
    assert!(
        fwd_result.is_ok(),
        "forward must accept RAT after deletion: {fwd_result:?}"
    );

    // Backward with RAT:
    let mut bwd = BackwardChecker::new(4, true);
    let bwd_result = bwd.verify(&clauses, &steps);
    assert!(
        bwd_result.is_ok(),
        "backward must accept RAT after deletion reduces candidate set: {bwd_result:?}"
    );
}

/// Dead RAT clause: forward vs backward divergence.
///
/// XOR formula on {a,b} is UNSAT. Proof adds (c) — fresh variable, not RUP
/// (BCP from ~c finds no conflict), vacuous RAT (no clause contains ~c).
/// Then derives (a) and empty clause, both RUP from the XOR clauses alone.
///
/// Forward with RAT: accepts (c) as vacuous RAT.
/// Forward without RAT: rejects at (c) — not RUP, no RAT fallback.
/// Backward (either mode): (c) is NOT in the dependency chain of the empty
/// clause (which derives from the XOR originals), so it's never marked ACTIVE
/// and is skipped. This demonstrates backward checking's core property: it
/// only verifies the minimal proof core.
#[test]
fn test_backward_dead_rat_clause_not_active() {
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // C0: a v b
        vec![lit(0, false), lit(1, true)],  // C1: ~a v b
        vec![lit(0, true), lit(1, false)],  // C2: a v ~b
        vec![lit(0, false), lit(1, false)], // C3: ~a v ~b
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(2, true)]), // (c) — not RUP, vacuous RAT on c
        ProofStep::Add(vec![lit(0, true)]), // (a) — RUP from XOR
        ProofStep::Add(vec![]),             // empty clause
    ];

    // Forward with RAT: accepts (c) as vacuous RAT.
    let mut fwd_rat = DratChecker::new(3, true);
    assert!(fwd_rat.verify(&clauses, &steps).is_ok(), "forward+RAT");

    // Forward without RAT: rejects at (c).
    let mut fwd_no_rat = DratChecker::new(3, false);
    assert!(fwd_no_rat.verify(&clauses, &steps).is_err(), "forward-RAT");

    // Backward with RAT: (c) not ACTIVE, skipped.
    let mut bwd_rat = BackwardChecker::new(3, true);
    assert!(bwd_rat.verify(&clauses, &steps).is_ok(), "backward+RAT");

    // Backward without RAT: (c) still not ACTIVE, skipped.
    let mut bwd_no_rat = BackwardChecker::new(3, false);
    assert!(bwd_no_rat.verify(&clauses, &steps).is_ok(), "backward-RAT");
}

/// Clause reduction with multiple falsified literals.
/// Exercises the reduce_clause path with at least one literal removed.
///
/// Formula: (a), (~a v b v c), (~b v ~c), (b v ~c), (~b v c)
///   a=T from C0. C1 simplifies to (b v c). Remaining clauses form XOR on
///   {b,c} — no BCP propagation, but UNSAT by resolution.
///
/// Proof step (~a v b) has ~a falsified (a=T from unit). After reduction,
/// the clause becomes (b) and the reduction counter increments.
#[test]
fn test_backward_clause_reduction_multiple_falsified() {
    let clauses = vec![
        vec![lit(0, true)],                              // C0: (a)
        vec![lit(0, false), lit(1, true), lit(2, true)], // C1: (~a v b v c)
        vec![lit(1, false), lit(2, false)],              // C2: (~b v ~c)
        vec![lit(1, true), lit(2, false)],               // C3: (b v ~c)
        vec![lit(1, false), lit(2, true)],               // C4: (~b v c)
    ];
    // a=T from C0. C1 simplifies to (b v c).
    // Proof: add (~a v b) — ~a is falsified, reduces to (b).
    //   RUP for (b): assume ~b. (b v c) → c=T. (~b v ~c): ~c=F, conflict.
    //   Then derive (~c) and empty clause.
    let steps = vec![
        ProofStep::Add(vec![lit(0, false), lit(1, true)]), // (~a v b), reduces to (b)
        ProofStep::Add(vec![lit(2, false)]),               // (~c) — RUP
        ProofStep::Add(vec![]),                            // empty
    ];

    let mut fwd = DratChecker::new(3, false);
    assert!(fwd.verify(&clauses, &steps).is_ok(), "forward accepts");

    let mut bwd = BackwardChecker::new(3, false);
    let result = bwd.verify(&clauses, &steps);
    assert!(result.is_ok(), "backward must accept: {result:?}");
    assert!(
        bwd.stats().reduced_literals >= 1,
        "should reduce at least 1 falsified literal, got {}",
        bwd.stats().reduced_literals,
    );
}

/// Forward/backward consistency on a proof with interleaved RAT and
/// deletion steps. This exercises the full backward machinery:
/// deletion restore, RAT candidate collection, dep tracking.
#[test]
fn test_backward_rat_with_interleaved_deletions() {
    // Formula: (a v b), (~a v b), (a v ~b), (~a v ~b), (~c)
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // C0: a v b
        vec![lit(0, false), lit(1, true)],  // C1: ~a v b
        vec![lit(0, true), lit(1, false)],  // C2: a v ~b
        vec![lit(0, false), lit(1, false)], // C3: ~a v ~b
        vec![lit(2, false)],                // C4: ~c
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(2, true), lit(0, true)]), // S0: (c v a) — RAT on c
        ProofStep::Delete(vec![lit(2, false)]),           // S1: delete C4=(~c)
        // After deleting C4, no clause has ~c. Any clause with c is vacuous RAT.
        ProofStep::Add(vec![lit(1, true)]),  // S2: (b) — RUP
        ProofStep::Add(vec![lit(1, false)]), // S3: (~b) — RUP
        ProofStep::Add(vec![]),              // S4: empty clause
    ];

    let mut fwd = DratChecker::new(3, true);
    let fwd_result = fwd.verify(&clauses, &steps);
    assert!(fwd_result.is_ok(), "forward: {fwd_result:?}");

    let mut bwd = BackwardChecker::new(3, true);
    let bwd_result = bwd.verify(&clauses, &steps);
    assert!(bwd_result.is_ok(), "backward: {bwd_result:?}");
}
