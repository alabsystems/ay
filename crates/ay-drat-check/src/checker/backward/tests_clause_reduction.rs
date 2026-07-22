// Copyright 2026 Andrew Yates
// Tests for backward clause reduction (drat-trim.c:174-179, 935-950).
// Extracted from tests.rs for the 500-line limit (#5142).

use super::*;
use crate::checker::test_helpers::lit;

/// Test that backward clause reduction removes top-level falsified literals
/// before the RUP check (drat-trim sortSize() + truncation, lines 935-950).
///
/// The backward checker now uses the ORIGINAL proof step literals (not the
/// arena's simplified clause) for the RUP check. add_clause_internal strips
/// falsified literals during the forward pass, but drat-trim stores
/// unsimplified clauses and reduces them during the backward pass. Using
/// original literals enables the reduction counter to track removed literals.
#[test]
fn test_backward_clause_reduction_removes_falsified_literals() {
    // Formula: (a), (~a v b v c), (~b v ~c), (b v ~c), (~b v c)
    //
    // Original unit clause (a) forces a=true. (~a v b v c) simplifies to
    // (b v c) in the clause DB. The remaining clauses (b v c), (~b v ~c),
    // (b v ~c), (~b v c) are an XOR on b,c — UNSAT but no unit propagation.
    // So the formula is NOT immediately inconsistent from originals alone.
    //
    // Proof:
    //   step 0: add (~a v b) — original literals include ~a which is falsified
    //     (a=true from the unit clause). add_clause_internal simplifies this to
    //     (b) during the forward pass. Unit clause b=true propagates:
    //     (~b v ~c) → ~c. c=false. (b v ~c) → satisfied. (~b v c) → ~b=false,
    //     c=false → CONFLICT. Formula becomes inconsistent.
    //   step 1: add () — empty clause (after inconsistency)
    //
    // Backward pass:
    //   Step 0 is the conflict step (ACTIVE). The backward checker uses
    //   the ORIGINAL proof step literals [~a, b] for the RUP check. After
    //   unwinding to before step 0, a=true is on the trail (from original
    //   unit clause). Clause reduction removes ~a (falsified) → reduced
    //   clause is (b). RUP check on (b) succeeds.
    let clauses = vec![
        vec![lit(0, true)],                              // a
        vec![lit(0, false), lit(1, true), lit(2, true)], // ~a v b v c
        vec![lit(1, false), lit(2, false)],              // ~b v ~c
        vec![lit(1, true), lit(2, false)],               // b v ~c
        vec![lit(1, false), lit(2, true)],               // ~b v c
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(0, false), lit(1, true)]), // ~a v b
        ProofStep::Add(vec![]),                            // empty
    ];

    // Forward checker should also accept this proof.
    let mut fwd = DratChecker::new(3, false);
    assert!(
        fwd.verify(&clauses, &steps).is_ok(),
        "forward should verify"
    );

    let mut bwd = BackwardChecker::new(3, false);
    let result = bwd.verify(&clauses, &steps);
    assert!(
        result.is_ok(),
        "backward verification should succeed: {result:?}"
    );
    // The ~a literal should be removed by reduction since a=true from originals.
    assert!(
        bwd.stats().reduced_literals > 0,
        "clause reduction should remove at least one falsified literal, got {}",
        bwd.stats().reduced_literals,
    );
}

#[test]
fn test_backward_clause_reduction_removes_unused_assumed_literal() {
    // Unit-level test: check_rup_with_deps correctly identifies reducible
    // positions when a clause has extra literals not needed for the conflict.
    //
    // Formula: (a v b), (~a v b), (a v ~b), (~a v ~b) — UNSAT (XOR-2).
    //   No unit clauses → no BCP during add_original → checker NOT inconsistent.
    //
    // Clause (b v c): c is unused in the RUP derivation.
    //   assume ~b, ~c. (a v b) forces a=T (reason C0). (a v ~b) satisfied.
    //   (~a v ~b) with a=T, b=F → conflict (clause C3).
    //   Conflict analysis: marks a,b from C3; walks trail — b was assumed (no reason),
    //   a has reason C0 → marks a,b from C0. c was assumed but never marked → reducible.
    let mut checker = DratChecker::new(3, false);
    checker.add_original(&[lit(0, true), lit(1, true)]); // C0: a v b
    checker.add_original(&[lit(0, false), lit(1, true)]); // C1: ~a v b
    checker.add_original(&[lit(0, true), lit(1, false)]); // C2: a v ~b
    checker.add_original(&[lit(0, false), lit(1, false)]); // C3: ~a v ~b

    let result = checker.check_rup_with_deps(&[lit(1, true), lit(2, true)]); // (b v c)
    assert!(result.is_rup, "(b v c) must be RUP");
    assert!(
        result.reducible_positions.contains(&1),
        "position 1 (c) must be reducible: {:?}",
        result.reducible_positions
    );
    assert!(
        !result.reducible_positions.contains(&0),
        "position 0 (b) must NOT be reducible: {:?}",
        result.reducible_positions
    );
}

#[test]
fn test_backward_clause_reduction_no_removal_when_all_used() {
    // All literals in the proof clause participate in the conflict derivation.
    // No reduction should occur.
    //
    // Formula: (a v b), (~a v b), (a v ~b), (~a v ~b) — UNSAT (XOR).
    // Proof: add (b) — RUP: assume ~b. C1=(a v b) forces a (reason C0).
    //   C3=(~a v ~b) with a=true, b=false → conflict. Both a and b are used.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // a v b
        vec![lit(0, false), lit(1, true)],  // ~a v b
        vec![lit(0, true), lit(1, false)],  // a v ~b
        vec![lit(0, false), lit(1, false)], // ~a v ~b
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(1, true)]),  // (b) — all lits used
        ProofStep::Add(vec![lit(1, false)]), // (~b) — all lits used
        ProofStep::Add(vec![]),              // empty clause
    ];

    let mut bwd = BackwardChecker::new(2, false);
    assert!(bwd.verify(&clauses, &steps).is_ok(), "backward must accept");
    assert_eq!(
        bwd.stats().reduced_literals,
        0,
        "no reduction expected when all literals participate"
    );
}

#[test]
fn test_backward_clause_reduction_multiple_unused_literals() {
    // Unit-level test: check_rup_with_deps correctly identifies multiple
    // reducible positions when a clause has several extra literals.
    //
    // Formula: (a v b), (~a v b), (a v ~b), (~a v ~b) — UNSAT (XOR-2).
    //   No unit clauses → no BCP during add_original → checker NOT inconsistent.
    //
    // Clause (b v d v e): d and e are unused in the RUP derivation.
    //   assume ~b, ~d, ~e. (a v b) forces a=T. (~a v ~b) conflicts.
    //   d (pos 1) and e (pos 2) were assumed but never marked → reducible.
    let mut checker = DratChecker::new(5, false);
    checker.add_original(&[lit(0, true), lit(1, true)]); // C0: a v b
    checker.add_original(&[lit(0, false), lit(1, true)]); // C1: ~a v b
    checker.add_original(&[lit(0, true), lit(1, false)]); // C2: a v ~b
    checker.add_original(&[lit(0, false), lit(1, false)]); // C3: ~a v ~b

    let result = checker.check_rup_with_deps(&[lit(1, true), lit(3, true), lit(4, true)]); // (b v d v e)
    assert!(result.is_rup, "(b v d v e) must be RUP");
    assert_eq!(
        result.reducible_positions.len(),
        2,
        "d (pos 1) and e (pos 2) must be reducible: {:?}",
        result.reducible_positions
    );
    assert!(
        result.reducible_positions.contains(&1),
        "d at pos 1 must be reducible"
    );
    assert!(
        result.reducible_positions.contains(&2),
        "e at pos 2 must be reducible"
    );
}

#[test]
fn test_reduce_clause_helper() {
    // Unit test for the reduce_clause free function.
    let clause = vec![lit(0, true), lit(1, true), lit(2, true), lit(3, true)];
    let reduced = reduce_clause(&clause, &[1, 3]);
    assert_eq!(reduced.len(), 2);
    assert_eq!(reduced[0], lit(0, true));
    assert_eq!(reduced[1], lit(2, true));
}

#[test]
fn test_reduce_clause_empty_positions() {
    let clause = vec![lit(0, true), lit(1, true)];
    let reduced = reduce_clause(&clause, &[]);
    assert_eq!(reduced, clause);
}

#[test]
fn test_reduce_clause_all_positions() {
    let clause = vec![lit(0, true), lit(1, true)];
    let reduced = reduce_clause(&clause, &[0, 1]);
    assert!(reduced.is_empty());
}
