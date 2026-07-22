// Copyright 2026 Andrew Yates
// Regression and medium-scale tests for the backward DRAT checker.
//
// Pigeonhole (CaDiCaL-generated, drat-trim verified) and soundness
// regression tests extracted from tests.rs for the 500-line limit (#5142).

use super::*;

fn lit(var: u32, positive: bool) -> Literal {
    if positive {
        Literal::from_dimacs(var as i32 + 1)
    } else {
        Literal::from_dimacs(-(var as i32 + 1))
    }
}

// ─── Medium-scale pigeonhole tests (CaDiCaL-generated, drat-trim verified) ──

/// PHP(3,2): 3 pigeons, 2 holes. 6 vars, 9 clauses, 7-step proof.
#[test]
fn test_backward_pigeonhole_3_2() {
    use crate::cnf_parser::parse_cnf;
    use crate::drat_parser::parse_drat;

    let cnf = "p cnf 6 9\n\
        1 2 0\n3 4 0\n5 6 0\n\
        -1 -3 0\n-1 -5 0\n-3 -5 0\n\
        -2 -4 0\n-2 -6 0\n-4 -6 0\n";
    let proof = "-2 0\n1 0\n-3 0\n-5 0\n4 0\n6 0\n0\n";

    let parsed_cnf = parse_cnf(cnf.as_bytes()).expect("valid CNF");
    let steps = parse_drat(proof.as_bytes()).expect("valid DRAT");
    assert_eq!(steps.len(), 7);

    let mut fwd = DratChecker::new(parsed_cnf.num_vars, false);
    assert!(fwd.verify(&parsed_cnf.clauses, &steps).is_ok(), "fwd");

    let mut bwd = BackwardChecker::new(parsed_cnf.num_vars, false);
    assert!(bwd.verify(&parsed_cnf.clauses, &steps).is_ok(), "bwd");
}

/// PHP(4,3): 4 pigeons, 3 holes. 12 vars, 22 clauses, 112-step proof
/// with 49 additions and 63 deletions. Exercises hash collision handling,
/// multi-level ACTIVE marking, and clause restoration in backward pass.
#[test]
fn test_backward_pigeonhole_4_3() {
    let (cnf, proof) = php43_instance();
    verify_forward_backward(cnf, proof, 100);
}

/// Returns (CNF, DRAT proof) for PHP(4,3). CaDiCaL-generated, drat-trim verified.
fn php43_instance() -> (&'static str, &'static str) {
    (
        "p cnf 12 22\n\
        1 2 3 0\n4 5 6 0\n7 8 9 0\n10 11 12 0\n\
        -1 -4 0\n-1 -7 0\n-1 -10 0\n\
        -4 -7 0\n-4 -10 0\n-7 -10 0\n\
        -2 -5 0\n-2 -8 0\n-2 -11 0\n\
        -5 -8 0\n-5 -11 0\n-8 -11 0\n\
        -3 -6 0\n-3 -9 0\n-3 -12 0\n\
        -6 -9 0\n-6 -12 0\n-9 -12 0\n",
        "-4 2 3 0\n-7 2 3 0\n-10 2 3 0\nd 2 1 3 0\nd -1 -4 0\nd -1 -7 0\n\
        d -1 -10 0\n-7 6 5 0\n-10 6 5 0\n6 5 2 3 0\nd 4 6 5 0\nd -4 -7 0\n\
        d -4 -10 0\nd -4 2 3 0\n-10 9 8 0\n9 8 2 3 0\n9 8 6 5 0\nd 7 9 8 0\n\
        d -7 -10 0\nd -7 2 3 0\nd -7 6 5 0\n12 11 2 3 0\n12 11 6 5 0\n\
        12 11 9 8 0\nd 10 12 11 0\nd -10 2 3 0\nd -10 6 5 0\nd -10 9 8 0\n\
        -8 6 5 3 0\n-11 6 5 3 0\n-5 9 8 3 0\n-11 9 8 3 0\n-5 12 11 3 0\n\
        -8 12 11 3 0\nd 6 5 2 3 0\nd 9 8 2 3 0\nd 12 11 2 3 0\nd -2 -5 0\n\
        d -2 -8 0\nd -2 -11 0\n-8 6 3 0\nd -8 6 5 3 0\n-11 6 3 0\n\
        d -11 6 5 3 0\n-11 9 8 6 0\n9 8 6 3 0\n9 8 6 12 11 3 0\n\
        -8 12 11 6 0\n12 11 6 9 8 3 0\n12 11 6 3 0\nd 9 8 6 5 0\n\
        d 12 11 6 5 0\nd -5 -8 0\nd -5 -11 0\nd -5 9 8 3 0\n\
        d -5 12 11 3 0\nd 9 8 6 12 11 3 0\nd 12 11 6 9 8 3 0\n\
        -3 12 11 8 0\n-3 -11 8 6 0\n-6 12 11 8 0\n-6 -11 8 3 0\n\
        -12 -11 8 3 0\n-12 -11 8 6 0\n-12 8 6 3 0\nd -3 -9 0\nd -6 -9 0\n\
        d -9 -12 0\nd 12 11 9 8 0\nd -11 9 8 3 0\nd -11 9 8 6 0\n\
        d 9 8 6 3 0\n-3 11 8 0\nd -3 12 11 8 0\n-6 11 8 0\n\
        d -6 12 11 8 0\n-6 -8 11 3 0\n-3 -8 11 6 0\n11 6 3 8 0\n\
        d -8 12 11 3 0\nd -8 12 11 6 0\nd 12 11 6 3 0\nd -3 -12 0\n\
        d -6 -12 0\nd -12 -11 8 3 0\nd -12 -11 8 6 0\nd -12 8 6 3 0\n\
        -6 -11 8 0\nd -6 -11 8 3 0\n-6 -8 11 0\nd -6 -8 11 3 0\n\
        11 6 8 0\nd 11 6 3 8 0\n-11 8 6 0\nd -3 -11 8 6 0\n\
        -8 11 6 0\nd -3 -8 11 6 0\nd -3 -6 0\nd -3 11 8 0\n\
        d -8 6 3 0\nd -11 6 3 0\n11 8 0\nd 11 6 8 0\nd -6 11 8 0\n\
        -11 8 0\nd -11 8 6 0\nd -6 -11 8 0\n-8 11 0\nd -8 11 6 0\n\
        d -6 -8 11 0\n11 0\n0\n",
    )
}

// ─── Soundness regression tests (#5258) ─────────────────────────────

/// Regression test for #5258: backward checker must reject proofs on SAT formulas.
/// Formula: (a v b) ^ (a v ~b) — satisfiable (a=T).
/// Proof: derive (~a) then derive empty clause.
/// Forward checker correctly rejects. Before #5258 fix, backward checker
/// accepted because:
///   Bug 1: inconsistent flag from forward replay not reset before backward pass
///   Bug 2: trail reason clauses not marked ACTIVE at conflict point
#[test]
fn test_backward_rejects_sat_formula_proof_issue_5258() {
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],  // a v b
        vec![lit(0, true), lit(1, false)], // a v ~b
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(0, false)]), // ~a — NOT RUP (a satisfies both clauses)
        ProofStep::Add(vec![]),              // empty clause
    ];
    let mut fwd = DratChecker::new(2, false);
    assert!(
        fwd.verify(&clauses, &steps).is_err(),
        "forward should reject invalid proof on SAT formula"
    );
    let mut bwd = BackwardChecker::new(2, false);
    assert!(
        bwd.verify(&clauses, &steps).is_err(),
        "backward should reject invalid proof on SAT formula (#5258)"
    );
}

/// Regression test for #5258 bug 2: incomplete ACTIVE marking.
/// Without marking trail reason clauses, original clauses in the BCP chain
/// are not ACTIVE, making the RAT check vacuously true.
#[test]
fn test_backward_rejects_non_rup_with_unit_propagation_5258() {
    let clauses = vec![
        vec![lit(0, true), lit(1, true)], // a v b
        vec![lit(0, false)],              // ~a (forces a=F, then b=T via clause 1)
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(1, false)]), // ~b — NOT RUP (b forced true)
        ProofStep::Add(vec![]),              // empty clause
    ];
    let mut fwd = DratChecker::new(2, false);
    assert!(
        fwd.verify(&clauses, &steps).is_err(),
        "forward should reject ~b derivation"
    );
    let mut bwd = BackwardChecker::new(2, false);
    assert!(
        bwd.verify(&clauses, &steps).is_err(),
        "backward should reject ~b derivation (#5258)"
    );
}

/// Soundness regression: backward checker must reject a proof that derives a
/// non-RUP clause on a SAT formula.
///
/// Formula: (a v b) ^ (a v ~b) — satisfiable (a=T).
/// Bogus proof: add (-a), then add empty clause.
///
/// The forward checker correctly rejects (-a) as not RUP/RAT. The backward
/// checker previously accepted it because the `inconsistent` flag set during
/// the forward pass short-circuited all check_rup() calls to return `true`
/// in the backward pass. drat-trim correctly rejects this.
///
/// Root cause: `inconsistent` flag was not reset before the backward pass.
/// Fix: reset `self.inner.inconsistent = false` before backward walk.
#[test]
fn test_backward_rejects_non_rup_on_sat_formula() {
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],  // a v b
        vec![lit(0, true), lit(1, false)], // a v ~b
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(0, false)]), // -a: not RUP or RAT
        ProofStep::Add(vec![]),              // empty clause
    ];

    let mut fwd = DratChecker::new(2, true);
    assert!(fwd.verify(&clauses, &steps).is_err(), "forward must reject");

    let mut bwd = BackwardChecker::new(2, true);
    assert!(
        bwd.verify(&clauses, &steps).is_err(),
        "backward must reject bogus proof on SAT formula"
    );
}

/// Soundness regression: backward checker must reject a proof with only an
/// empty clause (no valid derivation chain) on a SAT formula.
///
/// Formula: (a) ^ (b) — satisfiable (a=T, b=T).
/// Bogus proof: just the empty clause, no intermediate steps.
#[test]
fn test_backward_rejects_empty_clause_only_on_sat() {
    let clauses = vec![
        vec![lit(0, true)], // a
        vec![lit(1, true)], // b
    ];
    let steps = vec![ProofStep::Add(vec![])];

    let mut fwd = DratChecker::new(2, false);
    assert!(fwd.verify(&clauses, &steps).is_err(), "forward must reject");

    let mut bwd = BackwardChecker::new(2, false);
    assert!(
        bwd.verify(&clauses, &steps).is_err(),
        "backward must reject bare empty clause on SAT formula"
    );
}

// ─── Pseudo-unit deletion protection (drat-trim.c:806-814) ──────────

/// Pseudo-unit deletion protection: forward checker silently ignores deletion
/// of a clause that is the current propagation reason for a watched literal.
///
/// drat-trim.c:806-814: if `S->reason[abs(lemmas[0])] - 1 == lemmas - S->DB`,
/// the deletion is nullified. This prevents corrupting the BCP trail.
///
/// Scenario: XOR formula with 4 binary clauses (all unassigned at start).
/// The proof derives (a) — BCP propagates ~b via (~a v ~b) as reason.
/// Then the proof tries to delete (~a v ~b). Since it's the reason for
/// b's assignment, the deletion must be silently skipped.
#[test]
fn test_forward_pseudo_unit_deletion_skipped() {
    // Formula: (a v b), (~a v ~b), (a v ~b), (~a v b)
    // XOR encoding — UNSAT, no BCP from originals (all binary, no unit).
    //
    // Proof: add (a) — RUP. After adding, a=T on trail.
    //   BCP visits watches for ~a. First: C1=(~a v ~b) cidx=1 → propagates
    //   ~b with reason cidx=1. Second: C3=(~a v b) cidx=3 → b=false → conflict.
    //
    //   Now reasons[var_b] = Some(1) pointing to C1=(~a v ~b).
    //   Delete (~a v ~b) — this is the reason for b, must be skipped.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // C0: a v b
        vec![lit(0, false), lit(1, false)], // C1: ~a v ~b (reason for ~b after add(a))
        vec![lit(0, true), lit(1, false)],  // C2: a v ~b
        vec![lit(0, false), lit(1, true)],  // C3: ~a v b
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(0, true)]), // add (a) — RUP, propagates a=T
        // After BCP: a=T, C1 propagates ~b (b=F) with reason cidx=1.
        // Delete C1=(~a v ~b) — reason for b, pseudo-unit skip expected.
        ProofStep::Delete(vec![lit(0, false), lit(1, false)]),
        ProofStep::Add(vec![lit(1, true)]), // add (b) — always OK, already inconsistent
        ProofStep::Add(vec![]),             // empty clause
    ];

    let mut fwd = DratChecker::new(2, false);
    let result = fwd.verify(&clauses, &steps);
    assert!(result.is_ok(), "forward must accept: {result:?}");
    assert_eq!(
        fwd.stats.pseudo_unit_skips, 1,
        "deletion of reason clause must be silently skipped"
    );
}

/// Pseudo-unit deletion protection in backward checker: delete_forward skips
/// deletion of reason clauses, matching drat-trim behavior.
#[test]
fn test_backward_pseudo_unit_deletion_skipped() {
    // Same formula and proof as forward test.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // C0: a v b
        vec![lit(0, false), lit(1, false)], // C1: ~a v ~b
        vec![lit(0, true), lit(1, false)],  // C2: a v ~b
        vec![lit(0, false), lit(1, true)],  // C3: ~a v b
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(0, true)]),
        ProofStep::Delete(vec![lit(0, false), lit(1, false)]),
        ProofStep::Add(vec![lit(1, true)]),
        ProofStep::Add(vec![]),
    ];

    let mut bwd = BackwardChecker::new(2, false);
    let result = bwd.verify(&clauses, &steps);
    assert!(result.is_ok(), "backward must accept: {result:?}");
    assert_eq!(
        bwd.stats().pseudo_unit_skips,
        1,
        "backward delete_forward must skip reason clause deletion"
    );
}

/// Non-reason clause deletion proceeds normally (no pseudo-unit skip).
#[test]
fn test_forward_non_reason_deletion_proceeds() {
    // Formula: (a v b), (~a v b), (a v ~b), (~a v ~b) — UNSAT (XOR).
    // No BCP chain from originals (all binary, no unit).
    // Proof: add (b), delete (a v b) — (a v b) is NOT the reason for b
    // because b was added directly as a derived unit, not propagated via
    // the binary clause.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // a v b
        vec![lit(0, false), lit(1, true)],  // ~a v b
        vec![lit(0, true), lit(1, false)],  // a v ~b
        vec![lit(0, false), lit(1, false)], // ~a v ~b
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(1, true)]),                  // (b) — RUP
        ProofStep::Delete(vec![lit(0, true), lit(1, true)]), // delete (a v b) — not a reason
        ProofStep::Add(vec![lit(1, false)]),                 // (~b) — RUP
        ProofStep::Add(vec![]),                              // empty
    ];

    let mut fwd = DratChecker::new(2, false);
    let result = fwd.verify(&clauses, &steps);
    assert!(result.is_ok(), "forward must accept: {result:?}");
    assert_eq!(
        fwd.stats.pseudo_unit_skips, 0,
        "non-reason deletion must not trigger pseudo-unit skip"
    );
}

/// Forward and backward agree on pseudo-unit skip count.
#[test]
fn test_pseudo_unit_skip_forward_backward_consistency() {
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // a v b
        vec![lit(0, false), lit(1, false)], // ~a v ~b
        vec![lit(0, true), lit(1, false)],  // a v ~b
        vec![lit(0, false), lit(1, true)],  // ~a v b
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(0, true)]),
        ProofStep::Delete(vec![lit(0, false), lit(1, false)]),
        ProofStep::Add(vec![lit(1, true)]),
        ProofStep::Add(vec![]),
    ];

    let mut fwd = DratChecker::new(2, false);
    let fwd_result = fwd.verify(&clauses, &steps);
    let mut bwd = BackwardChecker::new(2, false);
    let bwd_result = bwd.verify(&clauses, &steps);

    assert_eq!(
        fwd_result.is_ok(),
        bwd_result.is_ok(),
        "forward and backward must agree: fwd={fwd_result:?} bwd={bwd_result:?}"
    );
    assert_eq!(
        fwd.stats.pseudo_unit_skips,
        bwd.stats().pseudo_unit_skips,
        "pseudo-unit skip counts must match"
    );
}

// ─── Helpers ─────────────────────────────────────────────────────────

/// Parse CNF + DRAT, verify both forward and backward accept.
fn verify_forward_backward(cnf: &str, proof: &str, min_steps: usize) {
    use crate::cnf_parser::parse_cnf;
    use crate::drat_parser::parse_drat;

    let parsed_cnf = parse_cnf(cnf.as_bytes()).expect("valid CNF");
    let steps = parse_drat(proof.as_bytes()).expect("valid DRAT");
    assert!(steps.len() >= min_steps, "proof steps: {}", steps.len());

    let mut fwd = DratChecker::new(parsed_cnf.num_vars, false);
    assert!(fwd.verify(&parsed_cnf.clauses, &steps).is_ok(), "fwd");

    let mut bwd = BackwardChecker::new(parsed_cnf.num_vars, false);
    assert!(bwd.verify(&parsed_cnf.clauses, &steps).is_ok(), "bwd");
}
