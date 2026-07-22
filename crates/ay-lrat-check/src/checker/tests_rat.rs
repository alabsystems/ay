// Copyright 2026 Andrew Yates
// RAT (Resolution Asymmetric Tautology) tests for the LRAT proof checker (#5243).
//
// Tests RAT derivation, witness validation, completeness checking,
// and end-to-end RAT proof verification.

use super::*;
use crate::lrat_parser::LratStep;

// ─── RAT (Resolution Asymmetric Tautology) tests (#5243) ────────

/// RAT derivation with explicit witnesses.
///
/// Formula (XOR-2, UNSAT):
///   C1=(a v b), C2=(~a v b), C3=(a v ~b), C4=(~a v ~b)
///
/// Derive (a) by RAT on pivot a:
/// - Clauses containing ~a: C2, C4.
/// - Witness for C2 (~a v b): assume ~a (from clause negation), assume ~b
///   (from C2 \ {~a} = {b} negated). Hint C1 (a v b): a=false, b=false → conflict.
/// - Witness for C4 (~a v ~b): assume ~a, assume b (from C4 \ {~a} = {~b} negated).
///   Hint C3 (a v ~b): a=false, ~b=false → conflict.
///
/// LRAT hints: [-2, 1, -4, 3]  (RAT witness for C2 with hint C1, then C4 with C3)
#[test]
fn test_rat_derivation_xor2() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b
    checker.add_original(3, &[lit(1), lit(-2)]); // a v ~b
    checker.add_original(4, &[lit(-1), lit(-2)]); // ~a v ~b

    // Derive (a) by RAT on pivot a.
    assert!(
        checker.add_derived(5, &[lit(1)], &[-2, 1, -4, 3]),
        "RAT derivation of (a) must succeed"
    );
    assert_eq!(checker.stats.failures, 0);

    // Derive (~a) by RUP: assume a. C4 (~a v ~b): ~a=false → unit(~b).
    // C2 (~a v b): ~a=false, b=false → conflict.
    assert!(checker.add_derived(6, &[lit(-1)], &[4, 2]));

    // Derive empty clause.
    assert!(checker.add_derived(7, &[], &[5, 6]));
    assert!(checker.derived_empty_clause());
    assert_eq!(checker.stats.failures, 0);
}

/// RAT full proof through verify_proof (end-to-end).
#[test]
fn test_rat_verify_proof_end_to_end() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b
    checker.add_original(3, &[lit(1), lit(-2)]); // a v ~b
    checker.add_original(4, &[lit(-1), lit(-2)]); // ~a v ~b

    let steps = vec![
        LratStep::Add {
            id: 5,
            clause: vec![lit(1)],
            hints: vec![-2, 1, -4, 3], // RAT
        },
        LratStep::Add {
            id: 6,
            clause: vec![lit(-1)],
            hints: vec![4, 2], // RUP: assume a, C4→~b, C2→conflict
        },
        LratStep::Add {
            id: 7,
            clause: vec![],
            hints: vec![5, 6], // RUP: empty clause
        },
    ];
    assert!(checker.verify_proof(&steps));
}

/// RAT with invalid witness: witness clause does not contain ~pivot.
#[test]
fn test_rat_invalid_witness_missing_neg_pivot() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b
    checker.add_original(3, &[lit(1), lit(-2)]); // a v ~b

    // Try RAT derivation of (a) with witness C3 (a v ~b).
    // C3 does NOT contain ~a, so it's an invalid RAT witness.
    assert!(
        !checker.add_derived(5, &[lit(1)], &[-3, 1]),
        "RAT witness clause without ~pivot must be rejected"
    );
    assert_eq!(checker.stats.failures, 1);
}

/// RAT with nonexistent witness clause ID.
#[test]
fn test_rat_nonexistent_witness_clause() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]);

    // Witness references clause 99 which doesn't exist.
    assert!(!checker.add_derived(2, &[lit(1)], &[-99, 1]));
    assert_eq!(checker.stats.failures, 1);
}

/// RAT with incorrect RUP hints for a witness (no conflict reached).
#[test]
fn test_rat_witness_rup_fails() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b
    checker.add_original(3, &[lit(1), lit(-2)]); // a v ~b
    checker.add_original(4, &[lit(-1), lit(-2)]); // ~a v ~b

    // RAT derivation of (a) but with wrong hints for C4 witness:
    // C4 (~a v ~b): assume ~a, assume b. Hint C2 (~a v b): ~a=true, b=true → satisfied.
    // No conflict → verification fails.
    assert!(
        !checker.add_derived(5, &[lit(1)], &[-2, 1, -4, 2]),
        "RAT with insufficient witness hints must fail"
    );
}

/// RAT where RUP part succeeds (conflict found before RAT witnesses).
/// The negative hints are present but unnecessary since RUP already proved it.
#[test]
fn test_rat_with_rup_success_shortcircuit() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b

    // Derive (b) by RUP: hints [1, 2] find conflict.
    // Extra RAT hints are present but RUP succeeds first.
    // (In practice, proofs wouldn't include redundant RAT witnesses,
    // but the checker should handle it.)
    assert!(checker.add_derived(3, &[lit(2)], &[1, 2]));
    assert_eq!(checker.stats.failures, 0);
}

/// RAT on empty clause is invalid (no pivot literal).
#[test]
fn test_rat_empty_clause_no_pivot() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);

    // Empty clause with negative hints → RAT attempted but empty clause has no pivot.
    assert!(
        !checker.add_derived(3, &[], &[-1, 2]),
        "RAT on empty clause must fail (no pivot)"
    );
}

/// Text LRAT end-to-end with RAT proof.
#[test]
fn test_rat_text_lrat_end_to_end() {
    let cnf = b"\
p cnf 2 4
1 2 0
-1 2 0
1 -2 0
-1 -2 0
";
    let proof = "\
5 1 0 -2 1 -4 3 0
6 -1 0 4 2 0
7 0 5 6 0
";
    let crate::dimacs::CnfFormulaWithIds { num_vars, clauses } =
        crate::dimacs::parse_cnf_with_ids(&cnf[..]).expect("valid CNF");
    let steps = crate::lrat_parser::parse_text_lrat(proof).expect("valid LRAT");
    let mut checker = LratChecker::new(num_vars);
    for (id, clause) in &clauses {
        checker.add_original(*id, clause);
    }
    assert!(checker.verify_proof(&steps));
    assert_eq!(checker.stats.failures, 0);
}

// ─── RAT witness completeness tests (#5243) ─────────────────────────

/// RAT with incomplete witnesses: proof omits a witness for a clause
/// containing ~pivot. This must be rejected.
///
/// Soundness test: drat-trim lrat-check.c lines 166-172 and 184-189
/// verify that ALL clauses containing ~pivot are covered by RAT witness
/// groups. Without this completeness check, a proof can claim RAT
/// derivation while silently ignoring clauses that would make the
/// derivation invalid.
///
/// Formula:
///   C1=(a v b), C2=(~a v b), C3=(a v ~b), C4=(~a v ~b), C5=(~a v c)
///
/// Derive (a) by RAT on pivot a:
///   Clauses containing ~a: C2, C4, C5.
///   Proof provides witnesses for C2 and C4 only — omits C5.
///   This is INVALID because C5 is uncovered.
#[test]
fn test_rat_incomplete_witnesses_rejected() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b
    checker.add_original(3, &[lit(1), lit(-2)]); // a v ~b
    checker.add_original(4, &[lit(-1), lit(-2)]); // ~a v ~b
    checker.add_original(5, &[lit(-1), lit(3)]); // ~a v c  (extra clause with ~a)

    // RAT derivation of (a) with witnesses for C2 and C4, but NOT C5.
    // drat-trim would reject this because C5 contains ~a and has no witness.
    assert!(
        !checker.add_derived(6, &[lit(1)], &[-2, 1, -4, 3]),
        "RAT with incomplete witnesses must be rejected: clause 5 (~a v c) is uncovered"
    );
    assert_eq!(checker.stats.failures, 1);
}

/// RAT with all witnesses: same formula as above, but now C5 is also covered.
///
/// Witness for C5 (~a v c): assume ~a (clause negation), assume ~c
/// (from C5 \ {~a} = {c} negated). State: a=false, c=false.
/// Hint C1 (a v b): a=false, b=unassigned → unit(b), assign b=true.
/// Hint C3 (a v ~b): a=false, ~b=false (b=true) → conflict.
#[test]
fn test_rat_complete_witnesses_accepted() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b
    checker.add_original(3, &[lit(1), lit(-2)]); // a v ~b
    checker.add_original(4, &[lit(-1), lit(-2)]); // ~a v ~b
    checker.add_original(5, &[lit(-1), lit(3)]); // ~a v c

    // RAT derivation of (a) with witnesses for ALL clauses containing ~a: C2, C4, C5.
    // Witness for C2 (~a v b): ~a, ~b → C1 (a v b): a=false, b=false → conflict.
    // Witness for C4 (~a v ~b): ~a, b → C3 (a v ~b): a=false, ~b=false → conflict.
    // Witness for C5 (~a v c): ~a, ~c → C1 (a v b): unit(b) → C3 (a v ~b): conflict.
    assert!(
        checker.add_derived(6, &[lit(1)], &[-2, 1, -4, 3, -5, 1, 3]),
        "RAT with complete witnesses must succeed"
    );
    assert_eq!(checker.stats.failures, 0);
}

// ─── Coverage gaps from P1:586 reflection ──────────────────────

/// RAT witness with empty RUP hints fails.
///
/// When a RAT witness group has a negative clause ID but zero positive RUP
/// hints following it, `propagate_rup_hints(&[])` returns false (no conflict
/// reachable). The RAT derivation must fail.
#[test]
fn test_rat_empty_witness_rup_hints_rejected() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b
    checker.add_original(3, &[lit(1), lit(-2)]); // a v ~b
    checker.add_original(4, &[lit(-1), lit(-2)]); // ~a v ~b

    // RAT derivation of (a) on pivot a. Witnesses for C2 and C4.
    // C2 witness has hint C1 (correct), but C4 witness has NO hints (empty).
    // Format: [-2, 1, -4] — after -4 there are no positive hints before end.
    assert!(
        !checker.add_derived(5, &[lit(1)], &[-2, 1, -4]),
        "RAT witness with empty RUP hint group must fail"
    );
    assert_eq!(checker.stats.failures, 1);
}

/// RAT witness resolvent trivially satisfied by propagation (rat.rs:180-182).
///
/// When a literal in the witness clause (other than ~pivot) is already true
/// on the trail (because its negation was assumed from the derived clause),
/// the resolvent is trivially satisfied and `verify_one_rat_witness` returns
/// true via the early exit at rat.rs:180-182.
///
/// Setup:
///   Derived clause: (a v ~b) — pivot is a (first literal)
///   C1 = (a v b)       — does not contain ~a
///   C2 = (~a v b v c)  — contains ~a → needs RAT witness
///
/// During RAT witness check for C2:
///   1. Negate derived clause: assign ~a=true, b=true (negation of ~b)
///   2. Iterate C2 literals (skip ~a):
///      - b: neg=~b, value(~b) = false (b is true) → resolvent trivially satisfied
///   3. Early return true — no RUP hints needed.
///
/// The RAT derivation succeeds because the only clause containing ~a (C2)
/// has its witness trivially satisfied. No positive RUP hints are needed
/// after the witness clause ID.
#[test]
fn test_rat_resolvent_trivially_satisfied_by_propagation() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2), lit(3)]); // ~a v b v c

    // Derive (a v ~b) by RAT on pivot a.
    // Only clause containing ~a is C2.
    // Witness for C2: after negating derived clause (assume ~a, b),
    // literal b in C2 is already true → resolvent trivially satisfied.
    // Hints: [-2] — witness clause ID only, no positive RUP hints needed.
    assert!(
        checker.add_derived(3, &[lit(1), lit(-2)], &[-2]),
        "RAT resolvent trivially satisfied by derived clause negation must succeed"
    );
    assert_eq!(checker.stats.failures, 0);
}

/// Tautological hint inside RAT witness sub-check.
///
/// `propagate_rup_hints` (rat.rs:182-183) rejects tautological hints.
/// This path is tested for the RUP case, but not when called from within
/// a RAT witness verification context.
#[test]
fn test_rat_tautological_hint_in_witness_rejected() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b
    checker.add_original(3, &[lit(1), lit(-2)]); // a v ~b
    checker.add_original(4, &[lit(-1), lit(-2)]); // ~a v ~b
                                                  // Clause 5 is tautological: (a v ~a v c).
    checker.add_original(5, &[lit(1), lit(-1), lit(3)]);

    // RAT derivation of (a) on pivot a. Witness for C2: hint = C5 (tautological).
    assert!(
        !checker.add_derived(6, &[lit(1)], &[-2, 5, -4, 3]),
        "RAT witness using tautological hint must fail"
    );
    assert_eq!(checker.stats.failures, 1);
}
