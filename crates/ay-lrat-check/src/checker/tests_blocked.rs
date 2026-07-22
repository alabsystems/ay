// Copyright 2026 Andrew Yates
// Tests for blocked clause (ER) verification.
// Extracted from tests_resolution.rs for the 500-line limit (#5142).
//
// Reference: CaDiCaL lratchecker.cpp:384-444 (check_blocked),
// lratchecker.cpp:503-508 (dispatch).

use super::*;
use crate::dimacs::Literal;

// ─── Blocked clause (ER) check ────────────────────────────────────────

/// Basic blocked clause test.
///
/// Setup: a clause is "blocked" on literal L if every clause containing ¬L
/// (not exempt via the proof chain) resolves tautologically with the imported clause.
///
/// Example: imported clause {a, b}. Negative hint exempts clause 2.
/// Clause 1: {¬a, c} — contains ¬a, not in proof chain → must resolve
/// tautologically. Resolution of {a,b} with {¬a,c}: cancel a/¬a → {b,c}.
/// Not tautological! So "a" is not a valid pivot.
///
/// Better example for ER: gate definition.
/// Tseitin encoding: x ↔ (a ∧ b) produces:
///   Clause 1: {¬x, a}     (x → a)
///   Clause 2: {¬x, b}     (x → b)
///   Clause 3: {x, ¬a, ¬b} (a ∧ b → x)
/// For ER: introduce the "long" clause {x, ¬a, ¬b} via blocked check.
/// Clause {x, ¬a, ¬b} is blocked on x if:
///   Every clause containing ¬x resolves tautologically with {x, ¬a, ¬b}.
///   Clause 1 {¬x, a}: resolve → {a, ¬a, ¬b} — tautological ✓ (contains a, ¬a)
///   Clause 2 {¬x, b}: resolve → {b, ¬a, ¬b} — tautological ✓ (contains b, ¬b)
/// So {x, ¬a, ¬b} is blocked.
///
/// In the proof chain, clauses 1 and 2 have negative IDs (they're the witnesses).
#[test]
fn test_blocked_clause_gate_definition() {
    let mut checker = LratChecker::new(4);
    // Gate: x ↔ (a ∧ b), variables: 1=x, 2=a, 3=b
    checker.add_original(1, &[lit(-1), lit(2)]); // ¬x ∨ a
    checker.add_original(2, &[lit(-1), lit(3)]); // ¬x ∨ b

    // Try to add {x, ¬a, ¬b} as a blocked clause.
    // Proof chain: negative IDs [-1, -2] referencing clauses 1 and 2.
    // Both clauses contain ¬x (lit(-1)), which is the negation of x (lit(1)).
    // x is in the imported clause, so ¬x might be a pivot.
    //
    // For clause 1 {¬x, a}: count overlap with imported {x, ¬a, ¬b} negation
    //   = {¬x, a, b}. Overlap: ¬x (yes), a (yes) → count=2. ✓
    //   Candidates in marks: ¬x is in marks? marks has {¬x, a, b} initially.
    //   Clause 1 literals {¬x, a}: ¬x is in marks (candidate). a is in marks.
    //   So candidates = [¬x, a]. Since imported literal x has negation ¬x in candidates,
    //   x remains a valid RAT candidate. ¬a has negation a in candidates, so ¬a remains.
    //   ¬b has negation b NOT in candidates [¬x, a] → remove b from marks.
    //
    // For clause 2 {¬x, b}: count overlap with {¬x, a, b}: ¬x (yes), b (yes) → count=2. ✓
    //   Candidates: ¬x, b. ¬a has neg a not in [¬x, b] → keep removing (already removed).
    //   x has neg ¬x in candidates → still valid.
    //
    // After all clauses: marks still has ¬x set (for literal x in imported clause).
    // At least one candidate → PASS.
    assert!(checker.add_derived(3, &[lit(1), lit(-2), lit(-3)], &[-1, -2]));
    assert_eq!(checker.stats.failures, 0);
}

/// Blocked check (direct) fails when a non-exempt clause prevents blocking.
///
/// Tests check_blocked() directly to avoid the RAT verification path
/// (which succeeds for this example because the witness clause literals
/// are already assigned by the clause negation).
#[test]
fn test_blocked_clause_fails_non_exempt_direct() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(-1), lit(2)]); // ¬x ∨ a
    checker.add_original(2, &[lit(-1), lit(3)]); // ¬x ∨ b
                                                 // Clause 3 contains ¬x but is NOT in the proof chain.
    checker.add_original(3, &[lit(-1)]); // ¬x (unit)

    // Direct blocked check: imported {x, ¬a, ¬b} with hints [-1, -2].
    // Clause 3 {¬x} is non-exempt: its literal ¬x overlaps with
    // checked_lits → eliminates x as a RAT candidate.
    // After all exempt clauses narrow the candidate set and the non-exempt
    // clause eliminates the last candidate, no candidates remain → FAIL.
    assert!(
        !checker.check_blocked(&[lit(1), lit(-2), lit(-3)], &[-1, -2]),
        "blocked check must fail: non-exempt clause 3 prevents blocking on x"
    );
}

/// Negative-only hints: RUP finds no positive hints, skips to blocked check.
#[test]
fn test_negative_only_hints_blocked_check() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(-1), lit(2)]); // ¬x ∨ a
    checker.add_original(2, &[lit(-1), lit(3)]); // ¬x ∨ b

    // Only negative hints: no RUP phase at all.
    assert!(checker.add_derived(3, &[lit(1), lit(-2), lit(-3)], &[-1, -2]));
    assert_eq!(checker.stats.failures, 0);
}

/// Blocked check with insufficient overlap (count < 2) fails.
#[test]
fn test_blocked_clause_insufficient_overlap() {
    let mut checker = LratChecker::new(4);
    // Clause 1: {¬x} — only one literal overlapping with negated imported clause.
    checker.add_original(1, &[lit(-1)]);

    // Imported: {x, ¬a}. Negation: {¬x, a}.
    // Clause 1 {¬x} is exempt (in proof chain with -1).
    // Overlap count: ¬x ∈ checked_lits? checked has {¬x, a}. ¬x → yes. count=1.
    // count < 2 → FAIL.
    assert!(
        !checker.add_derived(2, &[lit(1), lit(-2)], &[-1]),
        "blocked check must fail: only 1 overlapping literal (need ≥2)"
    );
}

// ─── Edge cases: blocked ─────────────────────────────────────────────

/// Blocked check with missing witness clause returns false.
#[test]
fn test_blocked_missing_witness_clause() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(-1), lit(2)]); // ¬x ∨ a
                                                 // Hint -99 references clause 99 which doesn't exist.
    assert!(!checker.check_blocked(&[lit(1), lit(-2)], &[-1, -99]));
    assert!(checker.checked_lits.iter().all(|&b| !b));
    assert!(checker.marks.iter().all(|&b| !b));
}

/// Blocked check state cleanup on success.
#[test]
fn test_blocked_cleanup_on_success() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(-1), lit(2)]); // ¬x ∨ a
    checker.add_original(2, &[lit(-1), lit(3)]); // ¬x ∨ b
    assert!(checker.check_blocked(&[lit(1), lit(-2), lit(-3)], &[-1, -2]));
    assert!(checker.checked_lits.iter().all(|&b| !b));
    assert!(checker.marks.iter().all(|&b| !b));
}

/// Blocked check state cleanup on failure (insufficient overlap).
#[test]
fn test_blocked_cleanup_on_failure() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(-1)]);
    assert!(!checker.check_blocked(&[lit(1), lit(-2)], &[-1]));
    assert!(checker.checked_lits.iter().all(|&b| !b));
    assert!(checker.marks.iter().all(|&b| !b));
}

/// Blocked check with empty hints (no negative IDs) has no witnesses → fails.
#[test]
fn test_blocked_empty_hints() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(-1), lit(2)]);
    // No negative hints → neg_ids is empty. No witness clauses.
    // All clauses are non-exempt → they eliminate candidates.
    assert!(!checker.check_blocked(&[lit(1), lit(-2)], &[]));
    assert!(checker.checked_lits.iter().all(|&b| !b));
    assert!(checker.marks.iter().all(|&b| !b));
}

// -- Blocked clause (check_blocked) tests --
// Reference: CaDiCaL `lratchecker.cpp:384-444`.

/// check_blocked: basic blocked clause acceptance.
///
/// Formula:
///   1: {1, 2}
///   2: {-1, -2}
///
/// Imported clause: {1, 3} with negative hint referencing clause 2.
/// Clause 2 contains negations of imported literals:
///   -1 is the negation of imported literal 1 → checked
///   -2 is not a negation of any imported literal
///
/// Actually, for check_blocked: marks are set at negations of imported
/// clause literals. Imported = {1, 3}, so we mark -1 and -3.
/// Clause 2 = {-1, -2}: -1 is marked (count=1), -2 not marked (count=1).
/// Count < 2 → fail? Let's construct a proper case.
///
/// Better construction:
///   1: {-1, -3}   (contains negations of both imported literals 1 and 3)
///
/// check_blocked marks -1 and -3. Clause 1 = {-1, -3}: both are marked → count=2 ≥ 2.
/// Clause 1 is in the proof chain. Candidates: -1 is negation of what? Imported = {1, 3}.
///   lit=-1: cl.negated() = cl=1, 1.negated() = -1 = lit. So candidate at idx=0.
///   lit=-3: cl.negated() = cl=3, 3.negated() = -3 = lit. So candidate at idx=1.
/// Both candidates survive → at least one RAT candidate → PASS.
#[test]
fn test_check_blocked_basic_accept() {
    let mut checker = LratChecker::new(4);
    // Proof chain clause: contains negations of both imported literals.
    checker.add_original(1, &[lit(-1), lit(-3)]);

    let clause = &[lit(1), lit(3)];
    let hints: &[i64] = &[-1]; // Negative hint referencing clause 1.

    let ok = checker.check_blocked(clause, hints);
    assert!(ok, "blocked clause with valid proof chain should pass");
}

/// check_blocked: marks clean after successful check.
#[test]
fn test_check_blocked_marks_clean_after_success() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(-1), lit(-3)]);

    let clause = &[lit(1), lit(3)];
    let hints: &[i64] = &[-1];

    let ok = checker.check_blocked(clause, hints);
    assert!(ok);

    assert!(
        checker.marks.iter().all(|&m| !m),
        "marks should be clean after check_blocked"
    );
}

/// check_blocked: proof chain clause with count < 2 → reject.
///
/// Proof chain clause has only 1 checked literal (count < 2).
///   1: {-1, 2}   (only -1 is a negation of an imported literal)
///
/// Imported: {1, 3}, marks: -1, -3.
/// Clause 1 = {-1, 2}: -1 marked (count=1), 2 not marked (count=1). Count < 2 → fail.
#[test]
fn test_check_blocked_proof_chain_count_too_low() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(-1), lit(2)]);

    let clause = &[lit(1), lit(3)];
    let hints: &[i64] = &[-1];

    let ok = checker.check_blocked(clause, hints);
    assert!(!ok, "proof chain clause with count < 2 should fail");
}

/// check_blocked: marks clean after failure (count < 2).
#[test]
fn test_check_blocked_marks_clean_after_count_failure() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(-1), lit(2)]);

    let clause = &[lit(1), lit(3)];
    let hints: &[i64] = &[-1];

    let ok = checker.check_blocked(clause, hints);
    assert!(!ok);

    assert!(
        checker.marks.iter().all(|&m| !m),
        "marks should be clean after failed check_blocked"
    );
}

/// check_blocked: missing negative hint clause → reject.
#[test]
fn test_check_blocked_missing_negative_hint() {
    let mut checker = LratChecker::new(4);
    // Clause 99 doesn't exist.
    let clause = &[lit(1), lit(2)];
    let hints: &[i64] = &[-99];

    let ok = checker.check_blocked(clause, hints);
    assert!(!ok, "missing negative hint clause should fail");

    assert!(
        checker.marks.iter().all(|&m| !m),
        "marks should be clean after missing-hint failure"
    );
}

/// check_blocked: non-proof-chain clause eliminates all RAT candidates → reject.
///
/// Setup:
///   1: {-1, -2}  (proof chain, count=2 ✓, candidates both survive)
///   2: {-1}      (non-proof, eliminates candidate at idx=0)
///   3: {-2}      (non-proof, eliminates candidate at idx=1)
///
/// Imported: {1, 2}. Marks: -1, -2.
/// Proof chain clause 1 = {-1, -2}: count=2, candidates_in_clause=[0,1]. Both survive.
/// Non-proof clause 2 = {-1}: -1 is marked → eliminates candidate 0 (clause[0]=1, 1.negated()=-1=lit).
/// Non-proof clause 3 = {-2}: -2 is marked → eliminates candidate 1 (clause[1]=2, 2.negated()=-2=lit).
/// All candidates eliminated → reject.
///
/// Note: HashMap iteration order is non-deterministic. We need all non-proof clauses
/// processed after the proof-chain clause for this to fail as expected. Since all
/// non-proof clauses eliminate candidates independently, order doesn't matter here.
#[test]
fn test_check_blocked_all_candidates_eliminated() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(-1), lit(-2)]);
    checker.add_original(2, &[lit(-1)]);
    checker.add_original(3, &[lit(-2)]);

    let clause = &[lit(1), lit(2)];
    let hints: &[i64] = &[-1]; // Only clause 1 is in proof chain.

    let ok = checker.check_blocked(clause, hints);
    assert!(
        !ok,
        "all RAT candidates eliminated by non-proof clauses should reject"
    );
}

/// check_blocked: empty imported clause (no candidates to survive) → reject.
#[test]
fn test_check_blocked_empty_clause() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1)]);

    let clause: &[Literal] = &[];
    let hints: &[i64] = &[-1];

    let ok = checker.check_blocked(clause, hints);
    assert!(!ok, "empty imported clause has no RAT candidates");
}

/// check_blocked with multiple proof-chain clauses.
///
///   1: {-1, -2}  (proof chain, count=2)
///   2: {-1, -3}  (proof chain, count=2, but eliminates candidate 1 since -3≠-2)
///
/// Imported: {1, 2, 3}. Marks: -1, -2, -3.
/// Clause 1: {-1,-2}: count=2. candidates_in_clause: idx 0 (1↔-1), idx 1 (2↔-2). Survive: [0,1,2]→keep 0,1; kill 2.
/// Clause 2: {-1,-3}: count=2. candidates_in_clause: idx 0 (1↔-1), idx 2 (3↔-3). From prev: [0,1,dead]→keep 0; kill 1.
/// Surviving: [0]. At least one → accept.
#[test]
fn test_check_blocked_multiple_proof_chain_clauses() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(-1), lit(-2)]);
    checker.add_original(2, &[lit(-1), lit(-3)]);

    let clause = &[lit(1), lit(2), lit(3)];
    let hints: &[i64] = &[-1, -2]; // Both are proof chain clauses.

    let ok = checker.check_blocked(clause, hints);
    assert!(
        ok,
        "multiple proof chain clauses with surviving candidate should pass"
    );
}
