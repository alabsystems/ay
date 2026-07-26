// Copyright 2026 Andrew Yates
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0

//! Tests for theory conflict and propagation verification.

use ay_core::{TermId, TheoryConflict, TheoryLit};
use num_bigint::BigInt;

use super::dispatch::{
    classify_conflict_domain, classify_term_domain, verify_array_propagation,
    verify_bv_conflict_semantic, verify_bv_propagation, verify_lia_propagation,
    verify_lra_propagation, verify_mixed_conflict_semantic, verify_propagation_semantic,
    verify_string_conflict_structural, verify_string_propagation, TheoryDomain,
};
use super::*;

fn make_lit(term_id: u32, value: bool) -> TheoryLit {
    TheoryLit {
        term: TermId(term_id),
        value,
    }
}

#[test]
fn test_empty_conflict_rejected() {
    let result = verify_theory_conflict(&[]);
    assert!(matches!(result, Err(VerificationError::EmptyConflict)));
}

#[test]
fn test_single_literal_accepted() {
    // Single literal conflicts are valid (e.g., bounds conflicts like 0 <= -1)
    let conflict = vec![make_lit(1, true)];
    assert!(verify_theory_conflict(&conflict).is_ok());
}

#[test]
fn test_normal_conflict_accepted() {
    // Normal conflict with multiple distinct literals
    let conflict = vec![make_lit(1, true), make_lit(2, false), make_lit(3, true)];
    assert!(verify_theory_conflict(&conflict).is_ok());
}

#[test]
fn test_duplicate_literal_rejected() {
    // Same literal appearing twice is a bug
    let conflict = vec![
        make_lit(1, true),
        make_lit(2, false),
        make_lit(1, true), // Duplicate!
    ];
    let result = verify_theory_conflict(&conflict);
    assert!(matches!(
        result,
        Err(VerificationError::DuplicateLiteral {
            term: TermId(1),
            value: true
        })
    ));
}

#[test]
fn test_contradictory_literals_rejected() {
    // Same term with opposite values is a bug (self-contradictory conflict)
    let conflict = vec![
        make_lit(1, true),
        make_lit(1, false), // Contradictory!
    ];
    let result = verify_theory_conflict(&conflict);
    assert!(matches!(
        result,
        Err(VerificationError::ContradictoryLiterals { term: TermId(1) })
    ));
}

#[test]
fn test_distinct_terms_accepted() {
    // Multiple literals on different terms are fine
    let conflict = vec![
        make_lit(1, true),
        make_lit(2, true),
        make_lit(3, false),
        make_lit(4, false),
    ];
    assert!(verify_theory_conflict(&conflict).is_ok());
}

// NOTE: Bug #294 (spurious UNSAT on satisfiable blocking clauses) would NOT
// be caught by Phase 1 verification. The conflict literals in that bug were
// structurally valid (no duplicates, no contradictions), but the theory
// incorrectly claimed they were unsatisfiable together.
//
// To catch #294-style bugs, we need Phase 2 verification which would:
// 1. Take the conflict literals and build a mini SMT problem
// 2. Re-solve to verify they're actually UNSAT together
// 3. Fail if the mini-solver finds them SAT
//
// This is tracked in #298 Phase 2.

mod dedup_conflict_tests {
    use super::dispatch::verify_mixed_conflict_semantic;
    use super::*;
    use ay_core::{FarkasAnnotation, Sort, TermStore, TheoryConflict};

    /// Build the #6853 conflict shape observed downstream (verification-consumer
    /// index_range): `{logic_None != 0, logic_None <= 0, 0 <= logic_None}`.
    /// The two bounds force `logic_None = 0`, contradicting the disequality —
    /// jointly UNSAT over the integers.
    fn mk_6853_conflict(terms: &mut TermStore) -> Vec<TheoryLit> {
        let x = terms.mk_var("logic_None", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let x_eq_0 = terms.mk_eq(x, zero);
        let x_le_0 = terms.mk_le(x, zero);
        let zero_le_x = terms.mk_le(zero, x);
        vec![
            TheoryLit::new(x_eq_0, false), // logic_None != 0
            TheoryLit::new(x_le_0, true),
            TheoryLit::new(zero_le_x, true),
        ]
    }

    /// #6853: the 3-literal disequality+bounds conflict must verify UNSAT
    /// through both the domain dispatcher and the mixed (Nelson-Oppen)
    /// verifier, so the conflict is learned instead of churning.
    #[test]
    fn test_6853_three_literal_disequality_bounds_conflict_verifies_unsat() {
        let mut terms = TermStore::new();
        let conflict = mk_6853_conflict(&mut terms);

        assert!(
            verify_theory_conflict(&conflict).is_ok(),
            "structurally clean 3-literal conflict must pass"
        );
        assert!(
            verify_conflict_semantic(&conflict, &terms, &[]).is_ok(),
            "{{x != 0, x <= 0, 0 <= x}} is UNSAT and must be accepted by the dispatcher"
        );
        assert!(
            verify_mixed_conflict_semantic(&conflict, &terms, &[]).is_ok(),
            "{{x != 0, x <= 0, 0 <= x}} is UNSAT and must be accepted by the mixed verifier"
        );

        // Control (anti-optimism): dropping the disequality leaves a SATISFIABLE
        // set {x <= 0, 0 <= x} (x = 0). The verifiers must reject it — this
        // proves the Ok above is a genuine UNSAT verification, not an
        // optimistic skip.
        let sat_control = &conflict[1..];
        assert!(
            matches!(
                verify_conflict_semantic(sat_control, &terms, &[]),
                Err(VerificationError::ConflictIsSat)
            ),
            "{{x <= 0, 0 <= x}} is SAT and must be rejected by the dispatcher"
        );
        assert!(
            matches!(
                verify_mixed_conflict_semantic(sat_control, &terms, &[]),
                Err(VerificationError::ConflictIsSat)
            ),
            "{{x <= 0, 0 <= x}} is SAT and must be rejected by the mixed verifier"
        );
    }

    /// #4666: a duplicate-bearing copy of the #6853 conflict is structurally
    /// rejected as-is; after `dedup_conflict_literals` it passes the
    /// structural check AND verifies UNSAT semantically, so it can be
    /// learned (ending the re-derivation churn).
    #[test]
    fn test_4666_duplicate_literal_conflict_verifies_after_dedup() {
        let mut terms = TermStore::new();
        let clean = mk_6853_conflict(&mut terms);
        // {x != 0, x <= 0, x <= 0, 0 <= x} — duplicated middle literal.
        let mut with_dup = vec![clean[0], clean[1], clean[1], clean[2]];

        assert!(
            matches!(
                verify_theory_conflict(&with_dup),
                Err(VerificationError::DuplicateLiteral { .. })
            ),
            "pre-dedupe: duplicate literal must be structurally rejected"
        );

        dedup_conflict_literals(&mut with_dup);
        assert_eq!(with_dup, clean, "dedupe keeps first occurrences in order");
        assert!(verify_theory_conflict(&with_dup).is_ok());
        assert!(
            verify_conflict_semantic(&with_dup, &terms, &[]).is_ok(),
            "post-dedupe the conflict must verify UNSAT"
        );
    }

    /// Dedupe is EXACT-duplicate only: contradictory pairs (same term, both
    /// polarities) are preserved and still structurally rejected — a
    /// tautological conflict remains a surfaced producer bug.
    #[test]
    fn test_4666_dedup_preserves_contradictory_pairs() {
        let mut with_contradiction = vec![make_lit(1, true), make_lit(2, true), make_lit(1, false)];
        let before = with_contradiction.clone();
        dedup_conflict_literals(&mut with_contradiction);
        assert_eq!(with_contradiction, before, "no exact duplicates: untouched");
        assert!(matches!(
            verify_theory_conflict(&with_contradiction),
            Err(VerificationError::ContradictoryLiterals { .. })
        ));
    }

    /// Farkas-aware dedupe merges positional coefficients by SUM
    /// (λ₁·c + λ₂·c = (λ₁+λ₂)·c, non-negativity preserved).
    #[test]
    fn test_4666_dedup_farkas_merges_coefficients_by_sum() {
        let a = make_lit(1, true);
        let b = make_lit(2, false);
        let mut conflict =
            TheoryConflict::with_farkas(vec![a, b, a], FarkasAnnotation::from_ints(&[1, 2, 3]));
        dedup_conflict_with_farkas(&mut conflict);
        assert_eq!(conflict.literals, vec![a, b]);
        assert_eq!(
            conflict.farkas,
            Some(FarkasAnnotation::from_ints(&[4, 2])),
            "duplicate literal's coefficient must be summed into the first occurrence"
        );
        assert!(verify_theory_conflict(&conflict.literals).is_ok());
        assert!(verify_theory_conflict_with_farkas(&conflict).is_ok());
    }

    /// A mis-aligned Farkas annotation (wrong coefficient count) leaves the
    /// conflict untouched — the structural wrong-count error path plus the
    /// fail-closed semantic backstop is the correct handler for that bug.
    #[test]
    fn test_4666_dedup_farkas_length_mismatch_untouched() {
        let a = make_lit(1, true);
        let b = make_lit(2, false);
        let mut conflict =
            TheoryConflict::with_farkas(vec![a, b, a], FarkasAnnotation::from_ints(&[1, 2]));
        let before_lits = conflict.literals.clone();
        let before_farkas = conflict.farkas.clone();
        dedup_conflict_with_farkas(&mut conflict);
        assert_eq!(conflict.literals, before_lits);
        assert_eq!(conflict.farkas, before_farkas);
    }

    /// No-duplicate Farkas conflicts pass through byte-identical.
    #[test]
    fn test_4666_dedup_farkas_no_dup_untouched() {
        let a = make_lit(1, true);
        let b = make_lit(2, false);
        let mut conflict =
            TheoryConflict::with_farkas(vec![a, b], FarkasAnnotation::from_ints(&[1, 2]));
        let before = conflict.clone();
        dedup_conflict_with_farkas(&mut conflict);
        assert_eq!(conflict.literals, before.literals);
        assert_eq!(conflict.farkas, before.farkas);
    }
}

mod farkas_tests {
    use super::*;
    use ay_core::{FarkasAnnotation, Sort, TermStore};
    use num_rational::Rational64;

    #[test]
    fn test_valid_farkas_certificate() {
        let farkas = FarkasAnnotation::new(vec![
            Rational64::from(1),
            Rational64::from(2),
            Rational64::from(0),
        ]);
        assert!(verify_farkas_certificate(&farkas, 3).is_ok());
    }

    #[test]
    fn test_invalid_farkas_negative_coefficient() {
        let farkas = FarkasAnnotation::new(vec![
            Rational64::from(1),
            Rational64::from(-1), // Invalid!
            Rational64::from(2),
        ]);
        let result = verify_farkas_certificate(&farkas, 3);
        assert!(matches!(
            result,
            Err(VerificationError::InvalidFarkas { .. })
        ));
    }

    #[test]
    fn test_invalid_farkas_wrong_count() {
        let farkas = FarkasAnnotation::new(vec![Rational64::from(1), Rational64::from(2)]);
        let result = verify_farkas_certificate(&farkas, 3); // 2 coefficients, 3 literals
        assert!(matches!(
            result,
            Err(VerificationError::InvalidFarkas { .. })
        ));
    }

    #[test]
    fn test_conflict_with_valid_farkas() {
        let conflict = TheoryConflict::with_farkas(
            vec![make_lit(1, true), make_lit(2, false)],
            FarkasAnnotation::new(vec![Rational64::from(1), Rational64::from(1)]),
        );
        assert!(verify_theory_conflict_with_farkas(&conflict).is_ok());
    }

    #[test]
    fn test_conflict_with_invalid_farkas() {
        let conflict = TheoryConflict::with_farkas(
            vec![make_lit(1, true), make_lit(2, false)],
            FarkasAnnotation::new(vec![
                Rational64::from(1),
                Rational64::from(-1), // Invalid!
            ]),
        );
        let result = verify_theory_conflict_with_farkas(&conflict);
        assert!(matches!(
            result,
            Err(VerificationError::InvalidFarkas { .. })
        ));
    }

    /// Conflicts without Farkas annotation return MissingFarkasAnnotation (#6535).
    ///
    /// Previously this was a known gap where None annotations were silently
    /// accepted. Now the verification function explicitly reports the missing
    /// annotation so callers can distinguish it from invalid certificates.
    #[test]
    fn test_conflict_without_farkas_returns_missing_annotation() {
        let conflict = TheoryConflict::new(vec![make_lit(1, true), make_lit(2, false)]);
        let result = verify_theory_conflict_with_farkas(&conflict);
        assert!(
            matches!(result, Err(VerificationError::MissingFarkasAnnotation)),
            "Expected MissingFarkasAnnotation for None farkas, got: {result:?}"
        );
        // The error should be classified as a missing annotation (non-fatal)
        assert!(
            result.as_ref().unwrap_err().is_missing_annotation(),
            "MissingFarkasAnnotation should return true for is_missing_annotation()"
        );
    }

    /// verify_theory_conflict_with_farkas_full also returns MissingFarkasAnnotation
    /// for conflicts without Farkas annotations (#6535).
    #[test]
    fn test_full_conflict_without_farkas_returns_missing_annotation() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let five = terms.mk_int(BigInt::from(5));
        let ten = terms.mk_int(BigInt::from(10));

        // x <= 5 AND x >= 10 — genuinely UNSAT, but no Farkas certificate
        let x_le_5 = terms.mk_le(x, five);
        let x_ge_10 = terms.mk_ge(x, ten);
        let conflict = TheoryConflict::new(vec![
            TheoryLit::new(x_le_5, true),
            TheoryLit::new(x_ge_10, true),
        ]);
        assert!(conflict.farkas.is_none(), "Precondition: no Farkas");

        let result = verify_theory_conflict_with_farkas_full(&conflict, &terms);
        assert!(
            matches!(result, Err(VerificationError::MissingFarkasAnnotation)),
            "Expected MissingFarkasAnnotation for None farkas in _full, got: {result:?}"
        );
    }

    /// InvalidFarkas should NOT be classified as a missing annotation.
    #[test]
    fn test_invalid_farkas_is_not_missing_annotation() {
        let err = VerificationError::InvalidFarkas {
            reason: "negative coefficient".to_string(),
        };
        assert!(
            !err.is_missing_annotation(),
            "InvalidFarkas should return false for is_missing_annotation()"
        );
    }

    #[test]
    fn test_conflict_with_duplicate_and_farkas() {
        // Structural error should be caught even with valid Farkas
        let conflict = TheoryConflict::with_farkas(
            vec![make_lit(1, true), make_lit(1, true)], // Duplicate!
            FarkasAnnotation::new(vec![Rational64::from(1), Rational64::from(1)]),
        );
        let result = verify_theory_conflict_with_farkas(&conflict);
        assert!(matches!(
            result,
            Err(VerificationError::DuplicateLiteral { .. })
        ));
    }

    /// Regression test for #4515: verify_theory_conflict_with_farkas_full
    /// now runs in all builds (including release). This test exercises the
    /// full TheoryConflict → semantic Farkas verification path that was
    /// previously gated behind cfg(debug_assertions).
    #[test]
    fn test_farkas_full_via_theory_conflict_entry_point() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let five = terms.mk_int(BigInt::from(5));
        let ten = terms.mk_int(BigInt::from(10));

        // x <= 5 AND x >= 10 is UNSAT with Farkas λ=[1,1]
        let x_le_5 = terms.mk_le(x, five);
        let x_ge_10 = terms.mk_ge(x, ten);

        let conflict = TheoryConflict::with_farkas(
            vec![TheoryLit::new(x_le_5, true), TheoryLit::new(x_ge_10, true)],
            FarkasAnnotation::new(vec![Rational64::from(1), Rational64::from(1)]),
        );

        // This exercises verify_theory_conflict_with_farkas_full — the entry
        // point used at all integration sites, now unconditional in release.
        assert!(
            verify_theory_conflict_with_farkas_full(&conflict, &terms).is_ok(),
            "Valid Farkas conflict should pass full semantic verification"
        );

        // Also verify rejection of bad coefficients via the full path
        let bad_conflict = TheoryConflict::with_farkas(
            vec![TheoryLit::new(x_le_5, true), TheoryLit::new(x_ge_10, true)],
            FarkasAnnotation::new(vec![Rational64::from(1), Rational64::from(0)]),
        );
        let result = verify_theory_conflict_with_farkas_full(&bad_conflict, &terms);
        assert!(
            result.is_err(),
            "Bad Farkas coefficients (λ₂=0 drops a constraint) should be rejected. Got: {result:?}"
        );
    }

    #[test]
    fn test_full_farkas_verification_simple_bounds_conflict() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let five = terms.mk_int(BigInt::from(5));
        let ten = terms.mk_int(BigInt::from(10));

        // x <= 5
        let x_le_5 = terms.mk_le(x, five);
        // x >= 10 is normalized in TermStore as (<= 10 x)
        let x_ge_10 = terms.mk_ge(x, ten);

        let conflict_lits = vec![TheoryLit::new(x_le_5, true), TheoryLit::new(x_ge_10, true)];
        let farkas = FarkasAnnotation::new(vec![Rational64::from(1), Rational64::from(1)]);

        assert!(verify_farkas_certificate_full(&terms, &conflict_lits, &farkas).is_ok());
    }

    #[test]
    fn test_full_farkas_verification_strict_contradiction() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));

        // x < 0
        let x_lt_0 = terms.mk_lt(x, zero);
        // x >= 0 normalized as (<= 0 x)
        let x_ge_0 = terms.mk_ge(x, zero);

        let conflict_lits = vec![TheoryLit::new(x_lt_0, true), TheoryLit::new(x_ge_0, true)];
        let farkas = FarkasAnnotation::new(vec![Rational64::from(1), Rational64::from(1)]);

        assert!(verify_farkas_certificate_full(&terms, &conflict_lits, &farkas).is_ok());
    }

    #[test]
    fn test_full_farkas_verification_handles_equality_orientation() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let one = terms.mk_int(BigInt::from(1));

        // x = 0
        let x_eq_0 = terms.mk_eq(x, zero);
        // x >= 1 normalized as (<= 1 x)
        let x_ge_1 = terms.mk_ge(x, one);

        let conflict_lits = vec![TheoryLit::new(x_eq_0, true), TheoryLit::new(x_ge_1, true)];
        let farkas = FarkasAnnotation::new(vec![Rational64::from(1), Rational64::from(1)]);

        assert!(verify_farkas_certificate_full(&terms, &conflict_lits, &farkas).is_ok());
    }

    #[test]
    fn test_full_farkas_verification_rejects_bad_coefficients() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let five = terms.mk_int(BigInt::from(5));
        let ten = terms.mk_int(BigInt::from(10));

        let x_le_5 = terms.mk_le(x, five);
        let x_ge_10 = terms.mk_ge(x, ten);

        let conflict_lits = vec![TheoryLit::new(x_le_5, true), TheoryLit::new(x_ge_10, true)];
        // Wrong coefficients: doesn't eliminate `x`.
        let farkas = FarkasAnnotation::new(vec![Rational64::from(1), Rational64::from(0)]);

        let result = verify_farkas_certificate_full(&terms, &conflict_lits, &farkas);
        assert!(matches!(
            result,
            Err(VerificationError::InvalidFarkas { .. })
        ));
    }

    /// Discriminating test for Issue #308: LIA GCD conflicts don't have valid Farkas certificates.
    ///
    /// The Farkas lemma applies to real-valued linear systems:
    /// A system Ax ≤ b is infeasible iff ∃λ≥0: λᵀA = 0 and λᵀb < 0.
    ///
    /// GCD/divisibility failures (e.g., 2x = 1 is UNSAT over integers because 2∤1)
    /// are NOT Farkas-provable. For the single constraint 2x - 1 = 0:
    /// - Any non-zero λ produces λ*2 ≠ 0 (variable not eliminated)
    /// - λ=0 produces 0 ≤ 0, which is not a contradiction
    ///
    /// Therefore, LIA's GCD test MUST return TheoryResult::Unsat (without Farkas),
    /// not UnsatWithFarkas. This test verifies the verification correctly rejects
    /// invalid certificates for GCD failures.
    #[test]
    fn test_farkas_rejects_gcd_style_single_equality() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let two = terms.mk_int(BigInt::from(2));
        let one = terms.mk_int(BigInt::from(1));

        // 2*x = 1 (UNSAT over integers due to GCD, but no valid Farkas certificate)
        let two_x = terms.mk_mul(vec![two, x]);
        let eq = terms.mk_eq(two_x, one);

        // Attempt to use Farkas coefficient 1 for this single equality
        let conflict_lits = vec![TheoryLit::new(eq, true)];
        let farkas = FarkasAnnotation::new(vec![Rational64::from(1)]);

        // This MUST fail because λ=1 gives coefficient 2 on x, which doesn't cancel
        let result = verify_farkas_certificate_full(&terms, &conflict_lits, &farkas);
        assert!(
            matches!(result, Err(VerificationError::InvalidFarkas { .. })),
            "GCD-style conflicts should not have valid Farkas certificates. \
             The LIA solver should use TheoryResult::Unsat, not UnsatWithFarkas, \
             for GCD test failures. Got: {result:?}"
        );
    }

    /// Test that multi-variable equalities without proper cancellation are rejected.
    ///
    /// This catches #308: LIA's check_integer_bounds_conflict() sets λ=1 for all
    /// reasons, which doesn't produce valid Farkas certificates when multiple
    /// constraints involve different coefficients.
    #[test]
    fn test_farkas_rejects_naive_lambda_ones_for_complex_conflict() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let one = terms.mk_int(BigInt::from(1));
        let two = terms.mk_int(BigInt::from(2));
        let three = terms.mk_int(BigInt::from(3));

        // Create constraints where λ=[1,1,1] doesn't produce valid certificate:
        // x + y <= 2   (normalized: x + y - 2 <= 0)
        // x + y >= 3   (normalized: -x - y + 3 <= 0)
        // These together: (x + y - 2) + (-x - y + 3) = 1 <= 0, which IS a contradiction
        // BUT if we add a third constraint like x <= 1, naive λ=[1,1,1] fails
        let x_plus_y = terms.mk_add(vec![x, y]);
        let le_2 = terms.mk_le(x_plus_y, two);
        let ge_3 = terms.mk_ge(x_plus_y, three);
        let x_le_1 = terms.mk_le(x, one);

        // Conflict with 3 constraints and naive λ=[1,1,1]
        let conflict_lits = vec![
            TheoryLit::new(le_2, true),
            TheoryLit::new(ge_3, true),
            TheoryLit::new(x_le_1, true),
        ];
        let farkas = FarkasAnnotation::new(vec![
            Rational64::from(1),
            Rational64::from(1),
            Rational64::from(1),
        ]);

        // This should fail because the third constraint adds x coefficient without cancellation
        let result = verify_farkas_certificate_full(&terms, &conflict_lits, &farkas);
        assert!(
            matches!(result, Err(VerificationError::InvalidFarkas { .. })),
            "Naive λ=[1,1,1] should fail when constraints have different variable coefficients. \
             LIA must compute proper Farkas coefficients. Got: {result:?}"
        );
    }

    /// Verify that valid 2-constraint Farkas certificates still pass.
    /// This ensures we're not breaking correct behavior while fixing #308.
    #[test]
    fn test_farkas_accepts_valid_two_constraint_bounds() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let five = terms.mk_int(BigInt::from(5));
        let ten = terms.mk_int(BigInt::from(10));

        // x <= 5 AND x >= 10 is UNSAT with valid Farkas λ=[1,1]
        // Combination: (x - 5) + (-x + 10) = 5 <= 0, FALSE -> contradiction
        let x_le_5 = terms.mk_le(x, five);
        let x_ge_10 = terms.mk_ge(x, ten);

        let conflict_lits = vec![TheoryLit::new(x_le_5, true), TheoryLit::new(x_ge_10, true)];
        let farkas = FarkasAnnotation::new(vec![Rational64::from(1), Rational64::from(1)]);

        // This SHOULD pass
        let result = verify_farkas_certificate_full(&terms, &conflict_lits, &farkas);
        assert!(
            result.is_ok(),
            "Valid simple bounds conflict with λ=[1,1] should pass verification. Got: {result:?}"
        );
    }
}

mod euf_verification {
    use super::*;
    use ay_core::{Sort, Symbol, TermStore};

    /// Test that a valid EUF transitivity conflict is verified as UNSAT.
    #[test]
    fn test_verify_euf_transitivity_conflict() {
        let mut terms = TermStore::new();
        let u = Sort::Uninterpreted("U".to_string());
        let a = terms.mk_var("a", u.clone());
        let b = terms.mk_var("b", u.clone());
        let c = terms.mk_var("c", u);

        let eq_ab = terms.mk_eq(a, b);
        let eq_bc = terms.mk_eq(b, c);
        let eq_ac = terms.mk_eq(a, c);

        // Conflict: a=b, b=c, a≠c (UNSAT via transitivity)
        let conflict = vec![
            TheoryLit::new(eq_ab, true),
            TheoryLit::new(eq_bc, true),
            TheoryLit::new(eq_ac, false),
        ];

        let result = verify_euf_conflict(&conflict, &terms, &[]);
        assert!(
            result.is_ok(),
            "Transitivity conflict should verify as UNSAT: {result:?}"
        );
    }

    /// Test that a valid EUF congruence conflict is verified as UNSAT.
    #[test]
    fn test_verify_euf_congruence_conflict() {
        let mut terms = TermStore::new();
        let u = Sort::Uninterpreted("U".to_string());
        let a = terms.mk_var("a", u.clone());
        let b = terms.mk_var("b", u.clone());

        let f_a = terms.mk_app(Symbol::named("f"), vec![a], u.clone());
        let f_b = terms.mk_app(Symbol::named("f"), vec![b], u);

        let eq_ab = terms.mk_eq(a, b);
        let eq_fa_fb = terms.mk_eq(f_a, f_b);

        // Conflict: a=b, f(a)≠f(b) (UNSAT via congruence)
        let conflict = vec![TheoryLit::new(eq_ab, true), TheoryLit::new(eq_fa_fb, false)];

        let result = verify_euf_conflict(&conflict, &terms, &[]);
        assert!(
            result.is_ok(),
            "Congruence conflict should verify as UNSAT: {result:?}"
        );
    }

    /// Test that a satisfiable set of literals is rejected.
    #[test]
    fn test_verify_euf_sat_rejected() {
        let mut terms = TermStore::new();
        let u = Sort::Uninterpreted("U".to_string());
        let a = terms.mk_var("a", u.clone());
        let b = terms.mk_var("b", u.clone());
        let c = terms.mk_var("c", u);

        let eq_ab = terms.mk_eq(a, b);
        let eq_bc = terms.mk_eq(b, c);

        // This is SAT: a≠b, b≠c (no transitivity forces anything)
        let conflict = vec![TheoryLit::new(eq_ab, false), TheoryLit::new(eq_bc, false)];

        let result = verify_euf_conflict(&conflict, &terms, &[]);
        assert!(
            matches!(result, Err(VerificationError::ConflictIsSat)),
            "Satisfiable literals should be rejected: {result:?}"
        );
    }

    /// Test that an empty conflict is rejected (caught by basic verification).
    #[test]
    fn test_verify_euf_empty_rejected() {
        let terms = TermStore::new();
        let result = verify_euf_conflict(&[], &terms, &[]);
        assert!(
            matches!(result, Err(VerificationError::EmptyConflict)),
            "Empty conflict should be rejected: {result:?}"
        );
    }

    /// Test verification with a longer equality chain.
    #[test]
    fn test_verify_euf_long_chain_conflict() {
        let mut terms = TermStore::new();
        let u = Sort::Uninterpreted("U".to_string());

        // Create x0, x1, x2, x3, x4
        let x: Vec<_> = (0..5)
            .map(|i| terms.mk_var(format!("x{i}"), u.clone()))
            .collect();

        // Equalities: x0=x1, x1=x2, x2=x3, x3=x4
        let equalities: Vec<_> = (0..4).map(|i| terms.mk_eq(x[i], x[i + 1])).collect();
        let diseq_0_4 = terms.mk_eq(x[0], x[4]);

        // Conflict: all equalities hold, but x0 ≠ x4
        let mut conflict: Vec<_> = equalities
            .iter()
            .map(|&eq| TheoryLit::new(eq, true))
            .collect();
        conflict.push(TheoryLit::new(diseq_0_4, false));

        let result = verify_euf_conflict(&conflict, &terms, &[]);
        assert!(
            result.is_ok(),
            "Long chain conflict should verify as UNSAT: {result:?}"
        );
    }

    /// #8123: a datatype constructor-clash conflict (`self = Ok(a) AND
    /// self = Err(b)`) is UNSAT only because distinct constructors are disjoint.
    /// Pure EUF treats `Ok`/`Err` as uninterpreted functions, so without the
    /// datatype tautology axioms the fresh solver reports SAT and the conflict
    /// is spuriously rejected. With the generated disjointness/tester
    /// tautologies it must verify as UNSAT. This is the exact shape that killed
    /// own.rs::transpose.
    #[test]
    fn test_verify_euf_constructor_clash_needs_dt_axioms_8123() {
        use crate::verification::build_datatype_tautology_axioms;
        use ay_core::term::Symbol;
        use std::collections::HashMap;

        let mut terms = TermStore::new();
        let dt = Sort::Uninterpreted("ownresult".to_string());

        // self : ownresult, and two constructor applications Ok(a), Err(b).
        let self_v = terms.mk_var("self", dt.clone());
        let a = terms.mk_var("a", Sort::Int);
        let b = terms.mk_var("b", Sort::Int);
        let ok_a = terms.mk_app(Symbol::named("Ok"), vec![a], dt.clone());
        let err_b = terms.mk_app(Symbol::named("Err"), vec![b], dt);

        let eq_self_ok = terms.mk_eq(self_v, ok_a);
        let eq_self_err = terms.mk_eq(self_v, err_b);

        // Conflict: self = Ok(a) AND self = Err(b).
        let conflict = vec![
            TheoryLit::new(eq_self_ok, true),
            TheoryLit::new(eq_self_err, true),
        ];

        // Without datatype axioms: pure EUF sees Ok/Err as UF, conflict is SAT.
        let without = verify_euf_conflict(&conflict, &terms, &[]);
        assert!(
            matches!(without, Err(VerificationError::ConflictIsSat)),
            "without dt axioms, constructor-clash conflict looks SAT to pure EUF: {without:?}"
        );

        // Generate the datatype tautology axioms (disjointness + tester eval).
        let mut dt_ctors: HashMap<String, Vec<String>> = HashMap::new();
        dt_ctors.insert(
            "ownresult".to_string(),
            vec!["Ok".to_string(), "Err".to_string()],
        );
        let axioms = build_datatype_tautology_axioms(&mut terms, &dt_ctors);
        assert!(
            !axioms.is_empty(),
            "expected disjointness/tester tautologies for Ok/Err applications"
        );

        // With the datatype tautologies: the conflict is genuinely UNSAT.
        let with = verify_euf_conflict(&conflict, &terms, &axioms);
        assert!(
            with.is_ok(),
            "with dt tautology axioms, constructor-clash conflict must verify as UNSAT: {with:?}"
        );
    }

    /// #8123 soundness: the datatype tautology axioms must NOT manufacture a
    /// spurious conflict. A genuinely-SAT literal set (`self = Ok(a)` alone,
    /// with no contradicting constructor) stays SAT even with the tautologies
    /// asserted, so the verifier still rejects it as not-a-conflict.
    #[test]
    fn test_dt_axioms_do_not_manufacture_conflict_8123() {
        use crate::verification::build_datatype_tautology_axioms;
        use ay_core::term::Symbol;
        use std::collections::HashMap;

        let mut terms = TermStore::new();
        let dt = Sort::Uninterpreted("ownresult".to_string());
        let self_v = terms.mk_var("self", dt.clone());
        let a = terms.mk_var("a", Sort::Int);
        let ok_a = terms.mk_app(Symbol::named("Ok"), vec![a], dt);
        let eq_self_ok = terms.mk_eq(self_v, ok_a);

        // A satisfiable singleton "conflict": self = Ok(a). Not actually UNSAT.
        let fake_conflict = vec![TheoryLit::new(eq_self_ok, true)];

        let mut dt_ctors: HashMap<String, Vec<String>> = HashMap::new();
        dt_ctors.insert(
            "ownresult".to_string(),
            vec!["Ok".to_string(), "Err".to_string()],
        );
        let axioms = build_datatype_tautology_axioms(&mut terms, &dt_ctors);

        let result = verify_euf_conflict(&fake_conflict, &terms, &axioms);
        assert!(
            matches!(result, Err(VerificationError::ConflictIsSat)),
            "tautology axioms must not turn a SAT literal set into a spurious conflict: {result:?}"
        );
    }

    /// Unknown UF-containing Int equalities must not be ignored when they
    /// appear before a plain EUF literal in a conflict. The `take_first_mut`
    /// regression had several `seq_offset`/`seq_len` equalities followed by a
    /// final EUF equality; classifying that as pure EUF made semantic
    /// verification report SAT and fail closed to Unknown.
    #[test]
    fn test_unknown_then_euf_conflict_routes_to_mixed_verifier_6853() {
        let mut terms = TermStore::new();
        let u = Sort::Uninterpreted("Seq".to_string());
        let a = terms.mk_var("a", u.clone());
        let b = terms.mk_var("b", u.clone());
        let offset_a = terms.mk_app(Symbol::named("seq_offset"), vec![a], Sort::Int);
        let offset_b = terms.mk_app(Symbol::named("seq_offset"), vec![b], Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let one = terms.mk_int(BigInt::from(1));
        let offset_a_plus_one = terms.mk_add(vec![offset_a, one]);

        let offset_a_is_zero = terms.mk_eq(zero, offset_a);
        let offset_b_is_offset_a_plus_one = terms.mk_eq(offset_b, offset_a_plus_one);
        let a_eq_b = terms.mk_eq(a, b);

        let conflict = vec![
            TheoryLit::new(offset_a_is_zero, true),
            TheoryLit::new(offset_b_is_offset_a_plus_one, true),
            TheoryLit::new(a_eq_b, true),
        ];

        assert_eq!(
            classify_term_domain(&terms, offset_a_is_zero),
            TheoryDomain::Unknown
        );
        assert_eq!(
            classify_term_domain(&terms, offset_b_is_offset_a_plus_one),
            TheoryDomain::Unknown
        );
        assert_eq!(classify_term_domain(&terms, a_eq_b), TheoryDomain::Euf);
        assert_eq!(
            classify_conflict_domain(&terms, &conflict),
            TheoryDomain::Unknown
        );
        assert!(
            matches!(
                verify_euf_conflict(&conflict, &terms, &[]),
                Err(VerificationError::ConflictIsSat)
            ),
            "pure EUF cannot see the UF+LIA contradiction"
        );
        assert!(
            verify_conflict_semantic(&conflict, &terms, &[]).is_ok(),
            "mixed UF+LIA semantic verification should prove the conflict UNSAT"
        );
    }

    /// #AUFLIA-support (the capability win): a mixed Seq-bridge conflict whose
    /// UNSAT closure depends on a ground instance of an UNCONDITIONALLY-asserted
    /// Seq axiom (`forall s. seq_offset(s) >= 0`). WITHOUT the support axiom the
    /// isolated combiner sees `seq_offset(a) = -1` as satisfiable (seq_offset is
    /// an uninterpreted Int-valued function) and fail-closes to
    /// `Err(ConflictIsSat)` — the exact `ConflictIsSat -> Unknown` degrade that
    /// blocked take_first_mut. WITH the axiom instance threaded as
    /// `support_axioms`, the combined solver refutes `-1 >= 0` and returns Ok.
    #[test]
    fn test_verify_mixed_conflict_semantic_accepts_seq_axiom_supported_conflict_9187() {
        use num_bigint::BigInt;
        let mut terms = TermStore::new();
        let seq = Sort::Uninterpreted("Seq".to_string());
        let a = terms.mk_var("a", seq);
        let offset_a = terms.mk_app(Symbol::named("seq_offset"), vec![a], Sort::Int);
        let neg_one = terms.mk_int(BigInt::from(-1));
        let zero = terms.mk_int(BigInt::from(0));

        // Conflict: seq_offset(a) = -1  (satisfiable in isolation — SAT).
        let offset_a_is_neg_one = terms.mk_eq(offset_a, neg_one);
        let conflict = vec![TheoryLit::new(offset_a_is_neg_one, true)];

        // Baseline: with no support the isolated combiner reports it Sat and the
        // gate rejects (fail-closed) — the pre-fix degrade.
        assert!(
            matches!(
                verify_mixed_conflict_semantic(&conflict, &terms, &[]),
                Err(VerificationError::ConflictIsSat)
            ),
            "seq_offset(a) = -1 alone is satisfiable, so the isolated combiner \
             must fail-close to ConflictIsSat"
        );

        // The unconditional Seq axiom `forall s. seq_offset(s) >= 0` instantiated
        // at `a`: `seq_offset(a) >= 0`. Threading it (valid in every model) lets
        // the combined solver reach UNSAT.
        let offset_a_nonneg = terms.mk_ge(offset_a, zero);
        let support = vec![TheoryLit::new(offset_a_nonneg, true)];
        assert!(
            verify_mixed_conflict_semantic(&conflict, &terms, &support).is_ok(),
            "with the unconditional-Forall Seq axiom instance seq_offset(a) >= 0 \
             threaded as support, {{seq_offset(a) = -1, seq_offset(a) >= 0}} is \
             UNSAT and the conflict must be accepted"
        );
    }

    /// Adversarial mixed-arith spuriousness pin: a quantifier-free mixed conflict
    /// that is genuinely SATISFIABLE must STILL be rejected with an empty support
    /// set (the support-axiom channel only ADDS entailed facts; it can never
    /// launder a spurious conflict). Companion to the SumTo10 pin.
    /// #4535 fail-closed pin (rejection side): an UNKNOWN-DOMAIN conflict —
    /// literals mixing an opaque Seq-carrier UF with arithmetic so
    /// `classify_conflict_domain` yields `Unknown` — that is genuinely
    /// SATISFIABLE must be REJECTED by the full dispatcher
    /// (`verify_conflict_semantic`), NOT optimistically skipped. This pins
    /// that the Unknown arm delegates to the Nelson-Oppen combined verifier
    /// and keeps the fail-closed `ConflictIsSat` verdict, so a spurious
    /// Unknown-domain conflict can never be learned as a clause.
    #[test]
    fn test_4535_unknown_domain_spurious_conflict_stays_rejected() {
        let mut terms = TermStore::new();
        let u = Sort::Uninterpreted("Seq".to_string());
        let a = terms.mk_var("a", u);
        let offset_a = terms.mk_app(Symbol::named("seq_offset"), vec![a], Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let ten = terms.mk_int(BigInt::from(10));
        // {seq_offset(a) = 0, seq_offset(a) <= 10} — trivially satisfiable.
        let off_is_zero = terms.mk_eq(offset_a, zero);
        let off_le_ten = terms.mk_le(offset_a, ten);
        let conflict = vec![
            TheoryLit::new(off_is_zero, true),
            TheoryLit::new(off_le_ten, true),
        ];
        assert_eq!(
            classify_conflict_domain(&terms, &conflict),
            TheoryDomain::Unknown,
            "the shape must actually classify as Unknown for this pin to bite"
        );
        assert!(
            matches!(
                verify_conflict_semantic(&conflict, &terms, &[]),
                Err(VerificationError::ConflictIsSat)
            ),
            "a satisfiable Unknown-domain conflict must fail semantic verification \
             (fail-closed) instead of being skipped and learned"
        );
    }

    #[test]
    fn test_verify_mixed_conflict_semantic_still_rejects_spurious_no_forall_9187() {
        use num_bigint::BigInt;
        let mut terms = TermStore::new();
        let seq = Sort::Uninterpreted("Seq".to_string());
        let a = terms.mk_var("a", seq);
        let offset_a = terms.mk_app(Symbol::named("seq_offset"), vec![a], Sort::Int);
        let five = terms.mk_int(BigInt::from(5));
        // seq_offset(a) = 5 is satisfiable and there are NO quantifiers, so the
        // support set is empty and the gate must still reject it.
        let offset_a_is_five = terms.mk_eq(offset_a, five);
        let conflict = vec![TheoryLit::new(offset_a_is_five, true)];
        assert!(
            matches!(
                verify_mixed_conflict_semantic(&conflict, &terms, &[]),
                Err(VerificationError::ConflictIsSat)
            ),
            "a genuinely-SAT quantifier-free conflict must stay rejected (empty support)"
        );
    }
}

mod propagation_tests {
    use super::*;
    use ay_core::TheoryPropagation;

    fn make_prop(prop_term: u32, prop_value: bool, reasons: &[(u32, bool)]) -> TheoryPropagation {
        TheoryPropagation {
            literal: TheoryLit::new(TermId(prop_term), prop_value),
            reason: reasons
                .iter()
                .map(|&(t, v)| TheoryLit::new(TermId(t), v))
                .collect(),
            reason_data: None,
        }
    }

    #[test]
    fn test_valid_propagation_accepted() {
        // x=true, y=true => z=true
        let prop = make_prop(3, true, &[(1, true), (2, true)]);
        assert!(verify_theory_propagation(&prop).is_ok());
    }

    #[test]
    fn test_single_reason_accepted() {
        // x=true => y=false
        let prop = make_prop(2, false, &[(1, true)]);
        assert!(verify_theory_propagation(&prop).is_ok());
    }

    #[test]
    fn test_empty_reason_rejected() {
        let prop = make_prop(1, true, &[]);
        let result = verify_theory_propagation(&prop);
        assert!(
            matches!(result, Err(VerificationError::EmptyReason)),
            "Empty reason set should be rejected: {result:?}"
        );
    }

    #[test]
    fn test_duplicate_reason_rejected() {
        // Reason contains (1, true) twice
        let prop = make_prop(3, true, &[(1, true), (2, false), (1, true)]);
        let result = verify_theory_propagation(&prop);
        assert!(
            matches!(
                result,
                Err(VerificationError::DuplicateReasonLiteral {
                    term: TermId(1),
                    value: true,
                })
            ),
            "Duplicate reason literal should be rejected: {result:?}"
        );
    }

    #[test]
    fn test_same_term_opposite_value_in_reason_accepted() {
        // The same term with opposite values in the reason is unusual but not
        // structurally invalid — the reason set is contradictory, which means
        // the propagation is vacuously true.
        let prop = make_prop(3, true, &[(1, true), (1, false)]);
        assert!(verify_theory_propagation(&prop).is_ok());
    }

    #[test]
    fn test_circular_same_polarity_rejected() {
        // Propagated literal appears in its own reason (same polarity)
        let prop = make_prop(1, true, &[(1, true), (2, false)]);
        let result = verify_theory_propagation(&prop);
        assert!(
            matches!(
                result,
                Err(VerificationError::CircularPropagation {
                    term: TermId(1),
                    ..
                })
            ),
            "Circular propagation (same polarity) should be rejected: {result:?}"
        );
    }

    #[test]
    fn test_circular_opposite_polarity_rejected() {
        // Propagated literal's term appears in reason with opposite polarity
        let prop = make_prop(1, true, &[(1, false), (2, true)]);
        let result = verify_theory_propagation(&prop);
        assert!(
            matches!(
                result,
                Err(VerificationError::CircularPropagation {
                    term: TermId(1),
                    ..
                })
            ),
            "Circular propagation (opposite polarity) should be rejected: {result:?}"
        );
    }

    #[test]
    fn test_many_reason_literals_accepted() {
        // Large reason set, all distinct, no circularity
        let reasons: Vec<(u32, bool)> = (1..=20).map(|i| (i, i % 2 == 0)).collect();
        let prop = make_prop(100, true, &reasons);
        assert!(verify_theory_propagation(&prop).is_ok());
    }
}

mod semantic_propagation_tests {
    use super::*;
    use ay_core::{Sort, Symbol, TermStore, TheoryPropagation};

    // ── EUF semantic propagation tests ──

    /// Valid EUF propagation: a=b ⊨ f(a)=f(b) via congruence.
    #[test]
    fn test_euf_propagation_congruence_valid() {
        let mut terms = TermStore::new();
        let u = Sort::Uninterpreted("U".to_string());
        let a = terms.mk_var("a", u.clone());
        let b = terms.mk_var("b", u.clone());
        let f_a = terms.mk_app(Symbol::named("f"), vec![a], u.clone());
        let f_b = terms.mk_app(Symbol::named("f"), vec![b], u);
        let eq_ab = terms.mk_eq(a, b);
        let eq_fa_fb = terms.mk_eq(f_a, f_b);

        let prop = TheoryPropagation {
            literal: TheoryLit::new(eq_fa_fb, true),
            reason: vec![TheoryLit::new(eq_ab, true)],
            reason_data: None,
        };

        let result = verify_euf_propagation(&prop, &terms);
        assert!(
            result.is_ok(),
            "a=b should imply f(a)=f(b) via congruence: {result:?}"
        );
    }

    /// Valid EUF propagation: a=b, b=c ⊨ a=c via transitivity.
    #[test]
    fn test_euf_propagation_transitivity_valid() {
        let mut terms = TermStore::new();
        let u = Sort::Uninterpreted("U".to_string());
        let a = terms.mk_var("a", u.clone());
        let b = terms.mk_var("b", u.clone());
        let c = terms.mk_var("c", u);
        let eq_ab = terms.mk_eq(a, b);
        let eq_bc = terms.mk_eq(b, c);
        let eq_ac = terms.mk_eq(a, c);

        let prop = TheoryPropagation {
            literal: TheoryLit::new(eq_ac, true),
            reason: vec![TheoryLit::new(eq_ab, true), TheoryLit::new(eq_bc, true)],
            reason_data: None,
        };

        let result = verify_euf_propagation(&prop, &terms);
        assert!(
            result.is_ok(),
            "a=b, b=c should imply a=c via transitivity: {result:?}"
        );
    }

    /// Invalid EUF propagation: a=b does NOT imply a=c (unrelated).
    #[test]
    fn test_euf_propagation_invalid_rejected() {
        let mut terms = TermStore::new();
        let u = Sort::Uninterpreted("U".to_string());
        let a = terms.mk_var("a", u.clone());
        let b = terms.mk_var("b", u.clone());
        let c = terms.mk_var("c", u);
        let eq_ab = terms.mk_eq(a, b);
        let eq_ac = terms.mk_eq(a, c);

        let prop = TheoryPropagation {
            literal: TheoryLit::new(eq_ac, true),
            reason: vec![TheoryLit::new(eq_ab, true)],
            reason_data: None,
        };

        let result = verify_euf_propagation(&prop, &terms);
        assert!(
            matches!(result, Err(VerificationError::PropagationNotImplied { .. })),
            "a=b should NOT imply a=c (c unrelated): {result:?}"
        );
    }

    // ── LRA semantic propagation tests ──

    /// Valid LRA propagation: x <= 3, x >= 3 ⊨ x = 3.
    #[test]
    fn test_lra_propagation_tight_bounds_valid() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let three = terms.mk_int(BigInt::from(3));
        let x_le_3 = terms.mk_le(x, three);
        let x_ge_3 = terms.mk_ge(x, three);
        let x_eq_3 = terms.mk_eq(x, three);

        let prop = TheoryPropagation {
            literal: TheoryLit::new(x_eq_3, true),
            reason: vec![TheoryLit::new(x_le_3, true), TheoryLit::new(x_ge_3, true)],
            reason_data: None,
        };

        let result = verify_lra_propagation(&prop, &terms);
        assert!(result.is_ok(), "x<=3, x>=3 should imply x=3: {result:?}");
    }

    /// Valid LRA propagation: x <= 5 ⊨ x < 10.
    #[test]
    fn test_lra_propagation_bound_implication_valid() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let five = terms.mk_int(BigInt::from(5));
        let ten = terms.mk_int(BigInt::from(10));
        let x_le_5 = terms.mk_le(x, five);
        let x_lt_10 = terms.mk_lt(x, ten);

        let prop = TheoryPropagation {
            literal: TheoryLit::new(x_lt_10, true),
            reason: vec![TheoryLit::new(x_le_5, true)],
            reason_data: None,
        };

        let result = verify_lra_propagation(&prop, &terms);
        assert!(result.is_ok(), "x<=5 should imply x<10: {result:?}");
    }

    /// Invalid LRA propagation: x <= 5 does NOT imply x <= 3.
    #[test]
    fn test_lra_propagation_invalid_rejected() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let five = terms.mk_int(BigInt::from(5));
        let three = terms.mk_int(BigInt::from(3));
        let x_le_5 = terms.mk_le(x, five);
        let x_le_3 = terms.mk_le(x, three);

        let prop = TheoryPropagation {
            literal: TheoryLit::new(x_le_3, true),
            reason: vec![TheoryLit::new(x_le_5, true)],
            reason_data: None,
        };

        let result = verify_lra_propagation(&prop, &terms);
        assert!(
            matches!(result, Err(VerificationError::PropagationNotImplied { .. })),
            "x<=5 should NOT imply x<=3: {result:?}"
        );
    }

    /// #lra-fastpath-mixed-direction: a one-sided reason can never entail a
    /// bound in the OPPOSITE direction. The algebraic fast path used to accept
    /// these by testing `reason AND prop` unsatisfiability instead of
    /// entailment, so `x <= 3` "implied" `x >= 5` — a false accept inside the
    /// gate that exists to catch unsound implied-bound propagations.
    #[test]
    fn test_lra_propagation_mixed_direction_rejected() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let five = terms.mk_int(BigInt::from(5));
        let three = terms.mk_int(BigInt::from(3));
        let x_ge_5 = terms.mk_ge(x, five);
        let x_le_3 = terms.mk_le(x, three);

        let prop = TheoryPropagation {
            literal: TheoryLit::new(x_ge_5, true),
            reason: vec![TheoryLit::new(x_le_3, true)],
            reason_data: None,
        };

        let result = verify_lra_propagation(&prop, &terms);
        assert!(
            result.is_err(),
            "x<=3 must NOT be accepted as implying x>=5 (x=0 refutes it): {result:?}"
        );
    }

    /// The equality-reason twin of the above: `x = 3` must not be accepted as
    /// entailing `x >= 5` through the upper half of the equality.
    #[test]
    fn test_lra_propagation_eq_reason_mixed_direction_rejected() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let five = terms.mk_int(BigInt::from(5));
        let three = terms.mk_int(BigInt::from(3));
        let x_ge_5 = terms.mk_ge(x, five);
        let x_eq_3 = terms.mk_eq(x, three);

        let prop = TheoryPropagation {
            literal: TheoryLit::new(x_ge_5, true),
            reason: vec![TheoryLit::new(x_eq_3, true)],
            reason_data: None,
        };

        let result = verify_lra_propagation(&prop, &terms);
        assert!(
            result.is_err(),
            "x=3 must NOT be accepted as implying x>=5: {result:?}"
        );
    }

    /// Valid LIA propagation that is not valid over the real relaxation:
    /// not (1 <= x) entails x <= 0 for Int variables.
    #[test]
    fn test_lia_integer_gap_propagation_valid() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let one = terms.mk_int(BigInt::from(1));
        let one_le_x = terms.mk_le(one, x);
        let x_le_zero = terms.mk_le(x, zero);

        let prop = TheoryPropagation {
            literal: TheoryLit::new(x_le_zero, true),
            reason: vec![TheoryLit::new(one_le_x, false)],
            reason_data: None,
        };

        let result = verify_lia_propagation(&prop, &terms);
        assert!(
            result.is_ok(),
            "not (1 <= x) should imply x <= 0 over Int: {result:?}"
        );

        let dispatched = verify_propagation_semantic(&prop, &terms);
        assert!(
            dispatched.is_ok(),
            "semantic dispatcher should use LIA for integer-gap propagation: {dispatched:?}"
        );
    }

    /// Invalid LIA propagation: not (1 <= x) allows x = 0, so x <= -1 is not
    /// implied.
    #[test]
    fn test_lia_integer_gap_propagation_invalid_rejected() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let neg_one = terms.mk_int(BigInt::from(-1));
        let one = terms.mk_int(BigInt::from(1));
        let one_le_x = terms.mk_le(one, x);
        let x_le_neg_one = terms.mk_le(x, neg_one);

        let prop = TheoryPropagation {
            literal: TheoryLit::new(x_le_neg_one, true),
            reason: vec![TheoryLit::new(one_le_x, false)],
            reason_data: None,
        };

        let result = verify_lia_propagation(&prop, &terms);
        assert!(
            matches!(result, Err(VerificationError::PropagationNotImplied { .. })),
            "not (1 <= x) should NOT imply x <= -1 over Int: {result:?}"
        );

        let dispatched = verify_propagation_semantic(&prop, &terms);
        assert!(
            matches!(
                dispatched,
                Err(VerificationError::PropagationNotImplied { .. })
            ),
            "semantic dispatcher must reject invalid integer-gap propagation: {dispatched:?}"
        );
    }

    // ── Array semantic propagation tests ──

    #[test]
    fn test_classify_term_domain_select_int_equality_is_array() {
        let mut terms = TermStore::new();
        let array = terms.mk_var("a", Sort::array(Sort::Int, Sort::Int));
        let index = terms.mk_var("i", Sort::Int);
        let value = terms.mk_var("v", Sort::Int);
        let stored = terms.mk_store(array, index, value);
        let lhs = terms.mk_select(stored, index);
        let rhs = terms.mk_select(array, index);
        let eq = terms.mk_eq(lhs, rhs);

        assert_eq!(
            classify_term_domain(&terms, eq),
            TheoryDomain::Array,
            "select/store equalities over Int elements must route to the array verifier",
        );
    }

    #[test]
    fn test_classify_term_domain_select_int_inequality_is_array_1753() {
        let mut terms = TermStore::new();
        let array = terms.mk_var("a", Sort::array(Sort::Int, Sort::Int));
        let index = terms.mk_var("i", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let one = terms.mk_int(BigInt::from(1));
        let select_i = terms.mk_select(array, index);
        let plus_one = terms.mk_add(vec![select_i, one]);
        let ge_zero = terms.mk_ge(plus_one, zero);

        assert_eq!(
            classify_term_domain(&terms, ge_zero),
            TheoryDomain::Array,
            "arithmetic comparisons over select terms must route to the array verifier",
        );
    }

    #[test]
    fn test_array_propagation_cross_theory_arith_context_is_inconclusive() {
        let mut terms = TermStore::new();
        let array = terms.mk_var("a", Sort::array(Sort::Int, Sort::Int));
        let i = terms.mk_var("i", Sort::Int);
        let j = terms.mk_var("j", Sort::Int);
        let value = terms.mk_var("v", Sort::Int);
        let stored = terms.mk_store(array, i, value);
        let lhs = terms.mk_select(stored, j);
        let rhs = terms.mk_select(array, j);
        let row2_eq = terms.mk_eq(lhs, rhs);
        let i_lt_j = terms.mk_lt(i, j);

        let prop = TheoryPropagation {
            literal: TheoryLit::new(row2_eq, true),
            reason: vec![TheoryLit::new(i_lt_j, true)],
            reason_data: None,
        };

        let result = verify_array_propagation(&prop, &terms);
        assert!(
            result.is_ok(),
            "array propagation with arithmetic context should be treated as inconclusive, not rejected: {result:?}"
        );
    }

    #[test]
    fn test_array_propagation_pure_invalid_rejected() {
        let mut terms = TermStore::new();
        let sort = Sort::array(Sort::Int, Sort::Int);
        let a = terms.mk_var("a", sort.clone());
        let b = terms.mk_var("b", sort.clone());
        let c = terms.mk_var("c", sort);
        let i = terms.mk_var("i", Sort::Int);
        let eq_ab = terms.mk_eq(a, b);
        let select_a_i = terms.mk_select(a, i);
        let select_c_i = terms.mk_select(c, i);
        let eq_select_ac = terms.mk_eq(select_a_i, select_c_i);

        let prop = TheoryPropagation {
            literal: TheoryLit::new(eq_select_ac, true),
            reason: vec![TheoryLit::new(eq_ab, true)],
            reason_data: None,
        };

        let result = verify_array_propagation(&prop, &terms);
        assert!(
            matches!(result, Err(VerificationError::PropagationNotImplied { .. })),
            "pure array propagation that is not implied must still be rejected: {result:?}"
        );
    }

    // ── Domain classification + dispatcher tests ──

    /// Dispatcher routes arithmetic propagation to LRA verifier.
    #[test]
    fn test_semantic_dispatcher_arithmetic() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let three = terms.mk_int(BigInt::from(3));
        let x_le_3 = terms.mk_le(x, three);
        let x_ge_3 = terms.mk_ge(x, three);
        let x_eq_3 = terms.mk_eq(x, three);

        let prop = TheoryPropagation {
            literal: TheoryLit::new(x_eq_3, true),
            reason: vec![TheoryLit::new(x_le_3, true), TheoryLit::new(x_ge_3, true)],
            reason_data: None,
        };

        let result = verify_propagation_semantic(&prop, &terms);
        assert!(
            result.is_ok(),
            "Dispatcher should route arithmetic propagation to LRA: {result:?}"
        );
    }

    /// Dispatcher routes EUF propagation to EUF verifier.
    #[test]
    fn test_semantic_dispatcher_euf() {
        let mut terms = TermStore::new();
        let u = Sort::Uninterpreted("U".to_string());
        let a = terms.mk_var("a", u.clone());
        let b = terms.mk_var("b", u.clone());
        let f_a = terms.mk_app(Symbol::named("f"), vec![a], u.clone());
        let f_b = terms.mk_app(Symbol::named("f"), vec![b], u);
        let eq_ab = terms.mk_eq(a, b);
        let eq_fa_fb = terms.mk_eq(f_a, f_b);

        let prop = TheoryPropagation {
            literal: TheoryLit::new(eq_fa_fb, true),
            reason: vec![TheoryLit::new(eq_ab, true)],
            reason_data: None,
        };

        let result = verify_propagation_semantic(&prop, &terms);
        assert!(
            result.is_ok(),
            "Dispatcher should route EUF propagation correctly: {result:?}"
        );
    }

    /// Dispatcher skips unknown/mixed domain propagations gracefully.
    #[test]
    fn test_semantic_dispatcher_unknown_domain_skips() {
        let mut terms = TermStore::new();
        // Boolean variable — not clearly arithmetic or EUF
        let p = terms.mk_var("p", Sort::Bool);
        let q = terms.mk_var("q", Sort::Bool);

        // Try to classify Boolean atoms — should be Unknown domain
        assert_eq!(classify_term_domain(&terms, p), TheoryDomain::Unknown);

        // A propagation with Bool-sorted vars gets Unknown classification
        let prop = TheoryPropagation {
            literal: TheoryLit::new(q, true),
            reason: vec![TheoryLit::new(p, true)],
            reason_data: None,
        };

        // Dispatcher should return Ok (skip, not error)
        let result = verify_propagation_semantic(&prop, &terms);
        assert!(
            result.is_ok(),
            "Unknown domain should be skipped, not rejected: {result:?}"
        );
    }
}

mod lia_semantic_conflict_tests {
    use super::dispatch::verify_lia_conflict_semantic;
    use super::*;
    use ay_core::{Sort, TermStore};

    /// Valid integer-gap conflict: x > 5 AND x < 6 is UNSAT over integers.
    /// There is no integer in the open interval (5, 6).
    /// This must PASS the LIA verifier (the conflict is correct).
    #[test]
    fn test_lia_integer_gap_conflict_valid() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let five = terms.mk_int(BigInt::from(5));
        let six = terms.mk_int(BigInt::from(6));
        let x_gt_5 = terms.mk_lt(five, x); // 5 < x, i.e. x > 5
        let x_lt_6 = terms.mk_lt(x, six); // x < 6

        let conflict = vec![TheoryLit::new(x_gt_5, true), TheoryLit::new(x_lt_6, true)];

        let result = verify_lia_conflict_semantic(&conflict, &terms);
        assert!(
            result.is_ok(),
            "Integer gap conflict (x > 5 AND x < 6) should be verified as UNSAT: {result:?}"
        );
    }

    /// Satisfiable fake conflict: x >= 0 AND x <= 10 is SAT (x=5 works).
    /// The LIA verifier must REJECT this as ConflictIsSat.
    #[test]
    fn test_lia_satisfiable_conflict_rejected() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let ten = terms.mk_int(BigInt::from(10));
        let x_ge_0 = terms.mk_ge(x, zero);
        let x_le_10 = terms.mk_le(x, ten);

        let conflict = vec![TheoryLit::new(x_ge_0, true), TheoryLit::new(x_le_10, true)];

        let result = verify_lia_conflict_semantic(&conflict, &terms);
        assert!(
            matches!(result, Err(VerificationError::ConflictIsSat)),
            "Satisfiable set (x >= 0 AND x <= 10) should be rejected: {result:?}"
        );
    }

    /// Valid simple bounds conflict: x <= 5 AND x >= 10 is UNSAT.
    #[test]
    fn test_lia_simple_bounds_conflict_valid() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let five = terms.mk_int(BigInt::from(5));
        let ten = terms.mk_int(BigInt::from(10));
        let x_le_5 = terms.mk_le(x, five);
        let x_ge_10 = terms.mk_ge(x, ten);

        let conflict = vec![TheoryLit::new(x_le_5, true), TheoryLit::new(x_ge_10, true)];

        let result = verify_lia_conflict_semantic(&conflict, &terms);
        assert!(
            result.is_ok(),
            "Simple bounds conflict (x <= 5 AND x >= 10) should pass: {result:?}"
        );
    }

    /// Multi-variable conflict: x + y >= 10, x <= 3, y <= 3 is UNSAT.
    #[test]
    fn test_lia_multi_var_conflict_valid() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let three = terms.mk_int(BigInt::from(3));
        let ten = terms.mk_int(BigInt::from(10));

        let x_plus_y = terms.mk_add(vec![x, y]);
        let sum_ge_10 = terms.mk_ge(x_plus_y, ten);
        let x_le_3 = terms.mk_le(x, three);
        let y_le_3 = terms.mk_le(y, three);

        let conflict = vec![
            TheoryLit::new(sum_ge_10, true),
            TheoryLit::new(x_le_3, true),
            TheoryLit::new(y_le_3, true),
        ];

        let result = verify_lia_conflict_semantic(&conflict, &terms);
        assert!(
            result.is_ok(),
            "Multi-var conflict (x+y >= 10, x <= 3, y <= 3) should pass: {result:?}"
        );
    }
}

mod mixed_conflict_verification_tests {
    use super::*;
    use ay_core::{Sort, Symbol, TermStore};

    fn option_seq_branch_reducer() -> (TermStore, TermId, TermId, TermId, TermId) {
        let mut terms = TermStore::new();
        let option_sort = Sort::enum_type("OptionSeq8971", ["None", "Some"]);
        let seq_sort = Sort::seq(Sort::Int);

        let call_2 = terms.mk_var("call_2", option_sort);
        let self_seq = terms.mk_var("self_seq", seq_sort);
        let zero = terms.mk_int(BigInt::from(0));

        let discr = terms.mk_app(
            Symbol::named("method_discriminant_1_Option"),
            vec![call_2],
            Sort::Int,
        );
        let len = terms.mk_app(Symbol::named("seq_len"), vec![self_seq], Sort::Int);

        let discr_eq_zero = terms.mk_eq(discr, zero);
        let discr_ge_zero = terms.mk_ge(discr, zero);
        let len_eq_zero = terms.mk_eq(len, zero);
        let len_ge_zero = terms.mk_ge(len, zero);

        (
            terms,
            discr_eq_zero,
            discr_ge_zero,
            len_eq_zero,
            len_ge_zero,
        )
    }

    #[test]
    fn test_unknown_uf_arith_conflict_verifier_rejects_sat_option_seq_reducer_8971() {
        let (terms, discr_eq_zero, discr_ge_zero, len_eq_zero, len_ge_zero) =
            option_seq_branch_reducer();

        assert_eq!(
            classify_term_domain(&terms, discr_eq_zero),
            TheoryDomain::Unknown
        );
        assert_eq!(
            classify_term_domain(&terms, len_eq_zero),
            TheoryDomain::Unknown
        );
        assert_eq!(
            classify_term_domain(&terms, discr_ge_zero),
            TheoryDomain::Arithmetic
        );
        assert_eq!(
            classify_term_domain(&terms, len_ge_zero),
            TheoryDomain::Arithmetic
        );

        // This is satisfiable: discr(call_2)=0 and seq_len(self_seq)=0 also
        // satisfy the weak >= 0 bounds. Before #8971, the Unknown equality
        // atoms made semantic conflict verification skip this family.
        let conflict = vec![
            TheoryLit::new(discr_eq_zero, true),
            TheoryLit::new(discr_ge_zero, true),
            TheoryLit::new(len_eq_zero, true),
            TheoryLit::new(len_ge_zero, true),
        ];

        let result = verify_conflict_semantic(&conflict, &terms, &[]);
        assert!(
            matches!(result, Err(VerificationError::ConflictIsSat)),
            "UF-arithmetic Option/Seq reducer is SAT and must not be accepted as a conflict: {result:?}"
        );
    }

    #[test]
    fn test_unknown_uf_arith_conflict_verifier_accepts_unsat_option_seq_reducer_8971() {
        let mut terms = TermStore::new();
        let option_sort = Sort::enum_type("OptionSeq8971Unsat", ["None", "Some"]);
        let seq_sort = Sort::seq(Sort::Int);

        let call_2 = terms.mk_var("call_2", option_sort);
        let self_seq = terms.mk_var("self_seq", seq_sort);
        let zero = terms.mk_int(BigInt::from(0));

        let discr = terms.mk_app(
            Symbol::named("method_discriminant_1_Option"),
            vec![call_2],
            Sort::Int,
        );
        let len = terms.mk_app(Symbol::named("seq_len"), vec![self_seq], Sort::Int);

        let discr_eq_zero = terms.mk_eq(discr, zero);
        let discr_gt_zero = terms.mk_gt(discr, zero);
        let len_eq_zero = terms.mk_eq(len, zero);
        let len_gt_zero = terms.mk_gt(len, zero);

        let conflict = vec![
            TheoryLit::new(discr_eq_zero, true),
            TheoryLit::new(discr_gt_zero, true),
            TheoryLit::new(len_eq_zero, true),
            TheoryLit::new(len_gt_zero, true),
        ];

        let result = verify_conflict_semantic(&conflict, &terms, &[]);
        assert!(
            result.is_ok(),
            "UF-arithmetic Option/Seq reducer contradiction should verify as UNSAT: {result:?}"
        );
    }
}

mod mixed_conflict_semantic_dispatch_tests {
    use super::dispatch::{
        verify_conflict_semantic, verify_lia_conflict_semantic, verify_mixed_conflict_semantic,
    };
    use super::*;
    use ay_core::{Sort, Symbol, TermStore};

    /// Mixed UFLIA conflict that IS genuinely UNSAT:
    /// x=5, y=5 forces x=y, so f(x)=f(y) by congruence,
    /// but f(x)=10 and f(y)=20 contradicts.
    ///
    /// Previously (#8123) this was skipped. Now verified via combined solver.
    #[test]
    fn test_verify_conflict_semantic_verifies_mixed_uflia_conflicts() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let five = terms.mk_int(BigInt::from(5));
        let ten = terms.mk_int(BigInt::from(10));
        let twenty = terms.mk_int(BigInt::from(20));
        let f_x = terms.mk_app(Symbol::named("f"), vec![x], Sort::Int);
        let f_y = terms.mk_app(Symbol::named("f"), vec![y], Sort::Int);

        let x_ge_5 = terms.mk_ge(x, five);
        let x_le_5 = terms.mk_le(x, five);
        let y_eq_5 = terms.mk_eq(y, five);
        let fx_eq_10 = terms.mk_eq(f_x, ten);
        let fy_eq_20 = terms.mk_eq(f_y, twenty);
        let conflict = vec![
            TheoryLit::new(x_ge_5, true),
            TheoryLit::new(x_le_5, true),
            TheoryLit::new(y_eq_5, true),
            TheoryLit::new(fx_eq_10, true),
            TheoryLit::new(fy_eq_20, true),
        ];

        let lia_only = verify_lia_conflict_semantic(&conflict, &terms);
        assert!(
            matches!(lia_only, Err(VerificationError::ConflictIsSat)),
            "standalone LIA cannot validate mixed EUF/LIA conflicts: {lia_only:?}"
        );

        // After #8123 fix: mixed conflicts are verified via combined solver,
        // not skipped. The combined solver correctly finds this UNSAT via
        // Nelson-Oppen (LIA + EUF congruence).
        let dispatched = verify_conflict_semantic(&conflict, &terms, &[]);
        assert!(
            dispatched.is_ok(),
            "combined solver should verify mixed UFLIA conflict as UNSAT: {dispatched:?}"
        );
    }

    /// Pure EUF conflict is now properly dispatched to the EUF verifier
    /// (previously fell through to the catch-all Ok(()) arm).
    #[test]
    fn test_verify_conflict_semantic_dispatches_euf_conflicts() {
        let mut terms = TermStore::new();
        let u = Sort::Uninterpreted("U".to_string());
        let a = terms.mk_var("a", u.clone());
        let b = terms.mk_var("b", u.clone());
        let c = terms.mk_var("c", u);
        let eq_ab = terms.mk_eq(a, b);
        let eq_bc = terms.mk_eq(b, c);
        let eq_ac = terms.mk_eq(a, c);

        // Valid EUF conflict: a=b, b=c, a!=c
        let conflict = vec![
            TheoryLit::new(eq_ab, true),
            TheoryLit::new(eq_bc, true),
            TheoryLit::new(eq_ac, false),
        ];
        let result = verify_conflict_semantic(&conflict, &terms, &[]);
        assert!(
            result.is_ok(),
            "EUF transitivity conflict should be verified as UNSAT: {result:?}"
        );

        // Invalid EUF "conflict": a!=b, b!=c (satisfiable)
        let fake_conflict = vec![TheoryLit::new(eq_ab, false), TheoryLit::new(eq_bc, false)];
        let result = verify_conflict_semantic(&fake_conflict, &terms, &[]);
        assert!(
            matches!(result, Err(VerificationError::ConflictIsSat)),
            "Satisfiable EUF literals should be rejected: {result:?}"
        );
    }

    /// Satisfiable mixed-domain literals should be rejected by the combined
    /// solver (#8123). Previously these were silently accepted.
    #[test]
    fn test_verify_mixed_conflict_rejects_satisfiable_mixed_literals() {
        let mut terms = TermStore::new();
        let u = Sort::Uninterpreted("U".to_string());
        let x = terms.mk_var("x", Sort::Int);
        let a = terms.mk_var("a", u.clone());
        let b = terms.mk_var("b", u);
        let five = terms.mk_int(BigInt::from(5));

        // x >= 5 AND a != b — clearly satisfiable (x=5, a!=b)
        let x_ge_5 = terms.mk_ge(x, five);
        let eq_ab = terms.mk_eq(a, b);
        let conflict = vec![TheoryLit::new(x_ge_5, true), TheoryLit::new(eq_ab, false)];

        let result = verify_mixed_conflict_semantic(&conflict, &terms, &[]);
        assert!(
            matches!(result, Err(VerificationError::ConflictIsSat)),
            "Satisfiable mixed-domain literals should be rejected: {result:?}"
        );
    }

    /// Mixed conflict with uninterpreted + arithmetic that is genuinely UNSAT:
    /// a = b, a != b  (trivially UNSAT, but classified as mixed because
    /// the equality is over uninterpreted sort while we also have arithmetic).
    #[test]
    fn test_verify_mixed_conflict_accepts_valid_mixed_conflict() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let five = terms.mk_int(BigInt::from(5));
        let ten = terms.mk_int(BigInt::from(10));
        let f_x = terms.mk_app(Symbol::named("f"), vec![x], Sort::Int);

        // x <= 5 AND f(x) = 10 AND x >= 10 — UNSAT due to x <= 5 AND x >= 10
        // The f(x) = 10 literal makes this mixed-domain.
        let x_le_5 = terms.mk_le(x, five);
        let x_ge_10 = terms.mk_ge(x, ten);
        let fx_eq_10 = terms.mk_eq(f_x, ten);
        let conflict = vec![
            TheoryLit::new(x_le_5, true),
            TheoryLit::new(x_ge_10, true),
            TheoryLit::new(fx_eq_10, true),
        ];

        let result = verify_mixed_conflict_semantic(&conflict, &terms, &[]);
        assert!(
            result.is_ok(),
            "Valid mixed conflict (arithmetic contradiction + EUF) should pass: {result:?}"
        );
    }

    /// VALID int<->real-bridged (LIRA) conflict must NOT be rejected as
    /// `ConflictIsSat` (#6853 completeness): no fresh combiner interprets the
    /// `to_real` coupling (UF+LIA leaves Real atoms uninterpreted; UF+LRA
    /// drops integrality), so their SAT verdicts are untrustworthy here and
    /// semantic re-verification is skipped. This is the exact conflict shape
    /// the AUFLIRA solver derives on deductive-checks's archimedean_nat obligation:
    ///   { k+2 <= 0,  0.0 <= x,  to_real(k+1) = f(k+1),  x < f(k+1) }
    /// which is valid (k+1 <= -1 => to_real(k+1) <= -1 => x < -1, contra
    /// 0 <= x) but was reported SAT, hard-degrading the solve to Unknown.
    #[test]
    fn test_verify_mixed_conflict_accepts_valid_bridged_lira_conflict_6853() {
        let mut terms = TermStore::new();
        let k = terms.mk_var("k", Sort::Int);
        let x = terms.mk_var("x", Sort::Real);
        let zero_i = terms.mk_int(BigInt::from(0));
        let one = terms.mk_int(BigInt::from(1));
        let two = terms.mk_int(BigInt::from(2));
        let zero_r = terms.mk_rational(num_rational::BigRational::from(BigInt::from(0)));
        let k_plus_1 = terms.mk_add(vec![k, one]);
        let k_plus_2 = terms.mk_add(vec![k, two]);
        let to_real_k1 = terms.mk_to_real(k_plus_1);
        let f_k1 = terms.mk_app(Symbol::named("f"), vec![k_plus_1], Sort::Real);

        let k2_le_0 = terms.mk_le(k_plus_2, zero_i);
        let zero_le_x = terms.mk_le(zero_r, x);
        let bridge_eq = terms.mk_eq(to_real_k1, f_k1);
        let x_lt_fk1 = terms.mk_lt(x, f_k1);
        let conflict = vec![
            TheoryLit::new(k2_le_0, true),
            TheoryLit::new(zero_le_x, true),
            TheoryLit::new(bridge_eq, true),
            TheoryLit::new(x_lt_fk1, true),
        ];

        let mixed = verify_mixed_conflict_semantic(&conflict, &terms, &[]);
        assert!(
            mixed.is_ok(),
            "valid bridged LIRA conflict must not be rejected by the mixed verifier: {mixed:?}"
        );
        let dispatched = verify_conflict_semantic(&conflict, &terms, &[]);
        assert!(
            dispatched.is_ok(),
            "valid bridged LIRA conflict must not be rejected by dispatch: {dispatched:?}"
        );
    }

    #[test]
    fn test_verify_conflict_semantic_rejects_verification_consumer_sumto10_partial_explanation_6853(
    ) {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::Int);
        let b = terms.mk_var("b", Sort::Int);
        let next_a = terms.mk_var("next_a", Sort::Int);
        let next_b = terms.mk_var("next_b", Sort::Int);
        let one = terms.mk_int(BigInt::from(1));
        let ten = terms.mk_int(BigInt::from(10));
        let a_plus_b = terms.mk_add(vec![a, b]);
        let a_plus_one = terms.mk_add(vec![a, one]);
        let b_minus_one = terms.mk_sub(vec![b, one]);

        let invariant = terms.mk_eq(a_plus_b, ten);
        let inc_post = terms.mk_eq(next_a, a_plus_one);
        let dec_post = terms.mk_eq(next_b, b_minus_one);
        let conflict = vec![
            TheoryLit::new(invariant, true),
            TheoryLit::new(inc_post, true),
            TheoryLit::new(dec_post, true),
        ];

        let result = verify_conflict_semantic(&conflict, &terms, &[]);
        assert!(
            matches!(result, Err(VerificationError::ConflictIsSat)),
            "partial SumTo10 transition explanation is satisfiable and must be rejected: {result:?}"
        );
    }

    #[test]
    fn test_verify_conflict_semantic_accepts_nested_store_array_conflict_8871() {
        let mut terms = TermStore::new();
        let array = terms.mk_var("a", Sort::array(Sort::Int, Sort::Int));
        let i = terms.mk_var("i", Sort::Int);
        let ten = terms.mk_int(BigInt::from(10));
        let twenty = terms.mk_int(BigInt::from(20));
        let one = terms.mk_int(BigInt::from(1));
        let i_plus_one = terms.mk_add(vec![i, one]);
        let inner_store = terms.mk_store(array, i, ten);
        let outer_store = terms.mk_store(inner_store, i_plus_one, twenty);
        let select_i = terms.mk_select(outer_store, i);
        let eq_select_10 = terms.mk_eq(select_i, ten);
        let not_eq_select_10 = terms.mk_not(eq_select_10);
        let conflict = vec![TheoryLit::new(not_eq_select_10, true)];

        let result = verify_conflict_semantic(&conflict, &terms, &[]);
        assert!(
            result.is_ok(),
            "pure array singleton conflict should be re-verified as UNSAT: {result:?}"
        );
    }

    #[test]
    fn test_verify_conflict_semantic_accepts_mixed_auflia_nested_store_conflict_8871() {
        let mut terms = TermStore::new();
        let array = terms.mk_var("a", Sort::array(Sort::Int, Sort::Int));
        let i = terms.mk_var("i", Sort::Int);
        let j = terms.mk_var("j", Sort::Int);
        let ten = terms.mk_int(BigInt::from(10));
        let twenty = terms.mk_int(BigInt::from(20));
        let one = terms.mk_int(BigInt::from(1));
        let i_plus_one = terms.mk_add(vec![i, one]);
        let inner_store = terms.mk_store(array, i, ten);
        let outer_store = terms.mk_store(inner_store, j, twenty);
        let select_i = terms.mk_select(outer_store, i);
        let eq_select_10 = terms.mk_eq(select_i, ten);
        let not_eq_select_10 = terms.mk_not(eq_select_10);
        let j_eq_i_plus_one = terms.mk_eq(j, i_plus_one);
        let conflict = vec![
            TheoryLit::new(j_eq_i_plus_one, true),
            TheoryLit::new(not_eq_select_10, true),
        ];

        let result = verify_conflict_semantic(&conflict, &terms, &[]);
        assert!(
            result.is_ok(),
            "mixed AUFLIA nested-store conflict should be re-verified as UNSAT: {result:?}"
        );
    }
}

mod mixed_need_lemmas_verification_tests {
    use super::dispatch::{
        close_valid_lemma_clauses, verify_mixed_conflict_semantic, LemmaTrailClosure,
    };
    use super::*;
    use crate::combined_solvers::combiner::TheoryCombiner;
    use ay_core::{Sort, Symbol, TermStore, TheoryResult, TheorySolver};

    fn first_auflia_result(
        conflict: &[TheoryLit],
        support_axioms: &[TheoryLit],
        terms: &TermStore,
    ) -> TheoryResult {
        let mut combiner = TheoryCombiner::auf_lia(terms);
        for lit in conflict.iter().chain(support_axioms.iter()) {
            combiner.register_atom(lit.term);
        }
        for lit in conflict.iter().chain(support_axioms.iter()) {
            combiner.assert_literal(lit.term, lit.value);
        }
        combiner.check()
    }

    #[test]
    fn test_valid_lemma_closure_distinguishes_zero_one_and_multiple_live_literals() {
        let a = TermId(1);
        let b = TermId(2);
        let c = TermId(3);

        let mut zero_live = ay_core::kani_compat::det_hash_map_with_capacity(2);
        zero_live.insert(a, true);
        zero_live.insert(b, false);
        assert_eq!(
            close_valid_lemma_clauses(
                &[vec![TheoryLit::new(a, false), TheoryLit::new(b, true)]],
                &mut zero_live,
            ),
            LemmaTrailClosure::Contradiction,
            "a fully falsified valid clause refutes the fixed context"
        );

        let mut one_live = ay_core::kani_compat::det_hash_map_with_capacity(1);
        one_live.insert(a, true);
        assert_eq!(
            close_valid_lemma_clauses(
                &[
                    vec![TheoryLit::new(a, false), TheoryLit::new(b, true)],
                    vec![TheoryLit::new(b, false), TheoryLit::new(c, true)],
                ],
                &mut one_live,
            ),
            LemmaTrailClosure::Complete(vec![TheoryLit::new(b, true), TheoryLit::new(c, true),]),
            "unit closure must reach a fixed point across the entire batch"
        );

        let mut multiple_live = ay_core::kani_compat::det_hash_map_with_capacity(1);
        multiple_live.insert(a, true);
        assert_eq!(
            close_valid_lemma_clauses(
                &[vec![
                    TheoryLit::new(a, false),
                    TheoryLit::new(b, true),
                    TheoryLit::new(c, true),
                ]],
                &mut multiple_live,
            ),
            LemmaTrailClosure::Inconclusive,
            "the verifier must not choose a disjunct from a multi-live clause"
        );
    }

    #[test]
    fn test_mixed_verifier_materializes_row2_unit_before_rechecking() {
        let mut terms = TermStore::new();
        let array = terms.mk_var("a", Sort::array(Sort::Int, Sort::Int));
        let i = terms.mk_var("i", Sort::Int);
        let j = terms.mk_var("j", Sort::Int);
        let ten = terms.mk_int(BigInt::from(10));
        let twenty = terms.mk_int(BigInt::from(20));
        let stored = terms.mk_store(array, i, ten);
        let stored_read = terms.mk_select(stored, j);
        let base_read = terms.mk_select(array, j);
        // Intern the ROW2 equality atom without asserting it. With i != j,
        // ROW2 makes this the one live disjunct of the emitted clause.
        let _reads_equal = terms.mk_eq(stored_read, base_read);
        let indices_equal = terms.mk_eq(i, j);
        let stored_read_eq_ten = terms.mk_eq(stored_read, ten);
        let base_read_eq_twenty = terms.mk_eq(base_read, twenty);
        let conflict = vec![
            TheoryLit::new(indices_equal, false),
            TheoryLit::new(stored_read_eq_ten, true),
            TheoryLit::new(base_read_eq_twenty, true),
        ];

        assert!(
            matches!(
                first_auflia_result(&conflict, &[], &terms),
                TheoryResult::NeedLemmas(_)
            ),
            "the fresh combiner must expose the drained ROW2 lemma lifecycle"
        );
        assert!(
            verify_mixed_conflict_semantic(&conflict, &terms, &[]).is_ok(),
            "the ROW2 lemma's sole live equality is entailed and must drive the valid conflict to UNSAT"
        );
    }

    #[test]
    fn test_mixed_verifier_accepts_fully_falsified_row2_context() {
        let mut terms = TermStore::new();
        let array = terms.mk_var("a", Sort::array(Sort::Int, Sort::Int));
        let i = terms.mk_var("i", Sort::Int);
        let j = terms.mk_var("j", Sort::Int);
        let value = terms.mk_var("v", Sort::Int);
        let stored = terms.mk_store(array, i, value);
        let stored_read = terms.mk_select(stored, j);
        let base_read = terms.mk_select(array, j);
        let indices_equal = terms.mk_eq(i, j);
        let reads_equal = terms.mk_eq(stored_read, base_read);
        let conflict = vec![
            TheoryLit::new(indices_equal, false),
            TheoryLit::new(reads_equal, false),
        ];

        assert!(
            matches!(
                first_auflia_result(&conflict, &[], &terms),
                TheoryResult::NeedLemmas(_)
                    | TheoryResult::Unsat(_)
                    | TheoryResult::UnsatWithFarkas(_)
            ),
            "the fresh combiner must expose the ROW2 inconsistency either directly \
             or as a permanent lemma; zero-live cardinality is pinned separately"
        );
        assert!(
            verify_mixed_conflict_semantic(&conflict, &terms, &[]).is_ok(),
            "a fully falsified valid ROW2 clause semantically refutes the fixed context"
        );
    }

    #[test]
    fn test_mixed_verifier_counts_support_axioms_in_row2_trail() {
        let mut terms = TermStore::new();
        let array = terms.mk_var("a", Sort::array(Sort::Int, Sort::Int));
        let i = terms.mk_var("i", Sort::Int);
        let j = terms.mk_var("j", Sort::Int);
        let value = terms.mk_var("v", Sort::Int);
        let stored = terms.mk_store(array, i, value);
        let stored_read = terms.mk_select(stored, j);
        let base_read = terms.mk_select(array, j);
        let indices_equal = terms.mk_eq(i, j);
        let reads_equal = terms.mk_eq(stored_read, base_read);
        let conflict = vec![TheoryLit::new(reads_equal, false)];
        let support_axioms = vec![TheoryLit::new(indices_equal, false)];

        assert!(
            matches!(
                first_auflia_result(&conflict, &support_axioms, &terms),
                TheoryResult::NeedLemmas(_)
            ),
            "the verifier fixture must reach the ROW2 lemma with one falsifying support literal"
        );
        assert!(
            verify_mixed_conflict_semantic(&conflict, &terms, &support_axioms).is_ok(),
            "support axioms are part of the fixed trail and fully falsify ROW2 with the conflict"
        );
    }

    #[test]
    fn test_mixed_verifier_accepts_conflict_opposed_by_support_axiom() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let x_eq_zero = terms.mk_eq(x, zero);
        let conflict = vec![TheoryLit::new(x_eq_zero, false)];
        let support_axioms = vec![TheoryLit::new(x_eq_zero, true)];

        assert!(
            verify_mixed_conflict_semantic(&conflict, &terms, &support_axioms).is_ok(),
            "opposite conflict/support polarities make the verification context immediately UNSAT"
        );
    }

    #[test]
    fn test_mixed_verifier_does_not_reject_support_only_string_length_bridge() {
        let mut terms = TermStore::new();
        let s = terms.mk_var("s", Sort::String);
        let n = terms.mk_var("n", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let n_lt_zero = terms.mk_lt(n, zero);
        let len_s = terms.mk_app(Symbol::named("str.len"), vec![s], Sort::Int);
        let n_eq_len_s = terms.mk_eq(n, len_s);
        let conflict = vec![TheoryLit::new(n_lt_zero, true)];
        let support_axioms = vec![TheoryLit::new(n_eq_len_s, true)];

        assert!(
            matches!(
                verify_mixed_conflict_semantic(&conflict, &terms, &[]),
                Err(VerificationError::ConflictIsSat)
            ),
            "n < 0 alone is satisfiable and should be rejected as a spurious conflict"
        );
        assert!(
            verify_mixed_conflict_semantic(&conflict, &terms, &support_axioms).is_ok(),
            "a support-only str.len bridge makes a fresh UF+LIA/SLIA Sat verdict \
             untrustworthy and must not reject the valid n < 0, n = len(s) context"
        );
    }

    #[test]
    fn test_mixed_verifier_does_not_reject_support_only_to_real_bridge() {
        let mut terms = TermStore::new();
        let k = terms.mk_var("k", Sort::Int);
        let r = terms.mk_var("r", Sort::Real);
        let zero_i = terms.mk_int(BigInt::from(0));
        let half = terms.mk_rational(num_rational::BigRational::new(
            BigInt::from(1),
            BigInt::from(2),
        ));
        let r_eq_half = terms.mk_eq(r, half);
        let to_real_k = terms.mk_to_real(k);
        let r_eq_to_real_k = terms.mk_eq(r, to_real_k);
        let k_eq_zero = terms.mk_eq(k, zero_i);
        let conflict = vec![TheoryLit::new(r_eq_half, true)];
        let support_axioms = vec![
            TheoryLit::new(r_eq_to_real_k, true),
            TheoryLit::new(k_eq_zero, true),
        ];

        assert!(
            matches!(
                verify_mixed_conflict_semantic(&conflict, &terms, &[]),
                Err(VerificationError::ConflictIsSat)
            ),
            "r = 1/2 alone is satisfiable and should be rejected as a spurious conflict"
        );
        assert!(
            verify_mixed_conflict_semantic(&conflict, &terms, &support_axioms).is_ok(),
            "a support-only Int-to-Real bridge is outside every single-sort \
             verification combiner and must not reject the valid context"
        );
    }
}

mod bv_verification_tests {
    use super::*;
    use ay_core::{Sort, TermStore, TheoryPropagation};

    /// BV domain classification: bvult over BitVec operands should be BitVec.
    #[test]
    fn test_classify_bv_comparison_as_bitvec() {
        let mut terms = TermStore::new();
        let bv8 = Sort::bitvec(8);
        let x = terms.mk_var("x", bv8.clone());
        let y = terms.mk_var("y", bv8);
        let x_ult_y = terms.mk_bvult(x, y);

        assert_eq!(
            classify_term_domain(&terms, x_ult_y),
            TheoryDomain::BitVec,
            "bvult should classify as BitVec domain"
        );
    }

    /// BV domain classification: equality over BitVec operands should be BitVec.
    #[test]
    fn test_classify_bv_equality_as_bitvec() {
        let mut terms = TermStore::new();
        let bv8 = Sort::bitvec(8);
        let x = terms.mk_var("x", bv8.clone());
        let y = terms.mk_var("y", bv8);
        let x_eq_y = terms.mk_eq(x, y);

        assert_eq!(
            classify_term_domain(&terms, x_eq_y),
            TheoryDomain::BitVec,
            "equality over BitVec sort should classify as BitVec domain"
        );
    }

    /// BV conflict structural verification: valid conflict passes.
    ///
    /// BV verification is structural-only because the BV solver uses eager
    /// bit-blasting and cannot independently verify conflicts without a SAT
    /// solver backend.
    #[test]
    fn test_bv_conflict_structural_valid() {
        let mut terms = TermStore::new();
        let bv8 = Sort::bitvec(8);
        let x = terms.mk_var("x", bv8);
        let zero = terms.mk_bitvec(BigInt::from(0), 8);
        let x_eq_zero = terms.mk_eq(x, zero);
        let zero_ult_x = terms.mk_bvult(zero, x);

        // x = 0 AND 0 < x — structurally valid conflict
        let conflict = vec![
            TheoryLit::new(x_eq_zero, true),
            TheoryLit::new(zero_ult_x, true),
        ];

        let result = verify_bv_conflict_semantic(&conflict, &terms);
        assert!(
            result.is_ok(),
            "Structurally valid BV conflict should pass: {result:?}"
        );
    }

    /// BV conflict structural verification: multiple distinct literals pass.
    #[test]
    fn test_bv_conflict_multiple_distinct_passes() {
        let mut terms = TermStore::new();
        let bv8 = Sort::bitvec(8);
        let x = terms.mk_var("x", bv8.clone());
        let y = terms.mk_var("y", bv8);
        let x_ult_y = terms.mk_bvult(x, y);
        let x_eq_y = terms.mk_eq(x, y);

        // Structurally valid: two distinct literals
        let conflict = vec![TheoryLit::new(x_ult_y, true), TheoryLit::new(x_eq_y, false)];

        let result = verify_bv_conflict_semantic(&conflict, &terms);
        assert!(
            result.is_ok(),
            "Structurally valid BV conflict should pass: {result:?}"
        );
    }

    /// BV conflict: structural check catches empty conflict.
    #[test]
    fn test_bv_conflict_empty_rejected() {
        let terms = TermStore::new();
        let result = verify_bv_conflict_semantic(&[], &terms);
        assert!(
            matches!(result, Err(VerificationError::EmptyConflict)),
            "Empty BV conflict should be rejected: {result:?}"
        );
    }

    /// BV conflict: structural check catches duplicate literals.
    #[test]
    fn test_bv_conflict_duplicate_rejected() {
        let mut terms = TermStore::new();
        let bv8 = Sort::bitvec(8);
        let x = terms.mk_var("x", bv8);
        let zero = terms.mk_bitvec(BigInt::from(0), 8);
        let x_eq_zero = terms.mk_eq(x, zero);

        let conflict = vec![
            TheoryLit::new(x_eq_zero, true),
            TheoryLit::new(x_eq_zero, true), // duplicate
        ];

        let result = verify_bv_conflict_semantic(&conflict, &terms);
        assert!(
            matches!(result, Err(VerificationError::DuplicateLiteral { .. })),
            "Duplicate BV conflict literal should be rejected: {result:?}"
        );
    }

    /// BV propagation structural verification: valid propagation passes.
    #[test]
    fn test_bv_propagation_structural_valid() {
        let mut terms = TermStore::new();
        let bv8 = Sort::bitvec(8);
        let x = terms.mk_var("x", bv8);
        let zero = terms.mk_bitvec(BigInt::from(0), 8);
        let x_eq_zero = terms.mk_eq(x, zero);
        let x_ule_zero = terms.mk_bvule(x, zero);

        let prop = TheoryPropagation {
            literal: TheoryLit::new(x_ule_zero, true),
            reason: vec![TheoryLit::new(x_eq_zero, true)],
            reason_data: None,
        };

        let result = verify_bv_propagation(&prop, &terms);
        assert!(
            result.is_ok(),
            "Structurally valid BV propagation should pass: {result:?}"
        );
    }

    /// BV propagation: structural check catches empty reason.
    #[test]
    fn test_bv_propagation_empty_reason_rejected() {
        let mut terms = TermStore::new();
        let bv8 = Sort::bitvec(8);
        let x = terms.mk_var("x", bv8);
        let zero = terms.mk_bitvec(BigInt::from(0), 8);
        let x_eq_zero = terms.mk_eq(x, zero);

        let prop = TheoryPropagation {
            literal: TheoryLit::new(x_eq_zero, true),
            reason: vec![],
            reason_data: None,
        };

        let result = verify_bv_propagation(&prop, &terms);
        assert!(
            matches!(result, Err(VerificationError::EmptyReason)),
            "Empty reason for BV propagation should be rejected: {result:?}"
        );
    }

    /// BV propagation: structural check catches circular propagation.
    #[test]
    fn test_bv_propagation_circular_rejected() {
        let mut terms = TermStore::new();
        let bv8 = Sort::bitvec(8);
        let x = terms.mk_var("x", bv8);
        let zero = terms.mk_bitvec(BigInt::from(0), 8);
        let x_eq_zero = terms.mk_eq(x, zero);

        let prop = TheoryPropagation {
            literal: TheoryLit::new(x_eq_zero, true),
            reason: vec![TheoryLit::new(x_eq_zero, false)], // circular: same term,
            reason_data: None,
        };

        let result = verify_bv_propagation(&prop, &terms);
        assert!(
            matches!(result, Err(VerificationError::CircularPropagation { .. })),
            "Circular BV propagation should be rejected: {result:?}"
        );
    }

    /// Semantic dispatch routes BV propagation to BV structural verifier.
    #[test]
    fn test_semantic_dispatcher_bitvec() {
        let mut terms = TermStore::new();
        let bv8 = Sort::bitvec(8);
        let x = terms.mk_var("x", bv8);
        let zero = terms.mk_bitvec(BigInt::from(0), 8);
        let x_eq_zero = terms.mk_eq(x, zero);
        let x_ule_zero = terms.mk_bvule(x, zero);

        let prop = TheoryPropagation {
            literal: TheoryLit::new(x_ule_zero, true),
            reason: vec![TheoryLit::new(x_eq_zero, true)],
            reason_data: None,
        };

        let result = verify_propagation_semantic(&prop, &terms);
        assert!(
            result.is_ok(),
            "Dispatcher should route BV propagation to structural verifier: {result:?}"
        );
    }
}

mod string_verification_tests {
    use super::*;
    use ay_core::{Sort, TermStore, TheoryPropagation};

    /// String domain classification: equality over String sort.
    #[test]
    fn test_classify_string_equality_as_string() {
        let mut terms = TermStore::new();
        let s1 = terms.mk_var("s1", Sort::String);
        let s2 = terms.mk_var("s2", Sort::String);
        let eq = terms.mk_eq(s1, s2);

        assert_eq!(
            classify_term_domain(&terms, eq),
            TheoryDomain::String,
            "equality over String sort should classify as String domain"
        );
    }

    /// Seq-SORTED equality with NO native seq/string content is an EUF atom:
    /// the sort is an opaque carrier (UF-encoded sequences, e.g. verification-consumer's
    /// Seq<Int>), and its conflicts must be verifiable — and thus learnable —
    /// by congruence closure. Classifying them as String sent them to the
    /// structural string verifier, which fails on plain UF equalities; since
    /// the #8595 fail-open removal those valid conflicts were never learned
    /// and trivially-UNSAT EUF queries degraded to Unknown (2026-07-05).
    #[test]
    fn test_classify_seq_carrier_equality_as_euf() {
        let mut terms = TermStore::new();
        let seq_int = Sort::seq(Sort::Int);
        let s1 = terms.mk_var("s1", seq_int.clone());
        let s2 = terms.mk_var("s2", seq_int);
        let eq = terms.mk_eq(s1, s2);

        assert_eq!(
            classify_term_domain(&terms, eq),
            TheoryDomain::Euf,
            "equality over a Seq carrier sort with no native seq/string \
             content should classify as EUF domain"
        );
    }

    /// Seq-sorted equality that DOES contain native seq content stays in the
    /// String domain (the seq/string solver owns its semantics).
    #[test]
    fn test_classify_seq_equality_with_native_ops_as_string() {
        let mut terms = TermStore::new();
        let seq_int = Sort::seq(Sort::Int);
        let s1 = terms.mk_var("s1", seq_int.clone());
        let x = terms.mk_var("x", Sort::Int);
        let unit = terms.mk_app(ay_core::Symbol::named("seq.unit"), [x], seq_int);
        let eq = terms.mk_eq(s1, unit);

        assert_eq!(
            classify_term_domain(&terms, eq),
            TheoryDomain::String,
            "equality over Seq terms containing native seq.* content should \
             stay in the String domain"
        );
    }

    /// String conflict structural verification: valid conflict passes.
    #[test]
    fn test_string_conflict_structural_valid() {
        let mut terms = TermStore::new();
        let s1 = terms.mk_var("s1", Sort::String);
        let s2 = terms.mk_var("s2", Sort::String);
        let eq = terms.mk_eq(s1, s2);
        let hello = terms.mk_string("hello".to_string());
        let world = terms.mk_string("world".to_string());
        let s1_eq_hello = terms.mk_eq(s1, hello);
        let s2_eq_world = terms.mk_eq(s2, world);

        // s1 = s2, s1 = "hello", s2 = "world" — structurally valid conflict
        let conflict = vec![
            TheoryLit::new(eq, true),
            TheoryLit::new(s1_eq_hello, true),
            TheoryLit::new(s2_eq_world, true),
        ];

        let result = verify_string_conflict_structural(&conflict, &terms);
        assert!(
            result.is_ok(),
            "Valid string conflict should pass structural verification: {result:?}"
        );
    }

    /// String conflict structural verification: empty conflict rejected.
    #[test]
    fn test_string_conflict_empty_rejected() {
        let terms = TermStore::new();
        let result = verify_string_conflict_structural(&[], &terms);
        assert!(
            matches!(result, Err(VerificationError::EmptyConflict)),
            "Empty string conflict should be rejected: {result:?}"
        );
    }

    /// String conflict structural verification: duplicate literal rejected.
    #[test]
    fn test_string_conflict_duplicate_rejected() {
        let mut terms = TermStore::new();
        let s1 = terms.mk_var("s1", Sort::String);
        let s2 = terms.mk_var("s2", Sort::String);
        let eq = terms.mk_eq(s1, s2);

        let conflict = vec![
            TheoryLit::new(eq, true),
            TheoryLit::new(eq, true), // duplicate
        ];

        let result = verify_string_conflict_structural(&conflict, &terms);
        assert!(
            matches!(result, Err(VerificationError::DuplicateLiteral { .. })),
            "Duplicate string conflict literal should be rejected: {result:?}"
        );
    }

    /// String conflict structural verification: contradictory literals rejected.
    #[test]
    fn test_string_conflict_contradictory_rejected() {
        let mut terms = TermStore::new();
        let s1 = terms.mk_var("s1", Sort::String);
        let s2 = terms.mk_var("s2", Sort::String);
        let eq = terms.mk_eq(s1, s2);

        let conflict = vec![
            TheoryLit::new(eq, true),
            TheoryLit::new(eq, false), // contradictory
        ];

        let result = verify_string_conflict_structural(&conflict, &terms);
        assert!(
            matches!(result, Err(VerificationError::ContradictoryLiterals { .. })),
            "Contradictory string conflict literals should be rejected: {result:?}"
        );
    }

    /// String propagation structural verification: valid propagation passes.
    #[test]
    fn test_string_propagation_structural_valid() {
        let mut terms = TermStore::new();
        let s1 = terms.mk_var("s1", Sort::String);
        let s2 = terms.mk_var("s2", Sort::String);
        let s3 = terms.mk_var("s3", Sort::String);
        let eq_12 = terms.mk_eq(s1, s2);
        let eq_13 = terms.mk_eq(s1, s3);

        let prop = TheoryPropagation {
            literal: TheoryLit::new(eq_13, true),
            reason: vec![TheoryLit::new(eq_12, true)],
            reason_data: None,
        };

        let result = verify_string_propagation(&prop, &terms);
        assert!(
            result.is_ok(),
            "Valid string propagation should pass structural verification: {result:?}"
        );
    }

    /// String propagation structural verification: empty reason rejected.
    #[test]
    fn test_string_propagation_empty_reason_rejected() {
        let mut terms = TermStore::new();
        let s1 = terms.mk_var("s1", Sort::String);
        let s2 = terms.mk_var("s2", Sort::String);
        let eq = terms.mk_eq(s1, s2);

        let prop = TheoryPropagation {
            literal: TheoryLit::new(eq, true),
            reason: vec![],
            reason_data: None,
        };

        let result = verify_string_propagation(&prop, &terms);
        assert!(
            matches!(result, Err(VerificationError::EmptyReason)),
            "Empty reason for string propagation should be rejected: {result:?}"
        );
    }

    /// String propagation structural verification: circular rejected.
    #[test]
    fn test_string_propagation_circular_rejected() {
        let mut terms = TermStore::new();
        let s1 = terms.mk_var("s1", Sort::String);
        let s2 = terms.mk_var("s2", Sort::String);
        let eq = terms.mk_eq(s1, s2);

        let prop = TheoryPropagation {
            literal: TheoryLit::new(eq, true),
            reason: vec![TheoryLit::new(eq, false)],
            reason_data: None,
        };

        let result = verify_string_propagation(&prop, &terms);
        assert!(
            matches!(result, Err(VerificationError::CircularPropagation { .. })),
            "Circular string propagation should be rejected: {result:?}"
        );
    }

    /// Semantic dispatch routes String propagation correctly.
    #[test]
    fn test_semantic_dispatcher_string() {
        let mut terms = TermStore::new();
        let s1 = terms.mk_var("s1", Sort::String);
        let s2 = terms.mk_var("s2", Sort::String);
        let s3 = terms.mk_var("s3", Sort::String);
        let eq_12 = terms.mk_eq(s1, s2);
        let eq_23 = terms.mk_eq(s2, s3);
        let eq_13 = terms.mk_eq(s1, s3);

        let prop = TheoryPropagation {
            literal: TheoryLit::new(eq_13, true),
            reason: vec![TheoryLit::new(eq_12, true), TheoryLit::new(eq_23, true)],
            reason_data: None,
        };

        let result = verify_propagation_semantic(&prop, &terms);
        assert!(
            result.is_ok(),
            "Dispatcher should route String propagation: {result:?}"
        );
    }
}
