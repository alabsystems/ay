// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `test_proof_artifact.rs` to preserve the existing test
// fully qualified names.

// Ground string and regex refutations, and the shared post-conditions every
// one of them must meet.

/// Assert the shared post-conditions of a refutation this round's string
/// passes rebuild, and that the step the checker accepted carries `kind`.
///
/// The PLAIN-checker call is the load-bearing one. `artifact.strict_verdict`
/// is NOT enough on its own: `strict_verdict_with_deferred_trust`
/// (`api/proofs.rs`) also reports `Verified` when the deferred-trust RESCUE
/// re-discharges an unverified leaf, so it cannot distinguish "the step was
/// checked" from "the step was tolerated". `check_proof_strict_with_datatypes`
/// is the same call `mint_unsat_certificate` makes BEFORE any rescue, and it
/// runs each new validator's full independent re-derivation.
#[cfg(test)]
fn assert_string_refutation_carries_kind(solver: &Solver, kind: TheoryLemmaKind) {
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("a certified UNSAT must publish a proof artifact");
    let proof = solver
        .last_proof()
        .expect("a certified UNSAT publishes its proof");

    solver
        .executor
        .check_proof_strict_with_datatypes(proof)
        .unwrap_or_else(|error| {
            panic!(
                "the PLAIN strict checker must accept the refutation, got \
                 {error}\n{}",
                artifact.alethe,
            )
        });

    // ...and the step it accepted is the expected rule, not something else.
    // Read the proof IR, not the printed text: Carcara has no rule for these
    // internal certificates, so the WIRE name is an honest `hole` while AY's
    // own checker validates the kind.
    assert!(
        proof
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::TheoryLemma { kind: k, .. } if *k == kind)),
        "refutation must contain a checker-validated {kind:?} lemma:\n{}",
        artifact.alethe,
    );
    assert!(
        artifact.quality.is_complete(),
        "proof must have zero trust/hole steps: {}\n{}",
        artifact.quality,
        artifact.alethe,
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(()),
    );
}

/// Regression (#trust-count→0, the extended-function reduction shape):
/// `(= x "hello")` propagated into `(= (str.substr x 1 3) "abc")` leaves a
/// GROUND claim — `str.substr("hello", 1, 3)` is `"ell"`, not `"abc"` — so the
/// problem is UNSAT and z3 5.0.0 agrees. AY computed that every time and
/// published `unknown`, because the reduction happens outside the SAT trace and
/// the reconstruction closed on the whole-problem `trust` fallback.
///
/// The rebuilt refutation transports the authored literal across the ground
/// binding with `eq_congruent` / `eq_congruent_pred` (whose validators re-derive
/// the per-argument matching themselves) and closes on `StringGroundEval`, whose
/// INDEPENDENT evaluator re-decides `str.substr("hello", 1, 3)`.
#[test]
fn qfslia_substr_ground_substitution_unsat_proof_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfSlia);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun x () String)
            (assert (= x "hello"))
            (assert (= (str.substr x 1 3) "abc"))
            "#,
        )
        .expect("substr reduction fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "str.substr(\"hello\", 1, 3) is \"ell\", not \"abc\"; UNSAT (z3 5.0.0 \
         agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_string_refutation_carries_kind(&solver, TheoryLemmaKind::StringGroundEval);
}

/// The same pass over `str.indexof`: `str.indexof("abcab", "b", 0)` is the
/// LEFTMOST occurrence, `1`, not `4`. z3 5.0.0 answers `unsat`.
#[test]
fn qfslia_indexof_ground_substitution_unsat_proof_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfSlia);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun x () String)
            (assert (= x "abcab"))
            (assert (= (str.indexof x "b" 0) 4))
            "#,
        )
        .expect("indexof reduction fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "the leftmost \"b\" in \"abcab\" is at index 1, not 4; UNSAT (z3 5.0.0 \
         agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_string_refutation_carries_kind(&solver, TheoryLemmaKind::StringGroundEval);
}

/// The same pass over `str.replace`, which rewrites only the FIRST occurrence:
/// `str.replace("abcab", "b", "z")` is `"azcab"`, not `"abcaz"`. z3 5.0.0
/// answers `unsat`.
#[test]
fn qfslia_replace_ground_substitution_unsat_proof_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfSlia);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun x () String)
            (assert (= x "abcab"))
            (assert (= (str.replace x "b" "z") "abcaz"))
            "#,
        )
        .expect("replace reduction fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "str.replace rewrites only the first occurrence; UNSAT (z3 5.0.0 \
         agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_string_refutation_carries_kind(&solver, TheoryLemmaKind::StringGroundEval);
}

/// Regression (#trust-count→0, the self-containment shape): every word contains
/// itself, so `(not (str.contains x x))` is UNSAT for any `x`. z3 5.0.0 agrees.
/// The refutation states that theorem as `StringContainmentIdentity`, whose
/// validator re-checks that the two argument positions hold the SAME term.
#[test]
fn qfs_self_containment_unsat_proof_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfS);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun x () String)
            (assert (not (str.contains x x)))
            "#,
        )
        .expect("self-containment fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "a word contains itself; UNSAT (z3 5.0.0 agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_string_refutation_carries_kind(&solver, TheoryLemmaKind::StringContainmentIdentity);
}

/// Regression (#trust-count→0, the ground-factor shape): `"c"` does not occur
/// in `"ab"`, so no value of `x` makes `x ++ "c"` a factor of `"ab"` and
/// `(str.contains "ab" (str.++ x "c"))` is UNSAT. z3 5.0.0 agrees.
#[test]
fn qfs_ground_factor_conflict_unsat_proof_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfS);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun x () String)
            (assert (str.contains "ab" (str.++ x "c")))
            "#,
        )
        .expect("ground-factor fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "\"c\" is not a factor of \"ab\"; UNSAT (z3 5.0.0 agrees), got \
         {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_string_refutation_carries_kind(&solver, TheoryLemmaKind::StringGroundFactorConflict);
}

/// The boundary-block arm of the same kind: the last character of `x ++ "b"` is
/// `"b"`, so `(str.suffixof "c" (str.++ x "b"))` is UNSAT. z3 5.0.0 agrees.
/// This exercises the prefix/suffix schema (pattern no longer than the ground
/// boundary block) rather than the factor scan.
#[test]
fn qfs_ground_suffix_conflict_unsat_proof_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfS);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun x () String)
            (assert (str.suffixof "c" (str.++ x "b")))
            "#,
        )
        .expect("ground-suffix fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "the last character of x ++ \"b\" is \"b\"; UNSAT (z3 5.0.0 agrees), \
         got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_string_refutation_carries_kind(&solver, TheoryLemmaKind::StringGroundFactorConflict);
}

/// Regression (#trust-count→0, the cancellation shape): `str.++` cancels on the
/// right in the free monoid, so `x ++ "c" = y ++ "c"` forces `x = y` and the
/// added `(not (= x y))` is UNSAT. z3 5.0.0 agrees. The refutation states the
/// cancellation as `StringConcatCancellation`, whose validator re-derives the
/// shared operand run and both residuals from the clause alone.
#[test]
fn qfslia_concat_cancellation_unsat_proof_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfSlia);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun x () String)
            (declare-fun y () String)
            (assert (= (str.len x) (str.len y)))
            (assert (= (str.++ x "c") (str.++ y "c")))
            (assert (not (= x y)))
            "#,
        )
        .expect("concat cancellation fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "str.++ cancels on the right; UNSAT (z3 5.0.0 agrees), got \
         {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_string_refutation_carries_kind(&solver, TheoryLemmaKind::StringConcatCancellation);
}

/// Regression (#trust-count→0, the regex length-bound shape): `x ++ x = "aaaa"`
/// pins `2*len(x) = 4`, i.e. `len(x) = 2`, while
/// `x` in `((_ re.loop 3 5) (str.to_re "a"))` pins `len(x) >= 3`. z3 5.0.0
/// answers `unsat`.
///
/// The bound joins the existing length-arithmetic pool as a
/// `RegexLengthLowerBound` clause, whose validator recomputes the regex's
/// minimum word length compositionally, and the pool closes on a rational
/// `LraFarkas` certificate.
#[test]
fn qfs_regex_length_lower_bound_unsat_proof_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfS);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun x () String)
            (assert (= (str.++ x x) "aaaa"))
            (assert (str.in_re x ((_ re.loop 3 5) (str.to_re "a"))))
            "#,
        )
        .expect("regex length-bound fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "len(x) = 2 contradicts the regex's minimum length 3; UNSAT (z3 5.0.0 \
         agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_string_refutation_carries_kind(&solver, TheoryLemmaKind::RegexLengthLowerBound);
}
