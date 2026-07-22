// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the consumer-facing proof artifact API (#6354).
//!
//! Verifies that `export_last_unsat_artifact` returns correct quality metrics
//! and restricted-rule-subset compatibility flags for pure Boolean, QF_UF, and arithmetic cases.

use crate::api::proofs::strict_verdict_from_result;
use crate::api::*;

/// pure Boolean contradiction: p AND NOT p.
/// The proof should be trust-free and restricted-rule-subset.
#[test]
fn artifact_qf_bool_accepts_strict_and_restricted_subset() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_produce_proofs(true);

    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);

    assert!(solver.check_sat().is_unsat());

    let artifact = solver
        .export_last_unsat_artifact()
        .expect("artifact must be present after UNSAT");

    assert!(!artifact.alethe.is_empty(), "Alethe text must be non-empty");
    assert!(
        artifact.quality.is_complete(),
        "pure Boolean proof must have zero trust/hole: {}",
        artifact.quality,
    );
    assert!(
        artifact.restricted_rule_subset,
        "pure Boolean proof must be restricted-rule-subset: {}",
        artifact.quality,
    );
    assert!(
        artifact
            .lrat_certificate
            .as_ref()
            .is_some_and(|bytes| !bytes.is_empty()),
        "pure Boolean artifact should carry non-empty LRAT bytes",
    );
    assert!(
        artifact.farkas_certificates.is_empty(),
        "pure Boolean proof should not export Farkas certificates",
    );
    match &artifact.strict_verdict {
        StrictProofVerdict::Verified(quality) => {
            assert!(
                quality.is_complete(),
                "pure Boolean strict proof must remain complete: {quality}",
            );
        }
        StrictProofVerdict::Rejected(reason) => {
            panic!("pure Boolean proof must pass strict validation, got: {reason}");
        }
    }
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(()),
        "pure Boolean artifact should be acceptable in strict mode",
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::RestrictedRuleSubset),
        Ok(()),
        "pure Boolean artifact should be acceptable in restricted-rule-subset mode",
    );
}

/// End-to-end SerializableProofBundle round-trip: a LIA contradiction
/// `x = 0 /\ x < 0` is solved to UNSAT, exported as a portable bundle,
/// round-tripped through JSON, and re-checked OFFLINE via
/// [`ay_proof::re_check_bundle_strict`] — with NO solver run and no access to the
/// producer's term store. This is the genuinely-external proof re-check: the
/// verdict rests on a checked proof object, not on re-running the solver.
///
/// Also asserts the proof's `assume` axiom set equals the bundle's
/// `obligation_assertions`, so a consumer can soundly bind the proof to the
/// obligation it discharges.
#[test]
fn bundle_export_roundtrip_offline_recheck_lia() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_proofs(true);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let eq0 = solver.eq(x, zero);
    let lt0 = solver.lt(x, zero);
    solver.assert_term(eq0);
    solver.assert_term(lt0);

    assert!(
        solver.check_sat().is_unsat(),
        "x = 0 /\\ x < 0 must be UNSAT"
    );

    let bundle = solver
        .export_last_unsat_bundle()
        .expect("bundle must be present after UNSAT");
    assert_eq!(bundle.schema, PROOF_BUNDLE_SCHEMA);
    assert!(!bundle.steps.is_empty(), "bundle must carry proof steps");
    assert!(
        !bundle.term_entries.is_empty(),
        "bundle must carry the term snapshot"
    );

    // Round-trip the bundle through JSON, exactly as a certificate would embed it.
    let json = serde_json::to_string(&bundle).expect("bundle serializes to JSON");
    let restored: SerializableProofBundle =
        serde_json::from_str(&json).expect("bundle deserializes from JSON");

    // OFFLINE strict re-check: rebuild a checker-only store + proof and validate,
    // with no solver and no producer term store.
    let recheck = re_check_bundle_strict(&restored)
        .expect("offline strict re-check must accept the embedded proof");
    assert!(
        recheck.quality.is_complete(),
        "the LIA refutation must be trust/hole-free under strict re-check: {}",
        recheck.quality,
    );

    // The proof's assume axioms must equal the asserted obligation (set-equal),
    // so the offline check is genuinely about THIS obligation and nothing else.
    use std::collections::BTreeSet;
    let assume_set: BTreeSet<u32> = recheck.assume_terms.iter().map(|t| t.0).collect();
    let oblig_set: BTreeSet<u32> = restored.obligation_assertions.iter().map(|t| t.0).collect();
    assert_eq!(
        assume_set, oblig_set,
        "proof assume axioms must match the bundle obligation assertions \
         (assume={assume_set:?}, obligation={oblig_set:?})"
    );
}

/// Simple QF_UF contradiction: a=b, b=c, NOT(a=c).
/// The proof should be trust-free and restricted-rule-subset.
///
/// Uses `parse_smtlib2` to declare an uninterpreted sort, since the Rust API
/// does not yet expose `declare_sort`.
#[test]
fn artifact_qf_uf_accepts_strict_and_restricted_subset() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_produce_proofs(true);

    solver
        .parse_smtlib2(
            r#"
            (declare-sort U 0)
            (declare-fun a () U)
            (declare-fun b () U)
            (declare-fun c () U)
            (assert (= a b))
            (assert (= b c))
            (assert (not (= a c)))
            "#,
        )
        .expect("SMT-LIB2 parsing should succeed");

    assert!(solver.check_sat().is_unsat());

    let artifact = solver
        .export_last_unsat_artifact()
        .expect("artifact must be present after UNSAT");

    assert!(!artifact.alethe.is_empty(), "Alethe text must be non-empty");
    assert!(
        artifact.quality.is_complete(),
        "QF_UF proof must have zero trust/hole: {}",
        artifact.quality,
    );
    assert!(
        artifact.restricted_rule_subset,
        "simple QF_UF proof must be restricted-rule-subset: {}",
        artifact.quality,
    );
    assert!(
        matches!(
            &artifact.strict_verdict,
            StrictProofVerdict::Verified(quality) if quality.is_complete()
        ),
        "QF_UF proof must export a successful strict verdict: {:?}",
        artifact.strict_verdict,
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(()),
        "QF_UF artifact should be acceptable in strict mode",
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::RestrictedRuleSubset),
        Ok(()),
        "QF_UF artifact should be acceptable in restricted-rule-subset mode",
    );
}

/// Simple QF_LRA contradiction: x > 0 AND x < 0.
///
/// The proof should pass strict checking, but restricted-rule-subset support is currently
/// limited to a strict subset that excludes arithmetic theory lemmas.
#[test]
fn artifact_qf_lra_strict_but_not_restricted_subset() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfLra);
    solver.set_produce_proofs(true);

    let x = solver.declare_const("x", Sort::Real);
    let zero = solver.real_const(0.0);
    let gt_term = solver.gt(x, zero);
    solver.assert_term(gt_term);
    let lt_term = solver.lt(x, zero);
    solver.assert_term(lt_term);

    assert!(solver.check_sat().is_unsat());

    let artifact = solver
        .export_last_unsat_artifact()
        .expect("artifact must be present after UNSAT");

    assert!(
        matches!(&artifact.strict_verdict, StrictProofVerdict::Verified(_)),
        "LRA proof must export a successful strict verdict: {:?}",
        artifact.strict_verdict,
    );
    assert!(
        !artifact.restricted_rule_subset,
        "LRA proof should remain outside the restricted-rule-subset subset",
    );
    assert!(
        artifact
            .lrat_certificate
            .as_ref()
            .is_some_and(|bytes| !bytes.is_empty()),
        "LRA artifact should carry non-empty LRAT bytes",
    );
    assert!(
        !artifact.farkas_certificates.is_empty(),
        "LRA artifact should export Farkas certificates",
    );
    assert!(
        artifact
            .farkas_certificates
            .iter()
            .all(|certificate| !certificate.coefficients.is_empty()),
        "exported Farkas certificates should contain coefficients",
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(()),
        "LRA artifact should be acceptable in strict mode",
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::RestrictedRuleSubset),
        Err(ProofAcceptanceError::NotRestrictedRuleSubset),
        "LRA artifact should be rejected in restricted-rule-subset mode",
    );
}

/// SAT result returns None for the proof artifact.
#[test]
fn artifact_sat_returns_none() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_produce_proofs(true);

    let p = solver.declare_const("p", Sort::Bool);
    solver.assert_term(p);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    assert!(
        solver.export_last_unsat_artifact().is_none(),
        "artifact must be None after SAT result"
    );
}

/// Proofs disabled returns None for the proof artifact.
#[test]
fn artifact_proofs_disabled_returns_none() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfUf);
    // Proofs disabled by default.

    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);

    assert!(solver.check_sat().is_unsat());

    assert!(
        solver.export_last_unsat_artifact().is_none(),
        "artifact must be None when proofs not enabled"
    );
}

/// Individual proof accessor: export_last_proof_alethe returns non-empty text.
#[test]
fn alethe_export_returns_text() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_produce_proofs(true);

    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);

    assert!(solver.check_sat().is_unsat());

    let alethe = solver
        .export_last_proof_alethe()
        .expect("Alethe text must be present");
    assert!(!alethe.is_empty());
    // Alethe proofs contain assume and step/resolution commands
    assert!(
        alethe.contains("assume") || alethe.contains("step"),
        "Alethe text should contain proof commands"
    );
}

/// Individual proof accessor: last_proof_quality returns metrics.
#[test]
fn quality_accessor_returns_metrics() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_produce_proofs(true);

    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);

    assert!(solver.check_sat().is_unsat());

    let quality = solver
        .last_proof_quality()
        .expect("quality must be present");
    assert!(quality.total_steps > 0);
    assert!(quality.is_complete());
}

/// Negative regression: a whitelisted rule (AllSimplify) that derives an
/// incorrect clause must be rejected by the strict gate even though the
/// diagnostic quality says "complete" and the rule whitelist accepts it.
///
/// This is the key #6541 regression: before the strict gate, this proof would
/// have been restricted_rule_subset=true because `trust_count == 0`, `hole_count == 0`,
/// and AllSimplify is in the whitelist. Now restricted_rule_subset requires
/// check_proof_strict to succeed, which rejects unvalidated generic rules.
#[test]
fn strict_rejection_is_preserved_on_artifact_boundary() {
    use ay_core::{AletheRule, Proof, Sort as CoreSort, TermStore};
    use ay_proof::{check_proof_strict, check_proof_with_quality};

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", CoreSort::Bool);
    let not_x = terms.mk_not(x);

    // Build a bogus proof:
    //   assume x
    //   AllSimplify deriving (not x) — this is semantically wrong
    //   resolution on x to derive empty clause
    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    let bogus = proof.add_rule_step(AletheRule::AllSimplify, vec![not_x], Vec::new(), Vec::new());
    proof.add_resolution(vec![], x, h0, bogus);

    // Diagnostic (non-strict) quality should say "complete" —
    // no trust, no hole, the proof derives the empty clause.
    let diag = check_proof_with_quality(&proof, &terms)
        .expect("non-strict check should accept this proof");
    assert!(
        diag.is_complete(),
        "diagnostic quality should be complete (no trust/hole): {diag}"
    );

    // Strict checker rejects: AllSimplify is not semantically validated.
    let strict_error = check_proof_strict(&proof, &terms)
        .expect_err("strict checker must reject bogus AllSimplify");
    let strict_error_text = strict_error.to_string();
    let strict_verdict = strict_verdict_from_result(Err(strict_error));
    assert_eq!(
        strict_verdict,
        StrictProofVerdict::Rejected(strict_error_text),
        "artifact boundary must preserve the strict rejection explanation",
    );
}

/// Regression (#trust bounds-VC gap): a trivially-UNSAT CONJUNCTIVE LIA
/// assertion must export a fully verified proof. Top-level and-flattening
/// asserts the conjuncts separately; their assume steps used to be demoted to
/// unverified `trust` steps ("step t0 uses unverified trust rule"), which
/// fail-closed the strict checker on every guarded bounds VC. The conjuncts
/// are now DERIVED from the asserted conjunction via and_pos + th_resolution.
#[test]
fn conjunctive_lia_unsat_proof_is_strict_verified() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_proofs(true);
    let i = solver.declare_const("i", Sort::Int);
    let c16 = solver.int_const(16);
    let lt = solver.lt(i, c16);
    let ge = solver.ge(i, c16);
    let conj = solver.and(lt, ge);
    solver.assert_term(conj);
    assert!(solver.check_sat().is_unsat());
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("artifact must be present after UNSAT");
    assert!(
        matches!(&artifact.strict_verdict, StrictProofVerdict::Verified(_)),
        "conjunctive LIA proof must be strict-verified, got {:?}\n{}",
        artifact.strict_verdict,
        artifact.alethe,
    );
    assert!(
        artifact.quality.is_complete(),
        "proof must have zero trust/hole steps: {} \n{}",
        artifact.quality,
        artifact.alethe,
    );
}

/// Regression (#trust slice-bounds gap, second export hole): preprocessing
/// variable substitution rewrites a conjunct under a conjunct equality
/// (`(<= n5 i)` under `(= len n5)` becomes `(<= len i)`), so the SAT-level
/// unit matches no conjunct exactly and used to surface as an unverified
/// `trust` step. The export now bridges it: derive the original conjunct and
/// the equality via and_pos, then a Farkas-certified LIA lemma
/// `(cl (not E) (not C) substituted)` resolved to the unit.
#[test]
fn substituted_conjunct_unsat_proof_is_strict_verified() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_proofs(true);
    let i = solver.declare_const("i", Sort::Int);
    let len = solver.declare_const("len", Sort::Int);
    let n4 = solver.declare_const("n4", Sort::Int);
    let n5 = solver.declare_const("n5", Sort::Int);
    let b3 = solver.declare_const("b3", Sort::Bool);
    let b6 = solver.declare_const("b6", Sort::Bool);
    let lt_i_n4 = solver.lt(i, n4);
    let lt_i_n5 = solver.lt(i, n5);
    let lt_i_len = solver.lt(i, len);
    let ge_i_n5 = solver.ge(i, n5);
    let eq_n4 = solver.eq(n4, len);
    let eq_n5 = solver.eq(n5, len);
    let eq_b3 = solver.eq(b3, lt_i_n4);
    let eq_b6 = solver.eq(b6, lt_i_n5);
    let conj = solver.and_many(&[eq_n4, eq_b3, lt_i_len, eq_n5, eq_b6, ge_i_n5]);
    solver.assert_term(conj);
    assert!(solver.check_sat().is_unsat());
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("artifact must be present after UNSAT");
    assert!(
        matches!(&artifact.strict_verdict, StrictProofVerdict::Verified(_)),
        "substituted-conjunct proof must be strict-verified, got {:?}\n{}",
        artifact.strict_verdict,
        artifact.alethe,
    );
    assert!(
        artifact.quality.is_complete(),
        "proof must have zero trust/hole steps: {} \n{}",
        artifact.quality,
        artifact.alethe,
    );
}

/// Regression (#trust slice-bounds gap, cross-root substitution): the exact
/// guarded-slice-index VC shape — nested conjunctions asserted as MULTIPLE
/// roots, with a conjunct rewritten under an equality conjunct from a
/// DIFFERENT root by preprocessing variable substitution. The substituted
/// SAT-level unit is derived via and_pos chains from both roots, `cong`
/// (substitution IS congruence), and an orientation-aware equiv_pos1/2
/// tautology — never an unverified trust step.
#[test]
fn cross_root_substituted_conjunct_proof_is_strict_verified() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_proofs(true);
    let i = solver.declare_const("i", Sort::Int);
    let len = solver.declare_const("samples__slice_len", Sort::Int);
    let n4 = solver.declare_const("_4", Sort::Int);
    let n5 = solver.declare_const("_5", Sort::Int);
    let b3 = solver.declare_const("_3", Sort::Bool);
    let b6 = solver.declare_const("_6", Sort::Bool);
    let eq4 = solver.eq(n4, len);
    let lt_i_n4 = solver.lt(i, n4);
    let eq3 = solver.eq(b3, lt_i_n4);
    let lt_i_len = solver.lt(i, len);
    let eq5 = solver.eq(n5, len);
    let lt_i_n5 = solver.lt(i, n5);
    let eq6 = solver.eq(b6, lt_i_n5);
    let ge_i_n5 = solver.ge(i, n5);
    let inner3 = solver.and_many(&[eq5, eq6, ge_i_n5]);
    let inner2 = solver.and_many(&[eq4, eq3, inner3]);
    let inner1 = solver.and_many(&[lt_i_len, inner2]);
    let outer = solver.and_many(&[eq4, eq3, inner1]);
    solver.assert_term(outer);
    assert!(solver.check_sat().is_unsat());
    let artifact = solver.export_last_unsat_artifact().expect("artifact");
    assert!(
        matches!(&artifact.strict_verdict, StrictProofVerdict::Verified(_)),
        "cross-root substituted-conjunct proof must be strict-verified, got {:?}\n{}",
        artifact.strict_verdict,
        artifact.alethe,
    );
    assert!(
        artifact.quality.is_complete(),
        "proof must have zero trust/hole steps: {} \n{}",
        artifact.quality,
        artifact.alethe,
    );
}
