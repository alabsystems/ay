// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact-query authority tests for the native strict UNSAT replay adapter.

use super::super::{smtlib_strict_unsat_cert_via_executor, split_leading_set_logic};

#[test]
fn strict_unsat_consumer_compares_ordered_unique_assumes() {
    use ay_core::TermId;

    let repeated = [TermId(9), TermId(4), TermId(9), TermId(4), TermId(7)];
    assert_eq!(
        super::super::strict_unsat::ordered_unique_assumes(&repeated),
        vec![TermId(9), TermId(4), TermId(7)]
    );
}

/// The strict replay adapter owns one exact, fresh UNSAT obligation. Its
/// authored solve boundary must retain enough exact-query/source authority to
/// publish an independently rechecked bundle. Alethe presentation is optional;
/// removing or retargeting the bundle's obligation binding must fail closed.
fn exact_strict_bundle_fixture(script: &str) -> ay_dpll::api::SerializableProofBundle {
    let (logic, body) = split_leading_set_logic(script, ay_dpll::api::Logic::All);
    let mut solver = ay_dpll::api::Solver::try_new(logic).expect("fixture solver");
    solver.set_produce_proofs(true);
    solver
        .try_set_option(":check-proofs-strict", "true")
        .expect("strict proof option");
    let binding = solver
        .parse_smtlib2_with_exact_query_binding(&body)
        .expect("fixture exact parse");
    assert!(solver.check_sat().is_unsat(), "fixture must be UNSAT");
    solver
        .export_last_unsat_bundle_for_exact_query(&binding)
        .expect("fixture must export an exact-bound bundle")
}

#[test]
fn strict_unsat_obligation_exports_bound_recheckable_evidence() {
    let script = "(set-logic QF_LIA)\n\
        (declare-const x Int)\n\
        (assert (> x 5))\n\
        (assert (< x 3))\n\
        (check-sat)\n\
        (exit)\n";
    let cert = smtlib_strict_unsat_cert_via_executor(script, None)
        .expect("the exact contradictory obligation must publish strict evidence");
    assert!(matches!(
        &cert.strict_verdict,
        ay_dpll::api::StrictProofVerdict::Verified(quality) if quality.is_complete()
    ));
    let checked = ay_dpll::api::re_check_bundle_strict(&cert.bundle)
        .expect("the simple QF_LIA bundle must independently recheck");
    assert!(checked.quality.is_complete());
    let exact_assertions: ay_core::kani_compat::DetHashSet<_> =
        cert.bundle.obligation_assertions.iter().copied().collect();
    assert!(checked
        .assume_terms
        .iter()
        .all(|term| exact_assertions.contains(term)));
    assert_eq!(
        cert.bundle.obligation_assertions.len(),
        2,
        "returned bundle must contain exactly the two parsed hard assertions"
    );

    let mut tampered = cert.bundle;
    assert!(
        !tampered.obligation_assertions.is_empty(),
        "fixture must exercise authored-assumption binding"
    );
    tampered.obligation_assertions.clear();
    assert!(
        ay_dpll::api::re_check_bundle_strict(&tampered).is_err(),
        "removing exact obligation authority must invalidate the proof bundle"
    );
}

/// The opaque parse binding is consumed before serialization, so the returned
/// inventory contains exactly the assumptions used by the independently
/// checked proof. Mutating either that authority or the proof must fail closed.
#[test]
fn strict_unsat_obligation_consumes_exact_binding_and_rejects_mutation() {
    let script = "(set-logic QF_LIA)\n\
        (declare-const x Int)\n\
        (assert (> x 5))\n\
        (assert (< x 3))\n\
        (check-sat)\n";
    let rebound = exact_strict_bundle_fixture(script);
    let checked = ay_dpll::api::re_check_bundle_strict(&rebound)
        .expect("exact-bound fixture must independently recheck");
    assert!(checked.quality.is_complete());
    assert_eq!(
        rebound.obligation_assertions, checked.assume_terms,
        "the exact export must retain only assumptions used by the checked proof"
    );

    let mut missing_authority = rebound.clone();
    missing_authority.obligation_assertions.clear();
    assert!(
        ay_dpll::api::re_check_bundle_strict(&missing_authority).is_err(),
        "removing exact-query authority must invalidate the bundle"
    );

    let mut mutated = rebound;
    mutated
        .steps
        .pop()
        .expect("fixture proof must be non-empty");
    assert!(
        ay_dpll::api::re_check_bundle_strict(&mutated).is_err(),
        "mutating the proof DAG must invalidate strict bundle authority"
    );
}

/// The authored boundary is sealed inside an UNSAT-only adapter. A satisfiable
/// synthesized query cannot leak a model, SAT capability, or certificate-shaped
/// success through this surface.
#[test]
fn strict_unsat_obligation_rejects_sat_without_evidence() {
    let script = "(set-logic QF_LIA)\n\
        (declare-const x Int)\n\
        (assert (> x 5))\n\
        (check-sat)\n";
    assert!(
        smtlib_strict_unsat_cert_via_executor(script, None).is_none(),
        "SAT must fail closed at the UNSAT-only adapter boundary"
    );
}

/// The exact authored capability is available only for the replay format's
/// plain hard assertion inventory. Soft constraints, optimization objectives,
/// assumption-query commands, and assertions after the query boundary must not
/// be silently reinterpreted as one final plain check while minting proof
/// authority.
#[test]
fn strict_unsat_obligation_rejects_non_plain_query_shapes() {
    for non_plain in [
        "(set-logic QF_LIA)\n\
            (declare-const x Int)\n\
            (assert (> x 5))\n\
            (assert (< x 3))\n\
            (assert-soft true :weight 1)\n\
            (check-sat)\n",
        "(set-logic QF_LIA)\n\
            (declare-const x Int)\n\
            (assert (> x 5))\n\
            (assert (< x 3))\n\
            (minimize x)\n\
            (check-sat)\n",
        "(set-logic QF_LIA)\n\
            (declare-const x Int)\n\
            (assert (> x 5))\n\
            (check-sat-assuming ((< x 3)))\n",
        "(set-logic QF_LIA)\n\
            (declare-const x Int)\n\
            (assert (> x 5))\n",
        "(set-logic QF_LIA)\n\
            (declare-const x Int)\n\
            (assert (> x 5))\n\
            (check-sat)\n\
            (check-sat)\n",
        "(set-logic QF_LIA)\n\
            (declare-const x Int)\n\
            (assert (> x 5))\n\
            (check-sat)\n\
            (assert (< x 3))\n",
        "(set-logic QF_LIA)\n\
            (declare-const x Int)\n\
            (exit)\n\
            (assert (> x 5))\n\
            (assert (< x 3))\n\
            (check-sat)\n",
        "(declare-const x Int)\n\
            (assert (> x 5))\n\
            (set-logic QF_LIA)\n\
            (assert (< x 3))\n\
            (check-sat)\n",
    ] {
        assert!(
            smtlib_strict_unsat_cert_via_executor(non_plain, None).is_none(),
            "non-plain replay query must fail closed: {non_plain}"
        );
    }
}
