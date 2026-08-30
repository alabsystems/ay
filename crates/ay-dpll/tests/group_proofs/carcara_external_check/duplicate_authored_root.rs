// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Real-checker controls for duplicate authored assertion roots.

use super::*;

const CANONICAL_IDENTITY_PRESENT: &str = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const b Int)
(assert (>= (f b) 0))
(assert (<= 0 (f b)))
(assert (not (<= 0 (f b))))
(check-sat)
"#;

const IDENTICAL_NONCANONICAL_ROWS: &str = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const b Int)
(assert (>= (f b) 0))
(assert (>= (f b) 0))
(assert (not (<= 0 (f b))))
(check-sat)
"#;

#[test]
#[cfg_attr(debug_assertions, timeout(120_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn duplicate_authored_root_proofs_are_exactly_bound_or_withheld() {
    let carcara = required_carcara_for_corpus();

    let identity_proof =
        solve_unsat_and_get_proof(CANONICAL_IDENTITY_PRESENT, "duplicate_identity_present");
    assert!(
        extract_assume_terms(&identity_proof)
            .iter()
            .any(|assume| assume == "(<= 0 (f b))"),
        "the authenticated identity row must be the duplicate-root assume:\n{identity_proof}"
    );
    let (valid, diagnostic) =
        exact_carcara_verdict(&carcara, CANONICAL_IDENTITY_PRESENT, &identity_proof);
    assert!(valid, "real Carcara rejected identity proof: {diagnostic}");

    // This is the critical negative control. The canonical proof is not
    // portable to a problem containing only the semantically equivalent `>=`
    // spelling: exact problem binding must reject the unchanged document.
    let (valid, diagnostic) =
        exact_carcara_verdict(&carcara, IDENTICAL_NONCANONICAL_ROWS, &identity_proof);
    assert!(
        !valid,
        "Carcara accepted canonical assume text absent from the problem: {diagnostic}"
    );

    // Solving the all-`>=` problem afresh may publish only the exact common
    // source spelling (otherwise AY must withhold Alethe). The supported
    // comparison bridge is exact, so require publication and real validation.
    let noncanonical_proof = solve_unsat_and_get_proof(
        IDENTICAL_NONCANONICAL_ROWS,
        "duplicate_identical_noncanonical",
    );
    let assumed = extract_assume_terms(&noncanonical_proof);
    assert!(
        assumed.iter().any(|assume| assume == "(>= (f b) 0)"),
        "the duplicate root must use its exact common source spelling:\n{noncanonical_proof}"
    );
    assert!(
        !assumed.iter().any(|assume| assume == "(<= 0 (f b))"),
        "an absent canonical source must never appear as an assume:\n{noncanonical_proof}"
    );
    let asserted = extract_asserted_terms(IDENTICAL_NONCANONICAL_ROWS);
    assert!(assumed.iter().all(|assume| asserted.contains(assume)));
    let (valid, diagnostic) =
        exact_carcara_verdict(&carcara, IDENTICAL_NONCANONICAL_ROWS, &noncanonical_proof);
    assert!(
        valid,
        "AY must not publish a proof real Carcara rejects: {diagnostic}"
    );
}
