// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Publication-boundary coverage for datatype collapses without a strict
//! certificate.
//!
//! The former premise-binding fallback replaced a bare `trust` leaf with an
//! attributed `hole` plus an n-ary resolution. That was useful diagnostic
//! output, but it is not a proof: the hole still owns the entire UNSAT claim.
//! That remains true, and this file still pins it — the published document for
//! these pigeonholes is NOT externally checkable.
//!
//! WHY THE EXPECTATION MOVED (was: `unknown` + revoked artifacts).
//! These queries are GENUINELY UNSAT, and trivially so: `places` constants are
//! asserted `distinct` while each is constrained to one of the THREE nullary
//! constructors of `Unit`, so any `places > 3` is a pigeonhole violation. Both
//! sizes exercised here (6 and 24) are far past the threshold, and z3 confirms
//! `unsat` for both. The old `unknown` was therefore a CHECKER-COVERAGE
//! downgrade, not a solver limit: AY decided the problem correctly and then
//! discarded the answer at the publication funnel, because the datatype
//! cardinality argument exports as a `Generic` theory lemma and
//! `check_proof_strict` rejects those BY RULE NAME.
//!
//! AY has since gained the deferred-trust discharge path
//! (`Executor::discharge_trust_steps_for_certification`). It replaces "reject
//! by name" with "verify": a fresh forged-UNSAT guard must not re-decide the
//! problem as definitive SAT, every NON-trust step must still clear the full
//! strict boundary, and each deferred trust clause must be independently
//! discharged — here through the context-dependent fallback, which re-decides
//! the ORIGINAL authored assertions in a fresh `Executor` and requires UNSAT.
//! So the VERDICT is certified by an independent re-solve and `unsat` publishes.
//!
//! THE PROOF IS STILL NOT EXTERNALLY CHECKABLE. The re-solve certifies the
//! CONCLUSION, not the document: the exported certificate is unchanged and
//! still terminates in `(step t0 (cl false) :rule hole)` — the hole owns the
//! whole UNSAT claim, exactly as the paragraph above says. `check_proof_strict`
//! must keep REJECTING it, which is why `--self-check` / `--strict-proofs`
//! answer `unknown` for these queries while default mode answers `unsat`. The
//! strict-rejection assertion below is what will fire if AY ever learns a real
//! datatype-cardinality proof rule, demanding this file be promoted.

use ay_dpll::Executor;
use ay_frontend::parse;
use ay_proof::check_proof_strict;
use ntest::timeout;

fn pigeonhole_script(places: usize) -> String {
    let mut script = String::from(
        "(set-option :produce-proofs true)\n\
         (set-logic QF_DT)\n\
         (declare-datatype Unit ((u0) (u1) (u2)))\n",
    );
    for index in 0..places {
        script.push_str(&format!("(declare-fun p{index} () Unit)\n"));
    }
    for index in 0..places {
        script.push_str(&format!(
            "(assert (or (= p{index} u0) (= p{index} u1) (= p{index} u2)))\n"
        ));
    }
    script.push_str("(assert (distinct");
    for index in 0..places {
        script.push_str(&format!(" p{index}"));
    }
    script.push_str("))\n(check-sat)\n(get-proof)\n");
    script
}

/// Assert the published shape for a pigeonhole of `places` constants over the
/// 3-constructor `Unit`: a certified-verdict `unsat` whose DOCUMENT is still
/// unproved. `places` must exceed 3 for the instance to be UNSAT.
fn assert_certified_unsat_with_uncheckable_proof(places: usize) {
    assert!(
        places > 3,
        "instance is only UNSAT when it overflows Unit's 3 constructors"
    );
    let script = pigeonhole_script(places);
    let commands = parse(&script).expect("parse datatype pigeonhole");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execute datatype pigeonhole");
    // Genuinely UNSAT: `places` pairwise-distinct constants cannot fit in the
    // 3 inhabitants of `Unit`.
    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));

    // The verdict is certified (independent re-solve), so artifacts publish
    // rather than being revoked.
    let proof = exec
        .last_proof()
        .expect("a certified UNSAT must publish its proof artifacts");
    assert!(
        outputs
            .get(1)
            .is_some_and(|output| !output.contains("proof is not available")),
        "get-proof must succeed after certified publication: {outputs:?}"
    );

    // SOUNDNESS GUARD (the point of this file): the premise-binding fallback
    // must NOT dress a hole up as a checkable derivation. The hole still owns
    // the UNSAT claim, so strict checking must keep rejecting the document.
    let strict = check_proof_strict(proof, exec.terms());
    assert!(
        strict.is_err(),
        "the datatype cardinality argument has no strict rule; the checker \
         must not accept a fabricated certificate: {strict:?}"
    );
    let alethe = outputs.get(1).expect("get-proof output");
    assert!(
        alethe.contains(":rule hole") || alethe.contains(":rule trust"),
        "the uncheckable gap must be disclosed as an unproved step:\n{alethe}"
    );
}

#[test]
#[timeout(30_000)]
fn test_unsupported_datatype_pigeonhole_publishes_uncheckable_certificate() {
    assert_certified_unsat_with_uncheckable_proof(6);
}

#[test]
#[timeout(60_000)]
fn test_large_unsupported_datatype_pigeonhole_publishes_uncheckable_certificate() {
    assert_certified_unsat_with_uncheckable_proof(24);
}
