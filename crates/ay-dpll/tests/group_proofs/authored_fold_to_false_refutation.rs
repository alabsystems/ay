// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! REACHABILITY for the fold-to-`false` promoter: the production `execute_all`
//! path in the mode a proof-artifact consumer actually runs in.
//!
//! The unit test beside the promoter proves its accepting step cannot be fooled.
//! It cannot prove anything ever builds the state. These do: an ordinary
//! SMT-LIB script whose authored assertion the preprocessor folds to `false`,
//! under `(set-option :produce-proofs true)`.
//!
//! Measured before the promoter, every accepting case here printed `unknown`:
//!
//! ```text
//! computed UNSAT rejected by mandatory strict certification:
//! strict UNSAT proof validation failed: step t0 uses unsupported hole rule
//! ```
//!
//! That `t0` is `false_source::set_empty_hole` — the ENTIRE proof erased to one
//! unattributed step, because the fold kept no record of the rewrite. Under an
//! explicit artifact request, independent query authority may not substitute
//! for the missing derivation (`nested_row_auxiliary_hole_fails_closed_when_alethe_artifact_is_required`
//! pins that), so a correct UNSAT was withdrawn. The promoter records the
//! argument instead, and the funnel's ORDINARY strict path accepts it.

use ay_dpll::Executor;
use ay_frontend::parse;

fn run(script: &str) -> (Vec<String>, Option<String>) {
    let commands = parse(script).expect("fixture script must parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("fixture script must run");
    let proof = if outputs.last().map(String::as_str) == Some("unsat") {
        let get_proof = parse("(get-proof)").expect("(get-proof) must parse");
        exec.execute_all(&get_proof)
            .ok()
            .and_then(|out| out.last().cloned())
    } else {
        None
    };
    (outputs, proof)
}

fn run_with_proofs(body: &str) -> (Vec<String>, Option<String>) {
    run(&format!("(set-option :produce-proofs true)\n{body}"))
}

/// The `trust-certify::certify_closed_constant_contradiction` shape: a
/// disjunction of CLOSED order atoms, every disjunct constant-false. This is
/// the query `finish_certificate` puts to AY (`AyProofBackend::new_with_proofs`
/// → `set_produce_proofs(true)`, no `:check-proofs-strict`) before it will
/// re-check a kernel term, and its gate is `Ok(AyProofResult::Unsat { .. })` —
/// AY's VERDICT. A withdrawal there closes the clean-CIC lane outright.
#[test]
fn closed_constant_order_atoms_publish_a_checked_refutation() {
    for assertion in [
        "(< 2 0)",
        "(>= 2 32)",
        "(or (< 2 0) (>= 2 32))",
        "(or (< 0 0) (>= 0 64))",
        "(or (< 2 0) (> 2 4294967295))",
    ] {
        let (outputs, proof) = run_with_proofs(&format!(
            "(set-logic QF_LIA)\n(assert {assertion})\n(check-sat)\n"
        ));
        assert_eq!(
            outputs.last().map(String::as_str),
            Some("unsat"),
            "{assertion}: the closed-constant contradiction lane needs a plain \
             Unsat verdict, got {outputs:?}"
        );

        // The proof is ANCHORED on the author's own assertion, not erased. A
        // bare `(step t0 (cl) :rule hole)` has no `assume` at all, so this is
        // the discriminator between "recorded" and "erased".
        let proof = proof.expect("a published UNSAT must export its artifact");
        assert!(
            proof.contains(&format!("(assume t0 {assertion})")),
            "{assertion}: the refutation must assume the AUTHORED assertion \
             verbatim, or an external checker cannot match it to the problem \
             premises:\n{proof}"
        );
        assert!(
            proof.contains(":rule th_resolution"),
            "{assertion}: the assumption must actually be resolved away:\n{proof}"
        );
    }
}

/// The promoter must never manufacture a refutation. Same fold machinery, a
/// true disjunct, so the query has a model.
#[test]
fn a_satisfiable_closed_constant_disjunction_stays_sat() {
    for assertion in [
        "(or (< 2 0) (>= 2 1))",
        "(>= 2 1)",
        "(or (< 0 1) (>= 0 64))",
    ] {
        let (outputs, _) = run_with_proofs(&format!(
            "(set-logic QF_LIA)\n(assert {assertion})\n(check-sat)\n"
        ));
        assert_eq!(
            outputs.last().map(String::as_str),
            Some("sat"),
            "{assertion} has a model and must never be published as a \
             refutation: {outputs:?}"
        );
    }
}

/// Requesting the artifact must not change the VERDICT. Before the promoter it
/// did — the caller who asked for MORE evidence got the weaker answer.
#[test]
fn the_same_query_agrees_with_and_without_an_artifact_request() {
    let body = "(set-logic QF_LIA)\n(assert (or (< 2 0) (>= 2 32)))\n(check-sat)\n";
    let (with_artifact, _) = run_with_proofs(body);
    let (without_artifact, _) = run(body);

    assert_eq!(
        with_artifact.last(),
        without_artifact.last(),
        "requesting a proof artifact must not change the verdict"
    );
}

/// THE BOUNDARY, pinned deliberately. The VerifierConsumer bare-claim obligation writes
/// its BV literals as `(_ bv1 64)`; the override-aware printer renders them
/// `#x0000000000000001`, so `rebuilt_root_prints_as_authored` refuses the
/// round-trip and the promoter declines. That guard is right — a premise an
/// external checker cannot match to the problem is strictly worse than the hole
/// it would replace (`authored_conjunct_eval`'s own rationale) — so the honest
/// state is a decline, and this pin records it.
///
/// EXPECTED TO GO RED IN THE GOOD DIRECTION once the printer and the surface
/// agree on bit-vector literal notation. A `sat` here would be the alarm.
#[test]
fn a_bitvector_literal_query_declines_the_promoter_and_stays_unknown() {
    let (outputs, _) = run_with_proofs(
        "(set-logic QF_BV)
(declare-const x (_ BitVec 64))
(declare-const r (_ BitVec 64))
(assert (= r (bvlshr x (_ bv1 64))))
(assert (not (bvule (_ bv0 64) (_ bv1 64))))
(check-sat)
",
    );
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unknown"),
        "the round-trip guard declines BV literal notation; a `sat` here would \
         mean the promoter published a model as a refutation: {outputs:?}"
    );
}
