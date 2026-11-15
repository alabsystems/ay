// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A REPLACEMENT proof's `assume` leaves keep the problem file's spelling.
//!
//! Two lanes install a refutation after the ordinary export collected the
//! authored spellings, and each published the CANONICAL root instead. Pinned
//! carcara matches an `assume` against the problem syntactically, so it refused
//! both documents at `t0` ("could not match term to any of the original problem
//! premises") although AY's strict checker, which compares interned roots,
//! accepted them:
//!
//! * the native SOS lane's shared installer retired the authored overrides and
//!   nothing rebuilt them: `(>= x 1)` shipped as `(assume t0 (<= 1 x))`;
//! * the consequence-replay cascade purged every printed term's spelling and
//!   the final restoration withheld the binary `distinct` root as unconfinable:
//!   `(distinct (select a #xff..ff) #x07)` shipped as
//!   `(assume t0 (not (= #b00000111 (select a #b1..1))))`.
//!
//! Both fixtures are external-corpus rows (`QF_NIA/simple_product_unsat.smt2`,
//! `model_checker_consumer_quantified_models/signed_range64_fill_unsat.smt2`) inlined without
//! their trailing `(exit)`. The SOS document is fully checked (its native
//! certificate renders through the checked `la_mult_pos`/`la_generic` lowering)
//! and so is the fill document (its guarded-instance lemma is lowered from its
//! closed signed guards, `alethe_printer/closed_guard.rs`): pinned carcara
//! answers `valid` for both, and neither row is in the corpus gate's
//! `ORACLE_UNSAT_HOLEY_PROOF_ROWS`. No `trust` step is allowed. Each test
//! asserts its exact verdict, read with NO allowance: `invalid` is the
//! premise-spelling regression, and `holey` is never external verification.

use super::{
    carcara_verdict_without_allowances, require_carcara_or_skip, solve_unsat_and_get_proof,
    CarcaraVerdict,
};
use ntest::timeout;

const SIMPLE_PRODUCT: &str = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (>= x 1))
(assert (<= x 2))
(assert (>= y 1))
(assert (<= y 2))
(assert (= (* x y) 7))
(check-sat)
"#;

const SIGNED_RANGE_FILL: &str = r#"
(set-logic ALL)
(declare-const a (Array (_ BitVec 64) (_ BitVec 8)))
(assert (forall ((i (_ BitVec 64)))
  (=> (and (bvsge i #xfffffffffffffffe) (bvslt i #x0000000000000002))
      (= (select a i) #x07))))
(assert (distinct (select a #xffffffffffffffff) #x07))
(check-sat)
"#;

fn assumes(proof: &str, spelling: &str) -> bool {
    proof
        .lines()
        .any(|line| line.starts_with("(assume ") && line.ends_with(&format!(" {spelling})")))
}

#[test]
#[timeout(60_000)]
fn native_sos_replacement_publishes_the_authored_comparison_premises() {
    let label = "replacement_premises_simple_product";
    let proof = solve_unsat_and_get_proof(SIMPLE_PRODUCT, label);
    assert!(
        proof.contains("ay-nra-sos"),
        "fixture must still exercise the native SOS replacement lane:\n{proof}"
    );
    for authored in ["(>= x 1)", "(>= y 1)"] {
        assert!(
            assumes(&proof, authored),
            "{authored} is the premise:\n{proof}"
        );
    }
    for canonical in ["(<= 1 x)", "(<= 1 y)"] {
        assert!(
            !assumes(&proof, canonical),
            "{canonical} is no premise:\n{proof}"
        );
    }
    assert!(!proof.contains(":rule trust"), "{proof}");
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    assert!(!proof.contains(":rule hole"), "{proof}");
    assert_eq!(
        carcara_verdict_without_allowances(&carcara, label, SIMPLE_PRODUCT, &proof),
        CarcaraVerdict::Valid,
        "the SOS replacement document, lowered SOS certificate included, must be re-derived by pinned carcara"
    );
}

#[test]
#[timeout(60_000)]
fn consequence_replay_replacement_publishes_the_authored_distinct_premise() {
    let label = "replacement_premises_signed_range_fill";
    let proof = solve_unsat_and_get_proof(SIGNED_RANGE_FILL, label);
    assert!(
        assumes(&proof, "(distinct (select a #xffffffffffffffff) #x07)"),
        "the authored distinct is the premise:\n{proof}"
    );
    assert!(proof.contains(":rule distinct_elim"), "{proof}");
    assert!(
        !proof
            .lines()
            .any(|line| line.starts_with("(assume ") && line.contains("(not (= #b00000111")),
        "the canonical negated equality is no premise:\n{proof}"
    );
    assert!(!proof.contains(":rule trust"), "{proof}");
    assert!(!proof.contains(":rule hole"), "{proof}");
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    assert_eq!(
        carcara_verdict_without_allowances(&carcara, label, SIGNED_RANGE_FILL, &proof),
        CarcaraVerdict::Valid,
        "the consequence-replay document must be re-derived by pinned carcara in full"
    );
}
