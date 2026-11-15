// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The BvUremBound joint is asked only where a pass would pay for an exact
//! divider (`guarded/urem_bound/before_division.rs`).
//!
//! An authored `bvurem` the refutation never needs, here `y = x % 7` beside
//! `a + y < b < a + y`, is refuted with the division abstracted, so the
//! residual-trust rescue keeps its own anchor and its carcara-valid document
//! (f6555db0b, `--proof`: 67,273 bytes, `carcara check` valid). Asked
//! whenever a `bvurem` was authored, the joint displaced that anchor with a
//! 918,768-byte document that Carcara 1.1.0 rejects at `bitblast_urem`.

use ay_dpll::api::CarcaraSurface;
use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

const REMAINDER_NEVER_NEEDED_16: &str = r#"
    (set-option :produce-proofs true)
    (set-logic QF_BV)
    (declare-const x (_ BitVec 16))
    (declare-const a (_ BitVec 16))
    (declare-const b (_ BitVec 16))
    (declare-const y (_ BitVec 16))
    (assert (= y (bvurem x #x0007)))
    (assert (bvult (bvadd a y) b))
    (assert (bvult b (bvadd a y)))
    (check-sat)
"#;

#[test]
#[timeout(120_000)]
fn an_authored_remainder_the_refutation_never_needs_keeps_its_certificate() {
    let commands = parse(REMAINDER_NEVER_NEEDED_16).expect("parse");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute");
    assert_eq!(outputs, ["unsat"]);
    let proof = exec.last_proof().expect("a proof after unsat");
    assert!(
        !proof.steps.iter().any(|step| matches!(
            step,
            ay_core::ProofStep::TheoryLemma {
                kind: ay_core::TheoryLemmaKind::BvUremBound,
                ..
            }
        )),
        "the joint displaced a certificate that needs no divider: {proof:#?}"
    );
    assert!(ay_proof::terminal_trust_report(proof).is_trust_free());
    let (document, surface) = exec
        .try_export_last_proof_alethe_for_problem_scope_with_carcara_surface()
        .expect("a retained proof")
        .expect("the proof renders");
    assert!(!document.contains("bitblast_urem"), "{document}");
    assert_eq!(surface, CarcaraSurface::Supported, "{document}");
}
