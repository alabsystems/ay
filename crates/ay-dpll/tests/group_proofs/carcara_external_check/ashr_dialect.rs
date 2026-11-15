// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `bitblast_ashr` in both Alethe dialects, end to end through the Executor
//! and pinned Carcara 9a352ee.
//!
//! REGRESSION (475ba9547, measured 2026-09-29 on 938ec0327): a QF_BV
//! refutation that needs the sign-extending meaning of `bvashr` over an
//! operand whose sign bit is not literally `false` prints a `bitblast_ashr`
//! step, spelled since 475ba9547 with Clean's sign-filled final layer. Pinned
//! Carcara refuses that step (`with rule 'bitblast_ashr'`), and AY disclosed
//! the document `carcara_surface=supported`. The Clean spelling stays the
//! default, because external-codegen promotes on Clean; `Executor::set_alethe_dialect`
//! selects the pinned spelling, which must be a literal `valid`.
//!
//! The fixtures are the reviser's probes: a constant shift of a symbolic byte
//! (p01), a negative byte shifted by a constant (p02, the packed lane), a
//! fixed negative operand (p09, the complete bit-blast lane), the widest shift
//! a 64-bit word admits (p14), a 4-bit shift by one (p15) and `ASR #0` (p16).

use super::Executor;
use super::{exact_carcara_verdict, parse, require_carcara_or_skip};
use ay_proof::AletheDialect;
use ntest::timeout;

const PROBES: [(&str, &str); 6] = [
    (
        "p01_const3_w8",
        "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n\
         (assert (not (= (bvashr x #x03) ((_ sign_extend 3) ((_ extract 7 3) x)))))\n(check-sat)\n",
    ),
    (
        "p02_neg_const_w8",
        "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n\
         (assert (bvslt x #x00))\n(assert (bvsge (bvashr x #x02) #x00))\n(check-sat)\n",
    ),
    (
        "p09_ground_neg",
        "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n\
         (assert (= x #xf0))\n(assert (not (= (bvashr x #x02) #xfc)))\n(check-sat)\n",
    ),
    (
        "p14_w64_const",
        "(set-logic QF_BV)\n(declare-const x (_ BitVec 64))\n\
         (assert (not (= (bvashr x #x000000000000003f) (ite (bvslt x #x0000000000000000) \
         #xffffffffffffffff #x0000000000000000))))\n(check-sat)\n",
    ),
    (
        "p15_w4_const1",
        "(set-logic QF_BV)\n(declare-const x (_ BitVec 4))\n\
         (assert (not (= ((_ extract 3 3) (bvashr x #x1)) ((_ extract 3 3) x))))\n(check-sat)\n",
    ),
    (
        "p16_asr0",
        "(set-logic QF_BV)\n(declare-const x (_ BitVec 32))\n\
         (assert (not (= (bvashr x #x00000000) x)))\n(check-sat)\n",
    ),
];

/// `unsat` and the `(get-proof)` document of `problem`, in `dialect`.
fn proof_in(dialect: AletheDialect, label: &str, problem: &str) -> String {
    let script = format!("(set-option :produce-proofs true)\n{problem}\n(get-proof)\n");
    let mut exec = Executor::new();
    exec.set_alethe_dialect(dialect);
    let outputs = exec
        .execute_all(&parse(&script).expect("parse SMT-LIB script"))
        .expect("execute SMT-LIB script");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{label}"
    );
    let proof = outputs.last().cloned().expect("proof output");
    assert!(
        proof.contains(":rule bitblast_ashr"),
        "{label}: no bitblast_ashr\n{proof}"
    );
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "{label}: the certificate must carry no unchecked step:\n{proof}"
    );
    proof
}

#[test]
#[timeout(300_000)]
fn test_carcara_bvashr_pinned_dialect_is_valid_and_restricted_subset_is_refused() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    for (label, problem) in PROBES {
        let pinned = proof_in(AletheDialect::PinnedCarcara, label, problem);
        let (valid, diagnostic) = exact_carcara_verdict(&carcara, problem, &pinned);
        assert!(
            valid,
            "{label}: the pinned dialect must be a literal `valid`: {diagnostic}"
        );

        // NEGATIVE TWIN: the default (Clean) document of the same query is the
        // one the certificate line discloses `carcara_surface=clean-dialect`;
        // pinned Carcara must refuse it, and refuse it AT `bitblast_ashr`.
        let clean = proof_in(AletheDialect::Clean, label, problem);
        assert_ne!(clean, pinned, "{label}: the dialects must differ here");
        let (valid, diagnostic) = exact_carcara_verdict(&carcara, problem, &clean);
        assert!(
            !valid && diagnostic.contains("with rule 'bitblast_ashr'"),
            "{label}: the Clean layer must be refused at bitblast_ashr: {diagnostic}"
        );
    }
}

/// The selection is host configuration: it survives `(reset)`.
#[test]
fn the_alethe_dialect_survives_reset() {
    let mut exec = Executor::new();
    assert_eq!(
        exec.alethe_dialect(),
        AletheDialect::Clean,
        "Clean is the default"
    );
    exec.set_alethe_dialect(AletheDialect::PinnedCarcara);
    exec.execute_all(&parse("(reset)\n").expect("parse"))
        .expect("reset");
    assert_eq!(exec.alethe_dialect(), AletheDialect::PinnedCarcara);
}
