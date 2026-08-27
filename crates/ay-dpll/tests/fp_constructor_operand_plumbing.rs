// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Composite operands of the 3-argument `(fp s e m)` constructor.
//!
//! `decompose_fp_constructor` resolved its three fields through the LEAF-ONLY
//! `bitblast_bv_term`, which returns fresh *unconstrained* bits (and raises the
//! encoding-gap flag) for anything that is not a `Var` / 0-ary / constant. The
//! identical defect had already been found and fixed on the `to_fp` path, where
//! `bitblast_conv_bv_arg` documents it verbatim; it was simply never applied to
//! the constructor.
//!
//! It matters because the operands are composite in practice. The SV-COMP /
//! Ultimate-Automizer encoding of a `double` reinterpretation is
//!
//! ```text
//! (fp ((_ extract 63 63) q) ((_ extract 62 52) q) ((_ extract 51 0) q))
//! ```
//!
//! — three `extract`s over ONE shared 64-bit variable. Under the leaf-only call
//! each field became an independent fresh bit vector with no tie back to `q`,
//! the gap flag fired, and `solve_fp` published
//! `unknown (:reason-unknown incomplete)` with detail "FP base encoding left an
//! `ite` condition unresolved". Every assertion below returned `unknown` before
//! the fix; the expected verdicts are the ones z3 4.16.0 and cvc5 1.3.0 agree
//! on.
//!
//! Two classes of canary live here and both must stay:
//!
//! * **Capability** — the reinterpretation shape lifted verbatim from
//!   `image_filter` / `filter_iir` / `inv_Newton` in the Inc
//!   Equality_MachineArith division. It fails the moment the composite-aware
//!   encoder stops being reached.
//! * **Exactness** — the fields must be CONSTRAINED, not merely encoded. These
//!   are the ones that matter: unconstrained bits are a wrong-`sat` generator,
//!   so each `unsat` here becomes a `sat` if any field is left free. A test that
//!   only checked "the reason string changed" would pass against a fix that
//!   still leaves the bits loose.

mod common;

use common::{run_executor_smt_with_timeout, SolverOutcome};
use ntest::timeout;

const FP_TIMEOUT_SECS: u64 = 60;

fn check(name: &str, smt: &str, expected: SolverOutcome) {
    let outcome = run_executor_smt_with_timeout(smt, FP_TIMEOUT_SECS)
        .unwrap_or_else(|err| panic!("{name}: executor error: {err}"));
    assert_eq!(outcome, expected, "{name}");
}

/// CAPABILITY. The division's reinterpretation shape, verbatim: pin the
/// double built out of `q`'s three fields to `-1.0`. Satisfiable — `q` is
/// `0xBFF0000000000000`.
#[test]
#[timeout(120_000)]
fn reinterpret_double_from_extracts_is_satisfiable() {
    check(
        "reinterpret_double_from_extracts_is_satisfiable",
        r#"
        (set-logic QF_BVFP)
        (declare-const q (_ BitVec 64))
        (assert (= (fp ((_ extract 63 63) q)
                       ((_ extract 62 52) q)
                       ((_ extract 51 0) q))
                   ((_ to_fp 11 53) RNE (_ bv4294967295 32))))
        (check-sat)
        "#,
        SolverOutcome::Sat,
    );
}

/// EXACTNESS — the sign field is really `q`'s bit 63.
///
/// Pin the constructed double to `-1.0` (sign bit set) and simultaneously
/// demand `q`'s top bit be `0`. Contradictory ONLY if the sign field is tied to
/// `((_ extract 63 63) q)`. With the leaf-only encoder the field was a free
/// bit and this is `sat` — a wrong answer.
#[test]
#[timeout(120_000)]
fn sign_field_is_tied_to_its_extract() {
    check(
        "sign_field_is_tied_to_its_extract",
        r#"
        (set-logic QF_BVFP)
        (declare-const q (_ BitVec 64))
        (assert (= (fp ((_ extract 63 63) q)
                       ((_ extract 62 52) q)
                       ((_ extract 51 0) q))
                   ((_ to_fp 11 53) RNE (_ bv4294967295 32))))
        (assert (= ((_ extract 63 63) q) #b0))
        (check-sat)
        "#,
        SolverOutcome::Unsat,
    );
}

/// EXACTNESS — the significand field is really `q`'s low 52 bits.
///
/// `-1.0` has an all-zero significand, so demanding a non-zero low word is
/// contradictory exactly when the field is tied to its extract.
#[test]
#[timeout(120_000)]
fn significand_field_is_tied_to_its_extract() {
    check(
        "significand_field_is_tied_to_its_extract",
        r#"
        (set-logic QF_BVFP)
        (declare-const q (_ BitVec 64))
        (assert (= (fp ((_ extract 63 63) q)
                       ((_ extract 62 52) q)
                       ((_ extract 51 0) q))
                   ((_ to_fp 11 53) RNE (_ bv4294967295 32))))
        (assert (not (= ((_ extract 51 0) q) (_ bv0 52))))
        (check-sat)
        "#,
        SolverOutcome::Unsat,
    );
}

/// EXACTNESS — the exponent field is really `q`'s bits 62..52.
#[test]
#[timeout(120_000)]
fn exponent_field_is_tied_to_its_extract() {
    check(
        "exponent_field_is_tied_to_its_extract",
        r#"
        (set-logic QF_BVFP)
        (declare-const q (_ BitVec 64))
        (assert (= (fp ((_ extract 63 63) q)
                       ((_ extract 62 52) q)
                       ((_ extract 51 0) q))
                   ((_ to_fp 11 53) RNE (_ bv4294967295 32))))
        (assert (= ((_ extract 62 52) q) (_ bv0 11)))
        (check-sat)
        "#,
        SolverOutcome::Unsat,
    );
}

/// EXACTNESS, fully symbolic — no constant anywhere for a folding pass to
/// evaluate. Two constructors over the SAME three composite operands must
/// denote the same float, so demanding they differ is unsatisfiable. Under the
/// leaf-only encoder each constructor drew its own fresh bits and this was
/// `sat`.
#[test]
#[timeout(120_000)]
fn same_operands_give_the_same_float() {
    check(
        "same_operands_give_the_same_float",
        r#"
        (set-logic QF_BVFP)
        (declare-const q (_ BitVec 64))
        (declare-const r (_ BitVec 64))
        (assert (= q r))
        (assert (not (fp.eq
            (fp ((_ extract 63 63) q) ((_ extract 62 52) q) ((_ extract 51 0) q))
            (fp ((_ extract 63 63) r) ((_ extract 62 52) r) ((_ extract 51 0) r)))))
        (assert (not (fp.isNaN
            (fp ((_ extract 63 63) q) ((_ extract 62 52) q) ((_ extract 51 0) q)))))
        (check-sat)
        "#,
        SolverOutcome::Unsat,
    );
}

/// EXACTNESS, fully symbolic — `concat` operands, a different composite.
///
/// The field boundaries deliberately do NOT line up with the concatenation:
/// `hi` and `lo` are 32 bits each, so every extract straddles into the middle of
/// `hi`. Aligning them (`(concat s (concat e m))` with the fields extracted back
/// out) lets the simplifier fold each operand to a bare variable, and a bare
/// variable is a LEAF — the leaf-only encoder handles it fine and the test
/// silently stops discriminating. Verified: with the fix reverted this shape
/// fails and the aligned one passes.
///
/// A NaN needs an all-ones exponent and a non-zero significand; pinning `hi`'s
/// exponent bits to all-ones and `lo` to non-zero and then denying `fp.isNaN`
/// is a contradiction only if the fields are really tied to the concatenation.
#[test]
#[timeout(120_000)]
fn concat_operands_are_constrained() {
    check(
        "concat_operands_are_constrained",
        r#"
        (set-logic QF_BVFP)
        (declare-const hi (_ BitVec 32))
        (declare-const lo (_ BitVec 32))
        (assert (= ((_ extract 30 20) hi) (_ bv2047 11)))
        (assert (not (= lo (_ bv0 32))))
        (assert (not (fp.isNaN (fp ((_ extract 63 63) (concat hi lo))
                                   ((_ extract 62 52) (concat hi lo))
                                   ((_ extract 51 0) (concat hi lo))))))
        (check-sat)
        "#,
        SolverOutcome::Unsat,
    );
}

/// EXACTNESS — a mixed constructor: literal sign, composite exponent and
/// significand. The concrete field must still constrain the value (the #bug8
/// invariant) while the composite ones are tied to `q`. `+0.0` needs a zero
/// exponent AND a zero significand, so a non-zero low word refutes it.
#[test]
#[timeout(120_000)]
fn mixed_literal_and_composite_fields_all_constrain() {
    check(
        "mixed_literal_and_composite_fields_all_constrain",
        r#"
        (set-logic QF_BVFP)
        (declare-const q (_ BitVec 64))
        (assert (fp.isZero (fp #b0 ((_ extract 62 52) q) ((_ extract 51 0) q))))
        (assert (not (= ((_ extract 51 0) q) (_ bv0 52))))
        (check-sat)
        "#,
        SolverOutcome::Unsat,
    );
}
