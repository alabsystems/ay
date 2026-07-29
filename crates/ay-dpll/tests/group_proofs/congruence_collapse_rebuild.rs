// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Producer-side tests for the EUF-congruence fold-to-false rebuild
//! (`rebuild_congruence_collapse` in `proof_trust_surgery.rs`).
//!
//! When the assertion set is `(= a b)` plus `(not (= C[a] C[b]))`, the
//! preprocessor rewrites one side into the other and folds the result, so the
//! exported proof degenerates to the bare `(cl false) :rule trust` that every
//! external checker rejects. The rebuild re-proves `(cl)` from the ORIGINAL
//! assertions with a single `cong` step — a first-class Alethe rule AY's own
//! strict checker validates and Carcara checks natively.

use ay_dpll::Executor;
use ay_frontend::parse;
use ay_proof::{check_proof_strict, ProofQuality};
use ntest::timeout;

fn solve_unsat(script: &str) -> (Executor, String) {
    let commands = parse(script).expect("parse SMT-LIB script");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute SMT-LIB script");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "expected UNSAT, got {outputs:?}"
    );
    let alethe = outputs.last().cloned().unwrap_or_default();
    (exec, alethe)
}

fn strict_quality(exec: &Executor) -> ProofQuality {
    let proof = exec.last_proof().expect("last proof after UNSAT");
    check_proof_strict(proof, exec.terms())
        .expect("strict checker rejected the rebuilt proof (trust/hole or invalid step)")
}

fn assert_congruence_rebuild(alethe: &str, exec: &Executor) {
    let quality = strict_quality(exec);
    assert_eq!(quality.trust_count, 0, "no trust steps: {quality}");
    assert_eq!(quality.hole_count, 0, "no hole steps: {quality}");
    assert!(
        !alethe.contains(":rule trust"),
        "printed Alethe must be trust-free:\n{alethe}"
    );
    assert!(
        !alethe.contains(":rule false"),
        "the misused `false` wiring must be gone:\n{alethe}"
    );
    assert!(
        alethe.contains(":rule cong"),
        "expected a congruence step:\n{alethe}"
    );
}

/// `(= a b)` with `(not (= (select a i) (select b i)))`: congruence at the
/// array argument of `select`.
#[test]
#[timeout(10_000)]
fn array_equality_select_congruence_rebuilds_strict() {
    let script = r#"
        (set-option :produce-proofs true)
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun i () Index)
        (assert (= a b))
        (assert (not (= (select a i) (select b i))))
        (check-sat)
        (get-proof)
    "#;
    let (exec, alethe) = solve_unsat(script);
    assert_congruence_rebuild(&alethe, &exec);
    assert!(
        alethe.contains("(step t2 (cl (= (select a i) (select b i))) :rule cong :premises (t0))"),
        "{alethe}"
    );
}

/// `(= a b)` with `(not (= (store a i v) (store b i v)))`: congruence at the
/// array argument of `store`, with two REFLEXIVE argument positions that must
/// need no premise of their own.
#[test]
#[timeout(10_000)]
fn array_equality_store_congruence_rebuilds_strict() {
    let script = r#"
        (set-option :produce-proofs true)
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun v () Element)
        (assert (= a b))
        (assert (not (= (store a i v) (store b i v))))
        (check-sat)
        (get-proof)
    "#;
    let (exec, alethe) = solve_unsat(script);
    assert_congruence_rebuild(&alethe, &exec);
    assert!(
        alethe.contains("(step t2 (cl (= (store a i v) (store b i v))) :rule cong :premises (t0))"),
        "{alethe}"
    );
}
