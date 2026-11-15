// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A lia-mod lattice-closure refutation found at decision level 0 must reach
//! the proof as a checked integer lemma, not a whole-problem trust lemma.
//!
//! `ring_2exp16_5vars_cascade_unsat` with its first multiple-of-three
//! constraint written as a disjunction (`(or (= (* 3 m1) x1) (< m1 0))`, the
//! second disjunct refuted by `m1 >= 0`) is refuted by the lattice closure
//! (`ay_lia::lattice_refute_bridge`) before the first branch-and-bound split
//! on an unbounded `m_i`. Its core rests on carry bounds `¬(c_i <= 0)` that
//! hold at level 0, so no conflict analysis explains them. The conflict
//! recorder labelled the core `Generic`; the level-0 reconstruction closers
//! admit only non-trust leaves, so the refutation closed with one trust lemma
//! over every assertion and mandatory strict certification withheld it:
//! `unknown (incomplete self-check-rejected)`, "step t156 uses unsupported
//! theory lemma kind Generic in strict mode" (1daea89a6 answered `unsat`;
//! the lattice-closure merge 538bd3529 turned it to `unknown`).

use ay_core::{ProofStep, TheoryLemmaKind};
use ay_dpll::Executor;
use ay_frontend::parse;
use ay_proof::check_proof_strict;
use ntest::timeout;

/// The cascade variant, with `s4 = tail`.
fn cascade(tail: i64) -> String {
    format!(
        r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x1 Int) (declare-const x2 Int) (declare-const x3 Int)
        (declare-const x4 Int) (declare-const x5 Int)
        (declare-const s1 Int) (declare-const s2 Int) (declare-const s3 Int)
        (declare-const s4 Int)
        (declare-const c1 Int) (declare-const c2 Int) (declare-const c3 Int)
        (declare-const c4 Int)
        (declare-const m1 Int) (declare-const m2 Int) (declare-const m3 Int)
        (declare-const m4 Int) (declare-const m5 Int)
        (assert (>= x1 0)) (assert (<= x1 65535))
        (assert (>= x2 0)) (assert (<= x2 65535))
        (assert (>= x3 0)) (assert (<= x3 65535))
        (assert (>= x4 0)) (assert (<= x4 65535))
        (assert (>= x5 0)) (assert (<= x5 65535))
        (assert (>= s1 0)) (assert (<= s1 65535))
        (assert (>= s2 0)) (assert (<= s2 65535))
        (assert (>= s3 0)) (assert (<= s3 65535))
        (assert (>= s4 0)) (assert (<= s4 65535))
        (assert (>= c1 0)) (assert (<= c1 1))
        (assert (>= c2 0)) (assert (<= c2 1))
        (assert (>= c3 0)) (assert (<= c3 1))
        (assert (>= c4 0)) (assert (<= c4 1))
        (assert (= (+ x1 x2) (+ (* 65536 c1) s1)))
        (assert (= (+ s1 x3) (+ (* 65536 c2) s2)))
        (assert (= (+ s2 x4) (+ (* 65536 c3) s3)))
        (assert (= (+ s3 x5) (+ (* 65536 c4) s4)))
        (assert (or (= (* 3 m1) x1) (< m1 0)))
        (assert (= x2 (* 3 m2)))
        (assert (= x3 (* 3 m3)))
        (assert (= x4 (* 3 m4)))
        (assert (= x5 (* 3 m5)))
        (assert (>= m1 0)) (assert (>= m2 0)) (assert (>= m3 0))
        (assert (>= m4 0)) (assert (>= m5 0))
        (assert (>= x1 40000)) (assert (not (> x1 60000)))
        (assert (>= x2 40000)) (assert (<= x2 60000))
        (assert (>= x3 40000)) (assert (<= x3 60000))
        (assert (>= x4 40000)) (assert (<= x4 60000))
        (assert (>= x5 40000)) (assert (<= x5 60000))
        (assert (= s4 {tail}))
        (check-sat)
        "#
    )
}

fn solve(script: &str) -> (Executor, Vec<String>) {
    let commands = parse(script).expect("parse SMT-LIB script");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute SMT-LIB script");
    (exec, outputs)
}

/// Unsat under `:produce-proofs` (mandatory strict certification passed),
/// trust-free under the strict checker, and the closure's core is a checked
/// `IntCgCutChain` lemma in the published proof. `:check-proofs-strict` (and
/// `--rigor strict`) still withhold this verdict: the rendered document keeps
/// one or two printer holes, which the branch-and-bound route before the
/// closure kept as well.
#[test]
#[timeout(60_000)]
fn lattice_closure_refutation_certifies_under_produce_proofs() {
    let (exec, outputs) = solve(&cascade(1));
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "the lattice-closure refutation must certify: {outputs:?}"
    );
    let proof = exec.last_proof().expect("a proof after a certified unsat");
    let quality = check_proof_strict(proof, exec.terms())
        .expect("the strict checker accepts the published refutation");
    assert_eq!(quality.trust_count, 0, "no trust step: {quality}");
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::IntCgCutChain,
                ..
            }
        )),
        "the closure's integer-lattice core is a checked cut-chain lemma"
    );
}

/// NEGATIVE TWIN: `s4 = 2` makes the five multiples of three sum to
/// `262146 = 3·87382`, e.g. `m = (17476, 17476, 17476, 17477, 17477)` with
/// every carry set, so the variant is satisfiable and must stay `sat`.
#[test]
#[timeout(60_000)]
fn the_satisfiable_cascade_variant_stays_sat() {
    let (_, outputs) = solve(&cascade(2));
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "{outputs:?}"
    );
}
