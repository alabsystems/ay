// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #prepass-reachability: a check-sat pre-pass may not be gated on a condition
//! that is unconditionally false on the public path.
//!
//! A pre-pass behind an always-false guard is DEAD, not opted out — and it is
//! dead SILENTLY. Every fail-closed pre-pass degrades to "keep the status quo",
//! which is byte-identical to never running, so no verdict-level assertion can
//! tell the two apart. This codebase has paid for that repeatedly: the doc
//! comment on `Executor::produce_proofs_enabled` lists ten passes that stopped
//! firing when the internal UNSAT certificate became mandatory (two QF_ABV
//! instances regressed `unsat` -> `unknown`), `cegar_refine_solve` was the
//! eleventh, the nested-array residue rescue the twelfth, and the deep-QE
//! pre-pass the thirteenth.
//!
//! The tests below close the class structurally instead of one site at a time,
//! by observing counters the solver itself never reads:
//!
//! * `deep_qe_applicable` — the site was reached and the pass APPLIES
//!   (quantified assertions are present). Anything that keeps the pass from
//!   running past this point is a mode guard, not applicability.
//! * `deep_qe_internal_tracker_on` — `produce_proofs_enabled()` sampled AT the
//!   site. This pins the trap as a measurement: the predicate whose negation
//!   reads like "the caller did not ask for proofs" is in fact always true
//!   there, so `!produce_proofs_enabled()` is a vacuous guard.
//! * `deep_qe_entered` — the pass actually ran.
//!
//! Asserting on reachability rather than on a verdict is the whole point: a
//! dead fail-closed pre-pass and a live one that refuses produce the SAME
//! verdict, which is exactly why the previous twelve instances were invisible.

use super::*;

/// A quantified LIA problem squarely inside the deep-QE fragment.
const QUANTIFIED_LIA: &str = r#"
    (set-logic LIA)
    (assert (forall ((x Int)) (exists ((y Int)) (and (> y x) (> y 5)))))
    (check-sat)
"#;

/// The trap, measured in situ: on an ORDINARY public solve — no `--proof`, no
/// `(set-option :produce-proofs true)` — the internal proof tracker is
/// recording at the pre-pass site every single time the site is reached.
///
/// `begin_public_solve` enables it for every public decision because the UNSAT
/// certificate is mandatory and does not depend on `:produce-proofs`.
/// Consequently `!produce_proofs_enabled()` is FALSE there, and any pre-pass
/// guarded by it never runs. The caller-facing question is
/// `is_producing_proofs()`, pinned here as the honest default-mode answer.
#[test]
fn internal_proof_tracking_is_unconditionally_on_at_the_prepass_site() {
    let commands = parse(QUANTIFIED_LIA).unwrap();
    let mut exec = Executor::new();
    let _ = exec.execute_all(&commands).unwrap();
    let seen = exec.prepass_reachability();

    assert!(
        seen.deep_qe_applicable > 0,
        "the deep-QE pre-pass site must be reached on a quantified problem"
    );
    assert_eq!(
        seen.deep_qe_internal_tracker_on, seen.deep_qe_applicable,
        "`produce_proofs_enabled()` is true at the pre-pass site on EVERY public \
         solve, so its negation is a vacuous guard, not a mode switch"
    );
    assert!(
        !exec.is_producing_proofs(),
        "no proof ARTIFACT was requested — that is the honest caller-facing \
         predicate, and it is the one a mode guard must use"
    );
}

/// The deep-QE pre-pass must actually execute on the lane that owns it.
///
/// Since #qe-prepass the owning lane is the `Unknown` fallback
/// (`deep_qe_unknown_retry`) rather than every solve, so the witness has to be
/// a quantified problem the ordinary lanes do NOT decide. The battery below is
/// alternation-deep LIA/LRA squarely inside the pre-pass's own fragment and far
/// outside what E-matching/CEGQI close; several inputs are used so that one of
/// them becoming decidable later cannot silently turn this test vacuous.
///
/// It fails if the pre-pass's guard is ever re-tightened onto a vacuously-false
/// condition, whatever that condition is spelled as — including a regression to
/// `!produce_proofs_enabled()`, and including an `Unknown` lane that stops
/// arming.
#[test]
fn deep_qe_prepass_is_entered_on_the_unknown_fallback_lane() {
    const UNDECIDED_BY_THE_ORDINARY_LANES: &[&str] = &[
        // Four-level alternation with a divisibility side condition.
        r"(set-logic LIA)
          (assert (forall ((x Int)) (exists ((y Int)) (forall ((z Int)) (exists ((w Int))
              (and (> w (+ x y z)) (= (mod w 3) 0)))))))
          (check-sat)",
        // Three-level LIA alternation.
        r"(set-logic LIA)
          (assert (forall ((x Int)) (exists ((y Int))
              (forall ((z Int)) (=> (< z y) (< z (+ x 10)))))))
          (check-sat)",
        // Dense-order LRA alternation (Loos-Weispfenning fragment).
        r"(set-logic LRA)
          (assert (forall ((x Real)) (exists ((y Real))
              (forall ((z Real)) (=> (< z y) (< z (+ x 1.5)))))))
          (check-sat)",
    ];

    let mut entered = 0;
    let mut applicable = 0;
    for source in UNDECIDED_BY_THE_ORDINARY_LANES {
        let commands = parse(source).unwrap();
        let mut exec = Executor::new();
        let _ = exec.execute_all(&commands).unwrap();
        let seen = exec.prepass_reachability();
        applicable += seen.deep_qe_applicable;
        entered += seen.deep_qe_entered;
    }

    assert!(
        applicable > 0,
        "the deep-QE pre-pass site must be reached on quantified problems"
    );
    assert!(
        entered > 0,
        "the deep-QE pre-pass never ran on ANY of the alternation-deep problems \
         in its own fragment — either its guard is vacuously false, or the \
         `Unknown` fallback lane no longer arms (#prepass-reachability)"
    );
}

/// A caller that asked for a proof ARTIFACT keeps the exact quantified source,
/// so the instantiation lanes can derive their ground instances with
/// `forall_inst`. That distinction is a real mode difference — this test is
/// what stops the reachability test above from being "satisfied" by deleting
/// the guard outright.
#[test]
fn deep_qe_prepass_stands_down_when_a_proof_artifact_was_requested() {
    let input = r#"
        (set-logic LIA)
        (set-option :produce-proofs true)
        (assert (forall ((x Int)) (exists ((y Int)) (forall ((z Int)) (exists ((w Int))
            (and (> w (+ x y z)) (= (mod w 3) 0)))))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let _ = exec.execute_all(&commands).unwrap();
    let seen = exec.prepass_reachability();

    assert!(
        seen.deep_qe_applicable > 0,
        "the deep-QE pre-pass site must be reached on a quantified problem"
    );
    assert_eq!(
        seen.deep_qe_entered, 0,
        "an explicit proof-artifact request must keep the authored quantified \
         source, so the pre-pass must stand down"
    );
}

/// Canonical exact finite expansion now resolves this bounded `exists` query
/// on the primary quantifier path. A successful primary SAT must not enter the
/// deep-QE fallback, which is reserved for an initial `Unknown` result.
///
/// `deep_qe_prepass_is_entered_on_the_unknown_fallback_lane` above separately
/// preserves positive reachability coverage for the fallback itself.
#[test]
fn exact_finite_exists_sat_preempts_the_deep_qe_unknown_retry() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (assert (forall ((v Int)) (= (P v) (= v 300))))
        (assert (exists ((x Int)) (and (<= 0 x) (<= x 500) (P x))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    let seen = exec.prepass_reachability();

    assert_eq!(
        outputs,
        vec!["sat"],
        "z3 5.0.0 answers sat (witness x = 300)"
    );
    assert!(
        seen.deep_qe_applicable > 0,
        "the query remains quantified at the deep-QE applicability site"
    );
    assert_eq!(
        seen.deep_qe_unknown_retries, 0,
        "exact finite expansion must resolve SAT before the Unknown-only retry"
    );
    assert_eq!(
        seen.deep_qe_entered, 0,
        "the deep-QE pre-pass must not run without an Unknown retry"
    );
}

/// Ground problems must not pay for the pre-pass at all: the site's OTHER
/// condition (`has_quantified_assertions`) is genuine applicability, not a mode
/// switch, and the reachability test must not be satisfiable by removing it.
#[test]
fn deep_qe_prepass_is_not_applicable_to_a_ground_problem() {
    let input = r#"
        (set-logic LIA)
        (declare-const a Int)
        (assert (> a 5))
        (assert (< a 100))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["sat"]);
    let seen = exec.prepass_reachability();
    assert_eq!(
        seen.deep_qe_applicable, 0,
        "a problem with no quantified assertion is not deep-QE applicable"
    );
    assert_eq!(
        seen.deep_qe_entered, 0,
        "a problem with no quantified assertion must not enter the pre-pass"
    );
}
