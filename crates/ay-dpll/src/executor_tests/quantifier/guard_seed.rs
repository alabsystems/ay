// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Guard-bound seed instances and the seed presolve (#nra-guard-seed-instances).
//!
//! The fixtures are the KeYmaera verification-condition shape, reduced: one
//! negated existential over a `Real` time binder whose body is a conjunction
//! of binder-free facts and one interval-guarded obligation, with nonlinear
//! dynamics. Measured on the full corpus file
//! (`keymaera/magnetic_field-node101077.smt2`) the base tree answered
//! `unknown` after the whole 20 s budget in both postures.

use super::*;

/// A refutable VC: the binder-free facts `(= m 2)` and `(= m 1)` contradict
/// each other, so the instance at ANY closed term refutes it; the obligation
/// at the guard's end point `s := t` contradicts the goal as well.
const REFUTABLE: &str = r#"
    (set-logic NRA)
    (declare-fun t () Real)
    (declare-fun a () Real)
    (declare-fun v () Real)
    (declare-fun m () Real)
    (assert (not (exists ((s Real))
      (=> (and (=> (and (<= 0 s) (<= s t)) (<= (* a s) v))
               (>= t 0) (= m 2) (= m 1) (= (* a v) 3))
          (= (* a t) v)))))
    (check-sat)
"#;

/// Only the end-point instance refutes: `s := t` turns the guarded
/// obligation into `a·t <= v`, which the goal's negation `a·t > v` closes.
///
/// `a` is declared before `t` so the exact instance of the body's `(* a s)`
/// is the goal's own canonical monomial `(* a t)`. Declared the other way,
/// the parser canonicalizes the goal to `(* t a)` while the exact
/// `forall_inst` conclusion keeps `(* a t)`; measured, the proof-producing
/// certificate probe then answers `unknown`, the presolve's refutation is not
/// adopted and the pipeline's own verdict stands (the proof-shedding
/// presolve, whose instance is built by the canonicalizing constructors,
/// refutes either way).
const END_POINT_REFUTABLE: &str = r#"
    (set-logic NRA)
    (declare-fun a () Real)
    (declare-fun t () Real)
    (declare-fun v () Real)
    (assert (not (exists ((s Real))
      (=> (and (=> (and (<= 0 s) (<= s t)) (<= (* a s) v))
               (>= t 0) (> a 0) (> (* a v) 0))
          (<= (* a t) v)))))
    (check-sat)
"#;

/// Satisfiable: the guarded obligation holds at every point of the interval
/// for `a = 0`, and nothing refutes it. Seeds are consequences only, so the
/// pass must never turn this into `unsat`.
const SATISFIABLE: &str = r#"
    (set-logic NRA)
    (declare-fun t () Real)
    (declare-fun a () Real)
    (declare-fun v () Real)
    (assert (not (exists ((s Real))
      (=> (and (=> (and (<= 0 s) (<= s t)) (<= (* a s) v))
               (>= t 0) (= (* a v) 0))
          false))))
    (check-sat)
"#;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Posture {
    /// `--z3-mode`: the proof cycle shed.
    Competition,
    /// The CLI default: best-effort proof, mandatory certification mint.
    Default,
}

struct Outcome {
    verdict: String,
    seed_instances: u64,
    presolve_published: u64,
    exec: Executor,
}

fn solve(smt: &str, posture: Posture, flags: Option<ay_core::MiscCliFlags>) -> Outcome {
    let guard = flags.map(ay_core::misc_test_override::set);
    let commands = parse(smt).expect("fixture parses");
    let mut exec = Executor::new();
    exec.set_timeout(Some(std::time::Duration::from_secs(20)));
    match posture {
        Posture::Competition => exec.set_competition_mode(true),
        Posture::Default => exec.set_best_effort_produce_proofs(1_000_000),
    }
    let outputs = exec.execute_all(&commands).expect("fixture solves");
    drop(guard);
    let stats = exec.statistics();
    Outcome {
        verdict: outputs.last().cloned().unwrap_or_default(),
        seed_instances: stats
            .get_int("quantifier.guard_seed.instances")
            .unwrap_or(0),
        presolve_published: stats
            .get_int("quantifier.guard_seed.presolve_published")
            .unwrap_or(0),
        exec,
    }
}

#[test]
fn guard_seed_presolve_refutes_the_binder_free_contradiction_in_both_postures() {
    for posture in [Posture::Competition, Posture::Default] {
        let outcome = solve(REFUTABLE, posture, None);
        assert_eq!(outcome.verdict, "unsat", "{posture:?}");
        assert!(outcome.seed_instances >= 2, "{posture:?}: seeds at 0 and t");
        assert_eq!(outcome.presolve_published, 1, "{posture:?}");
    }
}

#[test]
fn guard_seed_presolve_refutes_through_the_guard_end_point() {
    for posture in [Posture::Competition, Posture::Default] {
        let outcome = solve(END_POINT_REFUTABLE, posture, None);
        assert_eq!(outcome.verdict, "unsat", "{posture:?}");
        assert_eq!(outcome.presolve_published, 1, "{posture:?}");
    }
}

/// The default posture publishes only through an installed authored-scope
/// certificate: a `qnt_neg_exists` dual, `forall_inst` at a seed, and no
/// `trust` step anywhere, accepted by the strict checker.
#[test]
fn guard_seed_refutation_is_certified_by_forall_inst_over_the_authored_root() {
    let outcome = solve(END_POINT_REFUTABLE, Posture::Default, None);
    assert_eq!(outcome.verdict, "unsat");
    let proof = outcome
        .exec
        .last_proof()
        .cloned()
        .expect("the certified refutation leaves its proof installed");
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ay_core::ProofStep::Step {
            rule: ay_core::AletheRule::ForallInst,
            ..
        }
    )));
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ay_core::ProofStep::Step {
            rule: ay_core::AletheRule::QntNegExists,
            ..
        }
    )));
    assert!(!proof.steps.iter().any(|step| matches!(
        step,
        ay_core::ProofStep::Step {
            rule: ay_core::AletheRule::Trust,
            ..
        }
    )));
    assert!(outcome
        .exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
}

#[test]
fn guard_seeds_never_refute_a_satisfiable_vc() {
    for posture in [Posture::Competition, Posture::Default] {
        let outcome = solve(SATISFIABLE, posture, None);
        assert_ne!(outcome.verdict, "unsat", "{posture:?}");
        assert!(outcome.seed_instances >= 2, "{posture:?}: the pass ran");
        assert_eq!(outcome.presolve_published, 0, "{posture:?}");
    }
}

#[test]
fn guard_seed_kill_switch_asserts_no_seed() {
    let outcome = solve(
        REFUTABLE,
        Posture::Competition,
        Some(ay_core::MiscCliFlags {
            no_quantifier_guard_seeds: true,
            ..Default::default()
        }),
    );
    assert_eq!(outcome.seed_instances, 0);
    assert_eq!(outcome.presolve_published, 0);
    assert_ne!(outcome.verdict, "sat", "a refutable VC is never sat");
}

/// SOUNDNESS: a universal in a DISJUNCTIVE position is not entailed, so its
/// instances are not consequences and must never be seeded. Here the
/// universal is false (its instance at `t` says `a·t < 0` against `a, t > 0`)
/// and the disjunct `p` carries the model; seeding it would assert that false
/// instance as a fact and refute a satisfiable query.
#[test]
fn a_disjunctive_universal_is_never_seeded() {
    let smt = r#"
        (set-logic NRA)
        (declare-fun t () Real)
        (declare-fun a () Real)
        (declare-fun p () Bool)
        (assert (> t 0))
        (assert (> a 0))
        (assert (or p (forall ((s Real)) (=> (and (<= 0 s) (<= s t)) (< (* a s) 0)))))
        (check-sat)
    "#;
    for posture in [Posture::Competition, Posture::Default] {
        let outcome = solve(smt, posture, None);
        assert_ne!(outcome.verdict, "unsat", "{posture:?}");
        assert_eq!(outcome.seed_instances, 0, "{posture:?}");
    }
}

/// A refutation decided on the disposable probe has no unsat core, so the
/// presolve stands down when one is requested; the seeds themselves (plain
/// consequences) still reach the primary dispatch.
#[test]
fn guard_seed_presolve_stands_down_for_an_unsat_core_request() {
    let smt = format!("(set-option :produce-unsat-cores true)\n{REFUTABLE}");
    let outcome = solve(&smt, Posture::Competition, None);
    assert_eq!(outcome.presolve_published, 0);
    assert!(outcome.seed_instances >= 2);
    assert_ne!(outcome.verdict, "sat", "a refutable VC is never sat");
}
