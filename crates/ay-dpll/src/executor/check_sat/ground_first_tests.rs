// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ground-first scheduling (#qe-ground-first): which roots are set aside as
//! axioms, where the pass runs and how the refutation of the rest publishes in
//! each posture, and that the pass never decides anything that rest does not
//! refute — nor anything the ordinary pipeline decides outside competition
//! shedding.

use super::is_universal_axiom;
use crate::executor::{Executor, ProofDeclineMechanism};
use ay_frontend::parse;

/// The AUFNIRA nasa shape (`quaternion_ds1_symm_1304`): axioms the
/// instantiation pipeline cannot finish (an `Array`-sorted binder, an
/// arithmetic universal over an uninterpreted function) next to a negated goal
/// whose Skolemization is `A=0 ∧ B=0 ∧ A=3 ∧ B=4`. z3 5.1.0 answers `unsat`;
/// before this pass AY answered `unknown` in both postures. The remainder's
/// refutation rests on a trust step, so its seal is `discharged-trust`.
const NEGATED_GOAL_UNSAT: &str = r"
    (set-logic AUFNIRA)
    (declare-fun f ((Array Int Real)) Real)
    (declare-fun g (Int Int) Int)
    (declare-const def Real)
    (declare-const use Real)
    (assert (forall ((a (Array Int Real)) (n Int)) (=> (>= n 0) (>= (f a) (to_real n)))))
    (assert (forall ((x Int) (c Int)) (=> (>= x 0) (<= (g c x) x))))
    (assert (not (= def use)))
    (assert (not (forall ((A Int) (B Int))
        (or (not (= A 0)) (not (= B 0)) (not (= A 3)) (not (= B 4))))))
    (check-sat)
";

/// Without its axiom the query `{f(a) < 0}` is satisfiable; only the instance `f(a) > 0`
/// of the universal refutes the problem.
const NEEDS_AN_INSTANCE: &str = r"
    (set-logic UFLIA)
    (declare-fun f (Int) Int)
    (declare-const a Int)
    (assert (forall ((x Int)) (> (f x) 0)))
    (assert (< (f a) 0))
    (check-sat)
";

/// Satisfiable: `f := λx. 1`, `z := 0` for the negated goal's witness.
const SATISFIABLE: &str = r"
    (set-logic UFLIA)
    (declare-fun f (Int) Int)
    (declare-const a Int)
    (assert (forall ((x Int)) (> (f x) 0)))
    (assert (> (f a) 0))
    (assert (not (forall ((z Int)) (> z 5))))
    (check-sat)
";

#[derive(Clone, Copy, Debug)]
enum Posture {
    /// `--z3-mode`: competition shedding.
    Competition,
    /// The default CLI posture (best-effort Alethe sidecar).
    BestEffortSidecar,
    /// An in-script `:produce-proofs true` demand.
    ProofDemanded,
}

const POSTURES: [Posture; 3] = [
    Posture::Competition,
    Posture::BestEffortSidecar,
    Posture::ProofDemanded,
];

fn solve(source: &str, posture: Posture) -> (Vec<String>, Executor) {
    let source = match posture {
        Posture::ProofDemanded => format!("(set-option :produce-proofs true)\n{source}"),
        _ => source.to_string(),
    };
    let commands = parse(&source).unwrap();
    let mut exec = Executor::new();
    match posture {
        Posture::Competition => exec.set_competition_mode(true),
        Posture::BestEffortSidecar => exec.set_best_effort_produce_proofs(1_000_000),
        Posture::ProofDemanded => {}
    }
    let outputs = exec.execute_all(&commands).unwrap();
    (outputs, exec)
}

/// `script` in `posture` with the pass switched off (`--no-ground-first`).
fn solve_without_ground_first(source: &str, posture: Posture) -> (Vec<String>, Executor) {
    let _off = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_ground_first: true,
        ..ay_core::misc_cli_flags().clone()
    });
    solve(source, posture)
}

/// The Alethe document the query publishes.
fn document(exec: &Executor) -> String {
    let mut bytes = Vec::new();
    let exported = exec.try_export_last_proof_alethe_for_problem_scope_to(&mut bytes);
    assert!(
        matches!(exported, Some(Ok(()))),
        "no document: {exported:?}"
    );
    String::from_utf8(bytes).unwrap()
}

fn counter(exec: &Executor, name: &str) -> u64 {
    exec.statistics()
        .get_int(&format!("quantifier.ground_first.{name}"))
        .unwrap_or(0)
}

/// Whether each asserted root of `script` is set aside as an axiom.
fn axiom_membership(script: &str) -> Vec<bool> {
    let commands = parse(script).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();
    exec.ctx
        .assertions
        .iter()
        .map(|&root| is_universal_axiom(&exec.ctx.terms, root))
        .collect()
}

#[test]
fn only_top_level_universals_are_set_aside() {
    let membership = axiom_membership(
        r"
        (declare-fun p (Int) Bool)
        (declare-const c Int)
        (declare-const b Bool)
        (assert (> c 0))
        (assert (forall ((x Int)) (p x)))
        (assert (! (forall ((x Int)) (=> (p x) b)) :named ax))
        (assert (not (exists ((x Int)) (p x))))
        (assert (not (forall ((x Int)) (p x))))
        (assert (exists ((x Int)) (p x)))
        (assert (=> b (forall ((x Int)) (p x))))
        (assert (not (forall ((x Int)) (=> (forall ((y Int)) (p y)) (p x)))))
        ",
    );
    assert_eq!(
        membership,
        vec![
            false, // quantifier-free
            true,  // a universal axiom
            true,  // a named universal axiom
            true,  // a negated existential is the same universal
            false, // a negated goal: Skolemization grounds it
            false, // a positive existential
            false, // a guarded universal is a hypothesis, not an axiom
            false, // a goal whose own hypothesis is universal
        ]
    );
}

#[test]
fn refutation_publishes_directly_under_competition_shedding() {
    let (outputs, exec) = solve(NEGATED_GOAL_UNSAT, Posture::Competition);
    assert_eq!(outputs.last().map(String::as_str), Some("unsat"));
    assert_eq!(counter(&exec, "probes"), 1);
    assert_eq!(counter(&exec, "refuted"), 1);
    assert_eq!(counter(&exec, "published"), 1);
    assert_eq!(counter(&exec, "dropped_roots"), 2);
    assert_eq!(
        exec.last_command_unsat_admission_tag(),
        Some("competition-raw")
    );
}

#[test]
fn a_query_the_pipeline_leaves_unknown_is_refuted_in_the_fallback_slot() {
    let (outputs, _) = solve_without_ground_first(NEGATED_GOAL_UNSAT, Posture::BestEffortSidecar);
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unknown"),
        "the fixture must defeat the ordinary pipeline, or the fallback slot is untested"
    );
    let (outputs, exec) = solve(NEGATED_GOAL_UNSAT, Posture::BestEffortSidecar);
    assert_eq!(outputs.last().map(String::as_str), Some("unsat"));
    assert_eq!(counter(&exec, "published"), 1);
    // The theorem inherits the certifying probe's class and never upgrades it,
    // and the decline line names the theorem, not a term-construction residue.
    assert!(
        matches!(
            exec.last_command_unsat_admission_tag(),
            Some("checked-exact-authored-subset" | "discharged-trust")
        ),
        "{:?}",
        exec.last_command_unsat_admission_tag()
    );
    assert_eq!(
        exec.last_proof_decline(),
        Some(ProofDeclineMechanism::AuthoredSubsetUnrendered)
    );
    // The pipeline's `unknown` attribution does not survive beside `unsat`.
    assert_eq!(exec.statistics().get_string("unknown.reason"), None);
}

/// A quantifier-free remainder `{x > 5, x < 3}` beside an axiom.
const GROUND_REMAINDER_UNSAT: &str = r"
    (set-logic UFLIA)
    (declare-fun f (Int) Int)
    (declare-const x Int)
    (assert (forall ((y Int)) (> (f y) (f (+ y 1)))))
    (assert (> x 5))
    (assert (< x 3))
    (check-sat)
";

/// Outside competition shedding the pass never runs on a query the ordinary
/// pipeline decides: its verdict and its evidence are the pipeline's.
#[test]
fn a_query_the_pipeline_decides_keeps_the_pipeline_evidence() {
    for fixture in [GROUND_REMAINDER_UNSAT, GOAL_REMAINDER_UNSAT] {
        let (outputs, exec) = solve(fixture, Posture::BestEffortSidecar);
        assert_eq!(outputs.last().map(String::as_str), Some("unsat"));
        assert_eq!(counter(&exec, "probes"), 0);
        assert_eq!(
            exec.last_command_unsat_admission_tag(),
            Some("strict-proof")
        );
        let (_, without) = solve_without_ground_first(fixture, Posture::BestEffortSidecar);
        assert_eq!(document(&exec), document(&without));
    }
}

/// The verifier's minimal ground remainder `{x > 5, y = x + 1, y < 3}` beside
/// axioms the instantiation pipeline cannot finish, so only the fallback
/// decides it.
const FALLBACK_GROUND_UNSAT: &str = r"
    (set-logic AUFNIRA)
    (declare-fun f ((Array Int Real)) Real)
    (declare-fun g (Int Int) Int)
    (declare-const x Int)
    (declare-const y Int)
    (assert (forall ((a (Array Int Real)) (n Int)) (=> (>= n 0) (>= (f a) (to_real n)))))
    (assert (forall ((z Int) (c Int)) (=> (>= z 0) (<= (g c z) z))))
    (assert (> x 5))
    (assert (= y (+ x 1)))
    (assert (< y 3))
    (check-sat)
";

/// The fallback's document assumes each premise as the problem wrote it: the
/// probe's source spellings travel with its proof. Without them the document
/// read `(assume t0 (< 5 x))` for the authored `(> x 5)`, which AY itself
/// flagged `foreign_assumes=yes` and carcara rejected.
#[test]
fn the_fallback_document_assumes_the_authored_premises() {
    let (outputs, _) =
        solve_without_ground_first(FALLBACK_GROUND_UNSAT, Posture::BestEffortSidecar);
    assert_eq!(outputs.last().map(String::as_str), Some("unknown"));
    let (outputs, exec) = solve(FALLBACK_GROUND_UNSAT, Posture::BestEffortSidecar);
    assert_eq!(outputs.last().map(String::as_str), Some("unsat"));
    assert_eq!(counter(&exec, "published"), 1);
    assert_eq!(
        exec.last_command_unsat_admission_tag(),
        Some("strict-proof")
    );
    let document = document(&exec);
    assert!(document.contains("(assume t0.a (> x 5))"), "{document}");
    assert!(!document.contains("(assume t0 (< 5 x))"), "{document}");
    assert!(!exec.unsat_proof_terminal_trust_detected());
}

/// A satisfiable remainder beside the same axioms: the fallback probe runs,
/// does not refute, and the pipeline's `unknown` stands with the attribution
/// it recorded.
#[test]
fn a_declined_fallback_restores_the_pipeline_unknown() {
    let script = r"
        (set-logic AUFNIRA)
        (declare-fun f ((Array Int Real)) Real)
        (declare-fun g (Int Int) Int)
        (declare-const x Int)
        (assert (forall ((a (Array Int Real)) (n Int)) (=> (>= n 0) (>= (f a) (to_real n)))))
        (assert (forall ((z Int) (c Int)) (=> (>= z 0) (<= (g c z) z))))
        (assert (> x 5))
        (check-sat)
    ";
    let (outputs, exec) = solve(script, Posture::BestEffortSidecar);
    let (without_outputs, without) = solve_without_ground_first(script, Posture::BestEffortSidecar);
    assert_eq!(outputs, without_outputs);
    assert_ne!(outputs.last().map(String::as_str), Some("unsat"));
    assert_eq!(counter(&exec, "refuted"), 0);
    for key in ["unknown.reason", "unknown.phase", "unknown.cost_center"] {
        assert_eq!(
            exec.statistics().get_string(key),
            without.statistics().get_string(key),
            "{key}"
        );
    }
}

/// A stack a definitional-adoption fallback stack would re-solve does not run
/// the pass: the last stack of the chain does.
#[test]
fn the_fallback_slot_waits_for_the_last_definitional_stack() {
    let assertions = NEGATED_GOAL_UNSAT.replace("(check-sat)", "");
    let commands = parse(&assertions).unwrap();
    let mut exec = Executor::new();
    exec.set_best_effort_produce_proofs(1_000_000);
    exec.execute_all(&commands).unwrap();
    exec.ground_first_awaits_fallback_stack = true;
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    let raw = exec.check_sat().unwrap();
    assert!(!raw.is_unsat(), "{raw:?}");
    assert_eq!(counter(&exec, "probes"), 0);
}

#[test]
fn a_demanded_proof_artifact_skips_the_pass() {
    let (_, exec) = solve(NEGATED_GOAL_UNSAT, Posture::ProofDemanded);
    assert_eq!(counter(&exec, "probes"), 0);
}

#[test]
fn satisfiable_remainder_leaves_the_verdict_to_instantiation() {
    for posture in POSTURES {
        let (outputs, exec) = solve(NEEDS_AN_INSTANCE, posture);
        assert_eq!(
            outputs.last().map(String::as_str),
            Some("unsat"),
            "{posture:?}"
        );
        // Only competition shedding probes first; every other posture's
        // pipeline decides this query before its fallback slot is reached.
        let expected_probes = u64::from(matches!(posture, Posture::Competition));
        assert_eq!(counter(&exec, "probes"), expected_probes, "{posture:?}");
        assert_eq!(counter(&exec, "refuted"), 0, "{posture:?}");
        assert_eq!(counter(&exec, "published"), 0, "{posture:?}");
    }
}

#[test]
fn ground_first_never_refutes_a_satisfiable_problem() {
    for posture in POSTURES {
        let (outputs, exec) = solve(SATISFIABLE, posture);
        assert_ne!(
            outputs.last().map(String::as_str),
            Some("unsat"),
            "{posture:?}"
        );
        assert_eq!(counter(&exec, "refuted"), 0, "{posture:?}");
    }
}

#[test]
fn ground_first_is_decided_per_check_sat() {
    let script = r"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (assert (forall ((x Int)) (> (f x) 0)))
        (push 1)
        (assert (> a 5))
        (assert (< a 3))
        (check-sat)
        (pop 1)
        (assert (> (f a) 0))
        (check-sat)
    ";
    for posture in POSTURES {
        let (outputs, _) = solve(script, posture);
        assert_eq!(outputs.len(), 2, "{posture:?}: {outputs:?}");
        assert_eq!(outputs[0], "unsat", "{posture:?}");
        assert_ne!(outputs[1], "unsat", "{posture:?}");
    }
}

#[test]
fn ground_first_stands_down_when_a_core_is_requested() {
    let script = format!("(set-option :produce-unsat-cores true)\n{NEGATED_GOAL_UNSAT}");
    let (_, exec) = solve(&script, Posture::Competition);
    assert_eq!(counter(&exec, "probes"), 0);
}

#[test]
fn ground_first_stands_down_when_unsat_assumptions_are_requested() {
    let script = format!("(set-option :produce-unsat-assumptions true)\n{NEGATED_GOAL_UNSAT}");
    let (_, exec) = solve(&script, Posture::Competition);
    assert_eq!(counter(&exec, "probes"), 0);
}

/// A remainder whose only quantifier is the negated goal: Skolemization
/// grounds `∃z. z > x ∧ z + 1 <= x`, which is refuted beside an axiom.
const GOAL_REMAINDER_UNSAT: &str = r"
    (set-logic UFLIA)
    (declare-fun f (Int) Int)
    (declare-const x Int)
    (assert (forall ((y Int)) (> (f y) (f (+ y 1)))))
    (assert (not (forall ((z Int)) (=> (> z x) (> (+ z 1) x)))))
    (check-sat)
";

#[test]
fn a_subset_theorem_over_a_trust_refutation_is_a_discharged_trust_admission() {
    let commands = parse(NEGATED_GOAL_UNSAT).unwrap();
    let mut exec = Executor::new();
    exec.set_retain_parsed_assertions(true);
    let out = exec.execute_all(&commands).unwrap();
    assert_eq!(out, vec!["unsat"]);
    assert_eq!(counter(&exec, "published"), 1);
    assert_eq!(
        exec.last_command_unsat_admission_tag(),
        Some("discharged-trust")
    );
    assert!(!exec.last_command_unsat_was_exact_semantically_verified());
    let census = exec
        .last_semantic_token_census()
        .expect("the semantic mint records its census when it publishes");
    assert_eq!(census.kind, "authored-subset");
    assert_eq!(
        (
            census.obligations,
            census.nested_refuted,
            census.nested_trust_refuted
        ),
        (1, 0, 1)
    );
}

/// The class is transitive: a probe that published on this theorem seals into
/// an enclosing certificate as trust.
#[test]
fn a_probe_publishing_on_a_subset_theorem_over_trust_seals_as_trust() {
    use crate::executor::unsat_cert::ProbeUnsatAuthority;
    let assertions = NEGATED_GOAL_UNSAT.replace("(check-sat)", "");
    let commands = parse(&assertions).unwrap();
    let mut probe = Executor::new();
    probe.set_retain_parsed_assertions(true);
    probe.execute_all(&commands).unwrap();
    probe.begin_public_solve(false);
    probe.bind_unsat_query_assumptions(&[]);
    let raw = probe.check_sat().unwrap();
    assert!(raw.is_unsat(), "{raw:?}");
    let published = probe.certify_unsat_for_publication(raw, &[]);
    assert!(published.is_unsat(), "{published:?}");
    let census = probe.last_semantic_token_census().unwrap();
    assert_eq!(census.kind, "authored-subset");
    let token = probe.take_unsat_certificate().unwrap();
    assert!(!token.exact_semantic_verified());
    assert_eq!(
        token.probe_authority(),
        ProbeUnsatAuthority::DischargedTrust
    );
}
