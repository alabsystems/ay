// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A refutation that runs through LEVEL-0 lazy theory propagations must still
//! publish a strict, hole-free proof (model-checker consumer, BEANS `live_decrease`).
//!
//! Since `4a0869ae3` (2026-09-06) the LRA implied-bound propagations reach the
//! SAT core with lazy reasons. On the query below every literal of the
//! refutation is fixed at decision level 0 by BCP plus those propagations, so
//! the conflict is a level-0 conflict. A lazy reason is a theory-local handle,
//! not a clause, so `materialize_level0_unit_proofs` could not give the
//! propagated literal a unit proof, the level-0 conflict chain was incomplete,
//! and the clause trace was marked `proof_work_exhausted`. SAT proof
//! reconstruction then stopped and the SMT proof degenerated to one
//! whole-query `Generic` lemma, which mandatory strict certification rejects:
//! the computed UNSAT was published as `unknown` with
//! `step t4 uses unsupported theory lemma kind Generic in strict mode`.
//!
//! The query is the model-checker consumer's `live_decrease` obligation for the BEANS liveness spec
//! (`J /\ ~P /\ Next /\ m' >= m`, measure `b + w`), state names shortened.
//! Each proof accepted here is re-checked by the unchanged strict checker.

use ay_dpll::api::{
    re_check_bundle_strict, Logic, SerializableProofBundle, Solver, StrictProofVerdict,
};
use ay_dpll::Executor;
use ay_frontend::parse;
use ay_proof::{check_proof_strict, ProofQuality};
use ntest::timeout;

const BEANS_LIVE_DECREASE_LIA: &str = r#"
    (set-option :produce-proofs true)
    (set-logic QF_LIA)
    (declare-const b0 Int)
    (declare-const w0 Int)
    (declare-const b1 Int)
    (declare-const w1 Int)
    (assert (<= 0 (+ b0 w0)))
    (assert (<= 1 (+ b0 w0)))
    (assert (or (and (<= 1 (+ b0 w0)) (= b1 (+ b0 (- 1))) (= w0 w1))
                (and (<= 1 (+ b0 w0)) (= b0 b1) (= w1 (+ w0 (- 1))))
                (and (= w0 w1) (= b0 b1) (< (+ b0 w0) 1))))
    (assert (<= (+ b0 w0) (+ b1 w1)))
    (check-sat)
    (get-proof)
"#;

/// The same obligation over the reals: the LRA lane takes the same lazy
/// level-0 route and lost its certificate the same way.
const BEANS_LIVE_DECREASE_LRA: &str = r#"
    (set-option :produce-proofs true)
    (set-logic QF_LRA)
    (declare-const b0 Real)
    (declare-const w0 Real)
    (declare-const b1 Real)
    (declare-const w1 Real)
    (assert (<= 0.0 (+ b0 w0)))
    (assert (<= 1.0 (+ b0 w0)))
    (assert (or (and (<= 1.0 (+ b0 w0)) (= b1 (+ b0 (- 1.0))) (= w0 w1))
                (and (<= 1.0 (+ b0 w0)) (= b0 b1) (= w1 (+ w0 (- 1.0))))
                (and (= w0 w1) (= b0 b1) (< (+ b0 w0) 1.0))))
    (assert (<= (+ b0 w0) (+ b1 w1)))
    (check-sat)
    (get-proof)
"#;

/// Solve with proofs; return the executor, every command output, and the
/// rendered Alethe text.
fn solve(script: &str) -> (Executor, Vec<String>) {
    let commands = parse(script).expect("parse SMT-LIB script");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute SMT-LIB script");
    (exec, outputs)
}

fn assert_strict_hole_free_unsat(script: &str) -> ProofQuality {
    let (exec, outputs) = solve(script);
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "a computed UNSAT must survive mandatory strict certification, got {outputs:?}"
    );
    let alethe = outputs.last().cloned().unwrap_or_default();
    let proof = exec.last_proof().expect("last proof after UNSAT");
    let quality = check_proof_strict(proof, exec.terms())
        .expect("strict checker rejected the published proof");
    assert_eq!(quality.trust_count, 0, "no trust steps: {quality}");
    assert_eq!(quality.hole_count, 0, "no hole steps: {quality}");
    assert!(
        quality.theory_lemma_count >= 1,
        "expected certified Farkas lemmas: {quality}"
    );
    assert!(
        alethe.contains(":rule la_generic"),
        "expected printed la_generic lemmas:\n{alethe}"
    );
    for rule in [":rule hole", ":rule trust"] {
        assert!(
            !alethe.contains(rule),
            "printed Alethe must not contain {rule}:\n{alethe}"
        );
    }
    quality
}

#[test]
#[timeout(20_000)]
fn beans_live_decrease_lia_publishes_strict_unsat() {
    assert_strict_hole_free_unsat(BEANS_LIVE_DECREASE_LIA);
}

#[test]
#[timeout(20_000)]
fn beans_live_decrease_lra_publishes_strict_unsat() {
    assert_strict_hole_free_unsat(BEANS_LIVE_DECREASE_LRA);
}

/// Control: without a proof demand the verdict was already `unsat` and stays
/// so (the change only touches proof-tracking sessions).
#[test]
#[timeout(20_000)]
fn beans_live_decrease_without_proofs_stays_unsat() {
    let script = BEANS_LIVE_DECREASE_LIA
        .replace("(set-option :produce-proofs true)", "")
        .replace("(get-proof)", "");
    let (_exec, outputs) = solve(&script);
    assert_eq!(outputs, vec!["unsat".to_string()]);
}

/// Control: without the `m' >= m` premise the query is satisfiable (any
/// decreasing step, e.g. `b0 = 1, w0 = 0, b1 = 0, w1 = 0`, is a model), so
/// the certificate above is not bought by over-propagating at level 0.
#[test]
#[timeout(20_000)]
fn beans_without_the_decrease_premise_stays_sat() {
    let script = BEANS_LIVE_DECREASE_LIA
        .replace("(assert (<= (+ b0 w0) (+ b1 w1)))", "")
        .replace("(get-proof)", "");
    let (_exec, outputs) = solve(&script);
    assert_eq!(outputs, vec!["sat".to_string()]);
}

/// the model-checker consumer's own consumer path (`tla-check` `scratch_check_unsat_with_proof`): the
/// native API with proofs on, the exported artifact's strict verdict, and the
/// portable bundle re-checked offline after a JSON round trip, with no solver.
#[test]
#[timeout(20_000)]
fn beans_live_decrease_api_artifact_and_bundle_recheck_strictly() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA solver");
    solver.set_produce_proofs(true);
    let declarations_and_assertions = BEANS_LIVE_DECREASE_LIA
        .replace("(set-option :produce-proofs true)", "")
        .replace("(set-logic QF_LIA)", "")
        .replace("(check-sat)", "")
        .replace("(get-proof)", "");
    let asserted = solver
        .parse_smtlib2(&declarations_and_assertions)
        .expect("parse the obligation");
    assert_eq!(asserted.len(), 4);
    let verdict = solver.try_check_sat().expect("check-sat").into_inner();
    assert!(verdict.is_unsat(), "expected unsat, got {verdict:?}");

    let artifact = solver
        .export_last_unsat_artifact()
        .expect("an UNSAT proof artifact");
    assert!(
        matches!(artifact.strict_verdict, StrictProofVerdict::Verified(_)),
        "artifact strict verdict: {:?}",
        artifact.strict_verdict
    );
    let bundle = solver
        .export_last_unsat_bundle()
        .expect("a portable proof bundle");
    let json = serde_json::to_string(&bundle).expect("serialize the bundle");
    let reread: SerializableProofBundle =
        serde_json::from_str(&json).expect("deserialize the bundle");
    re_check_bundle_strict(&reread).expect("the offline strict re-check accepts the bundle");
}

fn stat(exec: &Executor, name: &str) -> u64 {
    exec.statistics().get_int(name).unwrap_or(0)
}

/// The QF_LIA lane certifies BEANS by EXPLAINING its level-0 implied bound
/// (the LRA explanation, reached through `LiaSolver`), not by dropping it.
/// d2bc57bb2 dropped every QF_LIA level-0 lazy propagation, because
/// `LiaSolver` had no explanation for its LRA's propagations; the drop is what
/// stalled the model-checker consumer's k-induction BMC (next test).
#[test]
#[timeout(20_000)]
fn beans_live_decrease_lia_explains_its_level0_implied_bound() {
    let (exec, outputs) = solve(BEANS_LIVE_DECREASE_LIA);
    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));
    let explained = stat(&exec, "dpll.eager.level0_lazy_explained");
    let unexplained = stat(&exec, "dpll.eager.level0_lazy_unexplained");
    assert!(explained >= 1, "no level-0 explanation ran: {explained}");
    assert_eq!(unexplained, 0, "a level-0 implied bound went unexplained");
    assert!(stat(&exec, "dpll.eager.props_clause_added") >= explained);
}

/// the model-checker consumer's k-induction base case for a 6-state counter at BMC depth `depth`
/// (`x_0 = 0`, `x_{i+1} = ite(x_i < 5, x_i + 1, 0)`, some `x_i` outside
/// `0..=5`): unsat, and decided by level-0 propagation alone.
fn kinduction_bmc_query(depth: usize) -> String {
    let mut script = String::from("(set-logic QF_LIA)\n");
    for i in 0..=depth {
        script.push_str(&format!("(declare-fun x_{i} () Int)\n"));
    }
    script.push_str("(assert (= x_0 0))\n");
    for i in 0..depth {
        let next = i + 1;
        script.push_str(&format!(
            "(assert (= x_{next} (ite (< x_{i} 5) (+ x_{i} 1) 0)))\n"
        ));
    }
    let violations: Vec<String> = (0..=depth)
        .map(|i| format!("(not (and (>= x_{i} 0) (<= x_{i} 5)))"))
        .collect();
    script.push_str(&format!(
        "(assert (or {}))\n(check-sat)\n",
        violations.join(" ")
    ));
    script
}

/// Work, not time: the level-0 explanation must leave the level-0 trail as
/// lazy delivery leaves it. Each level-0 lazy propagation is explained at
/// most once, and the refutation needs no search. With the d2bc57bb2 drop,
/// depth 13 took 126,943 conflicts and 507,853 decisions (0.09 s -> 45 s);
/// before it and after this fix, 0 and 0.
#[test]
#[timeout(60_000)]
fn kinduction_bmc_is_refuted_at_level0_without_search() {
    for depth in [8, 12, 13, 14, 16] {
        let (exec, outputs) = solve(&kinduction_bmc_query(depth));
        assert_eq!(outputs, vec!["unsat".to_string()], "depth {depth}");
        let conflicts = stat(&exec, "conflicts");
        let decisions = stat(&exec, "decisions");
        assert!(
            conflicts <= 100 && decisions <= 100,
            "depth {depth}: the level-0 refutation became a search \
             ({conflicts} conflicts, {decisions} decisions)"
        );
        let explained = stat(&exec, "dpll.eager.level0_lazy_explained");
        let emitted = stat(&exec, "lra_reasons_lazy_emitted");
        assert!(
            explained <= emitted,
            "depth {depth}: {explained} level-0 explanations for {emitted} lazy propagations"
        );
        let certified = stat(&exec, "dpll.eager.level0_lazy_certified");
        assert!(
            certified <= explained,
            "depth {depth}: {certified} certificates for {explained} explanations"
        );
    }
}
