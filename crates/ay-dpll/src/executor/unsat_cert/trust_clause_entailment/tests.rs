// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pins for step (4a), the deferred-clause entailment re-decision.

use ay_core::time::Instant;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, TermId};

use super::super::{UnsatCertificationError, WHOLE_PROBLEM_RECONFIRMATION_LIMITS};
use super::{entailment_limits, negated_clause_disjunction};
use crate::api::proofs::EnvelopeStop;
use crate::executor::{CorroborationMethod, Executor, UnsatCorroboration};
use crate::executor_types::{SolveResult, UnknownReason};

/// Eligibility reads the proof only for subproof anchors, so one bare `trust`
/// step stands in for the first solve's proof.
fn trust_only_proof() -> Proof {
    Proof::from_steps(vec![ProofStep::Step {
        rule: AletheRule::Trust,
        clause: Vec::new(),
        premises: Vec::new(),
        args: Vec::new(),
    }])
}

/// `p`, `p => q`, `q => r` (satisfiable) and the Bool variables `q`, `r` and
/// an unconstrained `s`.
fn implication_chain() -> (Executor, Vec<TermId>, [TermId; 3]) {
    let mut exec = Executor::new();
    let terms = &mut exec.ctx.terms;
    let p = terms.mk_var("entail_p", Sort::Bool);
    let q = terms.mk_var("entail_q", Sort::Bool);
    let r = terms.mk_var("entail_r", Sort::Bool);
    let s = terms.mk_var("entail_s", Sort::Bool);
    let p_implies_q = terms.mk_implies(p, q);
    let q_implies_r = terms.mk_implies(q, r);
    let problem = vec![p, p_implies_q, q_implies_r];
    exec.ctx.assertions = problem.clone();
    exec.last_proof = Some(trust_only_proof());
    (exec, problem, [q, r, s])
}

/// `p` and `not p`: an UNSATISFIABLE scope, over which any question the arm
/// actually asks succeeds, so only a guard can refuse one.
fn contradictory_scope() -> (Executor, Vec<TermId>, TermId) {
    let mut exec = Executor::new();
    let p = exec.ctx.terms.mk_var("entail_vacuous_p", Sort::Bool);
    let not_p = exec.ctx.terms.mk_not(p);
    let problem = vec![p, not_p];
    exec.ctx.assertions = problem.clone();
    exec.last_proof = Some(trust_only_proof());
    (exec, problem, p)
}

fn deferred(clauses: &[Vec<TermId>]) -> Vec<(ProofId, Vec<TermId>)> {
    (0u32..)
        .zip(clauses)
        .map(|(step, clause)| (ProofId(step), clause.clone()))
        .collect()
}

/// The acceptance this arm adds: a SATISFIABLE scope that entails every
/// deferred clause re-decides as entailing them. (On its own that proves
/// nothing about the verdict; step (2) supplies the rest of the proof.)
#[test]
fn a_scope_that_entails_every_deferred_clause_reconfirms() {
    let (mut exec, problem, [q, r, _]) = implication_chain();
    assert!(entails(&exec, &problem, &deferred(&[vec![q], vec![r]])));
    // A two-literal clause is asked as the disjunction it is.
    let not_q = exec.ctx.terms.mk_not(q);
    assert!(entails(&exec, &problem, &deferred(&[vec![not_q, r]])));
}

/// NEGATIVE TWIN: the first solve's claim is false. A forged proof that leans
/// on `s`, which the scope does not entail, must be refused, alone or hidden
/// among entailed clauses (the question covers every deferred clause).
#[test]
fn a_deferred_clause_the_scope_does_not_entail_is_refused() {
    let (exec, problem, [q, r, s]) = implication_chain();
    assert!(!entails(&exec, &problem, &deferred(&[vec![s]])));
    assert!(!entails(
        &exec,
        &problem,
        &deferred(&[vec![q], vec![s], vec![r]])
    ));
}

/// NEGATIVE TWIN at step (4)'s entry, with a NON-empty deferred list: over a
/// satisfiable scope, one non-entailed clause among entailed ones makes every
/// fresh arm decline. The positive case pins the contract the function's
/// documentation states: a satisfiable scope that entails its deferred
/// clauses IS answered by the `entailment` corroboration, which is evidence only
/// after step (2).
#[test]
fn step_4_refuses_a_non_entailed_clause_over_a_satisfiable_scope() {
    let (exec, problem, [q, _, s]) = implication_chain();
    assert_eq!(
        exec.fresh_executor_corroboration(
            &problem,
            &problem,
            &deferred(&[vec![q], vec![s]]),
            &exec.certification_discharge_controls(),
        ),
        None
    );
    assert_eq!(
        exec.fresh_executor_corroboration(
            &problem,
            &problem,
            &deferred(&[vec![q]]),
            &exec.certification_discharge_controls(),
        )
        .map(UnsatCorroboration::method),
        Some(CorroborationMethod::Entailment)
    );
}

/// The questions that must never be asked, each pinned over an UNSATISFIABLE
/// scope (where any asked question succeeds) so only the guard can refuse it:
/// no deferred clause (`false`), an empty clause (`true`), a disjunction that
/// folds to `true` (the clause `[false]`, two complementary units: the whole
/// problem, step (4)'s question) or to `false` (only tautologies), a
/// quantified clause, and a proof with a subproof anchor.
#[test]
fn vacuous_constant_quantified_and_anchored_questions_decline() {
    // The dangerous one: with no deferred clause the question would be
    // `G ∧ false`, which refutes even this SATISFIABLE scope.
    let (sat_exec, sat_problem, _) = implication_chain();
    assert!(!entails(&sat_exec, &sat_problem, &[]));

    let (mut exec, problem, p) = contradictory_scope();
    let not_p = exec.ctx.terms.mk_not(p);
    let falsity = exec.ctx.terms.false_term();
    let truth = exec.ctx.terms.true_term();
    let x = exec.ctx.terms.mk_var("entail_vacuous_x", Sort::Int);
    let zero = exec.ctx.terms.mk_int(0.into());
    let x_ge_0 = exec.ctx.terms.mk_ge(x, zero);
    let quantified = exec
        .ctx
        .terms
        .mk_forall(vec![("entail_vacuous_x".to_string(), Sort::Int)], x_ge_0);

    // Control: a genuine ground question succeeds.
    assert!(entails(&exec, &problem, &deferred(&[vec![p]])));

    for refused in [
        Vec::new(),
        deferred(&[Vec::new()]),
        deferred(&[vec![p], Vec::new()]),
        deferred(&[vec![falsity]]),
        deferred(&[vec![p], vec![falsity]]),
        deferred(&[vec![p], vec![not_p]]),
        deferred(&[vec![truth]]),
        deferred(&[vec![p, not_p]]),
        deferred(&[vec![quantified]]),
    ] {
        assert!(
            !entails(&exec, &problem, &refused),
            "asked a question that must be refused: {refused:?}"
        );
    }

    let mut terms = exec.ctx.terms.clone();
    for refused in [
        Vec::new(),
        vec![vec![p], Vec::new()],
        vec![vec![falsity]],
        vec![vec![p], vec![not_p]],
        vec![vec![truth]],
    ] {
        assert_eq!(negated_clause_disjunction(&mut terms, &refused), None);
    }

    let mut anchored = trust_only_proof();
    anchored.steps.push(ProofStep::Anchor {
        end_step: ProofId(0),
        variables: Vec::new(),
    });
    exec.last_proof = Some(anchored);
    assert!(!entails(&exec, &problem, &deferred(&[vec![p]])));
}

/// A clause about a constant that a quantified root mentions and no
/// quantifier-free root does is a quantifier instance in practice; step (4a)
/// leaves it to step (4) without asking. Pinned over an UNSATISFIABLE scope,
/// where the question, if asked, would succeed. A constant no root mentions
/// (a fresh symbol) does not exclude a clause, nor does one a quantifier-free
/// root also mentions.
#[test]
fn a_clause_about_a_constant_only_a_quantifier_mentions_is_left_to_step_4() {
    let (mut exec, mut problem, p) = contradictory_scope();
    let terms = &mut exec.ctx.terms;
    let c = terms.mk_var("entail_quantified_c", Sort::Int);
    let fresh = terms.mk_var("entail_fresh_d", Sort::Int);
    let x = terms.mk_var("entail_quantified_x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let five = terms.mk_int(5.into());
    let x_ge_c = terms.mk_ge(x, c);
    let universal = terms.mk_forall(vec![("entail_quantified_x".to_string(), Sort::Int)], x_ge_c);
    let instance = terms.mk_ge(zero, c);
    let about_fresh = terms.mk_ge(zero, fresh);
    let c_ge_5 = terms.mk_ge(c, five);
    problem.push(universal);
    exec.ctx.assertions = problem.clone();

    assert!(entails(&exec, &problem, &deferred(&[vec![p]])));
    assert!(!entails(&exec, &problem, &deferred(&[vec![instance]])));
    assert!(!entails(
        &exec,
        &problem,
        &deferred(&[vec![p], vec![instance]])
    ));
    assert!(entails(&exec, &problem, &deferred(&[vec![about_fresh]])));

    problem.push(c_ge_5);
    exec.ctx.assertions = problem.clone();
    assert!(entails(&exec, &problem, &deferred(&[vec![instance]])));
}

/// The question's counts: twice the first solve's round trips, conflicts and
/// assembly observations, each with its floor, step (4)'s decisions, and never
/// more conflicts than step (4)'s allowance. They read the first solve's
/// counted work, never its duration.
#[test]
fn the_question_is_counted_from_the_first_solves_work() {
    let mut exec = Executor::new();
    let floors = entailment_limits(&exec.certification_discharge_controls());
    assert_eq!(floors.max_round_trips, Some(64));
    assert_eq!(floors.max_conflicts, 10_000);
    assert_eq!(floors.max_assembly_observations, Some(4_096));
    assert_eq!(
        floors.max_decisions,
        WHOLE_PROBLEM_RECONFIRMATION_LIMITS.max_decisions
    );

    exec.last_statistics.set_int("all_lanes.round_trips", 2_600);
    exec.last_statistics.set_int("all_lanes.conflicts", 105_195);
    exec.last_statistics
        .set_int("proof_assembly.observations", 50_000);
    exec.last_statistics.time_seconds = 1.0e-6;
    let measured = entailment_limits(&exec.certification_discharge_controls());
    assert_eq!(measured.max_round_trips, Some(5_200));
    assert_eq!(measured.max_conflicts, 210_390);
    assert_eq!(measured.max_assembly_observations, Some(100_000));

    exec.last_statistics.set_int("all_lanes.conflicts", 878_316);
    exec.last_statistics.time_seconds = 1.0e6;
    let capped = entailment_limits(&exec.certification_discharge_controls());
    assert_eq!(
        capped.max_conflicts, WHOLE_PROBLEM_RECONFIRMATION_LIMITS.max_conflicts,
        "never more conflicts than step (4)'s allowance"
    );
    assert_eq!(capped.max_round_trips, measured.max_round_trips);
    assert_eq!(
        capped.max_assembly_observations,
        measured.max_assembly_observations
    );
}

/// The certification's deadline bounds the question too: with the envelope
/// already spent, a question that otherwise succeeds ends on the envelope's
/// own stop, which the funnel reports as the `Backstop` it was, never as a
/// decline of the question's own.
#[test]
fn a_spent_envelope_is_step_4as_stop() {
    let (exec, problem, p) = contradictory_scope();
    assert!(entails(&exec, &problem, &deferred(&[vec![p]])));
    exec.certification_deadline.set(Some(Instant::now()));
    let controls = exec.certification_discharge_controls();
    assert!(!exec.reconfirms_deferred_clause_entailment(
        &problem,
        &deferred(&[vec![p]]),
        &controls
    ));
    assert_eq!(controls.decline_stop(), Some(EnvelopeStop::Backstop));
}

/// An executor that has elaborated `script` and opened its public solve, as
/// the funnel finds it after a first solve.
fn elaborated(script: &str) -> Executor {
    let commands = ay_frontend::parse(script).expect("fixture parses");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("fixture elaborates");
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    exec
}

/// `a = store(b, i, v)` over 8-bit indices and values, with `fact` as the last
/// root. The clause `(= (select a i) v)` is entailed by the first root but is
/// no array tautology, so step (3) cannot discharge it.
fn read_over_write_executor(fact: &str) -> Executor {
    elaborated(&format!(
        "(set-logic QF_ABV)
         (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
         (declare-const b (Array (_ BitVec 8) (_ BitVec 8)))
         (declare-const i (_ BitVec 8))
         (declare-const j (_ BitVec 8))
         (declare-const v (_ BitVec 8))
         (assert (= a (store b i v)))
         (assert {fact})"
    ))
}

/// The first solve's proof, forged: `assume (not C)` for the LAST root, a
/// `trust` step for `C`, and the resolution of the two. Everything but the
/// trust step is strictly valid, so the deferred-trust discharge collects
/// exactly `[C]`.
fn forge_trust_refutation(exec: &mut Executor) {
    let negated_fact = *exec.ctx.assertions.last().expect("the fixture has roots");
    let fact = match exec.ctx.terms.get(negated_fact) {
        ay_core::term::TermData::Not(inner) => *inner,
        other => panic!("the fixture's last root must be a negation, got {other:?}"),
    };
    exec.last_proof = Some(Proof::from_steps(vec![
        ProofStep::Step {
            rule: AletheRule::Trust,
            clause: vec![fact],
            premises: Vec::new(),
            args: Vec::new(),
        },
        ProofStep::Assume(negated_fact),
        ProofStep::Resolution {
            clause: Vec::new(),
            pivot: fact,
            clause1: ProofId(0),
            clause2: ProofId(1),
        },
    ]));
    exec.last_checked_sat_refutation = None;
}

/// The arm publishes through the funnel and the record names it.
#[test]
fn a_context_dependent_trust_clause_publishes_through_step_4a() {
    let mut exec = read_over_write_executor("(not (= (select a i) v))");
    forge_trust_refutation(&mut exec);
    let published = exec.certify_unsat_for_publication(SolveResult::unsat(), &[]);
    assert!(
        published.is_unsat(),
        "an entailed trust clause must publish"
    );
    assert_eq!(
        exec.last_unsat_corroboration()
            .map(UnsatCorroboration::method),
        Some(CorroborationMethod::Entailment)
    );
    assert!(exec.take_unsat_certificate().is_some());
}

/// Through the funnel: `(select a j)` is not entailed to be `v` (take
/// `j != i`), so the problem is satisfiable and the forged refutation must
/// publish `unknown`, with no certificate and no corroboration record. Here
/// the forged-UNSAT guard (1) refuses first; the next test silences it.
#[test]
fn a_forged_trust_clause_over_a_satisfiable_problem_is_refused() {
    let mut exec = read_over_write_executor("(not (= (select a j) v))");
    forge_trust_refutation(&mut exec);
    let published = exec.certify_unsat_for_publication(SolveResult::unsat(), &[]);
    assert!(
        published.is_unknown(),
        "a forged trust clause must not publish"
    );
    assert!(exec.take_unsat_certificate().is_none());
    assert_eq!(exec.last_unsat_corroboration(), None);
    assert_eq!(
        exec.unknown_reason(),
        Some(UnknownReason::SelfCheckRejected)
    );
}

/// NEGATIVE TWIN through the funnel with the forged-UNSAT guard SILENT: the
/// unbounded universal keeps guard (1) from deciding `sat`, so step (4a), then
/// step (4), is what must refuse the forged `(= (select a j) v)`. (Without the
/// negation in the question, step (4a) would ask `G ∧ C` and accept.)
#[test]
fn a_forged_trust_clause_the_forged_guard_cannot_refute_is_refused_by_4a() {
    let fixture = || {
        let mut exec = elaborated(
            "(set-logic AUFLIA)
             (declare-const a (Array Int Int))
             (declare-const b (Array Int Int))
             (declare-const i Int)
             (declare-const j Int)
             (declare-const v Int)
             (declare-fun h (Int) Int)
             (assert (forall ((x Int)) (> (h (+ x 1)) (h x))))
             (assert (= a (store b i v)))
             (assert (not (= (select a j) v)))",
        );
        forge_trust_refutation(&mut exec);
        exec
    };
    match fixture().mint_unsat_certificate(&[]) {
        Err(UnsatCertificationError::StrictProofRejected { reason }) => assert!(
            reason.contains("deferred-trust discharge failed"),
            "guard (1) must stay silent here so step (4a) is exercised: {reason}"
        ),
        Err(other) => panic!("unexpected certification error: {other:?}"),
        Ok(_) => panic!("a forged trust clause minted a certificate"),
    }
    let mut exec = fixture();
    let published = exec.certify_unsat_for_publication(SolveResult::unsat(), &[]);
    assert!(
        published.is_unknown(),
        "a forged trust clause must not publish"
    );
    assert!(exec.take_unsat_certificate().is_none());
    assert_eq!(exec.last_unsat_corroboration(), None);
}

/// LIVENESS through the funnel. Over this QF_ALIA refutation's eleven deferred
/// store-chain clauses, step (4a)'s question does not end on its own (in
/// release: 98 s until killed, inside the array solver's cross-chain equality
/// propagation, far below step (4)'s conflict and decision allowances), while
/// step (4) re-decides the problem in milliseconds. The question's round-trip
/// count ends the question (on a slow host its cap, half of the envelope, may
/// end it first) and step (4) publishes. Counterfactual: give the question
/// the whole envelope and no count, and step (4) is left nothing, so the
/// command publishes `unknown`.
#[test]
fn a_question_that_does_not_end_leaves_step_4_its_time() {
    let script = "(set-logic QF_ALIA)
         (set-option :timeout 20000)
         (declare-fun a0 () (Array Int Int))
         (declare-fun b () (Array Int Int))
         (declare-fun i () Int)
         (assert (= b ((as const (Array Int Int)) 0)))
         (assert (= (store (store (store b (- i 2) i) 1 i) i i)
                    (store (store (store ((as const (Array Int Int)) 0) i (select (store a0 5 0) i))
                                  0 (select a0 i))
                           2 i)))
         (assert (not (= (select (store a0 0 2) i) 2)))
         (assert (>= i 1))
         (check-sat)";
    let commands = ay_frontend::parse(script).expect("fixture parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("fixture executes");
    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));
    assert_eq!(
        exec.last_unsat_corroboration()
            .map(UnsatCorroboration::method),
        Some(CorroborationMethod::Resolve)
    );
}

/// Step (4a) in `exec`'s own certification envelope.
fn entails(exec: &Executor, scope: &[TermId], deferred: &[(ProofId, Vec<TermId>)]) -> bool {
    exec.reconfirms_deferred_clause_entailment(
        scope,
        deferred,
        &exec.certification_discharge_controls(),
    )
}

#[path = "tests/envelope_stops.rs"]
mod envelope_stops;

#[path = "tests/counted_redecisions.rs"]
mod counted_redecisions;

#[path = "tests/unit_scope_routing.rs"]
mod unit_scope_routing;
