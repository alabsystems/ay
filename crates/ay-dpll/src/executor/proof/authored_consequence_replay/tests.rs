// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

type ReplayPlans = ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan>;

fn singleton_plan(plan: ConsequencePlan) -> ReplayPlans {
    let mut plans = ReplayPlans::default();
    plans.insert(TermId(0), plan);
    plans
}

fn forall_only_plan() -> ReplayPlans {
    singleton_plan(ConsequencePlan::ForallInstance {
        quantifier: TermId(1),
        binding: vec![TermId(2)],
    })
}

fn dual_forall_plan() -> ReplayPlans {
    let mut plans = forall_only_plan();
    plans.insert(
        TermId(3),
        ConsequencePlan::NegatedExistsDual {
            not_exists_root: TermId(4),
            exists: TermId(5),
        },
    );
    plans
}

fn negative_skolem_plan() -> ReplayPlans {
    singleton_plan(ConsequencePlan::SkolemInstance {
        source: TermId(1),
        quantified: TermId(2),
        witness: TermId(3),
        instance: TermId(4),
        positive: false,
    })
}

fn positive_skolem_plan() -> ReplayPlans {
    singleton_plan(ConsequencePlan::SkolemInstance {
        source: TermId(1),
        quantified: TermId(2),
        witness: TermId(3),
        instance: TermId(4),
        positive: true,
    })
}

#[test]
fn ordinary_and_best_effort_forall_probes_keep_two_second_budget() {
    let mut exec = Executor::new();
    let plan_shape = ConsequenceReplayPlanShape::classify(&forall_only_plan());
    assert!(!exec.strict_unsat_presentation_required());
    assert_eq!(plan_shape, ConsequenceReplayPlanShape::Standard);
    assert_eq!(plan_shape.probe_budget().milliseconds(), 2_000);

    exec.set_best_effort_produce_proofs(1);
    assert!(!exec.strict_unsat_presentation_required());
    assert_eq!(plan_shape.probe_budget().milliseconds(), 2_000);
}

#[test]
fn strict_posture_does_not_raise_forall_probe_budget() {
    let plan_shape = ConsequenceReplayPlanShape::classify(&forall_only_plan());

    let mut self_checked = Executor::new();
    self_checked.set_self_check(true);
    assert!(self_checked.strict_unsat_presentation_required());
    assert_eq!(plan_shape.probe_budget().milliseconds(), 2_000);

    let mut explicit_proof = Executor::new();
    explicit_proof.set_produce_proofs(true);
    assert!(explicit_proof.strict_unsat_presentation_required());
    assert_eq!(plan_shape.probe_budget().milliseconds(), 2_000);
}

#[test]
fn only_positive_skolem_plan_gets_extended_probe_budget() {
    let dual_shape = ConsequenceReplayPlanShape::classify(&dual_forall_plan());
    assert_eq!(
        dual_shape,
        ConsequenceReplayPlanShape::Standard,
        "a negated-exists dual is source authority, not extra probe workload"
    );
    assert_eq!(dual_shape.probe_budget().milliseconds(), 2_000);

    let negative_shape = ConsequenceReplayPlanShape::classify(&negative_skolem_plan());
    assert_eq!(negative_shape, ConsequenceReplayPlanShape::Standard);
    assert_eq!(negative_shape.probe_budget().milliseconds(), 2_000);

    let positive_shape = ConsequenceReplayPlanShape::classify(&positive_skolem_plan());
    assert_eq!(positive_shape, ConsequenceReplayPlanShape::PositiveSkolem);
    assert_eq!(positive_shape.probe_budget().milliseconds(), 5_000);
}

fn executor_with_assertions(script: &str) -> Executor {
    let commands = ay_frontend::parse(script).expect("consequence-replay fixture parses");
    let mut exec = Executor::new();
    assert!(
        exec.execute_all(&commands)
            .expect("consequence-replay fixture loads")
            .is_empty(),
        "fixture must contain declarations and assertions only"
    );
    exec
}

/// A guarded-implication universal — the exact shape the flat arithmetic
/// `forall_inst` lane's comparison pre-filter refuses — with a recorded
/// instance that conflicts with the authored ground facts.
fn guarded_conflict_executor() -> Executor {
    let mut exec = executor_with_assertions(
        r#"
                (set-logic LIA)
                (declare-const a Int)
                (assert (>= a 5))
                (assert (forall ((x Int)) (=> (>= x 0) (< x a))))
            "#,
    );
    let forall = exec.ctx.assertions[1];
    let TermData::Forall(vars, body, _) = exec.ctx.terms.get(forall).clone() else {
        panic!("fixture asserts a forall");
    };
    // The declared constant `a`, robust to comparison normalization.
    let value = match exec.ctx.terms.get(exec.ctx.assertions[0]).clone() {
        TermData::App(_, args) => args
            .iter()
            .copied()
            .find(|&arg| matches!(exec.ctx.terms.get(arg), TermData::Var(..)))
            .expect("fixture ground fact mentions the declared constant"),
        _ => panic!("fixture ground fact is a comparison"),
    };
    let mut subst: ay_core::kani_compat::DetHashMap<String, TermId> =
        ay_core::kani_compat::DetHashMap::default();
    subst.insert(vars[0].0.clone(), value);
    // The EXACT structural substitution the write chokepoints record in
    // proof mode; folding constructors would be an illegal `forall_inst`
    // conclusion.
    let instance = crate::ematching::subst_vars_exact_qf(&mut exec.ctx.terms, body, &subst)
        .expect("fixture body is quantifier-free");
    exec.ematching_proof_records
        .push(crate::executor::EmatchingProofRecord {
            assertion_index: 1,
            quantifier: forall,
            binding: vec![value],
            instance,
        });
    exec
}

#[test]
fn translates_recorded_guarded_instance_conflict_to_strict_proof() {
    let mut exec = guarded_conflict_executor();
    assert!(
        exec.try_translate_authored_consequence_replay_unsat(),
        "the recorded instance at x := a conflicts with (>= a 5) and must translate"
    );
    let proof = exec
        .last_proof
        .clone()
        .expect("translation installs last_proof");
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::ForallInst,
                ..
            }
        )),
        "the stitched proof derives the instance via forall_inst"
    );
    assert!(exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
    let authored = exec.exact_concrete_authored_scope();
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &authored).is_ok());
}

#[test]
fn attempt_budget_is_enforced() {
    // GUARD-REMOVAL PROOF (attempt budget): the identical executor
    // translates with a fresh budget (sibling test); exhausting the
    // per-check-sat probe budget must decline without touching proof
    // state. (The the consequence-replay switch kill-switch half lives in the
    // dedicated single-test binary `consequence_replay_kill_switch.rs` —
    // env mutation must never race sibling tests in a shared process.)
    let mut exec = guarded_conflict_executor();
    exec.consequence_replay_attempts.set(MAX_REPLAY_ATTEMPTS);
    assert!(
        !exec.try_translate_authored_consequence_replay_unsat(),
        "the replay attempt budget must be enforced"
    );
    assert!(exec.last_proof.is_none());
}

#[test]
fn declines_without_a_recorded_instance() {
    // GUARD-REMOVAL PROOF: a pure-ground UNSAT problem must not be
    // re-solved by this lane — no recorded instance, no probe.
    let mut exec = executor_with_assertions(
        r#"
                (set-logic LIA)
                (declare-const a Int)
                (assert (>= a 5))
                (assert (< a 0))
            "#,
    );
    assert!(
        !exec.try_translate_authored_consequence_replay_unsat(),
        "no recorded instance: the lane has nothing to add and must decline"
    );
    assert_eq!(
        exec.consequence_replay_attempts.get(),
        0,
        "a plan-less decline must not consume a probe attempt"
    );
    assert!(exec.last_proof.is_none());
}

/// A negated vacuous-binder universal whose Skolem instance contradicts an
/// authored ground fact: the smallest fixture exercising the `sko_forall`
/// chain arm end to end.
fn skolem_conflict_executor(register_witness: bool) -> Executor {
    let mut exec = executor_with_assertions(
        r#"
                (set-logic UFLIA)
                (declare-fun p (Int) Bool)
                (assert (p 7))
                (assert (not (forall ((x Int)) (p 7))))
            "#,
    );
    let source = exec.ctx.assertions[1];
    let TermData::Not(quantified) = *exec.ctx.terms.get(source) else {
        panic!("fixture asserts a negated forall");
    };
    let TermData::Forall(_, body, _) = exec.ctx.terms.get(quantified).clone() else {
        panic!("fixture wraps a forall");
    };
    let witness = exec.ctx.terms.mk_fresh_var("ay_sk_replay_test", Sort::Int);
    if register_witness {
        let TermData::Var(name, _) = exec.ctx.terms.get(witness).clone() else {
            panic!("fresh witness is a var");
        };
        exec.ctx.terms.mark_skolem_symbol(name);
    }
    let asserted = exec.ctx.terms.mk_not_raw(body);
    exec.skolem_instance_records
        .push(crate::executor::SkolemInstanceRecord {
            source,
            quantified,
            witness,
            instance: body,
            asserted,
            positive: false,
        });
    exec
}

#[test]
fn translates_recorded_skolem_instance_conflict_to_strict_proof() {
    let mut exec = skolem_conflict_executor(true);
    assert!(
        exec.try_translate_authored_consequence_replay_unsat(),
        "the negated-forall Skolem instance contradicts (p 7) and must translate"
    );
    let proof = exec
        .last_proof
        .clone()
        .expect("translation installs last_proof");
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::Skolem,
                ..
            }
        )),
        "the stitched proof derives the instance via the sko_forall chain"
    );
    assert!(exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
    let authored = exec.exact_concrete_authored_scope();
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &authored).is_ok());
}

#[test]
fn unregistered_skolem_witness_cannot_mint_a_certificate() {
    // GUARD-REMOVAL PROOF: the strict checker's Skolem-registry authority
    // is load-bearing — an identical chain over an unregistered witness
    // must be refused wholesale, leaving proof state untouched.
    let mut exec = skolem_conflict_executor(false);
    assert!(
        !exec.try_translate_authored_consequence_replay_unsat(),
        "an unregistered witness must fail the sko_forall authority check"
    );
    assert!(exec.last_proof.is_none());
}

#[test]
fn declines_a_forged_binding_that_breaks_the_substitution() {
    // The forged instance is NOT the substitution at the recorded binder
    // value; the strict forall_inst validator must refuse the stitched
    // candidate, and nothing may install.
    let mut exec = executor_with_assertions(
        r#"
                (set-logic LIA)
                (declare-const a Int)
                (assert (>= a 5))
                (assert (forall ((x Int)) (=> (>= x 0) (< x a))))
            "#,
    );
    let forall = exec.ctx.assertions[1];
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let false_term = exec.ctx.terms.false_term();
    exec.ematching_proof_records
        .push(crate::executor::EmatchingProofRecord {
            assertion_index: 1,
            quantifier: forall,
            binding: vec![zero],
            instance: false_term,
        });
    assert!(
        !exec.try_translate_authored_consequence_replay_unsat(),
        "a forged instance term must be refused by the strict replay"
    );
    assert!(exec.last_proof.is_none());
}

#[test]
fn satisfiable_consequences_cannot_mint_a_certificate() {
    // The recorded instance is consistent with the ground facts: the probe
    // finds no refutation and the producer must decline.
    let mut exec = executor_with_assertions(
        r#"
                (set-logic LIA)
                (declare-const a Int)
                (assert (>= a 5))
                (assert (forall ((x Int)) (=> (>= x 0) (<= 0 (+ x a)))))
            "#,
    );
    let forall = exec.ctx.assertions[1];
    let TermData::Forall(vars, body, _) = exec.ctx.terms.get(forall).clone() else {
        panic!("fixture asserts a forall");
    };
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let mut subst: ay_core::kani_compat::DetHashMap<String, TermId> =
        ay_core::kani_compat::DetHashMap::default();
    subst.insert(vars[0].0.clone(), zero);
    let instance = crate::ematching::subst_vars(&mut exec.ctx.terms, body, &subst);
    exec.ematching_proof_records
        .push(crate::executor::EmatchingProofRecord {
            assertion_index: 1,
            quantifier: forall,
            binding: vec![zero],
            instance,
        });
    assert!(
        !exec.try_translate_authored_consequence_replay_unsat(),
        "a satisfiable consequence set must never mint a refutation"
    );
    assert!(exec.last_proof.is_none());
}
