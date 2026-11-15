// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

type Plans = ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan>;

const FORALL: &str = "(forall ((q (_ BitVec 64))) (fp.isNaN (fp \
    ((_ extract 63 63) q) ((_ extract 62 52) q) ((_ extract 51 0) q))))";

fn exact_instance(exec: &mut Executor, forall: TermId, binding: &[TermId]) -> TermId {
    let TermData::Forall(vars, body, _) = exec.ctx.terms.get(forall).clone() else {
        panic!("fixture has one universal");
    };
    assert_eq!(vars.len(), binding.len());
    let subst = vars
        .iter()
        .zip(binding)
        .map(|((name, _), &value)| (name.clone(), value))
        .collect();
    crate::ematching::subst_vars_exact_qf(&mut exec.ctx.terms, body, &subst).unwrap()
}

fn fixture() -> (Executor, crate::ematching::ForallInstantiationProvenance) {
    let mut exec = Executor::new();
    let script = format!("(set-logic BVFP)(set-option :produce-proofs true)(assert {FORALL})");
    exec.execute_all(&ay_frontend::parse(&script).unwrap())
        .unwrap();
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    let quantifier = exec.ctx.assertions[0];
    let zero = exec.ctx.terms.mk_bitvec(0.into(), 64);
    let instance = exact_instance(&mut exec, quantifier, &[zero]);
    (
        exec,
        crate::ematching::ForallInstantiationProvenance {
            quantifier,
            binding: vec![zero],
            instance,
        },
    )
}

fn plan(record: &crate::ematching::ForallInstantiationProvenance) -> Plans {
    let mut plans = Plans::default();
    plans.insert(
        record.instance,
        ConsequencePlan::ForallInstance {
            quantifier: record.quantifier,
            binding: record.binding.clone(),
        },
    );
    plans
}

#[test]
fn exact_fp_instance_installs_a_complete_authored_proof_without_pins_or_probe() {
    let (mut exec, record) = fixture();
    assert!(exec.try_translate_authored_consequence_replay_unsat_with(&[record]));
    assert_eq!(exec.consequence_replay_attempts.get(), 0);
    let proof = exec.last_proof.as_ref().unwrap();
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::ForallInst,
            ..
        }
    )));
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::FpGroundEval,
            ..
        }
    )));
    assert!(ay_proof::terminal_trust_report(proof).is_trust_free());
    assert!(exec
        .check_proof_strict_with_datatypes(proof)
        .unwrap()
        .is_complete());
    let authored = exec.exact_concrete_authored_scope();
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(proof, &authored).is_ok());
    assert!(Executor::proof_derives_empty_clause(proof));
}

#[test]
fn fp_instance_with_forged_witness_is_rejected_by_exact_substitution() {
    let (mut exec, mut record) = fixture();
    // The instance is still isNaN(+zero), but the alleged witness is a NaN.
    record.binding[0] = exec
        .ctx
        .terms
        .mk_bitvec(0x7ff8_0000_0000_0000_u64.into(), 64);
    let authored = exec.exact_concrete_authored_scope();
    let candidate = exec
        .build_fp_instance_refutation(&authored, &plan(&record), record.instance)
        .expect("the untrusted producer can propose a bad substitution");
    assert!(exec.check_proof_strict_with_datatypes(&candidate).is_err());
    assert!(!exec.ground_pin_candidate_is_strict(&candidate, &authored));
    assert!(exec.last_proof.is_none());
}

#[test]
fn a_true_fp_instance_cannot_supply_the_refutation_lemma() {
    let (mut exec, mut record) = fixture();
    record.binding[0] = exec
        .ctx
        .terms
        .mk_bitvec(0x7ff8_0000_0000_0000_u64.into(), 64);
    record.instance = exact_instance(&mut exec, record.quantifier, &record.binding);
    let authored = exec.exact_concrete_authored_scope();
    assert!(exec
        .build_fp_instance_refutation(&authored, &plan(&record), record.instance)
        .is_none());
}

#[test]
fn fp_instance_cannot_assume_an_unauthored_universal() {
    let (mut exec, record) = fixture();
    let unrelated = exec.ctx.terms.mk_var("unrelated", Sort::Bool);
    assert!(exec
        .build_fp_instance_refutation(&[unrelated], &plan(&record), record.instance)
        .is_none());
}

#[test]
fn fp_instance_uses_the_existing_direct_attempt_budget() {
    let (mut exec, record) = fixture();
    exec.consequence_replay_direct_state
        .set(Some((0, MAX_DIRECT_REPLAY_ATTEMPTS)));
    assert!(exec
        .try_distinct_ground_pin(&plan(&record), &[record.instance])
        .is_none());
    assert!(exec.last_proof.is_none());
}

#[test]
fn corrupted_fp_lemma_cannot_close_the_authored_proof() {
    let (mut exec, record) = fixture();
    let authored = exec.exact_concrete_authored_scope();
    let mut candidate = exec
        .build_fp_instance_refutation(&authored, &plan(&record), record.instance)
        .unwrap();
    for step in &mut candidate.steps {
        if let ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::FpGroundEval,
            clause,
            ..
        } = step
        {
            *clause = vec![record.instance];
        }
    }
    assert!(exec.check_proof_strict_with_datatypes(&candidate).is_err());
}

#[test]
fn fp_shortcut_refuses_residual_variables_and_oversized_terms() {
    let (mut exec, record) = fixture();
    let TermData::Forall(_, body, _) = exec.ctx.terms.get(record.quantifier) else {
        panic!("fixture has one universal");
    };
    assert!(!closed_fp_instance(&exec.ctx.terms, *body));
    let mut oversized = record.instance;
    for _ in 0..MAX_CLOSED_FP_NODES {
        oversized = exec.ctx.terms.mk_not_raw(oversized);
    }
    assert!(!closed_fp_instance(&exec.ctx.terms, oversized));
    assert!(closed_fp_instance(&exec.ctx.terms, record.instance));
}

#[test]
fn fp_shortcut_refuses_non_boolean_instance_hints() {
    let (mut exec, record) = fixture();
    let fp = exec.ctx.terms.mk_app(
        Symbol::indexed("+zero", vec![11, 53]),
        [],
        Sort::FloatingPoint(11, 53),
    );
    let authored = exec.exact_concrete_authored_scope();
    assert!(exec
        .build_fp_instance_refutation(&authored, &plan(&record), fp)
        .is_none());
}

#[test]
fn cancelled_fp_attempt_preserves_the_existing_proof() {
    let (mut exec, record) = fixture();
    let authored = exec.exact_concrete_authored_scope();
    let candidate = exec
        .build_fp_instance_refutation(&authored, &plan(&record), record.instance)
        .unwrap();
    let steps = candidate.steps.clone();
    exec.last_proof = Some(candidate);
    exec.set_interrupt(std::sync::Arc::new(std::sync::atomic::AtomicBool::new(
        true,
    )));
    assert!(exec
        .build_fp_instance_refutation(&authored, &plan(&record), record.instance)
        .is_none());
    assert_eq!(exec.last_proof.as_ref().unwrap().steps, steps);
}
