// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const FALSE_REAL: &str = "(forall ((q Real)) (and (> (+ q q) q) (fp.isNaN (_ NaN 11 53))))";

fn fixture(declarations: &str, formula: &str) -> Executor {
    let mut exec = Executor::new();
    let script =
        format!("(set-logic ALL)(set-option :produce-proofs true){declarations}(assert {formula})");
    exec.execute_all(&ay_frontend::parse(&script).unwrap())
        .unwrap();
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    exec
}

fn assert_checked(exec: &Executor, authored: &[TermId]) {
    assert_eq!(exec.consequence_replay_attempts.get(), 0, "no solver probe");
    let proof = exec.last_proof.as_ref().expect("checked proof installed");
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
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(proof, authored).is_ok());
    assert!(Executor::proof_derives_empty_clause(proof));
    assert!(exec
        .check_proof_strict_with_datatypes(proof)
        .unwrap()
        .is_complete());
}

fn scan_body(exec: &Executor, root: TermId, vars: &[(String, Sort)]) -> Option<Option<bool>> {
    let mut remaining = MAX_AND_PATH_WORK;
    exec.closed_fp_zero_body(root, vars, &mut remaining)
}

#[test]
fn real_zero_instance_completes_without_ground_probe() {
    let mut exec = fixture("", FALSE_REAL);
    let authored = exec.exact_concrete_authored_scope();
    assert_eq!(
        exec.ematching_proof_records,
        [] as [crate::executor::query_state::EmatchingProofRecord; 0]
    );
    assert!(exec.last_model.is_none());
    assert!(exec.try_translate_closed_fp_forall_zero_unsat());
    assert_checked(&exec, &authored);
    assert_eq!(
        exec.ctx.assertions, authored,
        "no search assertion was added"
    );
}

#[test]
fn positive_and_sources_and_zero_tuples_keep_original_scope() {
    let source = "(and keep (forall ((r Real) (i Int))
        (and (> (+ r r) r) (> (+ i i) i) (fp.isNaN (_ NaN 11 53)))))";
    let mut exec = fixture("(declare-const keep Bool)", source);
    let authored = exec.exact_concrete_authored_scope();
    assert!(matches!(exec.ctx.terms.get(authored[0]),
        TermData::App(Symbol::Named(name), _) if name == "and"));
    assert!(exec.try_translate_closed_fp_forall_zero_unsat());
    assert_checked(&exec, &authored);
    assert!(exec
        .last_proof
        .as_ref()
        .unwrap()
        .steps
        .iter()
        .any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::AndPos(_),
                ..
            }
        )));
}

#[test]
fn trigger_metadata_does_not_block_checked_zero_instantiation() {
    let source = "(forall ((q Real)) (!
        (and (> (+ q q) q) (fp.isNaN (_ NaN 11 53)))
        :pattern ((+ q q))))";
    let mut exec = fixture("", source);
    let authored = exec.exact_concrete_authored_scope();
    assert!(matches!(exec.ctx.terms.get(authored[0]),
        TermData::Forall(_, _, triggers) if !triggers.is_empty()));
    assert!(exec.try_translate_closed_fp_forall_zero_unsat());
    assert_checked(&exec, &authored);
}

#[test]
fn rounded_fp_operation_is_checked_after_a_true_arithmetic_conjunct() {
    let source = "(forall ((q Real)) (and (>= (+ q q) q)
        (not (fp.eq (fp.add RNE (_ +zero 11 53) (_ +zero 11 53)) (_ +zero 11 53)))))";
    let mut exec = fixture("", source);
    let authored = exec.exact_concrete_authored_scope();
    assert!(exec.try_translate_closed_fp_forall_zero_unsat());
    assert_checked(&exec, &authored);
}

#[test]
fn nonconjunctive_residual_and_ematching_only_sources_are_not_hints() {
    for (declarations, source) in [
        (
            "(declare-const keep Bool)",
            format!("(or keep {FALSE_REAL})"),
        ),
        (
            "(declare-fun f (Real) Real)",
            "(forall ((q Real)) (and (> (f q) q) (fp.isNaN (_ NaN 11 53))))".into(),
        ),
        (
            "(declare-const free Real)",
            "(forall ((q Real)) (and (> (+ q free) q) (fp.isNaN (_ NaN 11 53))))".into(),
        ),
    ] {
        let mut exec = fixture(declarations, &source);
        assert!(!exec.try_translate_closed_fp_forall_zero_unsat());
        assert!(exec.last_proof.is_none());
        assert_eq!(exec.consequence_replay_attempts.get(), 0);
    }
    let mut exec = fixture("", FALSE_REAL);
    exec.ctx.terms.mark_no_mbqi(exec.ctx.assertions[0]);
    assert!(!exec.try_translate_closed_fp_forall_zero_unsat());
    assert!(exec.consequence_replay_direct_state.get().is_none());
}

#[test]
fn true_zero_instance_and_shared_attempt_limit_preserve_proof_state() {
    let source = "(forall ((q Real))
        (and (>= (+ q q) q) (fp.isNaN (_ NaN 11 53))))";
    let mut exec = fixture("", source);
    assert!(!exec.try_translate_closed_fp_forall_zero_unsat());
    let first = exec.consequence_replay_direct_state.get();
    assert!(first.is_some());
    assert!(!exec.try_translate_closed_fp_forall_zero_unsat());
    assert_eq!(exec.consequence_replay_direct_state.get(), first);
    assert_eq!(exec.consequence_replay_attempts.get(), 0);
    assert!(exec.last_proof.is_none());

    let mut exec = fixture("", FALSE_REAL);
    exec.consequence_replay_direct_state
        .set(Some((0, MAX_DIRECT_REPLAY_ATTEMPTS)));
    let terms = exec.ctx.terms.len();
    assert!(!exec.try_translate_closed_fp_forall_zero_unsat());
    assert_eq!(exec.ctx.terms.len(), terms);
    assert!(exec.last_proof.is_none());
}

#[test]
fn stopped_stale_or_unbound_source_epochs_cannot_complete() {
    let mut exec = fixture("", FALSE_REAL);
    assert!(exec.try_translate_closed_fp_forall_zero_unsat());
    let steps = exec.last_proof.as_ref().unwrap().steps.clone();
    exec.set_interrupt(std::sync::Arc::new(std::sync::atomic::AtomicBool::new(
        true,
    )));
    let terms = exec.ctx.terms.len();
    assert!(!exec.try_translate_closed_fp_forall_zero_unsat());
    assert_eq!(exec.ctx.terms.len(), terms);
    assert_eq!(exec.last_proof.as_ref().unwrap().steps, steps);

    let mut exec = fixture("", FALSE_REAL);
    exec.ctx
        .process_command(&ay_frontend::parse("(declare-const later Bool)").unwrap()[0])
        .unwrap();
    assert!(!exec.try_translate_closed_fp_forall_zero_unsat());
    assert!(exec.last_proof.is_none());

    let mut exec = fixture("", FALSE_REAL);
    exec.begin_public_solve(false);
    assert!(
        !exec.try_translate_closed_fp_forall_zero_unsat(),
        "assumptions not bound"
    );
    assert!(exec.last_proof.is_none());

    let mut exec = fixture("", FALSE_REAL);
    exec.proof_problem_assertion_provenance
        .as_mut()
        .unwrap()
        .original_problem_assertions
        .clear();
    assert!(!exec.try_translate_closed_fp_forall_zero_unsat());
    assert!(exec.last_proof.is_none());

    let mut exec = fixture("(declare-const assumption Bool)", FALSE_REAL);
    let assumption = exec.ctx.symbol_info("assumption").unwrap().term.unwrap();
    exec.bind_unsat_query_assumptions(&[assumption]);
    exec.last_assumptions = Some(vec![assumption]);
    assert!(!exec.try_translate_closed_fp_forall_zero_unsat());
    assert!(exec.last_proof.is_none());
}

#[test]
fn borrowed_source_census_bounds_depth_payload_and_shared_expansion() {
    let mut exec = fixture("", FALSE_REAL);
    let TermData::Forall(vars, body, _) = exec.ctx.terms.get(exec.ctx.assertions[0]).clone() else {
        panic!("universal fixture");
    };
    assert_eq!(scan_body(&exec, body, &vars), Some(Some(true)));
    let mut deep = body;
    for _ in 0..=ground_pin::MAX_INSTANCE_DEPTH {
        deep = exec.ctx.terms.mk_not_raw(deep);
    }
    assert_eq!(scan_body(&exec, deep, &vars), None);

    let mut shared = body;
    for _ in 0..12 {
        shared = exec
            .ctx
            .terms
            .mk_app(Symbol::named("and"), [shared, shared], Sort::Bool);
    }
    assert_eq!(scan_body(&exec, shared, &vars), None);

    let huge = exec
        .ctx
        .terms
        .mk_int(BigInt::from(1) << (MAX_AND_PATH_WORK * 8));
    assert_eq!(scan_body(&exec, huge, &vars), None);
    let indexed = exec.ctx.terms.mk_app(
        Symbol::indexed("NaN", vec![0; MAX_AND_PATH_WORK + 1]),
        [],
        Sort::FloatingPoint(11, 53),
    );
    assert_eq!(scan_body(&exec, indexed, &vars), None);
    let many = vec![exec.ctx.assertions[0]; MAX_AND_PATH_WORK + 1];
    let mut remaining = MAX_AND_PATH_WORK;
    assert!(exec.closed_fp_zero_sources(&many, &mut remaining).is_none());
    let large_trigger = exec.ctx.terms.mk_forall_with_triggers(
        vars.clone(),
        body,
        vec![vec![body; MAX_AND_PATH_WORK + 1]],
    );
    let mut remaining = MAX_AND_PATH_WORK;
    assert!(exec
        .closed_fp_zero_sources(&[large_trigger], &mut remaining)
        .is_none());
    let duplicate_binders = exec
        .ctx
        .terms
        .mk_forall(vec![vars[0].clone(), vars[0].clone()], body);
    let mut remaining = MAX_AND_PATH_WORK;
    assert!(exec
        .closed_fp_zero_sources(&[duplicate_binders], &mut remaining)
        .is_none());
}

#[test]
fn disabled_completion_spends_no_attempt_and_installs_no_proof() {
    let _guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_consequence_replay: true,
        ..Default::default()
    });
    let mut exec = fixture("", FALSE_REAL);
    let terms = exec.ctx.terms.len();
    assert!(!exec.try_translate_closed_fp_forall_zero_unsat());
    assert_eq!(exec.ctx.terms.len(), terms);
    assert!(exec.last_proof.is_none());
    assert!(exec.consequence_replay_direct_state.get().is_none());
    assert_eq!(exec.consequence_replay_attempts.get(), 0);
}

#[test]
fn borrowed_source_census_rejects_wrong_variable_and_opaque_sorts() {
    let mut exec = fixture("", FALSE_REAL);
    let wrong = exec.ctx.terms.mk_var("q", Sort::Int);
    let vars = vec![("q".to_owned(), Sort::Real)];
    assert_eq!(scan_body(&exec, wrong, &vars), Some(None));
    let array = exec
        .ctx
        .terms
        .mk_var("array", Sort::array(Sort::Int, Sort::Int));
    assert_eq!(scan_body(&exec, array, &vars), Some(None));
}
