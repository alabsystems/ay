// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::ProofStep;
use ay_frontend::command::Term as Parsed;

fn begin(exec: &mut Executor) {
    exec.begin_external_decision_query(false);
    exec.bind_unsat_query_assumptions(&[]);
}

fn native(exec: &mut Executor, text: &str) -> TermId {
    let ay_frontend::command::Command::Assert(parsed) =
        ay_frontend::parse(&format!("(assert {text})"))
            .unwrap()
            .remove(0)
    else {
        panic!("an assertion")
    };
    let term = exec.ctx.elaborate_surface_subterm(&parsed).unwrap();
    exec.ctx.add_native_assertion_with_parsed(
        term,
        Parsed::Symbol(crate::executor::NATIVE_API_ASSERTION_PLACEHOLDER.into()),
    );
    term
}

fn setup(decls: &str, roots: &[&str]) -> (Executor, Vec<TermId>) {
    let mut exec = Executor::new();
    exec.execute_all(&ay_frontend::parse(&format!("(set-logic ALL) (set-option :produce-proofs true) (set-option :check-proofs-strict true) {decls}")).unwrap()).unwrap();
    let original = roots.iter().map(|s| native(&mut exec, s)).collect();
    (exec, original)
}

#[test]
fn native_source_offers_exact_choice_and_guard_are_checked_before_working_replacement() {
    let (mut exec, original) = setup(
        "(declare-fun member (Bool) Bool)",
        &[
            "(forall ((x Bool)) (= (member x) false))",
            "(not (forall ((x Bool)) (=> (member x) false)))",
        ],
    );
    begin(&mut exec);
    exec.offer_native_quantified_source_units()
        .expect("source-owned offers");
    assert!(!exec.ctx.assertions.contains(&original[1]));
    assert_eq!(exec.skolem_instance_records.len(), 1);
    let record = exec.skolem_instance_records[0].clone();
    assert_eq!(record.source, original[1]);
    assert!(exec.ctx.assertions.contains(&record.asserted));
    let proof = exec.proof_tracker.take_proof();
    let checked = ay_proof::authenticate_premise_clauses_strict_with_context(
        &proof,
        &exec.ctx.terms,
        None,
        None,
        &original,
    )
    .unwrap();
    assert!(proof
        .steps
        .iter()
        .enumerate()
        .any(|(i, _)| checked.clause(ProofId(i as u32)) == Some(&[record.asserted][..])));
    assert!(proof.steps.iter().any(|s| matches!(
        s,
        ProofStep::Step {
            rule: AletheRule::Skolem,
            ..
        }
    )));
    assert!(proof.steps.iter().all(|s| !matches!(s,
        ProofStep::Assume(root) if !original.contains(root))));
    // The same external attempt cannot mint a second incompatible choice.
    let steps = proof.steps.len();
    assert!(exec.offer_native_quantified_source_units().is_none());
    assert_eq!(exec.skolem_instance_records.len(), 1);
    assert_eq!(
        exec.proof_tracker.num_steps(),
        0,
        "proof was explicitly taken above, never rebuilt on refusal"
    );
    assert!(steps > 0);
}

#[test]
fn native_source_offers_negative_exists_retains_the_exact_dual_and_source() {
    let (mut exec, original) = setup("(declare-sort MaybeEmpty 0) (declare-const original_value MaybeEmpty) (declare-fun member (MaybeEmpty) Bool)", &[
        "(forall ((x MaybeEmpty)) (= (member x) true))",
        "(not (exists ((x MaybeEmpty)) (member x)))",
        "(member original_value)",
    ]);
    begin(&mut exec);
    exec.offer_native_quantified_source_units().unwrap();
    let proof = exec.proof_tracker.take_proof();
    ay_proof::authenticate_premise_clauses_strict_with_context(
        &proof,
        &exec.ctx.terms,
        None,
        None,
        &original,
    )
    .unwrap();
    assert!(proof.steps.iter().any(|s| matches!(
        s,
        ProofStep::Step {
            rule: AletheRule::QntNegExists,
            ..
        }
    )));
    assert!(proof.steps.iter().any(|s| matches!(
        s,
        ProofStep::Step {
            rule: AletheRule::ForallInst,
            ..
        }
    )));
    assert!(
        exec.skolem_instance_records.is_empty(),
        "a universal point offer is not an existential witness"
    );
}

#[test]
fn native_source_offers_both_polarities_bool_ite_empty_and_unit_require_complete_refutations() {
    let _diagnostic =
        ay_core::misc_test_override::set(ay_core::debug_channel::misc_cli_flags_with(|flags| {
            flags.debug_cert = true
        }));
    let cases = [
        (
            "(declare-fun member (Bool) Bool)",
            vec![
                "(forall ((x Bool)) (= (member x) true))",
                "(not (forall ((x Bool)) (=> (member x) (ite x x (not x)))))",
            ],
        ),
        (
            "(declare-fun member (Bool) Bool)",
            vec![
                "(forall ((x Bool)) (= (member x) true))",
                "(not (exists ((x Bool)) (and (member x) (ite x x (not x)))))",
            ],
        ),
        (
            "(declare-sort Empty 0) (declare-fun member (Empty) Bool)",
            vec![
                "(forall ((x Empty)) (= (member x) false))",
                "(not (forall ((x Empty)) (=> (member x) false)))",
            ],
        ),
        (
            "(declare-sort Empty 0) (declare-fun member (Empty) Bool)",
            vec![
                "(forall ((x Empty)) (= (member x) false))",
                "(exists ((x Empty)) (member x))",
            ],
        ),
        (
            "(declare-datatype Unit ((unit))) (declare-fun member (Unit) Bool)",
            vec![
                "(forall ((x Unit)) (= (member x) true))",
                "(forall ((x Unit)) (=> (member x) false))",
            ],
        ),
        (
            "(declare-datatype Unit ((unit))) (declare-fun member (Unit) Bool)",
            vec![
                "(forall ((x Unit)) (= (member x) true))",
                "(not (exists ((x Unit)) (member x)))",
            ],
        ),
    ];
    let mut failures = Vec::new();
    for (decls, roots) in cases {
        let (mut exec, original) = setup(decls, &roots);
        let result = exec
            .execute_all(&ay_frontend::parse("(check-sat)").unwrap())
            .unwrap();
        if result != ["unsat"] {
            failures.push(format!(
                "{roots:?}: {result:?}, reason={:?}, surface={:?}, statistics={:?}",
                exec.last_unknown_reason,
                exec.last_proof_surface_withheld,
                exec.last_statistics.extra
            ));
            continue;
        }
        let proof = exec
            .last_proof
            .as_ref()
            .expect("strict refutation is mandatory");
        assert!(
            exec.check_proof_strict_with_datatypes(proof)
                .unwrap()
                .is_complete(),
            "{roots:?}"
        );
        ay_proof::validate_reachable_assumes_in_problem_scope(proof, &original).unwrap();
        if decls.starts_with("(declare-datatype Unit") && roots[1].starts_with("(not (exists") {
            let (document, problem, surface) = exec
                .try_export_last_unsat_datatype_pair()
                .expect("the proof-only unit constructor is declared in the exact problem");
            assert!(surface.is_supported());
            crate::api::check_paired_document_for_test(&problem, &document);
            // The paired encoder also canonicalizes datatype tester spellings.
            // Hold that exact scope and spelling fixed for both negative cases.
            let scope = exec.proof_export_scope_assertions_for(proof).unwrap();
            let overrides = exec
                .datatype_problem_spelling_overrides(exec.last_proof_term_overrides.as_ref())
                .unwrap();
            let (_, mut declared) = exec
                .alethe_datatype_problem_with_constructors(&scope, Some(&overrides))
                .unwrap();
            assert!(declared.remove("unit").is_some());
            let missing = ay_proof::try_export_alethe_with_paired_datatype_constructors(
                proof,
                &exec.ctx.terms,
                &scope,
                Some(&overrides),
                &declared,
                None,
            );
            assert!(matches!(
                missing,
                Err(ay_proof::AlethePrintError::UndeclarableProofSymbols { .. })
            ));
            declared.insert("unit", original[0]); // a Boolean premise cannot authorize this Unit constant
            let forged = ay_proof::try_export_alethe_with_paired_datatype_constructors(
                proof,
                &exec.ctx.terms,
                &scope,
                Some(&overrides),
                &declared,
                None,
            );
            assert!(matches!(
                forged,
                Err(ay_proof::AlethePrintError::UndeclarableProofSymbols { .. })
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "all six original refutations remain required:\n{}",
        failures.join("\n")
    );
}

#[test]
fn native_source_offers_sat_twins_remain_validated_under_full_original_scope() {
    let _diagnostic =
        ay_core::misc_test_override::set(ay_core::debug_channel::misc_cli_flags_with(|flags| {
            flags.debug_cert = true
        }));
    let cases = [
        (
            "(declare-fun member (Bool) Bool)",
            vec![
                "(forall ((x Bool)) (= (member x) true))",
                "(not (forall ((x Bool)) (=> (member x) x)))",
            ],
        ),
        (
            "(declare-fun member (Bool) Bool)",
            vec![
                "(forall ((x Bool)) (= (member x) true))",
                "(exists ((x Bool)) (and (member x) (ite x x (not x))))",
            ],
        ),
        (
            "(declare-sort Empty 0) (declare-fun member (Empty) Bool)",
            vec![
                "(forall ((x Empty)) (= (member x) false))",
                "(forall ((x Empty)) (=> (member x) false))",
            ],
        ),
        (
            "(declare-sort Empty 0) (declare-fun member (Empty) Bool)",
            vec![
                "(forall ((x Empty)) (= (member x) false))",
                "(not (exists ((x Empty)) (member x)))",
            ],
        ),
        (
            "(declare-datatype Unit ((unit))) (declare-fun member (Unit) Bool)",
            vec![
                "(forall ((x Unit)) (= (member x) true))",
                "(forall ((x Unit)) (=> (member x) true))",
            ],
        ),
        (
            "(declare-datatype Unit ((unit))) (declare-fun member (Unit) Bool)",
            vec![
                "(forall ((x Unit)) (= (member x) true))",
                "(exists ((x Unit)) (member x))",
            ],
        ),
    ];
    let mut failures = Vec::new();
    for (decls, roots) in cases {
        let (mut exec, _) = setup(decls, &roots);
        let result = exec
            .execute_all(&ay_frontend::parse("(check-sat)").unwrap())
            .unwrap();
        if result != ["sat"] {
            failures.push(format!(
                "{roots:?}: {result:?}, reason={:?}, statistics={:?}",
                exec.last_unknown_reason, exec.last_statistics.extra
            ));
            continue;
        }
        assert!(
            exec.last_model.is_some(),
            "an actual full-original model must be retained: {roots:?}"
        );
    }
    assert!(
        failures.is_empty(),
        "all six original validated SAT twins remain required:\n{}",
        failures.join("\n")
    );
}

#[test]
fn native_source_offers_refuses_foreign_text_and_failed_original_owner_without_ambient_facts() {
    for mode in 0..3 {
        let (mut exec, _) = setup("", &["(not (forall ((x Bool)) x))"]);
        if mode == 0 {
            exec.execute_all(&ay_frontend::parse("(assert true)").unwrap())
                .unwrap();
        }
        begin(&mut exec);
        if mode == 1 {
            exec.native_universal_budget
                .borrow_mut()
                .charge(usize::MAX, 0, false);
        }
        if mode == 2 {
            exec.ctx = exec.ctx.clone();
        }
        let before = exec.ctx.assertions.clone();
        let metadata = exec.ctx.terms.checker_visible_metadata_generation();
        assert!(
            exec.offer_native_quantified_source_units().is_none(),
            "mode {mode}"
        );
        assert_eq!(exec.ctx.assertions, before);
        assert_eq!(
            exec.ctx.terms.checker_visible_metadata_generation(),
            metadata
        );
        assert_eq!(exec.proof_tracker.num_steps(), 0);
    }
}

#[test]
fn native_source_offers_negative_choice_metadata_matches_existing_replay_without_folding_raw_instance(
) {
    let (mut exec, original) = setup("", &["(not (forall ((x Bool)) (not x)))"]);
    begin(&mut exec);
    exec.offer_native_quantified_source_units().unwrap();
    let record = &exec.skolem_instance_records[0];
    let TermData::Forall(_, body, _) = exec.ctx.terms.get(record.quantified) else {
        panic!("forall")
    };
    let TermData::Not(bound) = exec.ctx.terms.get(*body) else {
        panic!("negative source body")
    };
    assert_eq!(
        exec.ctx.terms.skolem_choice(record.witness).unwrap().body,
        *bound
    );
    assert!(
        matches!(exec.ctx.terms.get(record.instance), TermData::Not(inner) if *inner==record.witness)
    );
    assert_eq!(record.asserted, record.witness);
    let proof = exec.proof_tracker.take_proof();
    ay_proof::authenticate_premise_clauses_strict_with_context(
        &proof,
        &exec.ctx.terms,
        None,
        None,
        &original,
    )
    .unwrap();
}
