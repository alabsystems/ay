// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{AletheRule, Proof, ProofStep, Symbol};
use ay_frontend::command::{Command, Term as Parsed};

fn marker() -> Parsed {
    Parsed::Symbol(crate::executor::NATIVE_API_ASSERTION_PLACEHOLDER.into())
}

fn begin(exec: &mut Executor) {
    exec.begin_external_decision_query(false);
    exec.bind_unsat_query_assumptions(&[]);
}

fn fixture() -> (Executor, TermId) {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let x = exec.ctx.terms.mk_var("lineage_x", Sort::Bool);
    let root = exec
        .ctx
        .terms
        .mk_forall(vec![("lineage_x".into(), Sort::Bool)], x);
    exec.ctx.add_native_assertion_with_parsed(root, marker());
    begin(&mut exec);
    (exec, root)
}

fn source(exec: &Executor) -> NativeUniversalSource {
    NativeUniversalSource::capture(exec).expect("positive native original scope")
}

#[test]
fn native_universal_lineage_exact_source_and_append_only_growth() {
    let (mut exec, root) = fixture();
    let receipt = source(&exec);
    assert!(receipt.admits(&exec, root));
    let _ = exec.ctx.terms.mk_fresh_var("derived_only", Sort::Int);
    assert!(receipt.is_current(&exec));
    let target = exec.ctx.terms.false_term();
    let original_assertions = exec.ctx.assertions.clone();
    assert!(exec
        .derive_native_universal_target(&receipt, root, &[target], target)
        .is_some());
    assert_eq!(
        exec.ctx.assertions, original_assertions,
        "lineage adds proof steps, never ambient facts"
    );
    let mut proof = exec.proof_tracker.take_proof();
    let proved_false = proof
        .steps
        .iter()
        .rposition(|step| {
            matches!(step,
        ProofStep::Resolution { clause, .. } if clause == &[target])
        })
        .unwrap();
    let not_false = exec.ctx.terms.mk_not_raw(target);
    let axiom = proof.add_rule_step(AletheRule::False, vec![not_false], Vec::new(), Vec::new());
    proof.add_resolution(
        Vec::new(),
        target,
        ay_core::ProofId(proved_false as u32),
        axiom,
    );
    assert!(exec
        .check_proof_strict_with_datatypes(&proof)
        .unwrap()
        .is_complete());
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::ForallInst,
            ..
        }
    )));
}

#[test]
fn native_universal_lineage_owner_epoch_context_pop_and_root_inventory_revoke() {
    for change in 0..5 {
        let (mut exec, root) = fixture();
        let receipt = source(&exec);
        match change {
            0 => begin(&mut exec),
            1 => {
                exec.execute_all(&ay_frontend::parse("(push 1)(pop 1)").unwrap())
                    .unwrap();
            }
            2 => {
                exec.execute_all(&ay_frontend::parse("(declare-const later Int)").unwrap())
                    .unwrap();
            }
            3 => {
                exec.proof_problem_assertion_provenance
                    .as_mut()
                    .unwrap()
                    .original_problem_assertions
                    .clear();
            }
            _ => {
                exec.ctx = exec.ctx.clone();
            }
        }
        assert!(!receipt.is_current(&exec), "change {change}");
        assert!(!receipt.admits(&exec, root));
    }
    let (exec, root) = fixture();
    let receipt = source(&exec);
    let (other, same_id) = fixture();
    assert_eq!(root, same_id);
    assert!(
        !receipt.admits(&other, same_id),
        "same integer ID is not ownership"
    );
}

#[test]
fn native_universal_lineage_rollbacks_and_checker_metadata_revoke() {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let checkpoint = exec.ctx.terms.rollback_checkpoint();
    let x = exec.ctx.terms.mk_var("lineage_reused", Sort::Bool);
    let root = exec
        .ctx
        .terms
        .mk_forall(vec![("lineage_reused".into(), Sort::Bool)], x);
    exec.ctx.add_native_assertion_with_parsed(root, marker());
    begin(&mut exec);
    let receipt = source(&exec);
    exec.ctx.terms.rollback_to(checkpoint);
    let x = exec.ctx.terms.mk_var("lineage_reused", Sort::Bool);
    let replacement = exec
        .ctx
        .terms
        .mk_forall(vec![("lineage_reused".into(), Sort::Bool)], x);
    assert_eq!(replacement, root);
    assert!(!receipt.is_current(&exec));
    let (mut exec, _) = fixture();
    let receipt = source(&exec);
    exec.ctx.terms.mark_to_real_shadowed();
    assert!(!receipt.is_current(&exec));
    assert!(
        NativeUniversalSource::capture(&exec).is_some(),
        "a fresh same-query plan rechecks actual current metadata"
    );
}

#[test]
fn native_universal_lineage_text_mixed_and_marker_spoof_never_mint() {
    for mode in 0..3 {
        let (mut exec, root) = fixture();
        if mode == 0 {
            exec = Executor::new();
            exec.execute_all(&ay_frontend::parse("(assert (forall ((x Bool)) x))").unwrap())
                .unwrap();
        } else if mode == 1 {
            exec.execute_all(&ay_frontend::parse("(assert true)").unwrap())
                .unwrap();
        } else {
            exec = Executor::new();
            let x = exec.ctx.terms.mk_var("lineage_x", Sort::Bool);
            let fake = exec
                .ctx
                .terms
                .mk_forall(vec![("lineage_x".into(), Sort::Bool)], x);
            assert_eq!(root, fake);
            exec.ctx.add_assertion_with_parsed(fake, marker());
        }
        begin(&mut exec);
        assert!(
            NativeUniversalSource::capture(&exec).is_none(),
            "mode {mode}"
        );
    }
}

#[test]
fn native_universal_lineage_rejects_nonoriginal_root_wrong_sort_and_false_fold() {
    let (mut exec, root) = fixture();
    let receipt = source(&exec);
    let foreign = exec.ctx.terms.mk_forall(
        vec![("other".into(), Sort::Bool)],
        exec.ctx.terms.true_term(),
    );
    assert!(!receipt.admits(&exec, foreign));
    let zero = exec.ctx.terms.mk_int(0.into());
    assert!(exec
        .native_universal_instance(&receipt, root, &[zero])
        .is_none());
    let before = exec.proof_tracker.num_steps();
    let truth = exec.ctx.terms.true_term();
    let falsity = exec.ctx.terms.false_term();
    assert!(exec
        .derive_native_universal_target(&receipt, root, &[truth], falsity)
        .is_none());
    assert_eq!(
        exec.proof_tracker.num_steps(),
        before,
        "rejected Boolean candidate is not indexed"
    );
}

#[test]
fn native_universal_lineage_full_guard_cannot_be_erased_into_an_unconditional_fact() {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    exec.execute_all(
        &ay_frontend::parse("(declare-fun guard (Int) Bool) (declare-fun consequence (Int) Bool)")
            .unwrap(),
    )
    .unwrap();
    let root = native_text(
        &mut exec,
        "(forall ((x Int)) (=> (guard x) (consequence x)))",
    );
    begin(&mut exec);
    let receipt = source(&exec);
    let value = exec.ctx.terms.mk_int(0.into());
    let target = exec
        .ctx
        .terms
        .mk_app(Symbol::named("consequence"), [value], Sort::Bool);
    let before = exec.proof_tracker.num_steps();
    assert!(exec
        .derive_native_universal_target(&receipt, root, &[value], target)
        .is_none());
    assert_eq!(exec.proof_tracker.num_steps(), before);
}

#[test]
fn native_universal_lineage_multi_binder_values_are_positional_and_sort_exact() {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let flag = exec.ctx.terms.mk_var("flag", Sort::Bool);
    let value = exec.ctx.terms.mk_var("value", Sort::Int);
    let body = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [value, value], Sort::Bool);
    let root = exec.ctx.terms.mk_forall_with_triggers(
        vec![("flag".into(), Sort::Bool), ("value".into(), Sort::Int)],
        body,
        vec![vec![flag, value]],
    );
    exec.ctx.add_native_assertion_with_parsed(root, marker());
    begin(&mut exec);
    let receipt = source(&exec);
    let truth = exec.ctx.terms.true_term();
    let zero = exec.ctx.terms.mk_int(0.into());
    let exact = exec
        .native_universal_instance(&receipt, root, &[truth, zero])
        .unwrap();
    assert!(exec
        .derive_native_universal_target(&receipt, root, &[truth, zero], exact)
        .is_some());
    assert!(exec
        .native_universal_instance(&receipt, root, &[zero, truth])
        .is_none());
    assert!(exec
        .native_universal_instance(&receipt, root, &[truth])
        .is_none());
}

#[test]
fn native_universal_lineage_witness_records_need_exact_source_typed_metadata_and_derivation() {
    for changed in 0..4 {
        let mut exec = Executor::new();
        let x = exec.ctx.terms.mk_var("witness_x", Sort::Bool);
        let q = exec
            .ctx
            .terms
            .mk_forall(vec![("witness_x".into(), Sort::Bool)], x);
        let original = exec.ctx.terms.mk_not_raw(q);
        let w = exec.ctx.terms.mk_var("sk!lineage_witness", Sort::Bool);
        if changed != 1 {
            exec.ctx.terms.mark_skolem_symbol("sk!lineage_witness");
        }
        let target = exec.ctx.terms.mk_not_raw(w);
        exec.ctx
            .add_native_assertion_with_parsed(original, marker());
        if changed == 3 {
            let raw_pin = exec
                .ctx
                .terms
                .mk_app(Symbol::named("="), [w, w], Sort::Bool);
            exec.ctx.add_native_assertion_with_parsed(raw_pin, marker());
        }
        let record = crate::executor::SkolemInstanceRecord {
            source: original,
            quantified: q,
            witness: w,
            instance: if changed == 2 {
                exec.ctx.terms.true_term()
            } else {
                w
            },
            asserted: target,
            positive: false,
        };
        begin(&mut exec);
        // Preprocessing records are query-local and begin_public_solve clears
        // the previous query's ledger. Install this fixture at its real stage.
        exec.skolem_instance_records.push(record);
        let receipt = std::sync::Arc::new(source(&exec));
        let accepted = exec.native_universal_witnesses(&receipt).unwrap();
        assert_eq!(
            accepted.len(),
            usize::from(changed == 0),
            "change {changed}"
        );
    }
}

#[test]
fn native_universal_lineage_preexisting_witness_never_refutes_the_original_sat_problem() {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let x = exec.ctx.terms.mk_var("original_bound", Sort::Bool);
    let q = exec
        .ctx
        .terms
        .mk_forall(vec![("original_bound".into(), Sort::Bool)], x);
    let not_q = exec.ctx.terms.mk_not_raw(q);
    let w = exec.ctx.terms.mk_var("preexisting_w", Sort::Bool);
    let not_w = exec.ctx.terms.mk_not_raw(w);
    exec.ctx.add_native_assertion_with_parsed(not_q, marker());
    exec.ctx.add_native_assertion_with_parsed(w, marker());
    // Simulate a forged retained producer record. Registering metadata cannot
    // make an existing original symbol fresh, even with an exact substitution.
    exec.ctx.terms.mark_skolem_symbol("preexisting_w");
    begin(&mut exec);
    exec.skolem_instance_records
        .push(crate::executor::SkolemInstanceRecord {
            source: not_q,
            quantified: q,
            witness: w,
            instance: w,
            asserted: not_w,
            positive: false,
        });
    let receipt = std::sync::Arc::new(source(&exec));
    assert!(exec
        .native_universal_witnesses(&receipt)
        .unwrap()
        .is_empty());

    // The complete attempted refutation is locally well-formed. Its false
    // credit would be exactly the non-fresh choice, which the independent
    // checker must reject against BOTH original roots before any publication.
    let mut proof = Proof::new();
    let source_id = proof.add_assume(not_q, None);
    let equality = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [q, w], Sort::Bool);
    let skolem = proof.add_rule_step(AletheRule::Skolem, vec![equality], vec![], vec![w]);
    let not_equality = exec.ctx.terms.mk_not_raw(equality);
    let equiv = proof.add_rule_step(
        AletheRule::EquivPos1,
        vec![not_equality, q, not_w],
        vec![],
        vec![],
    );
    let implication = proof.add_resolution(vec![q, not_w], equality, skolem, equiv);
    let false_unit = proof.add_resolution(vec![not_w], q, source_id, implication);
    let original_positive = proof.add_assume(w, None);
    proof.add_resolution(vec![], w, original_positive, false_unit);
    let error = ay_proof::check_proof_strict_with_context(
        &proof,
        &exec.ctx.terms,
        None,
        None,
        Some(receipt.roots()),
    )
    .expect_err("a pre-existing symbol cannot be a new Skolem choice");
    assert!(format!("{error:?}").contains("not fresh"), "{error:?}");

    // This is SAT, not merely an input for which a forged proof was declined.
    // Keep the actual native/API and event-DAG replay consumers strong.
    use crate::api::{Logic, NativeReplayMetadata, Solver};
    let mut solver = Solver::try_new(Logic::All).unwrap();
    solver.set_produce_proofs(true);
    let x = solver.try_fresh_var("original_bound", Sort::Bool).unwrap();
    let w = solver
        .try_declare_const("preexisting_w", Sort::Bool)
        .unwrap();
    let q = solver.try_forall(&[x], x).unwrap();
    let not_q = solver.try_not(q).unwrap();
    solver.try_assert_term(not_q).unwrap();
    solver.try_assert_term(w).unwrap();
    let input = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    assert_eq!(input.assertions.len(), 2);
    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_sat() && details.result.was_model_validated(),
        "{details:?}"
    );
    assert!(details.accept_for_consumer().is_ok(), "{details:?}");
    let replay = Solver::replay_native_replay_artifact(&input).unwrap();
    assert!(
        replay.result.is_sat() && replay.result.was_model_validated(),
        "{replay:?}"
    );
    assert!(replay.accept_for_consumer().is_ok(), "{replay:?}");
}

#[test]
fn native_universal_lineage_general_typed_binders_and_trigger_preservation() {
    for sort in [
        Sort::Bool,
        Sort::Int,
        Sort::Real,
        Sort::bitvec(8),
        Sort::Uninterpreted("LineageCarrier".into()),
        Sort::seq(Sort::Int),
        Sort::array(Sort::Int, Sort::Bool),
    ] {
        let mut exec = Executor::new();
        exec.set_produce_proofs(true);
        exec.execute_all(&ay_frontend::parse("(declare-sort LineageCarrier 0)").unwrap())
            .unwrap();
        let bound = exec.ctx.terms.mk_var("typed_bound", sort.clone());
        let body = exec.ctx.terms.mk_fresh_var("typed_body", Sort::Bool);
        let root = exec.ctx.terms.mk_forall_with_triggers(
            vec![("typed_bound".into(), sort.clone())],
            body,
            vec![vec![bound]],
        );
        exec.ctx.add_native_assertion_with_parsed(root, marker());
        begin(&mut exec);
        let receipt = source(&exec);
        let value = exec.ctx.terms.mk_fresh_var("typed_value", sort);
        assert_eq!(
            exec.native_universal_instance(&receipt, root, &[value]),
            Some(body)
        );
        assert!(exec
            .derive_native_universal_target(&receipt, root, &[value], body)
            .is_some());
        assert!(
            matches!(exec.ctx.terms.get(root), TermData::Forall(_, _, triggers) if triggers == &vec![vec![bound]])
        );
    }
}

#[test]
fn native_universal_lineage_nested_capture_and_duplicate_binders_decline() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_var("outer_x", Sort::Bool);
    let y = exec.ctx.terms.mk_var("inner_y", Sort::Bool);
    let body = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [x, y], Sort::Bool);
    let inner = exec
        .ctx
        .terms
        .mk_forall(vec![("inner_y".into(), Sort::Bool)], body);
    let outer = exec
        .ctx
        .terms
        .mk_forall(vec![("outer_x".into(), Sort::Bool)], inner);
    exec.ctx.add_native_assertion_with_parsed(outer, marker());
    begin(&mut exec);
    let receipt = source(&exec);
    assert!(exec
        .native_universal_instance(&receipt, outer, &[y])
        .is_none());
    let duplicate = exec
        .ctx
        .terms
        .mk_forall(vec![("x".into(), Sort::Bool), ("x".into(), Sort::Bool)], x);
    exec.ctx
        .add_native_assertion_with_parsed(duplicate, marker());
    begin(&mut exec);
    assert!(NativeUniversalSource::capture(&exec).is_none());
}

#[test]
fn native_universal_lineage_binder_annotations_cannot_retype_occurrences() {
    let mut exec = Executor::new();
    let boolean_x = exec.ctx.terms.mk_var("typed_x", Sort::Bool);
    let malformed = exec
        .ctx
        .terms
        .mk_forall(vec![("typed_x".into(), Sort::Int)], boolean_x);
    exec.ctx
        .add_native_assertion_with_parsed(malformed, marker());
    begin(&mut exec);
    assert!(NativeUniversalSource::capture(&exec).is_none());
    let mut exec = Executor::new();
    let boolean_x = exec.ctx.terms.mk_var("typed_x", Sort::Bool);
    let inner = exec
        .ctx
        .terms
        .mk_forall(vec![("typed_x".into(), Sort::Bool)], boolean_x);
    let outer = exec
        .ctx
        .terms
        .mk_forall(vec![("typed_x".into(), Sort::Int)], inner);
    exec.ctx.add_native_assertion_with_parsed(outer, marker());
    begin(&mut exec);
    assert!(
        NativeUniversalSource::capture(&exec).is_some(),
        "nearest actual binder wins"
    );
}

#[test]
fn native_universal_lineage_budget_and_cancel_are_shared_sticky_and_pre_copy() {
    let (mut exec, root) = fixture();
    let receipt = source(&exec);
    assert!(exec.charge_native_universal(usize::MAX, 0).is_none());
    assert!(exec.charge_native_universal(0, 0).is_none());
    assert!(!receipt.is_current(&exec));
    assert!(NativeUniversalSource::capture(&exec).is_none());
    begin(&mut exec);
    let receipt = source(&exec);
    let stop = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(true));
    exec.set_interrupt(stop.clone());
    assert!(!receipt.admits(&exec, root));
    stop.store(false, std::sync::atomic::Ordering::SeqCst);
    assert!(
        !receipt.is_current(&exec),
        "clearing cancel cannot replenish this query owner"
    );
}

#[test]
fn native_universal_lineage_original_deadline_cannot_be_cleared_to_renew_owner() {
    let (mut exec, _) = fixture();
    let receipt = source(&exec);
    exec.set_deadline(Some(ay_core::time::Instant::now()));
    assert!(!receipt.is_current(&exec));
    exec.set_deadline(None);
    assert!(!receipt.is_current(&exec));
    assert!(NativeUniversalSource::capture(&exec).is_none());
}

#[test]
fn native_universal_lineage_oversized_and_dangling_inputs_decline_before_substitution() {
    let (mut exec, root) = fixture();
    let receipt = source(&exec);
    let large = exec.ctx.terms.mk_fresh_var(&"x".repeat(4097), Sort::Bool);
    assert!(exec
        .native_universal_instance(&receipt, root, &[large])
        .is_none());
    assert!(exec
        .native_universal_instance(&receipt, root, &[TermId(u32::MAX)])
        .is_none());
    let repeated = exec
        .ctx
        .terms
        .mk_app(Symbol::named("and"), vec![large; 100_000], Sort::Bool);
    assert!(exec.admit_native_universal_terms(&[repeated]).is_none());
}

#[test]
fn native_universal_lineage_raw_literal_kind_sort_width_and_rational_denominator_are_checked() {
    use ay_core::term::{Constant, RationalWrapper};
    use num_rational::BigRational;
    let cases = [
        (Constant::Bool(false), Sort::Int, false),
        (Constant::Int(1.into()), Sort::Real, false),
        (
            Constant::BitVec {
                value: 1.into(),
                width: 8,
            },
            Sort::bitvec(16),
            false,
        ),
        (
            Constant::BitVec {
                value: (-1).into(),
                width: 8,
            },
            Sort::bitvec(8),
            false,
        ),
        (
            Constant::BitVec {
                value: 256.into(),
                width: 8,
            },
            Sort::bitvec(8),
            false,
        ),
        (
            Constant::BitVec {
                value: 0.into(),
                width: 0,
            },
            Sort::bitvec(0),
            false,
        ),
        (
            Constant::Rational(RationalWrapper(BigRational::new_raw(1.into(), 0.into()))),
            Sort::Real,
            false,
        ),
        (
            Constant::Rational(RationalWrapper(BigRational::new_raw(1.into(), (-2).into()))),
            Sort::Real,
            false,
        ),
        (
            Constant::Rational(RationalWrapper(BigRational::new_raw(1.into(), 2.into()))),
            Sort::Int,
            false,
        ),
        (Constant::Bool(false), Sort::Bool, true),
        (Constant::Int((-1).into()), Sort::Int, true),
        (
            Constant::BitVec {
                value: 255.into(),
                width: 8,
            },
            Sort::bitvec(8),
            true,
        ),
        (
            Constant::Rational(RationalWrapper(BigRational::new_raw((-1).into(), 2.into()))),
            Sort::Real,
            true,
        ),
        (
            Constant::Rational(RationalWrapper(BigRational::new_raw(2.into(), 4.into()))),
            Sort::Real,
            true,
        ),
    ];
    for (literal, sort, expected) in cases {
        let mut exec = Executor::new();
        // No normal producer may be called on this checker-only store. The
        // admission itself is borrowed; malformed payloads must decline here.
        exec.ctx.terms = ay_core::TermStore::from_entries(
            vec![
                (TermData::Const(Constant::Bool(false)), Sort::Bool),
                (TermData::Const(Constant::Bool(true)), Sort::Bool),
                (TermData::Const(literal), sort),
            ],
            Some(TermId(1)),
            Some(TermId(0)),
            0,
        );
        begin(&mut exec);
        assert_eq!(
            exec.admit_native_universal_terms(&[TermId(2)]).is_some(),
            expected
        );
    }
}

fn native_text(exec: &mut Executor, text: &str) -> TermId {
    let commands = ay_frontend::parse(&format!("(assert {text})")).unwrap();
    let Command::Assert(surface) = &commands[0] else {
        panic!("assert")
    };
    let root = exec.ctx.elaborate_surface_subterm(surface).unwrap();
    exec.ctx.add_native_assertion_with_parsed(root, marker());
    root
}

#[test]
fn native_universal_lineage_registered_nominal_seeds_do_not_inhabit_opaque_domains() {
    let mut exec = Executor::new();
    exec.execute_all(
        &ay_frontend::parse("(declare-sort Opaque 0) (declare-datatype Unit ((unit)))").unwrap(),
    )
    .unwrap();
    let mut values = Vec::new();
    begin(&mut exec);
    exec.seed_native_universal_values(&Sort::Uninterpreted("Opaque".into()), &mut values)
        .unwrap();
    assert!(values.is_empty());
    exec.seed_native_universal_values(&Sort::Uninterpreted("Unit".into()), &mut values)
        .unwrap();
    assert_eq!(values.len(), 1);
    let registered = exec
        .ctx
        .exact_datatype_member_info("unit")
        .unwrap()
        .term
        .unwrap();
    assert_eq!(
        values[0], registered,
        "seed custody is the exact live declaration handle"
    );
    assert!(matches!(exec.ctx.terms.get(values[0]), TermData::Var(name, _) if name == "unit"));
}

#[test]
fn native_universal_lineage_original_closed_terms_seed_opaque_carriers_without_membership() {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    exec.execute_all(
        &ay_frontend::parse(
            "(declare-sort Carrier 0) (declare-const original_value Carrier) \
         (declare-fun guarded (Carrier Carrier) Bool)",
        )
        .unwrap(),
    )
    .unwrap();
    let root = native_text(
        &mut exec,
        "(forall ((x Carrier)) (=> (guarded x original_value) false))",
    );
    let TermData::Forall(_, body, _) = exec.ctx.terms.get(root) else {
        panic!("forall")
    };
    let body = *body;
    begin(&mut exec);
    let receipt = source(&exec);
    let before = exec.proof_tracker.num_steps();
    let assertions = exec.ctx.assertions.clone();
    let mut values = Vec::new();
    exec.seed_native_universal_values(&Sort::Uninterpreted("Carrier".into()), &mut values)
        .unwrap();
    assert!(values.is_empty(), "opaque sort alone contributes no seed");
    exec.seed_native_universal_source_values(
        &receipt,
        &Sort::Uninterpreted("Carrier".into()),
        &mut values,
    )
    .unwrap();
    assert_eq!(values.len(), 1);
    assert!(
        matches!(exec.ctx.terms.get(values[0]), TermData::Var(name, _) if name == "original_value")
    );
    assert_eq!(
        exec.proof_tracker.num_steps(),
        before,
        "a proposed value proves no member fact"
    );
    assert_eq!(exec.ctx.assertions, assertions);
    let exact = exec
        .native_universal_instance(&receipt, root, &values)
        .unwrap();
    assert_ne!(exact, body, "the actual bound occurrence is substituted");
    assert!(
        exec.derive_native_universal_target(&receipt, root, &values, exec.ctx.terms.false_term())
            .is_none(),
        "the original guard cannot be erased"
    );
    assert_eq!(exec.proof_tracker.num_steps(), before);
}

#[test]
fn native_universal_lineage_closed_source_walk_borrows_long_nested_scope_prefixes() {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    exec.execute_all(
        &ay_frontend::parse(
            "(declare-sort Carrier 0) (declare-const closed_value Carrier) \
         (declare-fun nested_pair (Carrier Carrier) Bool)",
        )
        .unwrap(),
    )
    .unwrap();
    let ty = Sort::Uninterpreted("Carrier".into());
    let closed = exec
        .ctx
        .elaborate_surface_subterm(&Parsed::Symbol("closed_value".into()))
        .unwrap();
    let name =
        |level, index| format!("long_native_scope_{level:02}_{index:02}_abcdefghijklmnopqrstuvwx");
    let bound = exec.ctx.terms.mk_var(name(59, 0), ty.clone());
    let mut root = exec
        .ctx
        .terms
        .mk_app(Symbol::named("nested_pair"), [bound, closed], Sort::Bool);
    // The physical source still fits the original 4096/depth64/payload
    // admission. Owned copies of all 60 enclosing prefixes would be a much
    // larger allocation than the source's single set of names.
    for level in (0..60).rev() {
        let bindings = (0..16)
            .map(|index| (name(level, index), ty.clone()))
            .collect();
        root = exec.ctx.terms.mk_forall(bindings, root);
    }
    exec.ctx.add_native_assertion_with_parsed(root, marker());
    begin(&mut exec);
    let receipt = source(&exec);
    let assertions = exec.ctx.assertions.clone();
    let mut values = Vec::new();
    exec.seed_native_universal_source_values(&receipt, &ty, &mut values)
        .unwrap();
    assert_eq!(
        values,
        [closed],
        "no bound value is an original closed candidate"
    );
    assert_eq!(exec.proof_tracker.num_steps(), 0);
    assert_eq!(exec.ctx.assertions, assertions);
    assert!(exec.charge_native_universal(32 * 1024 * 1024, 0).is_none());
    assert!(exec
        .seed_native_universal_source_values(&receipt, &ty, &mut values)
        .is_none());
}

#[test]
fn native_universal_lineage_closed_source_walk_distinguishes_shared_bound_and_free_occurrences() {
    for free_occurrence in [false, true] {
        let mut exec = Executor::new();
        exec.set_produce_proofs(true);
        let ty = Sort::Uninterpreted("Carrier".into());
        let bound = exec.ctx.terms.mk_var("same_source_var", ty.clone());
        let body = exec
            .ctx
            .terms
            .mk_app(Symbol::named("source_pred"), [bound], Sort::Bool);
        let root = exec
            .ctx
            .terms
            .mk_forall(vec![("same_source_var".into(), ty.clone())], body);
        exec.ctx.add_native_assertion_with_parsed(root, marker());
        if free_occurrence {
            // Same exact node, but its second original occurrence has no
            // enclosing binder. A TermId-only groundness memo is insufficient.
            exec.ctx.add_native_assertion_with_parsed(body, marker());
        }
        begin(&mut exec);
        let receipt = source(&exec);
        let mut values = Vec::new();
        exec.seed_native_universal_source_values(&receipt, &ty, &mut values)
            .unwrap();
        assert_eq!(values.contains(&bound), free_occurrence);
        assert_eq!(
            exec.proof_tracker.num_steps(),
            0,
            "proposals add no assumptions"
        );
    }
}

#[test]
fn native_universal_lineage_actual_guarded_native_quantifier_consumers() {
    for (decls, roots) in [
        (
            "(declare-fun member (Bool) Bool)",
            vec![
                "(forall ((x Bool)) (= (member x) true))",
                "(forall ((x Bool)) (=> (member x) false))",
            ],
        ),
        (
            "(declare-fun member (Bool) Bool)",
            vec![
                "(forall ((x Bool)) (= (member x) true))",
                "(not (forall ((x Bool)) (=> (member x) (ite x x (not x)))))",
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
            "(declare-datatype Unit ((unit))) (declare-fun member (Unit) Bool)",
            vec![
                "(forall ((x Unit)) (= (member x) true))",
                "(forall ((x Unit)) (=> (member x) false))",
            ],
        ),
    ] {
        let mut exec = Executor::new();
        exec.execute_all(&ay_frontend::parse(&format!("(set-logic ALL) (set-option :produce-proofs true) (set-option :check-proofs-strict true) {decls}")).unwrap()).unwrap();
        let original: Vec<_> = roots
            .iter()
            .map(|root| native_text(&mut exec, root))
            .collect();
        let result = exec
            .execute_all(&ay_frontend::parse("(check-sat)").unwrap())
            .unwrap();
        assert_eq!(result, vec!["unsat"], "{roots:?}");
        let proof = exec
            .last_proof
            .as_ref()
            .expect("a checked proof is mandatory");
        assert!(exec
            .check_proof_strict_with_datatypes(proof)
            .unwrap()
            .is_complete());
        ay_proof::validate_reachable_assumes_in_problem_scope(proof, &original).unwrap();
    }
}

mod external;
