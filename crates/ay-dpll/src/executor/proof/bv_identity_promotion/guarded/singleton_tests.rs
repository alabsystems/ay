// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Search-path tests, not R35 CLI timing or consumer acceptance receipts.

#![cfg(test)]

use super::*;
use ay_core::{Constant, TermData, TermStore};
use std::cell::{Cell, RefCell};
use std::sync::{atomic::AtomicBool, Arc};

mod rem_digits;

const REM_RANGE: &str = include_str!("singleton_tests/rem_in_range.smt2");

#[derive(Default, Debug)]
struct Trace {
    skipped: Vec<TermId>,
    replayed: Vec<TermId>,
    joints: Vec<Vec<TermId>>,
}

thread_local! {
    static TRACE: RefCell<Option<Trace>> = const { RefCell::new(None) };
}

pub(super) fn skipped(root: TermId) {
    TRACE.with_borrow_mut(|trace| {
        if let Some(trace) = trace {
            trace.skipped.push(root);
        }
    });
}

pub(super) fn replayed(root: TermId) {
    TRACE.with_borrow_mut(|trace| {
        if let Some(trace) = trace {
            trace.replayed.push(root);
        }
    });
}

pub(super) fn joint(roots: &[TermId]) {
    TRACE.with_borrow_mut(|trace| {
        if let Some(trace) = trace {
            trace.joints.push(roots.to_vec());
        }
    });
}

fn observed<T>(run: impl FnOnce() -> T) -> (T, Trace) {
    struct Restore;
    impl Drop for Restore {
        fn drop(&mut self) {
            TRACE.with_borrow_mut(|trace| *trace = None);
        }
    }
    TRACE.with_borrow_mut(|trace| {
        assert!(trace.is_none());
        *trace = Some(Trace::default());
    });
    let _restore = Restore;
    let result = run();
    let trace = TRACE.with_borrow_mut(|trace| trace.take().expect("active observation"));
    (result, trace)
}

fn fixture(script: &str) -> Executor {
    let mut executor = Executor::new();
    for command in ay_frontend::parse(script).expect("original source") {
        assert!(!matches!(command, ay_frontend::Command::CheckSat));
        executor.execute(&command).expect("declarations and roots");
    }
    executor
}

fn root(executor: &mut Executor, index: usize) -> TermId {
    let surface = source::expand(&executor.ctx, &executor.ctx.assertions_parsed()[index])
        .expect("bounded original source");
    executor
        .raw_intern_ground_bv_surface(&surface)
        .expect("raw authenticated root")
}

fn rejected() -> Proof {
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    proof
}

fn prune(executor: &mut Executor) -> (bool, Proof, Trace) {
    let mut proof = rejected();
    let (accepted, trace) =
        observed(|| executor.promote_bv_guarded_collapse(&mut proof, GuardedCollapseStage::Final));
    (accepted, proof, trace)
}

fn assert_strict(executor: &mut Executor, proof: &Proof) {
    assert!(executor
        .check_proof_strict_with_datatypes(proof)
        .is_ok_and(|quality| quality.is_complete()));
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(
        proof,
        &executor.proof_export_scope_assertions()
    )
    .is_ok());
}

#[test]
fn actual_guarded_route_skips_exact_original_64_bit_remainder_ssa_singleton() {
    use sha2::{Digest, Sha256};
    assert_eq!(REM_RANGE.len(), 2487);
    assert_eq!(
        format!("{:x}", Sha256::digest(REM_RANGE)),
        "75f08f158e3386cc1b88a5c1342ce719ce7f7c8c2fa6ecde273e85029658d5b5"
    );
    // Select the unchanged fifth assertion from the full original, retaining
    // every declaration. This tests singleton planning, NOT the full query.
    let mut executor = Executor::new();
    let mut assertion = 0;
    for command in ay_frontend::parse(REM_RANGE).expect("byte-identical R35 source") {
        match &command {
            ay_frontend::Command::CheckSat => continue,
            ay_frontend::Command::Assert(_) => {
                assertion += 1;
                if assertion != 5 {
                    continue;
                }
            }
            _ => {}
        }
        executor
            .execute(&command)
            .expect("original declaration or selected root");
    }
    let expected = root(&mut executor, 0);
    let (accepted, proof, trace) = prune(&mut executor);
    assert!(!accepted, "a satisfiable definition is not a refutation");
    assert_eq!(trace.skipped, [expected], "{trace:?}");
    assert!(
        trace.replayed.is_empty() && trace.joints.is_empty(),
        "{trace:?}"
    );
    assert_eq!(
        format!("{:?}", proof.steps),
        format!("{:?}", rejected().steps)
    );
}

#[test]
fn renamed_division_and_boolean_definitions_skip_before_singleton_strict_replay() {
    for assertion in [
        "(= renamed (bvudiv input #x000000000000000a))",
        "(= renamed (ite flag (bvurem input #x00000000000f4243) old))",
        "(= flag (bvule (bvurem input #x000000000000000a) #x0000000000000009))",
    ] {
        let mut executor = fixture(&format!(
            "(declare-const renamed (_ BitVec 64)) (declare-const input (_ BitVec 64))
             (declare-const old (_ BitVec 64)) (declare-const flag Bool)
             (assert {assertion})"
        ));
        let expected = root(&mut executor, 0);
        let (accepted, _, trace) = prune(&mut executor);
        assert!(!accepted);
        assert_eq!(trace.skipped, [expected], "{assertion}: {trace:?}");
        assert!(
            trace.replayed.is_empty() && trace.joints.is_empty(),
            "{trace:?}"
        );
    }
}

#[test]
fn skipped_roots_remain_ordered_in_joint_strict_refutation() {
    let mut executor = fixture(
        "(declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8))
         (assert (= y (bvudiv x #x0a))) (assert (= x #x00)) (assert (= y #x01))",
    );
    let expected: Vec<_> = (0..3).map(|index| root(&mut executor, index)).collect();
    let (accepted, proof, trace) = prune(&mut executor);
    assert!(
        accepted,
        "the complete conjunction is contradictory: {trace:?}"
    );
    assert_eq!(trace.skipped, expected);
    assert!(trace.replayed.is_empty(), "{trace:?}");
    assert_eq!(trace.joints, [expected.clone()]);
    let assumptions: Vec<_> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Assume(term) => Some(*term),
            _ => None,
        })
        .collect();
    assert_eq!(assumptions, expected);
    assert_strict(&mut executor, &proof);
}

#[test]
fn contradictory_nondefinition_retains_cheap_or_strict_acceptance() {
    let mut executor = fixture("(declare-const x (_ BitVec 8)) (assert (= x (bvadd x #x01)))");
    let expected = root(&mut executor, 0);
    let (accepted, proof, trace) = prune(&mut executor);
    assert!(
        accepted,
        "the occurs-check must not prune this contradiction"
    );
    assert!(trace.skipped.is_empty());
    assert!(trace.replayed.iter().all(|root| *root == expected));
    assert_strict(&mut executor, &proof);
}

#[test]
fn unsupported_comparison_keeps_actual_singleton_replay() {
    let mut executor = fixture(
        "(declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8)) (assert (bvult x y))",
    );
    let expected = root(&mut executor, 0);
    let (accepted, _, trace) = prune(&mut executor);
    assert!(!accepted);
    assert!(trace.skipped.is_empty());
    assert_eq!(trace.replayed, [expected]);
}

#[test]
fn cancelled_guarded_pass_never_turns_advice_into_acceptance() {
    let mut executor = fixture(
        "(declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8))
         (assert (= x (bvurem y #x0a)))",
    );
    executor.set_solve_controls(Some(Arc::new(AtomicBool::new(true))), None);
    let (accepted, proof, trace) = prune(&mut executor);
    assert!(!accepted);
    assert!(trace.skipped.is_empty());
    assert_eq!(
        format!("{:?}", proof.steps),
        format!("{:?}", rejected().steps)
    );
}

#[test]
fn continuation_refuses_shadowed_unsupported_and_malformed_roots() {
    let mut executor = fixture(
        "(declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8))
         (assert (= x (bvurem y #x0a)))",
    );
    let original = root(&mut executor, 0);
    let x = executor.ctx.terms.find_var("x").expect("source x");
    executor
        .ctx
        .register_symbol("bvurem".into(), x, Sort::bitvec(8));
    assert!(!SingletonSearch::default().may_skip(
        original,
        &[original],
        &executor.ctx,
        &executor.proof_source_work,
        &|| false
    ));
    let mut unsupported = fixture(
        "(declare-const x (Array (_ BitVec 8) (_ BitVec 8)))
         (declare-const y (Array (_ BitVec 8) (_ BitVec 8))) (assert (= x y))",
    );
    let array_root = root(&mut unsupported, 0);
    assert!(!SingletonSearch::default().may_skip(
        array_root,
        &[array_root],
        &unsupported.ctx,
        &unsupported.proof_source_work,
        &|| false
    ));
    let mut malformed =
        fixture("(declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8)) (assert (= x y))");
    let x = malformed.ctx.terms.find_var("x").expect("source x");
    let mut entries = malformed.ctx.terms.entries_snapshot();
    let value = TermId(u32::try_from(entries.len()).expect("small fixture"));
    entries.push((
        TermData::Const(Constant::BitVec {
            value: 256.into(),
            width: 8,
        }),
        Sort::bitvec(8),
    ));
    let bad = TermId(u32::try_from(entries.len()).expect("small fixture"));
    entries.push((
        TermData::App(Symbol::named("="), vec![x, value]),
        Sort::Bool,
    ));
    malformed.ctx.terms =
        TermStore::from_entries(entries, None, None, malformed.ctx.terms.var_counter());
    assert!(!SingletonSearch::default().may_skip(
        bad,
        &[bad],
        &malformed.ctx,
        &malformed.proof_source_work,
        &|| false
    ));
}

#[test]
fn continuation_retains_original_refusal_and_work_across_context_mutation() {
    let mut executor = fixture(
        "(declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8))
         (assert (= x (bvurem y #x0a)))",
    );
    let original = root(&mut executor, 0);
    let calls = Cell::new(0);
    let stop = || {
        calls.set(calls.get() + 1);
        calls.get() == 1
    };
    let mut continuation = SingletonSearch::default();
    assert!(!continuation.may_skip(
        original,
        &[original],
        &executor.ctx,
        &executor.proof_source_work,
        &stop
    ));
    let _ = executor.ctx.terms.mk_not_raw(original);
    assert!(!continuation.may_skip(
        original,
        &[original],
        &executor.ctx,
        &executor.proof_source_work,
        &stop
    ));
    assert_eq!(calls.get(), 1, "no second owner or recovered callback");
    let mut continuation = SingletonSearch::default();
    executor.proof_source_work.set_remaining_for_test(0);
    for _ in 0..2 {
        assert!(!continuation.may_skip(
            original,
            &[original],
            &executor.ctx,
            &executor.proof_source_work,
            &|| false
        ));
        assert_eq!(executor.proof_source_work.remaining_for_test(), 0);
    }
}

#[test]
fn continuation_spends_one_cumulative_envelope_without_reusing_declarations() {
    let mut executor = fixture(
        "(declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8))
         (assert (= x (bvurem y #x0a)))",
    );
    let original = root(&mut executor, 0);
    let before = executor.proof_source_work.remaining_for_test();
    let mut continuation = SingletonSearch::default();
    assert!(continuation.may_skip(
        original,
        &[original],
        &executor.ctx,
        &executor.proof_source_work,
        &|| false
    ));
    let cost = before - executor.proof_source_work.remaining_for_test();
    assert!(cost > 0);
    executor
        .proof_source_work
        .set_remaining_for_test(2 * cost - 1);
    assert!(continuation.may_skip(
        original,
        &[original],
        &executor.ctx,
        &executor.proof_source_work,
        &|| false
    ));
    assert!(!continuation.may_skip(
        original,
        &[original],
        &executor.ctx,
        &executor.proof_source_work,
        &|| false
    ));
    let remaining = executor.proof_source_work.remaining_for_test();
    assert!(!continuation.may_skip(
        original,
        &[original],
        &executor.ctx,
        &executor.proof_source_work,
        &|| false
    ));
    assert_eq!(executor.proof_source_work.remaining_for_test(), remaining);

    // A new independent search still must authenticate changed declarations;
    // no cached symbol inventory from before raw interning grants authority.
    executor.proof_source_work.set_remaining_for_test(before);
    let mut fresh = SingletonSearch::default();
    assert!(fresh.may_skip(
        original,
        &[original],
        &executor.ctx,
        &executor.proof_source_work,
        &|| false
    ));
    executor
        .execute_all(&ay_frontend::parse("(declare-const x Bool)").expect("overload"))
        .expect("legal distinct result sort");
    assert!(!fresh.may_skip(
        original,
        &[original],
        &executor.ctx,
        &executor.proof_source_work,
        &|| false
    ));
}
