// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_frontend::Command;
use std::sync::{atomic::AtomicBool, Arc};
use std::time::{Duration, Instant};

mod actual_e1_local;
mod original_aggregate;
mod original_read_only;
mod original_scalar_access;
mod original_scalar_action;

const CELL32: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../ay-proof/src/alethe_printer/bv_packed/circuit/memory_fixtures/cell32.smt2"
));
const CELL64: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../ay-proof/src/alethe_printer/bv_packed/circuit/memory_fixtures/cell64.smt2"
));

fn loaded(source: &str) -> Executor {
    let mut executor = Executor::new();
    let commands = ay_frontend::parse(source).unwrap();
    for command in commands {
        if !matches!(command, Command::CheckSat | Command::Exit) {
            executor.execute_all(&[command]).unwrap();
        }
    }
    executor
}

fn arm(executor: &mut Executor) {
    executor.begin_public_solve(false);
    executor.bind_authored_unsat_query_assumptions(&[], &Command::CheckSat);
    assert!(!executor.prepare_check_sat_internal_state());
}

fn declined_without_authority(executor: &mut Executor) {
    assert!(!executor.try_early_ground_memory_refutation());
    assert!(executor.last_proof_raw_original_assertions.is_empty());
    assert!(executor.last_proof.is_none());
    assert!(executor.last_unsat_certificate.is_none());
}

#[test]
fn original_memory_queries_publish_checked_proofs() {
    for (name, source) in [("cell32", CELL32), ("cell64", CELL64)] {
        let mut executor = loaded(source);
        executor.set_memory_limit(Some(8 * 1024 * 1024 * 1024));
        let outputs = executor
            .execute_all(
                &ay_frontend::parse("(set-option :produce-proofs true)(check-sat)(get-proof)")
                    .unwrap(),
            )
            .unwrap();
        assert_eq!(
            outputs.first().map(String::as_str),
            Some("unsat"),
            "{name}: {:?}",
            executor.unknown_reason()
        );
        let proof = executor.last_proof().expect("public proof retained");
        executor.check_proof_strict_with_datatypes(proof).unwrap();
        let text = outputs.last().unwrap();
        assert!(!text.starts_with("(error"), "{name}: {text}");
        assert!(text.contains(":rule resolution"));
        assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
        let path = std::env::temp_dir().join(format!(
            "ay-early-memory-{name}-{}.json",
            std::process::id()
        ));
        std::fs::write(
            &path,
            serde_json::to_vec(&serde_json::json!({
                "type":"alethe_certificate", "version":"1.0", "problem":source, "proof":text
            }))
            .unwrap(),
        )
        .unwrap();
        println!("independent replay certificate: {}", path.display());
    }
}

#[test]
fn public_memory_surface_requires_both_exact_raw_authority_ledgers() {
    let mut executor = loaded(CELL32);
    let outputs = executor
        .execute_all(&ay_frontend::parse("(set-option :produce-proofs true)(check-sat)").unwrap())
        .unwrap();
    assert_eq!(outputs, ["unsat"]);
    assert!(executor
        .last_proof_with_authenticated_alethe_surface()
        .is_some());
    let raw = std::mem::take(&mut executor.last_proof_raw_original_assertions);
    assert!(executor
        .last_proof_with_authenticated_alethe_surface()
        .is_none());
    executor.last_proof_raw_original_assertions = raw;
    let rebuilt = std::mem::take(&mut executor.last_proof_rebuild_originals);
    assert!(executor
        .last_proof_with_authenticated_alethe_surface()
        .is_none());
    executor.last_proof_rebuild_originals = rebuilt;
    assert!(executor
        .last_proof_with_authenticated_alethe_surface()
        .is_some());
}

#[test]
fn unbound_and_changed_query_scopes_cannot_mint_memory_authority() {
    let mut executor = loaded(CELL32);
    declined_without_authority(&mut executor);
    executor.begin_public_solve(false);
    declined_without_authority(&mut executor);
    arm(&mut executor);
    executor.ctx.assertions[0] = executor.ctx.terms.true_term();
    declined_without_authority(&mut executor);
    // Even a newly captured epoch may not authorize a source that elaborates
    // to a different assertion than its supposedly corresponding core root.
    arm(&mut executor);
    declined_without_authority(&mut executor);
}

#[test]
fn assumptions_and_objectives_do_not_enter_the_plain_memory_route() {
    let mut executor = loaded(CELL32);
    executor.begin_public_solve(false);
    let false_term = executor.ctx.terms.false_term();
    executor.bind_authored_unsat_query_assumptions(
        &[false_term],
        &Command::CheckSatAssuming(vec![FrontendTerm::Const(
            super::super::FrontendConstant::False,
        )]),
    );
    declined_without_authority(&mut executor);
    for addition in ["(maximize entry_sp)", "(assert-soft true)"] {
        let mut executor = loaded(CELL32);
        executor
            .execute_all(&ay_frontend::parse(addition).unwrap())
            .unwrap();
        arm(&mut executor);
        declined_without_authority(&mut executor);
    }
}

#[test]
fn satisfiable_memory_source_is_not_a_refutation() {
    let mut executor = loaded(CELL32);
    let counterexample = executor.ctx.assertions_parsed()[0].clone();
    executor
        .execute_all(&ay_frontend::parse("(reset-assertions)").unwrap())
        .unwrap();
    executor
        .execute_all(&[Command::Assert(FrontendTerm::App(
            "not".into(),
            vec![counterexample],
        ))])
        .unwrap();
    arm(&mut executor);
    declined_without_authority(&mut executor);
}

#[test]
fn interrupt_deadline_and_term_memory_limits_prevent_early_authority() {
    for control in 0..3 {
        let mut executor = loaded(CELL32);
        arm(&mut executor);
        match control {
            0 => executor.set_interrupt(Arc::new(AtomicBool::new(true))),
            1 => executor.set_deadline(Some(Instant::now() - Duration::from_secs(1))),
            _ => executor.term_memory_limit = Some(1),
        }
        declined_without_authority(&mut executor);
    }
}

#[test]
fn push_pop_and_reset_retire_the_memory_refutation() {
    let mut executor = Executor::new();
    for command in ay_frontend::parse(CELL32).unwrap() {
        match command {
            Command::CheckSat | Command::Exit => (),
            Command::Assert(_) => {
                executor
                    .execute_all(&ay_frontend::parse("(push 1)").unwrap())
                    .unwrap();
                executor.execute_all(&[command]).unwrap();
            }
            _ => {
                executor.execute_all(&[command]).unwrap();
            }
        }
    }
    let outputs = executor
        .execute_all(
            &ay_frontend::parse("(check-sat)(pop 1)(check-sat)(reset-assertions)(check-sat)")
                .unwrap(),
        )
        .unwrap();
    assert_eq!(outputs, ["unsat", "sat", "sat"]);
    assert!(executor.last_proof().is_none());
    assert!(executor.last_proof_raw_original_assertions.is_empty());
    assert!(executor.last_unsat_certificate.is_none());
}

mod cli_boundary;
mod original_e1_roundtrip;
mod output_memory;

#[test]
fn array_free_frame_source_is_retained_before_preprocessing_without_authority() {
    let source = include_str!("../../../authored_ground_closure/tests/array-free-frame-image.smt2");
    let mut executor = loaded(source);
    let expected = executor.ctx.assertions[0];
    let (root, kind, used_definition) = executor
        .early_ground_memory_root(expected)
        .expect("bounded pure BV source");
    assert_eq!(kind, EarlyGroundKind::PureBitVector);
    assert!(!used_definition);
    let negative = executor.ctx.terms.mk_not_raw(root);
    assert!(executor.early_ground_memory_terms_print_faithfully(&[root, negative]));
    assert!(executor.last_proof_raw_original_assertions.is_empty());
    assert!(executor.last_proof_rebuild_originals.is_empty());
    assert!(executor.last_proof().is_none());
}

#[test]
fn early_pure_bv_satisfiable_source_declines_without_authority() {
    let source = "(set-option :produce-proofs true)(set-logic QF_UFBV)(declare-const x (_ BitVec 64))(declare-fun f ((_ BitVec 64)) (_ BitVec 64))(assert (and (= (f x) x) (= x x)))";
    let mut executor = loaded(source);
    arm(&mut executor);
    declined_without_authority(&mut executor);
}
