// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::api::*;
use ay_core::{Constant, Symbol, TermData};

fn budget() -> NativeDeclarationBudget {
    NativeDeclarationBudget::new(NativeDeclarationLimits::new(64 << 20, 64 << 20, 128))
}

#[test]
fn native_sequence_operations_ground_length_does_not_change_the_original_raw_term() {
    let mut solver = Solver::new(Logic::All);
    let empty = solver.try_seq_empty(Sort::Bool).unwrap();
    let value = solver.bool_const(true);
    let unit = solver.try_seq_unit(value).unwrap();
    let concat = solver.try_seq_concat(empty, unit).unwrap();
    let raw_length = solver.try_seq_len(concat).unwrap();
    let raw_before = solver.terms().get(raw_length.id()).clone();
    let roots = solver.assertions();
    let events = solver.native_replay_events.len();
    let normalized = solver
        .try_seq_len_with_progress(concat, &mut budget(), &mut |_, _| true)
        .unwrap();
    assert!(
        matches!(solver.terms().get(normalized.id()), TermData::Const(Constant::Int(n)) if n == &1.into())
    );
    assert_eq!(solver.terms().get(raw_length.id()), &raw_before);
    assert_eq!(solver.assertions(), roots);
    assert_eq!(solver.native_replay_events.len(), events);
    // A certificate issued for the new construction cannot be substituted
    // for a proof from the separately retained raw input.
    assert_ne!(raw_length, normalized);
}

#[test]
fn native_sequence_operations_keep_unit_payload_and_both_concat_children() {
    let mut solver = Solver::new(Logic::All);
    let mut owner = budget();
    let input = solver.declare_const("element", Sort::Int);
    let unit = solver
        .try_seq_unit_with_progress(input, &mut owner, &mut |_, _| true)
        .unwrap();
    assert!(
        matches!(solver.terms().get(unit.id()), TermData::App(Symbol::Named(name), args) if name == "seq.unit" && args == &[input.id()])
    );
    let empty = solver
        .try_seq_empty_with_progress(&Sort::Int, &mut owner, &mut |_, _| true)
        .unwrap();
    let concat = solver
        .try_seq_concat_with_progress(empty, unit, &mut owner, &mut |_, _| true)
        .unwrap();
    assert!(
        matches!(solver.terms().get(concat.id()), TermData::App(Symbol::Named(name), args) if name == "seq.++" && args == &[empty.id(), unit.id()])
    );
    let len = solver
        .try_seq_len_with_progress(concat, &mut owner, &mut |_, _| true)
        .unwrap();
    assert_eq!(len, solver.int_const(1));
}

#[test]
fn native_sequence_operations_shared_dag_keeps_unbounded_integer_magnitude() {
    let mut solver = Solver::new(Logic::All);
    let value = solver.bool_const(false);
    let mut sequence = solver.try_seq_unit(value).unwrap();
    for _ in 0..80 {
        // Original input is an eighty-node DAG denoting 2^80 elements; no
        // materialized sequence vector and no machine-integer narrowing.
        let id = solver.terms_mut().mk_app_structural(
            Symbol::named("seq.++"),
            vec![sequence.id(), sequence.id()],
            Sort::seq(Sort::Bool),
        );
        sequence = solver.wrap_term(id);
    }
    let len = solver
        .try_seq_len_with_progress(sequence, &mut budget(), &mut |_, _| true)
        .unwrap();
    assert!(
        matches!(solver.terms().get(len.id()), TermData::Const(Constant::Int(n)) if n == &(num_bigint::BigInt::from(1u8) << 80))
    );
}

#[test]
fn native_sequence_operations_opaque_leaves_and_declared_namesakes_remain_opaque() {
    let mut solver = Solver::new(Logic::All);
    let opaque = solver.declare_const("opaque_sequence", Sort::seq(Sort::Bool));
    let len = solver
        .try_seq_len_with_progress(opaque, &mut budget(), &mut |_, _| true)
        .unwrap();
    assert!(
        matches!(solver.terms().get(len.id()), TermData::App(Symbol::Named(name), args) if name == "seq.len" && args == &[opaque.id()])
    );
    let value = solver.bool_const(true);
    let raw = solver.terms_mut().mk_app_structural(
        Symbol::named("seq.unit"),
        vec![value.id()],
        Sort::seq(Sort::Bool),
    );
    solver.terms_mut().register_declared_function("seq.unit");
    let raw = solver.wrap_term(raw);
    let len = solver
        .try_seq_len_with_progress(raw, &mut budget(), &mut |_, _| true)
        .unwrap();
    assert!(
        matches!(solver.terms().get(len.id()), TermData::App(Symbol::Named(name), args) if name == "seq.len" && args == &[raw.id()])
    );
}

#[test]
fn native_sequence_operations_symbolic_concat_preserves_each_raw_length() {
    let mut solver = Solver::new(Logic::All);
    let sequence = solver.declare_const("symbolic", Sort::seq(Sort::Int));
    let value = solver.int_const(123);
    let unit = solver.try_seq_unit(value).unwrap();
    let concat = solver.try_seq_concat(sequence, unit).unwrap();
    let len = solver
        .try_seq_len_with_progress(concat, &mut budget(), &mut |_, _| true)
        .unwrap();
    let TermData::App(Symbol::Named(name), args) = solver.terms().get(len.id()) else {
        panic!("missing symbolic sum");
    };
    assert_eq!(name, "+");
    assert_eq!(args.len(), 2);
    assert!(
        matches!(solver.terms().get(args[0]), TermData::App(Symbol::Named(name), children) if name == "seq.len" && children == &[sequence.id()])
    );
    assert!(
        matches!(solver.terms().get(args[1]), TermData::Const(Constant::Int(n)) if n == &1.into())
    );
}

#[test]
fn native_sequence_operations_refuse_foreign_stale_and_mismatched_inputs_even_beside_empty() {
    let mut solver = Solver::new(Logic::All);
    let mut other = Solver::new(Logic::All);
    let foreign = other.try_seq_empty(Sort::Bool).unwrap();
    let empty = solver.try_seq_empty(Sort::Bool).unwrap();
    assert!(solver
        .try_seq_concat_with_progress(empty, foreign, &mut budget(), &mut |_, _| true)
        .is_err());
    let int_empty = solver.try_seq_empty(Sort::Int).unwrap();
    assert!(solver
        .try_seq_concat_with_progress(empty, int_empty, &mut budget(), &mut |_, _| true)
        .is_err());
    assert!(solver
        .try_seq_len_with_progress(foreign, &mut budget(), &mut |_, _| true)
        .is_err());
    solver.reset();
    assert!(solver
        .try_seq_len_with_progress(empty, &mut budget(), &mut |_, _| true)
        .is_err());
}

#[test]
fn native_sequence_operations_cancellation_and_low_budget_are_cumulative_across_pop() {
    let mut solver = Solver::new(Logic::All);
    let element = solver.bool_const(true);
    let mut owner = budget();
    let before = solver.terms().len();
    assert!(solver
        .try_seq_unit_with_progress(element, &mut owner, &mut |_, _| false)
        .is_err());
    solver.try_push().unwrap();
    solver.try_pop().unwrap();
    assert!(solver
        .try_seq_unit_with_progress(element, &mut owner, &mut |_, _| true)
        .is_err());
    assert_eq!(solver.terms().len(), before);
    let mut low = NativeDeclarationBudget::new(NativeDeclarationLimits::new(0, 64 << 20, 128));
    assert!(solver
        .try_seq_unit_with_progress(element, &mut low, &mut |_, _| true)
        .is_err());
    assert_eq!(solver.terms().len(), before);
}

#[test]
fn native_sequence_operations_nested_current_nominal_carrier_is_exact() {
    let mut solver = Solver::new(Logic::All);
    let nominal = solver.try_declare_opaque_sort("SequenceElement").unwrap();
    let actual = solver.declare_const(
        "nested_element",
        Sort::array(Sort::Int, Sort::seq(nominal.clone())),
    );
    let unit = solver
        .try_seq_unit_with_progress(actual, &mut budget(), &mut |_, _| true)
        .unwrap();
    assert_eq!(solver.get_sort(unit), Sort::seq(solver.get_sort(actual)));
    let len = solver
        .try_seq_len_with_progress(unit, &mut budget(), &mut |_, _| true)
        .unwrap();
    assert_eq!(len, solver.int_const(1));
}

#[test]
fn native_sequence_operations_ground_fold_cannot_bypass_a_declared_length_head() {
    let mut solver = Solver::new(Logic::All);
    let value = solver.bool_const(true);
    let unit = solver.try_seq_unit(value).unwrap();
    solver.terms_mut().register_declared_function("seq.len");
    let before = solver.terms().len();
    assert!(solver
        .try_seq_len_with_progress(unit, &mut budget(), &mut |_, _| true)
        .is_err());
    assert_eq!(solver.terms().len(), before);
}

#[test]
fn native_sequence_operations_symbolic_sum_cannot_use_a_declared_addition_head() {
    let mut solver = Solver::new(Logic::All);
    let opaque = solver.declare_const("symbolic_for_addition", Sort::seq(Sort::Bool));
    let value = solver.bool_const(true);
    let unit = solver.try_seq_unit(value).unwrap();
    let concat = solver.try_seq_concat(opaque, unit).unwrap();
    solver.terms_mut().register_declared_function("+");
    assert!(solver
        .try_seq_len_with_progress(concat, &mut budget(), &mut |_, _| true)
        .is_err());
    // A native integer addition of actual constant lengths has no named head.
    let len = solver
        .try_seq_len_with_progress(unit, &mut budget(), &mut |_, _| true)
        .unwrap();
    assert_eq!(len, solver.int_const(1));
}

#[test]
fn native_sequence_operations_memo_reuse_checks_the_entire_deeper_subtree() {
    let mut solver = Solver::new(Logic::All);
    let value = solver.bool_const(true);
    let unit = solver.try_seq_unit(value).unwrap();
    let mut shared = unit;
    for _ in 0..3 {
        shared = solver.try_seq_concat(shared, unit).unwrap();
    }
    let mut deeper = shared;
    for _ in 0..3 {
        deeper = solver.try_seq_concat(unit, deeper).unwrap();
    }
    let root = solver.try_seq_concat(shared, deeper).unwrap();
    let mut shallow =
        NativeDeclarationBudget::new(NativeDeclarationLimits::new(64 << 20, 64 << 20, 7));
    assert!(solver
        .try_seq_len_with_progress(root, &mut shallow, &mut |_, _| true)
        .is_err());
    assert!(matches!(
        shallow.refusal(),
        Some(NativeDeclarationRefusal::Depth { .. })
    ));
    // The same exact query has a legal construction under a sufficient owner.
    let normalized = solver
        .try_seq_len_with_progress(root, &mut budget(), &mut |_, _| true)
        .unwrap();
    assert_eq!(normalized, solver.int_const(11));
}

#[test]
fn native_sequence_operations_late_cancel_storage_and_depth_refuse_without_renewal() {
    let mut baseline = Solver::new(Logic::All);
    let element = baseline.bool_const(true);
    let unit = baseline.try_seq_unit(element).unwrap();
    let mut calls = 0;
    baseline
        .try_seq_len_with_progress(unit, &mut budget(), &mut |_, _| {
            calls += 1;
            true
        })
        .unwrap();
    let mut solver = Solver::new(Logic::All);
    let element = solver.bool_const(true);
    let unit = solver.try_seq_unit(element).unwrap();
    let mut owner = budget();
    let mut visited = 0;
    assert!(solver
        .try_seq_len_with_progress(unit, &mut owner, &mut |_, _| {
            visited += 1;
            visited < calls
        })
        .is_err());
    assert_eq!(visited, calls);
    assert!(solver
        .try_seq_len_with_progress(unit, &mut owner, &mut |_, _| true)
        .is_err());
    let mut storage = NativeDeclarationBudget::new(NativeDeclarationLimits::new(64 << 20, 0, 128));
    assert!(solver
        .try_seq_unit_with_progress(element, &mut storage, &mut |_, _| true)
        .is_err());
    let mut deep = unit;
    for _ in 0..6 {
        deep = solver.try_seq_concat(deep, unit).unwrap();
    }
    let mut shallow =
        NativeDeclarationBudget::new(NativeDeclarationLimits::new(64 << 20, 64 << 20, 3));
    assert!(solver
        .try_seq_len_with_progress(deep, &mut shallow, &mut |_, _| true)
        .is_err());
    assert!(matches!(
        shallow.refusal(),
        Some(NativeDeclarationRefusal::Depth { .. })
    ));
}

#[test]
fn native_sequence_operations_new_normalized_source_has_strict_proof_and_sat_neighbor() {
    for (expected_length, unsat) in [(1, true), (2, false)] {
        let mut solver = Solver::new(Logic::All);
        solver.set_produce_proofs(true);
        let mut owner = budget();
        let element = solver.bool_const(true);
        let empty = solver
            .try_seq_empty_with_progress(&Sort::Bool, &mut owner, &mut |_, _| true)
            .unwrap();
        let unit = solver
            .try_seq_unit_with_progress(element, &mut owner, &mut |_, _| true)
            .unwrap();
        let sequence = solver
            .try_seq_concat_with_progress(empty, unit, &mut owner, &mut |_, _| true)
            .unwrap();
        let length = solver
            .try_seq_len_with_progress(sequence, &mut owner, &mut |_, _| true)
            .unwrap();
        let numeral = solver.int_const(expected_length);
        let equal = solver.eq(length, numeral);
        let root = solver.not(equal);
        solver.assert_term(root);
        let artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
        if unsat {
            let (details, proof) = Solver::replay_native_replay_artifact_with_checked_proof(
                &artifact,
                std::time::Duration::from_secs(5),
            )
            .unwrap();
            assert!(details.result.is_unsat(), "{details:?}");
            let proof = proof.expect("checked proof for the actual new normalized source");
            proof
                .accept_for_consumer(ProofAcceptanceMode::Strict)
                .unwrap();
            assert_eq!(proof.quality.trust_count, 0);
            assert_eq!(proof.quality.hole_count, 0);
            let problem = proof.alethe_problem_smt2.as_ref().unwrap();
            super::test_native_datatype_batch::check_whole_paired_document(
                problem,
                &proof.alethe,
                &proof.carcara_surface,
            );
        } else {
            let details = Solver::replay_native_replay_artifact(&artifact).unwrap();
            assert!(
                details.result.is_sat() && details.result.was_model_validated(),
                "{details:?}"
            );
        }
    }
}

#[test]
fn native_sequence_operations_reference_length_laws() {
    use sha2::{Digest, Sha256};
    use std::{process::Stdio, time::Duration};
    use wait_timeout::ChildExt as _;
    let oracle = ay_test_support::z3::require_z3("bounded sequence construction length laws");
    let row = match (std::env::consts::OS, std::env::consts::ARCH) {
        ("macos", "aarch64") => "darwin_arm64",
        ("macos", "x86_64") => "darwin_x86_64",
        ("linux", "aarch64") => "linux_aarch64",
        ("linux", "x86_64") => "linux_x86_64",
        target => panic!("no pinned oracle row for {target:?}"),
    };
    let key = format!("Z3_BIN_SHA256_{row}=");
    let expected_digest = include_str!("../../../../../ci/z3.pin")
        .lines()
        .find_map(|line| line.strip_prefix(&key))
        .unwrap();
    let binary_digest = format!(
        "{:x}",
        Sha256::digest(std::fs::read(oracle.path()).unwrap())
    );
    assert_eq!(binary_digest, expected_digest);
    let cases = [
        ("empty", "(assert (not (= (seq.len (as seq.empty (Seq Bool))) 0)))", "unsat"),
        ("unit", "(declare-const x Int) (assert (not (= (seq.len (seq.unit x)) 1)))", "unsat"),
        ("symbolic-concat", "(declare-const s (Seq Bool)) (assert (not (= (seq.len (seq.++ s (seq.unit true))) (+ (seq.len s) 1))))", "unsat"),
        ("wrong-concat-neighbor", "(declare-const s (Seq Bool)) (assert (not (= (seq.len (seq.++ s (seq.unit true))) (+ (seq.len s) 2))))", "sat"),
    ];
    let directory = tempfile::tempdir().unwrap();
    for (label, assertion, expected) in cases {
        let input = format!("(set-logic ALL)\n{assertion}\n(check-sat)\n");
        let path = directory.path().join(format!("{label}.smt2"));
        let out = directory.path().join(format!("{label}.out"));
        let err = directory.path().join(format!("{label}.err"));
        std::fs::write(&path, &input).unwrap();
        let mut child = oracle
            .command()
            .arg("-smt2")
            .arg(&path)
            .stdin(Stdio::null())
            .stdout(std::fs::File::create(&out).unwrap())
            .stderr(std::fs::File::create(&err).unwrap())
            .spawn()
            .unwrap();
        let Some(status) = child.wait_timeout(Duration::from_secs(3)).unwrap() else {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("oracle {label} exceeded 3 seconds");
        };
        assert!(
            status.success(),
            "{label}: {}",
            std::fs::read_to_string(&err).unwrap()
        );
        assert!(std::fs::metadata(&out).unwrap().len() < 1 << 20);
        assert_eq!(
            std::fs::read_to_string(&out).unwrap().trim(),
            expected,
            "{label}"
        );
        eprintln!(
            "oracle {label}={expected} input_sha256={:x} binary_sha256={binary_digest}",
            Sha256::digest(input.as_bytes())
        );
    }
    assert_eq!(
        format!(
            "{:x}",
            Sha256::digest(std::fs::read(oracle.path()).unwrap())
        ),
        binary_digest
    );
}
