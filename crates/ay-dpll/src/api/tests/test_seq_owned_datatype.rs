// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Actual native Seq/inductive carrier questions. Native proof completeness
//! and public external-checker transport are deliberately separate boundaries.

use crate::api::*;
use std::time::Duration;

fn datatype() -> DatatypeSort {
    DatatypeSort::new(
        "OwnedR",
        vec![DatatypeConstructor::new(
            "owned_r",
            vec![DatatypeField::new(
                "owned_children",
                Sort::seq(Sort::Uninterpreted("OwnedR".into())),
            )],
        )],
    )
}
fn solver() -> (Solver, DatatypeSort) {
    let mut solver = Solver::new(Logic::All);
    solver.set_timeout(Some(Duration::from_secs(2)));
    let datatype = datatype();
    solver.try_declare_datatype(&datatype).unwrap();
    (solver, datatype)
}
fn assert_equal(solver: &mut Solver, a: Term, b: Term) {
    let equal = solver.try_eq(a, b).unwrap();
    solver.try_assert_term(equal).unwrap();
}

#[test]
fn seq_owned_datatype_empty_leaf_and_finite_children_have_validated_native_models() {
    for nested in [false, true] {
        let (mut solver, datatype) = solver();
        let empty = solver.seq_empty(Sort::Uninterpreted("OwnedR".into()));
        let leaf = solver
            .try_datatype_constructor(&datatype, "owned_r", &[empty])
            .unwrap();
        let children = if nested {
            solver.try_seq_unit(leaf).unwrap()
        } else {
            empty
        };
        let parent = solver
            .try_datatype_constructor(&datatype, "owned_r", &[children])
            .unwrap();
        let value = solver.declare_const("native_owned_value", Sort::Datatype(datatype.clone()));
        assert_equal(&mut solver, value, parent);
        let observed = solver
            .try_datatype_selector(
                "owned_children",
                value,
                Sort::seq(Sort::Uninterpreted("OwnedR".into())),
            )
            .unwrap();
        let length = solver.try_seq_len(observed).unwrap();
        let expected = solver.int_const(i64::from(nested));
        assert_equal(&mut solver, length, expected);
        let details = solver.check_sat_with_details();
        assert!(
            details.result.is_sat() && details.result.was_model_validated(),
            "nested={nested} {details:?}"
        );
        assert!(solver.model().is_some());
    }
}

#[test]
fn seq_owned_datatype_parent_unit_cycle_publication_retains_external_transport_refusal() {
    let (mut solver, datatype) = solver();
    solver.set_produce_proofs(true);
    solver
        .try_set_option(":check-proofs-strict", "true")
        .unwrap();
    let value = solver.declare_const("native_owned_cycle", Sort::Datatype(datatype.clone()));
    let sequence = solver.try_seq_unit(value).unwrap();
    let parent = solver
        .try_datatype_constructor(&datatype, "owned_r", &[sequence])
        .unwrap();
    assert_equal(&mut solver, value, parent);
    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_unknown(),
        "necessary Seq proof syntax is not silently published as externally checked: {details:?}"
    );
    assert_eq!(details.unknown_reason,Some(UnknownReason::ProofTrusted),"the computed native refutation must reach the actual strict publication boundary: {details:?}");
}

#[test]
fn seq_owned_datatype_in_bounds_nth_cycle_reaches_strict_publication_boundary() {
    let (mut solver, datatype) = solver();
    solver.set_produce_proofs(true);
    solver
        .try_set_option(":check-proofs-strict", "true")
        .unwrap();
    let value = solver.declare_const("native_nth_cycle", Sort::Datatype(datatype.clone()));
    let sequence = solver.declare_const(
        "native_children",
        Sort::seq(Sort::Uninterpreted("OwnedR".into())),
    );
    let index = solver.declare_const("native_child_index", Sort::Int);
    let parent = solver
        .try_datatype_constructor(&datatype, "owned_r", &[sequence])
        .unwrap();
    let child = solver.try_seq_nth(sequence, index).unwrap();
    assert_equal(&mut solver, value, parent);
    assert_equal(&mut solver, value, child);
    let zero = solver.int_const(0);
    let length = solver.try_seq_len(sequence).unwrap();
    let lower = solver.try_le(zero, index).unwrap();
    let upper = solver.try_lt(index, length).unwrap();
    solver.try_assert_term(lower).unwrap();
    solver.try_assert_term(upper).unwrap();
    let details = solver.check_sat_with_details();
    assert!(details.result.is_unknown(), "{details:?}");
    assert_eq!(
        details.unknown_reason,
        Some(UnknownReason::ProofTrusted),
        "{details:?}"
    );
}

#[test]
fn seq_owned_datatype_out_of_bounds_and_wrong_sequence_guard_have_validated_models() {
    for wrong_sequence in [false, true] {
        let (mut solver, datatype) = solver();
        let empty = solver.seq_empty(Sort::Uninterpreted("OwnedR".into()));
        let value = solver.declare_const("native_oob_parent", Sort::Datatype(datatype.clone()));
        let leaf = solver
            .try_datatype_constructor(&datatype, "owned_r", &[empty])
            .unwrap();
        assert_equal(&mut solver, value, leaf);
        let zero = solver.int_const(0);
        let child = solver.try_seq_nth(empty, zero).unwrap();
        assert_equal(&mut solver, value, child);
        let guarded_sequence = if wrong_sequence {
            solver.try_seq_unit(value).unwrap()
        } else {
            empty
        };
        let length = solver.try_seq_len(guarded_sequence).unwrap();
        let guard = if wrong_sequence {
            solver.try_lt(zero, length).unwrap()
        } else {
            solver.try_ge(zero, length).unwrap()
        };
        solver.try_assert_term(guard).unwrap();
        let details = solver.check_sat_with_details();
        assert!(
            details.result.is_sat() && details.result.was_model_validated(),
            "wrong_sequence={wrong_sequence} {details:?}"
        );
    }
}

#[test]
fn seq_owned_datatype_empty_concat_self_identity_has_validated_model() {
    let (mut solver, datatype) = solver();
    let sequence = solver.declare_const(
        "native_concat_sequence",
        Sort::seq(Sort::Uninterpreted("OwnedR".into())),
    );
    let empty = solver.seq_empty(Sort::Uninterpreted("OwnedR".into()));
    let concat = solver.try_seq_concat(sequence, empty).unwrap();
    assert_equal(&mut solver, sequence, concat);
    assert_equal(&mut solver, sequence, empty);
    let value = solver.declare_const("native_concat_parent", Sort::Datatype(datatype.clone()));
    let parent = solver
        .try_datatype_constructor(&datatype, "owned_r", &[sequence])
        .unwrap();
    assert_equal(&mut solver, value, parent);
    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_sat() && details.result.was_model_validated(),
        "{details:?}"
    );
}

#[test]
fn seq_owned_datatype_reference_distinguishes_original_declaration_and_base_constructor_matrix() {
    use sha2::{Digest, Sha256};
    use std::process::Stdio;
    use wait_timeout::ChildExt as _;
    let oracle = ay_test_support::z3::require_z3("native owned Seq/datatype semantics");
    let row = match (std::env::consts::OS, std::env::consts::ARCH) {
        ("macos", "aarch64") => "darwin_arm64",
        ("macos", "x86_64") => "darwin_x86_64",
        ("linux", "aarch64") => "linux_aarch64",
        ("linux", "x86_64") => "linux_x86_64",
        target => panic!("no pinned reference row for {target:?}"),
    };
    let key = format!("Z3_BIN_SHA256_{row}=");
    let digest = include_str!("../../../../../ci/z3.pin")
        .lines()
        .find_map(|line| line.strip_prefix(&key))
        .expect("canonical oracle pin");
    let before = format!(
        "{:x}",
        Sha256::digest(std::fs::read(oracle.path()).unwrap())
    );
    assert_eq!(
        before, digest,
        "the semantic reference must be the repository-pinned binary"
    );
    let cases=[
        ("empty-leaf","(declare-const r OwnedR) (assert (= r (owned_r (as seq.empty (Seq OwnedR)))))","sat"),
        ("finite-nesting","(declare-const r OwnedR) (assert (= r (owned_r (seq.unit (owned_r (as seq.empty (Seq OwnedR)))))))","sat"),
        ("unit-parent-cycle","(declare-const r OwnedR) (assert (= r (owned_r (seq.unit r))))","unsat"),
        ("guarded-nth-cycle","(declare-const r OwnedR) (declare-const s (Seq OwnedR)) (declare-const i Int) (assert (= r (owned_r s))) (assert (= r (seq.nth s i))) (assert (<= 0 i)) (assert (< i (seq.len s)))","unsat"),
        ("out-of-bounds","(declare-const r OwnedR) (assert (= r (owned_r (as seq.empty (Seq OwnedR))))) (assert (= r (seq.nth (as seq.empty (Seq OwnedR)) 0)))","sat"),
        ("wrong-sequence-guard","(declare-const r OwnedR) (assert (= r (owned_r (as seq.empty (Seq OwnedR))))) (assert (= r (seq.nth (as seq.empty (Seq OwnedR)) 0))) (assert (< 0 (seq.len (seq.unit r))))","sat"),
        ("concat-identity","(declare-const r OwnedR) (declare-const s (Seq OwnedR)) (assert (= r (owned_r s))) (assert (= s (seq.++ s (as seq.empty (Seq OwnedR))))) (assert (= (seq.len s) 0))","sat"),
    ];
    let directory = tempfile::tempdir().unwrap();
    let run = |label: &str, input: &str| {
        let problem = directory.path().join(format!("{label}.smt2"));
        let out = directory.path().join(format!("{label}.out"));
        let err = directory.path().join(format!("{label}.err"));
        std::fs::write(&problem, input).unwrap();
        let mut child = oracle
            .command()
            .arg("-smt2")
            .arg(&problem)
            .stdin(Stdio::null())
            .stdout(std::fs::File::create(&out).unwrap())
            .stderr(std::fs::File::create(&err).unwrap())
            .spawn()
            .unwrap();
        let Some(status) = child.wait_timeout(Duration::from_secs(3)).unwrap() else {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("reference {label} exceeded its actual limit");
        };
        assert!(
            std::fs::metadata(&out).unwrap().len() <= 1 << 20
                && std::fs::metadata(&err).unwrap().len() <= 1 << 20
        );
        (
            status,
            std::fs::read_to_string(&out).unwrap(),
            std::fs::read_to_string(&err).unwrap(),
        )
    };
    // Keep the native original declaration visible. The pinned reference
    // rejects its well-foundedness; a trailing answer after that error is not
    // oracle agreement. A future reference supporting it must answer exactly.
    let original = format!("(set-option :timeout 2000) (set-logic ALL) (declare-datatypes ((OwnedR 0)) (((owned_r (owned_children (Seq OwnedR)))))) {} (check-sat)\n", cases[0].1);
    let (status, stdout, stderr) = run("original-single-constructor", &original);
    if status.success() {
        assert_eq!(stdout.trim(), "sat", "{stderr}\n{original}");
        eprintln!(
            "reference supports original empty-leaf input, input_sha256={:x}",
            Sha256::digest(original.as_bytes())
        );
    } else {
        assert!(
            stdout.contains("datatype is not well-founded")
                || stderr.contains("datatype is not well-founded"),
            "unexpected original-declaration failure: {status} {stdout} {stderr}"
        );
        eprintln!("reference REJECTS original declaration; no original-query oracle agreement claimed, input_sha256={:x}", Sha256::digest(original.as_bytes()));
    }
    // This is a separate, comparable datatype with an explicit nullary base.
    // The original AY source questions above retain their single constructor.
    for (label, assertions, expected) in cases {
        let input = format!("(set-option :timeout 2000) (set-logic ALL) (declare-datatypes ((OwnedR 0)) (((owned_base) (owned_r (owned_children (Seq OwnedR)))))) {assertions} (check-sat)\n");
        let (status, stdout, stderr) = run(&format!("explicit-base-{label}"), &input);
        assert!(
            status.success(),
            "explicit-base {label}: {status} {stdout} {stderr}\n{input}"
        );
        assert_eq!(
            stdout.trim(),
            expected,
            "explicit-base {label}: {stderr}\n{input}"
        );
        eprintln!("explicit-base Seq/datatype reference {label}: {expected}, input_sha256={:x}, oracle_sha256={before}", Sha256::digest(input.as_bytes()));
    }
    assert_eq!(
        before,
        format!(
            "{:x}",
            Sha256::digest(std::fs::read(oracle.path()).unwrap())
        )
    );
}
