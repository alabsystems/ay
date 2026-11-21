// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Paired API transport, independently checked as a whole document. The native
//! fixtures are retained current-stack inputs, not complete consumer sessions.

use std::fs::File;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::Duration;

use ay_core::{DatatypeConstructor, DatatypeSort, Sort};
use ay_dpll::api::{Logic, NativeReplayArtifact, Solver, UnsatProofArtifact};
use wait_timeout::ChildExt;

fn carcara(problem: &str, proof: &str) -> String {
    ay_core::pinned_carcara::pinned_carcara_can_judge(problem, proof)
        .expect("pair is outside pinned checker misjudgments");
    let checker =
        std::env::var_os("CARCARA_PATH").map_or_else(|| PathBuf::from("carcara"), PathBuf::from);
    let version = Command::new(&checker)
        .arg("--version")
        .output()
        .expect("pinned Carcara");
    assert!(version.status.success());
    assert!(String::from_utf8_lossy(&version.stdout).contains("9a352ee"));
    let dir = tempfile::tempdir().expect("checker files");
    let smt = dir.path().join("problem.smt2");
    let al = dir.path().join("proof.alethe");
    let stdout = dir.path().join("stdout");
    let stderr = dir.path().join("stderr");
    std::fs::write(&smt, problem).expect("exact paired problem");
    std::fs::write(&al, proof).expect("exact proof");
    let mut child = Command::new(checker)
        .args(["check", "--no-color", "--"])
        .arg(al)
        .arg(smt)
        .stdout(Stdio::from(File::create(&stdout).expect("stdout")))
        .stderr(Stdio::from(File::create(&stderr).expect("stderr")))
        .spawn()
        .expect("checker child");
    let status = match child.wait_timeout(Duration::from_secs(15)).expect("wait") {
        Some(status) => status,
        None => {
            child.kill().expect("kill own expired checker");
            child.wait().expect("reap");
            panic!("Carcara timed out");
        }
    };
    let output = std::fs::read_to_string(stdout).expect("output");
    let error = std::fs::read_to_string(stderr).expect("diagnostic");
    assert!(!error.contains("parser error"), "{error}\n{problem}");
    let tokens: Vec<_> = output
        .lines()
        .filter(|line| matches!(*line, "valid" | "invalid" | "holey"))
        .collect();
    assert_eq!(tokens.len(), 1, "{status:?}: {output}\n{error}");
    if tokens[0] == "valid" {
        assert!(status.success(), "{error}");
    }
    tokens[0].to_owned()
}

fn strict(source: &str) -> (Solver, UnsatProofArtifact) {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    solver.set_produce_proofs(true);
    solver
        .try_set_option("check-proofs-strict", "true")
        .expect("strict");
    solver.parse_smtlib2(source).expect("source");
    let details = solver.check_sat_with_details();
    assert!(details.result.is_unsat(), "{details:?}");
    details
        .accept_for_consumer()
        .expect("checked proof authority");
    let proof = solver.export_last_unsat_artifact().expect("artifact");
    (solver, proof)
}

fn retained_native_input(json: &str, carrier: &str) {
    let input = NativeReplayArtifact::from_json_str(json).expect("retained input");
    let cap =
        Duration::from_millis(u64::try_from(input.timeout_ms.expect("original cap")).expect("u64"));
    let (details, proof) = Solver::replay_native_replay_artifact_with_checked_proof(&input, cap)
        .expect("one checked replay");
    assert!(details.result.is_unsat(), "{details:?}");
    details.accept_for_consumer().expect("strict authority");
    let proof = proof.expect("same-execution proof");
    assert!(!proof.alethe.contains(":rule hole"));
    assert!(!proof.alethe.contains(":rule trust"));
    assert!(
        proof.carcara_surface.is_supported(),
        "{:?}",
        proof.carcara_surface
    );
    let problem = proof
        .alethe_problem_smt2
        .expect("faithful full datatype context");
    assert_eq!(
        problem.matches("(assert ").count(),
        input.assertions.len(),
        "complete original stack"
    );
    assert!(problem.contains("(declare-datatypes"), "{problem}");
    assert!(
        !problem.contains(&format!("(declare-sort {carrier} ")),
        "{problem}"
    );
    assert_eq!(carcara(&problem, &proof.alethe), "valid");
    assert_eq!(
        proof
            .alethe
            .matches(":rule la_generic :args (1 1 1)")
            .count(),
        1
    );
    let forged = proof.alethe.replace(
        ":rule la_generic :args (1 1 1)",
        ":rule la_generic :args (0 0 0)",
    );
    assert_eq!(carcara(&problem, &forged), "invalid");
}

#[test]
fn native_datatype_problem_transport_retained_mut_s() {
    retained_native_input(
        include_str!("fixtures/native_record_proof_transport/mut_s.json"),
        "S",
    );
}

#[test]
fn native_datatype_problem_transport_retained_mut_p() {
    retained_native_input(
        include_str!("fixtures/native_record_proof_transport/mut_p.json"),
        "P",
    );
}

#[test]
fn native_datatype_problem_transport_checked_native_testers() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    solver.set_produce_proofs(true);
    solver
        .try_set_option("check-proofs-strict", "true")
        .expect("strict");
    let datatype = DatatypeSort::new(
        "NativeChoice",
        vec![
            DatatypeConstructor::unit("native-left"),
            DatatypeConstructor::unit("native-right"),
        ],
    );
    solver.try_declare_datatype(&datatype).expect("datatype");
    let a = solver.declare_const("choice-a", Sort::Datatype(datatype.clone()));
    let b = solver.declare_const("choice-b", Sort::Datatype(datatype));
    let receivers = solver.try_eq(a, b).expect("receivers");
    let left_a = solver.datatype_tester("native-left", a);
    let left_b = solver.datatype_tester("native-left", b);
    let equal = solver.try_eq(left_a, left_b).expect("Boolean equality");
    let different = solver.not(equal);
    solver.assert_term(receivers);
    solver.assert_term(different);
    let details = solver.check_sat_with_details();
    assert!(details.result.is_unsat(), "{details:?}");
    details.accept_for_consumer().expect("strict authority");
    let proof = solver.export_last_unsat_artifact().expect("artifact");
    assert!(
        proof.carcara_surface.is_supported(),
        "{:?}",
        proof.carcara_surface
    );
    let problem = proof
        .alethe_problem_smt2
        .expect("same canonical tester pair");
    assert_eq!(problem.matches("(assert ").count(), 2);
    assert!(problem.contains("(_ is native-left)"), "{problem}");
    assert!(
        !problem.contains("(define-fun is-"),
        "no checker-specific alias: {problem}"
    );
    assert!(
        !problem.contains("(declare-fun is-"),
        "no free tester: {problem}"
    );
    assert_eq!(carcara(&problem, &proof.alethe), "valid");
    let congruence = proof
        .alethe
        .lines()
        .find(|line| line.contains(":rule cong ") && line.contains("(_ is native-left)"))
        .expect("the indexed tester equality is checked by cong");
    let forged_step = congruence.replacen("(_ is native-left)", "(_ is native-right)", 1);
    let forged = proof.alethe.replacen(congruence, &forged_step, 1);
    assert_eq!(carcara(&problem, &forged), "invalid");
}

#[test]
fn native_datatype_problem_transport_keeps_ordinary_transport_after_pop() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    solver.set_produce_proofs(true);
    solver
        .try_set_option("check-proofs-strict", "true")
        .expect("strict");
    solver.try_push().expect("push");
    solver.parse_smtlib2("\
        (declare-datatypes ((PoppedOption 1)) ((par (T) ((popped-none) (popped-some (popped-item T))))))
        (declare-const popped-value (PoppedOption Int))
    ").expect("scoped datatype");
    solver.try_pop().expect("pop");
    let p = solver.declare_const("after-pop", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);
    let details = solver.check_sat_with_details();
    assert!(details.result.is_unsat(), "{details:?}");
    details.accept_for_consumer().expect("strict authority");
    let proof = solver
        .export_last_unsat_artifact()
        .expect("ordinary artifact");
    let problem = proof.alethe_problem_smt2.expect("ordinary paired problem");
    assert!(!problem.contains("PoppedOption"), "{problem}");
    assert!(!problem.contains("popped-value"), "{problem}");
    assert_eq!(carcara(&problem, &proof.alethe), "valid");
}

#[test]
fn native_datatype_problem_transport_keeps_full_scope_and_lexical_binders() {
    let (solver, proof) = strict(
        "\
        (declare-datatype TransportBox ((transport-box (transport-value Int))))
        (declare-const transport-p Bool)
        (declare-fun transport-f (Int) Int)
        (assert (forall ((transport-bound Int)) (>= (transport-f transport-bound) transport-bound)))
        (assert transport-p) (assert transport-p) (assert (not transport-p))
    ",
    );
    let problem = proof.alethe_problem_smt2.expect("paired context");
    assert_eq!(
        problem.matches("(assert ").count(),
        solver.assertions_iter().len()
    );
    assert!(
        !problem.contains("(declare-fun transport-bound"),
        "{problem}"
    );
    assert!(
        problem.contains("(forall ((transport-bound Int))"),
        "{problem}"
    );
    assert!(
        !problem.contains("(declare-fun transport-value"),
        "{problem}"
    );
    assert_eq!(carcara(&problem, &proof.alethe), "valid");
}

#[test]
fn native_datatype_problem_transport_refuses_defined_context_without_erasing_it() {
    let (_, proof) = strict(
        "\
        (declare-datatype DefinedBox ((defined-box (defined-value Int))))
        (define-fun defined-identity ((x Int)) Int x)
        (declare-const defined-p Bool)
        (assert defined-p) (assert (not defined-p))
    ",
    );
    assert!(
        proof.alethe_problem_smt2.is_none(),
        "definition must not become a UF"
    );
}

#[test]
fn native_datatype_problem_transport_refuses_ambiguous_member_surfaces() {
    let (_, proof) = strict(
        "\
        (declare-datatype FirstBox ((first-box (shared-field Int))))
        (declare-datatype SecondBox ((second-box (shared-field Int))))
        (declare-const overload-p Bool)
        (assert overload-p) (assert (not overload-p))
    ",
    );
    assert!(
        proof.alethe_problem_smt2.is_none(),
        "no guessed overload declaration"
    );
}

#[test]
fn native_datatype_problem_transport_refuses_parametric_instances() {
    let (_, proof) = strict("\
        (declare-datatypes ((TransportOption 1)) ((par (T) ((transport-none) (transport-some (transport-item T))))))
        (declare-const optional-value (TransportOption Int))
        (declare-const parametric-p Bool)
        (assert parametric-p) (assert (not parametric-p))
    ");
    assert!(
        proof.alethe_problem_smt2.is_none(),
        "no erased type arguments"
    );
}
