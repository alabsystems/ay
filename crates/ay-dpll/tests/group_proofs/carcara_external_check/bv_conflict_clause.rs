// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A bit-vector conflict CLAUSE over an authored read-over-write.
//!
//! `QF_ABV_wide_mul_unsat` asserts `(bvugt (select (store a #x00 (bvmul x y))
//! #x00) #x00000000)`. Preprocessing folds the read-over-write and flips the
//! comparison, so the store keeps `(bvult 0 (bvmul x y))` and the bit-blaster
//! refutes it with the TWO-literal lemma
//! `(cl (not (= x 0)) (not (bvult 0 (bvmul x y))))`. Until this lowering the
//! document printed that lemma over the authored spelling as one `hole`
//! (carcara 1.1.0: `holey`): no checked bit-blast lowering takes a clause of
//! more than one literal, and none takes a printed atom that is not its term.
//!
//! Now the authored text is confined to its `assume` and bridged with stock
//! rules (`pbblast_bvugt`/`pbblast_bvult` for the reversal, `arrays_idx` under
//! `cong` for the read), and the lemma is the complete blast of the
//! conjunction of its atoms, opened by `and_neg`.

use super::{
    carcara_stdout_verdict, extract_asserted_terms, extract_assume_terms,
    refuse_pinned_carcara_misjudgments, require_carcara_or_skip, run_carcara_trust_free,
    solve_unsat_and_get_proof, CarcaraVerdict,
};
use ntest::timeout;
use std::path::Path;

/// `benchmarks/smt/QF_ABV/wide_mul_unsat.smt2`, inlined so the pin does not
/// depend on a corpus a worktree may not carry.
const WIDE_MUL: &str = r#"
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 32)))
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= x #x00000000))
(assert (bvugt (select (store a #x00 (bvmul x y)) #x00) #x00000000))
(check-sat)
"#;

/// The same read without the reversal: `arrays_idx` under `cong` alone.
const WIDE_MUL_ULT: &str = r#"
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 32)))
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= x #x00000000))
(assert (bvult #x00000000 (select (store a #x00 (bvmul x y)) #x00)))
(check-sat)
"#;

fn trust_free_document(problem: &str, label: &str) -> String {
    let proof = solve_unsat_and_get_proof(problem, label);
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "{label}: the document must be hole- and trust-free"
    );
    for rule in ["arrays_idx", "and_neg", "bitblast_mult"] {
        assert!(
            proof.contains(&format!(":rule {rule}")),
            "{label}: expected a `{rule}` step"
        );
    }
    let asserted = extract_asserted_terms(problem);
    for assume in extract_assume_terms(&proof) {
        assert!(
            asserted.contains(&assume),
            "{label}: assume is not a problem premise: {assume}"
        );
    }
    proof
}

#[test]
#[timeout(120_000)]
fn authored_read_over_write_conflict_clause_is_carcara_valid() {
    let proof = trust_free_document(WIDE_MUL, "bv_conflict_clause_wide_mul");
    assert!(proof.contains(":rule pbblast_bvugt"));
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    assert!(run_carcara_trust_free(
        &carcara,
        "bv_conflict_clause_wide_mul",
        WIDE_MUL,
        &proof
    ));

    let proof = trust_free_document(WIDE_MUL_ULT, "bv_conflict_clause_wide_mul_ult");
    assert!(run_carcara_trust_free(
        &carcara,
        "bv_conflict_clause_wide_mul_ult",
        WIDE_MUL_ULT,
        &proof
    ));
}

/// The name of the one step whose line contains `needle`.
fn step_containing<'p>(proof: &'p str, needle: &str) -> &'p str {
    let lines: Vec<&str> = proof.lines().filter(|line| line.contains(needle)).collect();
    let [line] = lines.as_slice() else {
        panic!("`{needle}` is on {} lines, not one", lines.len());
    };
    line.strip_prefix("(step ")
        .and_then(|rest| rest.split_whitespace().next())
        .unwrap_or_else(|| panic!("not a step line: {line}"))
}

/// Pinned Carcara's verdict and stderr under the corpus flags, with NO
/// allowance, in a directory removed afterwards (a refused forgery leaves no
/// debug copy behind).
fn carcara_check(carcara: &Path, problem: &str, proof: &str) -> (CarcaraVerdict, String) {
    refuse_pinned_carcara_misjudgments("bv conflict clause", problem, proof);
    let directory = tempfile::tempdir().expect("temporary Carcara directory");
    let problem_path = directory.path().join("problem.smt2");
    let proof_path = directory.path().join("proof.alethe");
    std::fs::write(&problem_path, problem).expect("write problem");
    std::fs::write(&proof_path, proof).expect("write proof");
    let output = std::process::Command::new(carcara)
        .args(["check", "--expand-let-bindings", "--no-color", "--"])
        .arg(&proof_path)
        .arg(&problem_path)
        .output()
        .expect("run pinned Carcara");
    let stdout = String::from_utf8_lossy(&output.stdout);
    (
        carcara_stdout_verdict(output.status.success(), &stdout),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

/// NEGATIVE TWIN at the checker boundary: the bridge and the opening are
/// re-derived by carcara, not allowed. Reading the write at ANOTHER index, or
/// opening a conjunction over a different atom, is refused AT THAT STEP, by
/// that step's own rule, while the untampered document is `valid`.
#[test]
#[timeout(120_000)]
fn tampered_read_or_opening_is_refused_by_carcara() {
    let proof = trust_free_document(WIDE_MUL, "bv_conflict_clause_tamper");
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let (verdict, stderr) = carcara_check(&carcara, WIDE_MUL, &proof);
    assert_eq!(verdict, CarcaraVerdict::Valid, "untampered: {stderr}");
    let read = "(cl (= (select (store a #x00 (bvmul x y)) #x00) (bvmul x y))) :rule arrays_idx)";
    let opening = "(cl (and (= x #x00000000) ";
    for (needle, tampered, rule) in [
        (
            read,
            "(cl (= (select (store a #x00 (bvmul x y)) #x01) (bvmul x y))) :rule arrays_idx)",
            "arrays_idx",
        ),
        (opening, "(cl (and (= y #x00000000) ", "and_neg"),
    ] {
        assert_eq!(proof.matches(needle).count(), 1, "{needle}");
        let step = step_containing(&proof, needle);
        let forged = proof.replacen(needle, tampered, 1);
        let (verdict, stderr) = carcara_check(&carcara, WIDE_MUL, &forged);
        assert_eq!(verdict, CarcaraVerdict::Invalid, "{tampered}: {stderr}");
        let refusal = format!("checking failed on step '{step}' with rule '{rule}'");
        assert!(stderr.contains(&refusal), "{refusal}: {stderr}");
    }
}

/// NEGATIVE CONTROL: this file's runner refuses, before the checker runs, the
/// pair pinned carcara prints `valid` for only through its `evaluate` defect.
#[test]
#[should_panic(expected = "is not evidence")]
fn the_bv_conflict_clause_runner_refuses_a_document_pinned_carcara_misjudges() {
    carcara_check(
        Path::new("carcara"),
        ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROBLEM,
        ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROOF,
    );
}
