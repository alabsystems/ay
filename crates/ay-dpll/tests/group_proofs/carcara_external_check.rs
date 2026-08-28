// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr)]

use ay_core::Sort;
use ay_dpll::api::{Logic, Solver, StrictProofVerdict};
use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;

#[path = "carcara_external_check/folded_atom_assumptions.rs"]
mod folded_atom_assumptions;
#[path = "carcara_external_check/folded_conjunction_assumptions.rs"]
mod folded_conjunction_assumptions;
include!("carcara_external_check/fixtures.rs");
fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root")
        .to_path_buf()
}

fn keep_alethe_artifacts() -> bool {
    ay_core::misc_cli_flags().keep_alethe_artifacts
}

fn find_carcara() -> Option<PathBuf> {
    if let Some(path) = std::env::var_os("CARCARA_PATH") {
        let path = PathBuf::from(path);
        assert!(
            path.is_file(),
            "CARCARA_PATH is configured but does not name a checker file: {}",
            path.display()
        );
        return Some(path);
    }

    if let Some(home) = std::env::var_os("HOME") {
        let candidate = PathBuf::from(home).join(".cargo/bin/carcara");
        if candidate.is_file() {
            return Some(candidate);
        }
    }

    let candidates = [
        workspace_root().join("bin/carcara"),
        workspace_root().join("reference/carcara/target/release/carcara"),
        workspace_root().join("reference/carcara/target/researcher_20/release/carcara"),
        PathBuf::from("/tmp/carcara/target/release/carcara"),
        PathBuf::from("/usr/local/bin/carcara"),
        PathBuf::from("/opt/homebrew/bin/carcara"),
    ];
    for candidate in candidates {
        if candidate.is_file() {
            return Some(candidate);
        }
    }

    let path_var = std::env::var_os("PATH")?;
    for dir in std::env::split_paths(&path_var) {
        let candidate = dir.join("carcara");
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

fn required_carcara_for_corpus() -> PathBuf {
    find_carcara().unwrap_or_else(|| {
        panic!(
            "the canonical external UNSAT corpus requires the real Carcara checker; \
             set CARCARA_PATH or install it with `cargo install --git \
             https://github.com/ufmg-smite/carcara.git`"
        )
    })
}

fn require_carcara_or_skip() -> Option<PathBuf> {
    if let Some(path) = find_carcara() {
        return Some(path);
    }

    assert!(
        std::env::var_os("CI").is_none(),
        "carcara not found. External Alethe verification is mandatory in CI.\n\
         Install: cargo install --git https://github.com/ufmg-smite/carcara.git"
    );

    eprintln!("carcara not found, skipping external Alethe verification");
    None
}

fn required_cargo_home_carcara() -> PathBuf {
    let home = std::env::var_os("HOME").expect("HOME must be set for the production proof gate");
    let path = PathBuf::from(home).join(".cargo/bin/carcara");
    assert!(
        path.is_file(),
        "the production E5 proof gate requires the real checker at {}",
        path.display()
    );
    path
}

fn exact_carcara_verdict(carcara: &Path, problem: &str, proof: &str) -> (bool, String) {
    let directory = tempfile::tempdir().expect("temporary Carcara directory");
    let problem_path = directory.path().join("problem.smt2");
    let proof_path = directory.path().join("proof.alethe");
    std::fs::write(&problem_path, problem).expect("write exact problem");
    std::fs::write(&proof_path, proof).expect("write exact proof");
    let output = std::process::Command::new(carcara)
        .arg("check")
        .arg("--no-color")
        .arg("--")
        .arg(&proof_path)
        .arg(&problem_path)
        .output()
        .expect("run production Carcara checker");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let diagnostic = format!(
        "status={:?}; stdout={}; stderr={}",
        output.status.code(),
        stdout.trim(),
        stderr.trim()
    );
    (
        trust_free_carcara_verdict_is_valid(output.status.success(), &stdout),
        diagnostic,
    )
}

include!("carcara_external_check/runner.rs");
include!("carcara_external_check/ite_bv.rs");
include!("carcara_external_check/uf_lia.rs");
include!("carcara_external_check/corpus.rs");
include!("carcara_external_check/authored_assume.rs");
include!("carcara_external_check/normalized_bv.rs");

/// Production gate for Trust's bounded E5 shift-count contradiction.
///
/// Native strict verification and external Carcara verification are separate
/// verdicts. The latter consumes the exact problem bytes carried beside the
/// proof artifact; both proof tampering and problem/surface substitution must
/// be independently rejected.
#[test]
#[timeout(60_000)]
fn test_e5_shift_exact_artifact_is_native_strict_and_carcara_valid() {
    let carcara = required_cargo_home_carcara();
    let mut solver = Solver::try_new(Logic::QfBv).expect("QF_BV solver");
    solver.set_produce_proofs(true);
    let x = solver.declare_const("x", Sort::bitvec(8));
    let zero = solver.bv_const(0, 8);
    let one = solver.bv_const(1, 8);
    let positive = solver.bvult(zero, x);
    let shifted = solver.bvlshr(x, one);
    let non_strict = solver.bvule(x, shifted);
    let contradiction = solver.and(positive, non_strict);
    solver.assert_term(contradiction);

    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_unsat(),
        "bounded shift contradiction must be UNSAT: {details:?}"
    );
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("E5 UNSAT must export a proof artifact");
    assert!(matches!(
        artifact.strict_verdict,
        StrictProofVerdict::Verified(ref quality) if quality.is_complete()
    ));
    assert!(
        !artifact.alethe.contains(":rule hole") && !artifact.alethe.contains(":rule trust"),
        "external artifact must contain no unchecked rule:\n{}",
        artifact.alethe
    );
    let exact_problem = artifact
        .alethe_problem_smt2
        .as_deref()
        .expect("QF_BV artifact must carry exact checker problem bytes");
    let normalized_shift = "(concat #b0 ((_ extract 7 1) x))";
    assert!(exact_problem.contains(normalized_shift), "{exact_problem}");
    assert!(!exact_problem.contains("bvlshr"), "{exact_problem}");
    assert!(!exact_problem.contains("zero_extend"), "{exact_problem}");

    let (valid, diagnostic) = exact_carcara_verdict(&carcara, exact_problem, &artifact.alethe);
    assert!(
        valid,
        "exact E5 artifact must be Carcara-valid: {diagnostic}"
    );

    let tampered_proof = artifact
        .alethe
        .replacen(":rule bitblast_const", ":rule false", 1);
    assert_ne!(
        tampered_proof, artifact.alethe,
        "proof tamper target missing"
    );
    let (valid, diagnostic) = exact_carcara_verdict(&carcara, exact_problem, &tampered_proof);
    assert!(!valid, "Carcara accepted a tampered proof: {diagnostic}");

    let tampered_problem = exact_problem.replacen("#b00000000", "#b00000001", 1);
    assert_ne!(
        tampered_problem, exact_problem,
        "problem tamper target missing"
    );
    let (valid, diagnostic) = exact_carcara_verdict(&carcara, &tampered_problem, &artifact.alethe);
    assert!(!valid, "Carcara accepted a tampered problem: {diagnostic}");

    // A consumer rebuilding the pre-normalization source formula produces an
    // equivalent SMT proposition, but not the exact assumption surface bound
    // into this Alethe certificate. That pair must be refused.
    let rebuilt_problem = exact_problem.replacen(normalized_shift, "(bvlshr x #x01)", 1);
    assert_ne!(
        rebuilt_problem, exact_problem,
        "normalization-binding target missing"
    );
    let (valid, diagnostic) = exact_carcara_verdict(&carcara, &rebuilt_problem, &artifact.alethe);
    assert!(
        !valid,
        "Carcara accepted proof against consumer-rebuilt problem: {diagnostic}"
    );
}

/// The external-codegen GUARDED-division obligation, verbatim from a captured bridge
/// query. `(and (not (= b 0)) (not (= X X)))` folds to `false` at elaboration
/// and used to export the three-step `assume`/`hole`/`resolution` rescue —
/// `holey`, never `valid`. `promote_and_self_eq_contradiction_collapse` must
/// make it fully re-derivable by an INDEPENDENT checker.
///
/// Verified against the untouched problem text, never a re-derived assumption
/// scope: replaying AY's own printed assumes as the problem cannot detect an
/// `assume` that fails to match the real input.
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_guarded_self_equality_division() {
    let problem = r#"
(set-logic QF_BV)
(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))
(assert (and (not (= b (_ bv0 32))) (not (= (bvsub a (bvmul (bvudiv a b) b)) (bvsub a (bvmul (bvudiv a b) b))))))
(check-sat)
"#;
    let proof = solve_unsat_and_get_proof(problem, "guarded_self_eq_division");
    assert!(
        !proof.contains(":rule hole"),
        "guarded self-equality must not publish an unproved step:\n{proof}"
    );
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    assert!(
        run_carcara_trust_free(&carcara, "guarded_self_eq_division", problem, &proof),
        "guarded self-equality proof must be trust-free verifiable by carcara"
    );
}

/// The external-codegen memory-image obligation: a QF_ABV self-equality over
/// `select`/`store`/const-array terms. Two independent gaps kept this `holey`:
/// the faithful rebuilders had no array fragment, and AY's internal
/// `(const-array v)` spelling does not parse as SMT-LIB. Both are on the path
/// this test exercises, and the const-array one can only be caught by an
/// external checker — AY's own strict checker accepts the internal spelling.
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_array_backed_self_equality() {
    let problem = r#"
(set-logic QF_ABV)
(declare-const base (_ BitVec 64))
(declare-const val (_ BitVec 64))
(declare-const fill (_ BitVec 8))
(assert (not (= ((_ zero_extend 56) (select (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) fill) (bvadd base (_ bv8 64)) ((_ extract 7 0) val)) base))
                ((_ zero_extend 56) (select (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) fill) (bvadd base (_ bv8 64)) ((_ extract 7 0) val)) base)))))
(check-sat)
"#;
    let proof = solve_unsat_and_get_proof(problem, "array_self_eq");
    assert!(
        !proof.contains(":rule hole"),
        "array self-equality must not publish an unproved step:\n{proof}"
    );
    assert!(
        !proof.contains("(const-array"),
        "AY's internal constant-array spelling does not parse as SMT-LIB:\n{proof}"
    );
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    assert!(
        run_carcara_trust_free(&carcara, "array_self_eq", problem, &proof),
        "array self-equality proof must be trust-free verifiable by carcara"
    );
}
