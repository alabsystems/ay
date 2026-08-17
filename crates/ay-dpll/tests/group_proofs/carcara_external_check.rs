// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr)]

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
    if let Ok(path) = std::env::var("CARCARA_PATH") {
        let path = PathBuf::from(path);
        if path.is_file() {
            return Some(path);
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

include!("carcara_external_check/runner.rs");
include!("carcara_external_check/ite_bv.rs");
include!("carcara_external_check/uf_lia.rs");
include!("carcara_external_check/corpus.rs");
include!("carcara_external_check/normalized_bv.rs");

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
