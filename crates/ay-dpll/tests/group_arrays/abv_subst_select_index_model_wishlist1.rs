// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for the ABV invalid-model construction bug (wishlist#1,
//! #abv-select-congruence / #abv-subst-model-retry).
//!
//! Shape: a table read `(select tbl (concat op lhs rhs))` whose index
//! components are pinned by top-level equalities. VariableSubstitution
//! eliminates the components (constant-folding the index), decoupling the
//! ORIGINAL select term from its bit-blasted instance. Substitution recovery
//! then fell back to the select's stale, unconstrained bit-blast value (or a
//! default 0), emitting a model that falsified `(distinct out #x00000000)` —
//! the in-loop validator (or the independent soundness gate on larger
//! instances) fail-closed the genuine SAT to `unknown`.
//!
//! The fix resolves such reads by index-value congruence against the other
//! bit-blasted reads of the same array (fail-closed on conflicts), and a
//! model rejection from the substitution-carrying BV lane triggers ONE
//! preprocessing-free re-solve as a backstop.

use ntest::timeout;

fn results(output: &str) -> Vec<&str> {
    output
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .collect()
}

/// Solve with the executor configured the way the `ay solve FILE` CLI runs it
/// (#w1-cli-path-gap): proof production ON (the CLI synthesizes a default
/// Alethe proof config and calls `set_produce_proofs(true)`, which also turns
/// on parsed-assertion retention) and a wall-clock solve deadline armed
/// (`--timeout`). The plain `common::solve` harness runs a bare
/// `Executor::new()` with neither, so a regression that only manifests under
/// the CLI configuration (e.g. `use_delayed = ... && !proof_enabled` making
/// proof solves take the fully-eager bit-blast path) would pass the plain
/// tests and still break every `ay solve` invocation.
fn solve_cli_parity(smt: &str) -> String {
    let commands =
        ay_frontend::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    let mut exec = ay_dpll::Executor::new();
    exec.set_produce_proofs(true);
    exec.set_deadline(Some(
        std::time::Instant::now() + std::time::Duration::from_millis(60_000),
    ));
    exec.execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT2:\n{smt}"))
        .join("\n")
}

/// Extract a BV hex value from get-value output like `((out #x40400000))`.
fn get_bv_binding(line: &str, name: &str) -> Option<String> {
    let needle = format!("({name} ");
    let start = line.find(&needle)? + needle.len();
    let rest = &line[start..];
    let end = rest.find(')')?;
    Some(rest[..end].trim().to_string())
}

/// Narrow-width variant (BV24 index = concat of three BV8 components) of the
/// model-checker-consumer float-nan table-read shape: fast enough for CI, same decoupling.
#[test]
#[timeout(30_000)]
fn qf_abv_pinned_concat_index_select_model_wishlist1_bv24() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-const tbl (Array (_ BitVec 24) (_ BitVec 32)))
        (declare-const op (_ BitVec 8))
        (declare-const lhs (_ BitVec 8))
        (declare-const rhs (_ BitVec 8))
        (declare-const out (_ BitVec 32))
        (assert (= out (select tbl (concat op (concat lhs rhs)))))
        (assert (= op #x01))
        (assert (= (select tbl (concat #x01 (concat #x3f #x40))) #x40400000))
        (assert (= lhs #x3f))
        (assert (= rhs #x40))
        (assert (distinct out #x00000000))
        (check-sat)
        (get-value (out))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(
        lines[0], "sat",
        "pinned concat-index table read must be sat with a validating model, got: {lines:?}"
    );
    assert_eq!(
        get_bv_binding(lines[1], "out"),
        Some("#x40400000".to_string()),
        "out must equal the pinned table value, got: {lines:?}"
    );
}

/// The original 72-bit concat-index shape (op-tag ++ lhs ++ rhs over BV32
/// operands), exactly the `float_binop_tbl_f32: Array(BV72 -> BV32)` read
/// class from the model-checker-consumer report.
#[test]
#[timeout(60_000)]
fn qf_abv_pinned_concat_index_select_model_wishlist1_bv72() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-const tbl (Array (_ BitVec 72) (_ BitVec 32)))
        (declare-const op (_ BitVec 8))
        (declare-const lhs (_ BitVec 32))
        (declare-const rhs (_ BitVec 32))
        (declare-const out (_ BitVec 32))
        (assert (= out (select tbl (concat op (concat lhs rhs)))))
        (assert (= op #x01))
        (assert (= (select tbl (concat #x01 (concat #x3f800000 #x40000000))) #x40400000))
        (assert (= lhs #x3f800000))
        (assert (= rhs #x40000000))
        (assert (distinct out #x00000000))
        (check-sat)
        (get-value (out))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(
        lines[0], "sat",
        "72-bit pinned concat-index table read must be sat, got: {lines:?}"
    );
    assert_eq!(
        get_bv_binding(lines[1], "out"),
        Some("#x40400000".to_string()),
        "out must equal the pinned table value, got: {lines:?}"
    );
}

/// Whole-index variant: the index variable itself is pinned to a literal
/// concat, so substitution folds `(select tbl idx)` through an eliminated
/// index VARIABLE rather than eliminated components.
#[test]
#[timeout(60_000)]
fn qf_abv_pinned_index_var_select_model_wishlist1() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-const tbl (Array (_ BitVec 72) (_ BitVec 32)))
        (declare-const idx (_ BitVec 72))
        (declare-const out (_ BitVec 32))
        (assert (= out (select tbl idx)))
        (assert (= idx (concat #x01 (concat #x3f800000 #x40000000))))
        (assert (= (select tbl (concat #x01 (concat #x3f800000 #x40000000))) #x40400000))
        (assert (distinct out #x00000000))
        (check-sat)
        (get-value (out))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(
        lines[0], "sat",
        "pinned index-var table read must be sat, got: {lines:?}"
    );
    assert_eq!(
        get_bv_binding(lines[1], "out"),
        Some("#x40400000".to_string()),
        "out must equal the pinned table value, got: {lines:?}"
    );
}

/// CLI-parity (produce-proofs + deadline) variant of the narrow-width shape:
/// `ay solve` always runs with proof production enabled (synthesized-default
/// Alethe config) and a `--timeout` deadline armed, which flips
/// proof-gated branches in the BV pipeline (e.g. `use_delayed` requires
/// `!proof_enabled`, so CLI solves take the fully-eager bit-blast path).
/// The recovery/retry fix must hold in that configuration too.
#[test]
#[timeout(30_000)]
fn qf_abv_pinned_concat_index_select_model_wishlist1_bv24_cli_parity() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-const tbl (Array (_ BitVec 24) (_ BitVec 32)))
        (declare-const op (_ BitVec 8))
        (declare-const lhs (_ BitVec 8))
        (declare-const rhs (_ BitVec 8))
        (declare-const out (_ BitVec 32))
        (assert (= out (select tbl (concat op (concat lhs rhs)))))
        (assert (= op #x01))
        (assert (= (select tbl (concat #x01 (concat #x3f #x40))) #x40400000))
        (assert (= lhs #x3f))
        (assert (= rhs #x40))
        (assert (distinct out #x00000000))
        (check-sat)
        (get-value (out))
    "#;
    let output = solve_cli_parity(smt);
    let lines = results(&output);
    assert_eq!(
        lines[0], "sat",
        "CLI-parity (produce-proofs + deadline) pinned concat-index read must be sat, got: {lines:?}"
    );
    assert_eq!(
        get_bv_binding(lines[1], "out"),
        Some("#x40400000".to_string()),
        "out must equal the pinned table value under CLI-parity config, got: {lines:?}"
    );
}

/// CLI-parity variant of the original 72-bit model-checker-consumer table-read shape —
/// byte-identical to the `w72_basic.smt2` file the CLI battery replays.
#[test]
#[timeout(60_000)]
fn qf_abv_pinned_concat_index_select_model_wishlist1_bv72_cli_parity() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-const tbl (Array (_ BitVec 72) (_ BitVec 32)))
        (declare-const op (_ BitVec 8))
        (declare-const lhs (_ BitVec 32))
        (declare-const rhs (_ BitVec 32))
        (declare-const out (_ BitVec 32))
        (assert (= out (select tbl (concat op (concat lhs rhs)))))
        (assert (= op #x01))
        (assert (= (select tbl (concat #x01 (concat #x3f800000 #x40000000))) #x40400000))
        (assert (= lhs #x3f800000))
        (assert (= rhs #x40000000))
        (assert (distinct out #x00000000))
        (check-sat)
        (get-value (out))
    "#;
    let output = solve_cli_parity(smt);
    let lines = results(&output);
    assert_eq!(
        lines[0], "sat",
        "CLI-parity 72-bit pinned concat-index read must be sat, got: {lines:?}"
    );
    assert_eq!(
        get_bv_binding(lines[1], "out"),
        Some("#x40400000".to_string()),
        "out must equal the pinned table value under CLI-parity config, got: {lines:?}"
    );
}

/// In-script `(set-option :produce-proofs true)` variant: the proof flag can
/// also arrive through the SMT-LIB option (the executor consults the ctx
/// option in `produce_proofs_enabled`), not only through the API setter the
/// CLI uses. Both routes must keep the pinned read sat.
#[test]
#[timeout(30_000)]
fn qf_abv_pinned_concat_index_select_model_wishlist1_bv24_produce_proofs_option() {
    let smt = r#"
        (set-option :produce-proofs true)
        (set-logic QF_ABV)
        (declare-const tbl (Array (_ BitVec 24) (_ BitVec 32)))
        (declare-const op (_ BitVec 8))
        (declare-const lhs (_ BitVec 8))
        (declare-const rhs (_ BitVec 8))
        (declare-const out (_ BitVec 32))
        (assert (= out (select tbl (concat op (concat lhs rhs)))))
        (assert (= op #x01))
        (assert (= (select tbl (concat #x01 (concat #x3f #x40))) #x40400000))
        (assert (= lhs #x3f))
        (assert (= rhs #x40))
        (assert (distinct out #x00000000))
        (check-sat)
        (get-value (out))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(
        lines[0], "sat",
        ":produce-proofs pinned concat-index read must be sat, got: {lines:?}"
    );
    assert_eq!(
        get_bv_binding(lines[1], "out"),
        Some("#x40400000".to_string()),
        "out must equal the pinned table value with :produce-proofs, got: {lines:?}"
    );
}

/// CLI-parity genuine-UNSAT + proof guard: with proofs on (as `ay solve`
/// always runs), the contradictory pin must stay unsat AND the refutation
/// proof must still materialize — the recovery/retry machinery must not
/// starve the proof path.
#[test]
#[timeout(30_000)]
fn qf_abv_pinned_concat_index_select_unsat_proof_guard_wishlist1_cli_parity() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-const tbl (Array (_ BitVec 24) (_ BitVec 32)))
        (declare-const op (_ BitVec 8))
        (declare-const lhs (_ BitVec 8))
        (declare-const rhs (_ BitVec 8))
        (declare-const out (_ BitVec 32))
        (assert (= out (select tbl (concat op (concat lhs rhs)))))
        (assert (= op #x01))
        (assert (= (select tbl (concat #x01 (concat #x3f #x40))) #x40400000))
        (assert (= lhs #x3f))
        (assert (= rhs #x40))
        (assert (distinct out #x40400000))
        (check-sat)
    "#;
    let commands = ay_frontend::parse(smt).expect("parse");
    let mut exec = ay_dpll::Executor::new();
    exec.set_produce_proofs(true);
    exec.set_deadline(Some(
        std::time::Instant::now() + std::time::Duration::from_millis(60_000),
    ));
    let output = exec.execute_all(&commands).expect("execute").join("\n");
    let lines = results(&output);
    assert_eq!(
        lines[0], "unsat",
        "CLI-parity contradictory pinned read must stay unsat, got: {lines:?}"
    );
    // The CLI writes the `.alethe` certificate through exactly this export.
    let alethe = exec
        .try_export_last_proof_alethe_for_problem_scope()
        .expect("unsat under produce-proofs must carry a refutation proof")
        .expect("Alethe export must render");
    assert!(
        alethe.contains("step") || alethe.contains("assume"),
        "exported Alethe proof looks empty: {alethe:?}"
    );
}

/// Genuine-UNSAT guard: the same shape with a contradictory pin must stay
/// unsat — neither the congruence recovery nor the preprocessing-free retry
/// may flip a refutation.
#[test]
#[timeout(30_000)]
fn qf_abv_pinned_concat_index_select_unsat_guard_wishlist1() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-const tbl (Array (_ BitVec 24) (_ BitVec 32)))
        (declare-const op (_ BitVec 8))
        (declare-const lhs (_ BitVec 8))
        (declare-const rhs (_ BitVec 8))
        (declare-const out (_ BitVec 32))
        (assert (= out (select tbl (concat op (concat lhs rhs)))))
        (assert (= op #x01))
        (assert (= (select tbl (concat #x01 (concat #x3f #x40))) #x40400000))
        (assert (= lhs #x3f))
        (assert (= rhs #x40))
        (assert (distinct out #x40400000))
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(
        lines[0], "unsat",
        "contradictory pinned read must stay unsat, got: {lines:?}"
    );
}
