// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The instance-seeded authored equality closure, checked by pinned carcara.
//!
//! Five MODEL_CHECKER_CONSUMER UF controls (`uf_false_matrix`, `uf_false_query`,
//! `uf_nullary_global`, `uf_nested`, `uf_scalar`) answered `unknown` under
//! `:produce-proofs`: the lane that refuted them recorded no derivation, so
//! the strict gate saw an underived `trust` step (`strict UNSAT proof
//! validation failed: step t1 uses unverified trust rule`). The closure now
//! seeds the checked ground instance a matched authored universal yields (its
//! guards discharged by authored roots or by `evaluate`) and closes on an
//! authored disequality or on two distinct constants (`evaluate`).
//!
//! Each fixture is the smallest instance of one of those shapes and must
//! publish a document carcara 1.1.0 checks trust-free as `valid`. Each
//! satisfiable twin differs in exactly the fact the refutation needs and must
//! never publish `unsat`.

use super::Executor;
use super::{
    exact_carcara_verdict, parse, require_carcara_or_skip,
    solve_or_fail_closed_and_maybe_get_proof, solve_unsat_and_get_proof,
};
use ntest::timeout;

/// A matched instance whose guard `(bvult k 9)` is an authored root; the chain
/// ends at the authored `distinct` (the `uf_scalar` shape).
const SYMBOLIC_GUARD: &str = r#"
(set-logic ALL)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const fill (_ BitVec 8))
(declare-const k (_ BitVec 8))
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= fill (f x)))
(assert (bvult k (_ bv9 8)))
(assert (forall ((i (_ BitVec 8))) (=> (bvult i (_ bv9 8)) (= (select a i) (f x)))))
(assert (distinct (select a k) fill))
(check-sat)
"#;

/// A matched instance whose closed guard `(bvult 4 5)` is discharged by
/// `evaluate`; the chain ends at `#b1` and `#b0` (the `uf_false_matrix` shape).
const CLOSED_GUARD: &str = r#"
(set-logic ALL)
(declare-fun g (Bool (_ BitVec 8)) (_ BitVec 1))
(assert (forall ((i (_ BitVec 8))) (=> (bvult i (_ bv5 8)) (= (g false i) (_ bv1 1)))))
(assert (= (g false (_ bv4 8)) (_ bv0 1)))
(check-sat)
"#;

/// No quantifier: a four-edge chain through a nullary function between two
/// distinct 136-bit literals spelled `(_ bvN 136)` (the `uf_nullary_global`
/// shape; the closing `evaluate` has no width ceiling).
const WIDE_CONSTANT_CHAIN: &str = r#"
(set-logic ALL)
(declare-fun s () (_ BitVec 136))
(declare-const v0 (_ BitVec 136))
(declare-const v1 (_ BitVec 136))
(assert (= v0 s))
(assert (= v0 (_ bv0 136)))
(assert (= v1 s))
(assert (= v1 (_ bv5 136)))
(check-sat)
"#;

/// Two binders read off one application; both guards are authored roots
/// (the `uf_nested` shape without its datatype).
const TWO_BINDER_GUARDS: &str = r#"
(set-logic ALL)
(declare-fun h ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(declare-const k (_ BitVec 8))
(declare-const col (_ BitVec 8))
(declare-const c (_ BitVec 8))
(assert (bvult k (_ bv3 8)))
(assert (bvult col (_ bv4 8)))
(assert (forall ((i (_ BitVec 8)) (j (_ BitVec 8)))
  (=> (and (bvult i (_ bv3 8)) (bvult j (_ bv4 8))) (= (h i j) c))))
(assert (distinct (h k col) c))
(check-sat)
"#;

/// Unsat at `i = #xff`, but the only instance's closed guard
/// `(= (bvsub #xff #x01) #xfe)` nests an operator pinned carcara evaluates
/// wrongly (it computes `0`), so no published step may rest on evaluating it.
const NESTED_CLOSED_GUARD: &str = r#"
(set-logic ALL)
(declare-fun g ((_ BitVec 8)) (_ BitVec 8))
(assert (forall ((i (_ BitVec 8))) (=> (= (bvsub i #x01) #xfe) (= (g i) #x01))))
(assert (= (g #xff) #x00))
(check-sat)
"#;

/// Unsat at `i = 64`, and the closure derives it internally, but the authored
/// guard spells its bound through the `define-fun` `lim`, so the `evaluate`
/// that discharges it would not print the conclusion AY checked (carcara runs
/// without `--apply-function-defs`). The closure declines a candidate with a
/// known wire gap, so this must never publish a refused or invalid proof.
const DEFINE_FUN_GUARD: &str = r#"
(set-logic ALL)
(define-fun lim () (_ BitVec 64) (_ bv65 64))
(declare-fun summary (Bool (_ BitVec 64)) (_ BitVec 1))
(assert (forall ((i (_ BitVec 64))) (=> (bvult i lim) (= (summary false i) (_ bv1 1)))))
(assert (= (summary false (_ bv64 64)) (_ bv0 1)))
(check-sat)
"#;

/// `(bvult col 5)` admits `col = 4`, which the universal does not constrain.
const TWO_BINDER_GUARDS_SAT: &str = r#"
(set-logic ALL)
(declare-fun h ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(declare-const k (_ BitVec 8))
(declare-const col (_ BitVec 8))
(declare-const c (_ BitVec 8))
(assert (bvult k (_ bv3 8)))
(assert (bvult col (_ bv5 8)))
(assert (forall ((i (_ BitVec 8)) (j (_ BitVec 8)))
  (=> (and (bvult i (_ bv3 8)) (bvult j (_ bv4 8))) (= (h i j) c))))
(assert (distinct (h k col) c))
(check-sat)
"#;

/// `(bvult k 10)` admits `k = 9`, which the universal does not constrain.
const SYMBOLIC_GUARD_SAT: &str = r#"
(set-logic ALL)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const fill (_ BitVec 8))
(declare-const k (_ BitVec 8))
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= fill (f x)))
(assert (bvult k (_ bv10 8)))
(assert (forall ((i (_ BitVec 8))) (=> (bvult i (_ bv9 8)) (= (select a i) (f x)))))
(assert (distinct (select a k) fill))
(check-sat)
"#;

/// The pinned cell 5 lies outside `(bvult i 5)`.
const CLOSED_GUARD_SAT: &str = r#"
(set-logic ALL)
(declare-fun g (Bool (_ BitVec 8)) (_ BitVec 1))
(assert (forall ((i (_ BitVec 8))) (=> (bvult i (_ bv5 8)) (= (g false i) (_ bv1 1)))))
(assert (= (g false (_ bv5 8)) (_ bv0 1)))
(check-sat)
"#;

/// Both chain ends are the same 136-bit literal.
const WIDE_CONSTANT_CHAIN_SAT: &str = r#"
(set-logic ALL)
(declare-fun s () (_ BitVec 136))
(declare-const v0 (_ BitVec 136))
(declare-const v1 (_ BitVec 136))
(assert (= v0 s))
(assert (= v0 (_ bv0 136)))
(assert (= v1 s))
(assert (= v1 (_ bv0 136)))
(check-sat)
"#;

fn assert_trust_free_valid(label: &str, problem: &str, rules: &[&str]) {
    let proof = solve_unsat_and_get_proof(problem, label);
    for rule in [":rule hole", ":rule trust"] {
        assert!(
            !proof.contains(rule),
            "{label}: the document must carry no `{rule}` step:\n{proof}"
        );
    }
    for rule in rules {
        assert!(
            proof.contains(&format!(":rule {rule}")),
            "{label}: expected a `{rule}` step:\n{proof}"
        );
    }
    if let Some(carcara) = require_carcara_or_skip() {
        let (valid, diagnostic) = exact_carcara_verdict(&carcara, problem, &proof);
        assert!(
            valid,
            "{label}: pinned carcara must check the document trust-free: {diagnostic}\n{proof}"
        );
    }
}

fn proof_mode_verdict(problem: &str) -> String {
    let script = format!("(set-option :produce-proofs true)\n{problem}");
    let commands = parse(&script).expect("fixture parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("fixture runs");
    outputs.first().cloned().unwrap_or_default()
}

#[test]
#[timeout(120_000)]
fn symbolic_guard_instance_publishes_trust_free() {
    assert_trust_free_valid(
        "ground_instance_symbolic_guard",
        SYMBOLIC_GUARD,
        &["forall_inst"],
    );
}

#[test]
#[timeout(120_000)]
fn closed_guard_instance_and_constant_endpoints_publish_trust_free() {
    assert_trust_free_valid(
        "ground_instance_closed_guard",
        CLOSED_GUARD,
        &["forall_inst", "evaluate"],
    );
}

#[test]
#[timeout(120_000)]
fn constant_endpoint_chain_publishes_trust_free() {
    assert_trust_free_valid(
        "ground_wide_constant_chain",
        WIDE_CONSTANT_CHAIN,
        &["eq_transitive", "evaluate"],
    );
}

#[test]
#[timeout(120_000)]
fn two_binder_guarded_instance_publishes_trust_free() {
    assert_trust_free_valid(
        "ground_instance_two_binders",
        TWO_BINDER_GUARDS,
        &["forall_inst"],
    );
}

#[test]
#[timeout(120_000)]
fn satisfiable_twins_never_publish_unsat() {
    for (label, problem) in [
        ("symbolic_guard_sat", SYMBOLIC_GUARD_SAT),
        ("closed_guard_sat", CLOSED_GUARD_SAT),
        ("wide_constant_chain_sat", WIDE_CONSTANT_CHAIN_SAT),
        ("two_binder_guards_sat", TWO_BINDER_GUARDS_SAT),
    ] {
        let verdict = proof_mode_verdict(problem);
        assert_ne!(verdict, "unsat", "{label}: a satisfiable twin was refuted");
    }
}

#[test]
#[timeout(120_000)]
fn nested_closed_guard_never_publishes_a_step_carcara_refutes() {
    let label = "ground_instance_nested_closed_guard";
    let Some(proof) = solve_or_fail_closed_and_maybe_get_proof(NESTED_CLOSED_GUARD, label) else {
        return;
    };
    if let Some(carcara) = require_carcara_or_skip() {
        let (valid, diagnostic) = exact_carcara_verdict(&carcara, NESTED_CLOSED_GUARD, &proof);
        assert!(
            valid,
            "{label}: a published refutation must be carcara-valid: {diagnostic}\n{proof}"
        );
    }
}

#[test]
#[timeout(120_000)]
fn define_fun_guard_never_publishes_a_refused_or_invalid_proof() {
    let label = "ground_instance_define_fun_guard";
    let Some(proof) = solve_or_fail_closed_and_maybe_get_proof(DEFINE_FUN_GUARD, label) else {
        return;
    };
    if let Some(carcara) = require_carcara_or_skip() {
        let (valid, diagnostic) = exact_carcara_verdict(&carcara, DEFINE_FUN_GUARD, &proof);
        assert!(
            valid,
            "{label}: a published refutation must be carcara-valid: {diagnostic}\n{proof}"
        );
    }
}
