// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::executor_types::{SolveResult, UnknownReason};
use crate::Executor;
use ay_core::Sort;
use ay_frontend::parse;
use num_bigint::BigInt;

fn run_script(input: &str) -> Vec<String> {
    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("SMT-LIB script should execute")
}

// --- Core check-sat path tests ---

#[test]
fn qf_abv_scalar_budget_targets_select_dense_store_ssa_8140() {
    assert!(Executor::should_budget_scalar_variable_substitution(
        214, 3821
    ));
    assert!(!Executor::should_budget_scalar_variable_substitution(
        256, 1877
    ));
    assert!(!Executor::should_budget_scalar_variable_substitution(
        3200, 0
    ));
}

#[test]
fn bv_model_validation_failure_degrades_to_unknown_with_diagnostics() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_var("x", Sort::bitvec(4));
    let one = exec.ctx.terms.mk_bitvec(BigInt::from(1u64), 4);
    let assertion = exec.ctx.terms.mk_eq(x, one);

    let result = exec
        .finalize_bv_model_validation_failure(ay_bv::BvValidationError {
            assertion_index: 0,
            assertion,
        })
        .expect("BV model validation failure should fail closed");

    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(exec.last_result(), Some(&SolveResult::Unknown));
    assert_eq!(exec.get_reason_unknown(), Some(UnknownReason::Incomplete));
    assert_eq!(
        exec.statistics().get_int("model_validation_failures"),
        Some(1)
    );
    assert_eq!(
        exec.statistics()
            .get_int("model_validation.bv.failure.assertion_index"),
        Some(0)
    );
    assert_eq!(
        exec.statistics()
            .get_string("model_validation.bv.failure.kind"),
        Some("false-evaluation")
    );
    assert_eq!(
        exec.statistics().get_string("unknown.reason"),
        Some("incomplete")
    );
    assert_eq!(
        exec.statistics().get_string("unknown.phase"),
        Some("model-validation")
    );
    assert_eq!(
        exec.statistics().get_string("unknown.cost_center"),
        Some("bv-model-validation")
    );
    assert_eq!(
        exec.statistics().get_string("unknown.detail"),
        Some("BV SAT model validation false-evaluation at assertion 0")
    );
    assert!(
        exec.statistics()
            .get_string("model_validation.bv.failure.term")
            .is_some_and(|term| term.contains("#x1")),
        "expected failing BV assertion term in diagnostics, statistics={:?}",
        exec.statistics()
    );
}

#[test]
fn bv_sat_simple_equality() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x0A))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn bv_check_sat_applies_random_seed_to_sat() {
    let input = r#"
        (set-logic QF_BV)
        (set-option :random-seed 42)
        (declare-const x (_ BitVec 8))
        (assert (= x #x0A))
        (check-sat)
    "#;

    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("SMT-LIB script should execute");

    assert_eq!(outputs, vec!["sat"]);
    assert_eq!(exec.last_applied_sat_random_seed_for_test(), Some(42));
}

#[test]
fn bv_unsat_contradictory_values() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x01))
        (assert (= x #x02))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn bv_sat_arithmetic() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= (bvadd x y) #x0A))
        (assert (= x #x05))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn bv_unsat_overflow() {
    // For 8-bit: bvadd wraps, so x + 1 = 0 means x = 255
    // Combined with x < 200 (unsigned), this should be unsat
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= (bvadd x #x01) #x00))
        (assert (bvult x #xC8))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn bv_empty_assertions_sat() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 32))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn bv_sat_bitwise_ops() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= (bvand x #x0F) #x05))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

// --- Incremental / push-pop tests ---

#[test]
fn incremental_bv_push_pop_roundtrip() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x01))
        (push 1)
        (assert (= x #x02))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    assert_eq!(run_script(input), vec!["unsat", "sat"]);
}

#[test]
fn incremental_bv_persistent_sat_inherits_random_seed() {
    let input = r#"
        (set-logic QF_BV)
        (set-option :random-seed 42)
        (declare-const x (_ BitVec 8))
        (push 1)
        (assert (= x #x01))
        (check-sat)
    "#;

    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("SMT-LIB script should execute");

    assert_eq!(outputs, vec!["sat"]);

    let state = exec
        .incr_bv_state
        .as_ref()
        .expect("incremental BV state should exist");
    let solver = state
        .persistent_sat
        .as_ref()
        .expect("expected incremental BV to initialize a persistent SAT solver");
    assert_eq!(solver.random_seed(), 42);
}

#[test]
fn incremental_abv_persistent_sat_inherits_random_seed() {
    let input = r#"
        (set-logic QF_ABV)
        (set-option :random-seed 42)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (push 1)
        (assert (= (select a #x01) #x2A))
        (check-sat)
    "#;

    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("incremental ABV script should execute");

    assert_eq!(outputs, vec!["sat"]);

    let state = exec
        .incr_bv_state
        .as_ref()
        .expect("incremental ABV state should exist");
    let solver = state
        .persistent_sat
        .as_ref()
        .expect("expected incremental ABV to initialize a persistent SAT solver");
    assert_eq!(solver.random_seed(), 42);
}

#[test]
fn incremental_ufbv_persistent_sat_inherits_random_seed() {
    let input = r#"
        (set-logic QF_UFBV)
        (set-option :random-seed 42)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (push 1)
        (assert (= (f x) #x2A))
        (check-sat)
    "#;

    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("incremental UFBV script should execute");

    assert_eq!(outputs, vec!["sat"]);

    let state = exec
        .incr_bv_state
        .as_ref()
        .expect("incremental UFBV state should exist");
    let solver = state
        .persistent_sat
        .as_ref()
        .expect("expected incremental UFBV to initialize a persistent SAT solver");
    assert_eq!(solver.random_seed(), 42);
}

#[test]
fn incremental_aufbv_persistent_sat_inherits_random_seed() {
    let input = r#"
        (set-logic QF_AUFBV)
        (set-option :random-seed 42)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const x (_ BitVec 8))
        (push 1)
        (assert (= (select a x) (f x)))
        (check-sat)
    "#;

    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("incremental AUFBV script should execute");

    assert_eq!(outputs, vec!["sat"]);

    let state = exec
        .incr_bv_state
        .as_ref()
        .expect("incremental AUFBV state should exist");
    let solver = state
        .persistent_sat
        .as_ref()
        .expect("expected incremental AUFBV to initialize a persistent SAT solver");
    assert_eq!(solver.random_seed(), 42);
}

#[test]
fn incremental_bv_contradiction_after_push_pop_cycle() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x01))
        (push 1)
        (assert (bvugt x #x00))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= x #x02))
        (check-sat)
        (pop 1)
    "#;
    let result = run_script(input);
    assert_eq!(
        result,
        vec!["sat", "unsat"],
        "x=#x01 and x=#x02 should be UNSAT after push/pop cycle, got {result:?}"
    );
}

#[test]
fn incremental_bv_nested_push_pop() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x01))
        (push 1)
        (assert (bvugt x #x00))
        (push 1)
        (assert (= x #x02))
        (check-sat)
        (pop 1)
        (check-sat)
        (pop 1)
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat", "sat", "sat"]);
}

#[test]
fn incremental_bv_empty_assertions_are_sat() {
    let input = r#"
        (set-logic QF_BV)
        (push 1)
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    assert_eq!(run_script(input), vec!["sat", "sat"]);
}

/// Regression test for #5441: incremental BV path missing equality congruence axioms.
#[test]
fn incremental_bv_eq_congruence_basic_5441() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const a (_ BitVec 8))
        (declare-const b (_ BitVec 8))
        (assert (= a b))
        (push 1)
        (assert (= a #x05))
        (assert (not (= b #x05)))
        (check-sat)
        (pop 1)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

/// #5441: congruence axioms survive push/pop.
#[test]
fn incremental_bv_eq_congruence_push_pop_5441() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const a (_ BitVec 8))
        (declare-const b (_ BitVec 8))
        (assert (= a b))
        (push 1)
        (assert (= a #x05))
        (assert (not (= b #x05)))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat", "sat"]);
}

/// #5441: ITE-based congruence in incremental mode.
#[test]
fn incremental_bv_eq_congruence_ite_5441() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const a (_ BitVec 8))
        (declare-const b (_ BitVec 8))
        (declare-const r1 (_ BitVec 8))
        (declare-const r2 (_ BitVec 8))
        (assert (= a b))
        (push 1)
        (assert (= r1 (ite (= a #x05) #x01 #x00)))
        (assert (= r2 (ite (= b #x05) #x01 #x00)))
        (assert (not (= r1 r2)))
        (check-sat)
        (pop 1)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

// --- BV JIT integration tests (#8275) ---
// These tests exercise BV solving with formulas large enough to trigger JIT
// compilation (32-bit widths produce ~200+ ternary gate clauses).

#[test]
fn bv_jit_32bit_xor_sat() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 32))
        (declare-const y (_ BitVec 32))
        (assert (= (bvxor x y) #xDEADBEEF))
        (assert (= x #x12345678))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn bv_jit_32bit_contradiction_unsat() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 32))
        (declare-const y (_ BitVec 32))
        (assert (= (bvand x y) #xFFFFFFFF))
        (assert (= (bvor x y) #x00000000))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn bv_jit_multi_op_sat() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const a (_ BitVec 32))
        (declare-const b (_ BitVec 32))
        (declare-const c (_ BitVec 32))
        (assert (= a #x0000FFFF))
        (assert (= b #xFFFF0000))
        (assert (= c (bvxor a b)))
        (assert (= c #xFFFFFFFF))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn bv_jit_ite_mux_gates() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const sel Bool)
        (declare-const a (_ BitVec 32))
        (declare-const b (_ BitVec 32))
        (declare-const result (_ BitVec 32))
        (assert (= a #xAAAAAAAA))
        (assert (= b #x55555555))
        (assert (= result (ite sel a b)))
        (assert (= result #xAAAAAAAA))
        (assert sel)
        (check-sat)
    "#;
    let results = run_script(input);
    assert!(
        results == vec!["sat"] || results == vec!["unknown"],
        "expected sat or unknown, got {results:?}"
    );
}

#[test]
fn bv_jit_threshold_unsat() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 32))
        (declare-const y (_ BitVec 32))
        (declare-const z (_ BitVec 32))
        (assert (= z (bvadd x y)))
        (assert (= z (bvsub x y)))
        (assert (= x #x00000001))
        (assert (= y #x00000001))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

// --- QF_ABV (arrays + bitvectors) tests for EXTERNAL_CODEGEN GPU/memory encoding (#8512) ---

#[test]
fn abv_row1_read_after_write_same_index() {
    // ROW1: select(store(a, i, v), i) = v
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem (Array (_ BitVec 64) (_ BitVec 8)))
        (declare-const addr (_ BitVec 64))
        (assert (= (select (store mem addr #x42) addr) #x42))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn abv_row1_unsat_contradiction() {
    // ROW1: select(store(a, i, v), i) must equal v; asserting otherwise is UNSAT.
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem (Array (_ BitVec 32) (_ BitVec 8)))
        (declare-const addr (_ BitVec 32))
        (assert (not (= (select (store mem addr #xAB) addr) #xAB)))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn abv_row2_read_at_different_index() {
    // ROW2: i != j -> select(store(a, i, v), j) = select(a, j)
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem (Array (_ BitVec 32) (_ BitVec 8)))
        (declare-const i (_ BitVec 32))
        (declare-const j (_ BitVec 32))
        (assert (distinct i j))
        (assert (not (= (select (store mem i #xFF) j) (select mem j))))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn abv_row2_materializes_nested_store_base_reads() {
    // The top-level ROW2 obligation needs select(inner_store, j), which is
    // not present syntactically in the input.
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const j (_ BitVec 8))
        (assert (distinct j #x01))
        (assert (distinct j #x02))
        (assert (= (select mem j) #x11))
        (assert (not (=
            (select (store (store mem #x01 #xaa) #x02 #xbb) j)
            #x11)))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn abv_functional_consistency() {
    // FC: i = j -> select(a, i) = select(a, j)
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 32) (_ BitVec 8)))
        (declare-const i (_ BitVec 32))
        (declare-const j (_ BitVec 32))
        (assert (= i j))
        (assert (not (= (select a i) (select a j))))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn abv_byte_addressed_memory_4_stores() {
    // EXTERNAL_CODEGEN pattern: 4-byte store chain with constant offsets
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem (Array (_ BitVec 64) (_ BitVec 8)))
        (declare-const base (_ BitVec 64))
        (assert (=
            (select
                (store (store (store (store mem
                    base #xDE)
                    (bvadd base #x0000000000000001) #xAD)
                    (bvadd base #x0000000000000002) #xBE)
                    (bvadd base #x0000000000000003) #xEF)
                base)
            #xDE))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn abv_non_aliasing_memory_regions() {
    // EXTERNAL_CODEGEN pattern: two pointers to non-overlapping memory regions
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem (Array (_ BitVec 64) (_ BitVec 8)))
        (declare-const p0 (_ BitVec 64))
        (declare-const p1 (_ BitVec 64))
        (assert (bvugt (bvsub p1 p0) #x0000000000000003))
        (define-fun mem1 () (Array (_ BitVec 64) (_ BitVec 8))
            (store mem p0 #x42))
        (assert (= (select mem1 p1) (select mem p1)))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn abv_aliasing_detection_unsat() {
    // If p0 = p1, writing at p0 and asserting original value at p1 is UNSAT
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem (Array (_ BitVec 64) (_ BitVec 8)))
        (declare-const p0 (_ BitVec 64))
        (declare-const p1 (_ BitVec 64))
        (assert (= p0 p1))
        (assert (= (select mem p0) #x00))
        (assert (= (select (store mem p0 #xFF) p1) #x00))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn abv_incremental_push_pop() {
    // Incremental QF_ABV with push/pop
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (push 1)
        (assert (= (select a #x01) #x2A))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= (select a #x01) #x2A))
        (assert (not (= (select a #x01) #x2A)))
        (check-sat)
        (pop 1)
    "#;
    assert_eq!(run_script(input), vec!["sat", "unsat"]);
}

#[test]
fn abv_const_array() {
    // Const array: all elements have the same value
    let input = r#"
        (set-logic QF_ABV)
        (declare-const idx (_ BitVec 16))
        (assert (= (select ((as const (Array (_ BitVec 16) (_ BitVec 8))) #xFF) idx) #xFF))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn abv_store_forward_with_symbolic_index() {
    // EXTERNAL_CODEGEN pattern: store at symbolic index, read at same symbolic expression
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem (Array (_ BitVec 32) (_ BitVec 8)))
        (declare-const base (_ BitVec 32))
        (declare-const offset (_ BitVec 32))
        (define-fun addr () (_ BitVec 32) (bvadd base offset))
        (assert (= (select (store mem addr #xAB) (bvadd base offset)) #xAB))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn abv_wide_bitvector_index() {
    // Arrays with wide BV indices (128-bit)
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem (Array (_ BitVec 128) (_ BitVec 64)))
        (declare-const addr (_ BitVec 128))
        (declare-const val (_ BitVec 64))
        (assert (= val #x00000000DEADBEEF))
        (assert (= (select (store mem addr val) addr) val))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn abv_multiple_arrays_independent() {
    // Two independent arrays: stores to one don't affect the other
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem1 (Array (_ BitVec 32) (_ BitVec 8)))
        (declare-const mem2 (Array (_ BitVec 32) (_ BitVec 8)))
        (declare-const addr (_ BitVec 32))
        (assert (= (select mem1 addr) #x00))
        (assert (= (select (store mem2 addr #xFF) addr) #xFF))
        (assert (= (select mem1 addr) #x00))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

// --- #12: derived array equality must reach UF congruence (Nelson-Oppen gap) ---

#[test]
fn aufbv_derived_array_eq_propagates_to_uf_congruence() {
    // The store is a no-op: store(b, i, select a i) with select a i = select b i
    // means a = b extensionally. So h(a) must equal h(b), contradicting the
    // disequality. Previously wrong-SAT because the derived array equality
    // never reached the UF (h) congruence layer.
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-fun h ((Array (_ BitVec 1) (_ BitVec 1))) (_ BitVec 1))
        (declare-fun a () (Array (_ BitVec 1) (_ BitVec 1)))
        (declare-fun b () (Array (_ BitVec 1) (_ BitVec 1)))
        (declare-fun i () (_ BitVec 1))
        (assert (= (select a i) (select b i)))
        (assert (= a (store b i (select a i))))
        (assert (distinct (h a) (h b)))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn aufbv_direct_array_eq_with_uf_unsat() {
    // Direct array equality + UF disequality: a = b forces h(a) = h(b),
    // contradicting distinct. Must stay unsat.
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-fun h ((Array (_ BitVec 1) (_ BitVec 1))) (_ BitVec 1))
        (declare-fun a () (Array (_ BitVec 1) (_ BitVec 1)))
        (declare-fun b () (Array (_ BitVec 1) (_ BitVec 1)))
        (assert (= a b))
        (assert (distinct (h a) (h b)))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn aufbv_distinct_arrays_with_uf_stays_sat() {
    // Arrays genuinely differ: h(a) != h(b) is consistent. Reifying the
    // (= a b) atom for congruence must NOT over-constrain this to unsat.
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-fun h ((Array (_ BitVec 1) (_ BitVec 1))) (_ BitVec 1))
        (declare-fun a () (Array (_ BitVec 1) (_ BitVec 1)))
        (declare-fun b () (Array (_ BitVec 1) (_ BitVec 1)))
        (assert (distinct a b))
        (assert (distinct (h a) (h b)))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn aufbv_store_noop_array_diseq_unsat_no_uf() {
    // Store no-op derives a = b directly; with (distinct a b) and no UF this
    // already worked. Guards against regressing the array-only path.
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-fun a () (Array (_ BitVec 1) (_ BitVec 1)))
        (declare-fun b () (Array (_ BitVec 1) (_ BitVec 1)))
        (declare-fun i () (_ BitVec 1))
        (assert (= (select a i) (select b i)))
        (assert (= a (store b i (select a i))))
        (assert (distinct a b))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn aufbv_predicate_over_arrays_store_noop_unsat() {
    // Bool-return UF (predicate) over arrays: p(a) and (not (p b)) with a = b
    // derived from the store no-op must be unsat via predicate congruence.
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-fun p ((Array (_ BitVec 2) (_ BitVec 2))) Bool)
        (declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
        (declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
        (declare-fun i () (_ BitVec 2))
        (assert (= (select a i) (select b i)))
        (assert (= a (store b i (select a i))))
        (assert (and (p a) (not (p b))))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}
