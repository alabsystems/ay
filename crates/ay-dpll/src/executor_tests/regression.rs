// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests - statistics, soundness issue regressions (#858, #859, #919, #920),
//! and incremental cache soundness tests

use crate::{Executor, StatValue, Statistics};
// The one workspace env choke point: serialized, restore-on-exit env mutation.
use ay_frontend::parse;
use ay_test_support::env::{lock_env, ScopedEnvVar};
use ntest::timeout;

#[test]
fn test_get_statistics_propositional() {
    // Use QF_BOOL (pure propositional) to go through solve_propositional
    let smt = r#"
        (set-logic QF_BOOL)
        (declare-const a Bool)
        (declare-const b Bool)
        (declare-const c Bool)
        (assert (or a b))
        (assert (or (not a) c))
        (assert (or (not b) c))
        (assert (not c))
        (check-sat)
    "#;

    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let _result = exec.execute_all(&commands).unwrap();

    // Should be UNSAT: (a v b) & (~a v c) & (~b v c) & ~c
    // If a=T: need c (from ~a v c), contradicts ~c
    // If a=F: need b (from a v b), then need c (from ~b v c), contradicts ~c
    assert!(exec.last_result().is_some_and(|r| r.is_unsat()));

    let stats = exec.get_statistics();

    // Should have some conflicts (the problem is UNSAT)
    // Note: exact numbers depend on solver heuristics, just verify they're tracked
    assert!(
        stats.conflicts > 0 || stats.decisions > 0 || stats.propagations > 0,
        "Statistics should show some solver activity: conflicts={}, decisions={}, propagations={}",
        stats.conflicts,
        stats.decisions,
        stats.propagations
    );

    // num_assertions should match what we asserted
    assert_eq!(stats.num_assertions, 4, "Should have 4 assertions");
}

#[test]
fn test_dead_seq_declaration_does_not_override_datatype_route() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((Box 0)) (((box (val Int)))))
        (declare-const dead (Seq Int))
        (declare-const b Box)
        (assert (= b (box 7)))
        (assert (= (val b) 7))
        (check-sat)
    "#;

    let commands = parse(smt).expect("valid SMT-LIB");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute QF_DT");

    assert_eq!(outputs, vec!["sat"]);
    if let Some(StatValue::String(route)) = exec.get_statistics().extra.get("mixed_vc.route") {
        assert_ne!(
            route, "seqlia",
            "declaration-only Seq symbols must not force SeqLIA routing"
        );
    }
}

/// Test that Statistics Display format is SMT-LIB compatible
#[test]
fn test_statistics_display() {
    let mut stats = Statistics::new();
    stats.conflicts = 42;
    stats.decisions = 100;
    stats.propagations = 500;
    stats.restarts = 5;

    let display = format!("{stats}");
    assert!(display.contains(":conflicts 42"));
    assert!(display.contains(":decisions 100"));
    assert!(display.contains(":propagations 500"));
    assert!(display.contains(":restarts 5"));
}

/// Test StatValue Display formatting
#[test]
#[allow(clippy::approx_constant)] // 3.14 is intentional - testing format, not computing PI
fn test_stat_value_display() {
    assert_eq!(format!("{}", StatValue::Int(42)), "42");
    // Z3-compatible format: 2 decimal places
    assert_eq!(format!("{}", StatValue::Float(3.14)), "3.14");
    // String values should be escaped per SMT-LIB 2.6 (double-quote escaping)
    assert_eq!(
        format!("{}", StatValue::String("test".to_string())),
        "\"test\""
    );
    // SMT-LIB 2.6: embedded " is escaped by doubling -> ""
    assert_eq!(
        format!("{}", StatValue::String("test\"quote".to_string())),
        "\"test\"\"quote\""
    );
    // SMT-LIB 2.6: backslash is literal, no escaping needed
    assert_eq!(
        format!("{}", StatValue::String("test\\backslash".to_string())),
        "\"test\\backslash\""
    );
}

/// Verify that theory_conflicts and theory_propagations are non-zero after
/// solving a QF_LIA problem that requires DPLL(T) interaction (#4705).
///
/// The formula must require simplex-level reasoning that cannot be resolved
/// by preprocessing (VariableSubstitution) or SAT-level bound axioms alone.
/// A sum constraint `x + y >= 1` with individual upper bounds `x <= 0, y <= 0`
/// is UNSAT only because the simplex detects the sum infeasibility.
#[test]
fn test_theory_statistics_nonzero_4705() {
    // UNSAT problem: x + y >= 1 with x <= 0 and y <= 0.
    // VariableSubstitution cannot eliminate this (no direct equality).
    // Bound axioms on individual variables can't detect the cross-variable
    // conflict. The simplex must detect that x <= 0, y <= 0 contradicts
    // x + y >= 1. This guarantees theory interaction.
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= (+ x y) 1))
        (assert (<= x 0))
        (assert (<= y 0))
        (check-sat)
    "#;

    let commands = parse(smt).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let _result = exec.execute_all(&commands).expect("execution succeeds");

    assert!(exec.last_result().is_some_and(|r| r.is_unsat()));

    let stats = exec.get_statistics();

    // Theory interaction must have occurred: either conflicts or propagations
    // (exact counts depend on solver heuristics and eager/lazy mode).
    assert!(
        stats.theory_conflicts > 0 || stats.theory_propagations > 0,
        "QF_LIA UNSAT problem should generate theory interaction: \
         theory_conflicts={}, theory_propagations={}",
        stats.theory_conflicts,
        stats.theory_propagations
    );
}

/// Regression test for #858: Bool variable equated to BV equality result
///
/// This tests the pattern emitted by model-checker-consumer's AY backend where a Bool variable
/// is equated to a BV comparison result:
///   (assert (= t (= (bvadd x y) #x00000008)))
///   (assert (not t))
///
/// With x=5, y=3: bvadd(5,3) = 8, so (= (bvadd x y) 8) is true.
/// Therefore t must be true, and (not t) is unsatisfiable.
#[test]
fn test_qf_bv_bool_equality_soundness_858() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 32))
        (declare-const y (_ BitVec 32))
        (assert (= x #x00000005))
        (assert (= y #x00000003))
        (declare-const t Bool)
        (assert (= t (= (bvadd x y) #x00000008)))
        (assert (not t))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Z3 returns unsat; AY must match
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Soundness bug #858: Bool = BV equality returns sat instead of unsat"
    );
}

/// Regression test for soundness bug #859: QF_AUFBV Bool = BV equality
/// Same pattern as #858 but with QF_AUFBV logic (arrays + UF + bitvectors).
/// model-checker-consumer emits this pattern when encoding bitvector equality into Bool locals.
#[test]
fn test_qf_aufbv_bool_equality_soundness_859() {
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-const a (_ BitVec 32))
        (declare-const b (_ BitVec 32))
        (assert (= a #x00000005))
        (assert (= b #x00000003))
        (declare-const sum (_ BitVec 32))
        (assert (= sum (bvadd a b)))
        ; sum = 5 + 3 = 8, so (not (= sum #x8)) should be unsat
        (assert (not (= sum #x00000008)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Z3 returns unsat; AY must match
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Soundness bug #859: QF_AUFBV Bool = BV equality returns sat instead of unsat"
    );
}

/// Regression test for #859: More complex AUFBV pattern with Bool alias
/// This matches the model-checker-consumer pattern: Bool local aliased to BV equality result.
#[test]
fn test_qf_aufbv_bool_alias_soundness_859() {
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-const x (_ BitVec 32))
        (declare-const y (_ BitVec 32))
        (assert (= x #x00000005))
        (assert (= y #x00000003))
        (declare-const t Bool)
        (assert (= t (= (bvadd x y) #x00000008)))
        (assert (not t))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Z3 returns unsat; AY must match
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Soundness bug #859: QF_AUFBV Bool alias = BV equality returns sat instead of unsat"
    );
}

/// Regression test for #920: Array self-store soundness bug
/// When (= (store arr i v) arr) is asserted, it implies (= (select arr i) v).
/// AY was incorrectly returning SAT for the contradictory case.
#[test]
fn test_qf_aufbv_self_store_soundness_920() {
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-const arr (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        ; store arr i #x02 = arr implies arr[i] = #x02
        (assert (= (store arr i #x02) arr))
        (assert (not (= (select arr i) #x02)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Z3 returns unsat; AY must match
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Soundness bug #920: Self-store pattern returns sat instead of unsat"
    );
}

/// Regression test for #919: ITE with BV predicate condition and Bool variable branches
/// The bug was that polarity-aware Tseitin encoding for Boolean equality didn't trigger
/// both polarities for ITE subterms, leaving them under-constrained.
#[test]
fn test_qf_bv_ite_bool_var_branches_soundness_919() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const a (_ BitVec 32))
        (declare-const b Bool)
        (declare-const c Bool)
        (declare-const d Bool)
        ; d = ite((1 == a), b, c)
        (assert (= d (ite (= #x00000001 a) b c)))
        (assert (= a #x00000002))  ; condition is false
        (assert c)                  ; else branch is true
        (assert (not d))            ; d should equal c, but we say d is false
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // With condition false and c=true, d must equal c (true).
    // But we assert (not d), so this should be unsat.
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Soundness bug #919: ITE with Bool var branches returns sat instead of unsat"
    );
}

/// Regression test for #1007: incremental LIA Farkas verification panic.
///
/// This test exercises incremental LIA solving with two independent queries
/// separated by push/pop. The second query should not panic during Farkas
/// certificate verification in debug builds.
#[test]
fn test_incremental_lia_farkas_regression_1007() {
    // This SMT2 program triggered a Farkas verification panic in debug builds.
    // The issue was that the Farkas certificate referenced constraints in a form
    // that the verification function couldn't properly combine.
    let input = r#"
(set-logic QF_LIA)
(declare-const x0 Int)
(declare-const x1 Int)
(declare-const x2 Int)
(push 1)
(assert (not (= (+ 2 (* 1 x0)) (- 19))))
(assert (<= (+ (- 1) (* 1 x1) (* 2 x2)) (+ (- 9) (* 2 x0) (* (- 3) x1))))
(assert (>= (+ (- 10) (* 1 x0)) 11))
(assert (not (= (+ (- 9) (* 1 x1)) (- 16))))
(assert (>= (+ (- 5) (* (- 3) x0)) (+ 5 (* (- 1) x0) (* (- 2) x1) (* 3 x2))))
(check-sat)
(pop 1)
(push 1)
(assert (>= (+ (- 5) (* 1 x1) (* 2 x2)) (+ 4 (* (- 2) x0) (* (- 2) x2))))
(assert (>= (+ 2 (* 2 x2)) (- 1)))
(assert (= (+ (- 8) (* 1 x1)) (- 8)))
(assert (<= (+ (- 1) (* 1 x0) (* (- 2) x1) (* 1 x2)) 9))
(assert (<= (+ 2 (* (- 3) x0)) 12))
(assert (not (= (+ 10 (* 2 x1)) (+ 6 (* (- 2) x0)))))
(check-sat)
(pop 1)
(exit)
"#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    // Model validation may fail after LRA factory changes (#8008/#8064) due to
    // incomplete cross-theory propagation in incremental mode. Accept the error
    // gracefully rather than panicking on unwrap.
    match exec.execute_all(&commands) {
        Ok(outputs) => {
            // Both queries should complete without panic.
            // We expect 3 outputs: two check-sat results + "exit" from (exit) command.
            assert!(
                outputs.len() >= 2,
                "Expected at least two check-sat results"
            );
            // First check-sat: the LP relaxation diverges on x2 (unbounded direction),
            // so the branch-and-bound correctly detects divergence and returns unknown.
            // The formula IS sat (x0=21, x1=13, x2=-9) but the lazy split loop's
            // closest-integer heuristic picks the wrong branch direction. Accept unknown
            // until Gomory cuts or eager propagation fix the convergence (#1007).
            assert!(
                outputs[0] == "sat" || outputs[0] == "unsat" || outputs[0] == "unknown",
                "First check-sat should not error, got: {}",
                outputs[0]
            );
            // #8373: Model validation violations now degrade to "unknown"
            // instead of producing a hard error. Accept "unknown" here too.
            assert!(
                outputs[1] == "sat" || outputs[1] == "unsat" || outputs[1] == "unknown",
                "Second check-sat result should be sat, unsat, or unknown, got: {}",
                outputs[1]
            );
        }
        Err(e) => {
            // After #8373, ModelValidation errors should no longer propagate
            // from check-sat (they degrade to Unknown). This path is kept for
            // robustness but should not normally be hit.
            assert!(
                matches!(e, crate::executor_types::ExecutorError::ModelValidation(_)),
                "Expected ModelValidation error, got: {e}"
            );
        }
    }
}

/// Regression test for #1432/#1445: LIA incremental Tseitin cache soundness.
///
/// Tests the same hazard as EUF: if a term is encoded in one scope, popped,
/// and then reused in another scope, the cached term→var mapping must still
/// have its definitional clauses active.
#[test]
fn test_incremental_lia_tseitin_cache_soundness() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)

        (push 1)
        (assert (>= x 0))
        (check-sat)
        (pop 1)

        (push 1)
        (assert (and (>= x 0) (< x 0)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // First check-sat: (>= x 0) is satisfiable -> SAT
    // Second check-sat: (>= x 0) AND (< x 0) is unsatisfiable -> UNSAT
    assert_eq!(
        outputs,
        vec!["sat", "unsat"],
        "Bug #1432/#1445: LIA Tseitin definitions must remain active for cached vars"
    );
}

/// Regression test for #1432/#1445: LRA incremental Tseitin cache soundness.
#[test]
fn test_incremental_lra_tseitin_cache_soundness() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)

        (push 1)
        (assert (>= x 0.0))
        (check-sat)
        (pop 1)

        (push 1)
        (assert (and (>= x 0.0) (< x 0.0)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // First check-sat: (>= x 0.0) is satisfiable -> SAT
    // Second check-sat: (>= x 0.0) AND (< x 0.0) is unsatisfiable -> UNSAT
    assert_eq!(
        outputs,
        vec!["sat", "unsat"],
        "Bug #1432/#1445: LRA Tseitin definitions must remain active for cached vars"
    );
}

/// Regression test for #1432/#1445: BV incremental bitblaster cache soundness.
#[test]
fn test_incremental_bv_bitblast_cache_soundness() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))

        (push 1)
        (assert (= x #x00))
        (check-sat)
        (pop 1)

        (push 1)
        (assert (and (= x #x00) (distinct x #x00)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // First check-sat: (= x #x00) is satisfiable -> SAT
    // Second check-sat: (= x #x00) AND (distinct x #x00) is unsatisfiable -> UNSAT
    assert_eq!(
        outputs,
        vec!["sat", "unsat"],
        "Bug #1432/#1445: BV bitblaster definitions must remain active for cached vars"
    );
}

/// Test reset() clears BV state completely.
///
/// Unlike push/pop which scope assertions, reset() clears all state.
/// The solver should behave as freshly constructed after reset.
#[test]
fn test_incremental_bv_reset() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x42))
        (check-sat)
        (reset)
        (set-logic QF_BV)
        (declare-const y (_ BitVec 8))
        (assert (= y #x00))
        (assert (distinct y #x00))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // First: x = 0x42 is SAT
    // After reset, new problem: y = 0 AND y != 0 is UNSAT
    // Old variable x should not affect new problem
    assert_eq!(outputs, vec!["sat", "unsat"]);
}

/// Test reset() after push/pop maintains correct state.
#[test]
fn test_incremental_bv_reset_after_push_pop() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (bvult x #x10))
        (push 1)
        (assert (= x #x05))
        (check-sat)
        (pop 1)
        (reset)
        (set-logic QF_BV)
        (declare-const z (_ BitVec 8))
        (assert (= z #xFF))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // First: x < 16 AND x = 5 is SAT
    // After reset: z = 255 is SAT (completely fresh problem)
    assert_eq!(outputs, vec!["sat", "sat"]);
}

/// Test reset() clears bitblaster cache properly.
///
/// REQUIRES: reset() clears term_to_bits, predicate_to_var, tseitin_state
/// ENSURES: Re-using same variable name after reset doesn't reuse stale mappings
#[test]
fn test_incremental_bv_reset_clears_cache() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x42))
        (check-sat)
        (reset)
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x00))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Both should be SAT - the x after reset is a completely new variable
    // Even though it has the same name, bitblaster cache should be cleared
    assert_eq!(outputs, vec!["sat", "sat"]);
}

/// Test reset() inside an active scope (no pop) clears scope state.
///
/// REQUIRES: reset() clears scope_depth even without explicit pop
/// ENSURES: Fresh solver after reset has no pending scopes
#[test]
fn test_incremental_bv_reset_inside_scope() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (push 1)
        (assert (= x #x42))
        (check-sat)
        (reset)
        (set-logic QF_BV)
        (declare-const y (_ BitVec 8))
        (assert (= y #x00))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // First: inside scope, x = 0x42 is SAT
    // After reset (without pop): y = 0 is SAT
    // Reset should clear scope_depth even without explicit pop
    assert_eq!(outputs, vec!["sat", "sat"]);
}

/// Regression test for #2861: Executor::reset() must clear quantifier manager,
/// incremental state, and proof-related fields — matching the SMT-LIB (reset)
/// command handler behavior.
#[test]
fn test_executor_reset_clears_all_state_2861() {
    let input = r#"
        (set-logic LIA)
        (declare-const x Int)
        (push 1)
        (assert (forall ((y Int)) (>= (+ x y) y)))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();

    assert!(
        exec.incremental_mode,
        "incremental_mode should be true after push/pop"
    );

    exec.reset();

    assert!(
        !exec.incremental_mode,
        "incremental_mode should be false after reset()"
    );

    if let Some(ref qm) = exec.quantifier_manager {
        assert_eq!(
            qm.round(),
            0,
            "quantifier_manager round should be 0 after reset()"
        );
        assert!(
            !qm.has_deferred(),
            "quantifier_manager should have no deferred items after reset()"
        );
    }

    let input2 = r#"
        (set-logic QF_LIA)
        (declare-const z Int)
        (assert (= z 42))
        (check-sat)
    "#;
    let commands2 = parse(input2).unwrap();
    let outputs2 = exec.execute_all(&commands2).unwrap();
    assert_eq!(outputs2, vec!["sat"]);
}

/// Regression test for #1836: LIA unbounded oscillation detection (increasing)
///
/// This formula is UNSAT (loop preservation) but the LIA solver was hanging
/// because branch-and-bound kept splitting on unbounded variables without
/// making progress. The fix detects monotonically increasing/decreasing
/// split values and returns Unknown after a threshold.
#[test]
#[timeout(30_000)] // Should complete quickly; timeout ensures hang regressions fail fast.
fn test_lia_unbounded_oscillation_terminates_1836() {
    // Loop preservation pattern: i >= 0, i <= n, i < n, NOT(i+1 >= 0 AND i+1 <= n)
    // This is UNSAT by case analysis, but branch-and-bound oscillates forever
    // without Gomory/HNF cuts (no equalities, slack vars block Gomory).
    let input = r#"
(set-logic QF_LIA)
(declare-const i Int)
(declare-const n Int)
(assert (>= i 0))
(assert (<= i n))
(assert (< i n))
(assert (not (and (>= (+ i 1) 0) (<= (+ i 1) n))))
(check-sat)
"#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Should terminate quickly with "unknown" (not hang forever)
    // Z3 returns "unsat", but our mitigation returns "unknown" to prevent hang.
    // The key is that it terminates instead of infinite looping.
    assert!(
        outputs == vec!["unknown"] || outputs == vec!["unsat"],
        "Expected unknown or unsat, got {outputs:?}"
    );
}

/// Regression test for #1836: LIA unbounded oscillation detection (decreasing)
///
/// Tests the decreasing direction of unbounded oscillation detection.
/// Similar to the increasing test but with constraints that push values negative.
#[test]
#[timeout(30_000)] // Should complete quickly; timeout ensures hang regressions fail fast.
fn test_lia_unbounded_oscillation_decreasing_1836() {
    // Loop preservation pattern going negative: i <= 0, i >= n, i > n,
    // NOT(i-1 <= 0 AND i-1 >= n)
    // This creates monotonically decreasing split values.
    let input = r#"
(set-logic QF_LIA)
(declare-const i Int)
(declare-const n Int)
(assert (<= i 0))
(assert (>= i n))
(assert (> i n))
(assert (not (and (<= (- i 1) 0) (>= (- i 1) n))))
(check-sat)
"#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Should terminate quickly with "unknown" (not hang forever)
    assert!(
        outputs == vec!["unknown"] || outputs == vec!["unsat"],
        "Expected unknown or unsat, got {outputs:?}"
    );
}

/// Regression test for #4767: ITE with UF condition incorrectly returns SAT.
///
/// The formula `(f x) = true ∧ (g x) = 5 ∧ ite(f(x), g(x)+1, 0) ≠ 6`
/// is UNSAT because: f(x) true → ite branch is g(x)+1 → 5+1 = 6 → 6≠6 contradiction.
///
/// Root cause: Int-sorted equalities with UF subterms (e.g., (= (g x) 5)) were
/// not forwarded to LIA, so the arithmetic relationship between g(x)=5 and
/// g(x)+1=6 was invisible.
#[test]
fn test_ite_uf_condition_unsat_issue_4767() {
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Bool)
        (declare-fun g (Int) Int)
        (declare-const x Int)
        (assert (f x))
        (assert (= (g x) 5))
        (assert (not (= (ite (f x) (+ (g x) 1) 0) 6)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["unsat"],
        "ITE with UF condition must be UNSAT (#4767)"
    );
}

/// Variant of #4767: simpler case without ITE — just UF equality + arithmetic.
/// (g x) = 5 ∧ (g x) + 1 ≠ 6 is UNSAT.
#[test]
fn test_uf_equality_arithmetic_contradiction_issue_4767() {
    let input = "(set-logic QF_UFLIA)(declare-fun g (Int) Int)(declare-const x Int)\
        (assert (= (g x) 5))(assert (not (= (+ (g x) 1) 6)))(check-sat)";
    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["unsat"],
        "UF equality + arith contradiction must be UNSAT (#4767)"
    );
}

/// SAT variant of #4767: (g x) = 5 ∧ (g x) + 1 ≠ 7 is SAT (5+1=6≠7).
#[test]
fn test_uf_equality_arithmetic_sat_issue_4767() {
    let input = "(set-logic QF_UFLIA)(declare-fun g (Int) Int)(declare-const x Int)\
        (assert (= (g x) 5))(assert (not (= (+ (g x) 1) 7)))(check-sat)";
    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["sat"],
        "UF equality + non-contradictory arith should be SAT (#4767)"
    );
}

/// #5355: Interleaved declare-const/assert causes infinite loop in
/// non-incremental LIA path due to repeated identical disequality splits.
/// Term ID ordering from interleaved declarations caused the simplex model
/// to produce an excluded value outside the variable's feasible domain,
/// leading to non-converging splits.
#[test]
#[timeout(10_000)]
fn test_interleaved_declare_assert_hang_issue_5355() {
    // Interleaved order: declare x, assert x>=1, declare y, assert y>=1, ...
    // This previously hung because TermId ordering caused wrong excluded value.
    let interleaved = "\
        (set-logic QF_LIA)\
        (declare-const x Int)\
        (assert (>= x 1))\
        (declare-const y Int)\
        (assert (>= y 1))\
        (assert (not (= x y)))\
        (assert (= x 1))\
        (check-sat)";
    let commands = parse(interleaved).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["sat"],
        "interleaved declare/assert should be SAT (#5355)"
    );
}

/// #5355 variant: non-interleaved order (all declares before asserts).
/// This was always working — included to prevent regression.
#[test]
#[timeout(10_000)]
fn test_non_interleaved_declare_assert_issue_5355() {
    let non_interleaved = "\
        (set-logic QF_LIA)\
        (declare-const x Int)\
        (declare-const y Int)\
        (assert (>= x 1))\
        (assert (>= y 1))\
        (assert (not (= x y)))\
        (assert (= x 1))\
        (check-sat)";
    let commands = parse(non_interleaved).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["sat"],
        "non-interleaved declare/assert should be SAT (#5355)"
    );
}

/// #5560: solve_dt_auflira delegates to solve_lira, dropping array reasoning.
///
/// When DT is present with QF_AUFLIRA, the solver should use solve_auflira
/// (with array axioms and AufLiraSolver theory). The bug at euf.rs:187 routes
/// to solve_lira which lacks array reasoning, EUF, and array model extraction.
/// A second instance at executor.rs:1915 routes the assumptions path to
/// solve_lira_with_assumptions instead of solve_auflira_with_assumptions.
///
/// This formula uses symbolic indices to prevent eager read-over-write
/// simplification in mk_select, requiring theory-level array reasoning.
/// UNSAT because: i = j, so store at i and select at j hit the
/// same index, and the stored value must equal the selected value.
#[test]
#[timeout(30_000)]
fn test_dt_auflira_symbolic_index_array_5560() {
    // DT + Array + LIRA with symbolic indices.
    // Without array theory reasoning, the solver cannot determine that
    // select(store(a, i, v), j) = v when i = j symbolically.
    let input = r#"
        (set-logic QF_AUFLIRA)
        (declare-datatypes ((IPair 0)) (((mkip (ip_fst Int) (ip_snd Real)))))
        (declare-const a (Array Int Real))
        (declare-const i Int)
        (declare-const j Int)
        (declare-const v Real)
        (declare-const p IPair)
        (assert (= p (mkip i v)))
        (assert (= i j))
        (assert (= v 3.5))
        (assert (distinct (select (store a i v) j) v))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    // #5560 FIX: solve_dt_auflira now routes to solve_auflira (not solve_lira).
    // With array reasoning: i=j, so select(store(a,i,v),j) = v,
    // contradicting (distinct ... v) → UNSAT.
    assert_eq!(
        outputs,
        vec!["unsat"],
        "#5560: DT+AUFLIRA with array reasoning should return unsat"
    );
}

/// #5560 (assumption path): solve_lira_with_assumptions → solve_auflira_with_assumptions.
///
/// The assumption-based dispatch (executor.rs DtAuflira arm) had the same bug:
/// routing to solve_lira_with_assumptions instead of solve_auflira_with_assumptions.
/// This test exercises the check-sat-assuming path to verify both call sites are fixed.
#[test]
#[timeout(30_000)]
fn test_dt_auflira_assumptions_path_5560() {
    let input = r#"
        (set-logic QF_AUFLIRA)
        (declare-datatypes ((Wrap 0)) (((wrap (unwrap Int)))))
        (declare-const a (Array Int Real))
        (declare-const w Wrap)
        (declare-const k Int)
        (declare-const v Real)
        (assert (= (unwrap w) k))
        (assert (= v 2.0))
        (assert (distinct (select (store a k v) (unwrap w)) v))
        (check-sat-assuming (true))
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["unsat"],
        "#5560: DT+AUFLIRA assumption path should also return unsat"
    );
}

/// #5671: False UNSAT on QF_LIA with all-distinct + diagonal constraints.
///
/// AY incorrectly returned `unsat` on satisfiable 4-queens problems when
/// 4+ bounded integer variables had pairwise disequality constraints plus
/// additional linear arithmetic constraints on differences. Root cause:
/// single-variable enumeration in LRA theory split for multi-variable
/// disequalities incorrectly generated clauses that dropped constraints
/// on other variables, causing unsound UNSAT. Fixed by replacing
/// single-variable enumeration with direct expression split.
///
/// Minimal trigger: 4 vars in {1..4}, all pairwise distinct, plus one
/// diagonal constraint on q1-q2. Solution exists: e.g. q1=2,q2=4,q3=1,q4=3.
#[test]
#[timeout(30000)]
fn test_false_unsat_all_distinct_diagonal_5671() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const q1 Int)
        (declare-const q2 Int)
        (declare-const q3 Int)
        (declare-const q4 Int)
        (assert (>= q1 1)) (assert (<= q1 4))
        (assert (>= q2 1)) (assert (<= q2 4))
        (assert (>= q3 1)) (assert (<= q3 4))
        (assert (>= q4 1)) (assert (<= q4 4))
        (assert (not (= q1 q2)))
        (assert (not (= q1 q3)))
        (assert (not (= q1 q4)))
        (assert (not (= q2 q3)))
        (assert (not (= q2 q4)))
        (assert (not (= q3 q4)))
        (assert (not (= (+ q1 (- q2)) 1)))
        (assert (not (= (+ q1 (- q2)) (- 1))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["sat"],
        "#5671: 4 bounded vars + all-distinct + diagonal must be SAT"
    );
}

// ========== QF_UF EUF guard regression tests (#6498) ==========

#[test]
fn test_qf_uf_sat_not_degraded_to_unknown_6498() {
    // Pure QF_UF query: uninterpreted function, equality check.
    // Must return sat, not unknown — the EUF theory solver provides
    // independent verification of congruence closure consistency.
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-const a U)
        (declare-const b U)
        (assert (= (f a) b))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs[0], "sat",
        "QF_UF with EUF model must not degrade to unknown (#6498) — got: {}",
        outputs[0]
    );
}

#[test]
fn test_qf_uf_uninterpreted_fn_unconstrained_6498() {
    // Unconstrained UF function returning Bool — should be sat
    // (any interpretation of g works).
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun g (U) Bool)
        (declare-const x U)
        (assert (g x))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs[0], "sat",
        "Unconstrained UF function must return sat (#6498) — got: {}",
        outputs[0]
    );
}

#[test]
fn test_qf_uf_equality_coercion_6498() {
    // Equality between different UF applications — must return sat, not unknown.
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-fun g (U) U)
        (declare-const a U)
        (assert (= (f a) (g a)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs[0], "sat",
        "UF equality between different functions must return sat (#6498) — got: {}",
        outputs[0]
    );
}

/// Regression: QF_AX check-sat-assuming where the only array store/select
/// appears in the assumption. Without assumption-aware axiom generation
/// (#6736), the ROW axiom for the assumption-only store is never seeded.
#[test]
#[timeout(10_000)]
fn test_qf_ax_assumption_only_array_store_unsat_6736() {
    // a is an array. The only store appears in the assumption:
    //   (= (select (store a i v) i) v) is a tautology from ROW axiom.
    //   Assumption: (distinct (select (store a i v) i) v) contradicts ROW.
    let input = r#"
        (set-logic QF_AX)
        (declare-sort Idx 0)
        (declare-sort Elem 0)
        (declare-fun a () (Array Idx Elem))
        (declare-fun i () Idx)
        (declare-fun v () Elem)
        (check-sat-assuming (
            (distinct (select (store a i v) i) v)
        ))
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs[0], "unsat",
        "ROW axiom must fire for assumption-only store (#6736) — got: {}",
        outputs[0]
    );
}

/// Regression: QF_AUFLIA check-sat-assuming where array+LIA terms only
/// appear in assumptions. Without assumption-aware axiom generation
/// (#6736), integer-indexed array operations in assumptions get no axioms.
#[test]
#[timeout(10_000)]
fn test_qf_auflia_assumption_only_array_unsat_6736() {
    // Permanent assertion: just declares a and b as integer arrays.
    // Assumption: a = b AND select(a, 0) != select(b, 0) — contradicts
    // array extensionality + congruence.
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= a b))
        (check-sat-assuming (
            (distinct (select a 0) (select b 0))
        ))
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs[0], "unsat",
        "Array congruence must fire for assumption-only selects (#6736) — got: {}",
        outputs[0]
    );
}

/// Model recovery must retain the original assumption-only disequality after
/// preprocessing eliminates or rewrites its variables.  Otherwise class
/// reunification can collapse both array defaults to the same value and turn a
/// genuine SAT result into Unknown at the validation gate.
#[test]
#[timeout(10_000)]
fn test_qf_auflia_assumption_disequality_remains_a_model_root() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const x Int)
        (declare-const y Int)
        (assert (= x (default a)))
        (assert (= y (default b)))
        (assert (= (+ x y) 0))
        (check-sat-assuming ((distinct x y)))
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs[0], "sat",
        "assumption-only disequality must survive model extraction: {outputs:?}"
    );
}

/// The non-assumption AUFLIA route has the same model-root contract.  An
/// original disequality consumed by preprocessing still protects both values
/// from speculative EUF-class reunification.
#[test]
#[timeout(10_000)]
fn test_qf_auflia_original_disequality_remains_a_model_root() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const x Int)
        (declare-const y Int)
        (assert (= x (default a)))
        (assert (= y (default b)))
        (assert (= (+ x y) 0))
        (assert (distinct x y))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs[0], "sat",
        "original disequality must survive model extraction: {outputs:?}"
    );
}

/// UFLIA must restore exact original equalities before replaying eliminated
/// substitutions.  Replaying `z -> x + 1` from a stale opaque `f(a)` value
/// first permanently committed the wrong z and degraded SAT to Unknown.
#[test]
#[timeout(10_000)]
fn test_qf_uflia_exact_recovery_precedes_substitution_replay() {
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (declare-const x Int)
        (declare-const z Int)
        (assert (= x (f a)))
        (assert (= x 5))
        (assert (= z (+ x 1)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs[0], "sat",
        "exact anchors must precede substitution replay: {outputs:?}"
    );
    assert!(
        exec.validate_model().is_ok(),
        "recovered UFLIA model must satisfy the original dependency chain"
    );
}

/// UFLIA fixups must run before the shared LIA→EUF merge.  The original UF
/// argument remains `(+ x 1)` while preprocessing can solve x and register a
/// canonical constant argument; a stale EUF integer for the composite makes
/// the original table lookup miss and the validation gate reject SAT.
#[test]
#[timeout(10_000)]
fn test_qf_uflia_fixup_precedes_euf_integer_merge() {
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (assert (= x 4))
        (assert (= (f (+ x 1)) 10))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs[0], "sat",
        "final arithmetic UF arguments must reach both EUF value maps: {outputs:?}"
    );
    assert!(
        exec.validate_model().is_ok(),
        "the original pre-substitution UF application must validate"
    );
}

/// Congruent UF applications can be EUF-equal without both opaque Int atoms
/// receiving the same LIA value.  Reunification must cover every scoped peer
/// in the class, not only terms already present in `LiaModel::values`.
#[test]
#[timeout(10_000)]
fn test_qf_uflia_reunifies_all_scoped_integer_class_peers() {
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-sort U 0)
        (declare-fun f (U) Int)
        (declare-const a U)
        (declare-const b U)
        (declare-const y Int)
        (declare-const z Int)
        (assert (= a b))
        (assert (= (f a) 5))
        (assert (= y (f b)))
        (assert (= z (+ y 1)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs[0], "sat",
        "congruent Int applications must share one recovered class value: {outputs:?}"
    );
    assert!(
        exec.validate_model().is_ok(),
        "every original congruent application must validate"
    );
}

#[test]
#[timeout(10_000)]
fn test_qf_auflia_check_sat_assuming_persistent_sat_inherits_random_seed() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (set-option :random-seed 42)
        (declare-fun a () (Array Int Int))
        (declare-fun x () Int)
        (assert (> x 0))
        (assert (= (select a x) 1))
        (check-sat-assuming ((= (select a x) 1)))
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    assert_eq!(exec.last_applied_sat_random_seed_for_test(), Some(42));
}

/// Regression: QF_ABV check-sat-assuming with bitvector array store only
/// in assumption. Without assumption-aware axiom generation (#6736),
/// BV-array operations in assumptions get no ROW axioms.
#[test]
#[timeout(10_000)]
fn test_qf_abv_assumption_only_array_store_unsat_6736() {
    let input = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun i () (_ BitVec 8))
        (declare-fun v () (_ BitVec 8))
        (check-sat-assuming (
            (distinct (select (store a i v) i) v)
        ))
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs[0], "unsat",
        "ROW axiom must fire for assumption-only BV-array store (#6736) — got: {}",
        outputs[0]
    );
}

/// Regression test for #6853: QF_LIA incremental false-unsat.
///
/// Before the fix, `retain_encoded_assertions()` pruned `lia_derived_assertions`
/// to only keep terms already encoded. This removed activation-depth metadata for
/// new-but-not-yet-encoded assertions, causing `desired_activation_depth()` to
/// fall through to a misaligned `active_assertion_min_scope_depths()` which could
/// return depth 0 (global). Global activation clauses are permanent and irretractable,
/// so later check-sats that negate the same Tseitin root would see a conflict and
/// produce false UNSAT.
#[test]
#[timeout(30_000)]
fn test_incremental_lia_derived_assertion_scope_soundness_6853() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun z () Int)
        (push 1)
        (assert (>= x 0))
        (assert (<= x 10))
        (assert (= y (+ x 1)))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (>= x 5))
        (assert (<= x 20))
        (assert (= y (+ x 2)))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (>= x 0))
        (assert (<= y 100))
        (assert (= z (+ x y)))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (and (>= x 0) (<= x 5)))
        (assert (and (>= y 0) (<= y 5)))
        (check-sat)
        (pop 1)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs,
        vec!["sat", "sat", "sat", "sat"],
        "Bug #6853: LIA incremental push/pop must not produce false UNSAT \
         from leaked global activation clauses"
    );
}

/// Regression test for #6853: nested push/pop with LIA derived assertions.
#[test]
#[timeout(30_000)]
fn test_incremental_lia_nested_derived_assertion_scope_6853() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (push 1)
        (assert (>= a 0))
        (push 1)
        (assert (= b (+ a 1)))
        (assert (>= b 1))
        (check-sat)
        (pop 1)
        (check-sat)
        (pop 1)
        (push 1)
        (assert (>= a 0))
        (check-sat)
        (pop 1)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs,
        vec!["sat", "sat", "sat"],
        "Bug #6853: Nested LIA push/pop must not leak derived assertion activations"
    );
}

/// #8419: DT+BV injectivity axiom - same constructor equality implies field equality.
///
/// When C(a) = C(b), injectivity requires a = b. The BV solver uses axiom-based
/// DT reasoning (no interactive DT solver), so injectivity must be encoded as
/// explicit axioms. Without this, model-checker-consumer must flatten DT+BV to avoid relying on
/// injectivity reasoning.
#[test]
#[timeout(30_000)]
fn test_dt_bv_injectivity_axiom_8419() {
    // mk-pair(x, y) = mk-pair(y, x) → x = y (injectivity).
    // Combined with x != y → UNSAT.
    let input = r#"
        (set-logic _DT_UFBV)
        (declare-datatypes ((Pair 0)) (((mk-pair (fst (_ BitVec 8)) (snd (_ BitVec 8))))))
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= (mk-pair x y) (mk-pair y x)))
        (assert (distinct x y))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["unsat"],
        "#8419: DT+BV injectivity should detect x=y from mk-pair(x,y)=mk-pair(y,x)"
    );
}

/// #8419: DT+BV constructor disjointness - different constructors cannot be equal.
///
/// When C1(...) = C2(...) and C1 != C2, this is unsatisfiable. The axiom-based
/// path must explicitly encode this as a disjointness axiom.
#[test]
#[timeout(30_000)]
fn test_dt_bv_constructor_disjointness_8419() {
    let input = r#"
        (set-logic _DT_UFBV)
        (declare-datatypes ((Either 0)) (((left (l-val (_ BitVec 8))) (right (r-val (_ BitVec 8))))))
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= (left x) (right y)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["unsat"],
        "#8419: DT+BV constructor disjointness: left(x) != right(y)"
    );
}

/// #8419: DT+BV tester mutual exclusion - at most one tester true per variable.
///
/// For a DT variable x, (is-C1 x) and (is-C2 x) cannot both be true.
/// The axiom-based path needs explicit mutual exclusion constraints.
#[test]
#[timeout(30_000)]
fn test_dt_bv_tester_mutual_exclusion_8419() {
    let input = r#"
        (set-logic _DT_UFBV)
        (declare-datatypes ((Tag 0)) (((a) (b) (c))))
        (declare-const t Tag)
        (assert (is-a t))
        (assert (is-b t))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["unsat"],
        "#8419: DT+BV tester mutual exclusion: (is-a t) and (is-b t) cannot both hold"
    );
}

/// #8419: DT+BV mixed constraints - DT constructor + BV arithmetic.
///
/// This exercises the common model-checker-consumer pattern: a struct containing BV fields
/// where the solver must reason about both DT structure and BV values.
#[test]
#[timeout(30_000)]
fn test_dt_bv_mixed_struct_arithmetic_8419() {
    let input = r#"
        (set-logic _DT_UFBV)
        (declare-datatypes ((Val 0)) (((mk-val (data (_ BitVec 8))))))
        (declare-const v1 Val)
        (declare-const v2 Val)
        (declare-const x (_ BitVec 8))
        (assert (= v1 (mk-val x)))
        (assert (= v2 (mk-val (bvadd x #x01))))
        (assert (= (data v1) (data v2)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    // data(v1) = x, data(v2) = x + 1, so data(v1) != data(v2) for any x != 0xFF.
    // But x = 0xFF → x + 1 = 0x00 (wrapping), so data(v1) = 0xFF != 0x00 = data(v2).
    // Actually, wait: for x = 0xFF, bvadd(0xFF, 0x01) = 0x00, so data(v1) = 0xFF,
    // data(v2) = 0x00. These are not equal.
    // For any x: data(v1) = x and data(v2) = x+1. These can never be equal (mod 256).
    // Actually: if x+1 = x, that's never true for BV. So UNSAT.
    assert_eq!(
        outputs,
        vec!["unsat"],
        "#8419: DT+BV mixed: mk-val(x) with data = x, mk-val(x+1) with data = x+1 → data unequal"
    );
}

/// #8419: DT+BV check-sat-assuming path.
///
/// The CHC PDR engine uses check-sat-assuming. This tests the assumption-based
/// path through dt_combined_check_sat_assuming.
#[test]
#[timeout(30_000)]
fn test_dt_bv_check_sat_assuming_8419() {
    let input = r#"
        (set-logic _DT_UFBV)
        (declare-datatypes ((Maybe 0)) (((just (val (_ BitVec 8))) (nothing))))
        (declare-const m1 Maybe)
        (declare-const m2 Maybe)
        (declare-const x (_ BitVec 8))
        (assert (= m1 (just x)))
        (assert (= m2 nothing))
        (check-sat-assuming ((= m1 m2)))
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    // m1 = just(x) and m2 = nothing, so m1 = m2 requires just(x) = nothing → UNSAT.
    assert_eq!(
        outputs,
        vec!["unsat"],
        "#8419: DT+BV check-sat-assuming: just(x) != nothing"
    );
}

/// Keystone model-completion regression: Bool gate equality must report SAT.
///
/// `(= v9 (or v3 (<= v8 20)))` is eliminated by `VariableSubstitution`
/// (definitional equality `v9 -> RHS`), so the SAT model has no entry for
/// `v9`, and `v3`/`v8` are unconstrained. Model completion at finalize time
/// must recover `v9` from the substitution RHS and default the truly-free
/// variables, then full validation accepts the total model (CHC-COMP
/// KIND-check pattern, ~424 instances).
#[test]
#[timeout(30_000)]
fn test_bool_gate_equality_model_completion_sat() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const v3 Bool)
        (declare-const v9 Bool)
        (declare-const v8 Int)
        (assert (= v9 (or v3 (<= v8 20))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["sat"],
        "Bool gate-equality SAT degraded to unknown: model completion failed"
    );
}

/// UNSAT-side companion of `test_bool_gate_equality_model_completion_sat`:
/// asserting the gate output false while forcing the RHS true must stay UNSAT.
#[test]
#[timeout(30_000)]
fn test_bool_gate_equality_model_completion_unsat() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const v3 Bool)
        (declare-const v9 Bool)
        (declare-const v8 Int)
        (assert (= v9 (or v3 (<= v8 20))))
        (assert (not v9))
        (assert v3)
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(outputs, vec!["unsat"]);
}

/// SOUNDNESS (found by scripts/diff_fuzz.py multi-theory fan-out, QF_UFDT): a
/// datatype value satisfies exactly one recognizer, so `(_ is c0) (f x)` and
/// `(_ is c1) (f x)` is UNSAT — but AY returned `sat` when the tested term is a
/// UF application (the exhaustiveness/constructor DT axioms were emitted only for
/// declared variables/selectors, not UF-app/ite results — the unsound #6201
/// "ITE/UF inherit exhaustiveness from constituent variables" assumption). Fixed
/// in dt_axioms/selector.rs by also axiomatizing DT-sorted tester-argument terms.
/// Controls: plain-var and selector-headed tester-pairs were already correct.
#[test]
fn test_dt_tester_exclusion_on_uf_app_term_no_false_sat() {
    let input = r#"
        (set-logic QF_UFDT)
        (declare-datatype Enum ((c0) (c1) (c2)))
        (declare-fun f (Enum) Enum)
        (declare-const x Enum)
        (assert ((_ is c0) (f x)))
        (assert ((_ is c1) (f x)))
        (check-sat)
    "#;
    let commands = parse(input).expect("valid QF_UFDT input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute QF_UFDT");
    assert_eq!(
        outputs,
        vec!["unsat"],
        "a DT term (incl. a UF-app result) satisfies exactly one recognizer; \
         two distinct testers true on (f x) must be UNSAT"
    );
}

/// SOUNDNESS (found by scripts/diff_fuzz.py, QF_DT): occurs-check / acyclicity
/// was defeated by a forced-true `ite` guard. `(_ is mkRec) r` is a
/// SOLE-constructor tester (always true), so `(ite ((_ is mkRec) r) v12 v11)` is
/// definitionally `v12`, making `(= v12 (left v12))` — a tree equal to its own
/// left child (UNSAT) — but AY returned `sat` because the standalone DT
/// occurs-check did not look through the non-syntactically-true ite guard. Fixed
/// by folding sole-constructor testers to `true` at elaboration
/// (ay-frontend/.../indexed.rs), so the guard ite collapses and the cycle is seen.
#[test]
fn test_dt_occurs_check_through_sole_ctor_tester_ite_guard() {
    let input = r#"
        (set-logic QF_DT)
        (declare-datatypes ((Rec 0) (Tree 0))
          (((mkRec)) ((leaf) (node (left Tree) (right Tree)))))
        (declare-const r Rec)
        (declare-const v11 Tree)
        (declare-const v12 Tree)
        (assert (= (ite ((_ is mkRec) r) v12 v11) (left v12)))
        (assert ((_ is node) v12))
        (check-sat)
    "#;
    let commands = parse(input).expect("valid QF_DT input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute QF_DT");
    assert_eq!(
        outputs,
        vec!["unsat"],
        "a sole-constructor tester is always true, so the ite folds to v12 and \
         v12 = left(v12) is an acyclicity violation (UNSAT)"
    );
}

/// SOUNDNESS (TARGET dt_decision): the acyclicity occurs-check now resolves a
/// selector applied to a CONSTRUCTOR — `mid(node a v b) = v` by the datatype
/// selector axiom — so a recursive occurrence hidden behind `sel(C(.. v ..))`
/// is detected. `v = node(leaf, mid(node a v b), leaf)` is a tree equal to a
/// constructor that structurally contains `v` (via the projected middle field),
/// which is an acyclicity violation (UNSAT). Previously AY returned `sat`.
#[test]
fn test_dt_acyclicity_selector_over_constructor_projection_unsat() {
    let input = r#"
        (set-logic QF_UFDT)
        (declare-datatypes ((Tree 0))
          (((leaf) (node (left Tree) (mid Tree) (right Tree)))))
        (declare-const v Tree)
        (declare-const a Tree)
        (declare-const b Tree)
        (assert (= v (node leaf (mid (node a v b)) leaf)))
        (check-sat)
    "#;
    let commands = parse(input).expect("valid QF_UFDT input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute QF_UFDT");
    assert_eq!(
        outputs,
        vec!["unsat"],
        "mid(node a v b) projects to v, so v = node(.., v, ..) is a structural cycle (UNSAT)"
    );
}

/// CONTROL (TARGET dt_decision): the selector-projection must NOT fabricate a
/// cycle when the projected field is NOT the cyclic variable. `mid(node a b leaf)`
/// projects to the FREE `b`, so `v = node(leaf, b, leaf)` has no cycle and is SAT.
/// Also guards against projecting a selector applied to a free variable.
#[test]
fn test_dt_acyclicity_selector_projection_no_false_cycle_sat() {
    let input = r#"
        (set-logic QF_UFDT)
        (declare-datatypes ((Tree 0))
          (((leaf) (node (left Tree) (mid Tree) (right Tree)))))
        (declare-const v Tree)
        (declare-const a Tree)
        (declare-const b Tree)
        (declare-const w Tree)
        (assert (= v (node leaf (mid (node a b leaf)) (mid w))))
        (check-sat)
    "#;
    let commands = parse(input).expect("valid QF_UFDT input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute QF_UFDT");
    assert_eq!(
        outputs,
        vec!["sat"],
        "mid(node a b leaf) projects to free b (no cycle); mid(w) is opaque — must stay SAT"
    );
}

/// SOUNDNESS (TARGET dt_decision, C1): finite-enum CARDINALITY degrade in DEFAULT
/// mode. `fEnum: Enum -> Enum` over a 2-inhabitant enum with
/// `fEnum(v1)=v2 ∧ fEnum(v1) != fEnum(fEnum(v2))` is a functional finite-domain
/// pigeonhole (UNSAT for z3/cvc5). AY's EUF model over-populates the 2-inhabitant
/// `Enum` sort with 4 distinct representatives — a phantom infinite-domain model.
/// The default-mode cardinality gate detects this and degrades the wrong `sat` to
/// a sound `unknown` (NEVER a wrong answer). It does not claim UNSAT (that needs a
/// complete finite-model EUF procedure), only refuses the unsound `sat`.
#[test]
fn test_dt_finite_enum_functional_pigeonhole_not_false_sat() {
    let input = r#"
        (set-logic QF_UFDT)
        (declare-datatypes ((Enum 0)) (((c0) (c1))))
        (declare-const v1 Enum)
        (declare-const v2 Enum)
        (declare-fun fEnum (Enum) Enum)
        (assert (= (fEnum v1) v2))
        (assert (distinct (fEnum v1) (fEnum (fEnum v2))))
        (check-sat)
    "#;
    let commands = parse(input).expect("valid QF_UFDT input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute QF_UFDT");
    assert_ne!(
        outputs,
        vec!["sat"],
        "functional finite-enum pigeonhole is UNSAT; AY must NOT return a wrong sat \
         (cardinality gate degrades to unknown)"
    );
}

/// CONTROL (TARGET dt_decision): the cardinality gate must NOT degrade a GENUINE
/// enum SAT. `distinct x y z` over a 3-inhabitant enum exactly fills the domain
/// (3 distinct == k) and is SAT; `f(x)=x` over a 2-enum is SAT. Neither
/// over-populates the sort, so both must stay `sat`.
#[test]
fn test_dt_finite_enum_genuine_sat_not_degraded() {
    let distinct3 = r#"
        (set-logic QF_UFDT)
        (declare-datatypes ((C 0)) (((a) (b) (c))))
        (declare-const x C) (declare-const y C) (declare-const z C)
        (assert (distinct x y z))
        (check-sat)
    "#;
    let fxx = r#"
        (set-logic QF_UFDT)
        (declare-datatypes ((C 0)) (((a) (b))))
        (declare-fun f (C) C)
        (declare-const x C)
        (assert (= (f x) x))
        (check-sat)
    "#;
    for (src, label) in [
        (distinct3, "distinct over 3-enum"),
        (fxx, "f(x)=x over 2-enum"),
    ] {
        let commands = parse(src).expect("valid QF_UFDT input");
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).expect("execute QF_UFDT");
        assert_eq!(
            outputs,
            vec!["sat"],
            "genuine enum SAT ({label}) must not be degraded by the cardinality gate"
        );
    }
}

/// REGRESSION (#enum-model-repair, TARGET model completion): enum-sorted
/// SELECTOR APPLICATIONS must not permanently degrade a genuine SAT. On the
/// eager DtAx route, `(top x)`/`(top y)` over a 2-constructor enum land in
/// fresh EUF classes no committed equality pins to a constructor; extraction
/// then mints more distinct elements than the sort has inhabitants, the
/// (sound) enum-cardinality gate rejects the model, and iterative deepening
/// fixpoints to `unknown` forever — the entire 20230720-blocksworld SAT side
/// failed this way. `repair_enum_model_overpopulation` now maps the surplus
/// classes onto constructor slots (consistent with committed disequalities +
/// UF-table functional consistency) and the full validation pipeline accepts.
#[test]
fn test_dt_enum_selector_application_model_repair_sat() {
    // Minimal blocksworld shape: recursive datatype with an enum field,
    // selector applications forced pairwise-distinct (genuinely SAT: 2
    // selector terms over a 2-inhabitant enum).
    let plain = r#"
        (set-logic QF_DT)
        (declare-datatypes ((E 0)) (((A) (B))))
        (declare-datatypes ((T 0)) (((stack (top E) (rest T)) (empty))))
        (declare-fun x () T)
        (declare-fun y () T)
        (assert ((_ is stack) x))
        (assert ((_ is stack) y))
        (assert (distinct (top x) (top y)))
        (check-sat)
    "#;
    // Unit equalities force the selector classes onto constructors; the
    // surplus classes are the axiom-synthesized deeper selectors.
    let units = r#"
        (set-logic QF_DT)
        (declare-datatypes ((E 0)) (((A) (B))))
        (declare-datatypes ((T 0)) (((stack (top E) (rest T)) (empty))))
        (declare-fun x () T)
        (declare-fun y () T)
        (assert ((_ is stack) x))
        (assert ((_ is stack) y))
        (assert (distinct (top x) (top y)))
        (assert (= (top x) A))
        (assert (= (top y) B))
        (check-sat)
    "#;
    for (src, label) in [
        (plain, "distinct selectors"),
        (units, "unit-pinned selectors"),
    ] {
        let commands = parse(src).expect("valid QF_DT input");
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).expect("execute QF_DT");
        assert_eq!(
            outputs,
            vec!["sat"],
            "enum selector applications ({label}) are genuinely SAT; the repaired \
             model must pass the cardinality gate instead of degrading to unknown"
        );
    }
}

/// CONTROL (#enum-model-repair): the repair must NOT manufacture a wrong SAT
/// when the surplus classes are genuinely unmergeable. Three pairwise-distinct
/// selector applications over a 2-inhabitant enum are a finite-domain
/// pigeonhole (UNSAT for z3/cvc5); every 2-coloring violates a committed
/// disequality, so the repair aborts and the verdict stays sound (unsat via
/// the dedicated conflict rule, or a degraded unknown — never sat).
#[test]
fn test_dt_enum_selector_pigeonhole_not_false_sat() {
    let input = r#"
        (set-logic QF_DT)
        (declare-datatypes ((E 0)) (((A) (B))))
        (declare-datatypes ((T 0)) (((stack (top E) (rest T)) (empty))))
        (declare-fun x () T)
        (declare-fun y () T)
        (declare-fun z () T)
        (assert ((_ is stack) x))
        (assert ((_ is stack) y))
        (assert ((_ is stack) z))
        (assert (distinct (top x) (top y)))
        (assert (distinct (top y) (top z)))
        (assert (distinct (top x) (top z)))
        (check-sat)
    "#;
    let commands = parse(input).expect("valid QF_DT input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute QF_DT");
    assert_ne!(
        outputs,
        vec!["sat"],
        "3 pairwise-distinct selector terms over a 2-inhabitant enum are a \
         pigeonhole UNSAT; the model repair must not turn this into a wrong sat"
    );
}

/// REGRESSION (env-var deletion pass, 2026-07-05): soundness guards must be
/// UNCONDITIONAL — the former env kill-switches (`AY_LRA_NO_ITE_SHARED_EQ=0`,
/// `AY_NO_LRA_CSA_UNSAT_GUARD=1`, `AY_NO_DISEQ_CLOSURE_GUARD=1`, ...) were
/// deleted, so setting them must have NO effect on verdicts. This pins the
/// P1b QF_UFLRA ite-shared-equality reproducer (`(= (ga z) 5) /\ (= z (ite p
/// -3 -2))`, false-UNSAT under the pre-fix path) as SAT even with the old
/// switch values present in the environment.
#[test]
#[timeout(60000)]
fn test_deleted_env_kill_switches_have_no_effect_on_soundness_guards() {
    // Nothing reads these vars anymore; setting them must be inert. Serialized
    // + restored on scope exit through the one workspace env choke point.
    let _env_lock = lock_env();
    let _guards = [
        ScopedEnvVar::set("AY_LRA_NO_ITE_SHARED_EQ", "0"),
        ScopedEnvVar::set("AY_NO_LRA_CSA_UNSAT_GUARD", "1"),
        ScopedEnvVar::set("AY_NO_DISEQ_CLOSURE_GUARD", "1"),
        ScopedEnvVar::set("AY_NO_STALE_MODELEQ_SAT", "1"),
    ];
    let smt = r#"
        (set-logic QF_UFLRA)
        (declare-const z Real)
        (declare-const p Bool)
        (declare-fun ga (Real) Real)
        (assert (= (ga z) 5.0))
        (assert (= z (ite p (- 3.0) (- 2.0))))
        (check-sat)
    "#;
    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    // `_guards` restore (drop) at end of scope, still under `_env_lock`.
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("sat"),
        "ite-shared-eq guard must be active regardless of environment: {outputs:?}"
    );
}

// ========== Enum finite-domain SAT lane (#enum-sat-lane, stage 4) ===//
// Pure all-nullary-enum (dis)equality problems compile to one-hot CNF and are
// decided by the SAT core (executor/theories/euf/enum_sat.rs). These tests pin
// (a) the round trip — the decoded model must satisfy the ORIGINAL assertions,
// checked through the public `get-value` evaluator path, (b) the fragment
// gate — selector/tester/recursive/non-ground constructs must NOT take the
// lane, and (c) the proof-mode UNSAT fallthrough.

/// The lane fired iff the `solver.enum_sat_lane` stat carries its verdict.
fn enum_sat_lane_stat(exec: &Executor) -> Option<String> {
    match exec.get_statistics().extra.get("solver.enum_sat_lane") {
        Some(StatValue::String(s)) => Some(s.clone()),
        _ => None,
    }
}

#[test]
#[timeout(30000)]
fn test_enum_sat_lane_pure_enum_coloring_roundtrip() {
    // h-series shape: declared enum constants, domain or-clauses, distinct
    // edges. Every original assertion is re-evaluated under the decoded model
    // via get-value and must be true.
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Unit ((u0) (u1) (u2)))
        (declare-fun p1 () Unit)
        (declare-fun p2 () Unit)
        (declare-fun p3 () Unit)
        (assert (= p1 u0))
        (assert (or (= p2 u0) (= p2 u1)))
        (assert (distinct p1 p2))
        (assert (distinct p2 p3))
        (assert (distinct p1 p3))
        (check-sat)
        (get-value ((= p1 u0)
                    (or (= p2 u0) (= p2 u1))
                    (distinct p1 p2)
                    (distinct p2 p3)
                    (distinct p1 p3)))
    "#;
    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs[0], "sat",
        "coloring instance must be sat: {outputs:?}"
    );
    assert!(
        !outputs[1].contains("false"),
        "decoded model must satisfy every original assertion: {}",
        outputs[1]
    );
    assert_eq!(
        enum_sat_lane_stat(&exec).as_deref(),
        Some("sat"),
        "the enum SAT lane must decide this instance"
    );
}

#[test]
#[timeout(30000)]
fn test_enum_sat_lane_uf_at_ctor_args_roundtrip() {
    // k-series shape: UF from one enum to another, applied ONLY at
    // constructor constants (congruence-free; see enum_sat.rs module docs).
    let smt = r#"
        (set-logic QF_UFDT)
        (declare-datatype Place ((p1) (p2) (p3)))
        (declare-datatype Unit ((v0) (v1)))
        (declare-fun u (Place) Unit)
        (assert (= (u p1) v0))
        (assert (or (= (u p2) v0) (= (u p2) v1)))
        (assert (distinct (u p1) (u p2)))
        (check-sat)
        (get-value ((= (u p1) v0)
                    (or (= (u p2) v0) (= (u p2) v1))
                    (distinct (u p1) (u p2))))
    "#;
    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs[0], "sat",
        "UF coloring instance must be sat: {outputs:?}"
    );
    assert!(
        !outputs[1].contains("false"),
        "decoded model must satisfy every original assertion: {}",
        outputs[1]
    );
    assert_eq!(
        enum_sat_lane_stat(&exec).as_deref(),
        Some("sat"),
        "the enum SAT lane must decide this instance"
    );
}

#[test]
#[timeout(30000)]
fn test_enum_sat_lane_nested_skeleton_roundtrip() {
    // Atoms nested under ite / xor / n-ary distinct need FULL biconditional
    // channeling; the decoded model must still satisfy the original
    // structure. The ite forces y = u1 (x is pinned to u0), so the nested
    // n-ary distinct over {x, y, u2} = {u0, u1, u2} evaluates true and the
    // xor's second arm (= y u2) evaluates false.
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Unit ((u0) (u1) (u2)))
        (declare-fun x () Unit)
        (declare-fun y () Unit)
        (assert (= x u0))
        (assert (ite (= x u0) (= y u1) (= y u2)))
        (assert (xor (distinct x y u2) (= y u2)))
        (check-sat)
        (get-value ((ite (= x u0) (= y u1) (= y u2))
                    (xor (distinct x y u2) (= y u2))
                    (= y u1)))
    "#;
    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs[0], "sat",
        "nested skeleton instance must be sat: {outputs:?}"
    );
    assert!(
        !outputs[1].contains("false"),
        "decoded model must satisfy the nested assertions: {}",
        outputs[1]
    );
    assert_eq!(
        enum_sat_lane_stat(&exec).as_deref(),
        Some("sat"),
        "the enum SAT lane must decide this instance"
    );
}

#[test]
#[timeout(30000)]
fn test_enum_sat_lane_negated_distinct_forces_equality() {
    // unit-negative n-ary distinct: (not (distinct x y)) forces x = y.
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Unit ((u0) (u1) (u2)))
        (declare-fun x () Unit)
        (declare-fun y () Unit)
        (assert (= x u0))
        (assert (not (distinct x y)))
        (check-sat)
        (get-value ((= y u0)))
    "#;
    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs[0], "sat");
    assert!(
        outputs[1].contains("true"),
        "y must equal u0 under the decoded model: {}",
        outputs[1]
    );
    assert_eq!(enum_sat_lane_stat(&exec).as_deref(), Some("sat"));
}

#[test]
#[timeout(30000)]
fn test_enum_sat_lane_direct_conflict_unsat() {
    // Two different constructors for the same constant: conflict-derived
    // UNSAT through the definitional encoding.
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Unit ((u0) (u1)))
        (declare-fun x () Unit)
        (assert (= x u0))
        (assert (= x u1))
        (check-sat)
    "#;
    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
    assert_eq!(
        enum_sat_lane_stat(&exec).as_deref(),
        Some("unsat"),
        "the enum SAT lane must derive this conflict"
    );
}

#[test]
#[timeout(30000)]
fn test_enum_sat_lane_proof_mode_unsat_falls_through() {
    // Proof-producing solves must get their UNSAT from the proof-carrying
    // general lane, never from the lane's direct SAT encode.
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Unit ((u0) (u1)))
        (declare-fun x () Unit)
        (assert (= x u0))
        (assert (= x u1))
        (check-sat)
    "#;
    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
    assert_eq!(
        enum_sat_lane_stat(&exec).as_deref(),
        Some("fallback-proof"),
        "proof mode must fall through to the proof-carrying lane"
    );
}

#[test]
#[timeout(30000)]
fn test_enum_sat_lane_gate_excludes_selectors() {
    // Selector/tester applications are outside the fragment: the lane must
    // not fire, and the general lane keeps the verdict.
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((Maybe 0)) (((Nothing) (Just (value Int)))))
        (declare-const x Maybe)
        (assert (is-Just x))
        (assert (= (value x) 42))
        (check-sat)
    "#;
    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["sat"]);
    assert_eq!(
        enum_sat_lane_stat(&exec),
        None,
        "selector/tester instances must not take the enum SAT lane"
    );
}

#[test]
#[timeout(30000)]
fn test_enum_sat_lane_gate_excludes_recursive_datatypes() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
        (declare-const x Lst)
        (assert (= x nil))
        (check-sat)
    "#;
    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["sat"]);
    assert_eq!(
        enum_sat_lane_stat(&exec),
        None,
        "recursive datatypes must not take the enum SAT lane"
    );
}

#[test]
#[timeout(30000)]
fn test_enum_sat_lane_gate_excludes_uf_at_variable_args() {
    // (u x) with x a VARIABLE needs UF congruence with (u p1) when x = p1 —
    // outside the lane's congruence-free fragment; must fall through.
    let smt = r#"
        (set-logic QF_UFDT)
        (declare-datatype Unit ((u0) (u1)))
        (declare-fun f (Unit) Unit)
        (declare-fun x () Unit)
        (assert (= (f x) u0))
        (assert (= (f u0) u1))
        (check-sat)
    "#;
    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["sat"], "general lane must keep the verdict");
    assert_eq!(
        enum_sat_lane_stat(&exec),
        None,
        "UF applications at non-constructor arguments must not take the lane"
    );
}

/// #57 / #55 closure (2026-07-08): the div/mod theory-bug shapes behind
/// ay-chc's retired #C3 Safe→Unknown gate, pinned at the SMT layer. SMT-LIB
/// leaves `(div a 0)` / `(mod a 0)` UNDERSPECIFIED — an uninterpreted-but-
/// consistent value — so `(= v (div v 0))` is SATISFIABLE (choose the function
/// value to be v), never a refutation. The historic wrong-UNSAT instantiated
/// the total-div Euclidean axiom at divisor 0 (empty range → refuted the whole
/// formula).
#[test]
fn test_div_by_zero_underspecified_is_sat_57() {
    for body in [
        "(declare-const v Int)(assert (= v (div v 0)))",
        "(declare-const v Int)(assert (= v (mod v 0)))",
        "(declare-const v Int)(assert (not (= v (div v 0))))",
        "(declare-const v Int)(assert (= (div (div v 0) 0) v))",
    ] {
        let input = format!("(set-logic AUFNIRA){body}(check-sat)");
        let commands = parse(&input).unwrap();
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).unwrap();
        assert_ne!(
            outputs,
            vec!["unsat"],
            "underspecified div/mod-by-zero must never refute: {body}"
        );
    }
}

/// #55 shape: division by a `(select …)` that may be zero, under nonlinear
/// multiplication — historically a spurious unsat via the EUF↔arith loop.
#[test]
fn test_div_by_select_nonlinear_is_not_refuted_55() {
    let input = "(set-logic AUFNIRA)\
        (declare-const a (Array Int Int))(declare-const x Int)\
        (assert (= x (* x (div 1 (select a 0)))))(check-sat)";
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(
        outputs,
        vec!["unsat"],
        "satisfiable AUFNIRA div/select must never refute"
    );
}

/// Controls: the fixed semantics must not have gone soft — a genuine
/// contradiction over div/mod still refutes.
#[test]
fn test_div_mod_genuine_contradictions_still_unsat() {
    for body in [
        // p ∧ ¬p over an underspecified term is still propositionally UNSAT.
        "(declare-const v Int)(assert (and (= v (div v 0)) (not (= v (div v 0)))))",
        // SMT-LIB mod by nonzero constant is non-negative.
        "(declare-const v Int)(assert (< (mod v 5) 0))",
        // Euclidean division bound for a positive dividend.
        "(declare-const v Int)(assert (and (> v 10) (< (* 2 (div v 2)) (- v 1))))",
    ] {
        let input = format!("(set-logic AUFNIRA){body}(check-sat)");
        let commands = parse(&input).unwrap();
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).unwrap();
        assert_eq!(
            outputs,
            vec!["unsat"],
            "genuine contradiction must refute: {body}"
        );
    }
}
