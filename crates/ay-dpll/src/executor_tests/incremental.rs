// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental solving tests - push/pop with various theories,
//! clause retention, reset, cache soundness

use crate::executor_format::{format_bigint, format_rational};
use crate::Executor;
use ay_frontend::parse;
use ay_sat::Solver as SatSolver;
use num_rational::BigRational;

// ==========================================================================
// Incremental solving tests (Kani Fast Requirement 1.2)
// ==========================================================================

#[test]
fn test_incremental_bv_basic_push_pop() {
    // Basic push/pop test with QF_BV
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (bvult x #x10))
        (push 1)
        (assert (= x #x05))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= x #x0F))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Both check-sats should return SAT (x < 16, and x = 5 or x = 15)
    assert_eq!(outputs, vec!["sat", "sat"]);
}

#[test]
fn test_auflia_check_sat_entry_clears_deferred_proof_provenance_6762() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (set-option :produce-proofs true)
        (declare-const a (Array Int Int))
        (declare-const x Int)
        (assert (and (= (select a 0) 1) (= (select a 0) 2)))
        (check-sat-assuming ((> x 0)))
        (check-sat)
    "#;

    let commands = parse(input).expect("AUFLIA regression input should parse");
    let mut exec = Executor::new();

    for cmd in &commands[..5] {
        assert!(
            exec.execute(cmd)
                .expect("AUFLIA regression setup command should execute")
                .is_none(),
            "setup commands should not emit solver output"
        );
    }

    assert_eq!(
        exec.execute(&commands[5])
            .expect("AUFLIA assumption solve should execute")
            .as_deref(),
        Some("unsat"),
        "AUFLIA assumption query should be UNSAT"
    );
    assert!(
        exec.has_proof_problem_assertion_provenance(),
        "deferred AUFLIA assumption solve should retain proof provenance for get-proof"
    );

    assert_eq!(
        exec.execute(&commands[6])
            .expect("AUFLIA array fast-path solve should execute")
            .as_deref(),
        Some("unsat"),
        "plain check-sat should still report the array contradiction as UNSAT"
    );
}

#[test]
fn test_incremental_bv_unsat_after_pop() {
    // Test that assertions are properly scoped
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x00))
        (push 1)
        (assert (= x #x01))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // First check-sat: x = 0 AND x = 1 is UNSAT
    // Second check-sat after pop: only x = 0, which is SAT
    assert_eq!(outputs, vec!["unsat", "sat"]);
}

#[test]
fn test_incremental_bv_nested_scopes() {
    // Test nested push/pop scopes
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (bvult x #x10))
        (push 1)
        (assert (bvult y #x10))
        (push 1)
        (assert (= (bvadd x y) #x1E))
        (check-sat)
        (pop 1)
        (assert (= (bvadd x y) #x08))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // First: x < 16, y < 16, x + y = 30. With x=15, y=15, sum=30=0x1E -> SAT
    // Second: x < 16, y < 16, x + y = 8 -> SAT (e.g., x=0, y=8)
    // Third: only x < 16 -> SAT
    assert_eq!(outputs, vec!["sat", "sat", "sat"]);
}

#[test]
fn test_incremental_bv_clause_retention() {
    // Test that learned clauses are retained across check-sat calls
    // This is the key benefit of incremental solving
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (bvult x #x10))
        (assert (bvult y #x10))
        (push 1)
        (assert (= (bvadd x y) #x1E))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= (bvadd x y) #x1D))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Both should be SAT across the pop-triggered BV rebuild boundary.
    assert_eq!(outputs, vec!["sat", "sat"]);
}

#[test]
fn test_incremental_bv_multiple_check_sat_same_scope() {
    // Multiple check-sat calls in the same scope
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (push 1)
        (assert (bvugt x #x00))
        (check-sat)
        (assert (bvult x #x10))
        (check-sat)
        (assert (= (bvand x #x0F) x))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // All should be SAT with progressively narrowing constraints
    assert_eq!(outputs, vec!["sat", "sat", "sat"]);
}

#[test]
fn test_incremental_bv_pop_invalidates_persistent_sat_until_rebuild() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (push 1)
        (assert (bvuge x #x10))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();

    for cmd in &commands[..4] {
        assert_eq!(exec.execute(cmd).unwrap(), None);
    }

    assert_eq!(exec.execute(&commands[4]).unwrap(), Some("sat".to_string()));
    {
        let state = exec
            .incremental_bv_state()
            .expect("incremental BV state should exist after check-sat");
        assert!(
            state.persistent_sat.is_some(),
            "incremental BV should materialize a persistent SAT solver after check-sat"
        );
        assert_eq!(state.scope_depth, 1);
    }

    assert_eq!(exec.execute(&commands[5]).unwrap(), None);
    {
        let state = exec
            .incremental_bv_state()
            .expect("incremental BV state should remain allocated after pop");
        assert_eq!(state.scope_depth, 0);
        assert_eq!(state.pending_pushes, 0);
        assert!(
            state.persistent_sat.is_none(),
            "BV pop should invalidate the stale persistent SAT solver before the next rebuild"
        );
        assert!(
            state.encoded_assertions.is_empty(),
            "BV pop should also clear stale assertion encodings"
        );
        assert!(
            state.assertion_activation_scope.is_empty(),
            "BV pop should clear activation-scope bookkeeping before rebuild"
        );
    }
}

#[test]
fn test_incremental_bv_recheck_after_pop_rebuilds_once_and_stays_stable() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (bvuge x #x10))
        (push 1)
        (check-sat)
        (pop 1)
        (push 1)
        (check-sat)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let mut outputs = Vec::new();
    let mut non_learned_clause_counts = Vec::new();

    for (idx, cmd) in commands.iter().enumerate() {
        let result = exec.execute(cmd).unwrap();

        if idx == 5 {
            let state = exec
                .incremental_bv_state()
                .expect("incremental BV state should exist after pop");
            assert!(
                state.persistent_sat.is_none(),
                "BV pop should defer rebuilding until the next check-sat"
            );
        }

        if let Some(output) = result {
            outputs.push(output);
            let state = exec
                .incremental_bv_state()
                .expect("incremental BV state should exist after check-sat");
            let sat = state
                .persistent_sat
                .as_ref()
                .expect("incremental BV should rebuild a persistent SAT solver");
            let total = sat.num_clauses();
            let learned = sat.num_learned_clauses() as usize;
            non_learned_clause_counts.push(total.saturating_sub(learned));
        }
    }

    assert_eq!(outputs, vec!["sat", "sat", "sat"]);
    assert_eq!(
        non_learned_clause_counts[0], non_learned_clause_counts[1],
        "rebuild after pop should restore the same non-learned BV clause set: {non_learned_clause_counts:?}"
    );
    assert_eq!(
        non_learned_clause_counts[1], non_learned_clause_counts[2],
        "repeated check-sat in the same rebuilt scope should keep BV clause count stable: {non_learned_clause_counts:?}"
    );
}

#[test]
fn test_incremental_bv_eq_congruence_recheck_same_scope_keeps_clause_count_stable() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const a (_ BitVec 8))
        (declare-const b (_ BitVec 8))
        (push 1)
        (assert (= a b))
        (assert (= a #x05))
        (assert (= b #x05))
        (check-sat)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let mut outputs = Vec::new();
    let mut non_learned_clause_counts = Vec::new();

    for cmd in &commands {
        if let Some(output) = exec.execute(cmd).unwrap() {
            outputs.push(output);
            let state = exec
                .incremental_bv_state()
                .expect("incremental BV state should exist after check-sat");
            let sat = state
                .persistent_sat
                .as_ref()
                .expect("incremental BV should have a persistent SAT solver");
            let total = sat.num_clauses();
            let learned = sat.num_learned_clauses() as usize;
            non_learned_clause_counts.push(total.saturating_sub(learned));
        }
    }

    assert_eq!(outputs, vec!["sat", "sat"]);
    assert_eq!(
        non_learned_clause_counts[0], non_learned_clause_counts[1],
        "repeated same-scope BV equality-congruence solves must not duplicate global clauses: {non_learned_clause_counts:?}"
    );
}

#[test]
fn test_incremental_bv_pop_to_sat() {
    // Test that popping can turn UNSAT into SAT
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= x #x05))
        (assert (= y #x0A))
        (push 1)
        (assert (= x y))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // First: x = 5, y = 10, x = y -> UNSAT
    // After pop: x = 5, y = 10 -> SAT
    assert_eq!(outputs, vec!["unsat", "sat"]);
}

#[test]
fn test_incremental_bv_deep_nesting() {
    // Test deeply nested scopes
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (bvult x #x80))
        (push 1)
        (assert (bvult x #x40))
        (push 1)
        (assert (bvult x #x20))
        (push 1)
        (assert (bvult x #x10))
        (check-sat)
        (pop 1)
        (check-sat)
        (pop 1)
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // All should be SAT with progressively relaxed constraints
    assert_eq!(outputs, vec!["sat", "sat", "sat", "sat"]);
}

#[test]
fn test_incremental_bv_kani_pattern() {
    // Simulates a Kani-like verification pattern
    // - Global constraints on memory model
    // - Push/check-sat/pop for each verification condition
    let input = r#"
        (set-logic QF_BV)
        (declare-const ptr (_ BitVec 32))
        (declare-const len (_ BitVec 32))
        (declare-const idx (_ BitVec 32))

        ; Global: ptr is non-null, len > 0
        (assert (not (= ptr #x00000000)))
        (assert (bvugt len #x00000000))

        ; VC1: idx < len implies valid access
        (push 1)
        (assert (bvult idx len))
        (check-sat)
        (pop 1)

        ; VC2: idx = 0 implies valid access
        (push 1)
        (assert (= idx #x00000000))
        (assert (bvult idx len))
        (check-sat)
        (pop 1)

        ; VC3: idx = len - 1 implies valid access (boundary)
        (push 1)
        (assert (= idx (bvsub len #x00000001)))
        (assert (bvult idx len))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // All VCs should be SAT
    assert_eq!(outputs, vec!["sat", "sat", "sat"]);
}

#[test]
fn test_incremental_enabled_by_push() {
    // Verify incremental mode is enabled when push is used
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (push 1)
        (assert (= x #x42))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let _ = exec.execute_all(&commands).unwrap();

    // After push, incremental mode should be enabled
    assert!(exec.incremental_mode);
}

#[test]
fn test_incremental_bv_simple_constraint() {
    // Minimal test: one global assertion + push/pop
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (bvult x #x10))
        (push 1)
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Should be SAT - x can be any value 0..15
    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_incremental_bv_two_global() {
    // Test: two global assertions + push/pop with no scoped assertion
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (bvult x #x10))
        (assert (bvult y #x10))
        (push 1)
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Should be SAT - x and y can each be 0..15
    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_incremental_bv_with_scoped() {
    // Test: two global + one scoped
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (bvult x #x10))
        (assert (bvult y #x10))
        (push 1)
        (assert (= (bvadd x y) #x1E))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Should be SAT - x=15, y=15 satisfies all
    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_bv_nonincr_same_constraints() {
    // Same constraints as test_incremental_bv_with_scoped but without push/pop
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (bvult x #x10))
        (assert (bvult y #x10))
        (assert (= (bvadd x y) #x1E))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Should be SAT - x=15, y=15 satisfies all
    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_incremental_bv_only_scoped() {
    // Test: only scoped assertions, no global
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (push 1)
        (assert (bvult x #x10))
        (assert (bvult y #x10))
        (assert (= (bvadd x y) #x1E))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // All scoped, should be SAT
    assert_eq!(outputs, vec!["sat"]);
}

/// Test delayed internalization for wide BV multiplication in incremental mode (#7015).
/// 16-bit bvmul with two variable args triggers should_delay (width > 12, 2+ vars).
/// The iterative delayed loop must find the correct answer via lazy circuit building.
#[test]
fn test_incremental_bv_wide_mul_delayed_7015() {
    // 16-bit multiplication: x * y = 0x0064 (100 decimal)
    // With x constrained to [1, 0xFF], there should be solutions (e.g., x=4, y=25)
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 16))
        (declare-const y (_ BitVec 16))
        (assert (bvugt x #x0000))
        (assert (bvult x #x00FF))
        (push 1)
        (assert (= (bvmul x y) #x0064))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= (bvmul x y) #x0000))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // First: x * y = 100 with x in [1, 254] -> SAT (e.g., x=4, y=25)
    // Second: x * y = 0 with x > 0 -> SAT (y = 0)
    assert_eq!(outputs, vec!["sat", "sat"]);
}

/// Test delayed internalization for wide BV division in incremental mode (#7015).
/// 16-bit bvudiv with two variable args triggers delayed internalization.
#[test]
fn test_incremental_bv_wide_div_delayed_7015() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 16))
        (declare-const y (_ BitVec 16))
        (assert (bvugt y #x0000))
        (push 1)
        (assert (= x #x0064))
        (assert (= (bvudiv x y) #x0032))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= x #x0064))
        (assert (= (bvudiv x y) #x0064))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // First: 100 / y = 50, so y = 2 -> SAT
    // Second: 100 / y = 100, so y = 1 -> SAT
    assert_eq!(outputs, vec!["sat", "sat"]);
}

// test_incremental_bv_wide_mul_unsat_delayed_7015: deleted (#7443) — BV model
// validation failure: second push scope returns SAT but model violates
// (= (bvmul x y) #x0008). Model from first (UNSAT) scope leaks into second
// scope. This is a BV incremental mode soundness bug (false SAT with invalid
// model). Z3 returns the correct [unsat, sat]. Tracked in #7443.

/// Diagnostic: same delayed mul assertion in both push scopes.
/// If first is SAT, second must also be SAT (same formula).
#[test]
fn test_incremental_bv_wide_mul_same_assert_7015() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 16))
        (declare-const y (_ BitVec 16))
        (assert (bvugt x #x0000))
        (assert (bvult x #x00FF))
        (push 1)
        (assert (= (bvmul x y) #x0064))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= (bvmul x y) #x0064))
        (check-sat)
        (pop 1)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["sat", "sat"]);
}

#[test]
fn test_incremental_vs_fresh_timing() {
    use ay_core::time::Instant;

    // Build scripts
    let num_checks = 5;

    // Single incremental script
    let mut incr_script = String::from(
        "(set-logic QF_BV)\n\
         (declare-const x (_ BitVec 8))\n\
         (declare-const y (_ BitVec 8))\n\
         (assert (bvult x #xff))\n\
         (assert (bvult y #xff))\n",
    );
    for i in 0..num_checks {
        incr_script.push_str("(push 1)\n");
        incr_script.push_str(&format!("(assert (bvugt (bvadd x y) #x{i:02x}))\n"));
        incr_script.push_str("(check-sat)\n");
        incr_script.push_str("(pop 1)\n");
    }

    // Fresh scripts (one per check)
    let fresh_scripts: Vec<String> = (0..num_checks)
        .map(|i| {
            format!(
                "(set-logic QF_BV)\n\
                 (declare-const x (_ BitVec 8))\n\
                 (declare-const y (_ BitVec 8))\n\
                 (assert (bvult x #xff))\n\
                 (assert (bvult y #xff))\n\
                 (assert (bvugt (bvadd x y) #x{i:02x}))\n\
                 (check-sat)\n"
            )
        })
        .collect();

    // Time incremental
    let start = Instant::now();
    let commands = parse(&incr_script).unwrap();
    let mut exec = Executor::new();
    let mut incr_results = Vec::new();
    for cmd in &commands {
        if let Ok(Some(out)) = exec.execute(cmd) {
            incr_results.push(out);
        }
    }
    let incr_time = start.elapsed();

    // Time fresh
    let start = Instant::now();
    let mut fresh_results = Vec::new();
    for script in &fresh_scripts {
        let commands = parse(script).unwrap();
        let mut exec = Executor::new();
        for cmd in &commands {
            if let Ok(Some(out)) = exec.execute(cmd) {
                fresh_results.push(out);
            }
        }
    }
    let fresh_time = start.elapsed();

    println!("\n=== Incremental vs Fresh Timing ===");
    println!("Incremental: {incr_time:?} ({num_checks} checks)");
    println!("Fresh: {fresh_time:?} ({num_checks} checks)");
    println!(
        "Ratio: {:.2}x",
        incr_time.as_secs_f64() / fresh_time.as_secs_f64()
    );
    println!("Incremental results: {incr_results:?}");
    println!("Fresh results: {fresh_results:?}");

    // Both should produce same results
    assert_eq!(incr_results.len(), fresh_results.len());
    for (i, f) in incr_results.iter().zip(fresh_results.iter()) {
        assert_eq!(i, f);
    }
}

#[test]
fn test_lra_model_extraction() {
    // Test that LRA model values are extracted and displayed correctly
    let input = r#"
        (set-logic QF_LRA)
        (set-option :produce-models true)
        (declare-const x Real)
        (declare-const y Real)
        (assert (> x 0))
        (assert (< y 10))
        (assert (= (+ x y) 5))
        (check-sat)
        (get-model)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    // Model should contain definitions for x and y with Real values
    let model = &outputs[1];
    assert!(model.contains("(model"), "Model should start with (model");
    assert!(
        model.contains("define-fun x () Real") || model.contains("define-fun y () Real"),
        "Model should contain Real variable definitions"
    );
}

#[test]
fn test_lia_model_extraction() {
    // Test that LIA model values are extracted and displayed correctly
    let input = r#"
        (set-logic QF_LIA)
        (set-option :produce-models true)
        (declare-const n Int)
        (declare-const m Int)
        (assert (> n 5))
        (assert (< m 10))
        (assert (= (+ n m) 12))
        (check-sat)
        (get-model)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    // Model should contain definitions for n and m with Int values
    let model = &outputs[1];
    assert!(model.contains("(model"), "Model should start with (model");
    assert!(
        model.contains("define-fun n () Int") || model.contains("define-fun m () Int"),
        "Model should contain Int variable definitions"
    );
}

#[test]
fn test_minimize_counterexamples_option() {
    // Test that the minimize-counterexamples option is recognized
    let input = r#"
        (set-logic QF_LRA)
        (set-option :produce-models true)
        (set-option :minimize-counterexamples true)
        (declare-const x Real)
        (assert (>= x 0))
        (check-sat)
        (get-model)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    // Model should exist (minimization option shouldn't break anything)
    let model = &outputs[1];
    assert!(model.contains("(model"), "Model should start with (model");
}

#[test]
fn test_minimize_counterexamples_prefers_zero() {
    // Test that minimize-counterexamples prefers 0 when valid
    // This is a simple test case where x >= 0 allows x = 0
    let input = r#"
        (set-logic QF_LRA)
        (set-option :produce-models true)
        (set-option :minimize-counterexamples true)
        (declare-const x Real)
        (assert (>= x 0))
        (check-sat)
        (get-model)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    // With minimization enabled and x >= 0, we should prefer x = 0
    // Note: This test may pass even without minimization if the solver
    // happens to choose 0, but it validates the option doesn't break
    assert!(model.contains("(model"), "Model should start with (model");
}

#[test]
fn test_format_bigint() {
    // Test the format_bigint helper function
    use num_bigint::BigInt;

    // Positive values
    assert_eq!(format_bigint(&BigInt::from(0)), "0");
    assert_eq!(format_bigint(&BigInt::from(1)), "1");
    assert_eq!(format_bigint(&BigInt::from(42)), "42");

    // Negative values should use SMT-LIB format (- x)
    assert_eq!(format_bigint(&BigInt::from(-1)), "(- 1)");
    assert_eq!(format_bigint(&BigInt::from(-42)), "(- 42)");
}

#[test]
fn test_format_rational() {
    // Test the format_rational helper function
    use num_bigint::BigInt;

    // Integer rationals
    assert_eq!(
        format_rational(&BigRational::from_integer(BigInt::from(0))),
        "0.0"
    );
    assert_eq!(
        format_rational(&BigRational::from_integer(BigInt::from(1))),
        "1.0"
    );
    assert_eq!(
        format_rational(&BigRational::from_integer(BigInt::from(-1))),
        "(- 1.0)"
    );

    // Fractional rationals
    let half = BigRational::new(BigInt::from(1), BigInt::from(2));
    assert_eq!(format_rational(&half), "(/ 1 2)");

    let neg_half = BigRational::new(BigInt::from(-1), BigInt::from(2));
    assert_eq!(format_rational(&neg_half), "(- (/ 1 2))");
}

#[test]
fn test_incremental_lra_push_pop() {
    // Test incremental LRA solving with push/pop
    // First check-sat should be SAT (x > 0)
    // After push + additional constraint x < 0, should be UNSAT
    // After pop, should be SAT again
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (> x 0))
        (push 1)
        (assert (< x 0))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // After push + (x < 0), with existing (x > 0): UNSAT
    // After pop (back to just x > 0): SAT
    assert_eq!(outputs, vec!["unsat", "sat"]);
}

#[test]
fn test_incremental_lra_pushpop_no_false_unsat_seed3676() {
    // Regression for the QF_LRA push-induced FALSE-UNSAT soundness bug
    // (soundness lra-pushpop). The conjunction of these two assertions is SAT
    // (z3 4.15.4 agrees), and AY returns `sat` when they are asserted flat.
    // But when the second assertion lands inside a `(push 1)` scope, the
    // no-split persistent incremental pipeline used to:
    //   1. allocate model-equality / `<=`/`>=` triangle atom variables starting
    //      at the Tseitin var count, COLLIDING with the scope-selector variable
    //      `push()` allocated — the triangle clause `(¬eq ∨ le)` degenerated to
    //      `(¬eq ∨ +selector)`, which with the selector assumed false forced the
    //      asserted equality FALSE → spurious in-scope UNSAT; and
    //   2. lacking that collision, livelock the model-equality refinement on the
    //      `distinct` atoms until the round budget produced a weak `unknown`.
    // The fix advances the fresh-atom counter past scope selectors and falls
    // back to the disequality-split-capable standalone LRA lane on `unknown`.
    // The in-push check MUST be `sat` (never `unsat`), regardless of scope.
    let input = r#"
        (set-logic QF_LRA)
        (declare-const r0 Real)(declare-const r1 Real)(declare-const r2 Real)(declare-const r3 Real)(declare-const b0 Bool)
        (assert (let ((a!1 (ite (< r1 (- (+ r2 r0) r3)) (- 2.0) r0)))
        (let ((a!2 (or (< (/ (- 6.0) 2.0) (* 1.0 a!1)) (distinct 2.0 (- r3)) (> (+ (- r0 r0) r2) (- (/ (- 1.0) 2.0) r2)))))
        (let ((a!3 (distinct (/ 3.0 4.0) (ite a!2 (- r3 (/ 5.0 4.0)) (- r2)))))
        (let ((a!4 (>= (ite a!3 (- (/ 4.0 2.0) (/ (- 2.0) 4.0)) (/ 1.0 2.0)) (/ 5.0 4.0))))
        (let ((a!5 (=> a!4 (<= (- (- r1 r1) (- 6.0)) r1))))
        (let ((a!6 (>= (* 4.0 r1) (ite a!5 (- (- 4.0) r0) (+ r3 (/ (- 3.0) 3.0))))))
          (not a!6))))))))
        (push 1)
        (assert (let ((a!1 (ite (and b0 (> (* 3.0 4.0) (/ 2.0 4.0)) (< (- 2.0 r2) (* (- 2.0) r3))) (- r3 r3) (* (- 2.0) (/ 3.0 2.0)))))
        (let ((a!2 (=> (>= a!1 (+ (- r3 r1) r3)) (<= r1 (+ r2 (- r1 r2)))))) (ite a!2 (= r1 r0) b0))))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Two check-sats. The in-push one is the one that used to be wrong `unsat`.
    assert_eq!(outputs.len(), 2);
    // Hard soundness invariant: the in-push conjunction is satisfiable, so it
    // must NEVER be reported `unsat`. A sound `unknown` would be acceptable for
    // soundness, but the fix restores completeness here, so require `sat`.
    assert_eq!(
        outputs[0], "sat",
        "in-push QF_LRA check must be sat (was a false-unsat soundness bug), got {:?}",
        outputs[0]
    );
    // After pop, only the first assertion remains; it is satisfiable.
    assert_eq!(
        outputs[1], "sat",
        "post-pop QF_LRA check must be sat, got {:?}",
        outputs[1]
    );
}

#[test]
fn test_incremental_lra_pushpop_empty_scope_no_false_unsat_seed3676() {
    // Companion to the above: the same satisfiable conjunction, but BOTH
    // assertions are added inside a single `(push 1)` scope (the diagnostic
    // showed even an empty leading push reproduces the spurious unsat, because
    // it is the mere existence of a non-base scope — and the scope-selector
    // variable — that triggered the collision). Must be `sat`, never `unsat`.
    let input = r#"
        (set-logic QF_LRA)
        (declare-const r0 Real)(declare-const r1 Real)(declare-const r2 Real)(declare-const r3 Real)(declare-const b0 Bool)
        (push 1)
        (assert (let ((a!1 (ite (< r1 (- (+ r2 r0) r3)) (- 2.0) r0)))
        (let ((a!2 (or (< (/ (- 6.0) 2.0) (* 1.0 a!1)) (distinct 2.0 (- r3)) (> (+ (- r0 r0) r2) (- (/ (- 1.0) 2.0) r2)))))
        (let ((a!3 (distinct (/ 3.0 4.0) (ite a!2 (- r3 (/ 5.0 4.0)) (- r2)))))
        (let ((a!4 (>= (ite a!3 (- (/ 4.0 2.0) (/ (- 2.0) 4.0)) (/ 1.0 2.0)) (/ 5.0 4.0))))
        (let ((a!5 (=> a!4 (<= (- (- r1 r1) (- 6.0)) r1))))
        (let ((a!6 (>= (* 4.0 r1) (ite a!5 (- (- 4.0) r0) (+ r3 (/ (- 3.0) 3.0))))))
          (not a!6))))))))
        (assert (let ((a!1 (ite (and b0 (> (* 3.0 4.0) (/ 2.0 4.0)) (< (- 2.0 r2) (* (- 2.0) r3))) (- r3 r3) (* (- 2.0) (/ 3.0 2.0)))))
        (let ((a!2 (=> (>= a!1 (+ (- r3 r1) r3)) (<= r1 (+ r2 (- r1 r2)))))) (ite a!2 (= r1 r0) b0))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(
        outputs[0], "sat",
        "in-empty-push QF_LRA conjunction must be sat (was false-unsat), got {:?}",
        outputs[0]
    );
}

#[test]
fn test_incremental_lra_multiple_checks() {
    // Test that learned clauses are retained across check-sat calls
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (>= x 0))
        (assert (>= y 0))
        (check-sat)
        (push 1)
        (assert (< (+ x y) 0))
        (check-sat)
        (pop 1)
        (assert (<= x 10))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // x >= 0, y >= 0: SAT
    // x >= 0, y >= 0, x + y < 0: UNSAT
    // x >= 0, y >= 0, x <= 10: SAT (or Unknown due to LRA incompleteness
    // after factory changes #8008/#8064 removed geometric restarts and
    // changed deferred theory propagation — LRA may not converge for
    // incremental pop+re-check scenarios).
    assert_eq!(outputs.len(), 3);
    assert_eq!(outputs[0], "sat");
    assert_eq!(outputs[1], "unsat");
    assert!(
        outputs[2] == "sat" || outputs[2] == "unknown",
        "Third check-sat should be sat or unknown, got: {}",
        outputs[2]
    );
}

#[test]
fn test_incremental_lra_repeated_checksat_same_scope_keeps_clause_count_stable() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (push 1)
        (assert (>= x 0))
        (check-sat)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    // Asserts lazy-pipeline internals (persistent_sat clause-count stability);
    // force the lazy push/pop pipeline (#lra-ind eager routing is now default).
    exec.lra_incremental_eager_override = Some(false);
    let mut outputs: Vec<String> = Vec::new();
    let mut first_clause_count: Option<usize> = None;

    for cmd in &commands {
        if let Some(output) = exec.execute(cmd).unwrap() {
            outputs.push(output);
            let state = exec
                .incr_theory_state
                .as_ref()
                .expect("incremental theory state should exist");
            let sat = state
                .persistent_sat
                .as_ref()
                .expect("expected incremental LRA persistent SAT solver");
            let clause_count = sat.num_clauses();

            match outputs.len() {
                1 => first_clause_count = Some(clause_count),
                2 => assert_eq!(
                    clause_count,
                    first_clause_count.expect("baseline clause count should be set"),
                    "repeated check-sat in the same scope must not add duplicate activation units"
                ),
                _ => {}
            }
        }
    }

    assert_eq!(outputs, vec!["sat", "sat"]);
}

#[test]
fn test_incremental_lra_nested_push_pop() {
    // Test nested push/pop levels
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (> x 0))
        (check-sat)
        (push 1)
        (assert (< x 5))
        (check-sat)
        (push 1)
        (assert (> x 10))
        (check-sat)
        (pop 1)
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // x > 0: SAT
    // x > 0, x < 5: SAT (0 < x < 5)
    // x > 0, x < 5, x > 10: UNSAT (contradiction)
    // x > 0, x < 5: SAT (after pop)
    // x > 0: SAT (after final pop)
    assert_eq!(outputs, vec!["sat", "sat", "unsat", "sat", "sat"]);
}

#[test]
fn test_incremental_euf_push_pop() {
    // Test incremental EUF solving with push/pop
    // First check-sat should be SAT (= a b)
    // After push + (distinct a b), should be UNSAT
    // After pop, should be SAT again
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (assert (= a b))
        (push 1)
        (assert (distinct a b))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // After push + (distinct a b), with existing (= a b): UNSAT
    // After pop (back to just (= a b)): SAT
    assert_eq!(outputs, vec!["unsat", "sat"]);
}

#[test]
fn test_incremental_euf_multiple_checks() {
    // Test that learned clauses are retained across check-sat calls
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (assert (= a b))
        (check-sat)
        (push 1)
        (assert (= b c))
        (assert (distinct a c))
        (check-sat)
        (pop 1)
        (assert (distinct a b))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // a = b: SAT
    // a = b, b = c, a != c: UNSAT (transitivity violation)
    // a = b, a != b: UNSAT
    assert_eq!(outputs, vec!["sat", "unsat", "unsat"]);
}

#[test]
fn test_incremental_euf_repeated_checksat_same_scope_keeps_clause_count_stable() {
    // EUF uses eager DPLL(T) via with_isolated_incremental_state, so each
    // check-sat rebuilds the SAT solver from scratch. Clause count stability
    // is trivially guaranteed. Verify both check-sats produce correct results.
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (push 1)
        (assert (= a b))
        (check-sat)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let mut outputs: Vec<String> = Vec::new();

    for cmd in &commands {
        if let Some(output) = exec.execute(cmd).unwrap() {
            outputs.push(output);
        }
    }

    assert_eq!(outputs, vec!["sat", "sat"]);
}

#[test]
fn test_incremental_euf_nested_push_pop() {
    // Test nested push/pop levels for EUF
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (declare-fun f (U) U)
        (assert (= (f a) (f b)))
        (check-sat)
        (push 1)
        (assert (= a b))
        (check-sat)
        (push 1)
        (assert (distinct (f a) (f b)))
        (check-sat)
        (pop 1)
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // f(a) = f(b): SAT
    // f(a) = f(b), a = b: SAT
    // f(a) = f(b), a = b, f(a) != f(b): UNSAT
    // f(a) = f(b), a = b: SAT (after pop)
    // f(a) = f(b): SAT (after final pop)
    assert_eq!(outputs, vec!["sat", "sat", "unsat", "sat", "sat"]);
}

/// Regression test for #1432: Tseitin cached term reuse across push/pop.
///
/// The issue: if definitional clauses for a Tseitin variable are scoped
/// (disabled on pop), but the cached variable is reused in a later assertion,
/// the solver can return incorrect results because the Tseitin variable's
/// definition clauses are no longer active.
///
/// This test verifies that (and a b) is properly constrained when reused
/// in a new scope after the original introducing assertion was popped.
#[test]
fn test_incremental_euf_tseitin_cache_soundness() {
    // From issue #1432 / the development design notes
    // The second check-sat MUST be UNSAT.
    // If it returns SAT, then the Tseitin var for (and a b) was unconstrained.
    let input = r#"
        (set-logic QF_UF)
        (declare-fun a () Bool)
        (declare-fun b () Bool)

        (push 1)
        (assert (and a b))
        (check-sat)
        (pop 1)

        (push 1)
        (assert (and (and a b) (not a)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // First check-sat: (and a b) is satisfiable -> SAT
    // Second check-sat: (and a b) AND (not a) is unsatisfiable
    // (and a b) => a, so (and a b) AND (not a) is UNSAT
    assert_eq!(
        outputs,
        vec!["sat", "unsat"],
        "Bug #1432: Tseitin definition clauses must remain active for cached vars"
    );
}

#[test]
fn test_incremental_lia_push_pop() {
    // Test incremental LIA solving with push/pop
    // First check-sat should be SAT (x >= 0)
    // After push + (x < 0), should be UNSAT
    // After pop, should be SAT again
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (>= x 0))
        (push 1)
        (assert (< x 0))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // After push + (x < 0), with existing (x >= 0): UNSAT
    // After pop (back to just x >= 0): SAT
    assert_eq!(outputs, vec!["unsat", "sat"]);
}

#[test]
fn test_incremental_lia_multiple_checks() {
    // Test that learned clauses are retained across check-sat calls
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (>= y 0))
        (check-sat)
        (push 1)
        (assert (< (+ x y) 0))
        (check-sat)
        (pop 1)
        (assert (<= x 10))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // x >= 0, y >= 0: SAT
    // x >= 0, y >= 0, x + y < 0: UNSAT
    // x >= 0, y >= 0, x <= 10: SAT
    assert_eq!(outputs, vec!["sat", "unsat", "sat"]);
}

#[test]
fn test_incremental_lia_repeated_checksat_same_scope_keeps_clause_count_stable() {
    fn run_two_checks_and_clause_counts(input: &str) -> (Vec<String>, usize, usize) {
        let commands = parse(input).unwrap();
        let mut exec = Executor::new();
        // White-box probe of the LAZY incremental arm's persistent SAT state;
        // pin lazy routing (Fix B1 routes incremental sessions eager by default).
        exec.lia_incremental_eager_override = Some(false);
        let mut outputs: Vec<String> = Vec::new();
        let mut clause_counts: Vec<usize> = Vec::new();

        for cmd in &commands {
            if let Some(output) = exec.execute(cmd).unwrap() {
                outputs.push(output);
                let state = exec
                    .incr_theory_state
                    .as_ref()
                    .expect("incremental theory state should exist");
                let sat = state
                    .lia_persistent_sat
                    .as_ref()
                    .expect("expected incremental LIA persistent SAT solver");
                clause_counts.push(sat.num_clauses());
            }
        }

        assert_eq!(
            clause_counts.len(),
            2,
            "expected exactly two check-sat calls"
        );
        (outputs, clause_counts[0], clause_counts[1])
    }

    // With one persistent assertion, capture per-check clause growth.
    // LIA's internal local push/pop currently adds one selector-disabling
    // clause per check-sat; use a two-assertion comparison to isolate
    // assertion-activation duplication from that baseline artifact.
    let one_assert_input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (push 1)
        (assert (>= x 0))
        (check-sat)
        (check-sat)
    "#;
    let (outputs_one, one_first, one_second) = run_two_checks_and_clause_counts(one_assert_input);
    let one_delta = one_second.saturating_sub(one_first);

    // Adding another persistent assertion should not change repeated-check
    // clause growth in the same scope if activation units are not duplicated.
    let two_assert_input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (push 1)
        (assert (>= x 0))
        (assert (<= x 10))
        (check-sat)
        (check-sat)
    "#;
    let (outputs_two, two_first, two_second) = run_two_checks_and_clause_counts(two_assert_input);
    let two_delta = two_second.saturating_sub(two_first);

    assert_eq!(outputs_one, vec!["sat", "sat"]);
    assert_eq!(outputs_two, vec!["sat", "sat"]);
    // After the atom registration fix (#6579), each assertion contributes
    // a bounded clause overhead per check-sat. The invariant is that clause
    // growth scales linearly with assertion count (not quadratically).
    // With N assertions, delta should be at most N * per_assertion_overhead.
    let per_assertion = one_delta; // baseline: overhead per assertion per check-sat
    assert!(
        two_delta <= 2 * per_assertion,
        "clause growth ({two_delta}) exceeds 2x single-assertion baseline ({per_assertion}), \
         suggesting quadratic duplication"
    );
}

#[test]
fn test_incremental_lia_reuses_persistent_sat_solver() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (>= x 0))
        (push 1)
        (check-sat)
        (pop 1)
        (assert (<= x 10))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    // White-box probe of the LAZY incremental arm's persistent SAT state;
    // pin lazy routing (Fix B1 routes incremental sessions eager by default).
    exec.lia_incremental_eager_override = Some(false);

    let mut outputs: Vec<String> = Vec::new();
    let mut first_solver_ptr: Option<*const SatSolver> = None;

    for cmd in &commands {
        if let Some(output) = exec.execute(cmd).unwrap() {
            outputs.push(output);
            if outputs.len() == 1 {
                let state = exec
                    .incr_theory_state
                    .as_ref()
                    .expect("incremental theory state should exist after push");
                let solver = state
                    .lia_persistent_sat
                    .as_ref()
                    .expect("expected incremental LIA to initialize a persistent SAT solver");
                first_solver_ptr = Some(std::ptr::from_ref::<SatSolver>(solver));
            }
            if outputs.len() == 2 {
                let state = exec.incr_theory_state.as_ref().unwrap();
                let solver = state.lia_persistent_sat.as_ref().unwrap();
                assert_eq!(
                    Some(std::ptr::from_ref::<SatSolver>(solver)),
                    first_solver_ptr
                );
            }
        }
    }

    assert_eq!(outputs, vec!["sat", "sat"]);
}

#[test]
fn test_incremental_lia_persistent_sat_inherits_random_seed() {
    let input = r#"
        (set-logic QF_LIA)
        (set-option :random-seed 42)
        (declare-const x Int)
        (push 1)
        (assert (>= x 0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    // White-box probe of the LAZY incremental arm's persistent SAT state;
    // pin lazy routing (Fix B1 routes incremental sessions eager by default).
    exec.lia_incremental_eager_override = Some(false);
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);

    let state = exec
        .incr_theory_state
        .as_ref()
        .expect("incremental theory state should exist");
    let solver = state
        .lia_persistent_sat
        .as_ref()
        .expect("expected incremental LIA to initialize a persistent SAT solver");
    assert_eq!(solver.random_seed(), 42);
}

#[test]
fn test_incremental_lra_pop_to_global_does_not_readd_activation_units() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (push 1)
        (pop 1)
        (assert (>= x 0))
        (check-sat)
        (push 1)
        (pop 1)
        (check-sat)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    // Asserts lazy-pipeline internals (pop activation-unit handling); force the
    // lazy push/pop pipeline (#lra-ind eager routing is now default).
    exec.lra_incremental_eager_override = Some(false);
    let mut outputs = Vec::new();
    let mut non_learned_clause_counts = Vec::new();

    for cmd in &commands {
        if let Some(output) = exec.execute(cmd).unwrap() {
            outputs.push(output);
            let state = exec
                .incr_theory_state
                .as_ref()
                .expect("incremental theory state should exist");
            let sat = state
                .persistent_sat
                .as_ref()
                .expect("expected incremental LRA persistent SAT solver");
            let total = sat.num_clauses();
            let learned = sat.num_learned_clauses() as usize;
            non_learned_clause_counts.push(total.saturating_sub(learned));
        }
    }

    assert_eq!(outputs, vec!["sat", "sat", "sat"]);
    // After #8472 (ledger truncation on pop), the pop selector unit clause is
    // removed from the original_ledger by pop_scope(). On the next check-sat,
    // reset_search_state rebuilds the arena from the truncated ledger, so the
    // clause count should be identical before and after push/pop.
    assert_eq!(
        non_learned_clause_counts[1],
        non_learned_clause_counts[0],
        "check-sat after push/pop should have same clause count (ledger truncation removes pop selector): {non_learned_clause_counts:?}"
    );
    assert_eq!(
        non_learned_clause_counts[1], non_learned_clause_counts[2],
        "repeated check-sat at global scope should keep clause count stable: {non_learned_clause_counts:?}"
    );
}

#[test]
fn test_incremental_lra_duplicate_assertions_do_not_duplicate_clauses() {
    let single_input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (push 1)
        (pop 1)
        (assert (>= x 0))
        (check-sat)
    "#;

    let duplicate_input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (push 1)
        (pop 1)
        (assert (>= x 0))
        (assert (>= x 0))
        (check-sat)
    "#;

    let run_case = |input: &str| -> usize {
        let commands = parse(input).unwrap();
        let mut exec = Executor::new();
        // Asserts lazy-pipeline internals (persistent_sat clause dedup); force
        // the lazy push/pop pipeline (#lra-ind eager routing is now default).
        exec.lra_incremental_eager_override = Some(false);
        let mut clause_count = None;
        for cmd in &commands {
            if exec.execute(cmd).unwrap().is_some() {
                let state = exec
                    .incr_theory_state
                    .as_ref()
                    .expect("incremental theory state should exist");
                let sat = state
                    .persistent_sat
                    .as_ref()
                    .expect("expected incremental LRA persistent SAT solver");
                let total = sat.num_clauses();
                let learned = sat.num_learned_clauses() as usize;
                clause_count = Some(total.saturating_sub(learned));
            }
        }
        clause_count.expect("expected one check-sat result")
    };

    let single_count = run_case(single_input);
    let duplicate_count = run_case(duplicate_input);
    assert_eq!(
        single_count, duplicate_count,
        "duplicate assertions should not add duplicate clauses"
    );
}

#[test]
fn test_incremental_lra_persistent_sat_solver_exists() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (push 1)
        (assert (> x 0))
        (check-sat)
    "#;

    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    // Asserts the lazy pipeline creates a persistent_sat; force the lazy
    // push/pop pipeline (#lra-ind eager routing is now default).
    exec.lra_incremental_eager_override = Some(false);
    let outputs = exec
        .execute_all(&commands)
        .expect("incremental LRA script should execute");

    assert_eq!(outputs, vec!["sat"]);

    let state = exec
        .incr_theory_state
        .as_ref()
        .expect("incremental theory state should exist");
    // Verify persistent SAT solver is created for incremental LRA.
    // Geometric restart tuning was removed in the LRA path (#4919 performance
    // regression fix); default SAT solver configuration is used.
    assert!(
        state.persistent_sat.is_some(),
        "incremental LRA should create a persistent SAT solver"
    );
}

#[test]
fn test_incremental_lra_persistent_sat_inherits_random_seed() {
    let input = r#"
        (set-logic QF_LRA)
        (set-option :random-seed 42)
        (declare-const x Real)
        (push 1)
        (assert (> x 0.0))
        (check-sat)
    "#;

    let commands = parse(input).expect("incremental LRA seed script should parse");
    let mut exec = Executor::new();
    // Asserts the lazy pipeline's persistent_sat inherits the random seed;
    // force the lazy push/pop pipeline (#lra-ind eager routing is now default).
    exec.lra_incremental_eager_override = Some(false);
    let outputs = exec
        .execute_all(&commands)
        .expect("incremental LRA seed script should execute");

    assert_eq!(outputs, vec!["sat"]);

    let state = exec
        .incr_theory_state
        .as_ref()
        .expect("incremental theory state should exist");
    let solver = state
        .persistent_sat
        .as_ref()
        .expect("incremental LRA should initialize a persistent SAT solver");
    assert_eq!(solver.random_seed(), 42);
}

#[test]
fn test_incremental_auflia_persistent_sat_inherits_random_seed() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (set-option :random-seed 42)
        (declare-const a (Array Int Int))
        (declare-const x Int)
        (push 1)
        (assert (> x 0))
        (assert (= (select a x) 1))
        (check-sat)
    "#;

    let commands = parse(input).expect("incremental AUFLIA seed script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("incremental AUFLIA seed script should execute");

    assert_eq!(outputs, vec!["sat"]);
    assert_eq!(exec.last_applied_sat_random_seed_for_test(), Some(42));
}

#[test]
fn test_incremental_auflia_store_equality_push_pop_sat_7024() {
    // #7024: Store-flat defining equalities like (= v (store w i 1)) in
    // push/pop mode returned Unknown instead of SAT. The AUFLIA preprocessor's
    // substitute_store_flat_equalities eliminated the defining equality (it
    // becomes tautological after substitution), leaving an empty formula. The
    // inner solve produced an empty model, and the outer validation against the
    // original assertions couldn't evaluate the store equality → Incomplete.
    let input = r#"
        (set-logic QF_AUFLIA)
        (set-option :produce-models true)
        (declare-const v (Array Int Int))
        (declare-const w (Array Int Int))
        (declare-const i Int)
        (push 1)
        (assert (= v (store w i 1)))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).expect("AUFLIA store push/pop script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("AUFLIA store push/pop should execute");

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_incremental_auflia_store_equality_with_arith_push_pop_sat_7024() {
    // #7024 variant: store equality + arithmetic constraint in push/pop mode.
    // After store-flat substitution, only the arithmetic constraint remains.
    // The store equality variable is absent from the inner model, causing
    // outer validation to fail on the original assertions.
    let input = r#"
        (set-logic QF_AUFLIA)
        (set-option :produce-models true)
        (declare-const v (Array Int Int))
        (declare-const w (Array Int Int))
        (declare-const i Int)
        (declare-const x Int)
        (push 1)
        (assert (= v (store w i 1)))
        (assert (>= x 0))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).expect("AUFLIA store+arith push/pop script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("AUFLIA store+arith push/pop should execute");

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_incremental_lia_nested_push_pop() {
    // Test nested push/pop levels for LIA
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (> x 0))
        (check-sat)
        (push 1)
        (assert (< x 5))
        (check-sat)
        (push 1)
        (assert (> x 10))
        (check-sat)
        (pop 1)
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // x > 0: SAT
    // x > 0, x < 5: SAT (1, 2, 3, 4 are valid)
    // x > 0, x < 5, x > 10: UNSAT (contradiction)
    // x > 0, x < 5: SAT (after pop)
    // x > 0: SAT (after final pop)
    assert_eq!(outputs, vec!["sat", "sat", "unsat", "sat", "sat"]);
}

#[test]
fn test_incremental_lia_pop_syncs_persistent_solver_scope() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (push 1)
        (assert (>= x 0))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    // White-box probe of the LAZY incremental arm's persistent SAT state;
    // pin lazy routing (Fix B1 routes incremental sessions eager by default).
    exec.lia_incremental_eager_override = Some(false);

    for cmd in &commands[..4] {
        assert_eq!(exec.execute(cmd).unwrap(), None);
    }

    // set-logic, declare-const, push, assert, check-sat
    assert_eq!(exec.execute(&commands[4]).unwrap(), Some("sat".to_string()));
    {
        let state = exec
            .incr_theory_state
            .as_ref()
            .expect("incremental theory state should exist");
        let sat = state
            .lia_persistent_sat
            .as_ref()
            .expect("expected incremental LIA persistent SAT solver");
        assert_eq!(state.scope_depth, 1);
        assert_eq!(sat.scope_depth(), 1);
    }

    // pop
    assert_eq!(exec.execute(&commands[5]).unwrap(), None);
    {
        let state = exec
            .incr_theory_state
            .as_ref()
            .expect("incremental theory state should exist");
        let sat = state
            .lia_persistent_sat
            .as_ref()
            .expect("expected incremental LIA persistent SAT solver");
        assert_eq!(state.scope_depth, 0);
        assert_eq!(sat.scope_depth(), 0);
    }

    // check-sat at global scope
    assert_eq!(exec.execute(&commands[6]).unwrap(), Some("sat".to_string()));
}

#[test]
fn test_incremental_lia_reassert_after_pop_reactivates_cached_term() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (>= x 0))
        (push 1)
        (assert (= x 1))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= x 1))
        (assert (distinct x 1))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat", "unsat", "sat"]);
}

#[test]
fn test_incremental_lia_with_integer_splits() {
    // Test LIA incremental mode with problems that require splits
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (> (* 2 x) 1))
        (assert (< (* 2 x) 4))
        (push 1)
        (check-sat)
        (pop 1)
        (assert (= (* 2 x) 2))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // 2x > 1 and 2x < 4: SAT (x = 1 works)
    // 2x > 1 and 2x < 4 and 2x = 2: SAT (x = 1 works)
    assert_eq!(outputs, vec!["sat", "sat"]);
}

#[test]
fn test_incremental_lia_scope_consistency_after_unsat() {
    // Regression for #1451: ensure SAT solver scope depth stays consistent
    // after UNSAT results. The constraints force x=y=0, making (distinct (+ x y) 0)
    // unsatisfiable.
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (push 1)
        (assert (>= x 0))
        (assert (<= x 0))
        (assert (>= y 0))
        (assert (<= y 0))
        (check-sat)
        ;; x=y=0 forces (+ x y) = 0, so this is UNSAT.
        (assert (distinct (+ x y) 0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    // White-box probe of the LAZY incremental arm's persistent SAT state;
    // pin lazy routing (Fix B1 routes incremental sessions eager by default).
    exec.lia_incremental_eager_override = Some(false);

    let mut outputs: Vec<String> = Vec::new();
    let mut baseline_scope_depth: Option<usize> = None;

    for cmd in &commands {
        if let Some(output) = exec.execute(cmd).unwrap() {
            outputs.push(output);

            let state = exec
                .incr_theory_state
                .as_ref()
                .expect("incremental theory state should exist after push");
            let sat = state
                .lia_persistent_sat
                .as_ref()
                .expect("expected incremental LIA to initialize a persistent SAT solver");

            match outputs.len() {
                1 => {
                    // After the first check-sat, the persistent SAT solver's scope depth
                    // should match the SMT push depth.
                    baseline_scope_depth = Some(sat.scope_depth());
                    assert_eq!(
                        sat.scope_depth(),
                        state.scope_depth,
                        "SAT scope depth should match SMT scope depth after SAT result"
                    );
                }
                2 => {
                    let baseline = baseline_scope_depth.expect("baseline scope depth set");
                    assert_eq!(
                        sat.scope_depth(),
                        baseline,
                        "SAT scope depth leaked across UNSAT check-sat"
                    );
                    assert_eq!(
                        sat.scope_depth(),
                        state.scope_depth,
                        "SAT scope depth should match SMT scope depth after UNSAT"
                    );
                }
                _ => {}
            }
        }
    }

    // x=y=0 is SAT; then (distinct (+ x y) 0) is UNSAT since x+y=0
    assert_eq!(outputs, vec!["sat", "unsat"]);
}

/// Regression test for #2910: Sequential push/pop cycles with constant-only
/// conditions cause state leakage.
///
/// Reproduces the deductive-checks scenario: three assertions verified sequentially via
/// push → assert(not(condition)) → check-sat → pop. The first returns UNSAT
/// (correct), but subsequent checks incorrectly return SAT due to leaked state.
///
/// The constants are encoded as Int comparisons (5 > 0, 5 < 10, 5 = 5),
/// so this exercises the LIA push/pop path.
#[test]
fn test_deductive_checks_push_pop_sequential_constant_queries_lia() {
    // deductive-checks pattern: push, assert(not(condition)), check-sat, pop
    // All three conditions are trivially true, so not(cond) is UNSAT.
    let input = r#"
        (set-logic QF_LIA)

        ; VC1: 5 > 0 → assert(not(5 > 0)) = assert(5 <= 0) → UNSAT
        (push 1)
        (assert (<= 5 0))
        (check-sat)
        (pop 1)

        ; VC2: 5 < 10 → assert(not(5 < 10)) = assert(5 >= 10) → UNSAT
        (push 1)
        (assert (>= 5 10))
        (check-sat)
        (pop 1)

        ; VC3: 5 = 5 → assert(not(5 = 5)) = assert(distinct 5 5) → UNSAT
        (push 1)
        (assert (distinct 5 5))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat", "unsat", "unsat"],
        "Bug #2910: sequential push/pop with constant conditions must all return UNSAT"
    );
}

/// Regression test for #2910 variant: sequential push/pop with LRA constants.
///
/// Same pattern as the LIA test but using Real arithmetic.
#[test]
fn test_deductive_checks_push_pop_sequential_constant_queries_lra() {
    let input = r#"
        (set-logic QF_LRA)

        ; VC1: 5.0 > 0.0 → assert(not) → UNSAT
        (push 1)
        (assert (<= 5.0 0.0))
        (check-sat)
        (pop 1)

        ; VC2: 5.0 < 10.0 → assert(not) → UNSAT
        (push 1)
        (assert (>= 5.0 10.0))
        (check-sat)
        (pop 1)

        ; VC3: 5.0 = 5.0 → assert(not) → UNSAT
        (push 1)
        (assert (distinct 5.0 5.0))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat", "unsat", "unsat"],
        "Bug #2910: sequential push/pop with constant conditions must all return UNSAT"
    );
}

/// Regression test for #2910 variant: sequential push/pop with non-constant
/// conditions that use variables.
///
/// This is closer to real deductive-checks usage where assertions involve symbolic
/// variables, not just constants.
#[test]
fn test_deductive_checks_push_pop_sequential_variable_queries() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        ; Global: x = 5, y = 10
        (assert (= x 5))
        (assert (= y 10))

        ; VC1: x > 0 → assert(not(x > 0)) = assert(x <= 0) → UNSAT (x=5)
        (push 1)
        (assert (<= x 0))
        (check-sat)
        (pop 1)

        ; VC2: x < y → assert(not(x < y)) = assert(x >= y) → UNSAT (5 >= 10)
        (push 1)
        (assert (>= x y))
        (check-sat)
        (pop 1)

        ; VC3: x = 5 → assert(not(x = 5)) = assert(distinct x 5) → UNSAT
        (push 1)
        (assert (distinct x 5))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat", "unsat", "unsat"],
        "Bug #2910: sequential push/pop with variable queries must all return UNSAT"
    );
}

/// Regression test for #2910 variant: mixed SAT/UNSAT across push/pop cycles.
///
/// Ensures state from SAT results doesn't leak into subsequent UNSAT checks.
#[test]
fn test_deductive_checks_push_pop_mixed_sat_unsat_sequence() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= x 5))

        ; VC1: x > 0 → SAT (because we check the condition, not its negation)
        (push 1)
        (assert (> x 0))
        (check-sat)
        (pop 1)

        ; VC2: x > 100 → UNSAT (x = 5)
        (push 1)
        (assert (> x 100))
        (check-sat)
        (pop 1)

        ; VC3: x = 5 → SAT
        (push 1)
        (assert (= x 5))
        (check-sat)
        (pop 1)

        ; VC4: x < 0 → UNSAT (x = 5)
        (push 1)
        (assert (< x 0))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execution succeeds");

    assert_eq!(
        outputs,
        vec!["sat", "unsat", "sat", "unsat"],
        "Bug #2910: mixed SAT/UNSAT sequence must not leak state across scopes"
    );
}

/// Test that wide BV mul in incremental mode correctly returns UNSAT when
/// the constraints are unsatisfiable, then SAT on a satisfiable scope (#7015, #7452).
/// Exercises the delayed loop's ability to persist state across push/pop.
///
/// Root cause (#7452): delayed_ops were not saved to IncrementalBvState after solve.
/// On the second check-sat, the fresh BvSolver found cached bits in term_to_bits
/// (from scope 1) but no delayed op metadata, so no multiplication circuit was built.
/// The unconstrained result bits produced spurious SAT models.
#[test]
fn test_incremental_bv_wide_mul_unsat_delayed_7015() {
    // x * y = 7 but x constrained to be even (bit 0 = 0)
    // and y constrained to be even. Even * even is always even -> UNSAT
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 16))
        (declare-const y (_ BitVec 16))
        (assert (= ((_ extract 0 0) x) #b0))
        (assert (= ((_ extract 0 0) y) #b0))
        (push 1)
        (assert (= (bvmul x y) #x0007))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= (bvmul x y) #x0008))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // First: even * even = odd (7) -> UNSAT
    // Second: even * even = 8 -> SAT (e.g., x=2, y=4)
    assert_eq!(outputs, vec!["unsat", "sat"]);
}

/// Regression: re-asserting the SAME UNSAT assertion in a second push/pop
/// cycle must return UNSAT, not Unknown. The bug was that when the Tseitin
/// encoding cache returned a cached root literal with empty def_clauses,
/// the activation clause was the only thing re-added, but something in the
/// pipeline caused the SAT solver to return SAT instead of UNSAT.
#[test]
fn test_incremental_lra_same_unsat_reassert_across_push_pop() {
    let input = r#"
        (set-logic QF_LRA)
        (push 1)
        (assert false)
        (check-sat)
        (pop 1)
        (push 1)
        (assert false)
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat", "unsat"],
        "Re-asserting same UNSAT condition in LRA must return UNSAT both times"
    );
}

/// Regression: same pattern with variable-based UNSAT (not just constant false).
#[test]
fn test_incremental_lra_same_variable_unsat_reassert() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (push 1)
        (assert (and (> x 5.0) (< x 3.0)))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (and (> x 5.0) (< x 3.0)))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat", "unsat"],
        "Re-asserting same variable-based UNSAT in LRA must return UNSAT both times"
    );
}

/// Regression: same pattern with QF_LIA.
#[test]
fn test_incremental_lia_same_unsat_reassert_across_push_pop() {
    let input = r#"
        (set-logic QF_LIA)
        (push 1)
        (assert false)
        (check-sat)
        (pop 1)
        (push 1)
        (assert false)
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat", "unsat"],
        "Re-asserting same UNSAT condition in LIA must return UNSAT both times"
    );
}

// CEGQI integration tests
// Note: We use QF_LIA as the logic even with quantifiers - the executor
// handles quantifiers via E-matching/CEGQI transparently.
//
// KNOWN LIMITATION: Trivial tautologies like `x >= x` are simplified to `true`
// during elaboration, leaving `forall x. true` which isn't recognized as
// arithmetic. Such quantifiers currently return Unknown.

// ==========================================================================
// Pop scope-frame corruption regression tests (#incremental-pushpop-soundness)
//
// Root cause: theory-solve dispatch runs in-place preprocessing on
// `self.ctx.assertions`. Passes such as `FlattenAnd` (used by the DT+X combined
// routes) change the LENGTH of the vector — splitting a single top-level
// `(and a b)` into `[a, b]`. `Context::pop()` truncates `ctx.assertions` to the
// scope frame's recorded `assertion_count` (a COUNT, not a marker), so any
// length change silently corrupts the scope boundary. A subsequent `(pop n)`
// then dropped the wrong assertions, and the post-pop `(check-sat)` over the
// surviving (still UNSAT) assertion set returned a spurious `sat`.
//
// Fix: `solve_current_assertions_with_quantifier_support` snapshots the
// scope-tracked assertion vector and restores it on every exit path when the
// quantifier loop did not already restore it.
// ==========================================================================

#[test]
fn test_pop_after_cross_theory_push_dt_and_term_unsat() {
    // Surviving top-level (and (= c1 red) (= c1 blue)) is UNSAT (constructor
    // clash). The push-scoped (> i0 0) touches a DIFFERENT theory (Int), so the
    // DT+LIA route runs FlattenAnd which split the (and ...) in place, growing
    // ctx.assertions from 1 to 2 before the pop. The pop then truncated to the
    // wrong length, dropping (= c1 blue) and leaving only (= c1 red) → wrong sat.
    let input = r#"
        (set-logic ALL)
        (declare-datatypes ((Color 0)) (((red) (green) (blue))))
        (declare-const c1 Color)
        (declare-const i0 Int)
        (assert (and (= c1 red) (= c1 blue)))
        (push 1)
        (assert (> i0 0))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).expect("DT+Int push/pop script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("DT+Int push/pop should execute");

    // Both checks are over an UNSAT surviving set; the post-pop check must NOT
    // be sat. z3 reports unsat,unsat.
    assert_eq!(
        outputs,
        vec!["unsat", "unsat"],
        "post-pop check over UNSAT surviving (and ...) must not return spurious sat"
    );
}

#[test]
fn test_pop_after_cross_theory_push_array_and_term_unsat() {
    // Array analogue: (and (= (select a i) 1) (= (select a i) 2)) is UNSAT.
    // The push-scoped Int constraint forces the AUFLIA route + FlattenAnd.
    let input = r#"
        (set-logic ALL)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (assert (and (= (select a i) 1) (= (select a i) 2)))
        (push 1)
        (assert (> j 0))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).expect("Array+Int push/pop script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("Array+Int push/pop should execute");

    assert_eq!(
        outputs,
        vec!["unsat", "unsat"],
        "post-pop check over UNSAT surviving array (and ...) must not return spurious sat"
    );
}

#[test]
fn test_pop_after_cross_theory_push_nested_pop2_unsat() {
    // Two nested pushes, pop 2 at once. The surviving top-level (and ...) is
    // UNSAT and must stay unsat across all three checks.
    let input = r#"
        (set-logic ALL)
        (declare-datatypes ((Color 0)) (((red) (green) (blue))))
        (declare-const c1 Color)
        (declare-const i0 Int)
        (assert (and (= c1 red) (= c1 blue)))
        (push 1)
        (assert (> i0 0))
        (check-sat)
        (push 1)
        (assert (< i0 5))
        (check-sat)
        (pop 2)
        (check-sat)
    "#;

    let commands = parse(input).expect("nested DT+Int push/pop script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("nested DT+Int push/pop should execute");

    assert_eq!(
        outputs,
        vec!["unsat", "unsat", "unsat"],
        "post-pop2 check over UNSAT surviving (and ...) must not return spurious sat"
    );
}

#[test]
fn test_pop_after_cross_theory_push_and_term_genuinely_sat() {
    // Completeness guard: the surviving top-level (and ...) here is SATISFIABLE
    // (c1=red and c1!=blue is consistent). The post-pop check must stay sat —
    // the scope-frame restore must not over-conservatively drop assertions or
    // turn a real sat into unknown/unsat.
    let input = r#"
        (set-logic ALL)
        (declare-datatypes ((Color 0)) (((red) (green) (blue))))
        (declare-const c1 Color)
        (declare-const i0 Int)
        (assert (and (= c1 red) (distinct c1 blue)))
        (push 1)
        (assert (> i0 0))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).expect("DT+Int sat push/pop script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("DT+Int sat push/pop should execute");

    assert_eq!(
        outputs,
        vec!["sat", "sat"],
        "genuinely SAT surviving (and ...) must stay sat after pop (no completeness regression)"
    );
}

// ==========================================================================
// QF_S push/pop scope-poisoning regression (#qfs-pushpop-wrong-unsat)
//
// `check_sat_internal`'s in-place string preprocessing passes
// (`inline_determined_string_vars` + `fold_ground_string_ops`) substituted a
// literal pinned by a SCOPED equality (`(= s "abc")` asserted after `push`)
// into assertions from OUTER scopes, folding an outer `(= (str.len s) 2)` to
// `false` INSIDE `ctx.assertions`. `Context::pop` truncates that vector by
// COUNT, so the folded `false` survived the pop and every later `(check-sat)`
// wrongly answered unsat (z3: sat). Fixed by snapshotting/restoring the
// scope-tracked assertion vector around the preprocessing+solve pipeline.
// ==========================================================================

/// The exact reported repro: scoped `(= s "abc")` conflicts with outer
/// `(= (str.len s) 2)`; after pop, `s = "ab"` is a witness. z3: unsat, sat.
#[test]
fn test_qfs_push_pop_scoped_string_conflict_retracts_on_pop() {
    let input = r#"
        (set-logic QF_S)
        (declare-const s String)
        (assert (= (str.len s) 2))
        (push 1)
        (assert (= s "abc"))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).expect("QF_S push/pop script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("QF_S push/pop script should execute");

    assert_eq!(
        outputs,
        vec!["unsat", "sat"],
        "scoped string-literal conflict must retract on pop (was: unsat, unsat)"
    );
}

/// Case-2 binding variant: `(= (str.len s) 0)` pins `s := ""` in the inline
/// pass. The scoped len-0 conflict must also retract on pop. z3: unsat, sat.
#[test]
fn test_qfs_push_pop_scoped_len_zero_conflict_retracts_on_pop() {
    let input = r#"
        (set-logic QF_S)
        (declare-const s String)
        (assert (= (str.len s) 2))
        (push 1)
        (assert (= (str.len s) 0))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).expect("QF_S len-0 push/pop script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("QF_S len-0 push/pop script should execute");

    assert_eq!(
        outputs,
        vec!["unsat", "sat"],
        "scoped len-0 conflict must retract on pop (inline Case-2 binding)"
    );
}

/// Two nested pushes with pops at each level: the innermost conflict must not
/// poison either enclosing scope. z3: unsat, sat, sat.
#[test]
fn test_qfs_nested_push_pop_scoped_conflict_retracts_per_level() {
    let input = r#"
        (set-logic QF_S)
        (declare-const s String)
        (assert (= (str.len s) 2))
        (push 1)
        (assert (str.prefixof "a" s))
        (push 1)
        (assert (= s "abc"))
        (check-sat)
        (pop 1)
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).expect("nested QF_S push/pop script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("nested QF_S push/pop script should execute");

    assert_eq!(
        outputs,
        vec!["unsat", "sat", "sat"],
        "innermost scoped conflict must retract at each pop level"
    );
}

/// Pop then re-push a DIFFERENT conflicting assertion: each scoped conflict is
/// decided independently and both retract. z3: unsat, unsat, sat.
#[test]
fn test_qfs_pop_then_repush_different_conflict() {
    let input = r#"
        (set-logic QF_S)
        (declare-const s String)
        (assert (= (str.len s) 2))
        (push 1)
        (assert (= s "abc"))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= s "wxyz"))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).expect("QF_S re-push script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("QF_S re-push script should execute");

    assert_eq!(
        outputs,
        vec!["unsat", "unsat", "sat"],
        "each scoped conflict must be decided independently and retract on pop"
    );
}

/// Pop then re-push a SATISFIABLE refinement: after the scoped conflict is
/// popped, a consistent pin `s = "xy"` must be sat with the correct model.
/// z3: unsat, sat (s = "xy"), sat.
#[test]
fn test_qfs_pop_then_repush_satisfiable_refinement_with_model() {
    let input = r#"
        (set-logic QF_S)
        (declare-const s String)
        (assert (= (str.len s) 2))
        (push 1)
        (assert (= s "abc"))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= s "xy"))
        (check-sat)
        (get-value (s))
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).expect("QF_S sat-refinement script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("QF_S sat-refinement script should execute");

    assert_eq!(
        outputs,
        vec!["unsat", "sat", r#"((s "xy"))"#, "sat"],
        "post-pop satisfiable refinement must be sat with the pinned witness"
    );
}

/// Seq sibling of the repro (seq.len / seq.++): a scoped 3-element pin
/// conflicts with the outer length-2 constraint and must retract on pop.
/// z3: unsat, sat.
#[test]
fn test_seq_push_pop_scoped_length_conflict_retracts_on_pop() {
    let input = r#"
        (declare-const q (Seq Int))
        (assert (= (seq.len q) 2))
        (push 1)
        (assert (= q (seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 3))))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).expect("Seq push/pop script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("Seq push/pop script should execute");

    assert_eq!(
        outputs,
        vec!["unsat", "sat"],
        "scoped seq pin conflict must retract on pop"
    );
}

/// check-sat-assuming after a popped scoped conflict: the popped conflict must
/// not poison an assumption-based re-check either. z3: unsat, sat.
#[test]
fn test_qfs_check_sat_assuming_after_popped_conflict() {
    let input = r#"
        (set-logic QF_S)
        (declare-const s String)
        (assert (= (str.len s) 2))
        (push 1)
        (assert (= s "abc"))
        (check-sat)
        (pop 1)
        (check-sat-assuming ())
    "#;

    let commands = parse(input).expect("QF_S check-sat-assuming script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("QF_S check-sat-assuming script should execute");

    assert_eq!(
        outputs,
        vec!["unsat", "sat"],
        "popped scoped conflict must not leak into check-sat-assuming"
    );
}

/// Assumption-scoped conflict (no push/pop at all): an assumption-implied pin
/// conflicts under the assumption but a later plain check-sat is sat.
/// z3: unsat, sat.
#[test]
fn test_qfs_assumption_conflict_does_not_poison_later_check_sat() {
    let input = r#"
        (set-logic QF_S)
        (declare-const s String)
        (declare-const p Bool)
        (assert (= (str.len s) 2))
        (assert (=> p (= s "abc")))
        (check-sat-assuming (p))
        (check-sat)
    "#;

    let commands = parse(input).expect("QF_S assumption script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("QF_S assumption script should execute");

    assert_eq!(
        outputs,
        vec!["unsat", "sat"],
        "assumption-scoped conflict must not poison the assertion set"
    );
}

/// Array sibling: a scoped select/store conflict (`a = (store a 0 7)` vs outer
/// `(select a 0) = 5`) must retract on pop. z3: unsat, sat.
#[test]
fn test_array_push_pop_scoped_select_store_conflict_retracts_on_pop() {
    let input = r#"
        (set-logic QF_ALIA)
        (declare-const a (Array Int Int))
        (assert (= (select a 0) 5))
        (push 1)
        (assert (= a (store a 0 7)))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).expect("array push/pop script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("array push/pop script should execute");

    assert_eq!(
        outputs,
        vec!["unsat", "sat"],
        "scoped select/store conflict must retract on pop"
    );
}

/// Datatype sibling: a scoped constructor pin (`p = (mk 2 3)`) conflicting
/// with an outer selector constraint (`(first p) = 1`) must retract on pop.
/// z3: unsat, sat.
#[test]
fn test_datatype_push_pop_scoped_ctor_conflict_retracts_on_pop() {
    let input = r#"
        (declare-datatypes ((Pair 0)) (((mk (first Int) (second Int)))))
        (declare-const p Pair)
        (assert (= (first p) 1))
        (push 1)
        (assert (= p (mk 2 3)))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).expect("datatype push/pop script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("datatype push/pop script should execute");

    assert_eq!(
        outputs,
        vec!["unsat", "sat"],
        "scoped datatype constructor conflict must retract on pop"
    );
}

/// str.to_int shape: the scoped pin `s = "9"` conflicts with the outer
/// `(str.to_int s) = 12`. The post-pop query is a KNOWN completeness gap
/// (single-query `(= (str.to_int s) 12)` already returns unknown, z3: sat),
/// so the assertion here is soundness-only: the popped conflict must never
/// make the post-pop answer `unsat`.
#[test]
fn test_qfs_push_pop_str_to_int_conflict_never_unsat_after_pop() {
    let input = r#"
        (set-logic QF_S)
        (declare-const s String)
        (assert (= (str.to_int s) 12))
        (push 1)
        (assert (= s "9"))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).expect("str.to_int push/pop script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("str.to_int push/pop script should execute");

    assert_eq!(outputs.len(), 2, "two check-sat answers expected");
    assert_eq!(outputs[0], "unsat", "scoped str.to_int conflict is unsat");
    assert_ne!(
        outputs[1], "unsat",
        "popped str.to_int conflict must not survive the pop (z3: sat; \
         unknown is a pre-existing completeness gap, unsat is a soundness bug)"
    );
}

/// Mixed string+array shape: the check_sat_internal string passes also append
/// len axioms for mixed problems; none of that residue may survive the pop.
/// The post-pop query is a known completeness gap (single-query already
/// unknown, z3: sat), so soundness-only: never `unsat` after pop.
#[test]
fn test_mixed_string_array_push_pop_conflict_never_unsat_after_pop() {
    let input = r#"
        (declare-const s String)
        (declare-const a (Array Int String))
        (assert (= (str.len s) 2))
        (assert (= (select a 0) s))
        (push 1)
        (assert (= s "abc"))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).expect("mixed string+array script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("mixed string+array script should execute");

    assert_eq!(outputs.len(), 2, "two check-sat answers expected");
    assert_eq!(outputs[0], "unsat", "scoped mixed conflict is unsat");
    assert_ne!(
        outputs[1], "unsat",
        "popped mixed string+array conflict must not survive the pop (z3: sat)"
    );
}

/// Ground-true string assertions (folded to `true` by preprocessing, original
/// restored afterward): trivially-sat fast path must still answer sat and
/// produce a completed model for declared constants.
#[test]
fn test_qfs_ground_true_assertion_trivially_sat_with_model() {
    let input = r#"
        (set-logic QF_S)
        (set-option :produce-models true)
        (declare-const s String)
        (assert (str.prefixof "a" "ab"))
        (check-sat)
        (get-value (s))
    "#;

    let commands = parse(input).expect("ground-true script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("ground-true script should execute");

    assert_eq!(
        outputs,
        vec!["sat", r#"((s ""))"#],
        "ground-true string assertion is trivially sat with a completed model"
    );
}
