// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::ffi::{CStr, CString};

fn version_string() -> String {
    let version = ay_version();
    assert!(!version.is_null());

    // SAFETY: `ay_version` returns a valid heap-allocated C string or null.
    unsafe {
        let s = CStr::from_ptr(version)
            .to_str()
            .expect("test should succeed")
            .to_owned();
        ay_string_free(version);
        s
    }
}

#[test]
fn test_solver_new_free() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();
        assert!(!solver.is_null());
        ay_solver_free(solver);
    }
}

/// SMOKE TEST: Verifies ay_solver_free handles null pointers gracefully.
/// This is critical for FFI safety - callers may pass invalid pointers.
#[test]
fn test_solver_free_null() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        // Should not crash - null pointer handling is required for safe FFI.
        // No assertion needed: reaching this point without crash = success.
        ay_solver_free(std::ptr::null_mut());
    }
}

#[test]
fn test_solve_sat() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();
        let input = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (> x 0))
             (check-sat)",
        )
        .expect("test should succeed");

        let result = ay_solve_smtlib(solver, input.as_ptr());
        assert_eq!(result, AY_SAT);

        ay_solver_free(solver);
    }
}

#[test]
fn test_solve_unsat() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();
        let input = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (> x 0))
             (assert (< x 0))
             (check-sat)",
        )
        .expect("test should succeed");

        let result = ay_solve_smtlib(solver, input.as_ptr());
        assert_eq!(result, AY_UNSAT);

        ay_solver_free(solver);
    }
}

#[test]
fn test_parse_error() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();
        let input = CString::new("(invalid syntax here").expect("test should succeed");

        let result = ay_solve_smtlib(solver, input.as_ptr());
        assert_eq!(result, AY_ERROR);

        // Should have error message
        let error = ay_get_error(solver);
        assert!(!error.is_null());
        ay_string_free(error);

        ay_solver_free(solver);
    }
}

#[test]
fn test_quick_solve() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let input = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (> x 0))
             (check-sat)",
        )
        .expect("test should succeed");

        let result = ay_quick_solve(input.as_ptr());
        assert_eq!(result, AY_SAT);
    }
}

#[test]
fn test_solve_lia() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let input = CString::new(
            "(declare-const x Int)
             (declare-const y Int)
             (assert (> x 0))
             (assert (> y 0))
             (assert (= (+ x y) 10))
             (check-sat)",
        )
        .expect("test should succeed");

        let result = ay_solve_lia(input.as_ptr());
        assert_eq!(result, AY_SAT);
    }
}

#[test]
fn test_solve_sat_propositional() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let input = CString::new(
            "(declare-const p Bool)
             (declare-const q Bool)
             (assert (or p q))
             (assert (not p))
             (check-sat)",
        )
        .expect("test should succeed");

        let result = ay_solve_sat(input.as_ptr());
        assert_eq!(result, AY_SAT);
    }
}

#[test]
fn test_version() {
    let s = version_string();
    assert_eq!(s, env!("AY_BUILD_STAMP"));
    assert!(s.starts_with(env!("CARGO_PKG_VERSION")));
    assert!(s.contains("+build."));
    assert!(s.contains('@'));
}

#[test]
fn test_reset() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();

        // First solve
        let input1 = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (> x 0))
             (check-sat)",
        )
        .expect("test should succeed");
        let result1 = ay_solve_smtlib(solver, input1.as_ptr());
        assert_eq!(result1, AY_SAT);

        // Reset
        ay_reset(solver);

        // Second solve (fresh state)
        let input2 = CString::new(
            "(set-logic QF_LIA)
             (declare-const y Int)
             (assert (< y 0))
             (check-sat)",
        )
        .expect("test should succeed");
        let result2 = ay_solve_smtlib(solver, input2.as_ptr());
        assert_eq!(result2, AY_SAT);

        ay_solver_free(solver);
    }
}

#[test]
fn test_get_model() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();
        let input = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (= x 42))
             (check-sat)",
        )
        .expect("test should succeed");

        let result = ay_solve_smtlib(solver, input.as_ptr());
        assert_eq!(result, AY_SAT);

        let model = ay_get_model(solver);
        assert!(!model.is_null());

        let model_str = CStr::from_ptr(model).to_str().expect("test should succeed");
        assert!(model_str.contains('x'));
        assert!(model_str.contains("42"));

        ay_string_free(model);
        ay_solver_free(solver);
    }
}

// ========================================================================
// Memory lifecycle tests (#895)
// These tests verify CString allocation/free patterns don't cause UB.
// ========================================================================

/// Test repeated ay_get_model calls with proper freeing between each.
/// Verifies no double-free or use-after-free occurs.
#[test]
fn test_get_model_repeated_alloc_free() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();

        // First SAT solve
        let input1 = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (= x 42))
             (check-sat)",
        )
        .expect("test should succeed");
        assert_eq!(ay_solve_smtlib(solver, input1.as_ptr()), AY_SAT);

        // First model retrieval and free
        let model1 = ay_get_model(solver);
        assert!(!model1.is_null());
        let model1_str = CStr::from_ptr(model1)
            .to_str()
            .expect("test should succeed");
        assert!(model1_str.contains("42"));
        ay_string_free(model1);

        // Reset and second SAT solve with different value
        ay_reset(solver);
        let input2 = CString::new(
            "(set-logic QF_LIA)
             (declare-const y Int)
             (assert (= y 99))
             (check-sat)",
        )
        .expect("test should succeed");
        assert_eq!(ay_solve_smtlib(solver, input2.as_ptr()), AY_SAT);

        // Second model retrieval and free
        let model2 = ay_get_model(solver);
        assert!(!model2.is_null());
        let model2_str = CStr::from_ptr(model2)
            .to_str()
            .expect("test should succeed");
        assert!(model2_str.contains("99"));
        ay_string_free(model2);

        ay_solver_free(solver);
    }
}

/// Test ay_get_error lifecycle: call after error, free, call again when no error.
/// Verifies error state is properly cleared and string pointers are valid.
#[test]
fn test_get_error_lifecycle() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();

        // Initially no error - should return null
        let error_before = ay_get_error(solver);
        assert!(
            error_before.is_null(),
            "No error expected before any operations"
        );

        // Trigger a parse error
        let bad_input = CString::new("(invalid syntax").expect("test should succeed");
        let result = ay_solve_smtlib(solver, bad_input.as_ptr());
        assert_eq!(result, AY_ERROR);

        // Error should be set now
        let error1 = ay_get_error(solver);
        assert!(
            !error1.is_null(),
            "Error message expected after parse failure"
        );
        let error1_str = CStr::from_ptr(error1)
            .to_str()
            .expect("test should succeed");
        assert!(
            error1_str.contains("Parse") || error1_str.contains("error"),
            "Error should mention parse issue"
        );
        ay_string_free(error1);

        // Can retrieve error again (independent allocation each time)
        let error2 = ay_get_error(solver);
        assert!(!error2.is_null(), "Error should persist until cleared");
        ay_string_free(error2);

        // Successful operation should clear error
        let good_input = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (> x 0))
             (check-sat)",
        )
        .expect("test should succeed");
        let result2 = ay_solve_smtlib(solver, good_input.as_ptr());
        assert_eq!(result2, AY_SAT);

        // Error should be cleared now
        let error_after = ay_get_error(solver);
        assert!(
            error_after.is_null(),
            "Error should be cleared after successful operation"
        );

        ay_solver_free(solver);
    }
}

/// Test that strings obtained before ay_reset remain valid for freeing.
/// The reset shouldn't invalidate previously returned CStrings.
#[test]
fn test_reset_preserves_returned_string_validity() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();

        // Get a model
        let input = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (= x 42))
             (check-sat)",
        )
        .expect("test should succeed");
        assert_eq!(ay_solve_smtlib(solver, input.as_ptr()), AY_SAT);

        let model = ay_get_model(solver);
        assert!(!model.is_null());

        // Reset the solver (this should NOT affect the returned string)
        ay_reset(solver);

        // The model string should still be valid (independent allocation)
        // This tests that into_raw() properly transfers ownership
        let model_str = CStr::from_ptr(model).to_str().expect("test should succeed");
        assert!(model_str.contains("42"));

        // And can be freed safely after reset
        ay_string_free(model);

        ay_solver_free(solver);
    }
}

/// Test null pointer handling in ay_string_free (idempotent).
/// Multiple null frees should be safe.
#[test]
fn test_string_free_null_idempotent() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        // First null free
        ay_string_free(std::ptr::null_mut());
        // Second null free (should remain safe)
        ay_string_free(std::ptr::null_mut());
    }
}

/// Test ay_get_model handles UNSAT result without memory issues.
/// SMT-LIB doesn't define get-model behavior after UNSAT, so we just
/// ensure no memory errors occur regardless of what's returned.
#[test]
fn test_get_model_safe_after_unsat() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();

        let input = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (> x 0))
             (assert (< x 0))
             (check-sat)",
        )
        .expect("test should succeed");

        let result = ay_solve_smtlib(solver, input.as_ptr());
        assert_eq!(result, AY_UNSAT);

        // Behavior after UNSAT is undefined per SMT-LIB; we just ensure
        // no memory errors. If non-null, we must free it properly.
        let model = ay_get_model(solver);
        if !model.is_null() {
            ay_string_free(model);
        }

        ay_solver_free(solver);
    }
}

/// Test calling ay_get_model twice on the same SAT result without reset.
/// Each call should return an independently allocated string.
#[test]
fn test_get_model_twice_without_reset() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();

        let input = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (= x 42))
             (check-sat)",
        )
        .expect("test should succeed");
        assert_eq!(ay_solve_smtlib(solver, input.as_ptr()), AY_SAT);

        // First call - get and free
        let model1 = ay_get_model(solver);
        assert!(!model1.is_null());
        ay_string_free(model1);

        // Second call on same result - get and free again
        let model2 = ay_get_model(solver);
        assert!(!model2.is_null());
        ay_string_free(model2);

        ay_solver_free(solver);
    }
}

/// Test calling ay_get_error twice and freeing both.
/// Each call should return an independently allocated string.
#[test]
fn test_get_error_twice_and_free_both() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();

        // Trigger error
        let bad_input = CString::new("(invalid").expect("test should succeed");
        assert_eq!(ay_solve_smtlib(solver, bad_input.as_ptr()), AY_ERROR);

        // First call - get and free
        let error1 = ay_get_error(solver);
        assert!(!error1.is_null());
        ay_string_free(error1);

        // Second call - get and free again (error still present)
        let error2 = ay_get_error(solver);
        assert!(!error2.is_null());
        ay_string_free(error2);

        ay_solver_free(solver);
    }
}

// ========================================================================
// check-sat-assuming and unsat-core tests (#678)
// ========================================================================

#[test]
fn test_check_sat_assuming_sat() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();
        let input = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (> x 5))",
        )
        .expect("test should succeed");

        // Execute setup commands (no check-sat, so returns UNKNOWN)
        let setup_result = ay_solve_smtlib(solver, input.as_ptr());
        assert_eq!(setup_result, AY_UNKNOWN);

        // check-sat-assuming with compatible assumption: x > 5 AND x < 10 → SAT
        let assumptions = CString::new("(< x 10)").expect("test should succeed");
        let assumption_ptrs = [assumptions.as_ptr()];
        let result = ay_check_sat_assuming(solver, assumption_ptrs.as_ptr(), 1);
        assert_eq!(result, AY_SAT);

        ay_solver_free(solver);
    }
}

#[test]
fn test_check_sat_assuming_unsat() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();
        let input = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (> x 5))",
        )
        .expect("test should succeed");

        let setup_result = ay_solve_smtlib(solver, input.as_ptr());
        assert_eq!(setup_result, AY_UNKNOWN);

        // check-sat-assuming with conflicting assumption: x > 5 AND x < 3 → UNSAT
        let assumptions = CString::new("(< x 3)").expect("test should succeed");
        let assumption_ptrs = [assumptions.as_ptr()];
        let result = ay_check_sat_assuming(solver, assumption_ptrs.as_ptr(), 1);
        assert_eq!(result, AY_UNSAT);

        ay_solver_free(solver);
    }
}

#[test]
fn test_get_unsat_core_after_unsat() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();
        let input = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (> x 5))",
        )
        .expect("test should succeed");

        let setup_result = ay_solve_smtlib(solver, input.as_ptr());
        assert_eq!(setup_result, AY_UNKNOWN);

        // Two assumptions: (< x 3) is the one that conflicts with (> x 5)
        let a1 = CString::new("(< x 3)").expect("test should succeed");
        let a2 = CString::new("(> x 0)").expect("test should succeed");
        let assumption_ptrs = [a1.as_ptr(), a2.as_ptr()];
        let result = ay_check_sat_assuming(solver, assumption_ptrs.as_ptr(), 2);
        assert_eq!(result, AY_UNSAT);

        let core = ay_get_unsat_core(solver);
        assert!(
            !core.is_null(),
            "unsat core should be available after UNSAT check-sat-assuming"
        );

        let core_str = CStr::from_ptr(core).to_str().expect("test should succeed");
        // The core must contain at least `(< x 3)` since that conflicts with (> x 5)
        assert!(
            core_str.contains("(< x 3") || core_str.contains("(<= x"),
            "unsat core should contain the conflicting assumption, got: {core_str}"
        );

        ay_string_free(core);
        ay_solver_free(solver);
    }
}

/// ay_get_unsat_core returns null when no check-sat-assuming has been performed.
#[test]
fn test_get_unsat_core_null_when_no_assuming() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();
        let input = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (> x 0))
             (assert (< x 0))
             (check-sat)",
        )
        .expect("test should succeed");

        let result = ay_solve_smtlib(solver, input.as_ptr());
        assert_eq!(result, AY_UNSAT);

        // Regular check-sat was used (not check-sat-assuming), so core is unavailable
        let core = ay_get_unsat_core(solver);
        assert!(
            core.is_null(),
            "unsat core should be null when no check-sat-assuming was performed"
        );

        ay_solver_free(solver);
    }
}

#[test]
fn test_check_sat_assuming_null_pointers() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();
        let assumptions = CString::new("(< x 3)").expect("test should succeed");
        let assumption_ptrs = [assumptions.as_ptr()];

        // Null solver
        assert_eq!(
            ay_check_sat_assuming(std::ptr::null_mut(), assumption_ptrs.as_ptr(), 1),
            AY_ERROR
        );
        // Null assumptions with count > 0
        assert_eq!(ay_check_sat_assuming(solver, std::ptr::null(), 1), AY_ERROR);
        // Both null
        assert_eq!(
            ay_check_sat_assuming(std::ptr::null_mut(), std::ptr::null(), 0),
            AY_ERROR
        );
        // ay_get_unsat_core with null solver
        assert!(ay_get_unsat_core(std::ptr::null_mut()).is_null());

        ay_solver_free(solver);
    }
}

#[test]
fn test_check_sat_assuming_empty_assumptions() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();
        let input = CString::new(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (> x 5))",
        )
        .expect("test should succeed");

        let setup_result = ay_solve_smtlib(solver, input.as_ptr());
        assert_eq!(setup_result, AY_UNKNOWN);

        // Empty assumptions: check-sat-assuming () → should be SAT if assertions are satisfiable
        let result = ay_check_sat_assuming(solver, std::ptr::null(), 0);
        assert_eq!(result, AY_SAT);

        ay_solver_free(solver);
    }
}

/// Test that independent solver instances don't share state.
/// Each solver must have its own executor, error state, and model.
/// Memory corruption would show as cross-contamination between instances.
#[test]
fn test_independent_solver_instances_no_cross_contamination() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver_a = ay_solver_new();
        let solver_b = ay_solver_new();
        assert!(!solver_a.is_null());
        assert!(!solver_b.is_null());
        assert_ne!(solver_a, solver_b, "Solvers must be distinct allocations");

        // Give solver_a a SAT problem
        let sat_input =
            CString::new("(set-logic QF_LIA)(declare-const x Int)(assert (= x 42))(check-sat)")
                .expect("test should succeed");
        assert_eq!(ay_solve_smtlib(solver_a, sat_input.as_ptr()), AY_SAT);

        // Give solver_b an UNSAT problem
        let unsat_input = CString::new(
            "(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))(assert (< x 0))(check-sat)",
        )
        .expect("test should succeed");
        assert_eq!(ay_solve_smtlib(solver_b, unsat_input.as_ptr()), AY_UNSAT);

        // solver_a should still have a model (not affected by solver_b)
        let model_a = ay_get_model(solver_a);
        assert!(!model_a.is_null(), "solver_a model should be available");
        let model_str = CStr::from_ptr(model_a)
            .to_str()
            .expect("test should succeed");
        assert!(model_str.contains("42"), "solver_a model should contain 42");
        ay_string_free(model_a);

        // solver_b should have no error (UNSAT is not an error)
        let error_b = ay_get_error(solver_b);
        assert!(
            error_b.is_null(),
            "solver_b should have no error after clean UNSAT"
        );

        ay_solver_free(solver_a);
        ay_solver_free(solver_b);
    }
}

/// Test null pointer handling on all convenience solve functions.
/// Every entry point that accepts a pointer must handle null without UB.
#[test]
fn test_null_pointer_handling_all_entry_points() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        // Solver-level null handling
        assert_eq!(
            ay_solve_smtlib(std::ptr::null_mut(), std::ptr::null()),
            AY_ERROR
        );
        assert!(ay_get_model(std::ptr::null_mut()).is_null());
        assert!(ay_get_error(std::ptr::null_mut()).is_null());
        ay_set_timeout(std::ptr::null_mut(), 100);
        assert_eq!(ay_get_timeout(std::ptr::null_mut()), 0);
        assert!(ay_get_statistics(std::ptr::null_mut()).is_null());
        ay_reset(std::ptr::null_mut()); // Should be no-op

        // Convenience function null handling
        assert_eq!(ay_quick_solve(std::ptr::null()), AY_ERROR);
        assert_eq!(ay_solve_lia(std::ptr::null()), AY_ERROR);
        assert_eq!(ay_solve_sat(std::ptr::null()), AY_ERROR);
        assert_eq!(ay_solve_bv(std::ptr::null()), AY_ERROR);

        // Null smtlib with valid solver
        let solver = ay_solver_new();
        assert_eq!(ay_solve_smtlib(solver, std::ptr::null()), AY_ERROR);
        ay_solver_free(solver);
    }
}

/// Test timeout configuration stores per-solver state and survives reset.
#[test]
fn test_timeout_configuration_roundtrip() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();
        assert_eq!(ay_get_timeout(solver), 0);

        ay_set_timeout(solver, 1234);
        assert_eq!(ay_get_timeout(solver), 1234);

        ay_reset(solver);
        assert_eq!(
            ay_get_timeout(solver),
            1234,
            "reset should clear assertions but preserve solver configuration"
        );

        ay_set_timeout(solver, 0);
        assert_eq!(ay_get_timeout(solver), 0);

        ay_solver_free(solver);
    }
}

/// Test that disabling timeout leaves subsequent check-sat calls unbounded.
#[test]
fn test_set_timeout_zero_disables_timeout() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();

        let setup = CString::new("(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))")
            .expect("CString construction should succeed");
        assert_eq!(ay_solve_smtlib(solver, setup.as_ptr()), AY_UNKNOWN);

        ay_set_timeout(solver, 1);
        assert_eq!(ay_get_timeout(solver), 1);
        ay_set_timeout(solver, 0);
        assert_eq!(ay_get_timeout(solver), 0);

        assert_eq!(ay_check_sat(solver), AY_SAT);

        ay_solver_free(solver);
    }
}

/// Test statistics are returned as a heap-allocated SMT-LIB statistics string.
#[test]
fn test_get_statistics_returns_smtlib_statistics_string() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();

        let input = CString::new("(set-logic QF_UF)(declare-const p Bool)(assert p)(check-sat)")
            .expect("CString construction should succeed");
        assert_eq!(ay_solve_smtlib(solver, input.as_ptr()), AY_SAT);

        let stats = ay_get_statistics(solver);
        assert!(!stats.is_null());
        let stats_str = CStr::from_ptr(stats)
            .to_str()
            .expect("statistics should be valid UTF-8");
        assert!(stats_str.starts_with("(:"));
        assert!(stats_str.contains(":conflicts"));
        assert!(stats_str.contains(":decisions"));
        assert!(stats_str.contains(":propagations"));
        ay_string_free(stats);

        ay_solver_free(solver);
    }
}

/// Test that ay_version returns heap-allocated strings.
/// Each call must return an independently freeable pointer.
#[test]
fn test_version_returns_heap_allocated() {
    let v1 = ay_version();
    let v2 = ay_version();
    assert!(!v1.is_null());
    assert!(!v2.is_null());
    // Each call returns a separate heap allocation
    assert_ne!(
        v1, v2,
        "ay_version must return a fresh heap allocation each call"
    );
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let s1 = CStr::from_ptr(v1).to_str().expect("test should succeed");
        let s2 = CStr::from_ptr(v2).to_str().expect("test should succeed");
        assert_eq!(s1, env!("AY_BUILD_STAMP"));
        assert_eq!(s1, s2);
        // Both must be freed via ay_string_free, same as all other FFI strings
        ay_string_free(v1);
        ay_string_free(v2);
    }
}

// ========================================================================
// Incremental API tests (#643)
// ========================================================================

/// Test basic push/pop with ay_assert and ay_check_sat.
/// Push a scope, assert contradictory formulas → UNSAT, pop → SAT again.
#[test]
fn test_incremental_push_pop_basic() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();

        // Set up logic and variable
        let setup =
            CString::new("(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))").unwrap();
        ay_solve_smtlib(solver, setup.as_ptr());

        // Base level: x > 0 is SAT
        assert_eq!(ay_check_sat(solver), AY_SAT);

        // Push scope, add contradictory assertion
        ay_push(solver);
        let formula = CString::new("(< x 0)").unwrap();
        assert_eq!(ay_assert(solver, formula.as_ptr()), 0);
        assert_eq!(ay_check_sat(solver), AY_UNSAT);

        // Pop scope: contradiction removed, back to SAT
        assert_eq!(ay_pop(solver, 1), 0);
        assert_eq!(ay_check_sat(solver), AY_SAT);

        ay_solver_free(solver);
    }
}

/// Test nested push/pop with multiple assertion levels.
#[test]
fn test_incremental_multiple_push_pop() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();

        let setup = CString::new("(set-logic QF_LIA)(declare-const x Int)").unwrap();
        ay_solve_smtlib(solver, setup.as_ptr());

        // Base: assert x > 0
        let f1 = CString::new("(> x 0)").unwrap();
        assert_eq!(ay_assert(solver, f1.as_ptr()), 0);

        // Push level 1: assert x < 5
        ay_push(solver);
        let f2 = CString::new("(< x 5)").unwrap();
        assert_eq!(ay_assert(solver, f2.as_ptr()), 0);

        // Push level 2: assert x > 3
        ay_push(solver);
        let f3 = CString::new("(> x 3)").unwrap();
        assert_eq!(ay_assert(solver, f3.as_ptr()), 0);

        // x > 0 AND x < 5 AND x > 3 → SAT (x = 4)
        assert_eq!(ay_check_sat(solver), AY_SAT);

        // Pop level 2: back to x > 0 AND x < 5
        assert_eq!(ay_pop(solver, 1), 0);
        assert_eq!(ay_check_sat(solver), AY_SAT);

        // Pop level 1: back to x > 0
        assert_eq!(ay_pop(solver, 1), 0);
        assert_eq!(ay_check_sat(solver), AY_SAT);

        ay_solver_free(solver);
    }
}

/// Test ay_check_sat as standalone (no push/pop needed).
#[test]
fn test_incremental_check_sat_standalone() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();

        let setup = CString::new("(set-logic QF_LIA)(declare-const x Int)").unwrap();
        ay_solve_smtlib(solver, setup.as_ptr());

        let f = CString::new("(= x 42)").unwrap();
        assert_eq!(ay_assert(solver, f.as_ptr()), 0);

        assert_eq!(ay_check_sat(solver), AY_SAT);

        // Should be able to get model
        let model = ay_get_model(solver);
        assert!(!model.is_null());
        let model_str = CStr::from_ptr(model).to_str().unwrap();
        assert!(model_str.contains("42"));
        ay_string_free(model);

        ay_solver_free(solver);
    }
}

/// Test ay_assert with undeclared variable returns error.
#[test]
fn test_incremental_assert_error() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();

        // No set-logic or declarations — asserting should fail at execution
        let f = CString::new("(> x 0)").unwrap();
        let result = ay_assert(solver, f.as_ptr());
        assert_eq!(result, AY_ERROR);

        // Error message should be set
        let error = ay_get_error(solver);
        assert!(!error.is_null());
        ay_string_free(error);

        ay_solver_free(solver);
    }
}

/// Test ay_pop with no prior push returns error (scope underflow).
#[test]
fn test_incremental_pop_underflow() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();

        // Pop without push should error
        let result = ay_pop(solver, 1);
        assert_eq!(result, AY_ERROR);

        ay_solver_free(solver);
    }
}

/// Test ay_pop with invalid levels (0 and negative) returns error.
#[test]
fn test_incremental_pop_invalid_levels() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();

        assert_eq!(ay_pop(solver, 0), AY_ERROR);
        assert_eq!(ay_pop(solver, -1), AY_ERROR);

        ay_solver_free(solver);
    }
}

/// Test null pointer handling for all incremental API entry points.
#[test]
fn test_incremental_null_pointers() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        // ay_push with null — should not crash
        ay_push(std::ptr::null_mut());

        // ay_pop with null
        assert_eq!(ay_pop(std::ptr::null_mut(), 1), AY_ERROR);

        // ay_assert with null solver
        let f = CString::new("(> x 0)").unwrap();
        assert_eq!(ay_assert(std::ptr::null_mut(), f.as_ptr()), AY_ERROR);

        // ay_assert with null formula
        let solver = ay_solver_new();
        assert_eq!(ay_assert(solver, std::ptr::null()), AY_ERROR);
        ay_solver_free(solver);

        // ay_check_sat with null
        assert_eq!(ay_check_sat(std::ptr::null_mut()), AY_ERROR);

        // ay_check_sat_assuming with null solver
        assert_eq!(
            ay_check_sat_assuming(std::ptr::null_mut(), std::ptr::null(), 0),
            AY_ERROR
        );
    }
}

/// Test check-sat-assuming with boolean assumptions.
#[test]
fn test_check_sat_assuming_basic() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();

        let setup =
            CString::new("(set-logic QF_UF)(declare-const p Bool)(declare-const q Bool)").unwrap();
        ay_solve_smtlib(solver, setup.as_ptr());

        // Assert: at least one of p, q is true
        let f = CString::new("(or p q)").unwrap();
        assert_eq!(ay_assert(solver, f.as_ptr()), 0);

        // Assuming both false → UNSAT
        let a1 = CString::new("(not p)").unwrap();
        let a2 = CString::new("(not q)").unwrap();
        let assumptions = [a1.as_ptr(), a2.as_ptr()];
        assert_eq!(
            ay_check_sat_assuming(solver, assumptions.as_ptr(), 2),
            AY_UNSAT
        );

        // Assuming p = true → SAT
        let a3 = CString::new("p").unwrap();
        let assumptions2 = [a3.as_ptr()];
        assert_eq!(
            ay_check_sat_assuming(solver, assumptions2.as_ptr(), 1),
            AY_SAT
        );

        ay_solver_free(solver);
    }
}

/// Test check-sat-assuming with count=0 (no assumptions).
#[test]
fn test_check_sat_assuming_zero_count() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();

        let setup =
            CString::new("(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))").unwrap();
        ay_solve_smtlib(solver, setup.as_ptr());

        // Zero assumptions — should behave like check-sat
        assert_eq!(ay_check_sat_assuming(solver, std::ptr::null(), 0), AY_SAT);

        ay_solver_free(solver);
    }
}

/// Test that check-sat-assuming does not persist assumptions.
/// After a check-sat-assuming with (not p), a plain check-sat should still be SAT.
#[test]
fn test_check_sat_assuming_does_not_persist() {
    // SAFETY: Test-scope unsafe block: all handles (solvers, contexts, AST ids, etc.) are
    // allocated by `*_new`/`Z3_mk_*`/`*_solver_new` calls inside this block and freed by
    // matching `*_free`/`Z3_del_*`/drop paths. No pointer escapes the block and no concurrent
    // access can occur because this test owns the handles exclusively.
    unsafe {
        let solver = ay_solver_new();

        let setup = CString::new("(set-logic QF_UF)(declare-const p Bool)(assert p)").unwrap();
        ay_solve_smtlib(solver, setup.as_ptr());

        // p is asserted true, so assuming (not p) → UNSAT
        let a = CString::new("(not p)").unwrap();
        let assumptions = [a.as_ptr()];
        assert_eq!(
            ay_check_sat_assuming(solver, assumptions.as_ptr(), 1),
            AY_UNSAT
        );

        // But a plain check-sat should still be SAT (assumption didn't persist)
        assert_eq!(ay_check_sat(solver), AY_SAT);

        ay_solver_free(solver);
    }
}
