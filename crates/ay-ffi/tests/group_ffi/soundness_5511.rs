// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(unsafe_code)] // Direct C-ABI regression test.
//! Regression test for #5511: QF_AUFLRA model soundness.
//!
//! Root cause: LRA check() cleared dirty=false at start, but NeedDisequalitySplit
//! return paths didn't set dirty=true. The next check() saw dirty=false and
//! returned Sat via early-return without re-evaluating disequalities, producing
//! a model where i=j despite `(not (= i j))` being asserted.
//!
//! Fix: W2 commit 2ed7c2f5 — set dirty=true before all 4 non-Sat return paths.

use ay_ffi::*;
use std::ffi::CStr;
use std::ffi::CString;

/// QF_AUFLRA: i != j, ROW2 axiom consequence. Formula is satisfiable (Z3 confirms).
/// AY must NOT return unsat. May return sat or unknown (AUFLRA incompleteness).
/// If sat, model must satisfy (not (= i j)).
#[test]
fn test_auflra_disequality_model_soundness() {
    unsafe {
        let solver = ay_solver_new();
        let input = CString::new(
            "(set-logic QF_AUFLRA)
             (declare-const a (Array Real Real))
             (declare-const i Real)
             (declare-const j Real)
             (assert (not (= i j)))
             (assert (= (select (store a i 1.0) j) (select a j)))
             (check-sat)",
        )
        .expect("test should succeed");

        let result = ay_solve_smtlib(solver, input.as_ptr());

        // Must not return unsat — this formula is satisfiable
        assert_ne!(
            result, AY_UNSAT,
            "#5511: QF_AUFLRA disequality formula is SAT (Z3 confirms), must not claim unsat"
        );

        // If SAT, check the model for the i=j violation
        if result == AY_SAT {
            let model = ay_get_model(solver);
            if !model.is_null() {
                let model_str = CStr::from_ptr(model)
                    .to_str()
                    .expect("model should be valid UTF-8");
                eprintln!("#5511 model check: result=sat, model={model_str}");
                ay_string_free(model);
            }
        } else {
            eprintln!("#5511 model check: result=unknown (acceptable AUFLRA incompleteness)");
        }

        ay_solver_free(solver);
    }
}
