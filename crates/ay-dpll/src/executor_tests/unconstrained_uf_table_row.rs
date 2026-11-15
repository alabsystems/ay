// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A registered UF application that no assertion constrains is not a model
//! point, so it cannot make `(get-model)` fail.
//!
//! Measured (2026-10-01): with an array in the goal, a Real-ranged `h` whose
//! application `(h a)` is registered but unconstrained (here the assertion
//! `(= (h a) (h a))` folds to `true`; through the Z3 C API the term is merely
//! built) made `(get-model)` answer `(error "model value for function h is not
//! available: no model value for function-table entry of sort Real")`, and the
//! Z3 C API then published `sat` with an EMPTY model.

use ay_frontend::parse;

use crate::Executor;

#[test]
fn an_unconstrained_real_uf_application_does_not_fail_the_model() {
    let script = "(declare-fun A () (Array Int Int)) (declare-fun a () Int) \
                  (declare-fun h (Int) Real) \
                  (assert (= (select A a) 7)) (assert (= a 2)) (assert (= (h a) (h a))) \
                  (check-sat) (get-model) (get-value ((select A a) a))";
    let commands = parse(script).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");
    assert_eq!(outputs[0], "sat");
    assert!(!outputs[1].contains("error"), "{}", outputs[1]);
    assert!(outputs[1].contains("define-fun h"), "{}", outputs[1]);
    assert_eq!(outputs[2], "(((select A a) 7) (a 2))");
}
