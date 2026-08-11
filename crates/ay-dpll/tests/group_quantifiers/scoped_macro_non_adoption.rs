// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Scoped quantified definitions must never leak through the frontend's
//! outermost-only macro-adoption optimization.

#[test]
fn scoped_definition_pop_restores_free_uf_and_remains_sat() {
    let script = r#"
        (set-logic UFBV)
        (declare-fun f ((_ BitVec 1)) (_ BitVec 1))
        (push 1)
        (assert (forall ((x (_ BitVec 1))) (= (f x) x)))
        (pop 1)
        (assert (not (= (f #b0) #b0)))
        (check-sat)
    "#;

    assert_eq!(
        crate::common::solve_vec(script),
        ["sat"],
        "after pop, f is free and the witness f(#b0) = #b1 satisfies the query"
    );
}

#[test]
fn fixed_semantics_theory_declaration_is_not_adopted_as_a_free_macro() {
    let script = r#"
        (set-logic AUFBV)
        (declare-fun set.subset
          ((Array (_ BitVec 1) Bool) (Array (_ BitVec 1) Bool)) Bool)
        (assert
          (forall ((a (Array (_ BitVec 1) Bool))
                   (b (Array (_ BitVec 1) Bool)))
            (= (set.subset a b) false)))
        (check-sat)
    "#;

    assert_ne!(
        crate::common::solve_authored_vec(script),
        ["sat"],
        "set.subset has fixed theory semantics (in particular subset(a,a)); its declaration cannot be adopted as an arbitrary constant-false macro"
    );
}
