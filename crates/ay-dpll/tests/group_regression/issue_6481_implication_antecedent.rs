// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression test for issue #6481: implication antecedents containing a
//! ground atom alongside a quantified atom must not flip polarity during
//! Skolemization.

use ntest::timeout;

#[test]
#[timeout(10000)]
fn implication_antecedent_with_ground_and_forall_stays_sat_issue_6481() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const n Int)
        (declare-const ext_eq Bool)
        (assert ext_eq)
        (assert
          (=> (and (= n n)
                   (forall ((i Int))
                     (= (select a i) (select a i))))
              ext_eq))
        (check-sat)
    "#;

    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["sat"],
        "mixed ground+forall implication antecedent should stay SAT"
    );
}
