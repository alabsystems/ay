// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::check_sat_output;

/// SAT twin for the negated-exists bridge. The dual requires every `s(x,y)`;
/// an agreeing positive ground fact cannot manufacture a contradiction.
#[test]
fn diagonal_sat_twin_never_unsat() {
    let out = check_sat_output(
        r#"
        (declare-sort U 0)
        (declare-const d U)
        (declare-fun s (U U) Bool)
        (assert (s d d))
        (assert (not (exists ((x U) (y U)) (not (s x y)))))
        (check-sat)
    "#,
    );
    assert_ne!(
        out, "unsat",
        "satisfiable negated-exists twin must never be certified unsat"
    );
}
