// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// NRA sign consistency tests — N-ary products and implied signs.
// Included via include!() from nra.rs test module.

// Triple product sign: x>0, y>0, z>0 implies x*y*z > 0, so < 0 is UNSAT
#[test]
fn nra_unsat_triple_positive_product_negative() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (> x 0.0))
(assert (> y 0.0))
(assert (> z 0.0))
(assert (< (* x (* y z)) 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}
