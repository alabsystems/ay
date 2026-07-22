// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! LP parser unit tests, kept as an integration test file so
//! `crates/ay-lp/src/parser/lp.rs` stays under the 500-line module budget.

use ay_lp::{parse_lp, Sense, VarKind};

#[test]
fn test_parse_lp_trivial_min() {
    let input = "\
Minimize
 obj: 3 x + 2 y
Subject To
 c1: x + y >= 4
 c2: x + 3 y >= 6
Bounds
 x >= 0
 y >= 0
End
";
    let p = parse_lp(input).expect("parse");
    assert_eq!(p.sense, Sense::Min);
    assert_eq!(p.variables.len(), 2);
    assert_eq!(p.constraints.len(), 2);
    let x = p.var_index("x").expect("x");
    assert_eq!(p.variables[x].obj_coeff, 3.0);
}

#[test]
fn test_parse_lp_maximize_with_binary() {
    let input = "\
Maximize
 5 x + 4 y + 3 z
Subject To
 2 x + 3 y + z <= 5
 4 x + y + 2 z <= 11
Binary
 x y z
End
";
    let p = parse_lp(input).expect("parse");
    assert_eq!(p.sense, Sense::Max);
    for v in &p.variables {
        assert_eq!(v.kind, VarKind::Binary);
        assert_eq!(v.lower, 0.0);
        assert_eq!(v.upper, 1.0);
    }
}

#[test]
fn test_parse_lp_bound_range_and_free() {
    let input = "\
Minimize
 x + y
Subject To
 x + y >= 1
Bounds
 -5 <= x <= 5
 y free
End
";
    let p = parse_lp(input).expect("parse");
    let x = p.var_index("x").expect("x");
    let y = p.var_index("y").expect("y");
    assert_eq!(p.variables[x].lower, -5.0);
    assert_eq!(p.variables[x].upper, 5.0);
    assert!(p.variables[y].lower.is_infinite() && p.variables[y].lower < 0.0);
    assert!(p.variables[y].upper.is_infinite() && p.variables[y].upper > 0.0);
}
