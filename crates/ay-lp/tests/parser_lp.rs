// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! LP parser unit tests, kept as an integration test file so
//! `crates/ay-lp/src/parser/lp.rs` stays under the 500-line module budget.

use ay_lp::{parse_lp, LpError, Sense, VarKind};

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
fn test_parse_lp_binary_section_preserves_explicit_bounds() {
    let input = "\
Maximize
 x
Bounds
 x >= 2
Binary
 x
End
";
    let p = parse_lp(input).expect("parse");
    let x = p.var_index("x").expect("x");
    assert_eq!(p.variables[x].kind, VarKind::Binary);
    assert_eq!(p.variables[x].lower, 2.0);
    assert!(p.variables[x].upper.is_infinite() && p.variables[x].upper > 0.0);
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

#[test]
fn test_parse_lp_numeric_first_bounds_preserve_comparator_direction() {
    let input = "\
Minimize
 x + y + z
Bounds
 7 >= x
 9 = y
 5 >= z >= -2
End
";
    let p = parse_lp(input).expect("parse");
    let x = p.var_index("x").expect("x");
    let y = p.var_index("y").expect("y");
    let z = p.var_index("z").expect("z");
    assert_eq!(p.variables[x].lower, 0.0);
    assert_eq!(p.variables[x].upper, 7.0);
    assert_eq!(p.variables[y].lower, 9.0);
    assert_eq!(p.variables[y].upper, 9.0);
    assert_eq!(p.variables[z].lower, -2.0);
    assert_eq!(p.variables[z].upper, 5.0);
}

#[test]
fn test_parse_lp_rejects_crossed_ranged_bound_comparators() {
    let input = "\
Minimize
 x
Bounds
 0 <= x >= 1
End
";
    assert!(matches!(parse_lp(input), Err(LpError::Parse { .. })));
}

#[test]
fn test_parse_lp_rejects_non_finite_numeric_tokens() {
    let input = "\
Minimize
 1e999 x
Subject To
 x <= 1
End
";
    assert!(matches!(
        parse_lp(input),
        Err(LpError::InvalidNumber { .. })
    ));

    let input = "\
Minimize
 x
Subject To
 x <= 1e999
End
";
    assert!(matches!(
        parse_lp(input),
        Err(LpError::InvalidNumber { .. })
    ));
}

#[test]
fn test_parse_lp_rejects_finite_objective_terms_whose_sum_overflows() {
    let input = "\
Minimize
 1e308 x + 1e308 x
End
";
    assert!(matches!(parse_lp(input), Err(LpError::Parse { .. })));
}

#[test]
fn test_parse_lp_rejects_finite_objective_constants_whose_sum_overflows() {
    let input = "\
Minimize
 1e308 + 1e308
End
";
    assert!(matches!(parse_lp(input), Err(LpError::Parse { .. })));
}

#[test]
fn test_parse_lp_normalizes_repeated_constraint_terms_and_rejects_overflow() {
    let finite = "\
Minimize
 x
Subject To
 c: 1.5 x + 2.5 x <= 4
End
";
    let problem = parse_lp(finite).expect("parse");
    let x = problem.var_index("x").expect("x");
    assert_eq!(problem.constraints[0].coeffs, vec![(x, 4.0)]);

    let overflow = "\
Minimize
 x
Subject To
 c: 1e308 x + 1e308 x <= 1
End
";
    assert!(matches!(parse_lp(overflow), Err(LpError::Parse { .. })));
}

#[test]
fn test_parse_lp_still_accepts_infinite_bounds_syntax() {
    let input = "\
Minimize
 x
Bounds
 -inf <= x <= inf
End
";
    let p = parse_lp(input).expect("parse");
    let x = p.var_index("x").expect("x");
    assert!(p.variables[x].lower.is_infinite() && p.variables[x].lower < 0.0);
    assert!(p.variables[x].upper.is_infinite() && p.variables[x].upper > 0.0);
}
