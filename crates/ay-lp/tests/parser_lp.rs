// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! LP parser unit tests, kept as an integration test file so
//! `crates/ay-lp/src/parser/lp.rs` stays under the 500-line module budget.

use ay_lp::exact::decimal::parse_decimal;
use ay_lp::{parse_lp, parse_lp_exact, LpError, Sense, VarKind};
use num_rational::BigRational;

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

/// A binary variable with bounds other than `[0, 1]`: CPLEX replaces the
/// bounds by `[0, 1]`, other readers intersect them (here: empty), so the
/// file is refused (it was read as a binary in `[2, +inf)`).
#[test]
fn test_parse_lp_refuses_binary_with_bounds_other_than_0_1() {
    let input = "\
Maximize
 x
Bounds
 x >= 2
Binary
 x
End
";
    assert!(matches!(
        parse_lp(input),
        Err(LpError::Parse { line: 6, .. })
    ));
    let input = "\
Maximize
 x
Bounds
 0 <= x <= 1
Binary
 x
End
";
    let p = parse_lp(input).expect("parse");
    assert_eq!(p.variables[0].kind, VarKind::Binary);
    assert_eq!((p.variables[0].lower, p.variables[0].upper), (0.0, 1.0));
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

fn q(text: &str) -> BigRational {
    parse_decimal(text).expect("number")
}

/// AY-N12: every number of an LP file is kept as the rational it denotes:
/// integers above 2^53, decimals that are not binary fractions, summed
/// repeated terms, the objective constant.
#[test]
fn test_parse_lp_exact_keeps_every_number() {
    let input = "\
Maximize
 obj: 0.1 x + 9007199254740993 y - 0.3 + 0.2 x
Subject To
 c1: 9007199254740992 x + x - 0.7 y <= 9007199254740993
 0.1 x >= -0.3
 c3: y = 2.5e-1
Bounds
 x <= 9007199254740993
 -inf <= y <= 1e30
General
 x
End
";
    let p = parse_lp_exact(input).expect("parse");
    assert_eq!(p.sense, Sense::Max);
    assert_eq!(p.name, "obj");
    assert_eq!(p.offset, -q("0.3"));
    let (x, y) = (&p.columns[0], &p.columns[1]);
    assert_eq!((x.name.as_str(), y.name.as_str()), ("x", "y"));
    assert_eq!(x.objective, q("0.3"));
    assert_eq!(y.objective, q("9007199254740993"));
    assert_eq!(x.kind, VarKind::Integer);
    assert_eq!(
        (x.lower.clone(), x.upper.clone()),
        (Some(q("0")), Some(q("9007199254740993")))
    );
    assert_eq!((y.lower.clone(), y.upper.clone()), (None, None));
    assert_eq!(p.rows.len(), 3);
    assert_eq!(
        p.rows[0].coeffs,
        vec![(0, q("9007199254740993")), (1, q("-0.7"))]
    );
    assert_eq!(
        (p.rows[0].lower.clone(), p.rows[0].upper.clone()),
        (None, Some(q("9007199254740993")))
    );
    assert_eq!(p.rows[1].name, "c2");
    assert_eq!(
        (p.rows[1].lower.clone(), p.rows[1].upper.clone()),
        (Some(q("-0.3")), None)
    );
    assert_eq!(
        (p.rows[2].lower.clone(), p.rows[2].upper.clone()),
        (Some(q("0.25")), Some(q("0.25")))
    );
    // The floating-point copy is the rounding of this reading.
    let f = parse_lp(input).expect("parse");
    assert_eq!(f.variables[1].obj_coeff, 9007199254740992.0);
}

/// AY-N12: constructs that readers in common use read differently, or that
/// a line reader could take for another construct, are refused with the
/// line of the construct.
#[test]
fn test_parse_lp_refuses_ambiguous_constructs_with_their_line() {
    let cases: [(&str, &str, usize); 17] = [
        (
            "negative upper, default lower",
            "Minimize\n x\nBounds\n x <= -1\nEnd\n",
            4,
        ),
        (
            "bound in [1e20, 1e30)",
            "Minimize\n x\nBounds\n x <= 1e25\nEnd\n",
            4,
        ),
        (
            "rhs of 1e20",
            "Minimize\n x\nSubject To\n c: x <= 1e20\nEnd\n",
            4,
        ),
        (
            "second lower bound",
            "Minimize\n x\nBounds\n x >= 1\n 0 <= x <= 3\nEnd\n",
            5,
        ),
        ("two terms without a sign", "Minimize\n x y\nEnd\n", 2),
        (
            "variable on the right",
            "Minimize\n x\nSubject To\n c: x >= 2 y\nEnd\n",
            4,
        ),
        (
            "ranged constraint",
            "Minimize\n x\nSubject To\n c: -5 <= x <= 5\nEnd\n",
            4,
        ),
        (
            "double-sided constraint",
            "Minimize\n x\nSubject To\n c: x + y >= 1 <= 4\nEnd\n",
            4,
        ),
        (
            "constant on the left",
            "Minimize\n x\nSubject To\n c: x + 2 >= 4\nEnd\n",
            4,
        ),
        ("no End", "Minimize\n x\nSubject To\n c: x >= 1\n", 4),
        ("content after End", "Minimize\n x\nEnd\n x\n", 4),
        (
            "unclosed block comment",
            "\\* a\n x <= 1 *\\\nMinimize\n x\nEnd\n",
            1,
        ),
        (
            "indicator",
            "Minimize\n x\nSubject To\n c: b = 1 -> x <= 1\nEnd\n",
            4,
        ),
        (
            "semi-continuous",
            "Minimize\n x\nSemi-continuous\n x\nEnd\n",
            3,
        ),
        (
            "General and Binary",
            "Minimize\n x\nGeneral\n x\nBinary\n x\nEnd\n",
            6,
        ),
        (
            "section out of order",
            "Minimize\n x\nBounds\n x <= 1\nSubject To\n c: x >= 0\nEnd\n",
            5,
        ),
        ("'inf' as a variable", "Minimize\n inf\nEnd\n", 2),
    ];
    for (name, text, line) in cases {
        match parse_lp_exact(text) {
            Err(LpError::Parse { line: at, .. }) => assert_eq!(at, line, "{name}"),
            other => panic!("{name}: {other:?}"),
        }
    }
}

/// Infinity spellings, `free`, the reversed and fixing forms, and both
/// orders of General and Binary.
#[test]
fn test_parse_lp_exact_bounds_and_kinds() {
    let input = "\
Minimize
 a + b + c + d + e1 + f
Bounds
 a free
 -INF <= b <= +Infinity
 c >= -1e30
 c <= 1e+30
 3.5 >= d
 -2 = e1
 f >= -4
 f <= -1
Binary
 g
General
 a
End
";
    let p = parse_lp_exact(input).expect("parse");
    let side = |j: usize| (p.columns[j].lower.clone(), p.columns[j].upper.clone());
    assert_eq!(side(0), (None, None));
    assert_eq!(side(1), (None, None));
    assert_eq!(side(2), (None, None));
    assert_eq!(side(3), (Some(q("0")), Some(q("3.5"))));
    assert_eq!(side(4), (Some(q("-2")), Some(q("-2"))));
    assert_eq!(side(5), (Some(q("-4")), Some(q("-1"))));
    assert_eq!(p.columns[6].name, "g");
    assert_eq!(p.columns[6].kind, VarKind::Binary);
    assert_eq!(side(6), (Some(q("0")), Some(q("1"))));
    assert_eq!(p.columns[0].kind, VarKind::Integer);
}
