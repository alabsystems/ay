// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Alpha-renamed source shapes: two halved nondeterministic inputs, copied
//! sum/overflow fields and a merge with a shared Boolean head constraint.

use super::*;

#[derive(Clone, Copy)]
enum Path {
    Equality,
    MergedTrue,
}

fn formals(width: u32) -> Vec<ChcVar> {
    [
        "a", "c", "b", "s", "o", "v", "q", "u7", "u8", "u9", "u10", "u11",
    ]
    .into_iter()
    .enumerate()
    .map(|(i, name)| {
        ChcVar::new(
            name,
            if [4, 6, 8, 10, 11].contains(&i) {
                ChcSort::Bool
            } else {
                ChcSort::BitVec(width)
            },
        )
    })
    .collect()
}

fn common(width: u32, x_name: &str, y_name: &str) -> Vec<ChcExpr> {
    let vars = formals(width);
    let [a, c, b, s, o, v, ..] = vars.as_slice() else {
        unreachable!()
    };
    let x = var(x_name, width);
    let y = var(y_name, width);
    let sum = op(ChcOp::BvAdd, vec![quotient(&y, 2), expr(a)]);
    let overflow = op(ChcOp::BvULt, vec![sum.clone(), quotient(&y, 2)]);
    vec![
        eq(expr(a), quotient(&x, 2)),
        eq(expr(c), expr(s)),
        eq(expr(b), quotient(&y, 2)),
        eq(expr(s), sum),
        eq(expr(o), overflow.clone()),
        eq(expr(v), expr(a)),
        op(ChcOp::Not, vec![overflow]),
    ]
}

fn source(width: u32, path: Path) -> ChcExpr {
    let vars = formals(width);
    let gt = op(ChcOp::BvUGt, vec![expr(&vars[3]), expr(&vars[0])]);
    let a_zero = eq(expr(&vars[0]), ChcExpr::BitVec(0, width));
    match path {
        Path::Equality => {
            let mut atoms = common(width, "x", "y");
            atoms.extend([
                eq(
                    expr(&vars[6]),
                    eq(expr(&vars[2]), ChcExpr::BitVec(0, width)),
                ),
                op(ChcOp::Not, vec![gt]),
                op(ChcOp::Not, vec![a_zero]),
            ]);
            op(ChcOp::And, atoms)
        }
        Path::MergedTrue => {
            let mut greater = common(width, "x6", "y6");
            greater.push(gt.clone());
            let mut zero = common(width, "x8", "y8");
            zero.extend([op(ChcOp::Not, vec![gt]), a_zero]);
            op(
                ChcOp::And,
                vec![
                    expr(&vars[6]),
                    op(
                        ChcOp::Or,
                        vec![op(ChcOp::And, greater), op(ChcOp::And, zero)],
                    ),
                ],
            )
        }
    }
}

fn source_exists(width: u32, state: [u128; 7], path: Path) -> bool {
    let [a, c, b, s, o, v, q] = state;
    let size = 1u128 << width;
    (0..size).any(|x| {
        (0..size).any(|y| {
            let sum = (x / 2 + y / 2) % size;
            let overflow = sum < y / 2;
            let common = a == x / 2
                && b == y / 2
                && s == sum
                && c == sum
                && o == u128::from(overflow)
                && v == a
                && !overflow;
            common
                && match path {
                    Path::Equality => s <= a && a != 0 && (q != 0) == (b == 0),
                    Path::MergedTrue => q != 0 && (s > a || a == 0),
                }
        })
    })
}

#[test]
fn both_source_definitions_match_exhaustive_small_width_reachability() {
    assert_eq!(source(32, Path::Equality).node_count(1000), 58);
    let width = 2;
    for path in [Path::Equality, Path::MergedTrue] {
        let projected = closed(&source(width, path), &formals(width));
        assert_source_projection(&projected, width, path);
    }
}

#[test]
fn normalized_source_definitions_project_the_actual_shift_representation() {
    // ChcProblem::add_clause simplifies parsed rule constraints before any
    // inliner records them. Testing only the raw division AST misses that
    // production representation despite preserving the same 58-node shape.
    let first = source(32, Path::Equality).simplify_constants();
    assert_eq!(first.node_count(1000), 58);
    for path in [Path::Equality, Path::MergedTrue] {
        for width in [2, 32] {
            let normalized = source(width, path).simplify_constants();
            assert_eq!(super::shift::operation_count(&normalized, ChcOp::BvUDiv), 0);
            assert!(super::shift::operation_count(&normalized, ChcOp::BvLShr) >= 2);
            let projected = closed(&normalized, &formals(width));
            if width == 2 {
                assert_source_projection(&projected, width, path);
            }
        }
    }
}

fn assert_source_projection(projected: &ChcExpr, width: u32, path: Path) {
    for packed in 0..(1u128 << (width * 5)) {
        let mut bits = packed;
        let mut bv = [0u128; 5];
        for value in &mut bv {
            *value = bits & ((1u128 << width) - 1);
            bits >>= width;
        }
        for o in 0..2 {
            for q in 0..2 {
                let [a, c, b, s, v] = bv;
                let expected = source_exists(width, [a, c, b, s, o, v, q], path);
                let actual = oracle::truth(
                    projected,
                    &[
                        ("a", a),
                        ("c", c),
                        ("b", b),
                        ("s", s),
                        ("o", o),
                        ("v", v),
                        ("q", q),
                    ],
                );
                assert_eq!(
                    actual, expected,
                    "a={a} c={c} b={b} s={s} o={o} v={v} q={q}"
                );
            }
        }
    }
}

#[test]
fn branch_local_aliases_stay_inside_their_alternative() {
    let a = var("a", 4);
    let shared = var("shared", 4);
    let mut alternatives = Vec::new();
    for value in [3, 11] {
        let mut atoms = vec![eq(expr(&a), expr(&shared))];
        let aliases: Vec<_> = (0..18).map(|i| var(&format!("local_{i}"), 4)).collect();
        atoms.push(eq(expr(&shared), expr(&aliases[0])));
        for pair in aliases.windows(2) {
            atoms.push(eq(expr(&pair[0]), expr(&pair[1])));
        }
        atoms.push(eq(expr(aliases.last().unwrap()), ChcExpr::BitVec(value, 4)));
        alternatives.push(op(ChcOp::And, atoms));
    }
    // Deliberately reuse all local names across alternatives. Independent
    // branch substitution must not constrain one by the other's assignments.
    let projected = closed(&op(ChcOp::Or, alternatives), &[a]);
    for value in 0..16 {
        assert_eq!(
            oracle::truth(&projected, &[("a", value)]),
            value == 3 || value == 11
        );
    }
}
