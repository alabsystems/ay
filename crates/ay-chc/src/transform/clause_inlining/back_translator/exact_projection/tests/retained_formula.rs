// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! An already closed, fully typed formula needs no disjunctive projection.

use super::*;

pub(super) fn disjunctions(count: usize) -> (ChcExpr, Vec<ChcVar>) {
    let keep: Vec<_> = (0..count * 2)
        .map(|i| var(&format!("kept_{i}"), 2))
        .collect();
    let (pairs, remainder) = keep.as_chunks::<2>();
    assert_eq!(remainder, &[] as &[ChcVar]);
    let clauses = pairs
        .iter()
        .map(|pair| {
            op(
                ChcOp::Or,
                vec![
                    eq(expr(&pair[0]), ChcExpr::BitVec(0, 2)),
                    eq(expr(&pair[1]), ChcExpr::BitVec(1, 2)),
                ],
            )
        })
        .collect();
    (op(ChcOp::And, clauses), keep)
}

#[test]
fn sixteen_independent_retained_disjunctions_need_no_branch_credit() {
    let (formula, keep) = disjunctions(16);
    for branches in [0, 1, 64] {
        let mut scope = Scope::new(
            Limits {
                branches,
                ..Limits::default()
            },
            &|| true,
        );
        let Projection::Closed(projected) = run(&formula, &keep, &mut scope) else {
            panic!("a fully retained formula needs no branch enumeration")
        };
        assert_eq!(projected, formula, "preserve every original disjunction");
        assert_eq!(scope.remaining.branches, branches);
    }
}

#[test]
fn closed_scalar_and_array_guards_match_every_small_original_assignment() {
    let a = var("a", 2);
    let b = var("b", 2);
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let memory = ChcVar::new(
        "memory",
        ChcSort::Array(Box::new(ChcSort::BitVec(1)), Box::new(ChcSort::Bool)),
    );
    let mut atoms: Vec<_> = (0..16)
        .map(|i| {
            op(
                ChcOp::Or,
                vec![
                    eq(expr(&a), ChcExpr::BitVec(i % 3, 2)),
                    eq(expr(&b), ChcExpr::BitVec(if i % 3 == 2 { 2 } else { 1 }, 2)),
                ],
            )
        })
        .collect();
    atoms.push(expr(&flag));
    atoms.push(eq(
        expr(&memory),
        ChcExpr::ConstArray(ChcSort::BitVec(1), Arc::new(ChcExpr::Bool(true))),
    ));
    let formula = op(ChcOp::And, atoms);
    let projected = closed(&formula, &[a, b, flag, memory]);
    let mut true_count = 0;
    for a in 0..4 {
        for b in 0..4 {
            for flag in 0..2 {
                for memory in 0..4 {
                    let values = [("a", a), ("b", b), ("flag", flag), ("memory", memory)];
                    let expected = oracle::truth(&formula, &values);
                    true_count += usize::from(expected);
                    assert_eq!(oracle::truth(&projected, &values), expected);
                }
            }
        }
    }
    assert!(true_count > 0 && true_count < 128);
}

#[test]
fn fully_retained_does_not_bypass_typing_even_inside_a_dead_arm() {
    let a = var("a", 2);
    for bad in [
        op(ChcOp::BvAdd, vec![expr(&a)]),
        op(ChcOp::BvAdd, vec![expr(&a), ChcExpr::BitVec(1, 1)]),
        op(ChcOp::BvAdd, vec![expr(&a), ChcExpr::BitVec(4, 2)]),
        expr(&var("a", 1)),
    ] {
        declined(
            &op(ChcOp::And, vec![ChcExpr::Bool(false), eq(expr(&a), bad)]),
            std::slice::from_ref(&a),
        );
    }
}

#[test]
fn retained_disjunctions_do_not_hide_an_uneliminated_local() {
    let (formula, keep) = disjunctions(16);
    let local = var("local", 2);
    let condition = op(ChcOp::BvULt, vec![expr(&local), expr(&keep[0])]);
    declined(&condition, &keep);
    let formula = op(ChcOp::And, vec![formula, condition]);
    let mut scope = Scope::new(
        Limits {
            branches: 0,
            ..Limits::default()
        },
        &|| true,
    );
    assert!(matches!(
        run(&formula, &keep, &mut scope),
        Projection::Stopped
    ));
    assert_eq!(scope.poll(), Err(Failure::Stopped));
}

#[test]
fn closed_fast_path_still_observes_every_stop_and_numeric_boundary() {
    let a = var("a", 2);
    let formula = op(
        ChcOp::Or,
        vec![
            eq(expr(&a), ChcExpr::BitVec(0, 2)),
            eq(expr(&a), ChcExpr::BitVec(2, 2)),
        ],
    );
    resources::assert_poll_boundaries(&formula, std::slice::from_ref(&a));
    resources::assert_numeric_boundaries(&formula, std::slice::from_ref(&a));
}

pub(super) fn realloc_fact_shape() -> (ChcExpr, Vec<ChcVar>) {
    // Alpha-renamed constraint shape from the exact Oct14 query's first fact
    // (SHA256 0930146d...6412d7, line500): six nonoverlapping stack regions,
    // their original byte lengths/alignment bounds, one extra scalar stack
    // base, and the all-true BV32->Bool allocation table. The full stored query
    // is qualified separately; this self-contained test needs no sibling repo.
    let lengths = [16u128, 16, 16, 32, 16, 24];
    let mut keep: Vec<_> = (0..6).map(|i| var(&format!("stack_{i}"), 64)).collect();
    let mut atoms = Vec::new();
    for (base, length) in keep.iter().zip(lengths) {
        atoms.push(op(ChcOp::Not, vec![eq(expr(base), ChcExpr::BitVec(0, 64))]));
        atoms.push(eq(
            op(ChcOp::BvAnd, vec![expr(base), ChcExpr::BitVec(7, 64)]),
            ChcExpr::BitVec(0, 64),
        ));
        atoms.push(op(
            ChcOp::BvULe,
            vec![
                expr(base),
                ChcExpr::BitVec(u128::from(u64::MAX) - length, 64),
            ],
        ));
    }
    for i in 0..6 {
        for j in i + 1..6 {
            let before = |i, j| {
                op(
                    ChcOp::BvULe,
                    vec![
                        op(
                            ChcOp::BvAdd,
                            vec![expr(&keep[i]), ChcExpr::BitVec(lengths[i], 64)],
                        ),
                        expr(&keep[j]),
                    ],
                )
            };
            atoms.push(op(ChcOp::Or, vec![before(i, j), before(j, i)]));
        }
    }
    let extra = var("stack_36", 64);
    atoms.push(op(
        ChcOp::Not,
        vec![eq(expr(&extra), ChcExpr::BitVec(0, 64))],
    ));
    atoms.push(op(
        ChcOp::BvULe,
        vec![expr(&extra), ChcExpr::BitVec(u128::from(u64::MAX), 64)],
    ));
    keep.push(extra);
    let memory = ChcVar::new(
        "obj_valid",
        ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::Bool)),
    );
    atoms.push(eq(
        expr(&memory),
        ChcExpr::ConstArray(ChcSort::BitVec(32), Arc::new(ChcExpr::Bool(true))),
    ));
    keep.push(memory);
    keep.extend((0..35).map(|i| var(&format!("unused_{i}"), 32)));
    (op(ChcOp::And, atoms), keep)
}

#[test]
fn source_shaped_realloc_fact_survives_the_actual_inliner_reconstruction() {
    let (formula, keep) = realloc_fact_shape();
    assert_eq!(keep.len(), 43);
    assert_eq!(shift::operation_count(&formula, ChcOp::Or), 15);
    assert!(formula.vars().iter().all(|var| keep.contains(var)));
    let mut problem = crate::ChcProblem::new();
    let id = problem.declare_predicate("bb0", keep.iter().map(|v| v.sort.clone()).collect());
    let clause = crate::HornClause::new(
        crate::ClauseBody::new(Vec::new(), Some(formula)),
        crate::ClauseHead::Predicate(id, keep.iter().map(expr).collect()),
    );
    let reconstructed = super::super::super::InliningBackTranslator::synthesize_interpretation(
        &clause,
        &crate::InvariantModel::new(),
    )
    .expect("already closed original-style fact must not need 32768 branches");
    assert_eq!(reconstructed.vars, keep);
    assert_eq!(
        shift::operation_count(&reconstructed.formula, ChcOp::Or),
        15
    );
    assert!(reconstructed
        .formula
        .vars()
        .iter()
        .all(|v| keep.contains(v)));
}
