// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn chain(mut leaf: ChcExpr, length: usize, name: &str, sort: &ChcSort) -> ChcExpr {
    for _ in 0..length {
        leaf = ChcExpr::FuncApp(name.into(), sort.clone(), vec![Arc::new(leaf)]);
    }
    leaf
}

fn problem(expression: ChcExpr) -> ChcProblem {
    let mut problem = ChcProblem::new();
    push_raw(
        &mut problem,
        HornClause::query(ClauseBody::constraint(expression)),
    );
    problem
}

fn spelling(
    expr: &ChcExpr,
    callback: &mut dyn FnMut() -> bool,
) -> Result<String, IdentityHashInterrupted> {
    payload::expression(
        expr,
        &BTreeMap::new(),
        &mut Callback(callback),
        &mut payload::DatatypeRefs::default(),
    )
}

#[test]
fn unary_chain_has_exact_existing_golden_spelling() {
    let expr = ChcExpr::FuncApp(
        "outer".into(),
        ChcSort::Int,
        vec![Arc::new(ChcExpr::FuncApp(
            "inner".into(),
            ChcSort::Int,
            vec![Arc::new(ChcExpr::Int(7))],
        ))],
    );
    assert_eq!(
        spelling(&expr, &mut || true).expect("spelling"),
        "func:\"outer\":Int(func:\"inner\":Int(int:7))"
    );
    assert_oracle(&problem(expr));
}

#[test]
fn unary_chains_with_nonunary_leaves_match_recursive_oracle() {
    let leaves = [
        ChcExpr::FuncApp("zero".into(), ChcSort::Int, vec![]),
        ChcExpr::FuncApp(
            "pair".into(),
            ChcSort::Int,
            vec![Arc::new(ChcExpr::Int(3)), Arc::new(ChcExpr::Int(1))],
        ),
        ChcExpr::Op(
            ChcOp::Add,
            vec![
                Arc::new(ChcExpr::Int(3)),
                Arc::new(chain(ChcExpr::Int(1), 3, "nested", &ChcSort::Int)),
            ],
        ),
        ChcExpr::PredicateApp(
            "predicate\"".into(),
            PredicateId::new(7),
            vec![Arc::new(ChcExpr::Bool(true))],
        ),
        ChcExpr::ConstArray(ChcSort::Int, Arc::new(ChcExpr::Bool(false))),
        ChcExpr::Var(ChcVar::new("v\n\\\"λ", ChcSort::Int)),
    ];
    for leaf in leaves {
        for length in [0, 1, 2, 8, 32] {
            let expr = chain(
                leaf.clone(),
                length,
                "f\n\\\"λ",
                &ChcSort::Array(
                    Box::new(ChcSort::Int),
                    Box::new(ChcSort::Uninterpreted("S\t\"".into())),
                ),
            );
            assert_oracle(&problem(expr));
        }
    }
}

#[test]
fn unary_datatype_chain_preserves_definitions_schema_and_both_hashes() {
    let mut sorts = vec![ChcSort::BitVec(8)];
    for level in 1..=32 {
        let child = sorts.last().expect("initial scalar").clone();
        sorts.push(ChcSort::Datatype {
            name: format!("D{level}\""),
            constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
                name: format!("mk{level}\\"),
                selectors: vec![
                    ChcDtSelector {
                        name: "a\n".into(),
                        sort: child.clone(),
                    },
                    ChcDtSelector {
                        name: "b\"".into(),
                        sort: child,
                    },
                ],
            }]),
        });
    }
    let mut expr = ChcExpr::Var(ChcVar::new("root", sorts[32].clone()));
    for level in (0..32).rev() {
        expr = ChcExpr::FuncApp("a\n".into(), sorts[level].clone(), vec![Arc::new(expr)]);
    }
    let problem = problem(expr);
    assert_oracle(&problem);
    let input = input(&problem);
    assert!(input.starts_with("ay.chc.normalized-input/v2\n"));
    assert_eq!(
        input
            .lines()
            .filter(|line| line.starts_with("constructors @"))
            .count(),
        32
    );
}

#[test]
fn unary_chain_output_and_progress_grow_linearly() {
    let measure = |length| {
        let expr = chain(ChcExpr::Int(7), length, "f", &ChcSort::Int);
        let mut polls = 0usize;
        let output = spelling(&expr, &mut || {
            polls += 1;
            true
        })
        .expect("spelling");
        (output.len(), polls)
    };
    let (a, b, c) = (measure(16), measure(32), measure(48));
    assert_eq!(b.0 - a.0, c.0 - b.0);
    assert_eq!(b.1 - a.1, c.1 - b.1);
    assert!(b.1 > 32, "every prefix and closing delimiter is polled");
}

#[test]
fn every_unary_chain_poll_refuses_without_partial_spelling_or_retry() {
    let expr = chain(
        ChcExpr::FuncApp(
            "pair".into(),
            ChcSort::Bool,
            vec![
                Arc::new(ChcExpr::Bool(true)),
                Arc::new(ChcExpr::Bool(false)),
            ],
        ),
        12,
        "f\"",
        &ChcSort::Bool,
    );
    let mut total = 0usize;
    let expected = spelling(&expr, &mut || {
        total += 1;
        true
    })
    .expect("spelling");
    for refuse_at in 1..=total {
        let mut calls = 0;
        assert_eq!(
            spelling(&expr, &mut || {
                calls += 1;
                calls != refuse_at
            }),
            Err(IdentityHashInterrupted),
            "refusal at {refuse_at}/{total}"
        );
        assert_eq!(calls, refuse_at, "refusal cannot trigger another traversal");
    }
    assert_eq!(spelling(&expr, &mut || true), Ok(expected));
}
