// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::unwrap_used)]

use super::*;
use crate::quantified::counterexample::render_oracle as oracle;
use crate::quantified::QuantifiedHornClause;
use crate::{CancellationToken, ChcOp, ChcProblem, ChcSort, ClauseBody};
use ay_core::time::Instant;
use std::sync::Arc;
use std::time::Duration;

mod metadata;
mod resources;

fn op(operator: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(operator, args.into_iter().map(Arc::new).collect())
}

fn var(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, sort))
}

fn eq(left: ChcExpr, right: ChcExpr) -> ChcExpr {
    op(ChcOp::Eq, vec![left, right])
}

fn control(token: &CancellationToken) -> SourceControl<'_> {
    SourceControl::new(Instant::now() + Duration::from_secs(30), token)
}

fn output(problem: &QuantifiedChcProblem, path: &[usize]) -> String {
    let token = CancellationToken::new();
    render(problem, path, &control(&token)).unwrap()
}

fn scoped_source() -> QuantifiedChcProblem {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![ChcSort::BitVec(2)]);
    let x = var("x", ChcSort::Bool);
    let y = var("y", ChcSort::BitVec(2));
    let f = var("f", ChcSort::Bool);
    let bound_x = var("x", ChcSort::BitVec(2));
    let i = var("i", ChcSort::BitVec(2));
    let j = var("j", ChcSort::BitVec(2));
    let shadow = UniversalPremise::new(
        ChcVar::new("x", ChcSort::BitVec(2)),
        eq(bound_x.clone(), bound_x),
    );
    let joint = UniversalPremise::with_binders(
        vec![
            ChcVar::new("i", ChcSort::BitVec(2)),
            ChcVar::new("j", ChcSort::BitVec(2)),
        ],
        op(ChcOp::Implies, vec![eq(i, j), f]),
    )
    .unwrap();
    QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(
                HornClause::fact(
                    op(
                        ChcOp::And,
                        vec![x.clone(), eq(y.clone(), ChcExpr::BitVec(1, 2))],
                    ),
                    p,
                    vec![y.clone()],
                ),
                vec![shadow, joint],
            ),
            QuantifiedHornClause::new(
                HornClause::new(
                    ClauseBody {
                        predicates: vec![(p, vec![y])],
                        constraint: Some(op(ChcOp::Not, vec![x])),
                    },
                    ClauseHead::False,
                ),
                vec![],
            ),
        ],
    )
    .unwrap()
}

#[test]
fn path_scopes_preserve_matrix_only_frees_shadowing_and_complete_joint_binders() {
    let source = scoped_source();
    let script = output(&source, &[0, 1]);
    ay_frontend::parse(&script).expect("generated declarations/assertions parse normally");
    // Declaration order is sorted within each independent clause scope:
    // fact f:Bool,x:Bool,y:BV2; query x:Bool,y:BV2. Bound BV2 x must not
    // replace the fact's Bool x; matrix-only f must not remain undeclared.
    assert_eq!(oracle::models(&script), vec![vec![1, 1, 1, 0, 1]]);
    assert!(script.contains("(forall ((x (_ BitVec 2))) (= x x))"));
    assert!(script.contains("(forall ((i (_ BitVec 2))(j (_ BitVec 2)))"));
    assert_eq!(script.matches("(forall ").count(), 2);
    assert!(!script.contains("(P "));
    assert!(!script.contains("(assert false)"));
    assert_eq!(script, output(&source, &[0, 1]));
}

#[test]
fn repeated_rule_occurrences_have_distinct_values_and_exact_argument_links() {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![ChcSort::BitVec(2)]);
    let x = var("x", ChcSort::BitVec(2));
    let clauses = vec![
        HornClause::fact(ChcExpr::Bool(true), p, vec![ChcExpr::BitVec(0, 2)]),
        HornClause::new(
            ClauseBody {
                predicates: vec![(p, vec![x.clone()])],
                constraint: None,
            },
            ClauseHead::Predicate(
                p,
                vec![op(ChcOp::BvAdd, vec![x.clone(), ChcExpr::BitVec(1, 2)])],
            ),
        ),
        HornClause::new(
            ClauseBody {
                predicates: vec![(p, vec![x.clone()])],
                constraint: Some(eq(x, ChcExpr::BitVec(2, 2))),
            },
            ClauseHead::False,
        ),
    ];
    let source = QuantifiedChcProblem::new(
        declarations,
        clauses
            .into_iter()
            .map(|clause| QuantifiedHornClause::new(clause, vec![]))
            .collect(),
    )
    .unwrap();
    let script = output(&source, &[0, 1, 1, 2]);
    assert_eq!(oracle::models(&script), vec![vec![0, 1, 2]]);
    assert_eq!(
        oracle::models(&output(&source, &[0, 1, 2])),
        [] as [std::vec::Vec<u64>; 0]
    );
}

#[test]
fn bodyless_raw_queries_keep_false_constraints_and_vacuous_nullary_paths() {
    for value in [false, true] {
        let source = QuantifiedChcProblem::new(
            ChcProblem::new(),
            vec![QuantifiedHornClause::new(
                HornClause::new(
                    ClauseBody {
                        predicates: vec![],
                        constraint: Some(ChcExpr::Bool(value)),
                    },
                    ClauseHead::False,
                ),
                vec![],
            )],
        )
        .unwrap();
        let script = output(&source, &[0]);
        assert_eq!(oracle::models(&script).len(), usize::from(value));
        assert_eq!(script.contains("(assert false)"), !value);
    }
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(
                HornClause::new(
                    ClauseBody {
                        predicates: vec![],
                        constraint: None,
                    },
                    ClauseHead::Predicate(p, vec![]),
                ),
                vec![],
            ),
            QuantifiedHornClause::new(
                HornClause::new(
                    ClauseBody {
                        predicates: vec![(p, vec![])],
                        constraint: None,
                    },
                    ClauseHead::False,
                ),
                vec![],
            ),
        ],
    )
    .unwrap();
    assert_eq!(
        oracle::models(&output(&source, &[0, 1])),
        vec![Vec::<u64>::new()]
    );
}

#[test]
fn malformed_selected_paths_cannot_skip_links_or_treat_a_fact_as_a_query() {
    let source = scoped_source();
    let token = CancellationToken::new();
    for path in [
        vec![],
        vec![0],
        vec![1],
        vec![2],
        vec![1, 0],
        vec![0, 0, 1],
        vec![0; MAX_PATH_CLAUSES + 1],
    ] {
        assert!(render(&source, &path, &control(&token)).is_err());
    }
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let q = declarations.declare_predicate("Q", vec![]);
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(HornClause::fact(ChcExpr::Bool(true), p, vec![]), vec![]),
            QuantifiedHornClause::new(HornClause::fact(ChcExpr::Bool(true), q, vec![]), vec![]),
            QuantifiedHornClause::new(
                HornClause::new(
                    ClauseBody {
                        predicates: vec![(p, vec![])],
                        constraint: None,
                    },
                    ClauseHead::False,
                ),
                vec![],
            ),
            QuantifiedHornClause::new(
                HornClause::new(
                    ClauseBody {
                        predicates: vec![(p, vec![]), (p, vec![])],
                        constraint: None,
                    },
                    ClauseHead::False,
                ),
                vec![],
            ),
        ],
    )
    .unwrap();
    for path in [[1, 2], [0, 3]] {
        assert!(render(&source, &path, &control(&token)).is_err());
    }
}

#[test]
fn raw_indexed_sort_output_and_parsed_oracle_domain_agree() {
    let x = var("x", ChcSort::BitVec(2));
    let source = QuantifiedChcProblem::new(
        ChcProblem::new(),
        vec![QuantifiedHornClause::new(
            HornClause::new(
                ClauseBody {
                    predicates: vec![],
                    constraint: Some(eq(x.clone(), x)),
                },
                ClauseHead::False,
            ),
            vec![],
        )],
    )
    .unwrap();
    let script = output(&source, &[0]);
    assert!(script.contains("(declare-const ay_qcex_0 (_ BitVec 2))"));
    assert!(!script.contains("(|_| BitVec 2)"));
    ay_frontend::parse(&script).expect("raw indexed declarations must parse");
    assert_eq!(
        oracle::models(&script),
        vec![vec![0], vec![1], vec![2], vec![3]]
    );
    assert_eq!(
        oracle::models("(declare-const flag Bool)"),
        vec![vec![0], vec![1]]
    );
}

#[test]
fn oracle_domain_rejects_wrong_indexed_heads_widths_and_arity() {
    // A quoted numeral is a Symbol, not a Numeral. The other mutations change
    // the indexed head, carrier, width, or arity; none may enumerate BV2.
    for sort in [
        "(as BitVec 2)",
        "(_ Other 2)",
        "(_ BitVec 1)",
        "(_ BitVec 3)",
        "(_ BitVec |2|)",
        "(_ BitVec 2 2)",
    ] {
        let script = format!("(declare-const x {sort})");
        assert!(
            std::panic::catch_unwind(|| oracle::models(&script)).is_err(),
            "{sort}"
        );
    }
}
