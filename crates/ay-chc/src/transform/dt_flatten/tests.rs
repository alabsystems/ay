// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tests for DT flattening transform (#8288, per-variant columns item 4 Stage 4).

use std::sync::Arc;

use super::super::{SolidityArrayDtProjectionTransformer, TransformationPipeline};
use super::*;
use crate::{ChcDtConstructor, ChcDtSelector, ChcSort};

/// Helper: create a single-constructor (struct-like) DT sort.
fn pair_sort() -> ChcSort {
    ChcSort::Datatype {
        name: "Pair".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mk".to_string(),
            selectors: vec![
                ChcDtSelector {
                    name: "fst".to_string(),
                    sort: ChcSort::Int,
                },
                ChcDtSelector {
                    name: "snd".to_string(),
                    sort: ChcSort::Int,
                },
            ],
        }]),
    }
}

/// Helper: create a multi-constructor (enum-like) DT sort.
fn option_int_sort() -> ChcSort {
    ChcSort::Datatype {
        name: "OptionInt".to_string(),
        constructors: Arc::new(vec![
            ChcDtConstructor {
                name: "None".to_string(),
                selectors: vec![],
            },
            ChcDtConstructor {
                name: "Some".to_string(),
                selectors: vec![ChcDtSelector {
                    name: "val".to_string(),
                    sort: ChcSort::Int,
                }],
            },
        ]),
    }
}

fn option_pair_sort() -> ChcSort {
    ChcSort::Datatype {
        name: "OptionPair".to_string(),
        constructors: Arc::new(vec![
            ChcDtConstructor {
                name: "NonePair".to_string(),
                selectors: vec![],
            },
            ChcDtConstructor {
                name: "SomePair".to_string(),
                selectors: vec![ChcDtSelector {
                    name: "pair".to_string(),
                    sort: pair_sort(),
                }],
            },
        ]),
    }
}

fn result8_sort() -> ChcSort {
    ChcSort::Datatype {
        name: "Result8".to_string(),
        constructors: Arc::new(vec![
            ChcDtConstructor {
                name: "Ok".to_string(),
                selectors: vec![ChcDtSelector {
                    name: "ok_val".to_string(),
                    sort: ChcSort::BitVec(8),
                }],
            },
            ChcDtConstructor {
                name: "Err".to_string(),
                selectors: vec![ChcDtSelector {
                    name: "err_val".to_string(),
                    sort: ChcSort::BitVec(8),
                }],
            },
        ]),
    }
}

fn state_with_result8_sort() -> ChcSort {
    ChcSort::Datatype {
        name: "StateResult8".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mkStateResult8".to_string(),
            selectors: vec![
                ChcDtSelector {
                    name: "tag".to_string(),
                    sort: result8_sort(),
                },
                ChcDtSelector {
                    name: "counter".to_string(),
                    sort: ChcSort::BitVec(8),
                },
            ],
        }]),
    }
}

fn recursive_list_sort() -> ChcSort {
    let backedge = ChcSort::Uninterpreted("listOfInt".to_string());
    let shallow = ChcSort::Datatype {
        name: "listOfInt".to_string(),
        constructors: Arc::new(vec![
            ChcDtConstructor {
                name: "conslistOfInt".to_string(),
                selectors: vec![
                    ChcDtSelector {
                        name: "headlistOfInt".to_string(),
                        sort: ChcSort::Int,
                    },
                    ChcDtSelector {
                        name: "taillistOfInt".to_string(),
                        sort: backedge,
                    },
                ],
            },
            ChcDtConstructor {
                name: "nillistOfInt".to_string(),
                selectors: vec![],
            },
        ]),
    };
    ChcSort::Datatype {
        name: "listOfInt".to_string(),
        constructors: Arc::new(vec![
            ChcDtConstructor {
                name: "conslistOfInt".to_string(),
                selectors: vec![
                    ChcDtSelector {
                        name: "headlistOfInt".to_string(),
                        sort: ChcSort::Int,
                    },
                    ChcDtSelector {
                        name: "taillistOfInt".to_string(),
                        sort: shallow,
                    },
                ],
            },
            ChcDtConstructor {
                name: "nillistOfInt".to_string(),
                selectors: vec![],
            },
        ]),
    }
}

fn contains_func_name(expr: &ChcExpr, needle: &str) -> bool {
    match expr {
        ChcExpr::FuncApp(name, _, args) => {
            name == needle || args.iter().any(|arg| contains_func_name(arg, needle))
        }
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) => {
            args.iter().any(|arg| contains_func_name(arg, needle))
        }
        ChcExpr::ConstArray(_, value_expr) => contains_func_name(value_expr, needle),
        _ => false,
    }
}

fn contains_var_bv_eq(expr: &ChcExpr, var_name: &str, value: u128, width: u32) -> bool {
    match expr {
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            matches!(
                (args[0].as_ref(), args[1].as_ref()),
                (ChcExpr::Var(v), ChcExpr::BitVec(n, w))
                    if v.name == var_name && *n == value && *w == width
            ) || matches!(
                (args[1].as_ref(), args[0].as_ref()),
                (ChcExpr::Var(v), ChcExpr::BitVec(n, w))
                    if v.name == var_name && *n == value && *w == width
            )
        }
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            args.iter()
                .any(|arg| contains_var_bv_eq(arg.as_ref(), var_name, value, width))
        }
        ChcExpr::ConstArray(_, value_expr) => {
            contains_var_bv_eq(value_expr.as_ref(), var_name, value, width)
        }
        _ => false,
    }
}

#[test]
fn test_flatten_sort_single_ctor() {
    let sort = pair_sort();
    let flat = flatten_sort(&sort, DiscKind::Int);
    assert_eq!(flat, vec![ChcSort::Int, ChcSort::Int]);
}

#[test]
fn test_flatten_sort_multi_ctor() {
    let sort = option_int_sort();
    let flat = flatten_sort(&sort, DiscKind::Int);
    // disc + Some's val column (None owns no columns)
    assert_eq!(flat, vec![ChcSort::Int, ChcSort::Int]);
}

#[test]
fn test_flatten_sort_multi_ctor_bv_disc() {
    let sort = option_int_sort();
    let flat = flatten_sort(&sort, DiscKind::Bv8);
    assert_eq!(flat, vec![ChcSort::BitVec(8), ChcSort::Int]);
}

/// Heterogeneous variants each own their columns (per-variant layout).
#[test]
fn test_flatten_sort_heterogeneous_multi_ctor() {
    let sort = either_int_bool_sort();
    let flat = flatten_sort(&sort, DiscKind::Int);
    assert_eq!(flat, vec![ChcSort::Int, ChcSort::Int, ChcSort::Bool]);
}

#[test]
fn test_flatten_sort_recursive_list_default_preserves_opaque_backedge() {
    let sort = recursive_list_sort();
    let flat = flatten_sort(&sort, DiscKind::Int);
    assert_eq!(
        flat,
        vec![
            ChcSort::Int,
            ChcSort::Int,
            ChcSort::Int,
            ChcSort::Int,
            ChcSort::Uninterpreted("listOfInt".to_string())
        ],
        "default recursive list flattening should preserve legacy opaque backedge behavior"
    );
}

#[test]
fn test_flatten_sort_recursive_list_gated_scalar_prefix() {
    let sort = recursive_list_sort();
    let flat = flatten_sort_with_depth(&sort, RECURSIVE_DT_PREFIX_EXPERIMENT_DEPTH, DiscKind::Int);
    assert_eq!(
        flat,
        vec![ChcSort::Int, ChcSort::Int, ChcSort::Int, ChcSort::Int],
        "gated recursive prefix mode should expose two list spine levels and drop the opaque backedge"
    );
}

#[test]
fn test_dt_flattener_recursive_list_default_keeps_legacy_backedge() {
    let sort = recursive_list_sort();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![sort.clone()]);

    let nil = ChcExpr::FuncApp("nillistOfInt".to_string(), sort.clone(), vec![]);
    let cons = ChcExpr::FuncApp(
        "conslistOfInt".to_string(),
        sort,
        vec![Arc::new(ChcExpr::Int(7)), Arc::new(nil)],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(pred, vec![cons]),
    ));

    let result = Box::new(DtFlattener::new()).transform(problem);
    assert_eq!(result.problem.predicates()[0].arg_sorts.len(), 5);
    assert!(
        matches!(
            result.problem.predicates()[0].arg_sorts.last(),
            Some(ChcSort::Uninterpreted(name)) if name == "listOfInt"
        ),
        "default DtFlattener must keep the legacy opaque recursive backedge"
    );
    let ClauseHead::Predicate(_, args) = &result.problem.clauses()[0].head else {
        panic!("expected predicate head");
    };
    // cons(7, nil): disc=0 (cons), head=7, tail = nil flattened
    // (disc=1, default head, default opaque backedge).
    assert_eq!(
        args,
        &vec![
            ChcExpr::Int(0),
            ChcExpr::Int(7),
            ChcExpr::Int(1),
            ChcExpr::Int(0),
            ChcExpr::Int(0),
        ]
    );
}

fn contains_int_cmp(expr: &ChcExpr, op: ChcOp, var_fragment: &str, value: i128) -> bool {
    match expr {
        ChcExpr::Op(found_op, args) if *found_op == op && args.len() == 2 => {
            matches!(
                (args[0].as_ref(), args[1].as_ref()),
                (ChcExpr::Var(v), ChcExpr::Int(n))
                    if v.name.contains(var_fragment) && *n == value
            )
        }
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            args.iter()
                .any(|arg| contains_int_cmp(arg.as_ref(), op, var_fragment, value))
        }
        ChcExpr::ConstArray(_, value_expr) => {
            contains_int_cmp(value_expr.as_ref(), op, var_fragment, value)
        }
        _ => false,
    }
}

#[test]
fn test_dt_flattener_recursive_list_adds_discriminator_domain_constraints() {
    let sort = recursive_list_sort();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![sort.clone()]);
    let x = ChcVar::new("x", sort);

    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(pred, vec![ChcExpr::var(x)])], None),
        ClauseHead::False,
    ));

    let result = Box::new(DtFlattener::new()).transform(problem);
    let constraint = result.problem.clauses()[0]
        .body
        .constraint
        .as_ref()
        .expect("flattened recursive DT predicate should carry domain constraints");

    assert!(
        contains_int_cmp(constraint, ChcOp::Ge, "x_disc", 0)
            && contains_int_cmp(constraint, ChcOp::Le, "x_disc", 1),
        "top-level recursive list discriminator should be constrained to real constructors: {constraint:?}"
    );
    assert!(
        contains_int_cmp(constraint, ChcOp::Ge, "x_v0_taillistOfInt_disc", 0)
            && contains_int_cmp(constraint, ChcOp::Le, "x_v0_taillistOfInt_disc", 1),
        "active recursive tail discriminator should be guarded and constrained: {constraint:?}"
    );
}

#[test]
fn test_flatten_sort_scalar() {
    assert_eq!(
        flatten_sort(&ChcSort::Int, DiscKind::Int),
        vec![ChcSort::Int]
    );
    assert_eq!(
        flatten_sort(&ChcSort::Bool, DiscKind::Int),
        vec![ChcSort::Bool]
    );
}

#[test]
fn test_expand_dt_var_single_ctor() {
    let sort = pair_sort();
    let fields = expand_dt_var("p", &sort, DiscKind::Int);
    assert_eq!(fields.len(), 2);
    assert_eq!(fields[0].0, "p_fst");
    assert_eq!(fields[0].1, ChcSort::Int);
    assert_eq!(fields[1].0, "p_snd");
    assert_eq!(fields[1].1, ChcSort::Int);
}

#[test]
fn test_expand_dt_var_multi_ctor() {
    let sort = option_int_sort();
    let fields = expand_dt_var("x", &sort, DiscKind::Int);
    assert_eq!(fields.len(), 2); // disc + Some's val column
    assert_eq!(fields[0].0, "x_disc");
    assert_eq!(fields[0].1, ChcSort::Int);
    assert_eq!(fields[1].0, "x_v1_val");
    assert_eq!(fields[1].1, ChcSort::Int);
}

#[test]
fn test_expand_dt_var_heterogeneous_multi_ctor() {
    let sort = either_int_bool_sort();
    let fields = expand_dt_var("x", &sort, DiscKind::Int);
    assert_eq!(fields.len(), 3);
    assert_eq!(fields[0].0, "x_disc");
    assert_eq!(fields[0].1, ChcSort::Int);
    assert_eq!(fields[1].0, "x_v0_left");
    assert_eq!(fields[1].1, ChcSort::Int);
    assert_eq!(fields[2].0, "x_v1_right");
    assert_eq!(fields[2].1, ChcSort::Bool);
}

#[test]
fn test_dt_flattener_noop_for_non_dt() {
    let mut problem = ChcProblem::new();
    problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Bool]);
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(
            PredicateId::new(0),
            vec![ChcExpr::Int(0), ChcExpr::Bool(true)],
        ),
    ));

    let transformer = Box::new(DtFlattener::new());
    let result = transformer.transform(problem);

    // Should be unchanged
    assert_eq!(result.problem.predicates().len(), 1);
    assert_eq!(result.problem.predicates()[0].arity(), 2);
}

#[test]
fn test_dt_flattener_single_ctor_predicate() {
    let dt_sort = pair_sort();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![dt_sort.clone()]);

    // Init clause: (= (fst p) 0) AND (= (snd p) 0) => Inv(p)
    let p = ChcVar::new("p", dt_sort.clone());
    let fst_p = ChcExpr::FuncApp(
        "fst".to_string(),
        ChcSort::Int,
        vec![Arc::new(ChcExpr::Var(p.clone()))],
    );
    let snd_p = ChcExpr::FuncApp(
        "snd".to_string(),
        ChcSort::Int,
        vec![Arc::new(ChcExpr::Var(p.clone()))],
    );
    let constraint = ChcExpr::Op(
        ChcOp::And,
        vec![
            Arc::new(ChcExpr::Op(
                ChcOp::Eq,
                vec![Arc::new(fst_p), Arc::new(ChcExpr::Int(0))],
            )),
            Arc::new(ChcExpr::Op(
                ChcOp::Eq,
                vec![Arc::new(snd_p), Arc::new(ChcExpr::Int(0))],
            )),
        ],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(constraint),
        ClauseHead::Predicate(pred, vec![ChcExpr::Var(p.clone())]),
    ));

    let transformer = Box::new(DtFlattener::new());
    let result = transformer.transform(problem);

    // Predicate should now have 2 Int args instead of 1 DT arg
    assert_eq!(result.problem.predicates().len(), 1);
    assert_eq!(result.problem.predicates()[0].arity(), 2);
    assert_eq!(result.problem.predicates()[0].arg_sorts[0], ChcSort::Int);
    assert_eq!(result.problem.predicates()[0].arg_sorts[1], ChcSort::Int);
}

#[test]
fn test_dt_flattener_constructor_in_head() {
    let dt_sort = pair_sort();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![dt_sort.clone()]);

    // Init clause: true => Inv(mk(42, 7))
    let ctor_app = ChcExpr::FuncApp(
        "mk".to_string(),
        dt_sort.clone(),
        vec![Arc::new(ChcExpr::Int(42)), Arc::new(ChcExpr::Int(7))],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(pred, vec![ctor_app]),
    ));

    let transformer = Box::new(DtFlattener::new());
    let result = transformer.transform(problem);

    // Head should have the flattened fields: [42, 7]
    let clause = &result.problem.clauses()[0];
    if let ClauseHead::Predicate(_, args) = &clause.head {
        assert_eq!(args.len(), 2);
        assert_eq!(args[0], ChcExpr::Int(42));
        assert_eq!(args[1], ChcExpr::Int(7));
    } else {
        panic!("expected predicate head");
    }
}

#[test]
fn test_dt_equality_flattened() {
    let dt_sort = pair_sort();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![dt_sort.clone()]);

    // Clause: (= p (mk 42 7)) => Inv(p)
    let p = ChcVar::new("p", dt_sort.clone());
    let ctor_app = ChcExpr::FuncApp(
        "mk".to_string(),
        dt_sort.clone(),
        vec![Arc::new(ChcExpr::Int(42)), Arc::new(ChcExpr::Int(7))],
    );
    let eq_expr = ChcExpr::Op(
        ChcOp::Eq,
        vec![Arc::new(ChcExpr::Var(p.clone())), Arc::new(ctor_app)],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(eq_expr),
        ClauseHead::Predicate(pred, vec![ChcExpr::Var(p)]),
    ));

    let transformer = Box::new(DtFlattener::new());
    let result = transformer.transform(problem);

    // The constraint should be a conjunction of field equalities
    let clause = &result.problem.clauses()[0];
    assert!(clause.body.constraint.is_some());
    let c = clause.body.constraint.as_ref().unwrap();
    // Should be: (and (= p_fst 42) (= p_snd 7))
    assert!(
        matches!(c, ChcExpr::Op(ChcOp::And, args) if args.len() == 2),
        "Expected And of 2 equalities, got: {c:?}"
    );
}

#[test]
fn test_dt_valued_selector_constructor_equality_flattened() {
    let state_sort = state_with_result8_sort();
    let result_sort = result8_sort();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![state_sort.clone()]);

    let s = ChcVar::new("s", state_sort);
    let tag_s = ChcExpr::FuncApp(
        "tag".to_string(),
        result_sort.clone(),
        vec![Arc::new(ChcExpr::var(s.clone()))],
    );
    let ok = ChcExpr::FuncApp(
        "Ok".to_string(),
        result_sort,
        vec![Arc::new(ChcExpr::BitVec(7, 8))],
    );
    let eq = ChcExpr::eq(tag_s, ok);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(eq),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(s)]),
    ));

    let result = Box::new(DtFlattener::new()).transform(problem);
    // BV problem -> BV8 discriminant. Per-variant columns: disc, Ok payload,
    // Err payload, then the outer counter field.
    assert_eq!(
        result.problem.predicates()[0].arg_sorts,
        vec![
            ChcSort::BitVec(8),
            ChcSort::BitVec(8),
            ChcSort::BitVec(8),
            ChcSort::BitVec(8)
        ]
    );

    let constraint = result.problem.clauses()[0]
        .body
        .constraint
        .as_ref()
        .expect("constraint should be preserved");
    assert!(
        contains_var_bv_eq(constraint, "s_tag_disc", 0, 8),
        "DT-valued selector equality should lower constructor discriminant, got {constraint:?}"
    );
    assert!(
        contains_var_bv_eq(constraint, "s_tag_v0_ok_val", 7, 8),
        "DT-valued selector equality should lower constructor payload, got {constraint:?}"
    );
    assert!(
        !contains_var_bv_eq(constraint, "s_tag_v1_err_val", 0, 8),
        "inactive-variant columns must NOT be compared by DT equality, got {constraint:?}"
    );
    for name in ["tag", "is-Ok", "is-Err", "ok_val", "err_val"] {
        assert!(
            !contains_func_name(constraint, name),
            "DT-valued selector equality should not leave {name} applications, got {constraint:?}"
        );
    }
}

#[test]
fn test_dt_flattener_preserves_non_dt_args() {
    let dt_sort = pair_sort();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("P", vec![dt_sort.clone(), ChcSort::Int]);

    // Clause: true => P(mk(1, 2), 99)
    let ctor_app = ChcExpr::FuncApp(
        "mk".to_string(),
        dt_sort,
        vec![Arc::new(ChcExpr::Int(1)), Arc::new(ChcExpr::Int(2))],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(pred, vec![ctor_app, ChcExpr::Int(99)]),
    ));

    let transformer = Box::new(DtFlattener::new());
    let result = transformer.transform(problem);

    // P should now be (Int, Int, Int) — two from DT + one original Int
    assert_eq!(result.problem.predicates()[0].arity(), 3);
    let clause = &result.problem.clauses()[0];
    if let ClauseHead::Predicate(_, args) = &clause.head {
        assert_eq!(args.len(), 3);
        assert_eq!(args[0], ChcExpr::Int(1));
        assert_eq!(args[1], ChcExpr::Int(2));
        assert_eq!(args[2], ChcExpr::Int(99));
    } else {
        panic!("expected predicate head");
    }
}

/// Helper: create a nested DT sort (Outer wrapping Inner).
fn nested_sort() -> (ChcSort, ChcSort) {
    let inner_sort = ChcSort::Datatype {
        name: "Inner".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mkInner".to_string(),
            selectors: vec![ChcDtSelector {
                name: "ix".to_string(),
                sort: ChcSort::Int,
            }],
        }]),
    };
    let outer_sort = ChcSort::Datatype {
        name: "Outer".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mkOuter".to_string(),
            selectors: vec![
                ChcDtSelector {
                    name: "tag".to_string(),
                    sort: ChcSort::Int,
                },
                ChcDtSelector {
                    name: "payload".to_string(),
                    sort: inner_sort.clone(),
                },
            ],
        }]),
    };
    (inner_sort, outer_sort)
}

#[test]
fn test_flatten_sort_nested_dt() {
    let (_, outer_sort) = nested_sort();
    let flat = flatten_sort(&outer_sort, DiscKind::Int);
    // Outer(tag: Int, payload: Inner(ix: Int)) -> [Int, Int]
    assert_eq!(flat, vec![ChcSort::Int, ChcSort::Int]);
}

#[test]
fn test_expand_dt_var_nested() {
    let (_, outer_sort) = nested_sort();
    let fields = expand_dt_var("o", &outer_sort, DiscKind::Int);
    assert_eq!(fields.len(), 2);
    assert_eq!(fields[0].0, "o_tag");
    assert_eq!(fields[0].1, ChcSort::Int);
    assert_eq!(fields[1].0, "o_payload_ix");
    assert_eq!(fields[1].1, ChcSort::Int);
}

#[test]
fn test_dt_flattener_nested_struct() {
    let (inner_sort, outer_sort) = nested_sort();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![outer_sort.clone()]);

    // Clause: true => Inv(mkOuter(1, mkInner(42)))
    let inner_ctor = ChcExpr::FuncApp(
        "mkInner".to_string(),
        inner_sort,
        vec![Arc::new(ChcExpr::Int(42))],
    );
    let outer_ctor = ChcExpr::FuncApp(
        "mkOuter".to_string(),
        outer_sort,
        vec![Arc::new(ChcExpr::Int(1)), Arc::new(inner_ctor)],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(pred, vec![outer_ctor]),
    ));

    let transformer = Box::new(DtFlattener::new());
    let result = transformer.transform(problem);

    // Inv should now have 2 Int args (tag, ix) from nested flattening
    assert_eq!(result.problem.predicates()[0].arity(), 2);
    let clause = &result.problem.clauses()[0];
    if let ClauseHead::Predicate(_, args) = &clause.head {
        assert_eq!(args.len(), 2);
        assert_eq!(args[0], ChcExpr::Int(1));
        assert_eq!(args[1], ChcExpr::Int(42));
    } else {
        panic!("expected predicate head");
    }
}

#[test]
fn test_dt_flattener_multi_ctor_discriminant() {
    let sort = option_int_sort();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![sort.clone()]);

    // Clause: true => Inv(Some(42))
    let ctor_app = ChcExpr::FuncApp(
        "Some".to_string(),
        sort.clone(),
        vec![Arc::new(ChcExpr::Int(42))],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(pred, vec![ctor_app]),
    ));

    let transformer = Box::new(DtFlattener::new());
    let result = transformer.transform(problem);

    // Inv should now have 2 Int args (disc, val)
    assert_eq!(result.problem.predicates()[0].arity(), 2);
    let clause = &result.problem.clauses()[0];
    if let ClauseHead::Predicate(_, args) = &clause.head {
        assert_eq!(args.len(), 2);
        // Some is constructor index 1 (None=0, Some=1)
        assert_eq!(args[0], ChcExpr::Int(1));
        assert_eq!(args[1], ChcExpr::Int(42));
    } else {
        panic!("expected predicate head");
    }
}

#[test]
fn test_dt_flattener_none_constructor() {
    let sort = option_int_sort();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![sort.clone()]);

    // Clause: true => Inv(None)
    // None is a nullary constructor — represented as FuncApp with empty args
    let ctor_app = ChcExpr::FuncApp("None".to_string(), sort.clone(), vec![]);
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(pred, vec![ctor_app]),
    ));

    let transformer = Box::new(DtFlattener::new());
    let result = transformer.transform(problem);

    assert_eq!(result.problem.predicates()[0].arity(), 2);
    let clause = &result.problem.clauses()[0];
    if let ClauseHead::Predicate(_, args) = &clause.head {
        assert_eq!(args.len(), 2);
        // None is constructor index 0
        assert_eq!(args[0], ChcExpr::Int(0));
        // Default value for Some's (inactive) val column
        assert_eq!(args[1], ChcExpr::Int(0));
    } else {
        panic!("expected predicate head");
    }
}

#[test]
fn test_dt_flattener_tester_rewrite() {
    let sort = option_int_sort();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![sort.clone()]);

    // Clause with tester in constraint: (is-Some x) => Inv(x)
    let x = ChcVar::new("x", sort.clone());
    let tester = ChcExpr::FuncApp(
        "is-Some".to_string(),
        ChcSort::Bool,
        vec![Arc::new(ChcExpr::Var(x.clone()))],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(tester),
        ClauseHead::Predicate(pred, vec![ChcExpr::Var(x)]),
    ));

    let transformer = Box::new(DtFlattener::new());
    let result = transformer.transform(problem);

    // Constraint should rewrite `is-Some(x)` to `x_disc = 1`; flattened
    // multi-constructor predicate args also carry discriminator-domain guards.
    let clause = &result.problem.clauses()[0];
    assert!(clause.body.constraint.is_some());
    let c = clause.body.constraint.as_ref().unwrap();
    assert!(
        contains_int_cmp(c, ChcOp::Eq, "x_disc", 1),
        "Expected tester rewrite to include x_disc = 1, got: {c:?}"
    );
}

/// Tester applied directly to a constructor application folds to a constant.
#[test]
fn test_dt_flattener_tester_on_ctor_app_folds() {
    let sort = option_int_sort();
    let cx_vars = VarExpansion::default();
    let events = Cell::new(ApproxEvents::default());
    let wva_vars = std::cell::RefCell::new(FxHashMap::default());
    let cx = FlattenCx {
        vars: &cx_vars,
        disc: DiscKind::Int,
        events: &events,
        wva_vars: &wva_vars,
        clause_idx: 0,
    };
    let some = ChcExpr::FuncApp(
        "Some".to_string(),
        sort.clone(),
        vec![Arc::new(ChcExpr::Int(3))],
    );
    let none = ChcExpr::FuncApp("None".to_string(), sort, vec![]);
    let is_some_of_some =
        ChcExpr::FuncApp("is-Some".to_string(), ChcSort::Bool, vec![Arc::new(some)]);
    let is_some_of_none =
        ChcExpr::FuncApp("is-Some".to_string(), ChcSort::Bool, vec![Arc::new(none)]);
    assert_eq!(rewrite_expr(&is_some_of_some, &cx), ChcExpr::Bool(true));
    assert_eq!(rewrite_expr(&is_some_of_none, &cx), ChcExpr::Bool(false));
}

#[test]
fn test_dt_disequality_flattened() {
    let dt_sort = pair_sort();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![dt_sort.clone()]);

    // Clause: (not (= p (mk 42 7))) => Inv(p)
    let p = ChcVar::new("p", dt_sort.clone());
    let ctor_app = ChcExpr::FuncApp(
        "mk".to_string(),
        dt_sort,
        vec![Arc::new(ChcExpr::Int(42)), Arc::new(ChcExpr::Int(7))],
    );
    let ne_expr = ChcExpr::Op(
        ChcOp::Ne,
        vec![Arc::new(ChcExpr::Var(p.clone())), Arc::new(ctor_app)],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ne_expr),
        ClauseHead::Predicate(pred, vec![ChcExpr::Var(p)]),
    ));

    let transformer = Box::new(DtFlattener::new());
    let result = transformer.transform(problem);

    // Constraint should be the negation of the field-equality conjunction
    let clause = &result.problem.clauses()[0];
    assert!(clause.body.constraint.is_some());
    let c = clause.body.constraint.as_ref().unwrap();
    assert!(
        matches!(
            c,
            ChcExpr::Op(ChcOp::Not, not_args)
                if matches!(not_args[0].as_ref(), ChcExpr::Op(ChcOp::And, args) if args.len() == 2)
        ),
        "Expected Not(And of 2 equalities), got: {c:?}"
    );
}

/// #8419: DT with BV fields should flatten to BV-sorted scalar args (and,
/// with BV present, a BV8 discriminant).
#[test]
fn test_dt_flattener_bv_field_sorts_preserved() {
    let dt_sort = ChcSort::Datatype {
        name: "OptionBV8".to_string(),
        constructors: Arc::new(vec![
            ChcDtConstructor {
                name: "None".to_string(),
                selectors: vec![],
            },
            ChcDtConstructor {
                name: "Some".to_string(),
                selectors: vec![ChcDtSelector {
                    name: "val".to_string(),
                    sort: ChcSort::BitVec(8),
                }],
            },
        ]),
    };

    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![dt_sort.clone()]);

    // Clause: true => Inv(Some(#x04))
    let ctor_app = ChcExpr::FuncApp(
        "Some".to_string(),
        dt_sort,
        vec![Arc::new(ChcExpr::BitVec(4, 8))],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(pred, vec![ctor_app]),
    ));

    let transformer = Box::new(DtFlattener::new());
    let result = transformer.transform(problem);

    // Inv should now have (BV8 disc, BitVec(8) val) — BV problem uses a BV8
    // discriminant so the flattened problem stays in the BV-native lane.
    assert_eq!(result.problem.predicates()[0].arity(), 2);
    assert_eq!(
        result.problem.predicates()[0].arg_sorts[0],
        ChcSort::BitVec(8)
    );
    assert_eq!(
        result.problem.predicates()[0].arg_sorts[1],
        ChcSort::BitVec(8),
        "BV field sort should be preserved after DT flattening"
    );
    let ClauseHead::Predicate(_, args) = &result.problem.clauses()[0].head else {
        panic!("expected predicate head");
    };
    assert_eq!(args, &vec![ChcExpr::BitVec(1, 8), ChcExpr::BitVec(4, 8)]);
}

/// Multi-constructor padding must match the flattened field sort. This is
/// safety-critical for ADT-LIA/BV variants with nullary enum cases.
#[test]
fn test_dt_flattener_none_bv_padding_is_sort_correct() {
    let dt_sort = ChcSort::Datatype {
        name: "OptionBV8".to_string(),
        constructors: Arc::new(vec![
            ChcDtConstructor {
                name: "None".to_string(),
                selectors: vec![],
            },
            ChcDtConstructor {
                name: "Some".to_string(),
                selectors: vec![ChcDtSelector {
                    name: "val".to_string(),
                    sort: ChcSort::BitVec(8),
                }],
            },
        ]),
    };

    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![dt_sort.clone()]);
    let ctor_app = ChcExpr::FuncApp("None".to_string(), dt_sort, vec![]);
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(pred, vec![ctor_app]),
    ));

    let result = Box::new(DtFlattener::new()).transform(problem);
    let ClauseHead::Predicate(_, args) = &result.problem.clauses()[0].head else {
        panic!("expected predicate head");
    };
    assert_eq!(args, &vec![ChcExpr::BitVec(0, 8), ChcExpr::BitVec(0, 8)]);
}

#[test]
fn test_selector_extraction_flattens_nested_multi_ctor_payload_components() {
    let sort = option_pair_sort();
    let x = ChcVar::new("x", sort.clone());
    let vars = VarExpansion::default();
    let events = Cell::new(ApproxEvents::default());
    let wva_vars = std::cell::RefCell::new(FxHashMap::default());
    let cx = FlattenCx {
        vars: &vars,
        disc: DiscKind::Int,
        events: &events,
        wva_vars: &wva_vars,
        clause_idx: 0,
    };
    let components = selector_extraction(&ChcExpr::var(x), &sort, &cx);

    // Per-variant columns: [disc, SomePair.pair.fst, SomePair.pair.snd]
    assert_eq!(components.len(), 3);
    assert_eq!(components[0].sort(), ChcSort::Int);
    assert_eq!(components[1].sort(), ChcSort::Int);
    assert_eq!(components[2].sort(), ChcSort::Int);
    assert!(
        matches!(
            &components[1],
            ChcExpr::FuncApp(name, ChcSort::Int, _) if name == "fst"
        ),
        "first nested payload component should extract Pair.fst, got {:?}",
        components[1]
    );
    assert!(
        matches!(
            &components[2],
            ChcExpr::FuncApp(name, ChcSort::Int, _) if name == "snd"
        ),
        "second nested payload component should extract Pair.snd, got {:?}",
        components[2]
    );
}

/// #8419: Nested DT with BV fields should flatten recursively.
#[test]
fn test_dt_flattener_nested_bv_struct() {
    let inner_sort = ChcSort::Datatype {
        name: "BvPair".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mkBvPair".to_string(),
            selectors: vec![
                ChcDtSelector {
                    name: "lo".to_string(),
                    sort: ChcSort::BitVec(8),
                },
                ChcDtSelector {
                    name: "hi".to_string(),
                    sort: ChcSort::BitVec(8),
                },
            ],
        }]),
    };
    let outer_sort = ChcSort::Datatype {
        name: "Wrapper".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "wrap".to_string(),
            selectors: vec![
                ChcDtSelector {
                    name: "tag".to_string(),
                    sort: ChcSort::Int,
                },
                ChcDtSelector {
                    name: "payload".to_string(),
                    sort: inner_sort,
                },
            ],
        }]),
    };

    let flat = flatten_sort(&outer_sort, DiscKind::Int);
    // Wrapper(tag: Int, payload: BvPair(lo: BV8, hi: BV8)) -> [Int, BV8, BV8]
    assert_eq!(flat.len(), 3);
    assert_eq!(flat[0], ChcSort::Int);
    assert_eq!(flat[1], ChcSort::BitVec(8));
    assert_eq!(flat[2], ChcSort::BitVec(8));
}

#[test]
fn backtranslator_reconstructs_single_ctor_formula_selectors() {
    let dt_sort = pair_sort();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![dt_sort.clone()]);

    let result = Box::new(DtFlattener::new()).transform(problem);
    assert_eq!(result.problem.predicates()[0].arity(), 2);

    let fst = ChcVar::new("flat_fst", ChcSort::Int);
    let snd = ChcVar::new("flat_snd", ChcSort::Int);
    let formula = ChcExpr::eq(ChcExpr::var(fst.clone()), ChcExpr::var(snd.clone()));
    let mut model = InvariantModel::new();
    model.set(pred, PredicateInterpretation::new(vec![fst, snd], formula));

    let translated = result.back_translator.translate_validity(model);
    let interp = translated.get(&pred).expect("predicate should translate");
    assert_eq!(interp.vars.len(), 1);
    assert_eq!(interp.vars[0].sort, dt_sort);
    assert!(matches!(
        &interp.formula,
        ChcExpr::Op(ChcOp::Eq, args)
            if matches!(
                args[0].as_ref(),
                ChcExpr::FuncApp(name, ChcSort::Int, selector_args)
                    if name == "fst"
                    && matches!(selector_args[0].as_ref(), ChcExpr::Var(v) if v == &interp.vars[0])
            )
            && matches!(
                args[1].as_ref(),
                ChcExpr::FuncApp(name, ChcSort::Int, selector_args)
                    if name == "snd"
                    && matches!(selector_args[0].as_ref(), ChcExpr::Var(v) if v == &interp.vars[0])
            )
    ));
}

#[test]
fn dt_flat_map_remembers_single_ctor_selector_obligations() {
    let dt_sort = pair_sort();
    let info = make_flat_info(0, &dt_sort, DiscKind::Int).expect("pair should have flatten info");

    assert_eq!(info.original_arg, 0);
    assert_eq!(info.original_sort, dt_sort);
    assert!(info.single_ctor);
    assert_eq!(info.components.len(), 2);
    assert!(matches!(
        &info.components[0].obligation,
        DtRefinementObligation::SelectorPath(path) if path == &vec!["fst".to_string()]
    ));
    assert!(matches!(
        &info.components[1].obligation,
        DtRefinementObligation::SelectorPath(path) if path == &vec!["snd".to_string()]
    ));
}

#[test]
fn dt_flat_map_remembers_multi_ctor_refinement_obligations() {
    let dt_sort = option_int_sort();
    let info = make_flat_info(0, &dt_sort, DiscKind::Int).expect("option should have flatten info");

    assert!(!info.single_ctor);
    assert_eq!(info.components.len(), 2);
    assert!(matches!(
        info.components[0].obligation,
        DtRefinementObligation::Discriminant
    ));
    // Per-variant columns: the payload column is owned by exactly Some.
    assert!(matches!(
        &info.components[1].obligation,
        DtRefinementObligation::GuardedPayload {
            constructors,
            field_offset: 1
        } if constructors == &vec!["Some".to_string()]
    ));
}

#[test]
fn dt_flattener_transform_memory_persists_flattening_map_facts() {
    let mut problem = ChcProblem::new();
    problem.declare_predicate("PairInv", vec![pair_sort()]);
    problem.declare_predicate("OptionInv", vec![option_int_sort(), ChcSort::Int]);

    let result = Box::new(DtFlattener::new()).transform(problem);
    let memory = result.back_translator.transform_memory();

    assert_eq!(memory.fact_value("datatype_flattening_maps"), Some("2"));
    assert_eq!(memory.fact_value("datatype_flattened_args"), Some("2"));
    assert_eq!(
        memory.fact_value("datatype_component_obligations"),
        Some("4")
    );
    assert_eq!(memory.fact_value("datatype_single_ctor_args"), Some("1"));
    assert_eq!(memory.fact_value("datatype_multi_ctor_args"), Some("1"));
    assert!(memory.has_obligation("datatype-selector-refinement-obligations"));
    assert!(
        !memory.has_obligation(DT_FLATTEN_APPROX_OBLIGATION),
        "no clauses were flattened, so no approximation events should be recorded"
    );
    assert!(!memory.unsafe_backtranslation_complete());
}

fn balance_sort() -> ChcSort {
    ChcSort::Datatype {
        name: "Balance".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mkBalance".to_string(),
            selectors: vec![
                ChcDtSelector {
                    name: "balance".to_string(),
                    sort: ChcSort::BitVec(256),
                },
                ChcDtSelector {
                    name: "live".to_string(),
                    sort: ChcSort::Bool,
                },
            ],
        }]),
    }
}

fn solidity_state_sort() -> ChcSort {
    let balances_sort = ChcSort::Array(Box::new(ChcSort::BitVec(160)), Box::new(balance_sort()));
    ChcSort::Datatype {
        name: "State".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mkState".to_string(),
            selectors: vec![ChcDtSelector {
                name: "balances".to_string(),
                sort: balances_sort,
            }],
        }]),
    }
}

fn int_array_sort() -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int))
}

fn lia_array_state_sort() -> ChcSort {
    ChcSort::Datatype {
        name: "LiaArrayState".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mkLiaArrayState".to_string(),
            selectors: vec![
                ChcDtSelector {
                    name: "counter".to_string(),
                    sort: ChcSort::Int,
                },
                ChcDtSelector {
                    name: "heap".to_string(),
                    sort: int_array_sort(),
                },
            ],
        }]),
    }
}

#[test]
fn test_dt_flattener_lia_array_field_rewrites_selector_selects() {
    let state_sort = lia_array_state_sort();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![state_sort.clone()]);

    let state = ChcVar::new("s", state_sort.clone());
    let heap = ChcExpr::FuncApp(
        "heap".to_string(),
        int_array_sort(),
        vec![Arc::new(ChcExpr::var(state.clone()))],
    );
    let counter = ChcExpr::FuncApp(
        "counter".to_string(),
        ChcSort::Int,
        vec![Arc::new(ChcExpr::var(state.clone()))],
    );
    let constraint = ChcExpr::ge(ChcExpr::select(heap, ChcExpr::Int(4)), counter);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(constraint),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(state)]),
    ));

    let result = Box::new(DtFlattener::new()).transform(problem);

    assert_eq!(
        result.problem.predicates()[0].arg_sorts,
        vec![ChcSort::Int, int_array_sort()]
    );
    let constraint = result.problem.clauses()[0]
        .body
        .constraint
        .as_ref()
        .expect("constraint should be preserved");
    assert!(
        matches!(
            constraint,
            ChcExpr::Op(ChcOp::Ge, ge_args)
                if matches!(
                    ge_args[0].as_ref(),
                    ChcExpr::Op(ChcOp::Select, select_args)
                        if matches!(
                            select_args[0].as_ref(),
                            ChcExpr::Var(v) if v.name == "s_heap" && v.sort == int_array_sort()
                        )
                        && matches!(select_args[1].as_ref(), ChcExpr::Int(4))
                )
                && matches!(
                    ge_args[1].as_ref(),
                    ChcExpr::Var(v) if v.name == "s_counter" && v.sort == ChcSort::Int
                )
        ),
        "ADT-LIA array selector should rewrite to select over flattened array field, got {constraint:?}"
    );
}

#[test]
fn backtranslator_reconstructs_lia_array_field_selector_formula() {
    let state_sort = lia_array_state_sort();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![state_sort.clone()]);

    let result = Box::new(DtFlattener::new()).transform(problem);
    assert_eq!(
        result.problem.predicates()[0].arg_sorts,
        vec![ChcSort::Int, int_array_sort()]
    );

    let counter = ChcVar::new("counter", ChcSort::Int);
    let heap = ChcVar::new("heap", int_array_sort());
    let formula = ChcExpr::ge(
        ChcExpr::select(ChcExpr::var(heap.clone()), ChcExpr::Int(7)),
        ChcExpr::var(counter.clone()),
    );
    let mut model = InvariantModel::new();
    model.set(
        pred,
        PredicateInterpretation::new(vec![counter, heap], formula),
    );

    let translated = result.back_translator.translate_validity(model);
    let interp = translated.get(&pred).expect("predicate should translate");
    assert_eq!(interp.vars.len(), 1);
    assert_eq!(interp.vars[0].sort, state_sort);
    assert!(
        matches!(
            &interp.formula,
            ChcExpr::Op(ChcOp::Ge, ge_args)
                if matches!(
                    ge_args[0].as_ref(),
                    ChcExpr::Op(ChcOp::Select, select_args)
                        if matches!(
                            select_args[0].as_ref(),
                            ChcExpr::FuncApp(name, sort, selector_args)
                                if name == "heap"
                                && sort == &int_array_sort()
                                && matches!(
                                    selector_args[0].as_ref(),
                                    ChcExpr::Var(v) if v == &interp.vars[0]
                                )
                        )
                        && matches!(select_args[1].as_ref(), ChcExpr::Int(7))
                )
                && matches!(
                    ge_args[1].as_ref(),
                    ChcExpr::FuncApp(name, ChcSort::Int, selector_args)
                        if name == "counter"
                        && matches!(
                            selector_args[0].as_ref(),
                            ChcExpr::Var(v) if v == &interp.vars[0]
                        )
                )
        ),
        "flattened ADT-LIA array formula should backtranslate through original selectors"
    );
}

#[test]
fn backtranslator_reconstructs_composed_projection_array_selector_formula() {
    let state_sort = solidity_state_sort();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![state_sort.clone()]);

    let result = TransformationPipeline::new()
        .with(DtFlattener::new())
        .with(SolidityArrayDtProjectionTransformer::new())
        .transform(problem);
    assert_eq!(result.problem.predicates()[0].arity(), 2);

    let balance_array = ChcVar::new(
        "balance_array",
        result.problem.predicates()[0].arg_sorts[0].clone(),
    );
    let live_array = ChcVar::new(
        "live_array",
        result.problem.predicates()[0].arg_sorts[1].clone(),
    );
    let account = ChcExpr::BitVec(4, 160);
    let formula = ChcExpr::eq(
        ChcExpr::select(ChcExpr::var(balance_array.clone()), account.clone()),
        ChcExpr::BitVec(9, 256),
    );
    let mut model = InvariantModel::new();
    model.set(
        pred,
        PredicateInterpretation::new(vec![balance_array, live_array], formula),
    );

    let translated = result.back_translator.translate_validity(model);
    let interp = translated.get(&pred).expect("predicate should translate");
    assert_eq!(interp.vars.len(), 1);
    assert_eq!(interp.vars[0].sort, state_sort);
    assert!(matches!(
        &interp.formula,
        ChcExpr::Op(ChcOp::Eq, eq_args)
            if matches!(
                eq_args[0].as_ref(),
                ChcExpr::FuncApp(name, ChcSort::BitVec(256), selector_args)
                    if name == "balance"
                    && matches!(
                        selector_args[0].as_ref(),
                        ChcExpr::Op(ChcOp::Select, select_args)
                            if matches!(
                                select_args[0].as_ref(),
                                ChcExpr::FuncApp(array_name, _, array_selector_args)
                                    if array_name == "balances"
                                    && matches!(
                                        array_selector_args[0].as_ref(),
                                        ChcExpr::Var(v) if v == &interp.vars[0]
                                    )
                            )
                            && matches!(select_args[1].as_ref(), ChcExpr::BitVec(4, 160))
                    )
            )
            && matches!(eq_args[1].as_ref(), ChcExpr::BitVec(9, 256))
    ));
}

fn lia_entry_sort() -> ChcSort {
    ChcSort::Datatype {
        name: "LiaEntry".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mkLiaEntry".to_string(),
            selectors: vec![
                ChcDtSelector {
                    name: "value".to_string(),
                    sort: ChcSort::Int,
                },
                ChcDtSelector {
                    name: "limit".to_string(),
                    sort: ChcSort::Int,
                },
            ],
        }]),
    }
}

fn lia_entry_state_sort() -> ChcSort {
    let entries_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(lia_entry_sort()));
    ChcSort::Datatype {
        name: "LiaEntryState".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mkLiaEntryState".to_string(),
            selectors: vec![ChcDtSelector {
                name: "entries".to_string(),
                sort: entries_sort,
            }],
        }]),
    }
}

#[test]
fn backtranslator_reconstructs_composed_lia_array_dt_projection_formula() {
    let state_sort = lia_entry_state_sort();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![state_sort.clone()]);

    let result = TransformationPipeline::new()
        .with(DtFlattener::new())
        .with(SolidityArrayDtProjectionTransformer::new())
        .transform(problem);
    assert_eq!(result.problem.predicates()[0].arity(), 2);
    assert_eq!(
        result.problem.predicates()[0].arg_sorts,
        vec![
            ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
            ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
        ]
    );

    let value_array = ChcVar::new(
        "value_array",
        result.problem.predicates()[0].arg_sorts[0].clone(),
    );
    let limit_array = ChcVar::new(
        "limit_array",
        result.problem.predicates()[0].arg_sorts[1].clone(),
    );
    let formula = ChcExpr::ge(
        ChcExpr::select(ChcExpr::var(value_array.clone()), ChcExpr::Int(9)),
        ChcExpr::Int(0),
    );
    let mut model = InvariantModel::new();
    model.set(
        pred,
        PredicateInterpretation::new(vec![value_array, limit_array], formula),
    );

    let translated = result.back_translator.translate_validity(model);
    let interp = translated.get(&pred).expect("predicate should translate");
    assert_eq!(interp.vars.len(), 1);
    assert_eq!(interp.vars[0].sort, state_sort);
    assert!(
        matches!(
            &interp.formula,
            ChcExpr::Op(ChcOp::Ge, ge_args)
                if matches!(
                    ge_args[0].as_ref(),
                    ChcExpr::FuncApp(name, ChcSort::Int, selector_args)
                        if name == "value"
                        && matches!(
                            selector_args[0].as_ref(),
                            ChcExpr::Op(ChcOp::Select, select_args)
                                if matches!(
                                    select_args[0].as_ref(),
                                    ChcExpr::FuncApp(array_name, _, array_selector_args)
                                        if array_name == "entries"
                                        && matches!(
                                            array_selector_args[0].as_ref(),
                                            ChcExpr::Var(v) if v == &interp.vars[0]
                                        )
                                )
                                && matches!(select_args[1].as_ref(), ChcExpr::Int(9))
                        )
                )
                && matches!(ge_args[1].as_ref(), ChcExpr::Int(0))
        ),
        "ADT-LIA array-of-DT projection should backtranslate to selectors over the original array field"
    );
}

#[test]
fn backtranslator_reconstructs_multi_ctor_discriminant_formula() {
    let dt_sort = option_int_sort();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![dt_sort.clone()]);

    let result = Box::new(DtFlattener::new()).transform(problem);
    assert_eq!(result.problem.predicates()[0].arity(), 2);

    let disc = ChcVar::new("disc", ChcSort::Int);
    let val = ChcVar::new("val", ChcSort::Int);
    let mut model = InvariantModel::new();
    model.set(
        pred,
        PredicateInterpretation::new(
            vec![disc.clone(), val],
            ChcExpr::eq(ChcExpr::var(disc), ChcExpr::Int(1)),
        ),
    );

    let translated = result.back_translator.translate_validity(model);
    let interp = translated.get(&pred).expect("predicate should be present");
    assert_eq!(interp.vars.len(), 1);
    assert_eq!(interp.vars[0].sort, dt_sort);
    assert!(
        matches!(
            &interp.formula,
            ChcExpr::Op(ChcOp::Eq, eq_args)
                if matches!(
                    eq_args[0].as_ref(),
                    ChcExpr::Op(ChcOp::Ite, ite_args)
                        if matches!(
                            ite_args[0].as_ref(),
                            ChcExpr::FuncApp(name, ChcSort::Bool, tester_args)
                                if name == "is-Some"
                                && matches!(
                                    tester_args[0].as_ref(),
                                    ChcExpr::Var(v) if v == &interp.vars[0]
                                )
                        )
                        && matches!(ite_args[1].as_ref(), ChcExpr::Int(1))
                        && matches!(ite_args[2].as_ref(), ChcExpr::Int(0))
                )
                && matches!(eq_args[1].as_ref(), ChcExpr::Int(1))
        ),
        "multi-constructor discriminator should backtranslate through DT testers"
    );
}

#[test]
fn backtranslator_reconstructs_multi_ctor_payload_formula() {
    let dt_sort = option_int_sort();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![dt_sort.clone()]);

    let result = Box::new(DtFlattener::new()).transform(problem);
    assert_eq!(result.problem.predicates()[0].arity(), 2);

    let disc = ChcVar::new("disc", ChcSort::Int);
    let val = ChcVar::new("val", ChcSort::Int);
    let mut model = InvariantModel::new();
    model.set(
        pred,
        PredicateInterpretation::new(
            vec![disc, val.clone()],
            ChcExpr::ge(ChcExpr::var(val), ChcExpr::Int(0)),
        ),
    );

    let translated = result.back_translator.translate_validity(model);
    let interp = translated.get(&pred).expect("predicate should be present");
    assert_eq!(interp.vars.len(), 1);
    assert_eq!(interp.vars[0].sort, dt_sort);
    // Per-variant columns: the payload column back-translates to the plain
    // selector application (the free accessor value), not a tester-guarded
    // union merge.
    assert!(
        matches!(
            &interp.formula,
            ChcExpr::Op(ChcOp::Ge, ge_args)
                if matches!(
                    ge_args[0].as_ref(),
                    ChcExpr::FuncApp(name, ChcSort::Int, selector_args)
                        if name == "val"
                        && matches!(
                            selector_args[0].as_ref(),
                            ChcExpr::Var(v) if v == &interp.vars[0]
                        )
                )
                && matches!(ge_args[1].as_ref(), ChcExpr::Int(0))
        ),
        "multi-constructor payload should backtranslate through its owning selector, got {:?}",
        interp.formula
    );
}

fn either_int_bool_sort() -> ChcSort {
    ChcSort::Datatype {
        name: "EitherIntBool".to_string(),
        constructors: Arc::new(vec![
            ChcDtConstructor {
                name: "Left".to_string(),
                selectors: vec![ChcDtSelector {
                    name: "left".to_string(),
                    sort: ChcSort::Int,
                }],
            },
            ChcDtConstructor {
                name: "Right".to_string(),
                selectors: vec![ChcDtSelector {
                    name: "right".to_string(),
                    sort: ChcSort::Bool,
                }],
            },
        ]),
    }
}

/// Per-variant columns: heterogeneous union slots (the old flattener's bail
/// case) now flatten — every variant owns its own columns.
#[test]
fn dt_flattener_flattens_heterogeneous_multi_ctor_fields() {
    let dt_sort = either_int_bool_sort();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![dt_sort.clone()]);
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(
            pred,
            vec![ChcExpr::FuncApp(
                "Left".to_string(),
                dt_sort.clone(),
                vec![Arc::new(ChcExpr::Int(1))],
            )],
        ),
    ));

    let result = Box::new(DtFlattener::new()).transform(problem);

    assert_eq!(
        result.problem.predicates()[0].arg_sorts,
        vec![ChcSort::Int, ChcSort::Int, ChcSort::Bool]
    );
    let ClauseHead::Predicate(_, args) = &result.problem.clauses()[0].head else {
        panic!("expected predicate head");
    };
    // Left(1): disc=0, left=1, inactive Right column default-filled.
    assert_eq!(
        args,
        &vec![ChcExpr::Int(0), ChcExpr::Int(1), ChcExpr::Bool(false)]
    );
    // Default-filled inactive columns are an approximation event: the chain
    // must carry the approximation obligation so transformed-evidence Safe
    // acceptance fails closed.
    let memory = result.back_translator.transform_memory();
    assert!(memory.has_obligation(DT_FLATTEN_APPROX_OBLIGATION));
}

#[test]
fn heterogeneous_multi_ctor_field_sorts_have_backtranslation_bindings() {
    let dt_sort = either_int_bool_sort();
    let original_var = ChcVar::new("x", dt_sort.clone());
    let bindings = flattened_selector_bindings_for_sort(&dt_sort, &original_var, DiscKind::Int)
        .expect("per-variant layout must produce backtranslation bindings");
    assert_eq!(bindings.len(), 3);
    assert!(matches!(
        &bindings[1].replacement,
        ChcExpr::FuncApp(name, ChcSort::Int, _) if name == "left"
    ));
    assert!(matches!(
        &bindings[2].replacement,
        ChcExpr::FuncApp(name, ChcSort::Bool, _) if name == "right"
    ));
}

/// DT equality between two VARIABLES lowers to the recursive disc-guarded
/// schema: disc equality plus per-variant guarded field equalities.
#[test]
fn test_dt_var_var_equality_uses_guarded_schema() {
    let dt_sort = either_int_bool_sort();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![dt_sort.clone(), dt_sort.clone()]);

    let x = ChcVar::new("x", dt_sort.clone());
    let y = ChcVar::new("y", dt_sort.clone());
    let eq = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::var(y.clone()));
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(eq),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(x), ChcExpr::var(y)]),
    ));

    let result = Box::new(DtFlattener::new()).transform(problem);
    let constraint = result.problem.clauses()[0]
        .body
        .constraint
        .as_ref()
        .expect("constraint should be preserved");

    // Expect: (= x_disc y_disc), (=> (= x_disc 0) (= x_v0_left y_v0_left)),
    //         (=> (= x_disc 1) (= x_v1_right y_v1_right)) — all conjoined
    // with the predicate-arg domain constraints.
    fn count_implies(expr: &ChcExpr) -> usize {
        match expr {
            ChcExpr::Op(ChcOp::Implies, _) => 1,
            ChcExpr::Op(_, args) | ChcExpr::FuncApp(_, _, args) => {
                args.iter().map(|a| count_implies(a)).sum()
            }
            _ => 0,
        }
    }
    fn contains_var_var_eq(expr: &ChcExpr, a: &str, b: &str) -> bool {
        match expr {
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => matches!(
                (args[0].as_ref(), args[1].as_ref()),
                (ChcExpr::Var(l), ChcExpr::Var(r)) if l.name == a && r.name == b
            ),
            ChcExpr::Op(_, args) | ChcExpr::FuncApp(_, _, args) => args
                .iter()
                .any(|arg| contains_var_var_eq(arg.as_ref(), a, b)),
            _ => false,
        }
    }
    assert!(
        contains_var_var_eq(constraint, "x_disc", "y_disc"),
        "guarded schema must equate discriminants: {constraint:?}"
    );
    assert!(
        contains_var_var_eq(constraint, "x_v0_left", "y_v0_left"),
        "guarded schema must equate Left payloads under guard: {constraint:?}"
    );
    assert!(
        contains_var_var_eq(constraint, "x_v1_right", "y_v1_right"),
        "guarded schema must equate Right payloads under guard: {constraint:?}"
    );
    assert!(
        count_implies(constraint) >= 2,
        "per-variant field equalities must be disc-guarded implications: {constraint:?}"
    );
}

/// Selector on a PROVABLY-mismatched constructor application becomes a
/// per-clause free variable deduplicated by (selector, subject) — congruent
/// within the clause, never fresh-per-occurrence, and never the
/// payload/default of another variant.
#[test]
fn test_wrong_variant_selector_on_ctor_app_is_congruent_free_var() {
    let dt_sort = either_int_bool_sort();
    let vars = VarExpansion::default();
    let events = Cell::new(ApproxEvents::default());
    let wva_vars = std::cell::RefCell::new(FxHashMap::default());
    let cx = FlattenCx {
        vars: &vars,
        disc: DiscKind::Int,
        events: &events,
        wva_vars: &wva_vars,
        clause_idx: 0,
    };

    let left_one = ChcExpr::FuncApp(
        "Left".to_string(),
        dt_sort.clone(),
        vec![Arc::new(ChcExpr::Int(1))],
    );
    let read = ChcExpr::FuncApp(
        "right".to_string(),
        ChcSort::Bool,
        vec![Arc::new(left_one.clone())],
    );

    let rewritten_a = rewrite_expr(&read, &cx);
    let rewritten_b = rewrite_expr(&read, &cx);
    // Deduplicated and congruent: both occurrences rewrite to the SAME
    // clause-local free variable of the selector's sort.
    assert_eq!(rewritten_a, rewritten_b);
    assert!(
        matches!(
            &rewritten_a,
            ChcExpr::Var(v)
                if v.name.starts_with("dtflat_wva_c0_") && v.sort == ChcSort::Bool
        ),
        "wrong-variant read must become the deduplicated clause-local wva var, got {rewritten_a:?}"
    );
    assert!(events.get().wrong_variant_reads >= 2);

    // Matching-variant read still digs into the payload.
    let ok_read = ChcExpr::FuncApp("left".to_string(), ChcSort::Int, vec![Arc::new(left_one)]);
    assert_eq!(rewrite_expr(&ok_read, &cx), ChcExpr::Int(1));
}

/// Nested multi-ctor inside multi-ctor (the ControlFlow<ControlFlow<...>>
/// shape): per-variant columns nest recursively.
fn nested_cf_sorts() -> (ChcSort, ChcSort) {
    let inner = ChcSort::Datatype {
        name: "InnerCF".to_string(),
        constructors: Arc::new(vec![
            ChcDtConstructor {
                name: "IC".to_string(),
                selectors: vec![ChcDtSelector {
                    name: "ic_val".to_string(),
                    sort: ChcSort::Bool,
                }],
            },
            ChcDtConstructor {
                name: "IB".to_string(),
                selectors: vec![ChcDtSelector {
                    name: "ib_val".to_string(),
                    sort: ChcSort::Int,
                }],
            },
        ]),
    };
    let outer = ChcSort::Datatype {
        name: "OuterCF".to_string(),
        constructors: Arc::new(vec![
            ChcDtConstructor {
                name: "OC".to_string(),
                selectors: vec![ChcDtSelector {
                    name: "oc_val".to_string(),
                    sort: inner.clone(),
                }],
            },
            ChcDtConstructor {
                name: "OB".to_string(),
                selectors: vec![ChcDtSelector {
                    name: "ob_val".to_string(),
                    sort: ChcSort::Int,
                }],
            },
        ]),
    };
    (inner, outer)
}

#[test]
fn test_flatten_sort_nested_multi_ctor_per_variant() {
    let (_, outer) = nested_cf_sorts();
    let flat = flatten_sort(&outer, DiscKind::Int);
    // [outer disc, inner disc, IC Bool, IB Int, OB Int]
    assert_eq!(
        flat,
        vec![
            ChcSort::Int,
            ChcSort::Int,
            ChcSort::Bool,
            ChcSort::Int,
            ChcSort::Int
        ]
    );
}

#[test]
fn test_nested_multi_ctor_ctor_app_and_equality() {
    let (inner, outer) = nested_cf_sorts();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![outer.clone()]);

    // Clause: (= x (OC (IB 5))) => Inv(x)
    let x = ChcVar::new("x", outer.clone());
    let ib5 = ChcExpr::FuncApp("IB".to_string(), inner, vec![Arc::new(ChcExpr::Int(5))]);
    let oc = ChcExpr::FuncApp("OC".to_string(), outer, vec![Arc::new(ib5)]);
    let eq = ChcExpr::eq(ChcExpr::var(x.clone()), oc);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(eq),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(x)]),
    ));

    let result = Box::new(DtFlattener::new()).transform(problem);
    assert_eq!(result.problem.predicates()[0].arity(), 5);
    let constraint = result.problem.clauses()[0]
        .body
        .constraint
        .as_ref()
        .expect("constraint should be preserved");

    // x = OC(IB 5) pins: x_disc = 0, x_v0_oc_val_disc = 1,
    // x_v0_oc_val_v1_ib_val = 5. The IC Bool column and the OB column are
    // inactive and must not be constrained by the equality.
    assert!(
        contains_int_cmp(constraint, ChcOp::Eq, "x_disc", 0),
        "outer disc pin missing: {constraint:?}"
    );
    assert!(
        contains_int_cmp(constraint, ChcOp::Eq, "x_v0_oc_val_disc", 1),
        "nested disc pin missing: {constraint:?}"
    );
    assert!(
        contains_int_cmp(constraint, ChcOp::Eq, "x_v0_oc_val_v1_ib_val", 5),
        "nested payload pin missing: {constraint:?}"
    );
    assert!(
        !contains_int_cmp(constraint, ChcOp::Eq, "x_v1_ob_val", 0),
        "inactive OB column must not be equated to the default: {constraint:?}"
    );
}

/// BV problems constrain the BV8 discriminant domain with bvule.
#[test]
fn test_bv_disc_domain_uses_bvule() {
    let dt_sort = result8_sort();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![dt_sort.clone()]);
    let x = ChcVar::new("x", dt_sort);
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(pred, vec![ChcExpr::var(x)])], None),
        ClauseHead::False,
    ));

    let result = Box::new(DtFlattener::new()).transform(problem);
    let constraint = result.problem.clauses()[0]
        .body
        .constraint
        .as_ref()
        .expect("BV multi-ctor predicate args should carry disc domain constraints");

    fn contains_bvule(expr: &ChcExpr, var_fragment: &str, bound: u128) -> bool {
        match expr {
            ChcExpr::Op(ChcOp::BvULe, args) if args.len() == 2 => matches!(
                (args[0].as_ref(), args[1].as_ref()),
                (ChcExpr::Var(v), ChcExpr::BitVec(n, 8))
                    if v.name.contains(var_fragment) && *n == bound
            ),
            ChcExpr::Op(_, args) | ChcExpr::FuncApp(_, _, args) => args
                .iter()
                .any(|arg| contains_bvule(arg.as_ref(), var_fragment, bound)),
            _ => false,
        }
    }
    assert!(
        contains_bvule(constraint, "x_disc", 1),
        "BV8 discriminant should be domain-constrained via bvule: {constraint:?}"
    );
}

// ── dtmini verdict-preservation battery (designB fixtures, item 4 Stage 4) ──

mod dtmini {
    use super::*;
    use crate::adaptive::{AdaptiveConfig, AdaptivePortfolio};
    use crate::parser::ChcParser;

    fn parse(smt: &str) -> ChcProblem {
        let problem =
            ChcParser::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
        problem
            .validate()
            .unwrap_or_else(|err| panic!("CHC validation failed: {err}\nSMT2:\n{smt}"));
        problem
    }

    fn adaptive_verdict(problem: ChcProblem) -> crate::VerifiedChcResult {
        AdaptivePortfolio::new(
            problem,
            AdaptiveConfig::test_default().with_time_budget(std::time::Duration::from_secs(30)),
        )
        .solve()
    }

    /// Safe: P1 only ever holds Cont(true); the query needs Brk with payload 7.
    const DTMINI_SAFE: &str = r#"
(set-logic HORN)
(declare-datatype CF ((Cont (Cont_f Bool)) (Brk (Brk_f (_ BitVec 32)))))
(declare-var x CF)
(declare-var y CF)
(declare-rel P0 (CF))
(declare-rel P1 (CF))
(declare-rel error ())
(rule (=> (= x (Cont true)) (P0 x)))
(rule (=> (and (P0 x) (= y x)) (P1 y)))
(rule (=> (and (P1 x) ((_ is Brk) x) (= (Brk_f x) #x00000007)) error))
(query error)
"#;

    /// Safe, tester-guarded WRONG-VARIANT accessor: rule 2 reads `Brk_f x`
    /// under an `is Cont` guard (a free accessor value) and rebuilds a Brk;
    /// the query then needs `is Cont` on P1 which only holds Brk values.
    const DTMINI_SAFE2: &str = r#"
(set-logic HORN)
(declare-datatype CF ((Cont (Cont_f Bool)) (Brk (Brk_f (_ BitVec 32)))))
(declare-var x CF)
(declare-var y CF)
(declare-rel P0 (CF))
(declare-rel P1 (CF))
(declare-rel error ())
(rule (=> (= x (Cont true)) (P0 x)))
(rule (=> (and (P0 x) ((_ is Cont) x) (= y (Brk (bvadd (Brk_f x) #x00000001)))) (P1 y)))
(rule (=> (and (P1 x) ((_ is Cont) x)) error))
(query error)
"#;

    /// Unsafe twin of DTMINI_SAFE: P0 can also hold Brk(7).
    const DTMINI_UNSAFE: &str = r#"
(set-logic HORN)
(declare-datatype CF ((Cont (Cont_f Bool)) (Brk (Brk_f (_ BitVec 32)))))
(declare-var x CF)
(declare-var y CF)
(declare-rel P0 (CF))
(declare-rel P1 (CF))
(declare-rel error ())
(rule (=> (or (= x (Cont true)) (= x (Brk #x00000007))) (P0 x)))
(rule (=> (and (P0 x) (= y x)) (P1 y)))
(rule (=> (and (P1 x) ((_ is Brk) x) (= (Brk_f x) #x00000007)) error))
(query error)
"#;

    /// The heterogeneous CF union (Bool vs BV32 payloads) must now FLATTEN
    /// (the old union-slot flattener bailed on exactly this shape) with a
    /// BV8 discriminant and per-variant columns.
    #[test]
    fn dtmini_cf_flattens_per_variant() {
        let problem = parse(DTMINI_SAFE);
        let result = Box::new(DtFlattener::new()).transform(problem);
        let memory = result.back_translator.transform_memory();
        assert!(
            !memory.is_identity_grade(),
            "per-variant flattener must engage on the heterogeneous CF union"
        );
        assert!(!result.problem.has_datatype_sorts());
        // P0(CF) -> P0(disc BV8, Cont Bool col, Brk BV32 col)
        assert_eq!(
            result.problem.predicates()[0].arg_sorts,
            vec![ChcSort::BitVec(8), ChcSort::Bool, ChcSort::BitVec(32)]
        );
    }

    /// Verdict preservation, Unsafe direction: the flattened problem must
    /// still derive the error (encoding completeness for the unsafe path).
    #[test]
    fn dtmini_unsafe_flattened_problem_stays_unsafe() {
        let problem = parse(DTMINI_UNSAFE);
        let flat = Box::new(DtFlattener::new()).transform(problem).problem;
        assert!(!flat.has_datatype_sorts());
        let verdict = adaptive_verdict(flat);
        assert!(
            matches!(verdict, crate::VerifiedChcResult::Unsafe(_)),
            "flattened dtmini_unsafe must stay Unsafe, got {verdict}"
        );
    }

    /// Verdict preservation, Safe direction: the flattened problems must
    /// never flip to Unsafe (Unknown is acceptable fail-closed behavior).
    #[test]
    fn dtmini_safe_flattened_problems_never_flip_to_unsafe() {
        for (name, smt) in [("dtmini_safe", DTMINI_SAFE), ("dtmini_safe2", DTMINI_SAFE2)] {
            let problem = parse(smt);
            let flat = Box::new(DtFlattener::new()).transform(problem).problem;
            let verdict = adaptive_verdict(flat);
            assert!(
                !matches!(verdict, crate::VerifiedChcResult::Unsafe(_)),
                "{name}: flattened Safe fixture must never become Unsafe, got {verdict}"
            );
        }
    }

    /// End-to-end verdict preservation through the full adaptive portfolio
    /// (which flattens internally): Safe fixtures must not report Unsafe and
    /// the Unsafe fixture must be found.
    #[test]
    fn dtmini_end_to_end_verdicts() {
        let unsafe_verdict = adaptive_verdict(parse(DTMINI_UNSAFE));
        assert!(
            matches!(unsafe_verdict, crate::VerifiedChcResult::Unsafe(_)),
            "dtmini_unsafe end-to-end must be Unsafe, got {unsafe_verdict}"
        );
        for (name, smt) in [("dtmini_safe", DTMINI_SAFE), ("dtmini_safe2", DTMINI_SAFE2)] {
            let verdict = adaptive_verdict(parse(smt));
            assert!(
                !matches!(verdict, crate::VerifiedChcResult::Unsafe(_)),
                "{name} end-to-end must never be Unsafe, got {verdict}"
            );
        }
    }
}
