// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{ChcDtSelector, ChcOp};
use std::sync::Arc;

fn datatype(name: &str, constructor: &str, field: Option<ChcSort>) -> ChcSort {
    ChcSort::Datatype {
        name: name.to_owned(),
        constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
            name: constructor.to_owned(),
            selectors: field
                .into_iter()
                .map(|sort| ChcDtSelector {
                    name: "field".to_owned(),
                    sort,
                })
                .collect(),
        }]),
    }
}

fn array(key: ChcSort, value: ChcSort) -> ChcSort {
    ChcSort::Array(Box::new(key), Box::new(value))
}

#[test]
fn cloned_scalar_and_array_variables_cross_old_sort_charge_without_hiding_occurrences() {
    for (sort, nodes) in [
        (ChcSort::Int, 1),
        (array(ChcSort::BitVec(64), ChcSort::BitVec(8)), 3),
    ] {
        let count = MAX_DT_SORT_NODES / nodes + 1;
        assert!(count < MAX_DT_EXPR_NODES);
        let roots: Vec<_> = (0..count)
            .map(|_| ChcExpr::var(ChcVar::new("x", sort.clone())))
            .collect();
        let mut collector = DatatypeDeclarationCollector::default();
        for root in &roots {
            collector.visit_expr(root).unwrap();
        }
        assert_eq!(collector.sort_nodes, nodes);
        assert_eq!(collector.expr_nodes, count);
        assert_eq!(collector.name_bytes, count);
        assert_eq!(collector.checked_variable_sorts.len(), 1);
        assert_eq!(
            collect_dt_declarations_for_exprs(roots.iter()).unwrap(),
            [] as [(&str, &[ChcDtConstructor]); 0]
        );
    }
}

#[test]
fn distinct_variables_still_pay_the_exact_aggregate_sort_cap() {
    let variables: Vec<_> = (0..=MAX_DT_SORT_NODES)
        .map(|index| ChcVar::new(format!("v{index}"), ChcSort::Int))
        .collect();
    let mut collector = DatatypeDeclarationCollector::default();
    for variable in &variables[..MAX_DT_SORT_NODES] {
        collector.visit_variable(variable).unwrap();
    }
    assert_eq!(collector.sort_nodes, MAX_DT_SORT_NODES);
    assert!(matches!(
        collector.visit_variable(&variables[MAX_DT_SORT_NODES]),
        Err(DatatypeDeclarationError::ResourceLimit(
            "datatype sort nodes"
        ))
    ));
    assert_eq!(collector.checked_variable_sorts.len(), MAX_DT_SORT_NODES);
}

#[test]
fn differing_same_name_sort_shapes_are_checked_not_globally_rejected() {
    let cases = [
        (ChcSort::Int, ChcSort::Bool, 1),
        (ChcSort::BitVec(8), ChcSort::BitVec(16), 1),
        (
            array(ChcSort::Int, ChcSort::Bool),
            array(ChcSort::Bool, ChcSort::Bool),
            3,
        ),
        (
            array(ChcSort::Int, ChcSort::Bool),
            array(ChcSort::Int, ChcSort::Real),
            3,
        ),
        (
            ChcSort::Uninterpreted("U".into()),
            ChcSort::Uninterpreted("V".into()),
            1,
        ),
    ];
    for (left, right, additional) in cases {
        let first = ChcVar::new("x", left);
        let second = ChcVar::new("x", right);
        let mut collector = DatatypeDeclarationCollector::default();
        collector.visit_variable(&first).unwrap();
        let before = collector.sort_nodes;
        collector.visit_variable(&second).unwrap();
        assert_eq!(collector.sort_nodes, before + additional);
        assert!(std::ptr::eq(
            collector.checked_variable_sorts["x"],
            &raw const first.sort
        ));
    }
}

#[test]
fn same_name_nested_conflicts_survive_warm_variable_and_signature_caches_in_both_orders() {
    for (left, right) in [("left", "right"), ("right", "left")] {
        let first = ChcVar::new(
            "x",
            datatype("Outer", "outer", Some(datatype("Inner", left, None))),
        );
        let repeated = first.clone();
        let conflict = ChcVar::new(
            "x",
            datatype("Outer", "outer", Some(datatype("Inner", right, None))),
        );
        let mut collector = DatatypeDeclarationCollector::default();
        collector.visit_variable(&first).unwrap();
        collector.visit_variable(&repeated).unwrap();
        let result = collector.visit_variable(&conflict);
        assert!(
            matches!(result, Err(DatatypeDeclarationError::ConflictingDefinition(name)) if name == "Inner")
        );
        // The outer emitted signature compared equal. That is not authority
        // to skip the new allocation's recursively embedded Inner definition.
        assert_eq!(collector.checked_definition_pairs.len(), 1);
        drop(collector);
        let expressions = [ChcExpr::var(first), ChcExpr::var(conflict)];
        assert!(
            matches!(collect_dt_declarations_for_exprs(expressions.iter()),
            Err(DatatypeDeclarationError::ConflictingDefinition(name)) if name == "Inner")
        );
    }
}

#[test]
fn structurally_equal_definitions_are_one_allocation_and_need_no_comparison() {
    // Constructor lists are hash-consed, so independently built equal
    // definitions share metadata and take the pointer fast path.
    let variables = [
        ChcVar::new("a", datatype("T", "same", Some(ChcSort::Int))),
        ChcVar::new("b", datatype("T", "same", Some(ChcSort::Int))),
    ];
    let mut collector = DatatypeDeclarationCollector::default();
    for variable in &variables {
        collector.visit_variable(variable).unwrap();
    }
    assert_eq!(collector.definition_compare_work, 0);
    assert!(collector.checked_definition_pairs.is_empty());
    assert_eq!(collector.expanded_definition_instances.len(), 1);
}

#[test]
fn completed_definition_pair_comparisons_are_reused_without_deduplicating_variable_occurrences() {
    // Two allocations with one emitted signature: a finite-resolution
    // snapshot that cuts the field to its bare name, and one that carries it.
    let canonical = datatype(
        "T",
        "constructor-with-a-long-surface-name",
        Some(ChcSort::Uninterpreted("U".into())),
    );
    let equivalent = datatype(
        "T",
        "constructor-with-a-long-surface-name",
        Some(datatype("U", "u", None)),
    );
    let variables: Vec<_> = (0..20)
        .map(|index| {
            ChcVar::new(
                format!("v{index}"),
                if index == 0 {
                    canonical.clone()
                } else {
                    equivalent.clone()
                },
            )
        })
        .collect();
    let mut collector = DatatypeDeclarationCollector::default();
    collector.visit_variable(&variables[0]).unwrap();
    collector.visit_variable(&variables[1]).unwrap();
    let completed_work = collector.definition_compare_work;
    assert!(completed_work > 0);
    assert_eq!(collector.checked_definition_pairs.len(), 1);
    let expanded = collector.expanded_definition_instances.len();
    for variable in &variables[2..] {
        collector.visit_variable(variable).unwrap();
    }
    assert_eq!(collector.definition_compare_work, completed_work);
    assert_eq!(collector.expanded_definition_instances.len(), expanded);
    assert_eq!(collector.checked_variable_sorts.len(), variables.len());
    assert_eq!(collector.sort_nodes, variables.len() + 2);
}

#[test]
fn new_conflicting_metadata_is_not_a_completed_pair_hit() {
    // `a` and `b` are distinct allocations with one emitted signature (see
    // the snapshot fixture above); equal lists would share one allocation.
    let variables = [
        ChcVar::new(
            "a",
            datatype("T", "old", Some(ChcSort::Uninterpreted("U".into()))),
        ),
        ChcVar::new("b", datatype("T", "old", Some(datatype("U", "u", None)))),
        ChcVar::new("c", datatype("T", "new", None)),
    ];
    let mut collector = DatatypeDeclarationCollector::default();
    collector.visit_variable(&variables[0]).unwrap();
    collector.visit_variable(&variables[1]).unwrap();
    assert_eq!(collector.checked_definition_pairs.len(), 1);
    assert!(matches!(collector.visit_variable(&variables[2]),
        Err(DatatypeDeclarationError::ConflictingDefinition(name)) if name == "T"));
    assert_eq!(collector.checked_definition_pairs.len(), 1);
    let mut limited = DatatypeDeclarationCollector::default();
    limited.visit_variable(&variables[0]).unwrap();
    limited.definition_compare_work = MAX_DT_DEFINITION_COMPARE_WORK;
    assert!(matches!(
        limited.visit_variable(&variables[1]),
        Err(DatatypeDeclarationError::ResourceLimit(
            "datatype definition comparison"
        ))
    ));
    assert!(limited.checked_definition_pairs.is_empty());
}

#[test]
fn shared_metadata_with_different_datatype_names_and_placeholders_is_not_a_variable_hit() {
    let original = datatype("A", "shared", None);
    let ChcSort::Datatype { constructors, .. } = &original else {
        unreachable!()
    };
    let renamed = ChcSort::Datatype {
        name: "B".into(),
        constructors: constructors.clone(),
    };
    let variables = [
        ChcVar::new("x", original.clone()),
        ChcVar::new("x", renamed),
    ];
    let mut collector = DatatypeDeclarationCollector::default();
    for variable in &variables {
        collector.visit_variable(variable).unwrap();
    }
    assert_eq!(collector.definitions.len(), 2);
    assert_eq!(collector.sort_nodes, 2);
    assert_eq!(collector.expanded_definition_instances.len(), 1);

    let placeholder = ChcVar::new("x", ChcSort::Uninterpreted("A".into()));
    let concrete = ChcVar::new("x", original);
    let mut collector = DatatypeDeclarationCollector::default();
    collector.visit_variable(&placeholder).unwrap();
    collector.visit_variable(&concrete).unwrap();
    assert_eq!(collector.definitions.len(), 1);
    assert_eq!(collector.sort_nodes, 2);
}

/// `List = nil | cons (head: <head>, tail: <tail>)`. Lists are interned, so
/// equal calls share one allocation and different ones never do.
fn list(head: ChcSort, tail: ChcSort) -> ChcSort {
    ChcSort::Datatype {
        name: "List".to_owned(),
        constructors: crate::ChcDtConstructors::new(vec![
            ChcDtConstructor {
                name: "nil".to_owned(),
                selectors: Vec::new(),
            },
            ChcDtConstructor {
                name: "cons".to_owned(),
                selectors: vec![
                    ChcDtSelector {
                        name: "head".to_owned(),
                        sort: head,
                    },
                    ChcDtSelector {
                        name: "tail".to_owned(),
                        sort: tail,
                    },
                ],
            },
        ]),
    }
}

#[test]
fn self_recursive_snapshots_with_fresh_tail_metadata_are_compared_not_cached() {
    // The second occurrence of `x` carries a different allocation of the same
    // recursive definition, unfolded one level deeper. The variable cache is
    // keyed on metadata identity, so it misses and the collector compares:
    // the equal unfolding is one definition, and a forgery hidden inside the
    // unfolded tail (whose outer emitted signature compares equal nominally)
    // is still a conflict.
    let shallow = list(ChcSort::Int, ChcSort::Uninterpreted("List".into()));
    let unfolded = list(
        ChcSort::Int,
        list(ChcSort::Int, ChcSort::Uninterpreted("List".into())),
    );
    let forged = list(
        ChcSort::Int,
        list(ChcSort::Bool, ChcSort::Uninterpreted("List".into())),
    );
    let first = ChcVar::new("x", shallow);
    let second = ChcVar::new("x", unfolded.clone());
    let third = ChcVar::new("x", forged.clone());
    let mut collector = DatatypeDeclarationCollector::default();
    collector.visit_variable(&first).unwrap();
    let before = collector.sort_nodes;
    collector.visit_variable(&second).unwrap();
    assert!(
        collector.sort_nodes > before,
        "a different allocation is walked"
    );
    assert_eq!(collector.definitions.len(), 1);
    assert!(std::ptr::eq(
        collector.checked_variable_sorts["x"],
        &raw const first.sort
    ));
    assert!(matches!(
        collector.visit_variable(&third),
        Err(DatatypeDeclarationError::ConflictingDefinition(name)) if name == "List"
    ));
    drop(collector);

    let expressions = [
        ChcExpr::var(first.clone()),
        ChcExpr::var(ChcVar::new("y", unfolded)),
    ];
    let declarations = collect_dt_declarations_for_exprs(expressions.iter()).unwrap();
    assert_eq!(declarations.len(), 1);
    let expressions = [ChcExpr::var(first), ChcExpr::var(ChcVar::new("y", forged))];
    assert!(matches!(
        collect_dt_declarations_for_exprs(expressions.iter()),
        Err(DatatypeDeclarationError::ConflictingDefinition(name)) if name == "List"
    ));
}

#[test]
fn finite_recursive_snapshots_still_expand_new_nested_definitions() {
    let unresolved_a = datatype("A", "a", Some(ChcSort::Uninterpreted("B".into())));
    let resolved_b = datatype("B", "b", Some(unresolved_a.clone()));
    let resolved_a = datatype("A", "a", Some(resolved_b));
    let variables = [ChcVar::new("x", unresolved_a), ChcVar::new("x", resolved_a)];
    let declarations = collect_dt_declarations(&variables).unwrap();
    assert_eq!(
        declarations
            .iter()
            .map(|(name, _)| *name)
            .collect::<Vec<_>>(),
        ["A", "B"]
    );
    assert!(emit_declare_datatypes(&declarations).is_ok());
}

#[test]
fn cache_hits_keep_name_and_expression_occurrence_limits() {
    let variable = ChcVar::new("name", ChcSort::Int);
    let expression = ChcExpr::var(variable.clone());
    let mut collector = DatatypeDeclarationCollector::default();
    collector.visit_variable(&variable).unwrap();
    collector.name_bytes = MAX_DT_NAME_BYTES - variable.name.len();
    collector.visit_variable(&variable).unwrap();
    assert_eq!(collector.name_bytes, MAX_DT_NAME_BYTES);
    assert!(matches!(
        collector.visit_variable(&variable),
        Err(DatatypeDeclarationError::ResourceLimit(
            "executor surface name bytes"
        ))
    ));

    // Distinct nodes are charged one each (bridge item D-1 counts UNIQUE
    // nodes; the same node met again is not re-charged, see below).
    let occurrences = [expression.clone(), expression.clone(), expression.clone()];
    let mut collector = DatatypeDeclarationCollector::default();
    collector.visit_expr(&occurrences[0]).unwrap();
    collector.expr_nodes = MAX_DT_EXPR_NODES - 1;
    collector.visit_expr(&occurrences[1]).unwrap();
    assert!(matches!(
        collector.visit_expr(&occurrences[2]),
        Err(DatatypeDeclarationError::ResourceLimit(
            "datatype expression nodes"
        ))
    ));
}

// ---------------------------------------------------------------------------
// Bridge item D-1 (CHC-COMP 2026 Workstream D): unique-node admission
// ---------------------------------------------------------------------------

fn int_var(name: &str) -> Arc<ChcExpr> {
    Arc::new(ChcExpr::var(ChcVar::new(name, ChcSort::Int)))
}

/// e_{i+1} = (+ e_i e_i): a tree of 2^(levels+1) - 1 nodes that is a DAG of
/// levels + 1 nodes.
fn doubling_chain(levels: usize) -> Arc<ChcExpr> {
    let mut e = int_var("x");
    for _ in 0..levels {
        e = Arc::new(ChcExpr::Op(
            ChcOp::Add,
            vec![Arc::clone(&e), Arc::clone(&e)],
        ));
    }
    e
}

#[test]
fn admission_counts_unique_nodes_of_a_shared_dag() {
    // 2^20 leaves in the tree, 21 distinct nodes: admitted, with the tree
    // expansion measured exactly.
    let sum = doubling_chain(20);
    let root = ChcExpr::le(ChcExpr::Int(0), (*sum).clone());
    let (_, sizes) = collect_dt_declarations_for_expr_sized(&[], &root).unwrap();
    assert_eq!(sizes.unique_nodes, 23);
    assert_eq!(sizes.tree_nodes, (1 << 21) - 1 + 2);
    // The same node reached again is charged once, never re-expanded.
    let mut collector = DatatypeDeclarationCollector::default();
    collector.visit_expr(&sum).unwrap();
    collector.visit_expr(&sum).unwrap();
    assert_eq!(collector.expr_nodes, 21);
    assert_eq!(collector.tree_nodes, 2 * ((1 << 21) - 1));
}

#[test]
fn admission_still_refuses_a_deep_chain_and_a_huge_tree() {
    let mut deep = int_var("y");
    for _ in 0..=MAX_DT_NESTING_DEPTH {
        deep = Arc::new(ChcExpr::Op(ChcOp::Neg, vec![deep]));
    }
    assert!(matches!(
        collect_dt_declarations_for_expr(&[], &deep),
        Err(DatatypeDeclarationError::ResourceLimit(
            "datatype expression nesting depth"
        ))
    ));
    // Depth stays exact through sharing: a node first met shallowly and
    // later under a longer path is charged at the longer one.
    let shared = doubling_chain(8);
    let mut long = Arc::clone(&shared);
    for _ in 0..(MAX_DT_NESTING_DEPTH - 9) {
        long = Arc::new(ChcExpr::Op(ChcOp::Neg, vec![long]));
    }
    let at_cap = ChcExpr::Op(ChcOp::Eq, vec![Arc::clone(&shared), Arc::clone(&long)]);
    assert!(collect_dt_declarations_for_expr(&[], &at_cap).is_ok());
    let over = ChcExpr::Op(
        ChcOp::Eq,
        vec![shared, Arc::new(ChcExpr::Op(ChcOp::Neg, vec![long]))],
    );
    assert!(matches!(
        collect_dt_declarations_for_expr(&[], &over),
        Err(DatatypeDeclarationError::ResourceLimit(
            "datatype expression nesting depth"
        ))
    ));
    // 2^23 - 1 tree nodes from 23 distinct nodes: the tree cap guards the
    // unmemoised helpers that run after admission.
    let huge = doubling_chain(22);
    assert!(matches!(
        collect_dt_declarations_for_expr(&[], &huge),
        Err(DatatypeDeclarationError::ResourceLimit(
            "executor expression tree nodes"
        ))
    ));
}

#[test]
fn small_trees_take_the_plain_walk_and_large_trees_the_dag_walk() {
    // `le(0, doubling_chain(n))` has 2^(n+1) + 1 tree nodes over n + 3
    // distinct nodes. At or below DAG_WALK_MIN_TREE_NODES the plain walk
    // charges occurrences (unique == tree); above it the D-1 walk charges
    // distinct nodes. Tree size is exact on both paths.
    let small = ChcExpr::le(ChcExpr::Int(0), (*doubling_chain(10)).clone());
    let (_, sizes) = collect_dt_declarations_for_expr_sized(&[], &small).unwrap();
    assert_eq!(sizes.tree_nodes, (1 << 11) + 1);
    assert!(sizes.tree_nodes <= DAG_WALK_MIN_TREE_NODES);
    assert_eq!(sizes.unique_nodes, sizes.tree_nodes);
    let large = ChcExpr::le(ChcExpr::Int(0), (*doubling_chain(11)).clone());
    let (_, sizes) = collect_dt_declarations_for_expr_sized(&[], &large).unwrap();
    assert_eq!(sizes.tree_nodes, (1 << 12) + 1);
    assert!(sizes.tree_nodes > DAG_WALK_MIN_TREE_NODES);
    assert_eq!(sizes.unique_nodes, 11 + 3);
    // The sort scans agree across the threshold.
    for root in [&small, &large] {
        assert!(expr_sort_has(root, |sort| matches!(sort, ChcSort::Int)));
        assert!(!expr_sort_has(root, |sort| matches!(sort, ChcSort::Real)));
        assert_eq!(
            expr_sort_has(root, sort_contains_int),
            expr_sort_has_dag(root, sort_contains_int)
        );
    }
}

#[test]
fn tree_cap_binds_executor_admission_but_not_the_uf_surface_walk() {
    // Merge of bridge item D-1 with WP-F (batch 3): the tree cap guards the
    // executor's tree printers, so it binds the single-query admission; the
    // multi-root walk behind `ChcProblem::validate` / the UF surface prints
    // nothing and must stay DAG-linear however large the tree is.
    let huge = doubling_chain(22);
    let root = ChcExpr::le(ChcExpr::Int(0), (*huge).clone());
    assert!(matches!(
        collect_dt_declarations_for_expr(&[], &root),
        Err(DatatypeDeclarationError::ResourceLimit(
            "executor expression tree nodes"
        ))
    ));
    assert!(collect_dt_declarations_for_exprs([&root, &root]).is_ok());
    assert_eq!(
        collect_uninterpreted_function_declarations(&root).unwrap(),
        [] as [UninterpretedFunctionDeclaration; 0]
    );
}

#[test]
fn uf_surface_and_sort_scans_walk_each_distinct_node_once() {
    // 2^20-leaf tree over a 21-node DAG: both scans used to refuse it at the
    // tree cap; they now finish and agree with a structural answer.
    let sum = doubling_chain(20);
    let root = ChcExpr::le(ChcExpr::Int(0), (*sum).clone());
    assert_eq!(
        collect_uninterpreted_function_declarations(&root).unwrap(),
        [] as [UninterpretedFunctionDeclaration; 0]
    );
    assert!(expr_sort_has(&root, |sort| matches!(sort, ChcSort::Int)));
    assert!(!expr_sort_has(&root, |sort| matches!(sort, ChcSort::Real)));
    assert_eq!(
        detect_logic(&[ChcVar::new("x", ChcSort::Int)], &root),
        "QF_AUFLIA"
    );
}

#[test]
fn long_shared_metadata_names_keep_the_existing_name_byte_envelope() {
    let name = "T".repeat(128);
    let sort = datatype(&name, "c", None);
    let count = MAX_DT_DEFINITION_COMPARE_WORK / name.len() + 1;
    let variables: Vec<_> = (0..count).map(|_| ChcVar::new("x", sort.clone())).collect();
    let mut collector = DatatypeDeclarationCollector::default();
    for variable in &variables {
        collector.visit_variable(variable).unwrap();
    }
    assert_eq!(collector.sort_nodes, 1);
    assert_eq!(collector.variable_sort_compare_work, count - 1);
    assert_eq!(collector.name_bytes, count * (name.len() + 1) + 1);
    assert!(collector.name_bytes > MAX_DT_DEFINITION_COMPARE_WORK);
    assert!(collector.name_bytes < MAX_DT_NAME_BYTES);
}

#[test]
fn identity_comparison_and_failed_first_admission_are_bounded() {
    let left = array(ChcSort::Int, ChcSort::Bool);
    let right = left.clone();
    let mut exact = MAX_DT_DEFINITION_COMPARE_WORK - 3;
    let mut names = 0;
    assert!(variable_sorts::same_metadata_shape(
        &left,
        &right,
        &mut exact,
        &mut names,
        EXECUTOR_QUERY_LIMITS
    )
    .unwrap());
    assert_eq!(exact, MAX_DT_DEFINITION_COMPARE_WORK);
    let mut short = MAX_DT_DEFINITION_COMPARE_WORK - 2;
    assert!(matches!(
        variable_sorts::same_metadata_shape(
            &left,
            &right,
            &mut short,
            &mut names,
            EXECUTOR_QUERY_LIMITS
        ),
        Err(DatatypeDeclarationError::ResourceLimit(
            "variable sort comparison"
        ))
    ));

    let mut deep = ChcSort::Int;
    for _ in 0..=MAX_DT_NESTING_DEPTH {
        deep = array(ChcSort::Bool, deep);
    }
    let variable = ChcVar::new("deep", deep);
    let mut collector = DatatypeDeclarationCollector::default();
    assert!(collector.visit_variable(&variable).is_err());
    assert!(collector.checked_variable_sorts.is_empty());
    let healthy = ChcVar::new("deep", ChcSort::Int);
    DatatypeDeclarationCollector::default()
        .visit_variable(&healthy)
        .unwrap();
}

/// `Level = zero | succ (pred: Level)`, optionally with a third nullary
/// constructor `extra`. Lists are interned: equal calls share one allocation.
fn level(extra: bool) -> ChcSort {
    let mut ctors = vec![
        ChcDtConstructor {
            name: "zero".to_owned(),
            selectors: Vec::new(),
        },
        ChcDtConstructor {
            name: "succ".to_owned(),
            selectors: vec![ChcDtSelector {
                name: "pred".to_owned(),
                sort: ChcSort::Uninterpreted("Level".into()),
            }],
        },
    ];
    if extra {
        ctors.push(ChcDtConstructor {
            name: "extra".to_owned(),
            selectors: Vec::new(),
        });
    }
    ChcSort::Datatype {
        name: "Level".to_owned(),
        constructors: crate::ChcDtConstructors::new(ctors),
    }
}

#[test]
fn admission_is_per_call_and_same_named_definitions_conflict_within_one_call() {
    // One call admits `Level`; a separate call carrying a different `Level`
    // is admitted on its own terms, not from any cache. Within ONE call the
    // two conflict regardless of order, and regardless of a same-name
    // variable having been cached first.
    let q1 = [ChcExpr::var(ChcVar::new("x", level(false)))];
    let d1 = collect_dt_declarations_for_exprs(q1.iter()).unwrap();
    assert_eq!(d1.len(), 1);
    let q2 = [ChcExpr::var(ChcVar::new("x", level(true)))];
    let d2 = collect_dt_declarations_for_exprs(q2.iter()).unwrap();
    assert_eq!(d2.len(), 1);
    assert_ne!(format!("{d1:?}"), format!("{d2:?}"));
    for (a, b) in [(false, true), (true, false)] {
        let q = [
            ChcExpr::var(ChcVar::new("x", level(a))),
            ChcExpr::var(ChcVar::new("x", level(a))),
            ChcExpr::var(ChcVar::new("x", level(b))),
        ];
        assert!(matches!(
            collect_dt_declarations_for_exprs(q.iter()),
            Err(DatatypeDeclarationError::ConflictingDefinition(n)) if n == "Level"
        ));
        let q = [
            ChcExpr::var(ChcVar::new("x", level(a))),
            ChcExpr::var(ChcVar::new("y", level(b))),
        ];
        assert!(matches!(
            collect_dt_declarations_for_exprs(q.iter()),
            Err(DatatypeDeclarationError::ConflictingDefinition(n)) if n == "Level"
        ));
    }
    // A same-name variable whose SHARED metadata is the same Arc but whose
    // datatype name differs is not a cache hit either.
    let shared = level(false);
    let ChcSort::Datatype { constructors, .. } = &shared else {
        panic!()
    };
    let renamed = ChcSort::Datatype {
        name: "Other".to_owned(),
        constructors: constructors.clone(),
    };
    let q = [
        ChcExpr::var(ChcVar::new("x", shared.clone())),
        ChcExpr::var(ChcVar::new("x", renamed)),
    ];
    let d = collect_dt_declarations_for_exprs(q.iter()).unwrap();
    assert_eq!(d.len(), 2, "{d:?}");
}
