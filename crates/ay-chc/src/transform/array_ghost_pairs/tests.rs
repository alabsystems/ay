// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tests for the FORALL-ARR ghost-pair transformer and its quantified
//! certification (agenda #16).

use std::time::Duration;

use super::certify::{bounded_executor_budget, per_rule_budget};
use super::{
    clause_has_symbolic_index, collect_index_terms, instantiation_tuples,
    ArrayGhostPairTransformer, GhostPairCertificate, GhostPairSpec, BODY_INSTANCE_CAP,
};
use crate::pdr::{InvariantModel, PredicateInterpretation};
use crate::transform::{recheck_ghost_pair_certificate, Transformer};
use crate::{
    ChcExpr, ChcProblem, ChcReplayObligationKind, ChcSort, ChcVar, ClauseBody, ClauseHead,
    HornClause, PredicateId,
};

fn int_array_sort() -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int))
}

fn bv_array_sort(index_width: u32, value_sort: ChcSort) -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::BitVec(index_width)), Box::new(value_sort))
}

fn var(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, sort))
}

/// `P(a : Array Int Int, n : Int)` with:
/// - init:  `P(const0, 0)`
/// - trans: `P(a, n) /\ a' = store(a, n, 0)  =>  P(a', n + 1)`
/// - query: `P(a, n) /\ 0 <= q /\ select(a, q) != 0  =>  false`
///
/// Safe; the (necessarily quantified) invariant is `forall i. a[i] = 0`.
fn const_zero_array_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![int_array_sort(), ChcSort::Int]);

    // init: true => P(const0, 0)
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(
            p,
            vec![
                ChcExpr::const_array(ChcSort::Int, ChcExpr::Int(0)),
                ChcExpr::Int(0),
            ],
        ),
    ));

    // trans: P(a, n) /\ a2 = store(a, n, 0) => P(a2, n + 1)
    let a = var("a", int_array_sort());
    let a2 = var("a2", int_array_sort());
    let n = var("n", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![a.clone(), n.clone()])],
            Some(ChcExpr::eq(
                a2.clone(),
                ChcExpr::store(a.clone(), n.clone(), ChcExpr::Int(0)),
            )),
        ),
        ClauseHead::Predicate(p, vec![a2, ChcExpr::add(n, ChcExpr::Int(1))]),
    ));

    // query: P(a, n) /\ 0 <= q /\ select(a, q) != 0 => false
    let a = var("a", int_array_sort());
    let n = var("n", ChcSort::Int);
    let q = var("q", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![a.clone(), n])],
            Some(ChcExpr::and(
                ChcExpr::le(ChcExpr::Int(0), q.clone()),
                ChcExpr::ne(ChcExpr::select(a, q), ChcExpr::Int(0)),
            )),
        ),
        ClauseHead::False,
    ));

    problem
}

#[test]
fn transform_accepts_unused_datatype_prelude_and_preserves_metadata() {
    let mut problem = const_zero_array_problem();
    problem.mark_stripped_body_forall();
    problem.add_datatype_def(
        "UnusedModelCheckerConsumerBox".to_string(),
        vec![(
            "unused-model-checker-consumer-box".to_string(),
            vec![(
                "unused-model-checker-consumer-value".to_string(),
                ChcSort::Int,
            )],
        )],
    );
    let initialize = problem.declare_action("Initialize");
    let step = problem.declare_action("Step");
    for (index, clause) in problem.clauses_mut().iter_mut().enumerate() {
        clause.action_id = Some(if index == 0 { initialize } else { step });
    }

    assert!(
        !problem.uses_datatype_features(),
        "a declaration-only datatype prelude must remain semantically inactive"
    );
    let original_datatypes = problem.datatype_defs().clone();
    let original_action_names = problem.action_names().to_vec();
    let original_action_ids: Vec<_> = problem
        .clauses()
        .iter()
        .map(|clause| clause.action_id)
        .collect();

    let transformed = Box::new(ArrayGhostPairTransformer::new(1))
        .transform(problem)
        .problem;

    assert_eq!(
        transformed.predicates()[0].arg_sorts.len(),
        4,
        "the unused prelude must not turn ghost instrumentation into identity"
    );
    assert_eq!(transformed.datatype_defs(), &original_datatypes);
    assert_eq!(transformed.action_names(), original_action_names.as_slice());
    assert!(
        transformed.has_stripped_body_forall(),
        "the rebuilt problem must retain the unsafe-result downgrade marker"
    );
    assert_eq!(
        transformed
            .clauses()
            .iter()
            .map(|clause| clause.action_id)
            .collect::<Vec<_>>(),
        original_action_ids,
        "the rebuilt action table and positional clause ids must agree exactly"
    );
}

#[test]
fn transform_is_identity_when_a_datatype_is_actively_used() {
    let mut problem = const_zero_array_problem();
    let constructors = std::sync::Arc::new(vec![crate::ChcDtConstructor {
        name: "active-model-checker-consumer-box".to_string(),
        selectors: vec![crate::ChcDtSelector {
            name: "active-model-checker-consumer-value".to_string(),
            sort: ChcSort::Int,
        }],
    }]);
    let datatype_sort = ChcSort::Datatype {
        name: "ActiveModelCheckerConsumerBox".to_string(),
        constructors,
    };
    problem.add_datatype_def(
        "ActiveModelCheckerConsumerBox".to_string(),
        vec![(
            "active-model-checker-consumer-box".to_string(),
            vec![(
                "active-model-checker-consumer-value".to_string(),
                ChcSort::Int,
            )],
        )],
    );
    let left = ChcVar::new("active_left", datatype_sort.clone());
    let right = ChcVar::new("active_right", datatype_sort);
    problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::eq(
        ChcExpr::var(left),
        ChcExpr::var(right),
    ))));

    assert!(problem.uses_datatype_features());
    assert!(
        !GhostPairSpec::analyze(&problem, 1).is_empty(),
        "the array surface must otherwise qualify for instrumentation"
    );
    let original_clause_count = problem.clauses().len();

    let transformed = Box::new(ArrayGhostPairTransformer::new(1))
        .transform(problem)
        .problem;

    assert_eq!(transformed.predicates()[0].arg_sorts.len(), 2);
    assert_eq!(transformed.clauses().len(), original_clause_count);
    assert!(transformed.uses_datatype_features());
}

/// The quantified model `forall i. a[i] = 0`, expressed as the ghost model
/// `I'(a, n, idx, val) := val = 0` over the n=1 transformed signature.
fn val_is_zero_ghost_model(p: PredicateId) -> InvariantModel {
    let vars = vec![
        ChcVar::new(format!("__p{}_a0", p.index()), int_array_sort()),
        ChcVar::new(format!("__p{}_a1", p.index()), ChcSort::Int),
        ChcVar::new(format!("__p{}_a2", p.index()), ChcSort::Int),
        ChcVar::new(format!("__p{}_a3", p.index()), ChcSort::Int),
    ];
    let formula = ChcExpr::eq(ChcExpr::var(vars[3].clone()), ChcExpr::Int(0));
    let mut model = InvariantModel::new();
    model.set(p, PredicateInterpretation::new(vars, formula));
    model
}

/// A BV-indexed constant-zero array whose safety requires a quantified cell
/// invariant. The identity transition keeps the fixture focused on typed
/// transformation and certificate/replay plumbing.
fn bv_indexed_const_zero_problem(width: u32) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let array_sort = bv_array_sort(width, ChcSort::Int);
    let p = problem.declare_predicate("P", vec![array_sort.clone()]);
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(
            p,
            vec![ChcExpr::const_array(
                ChcSort::BitVec(width),
                ChcExpr::Int(0),
            )],
        ),
    ));
    let array = var("array", array_sort.clone());
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![array.clone()])], None),
        ClauseHead::Predicate(p, vec![array]),
    ));
    let array = var("array", array_sort);
    let index = var("index", ChcSort::BitVec(width));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![array.clone()])],
        Some(ChcExpr::ne(ChcExpr::select(array, index), ChcExpr::Int(0))),
    )));
    problem
}

fn bv_val_is_zero_ghost_model(p: PredicateId, width: u32) -> InvariantModel {
    let vars = vec![
        ChcVar::new(
            format!("__p{}_a0", p.index()),
            bv_array_sort(width, ChcSort::Int),
        ),
        ChcVar::new(format!("__p{}_a1", p.index()), ChcSort::BitVec(width)),
        ChcVar::new(format!("__p{}_a2", p.index()), ChcSort::Int),
    ];
    let formula = ChcExpr::eq(ChcExpr::var(vars[2].clone()), ChcExpr::Int(0));
    let mut model = InvariantModel::new();
    model.set(p, PredicateInterpretation::new(vars, formula));
    model
}

fn opaque_cell_problem_and_model(sort_name: &str) -> (ChcProblem, InvariantModel) {
    let mut problem = ChcProblem::new();
    let value_sort = ChcSort::Uninterpreted(sort_name.to_string());
    let array_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(value_sort.clone()));
    let p = problem.declare_predicate("P", vec![array_sort.clone(), value_sort.clone()]);
    let source_value = ChcExpr::FuncApp("opaque_value".to_string(), value_sort.clone(), vec![]);
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(
            p,
            vec![
                ChcExpr::const_array(ChcSort::Int, source_value.clone()),
                source_value.clone(),
            ],
        ),
    ));
    let array = var("array", array_sort.clone());
    let index = var("index", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![array.clone(), source_value.clone()])],
        Some(ChcExpr::ne(ChcExpr::select(array, index), source_value)),
    )));

    let params = vec![
        ChcVar::new("array_param", array_sort),
        ChcVar::new("scalar_param", value_sort.clone()),
        ChcVar::new("ghost_index", ChcSort::Int),
        ChcVar::new("ghost_value", value_sort),
    ];
    let formula = ChcExpr::eq(
        ChcExpr::var(params[3].clone()),
        ChcExpr::var(params[1].clone()),
    );
    let mut model = InvariantModel::new();
    model.set(p, PredicateInterpretation::new(params, formula));
    (problem, model)
}

#[test]
fn spec_analyzes_int_and_bounded_bv_indexed_array_arguments() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![int_array_sort(), ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int, ChcSort::Bool]);
    let r = problem.declare_predicate(
        "R",
        vec![ChcSort::Array(
            Box::new(ChcSort::Bool),
            Box::new(ChcSort::Int),
        )],
    );
    let bv32 = problem.declare_predicate("Bv32", vec![bv_array_sort(32, ChcSort::Bool)]);
    let bv64 = problem.declare_predicate("Bv64", vec![bv_array_sort(64, ChcSort::BitVec(8))]);
    let bv65 = problem.declare_predicate("Bv65", vec![bv_array_sort(65, ChcSort::Bool)]);

    let spec = GhostPairSpec::analyze(&problem, 1);
    assert_eq!(spec.preds.get(&p).unwrap().array_positions, vec![0]);
    assert!(!spec.preds.contains_key(&q), "no array args");
    assert_eq!(
        spec.preds.get(&bv32).unwrap().index_sorts,
        vec![ChcSort::BitVec(32)]
    );
    assert_eq!(
        spec.preds.get(&bv64).unwrap().index_sorts,
        vec![ChcSort::BitVec(64)]
    );
    assert!(
        !spec.preds.contains_key(&r),
        "Bool-indexed arrays are not instrumented"
    );
    assert!(
        !spec.preds.contains_key(&bv65),
        "the bounded route must fail closed above BV64"
    );
    assert_eq!(
        GhostPairSpec::analyze(&problem, 0).n,
        1,
        "zero requested pairs must clamp to the transformer's n=1 minimum"
    );
}

#[test]
fn spec_instruments_five_arrays_at_n1_but_skips_ten_slots_at_n2() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![int_array_sort(); 5]);

    let one_pair = GhostPairSpec::analyze(&problem, 1);
    assert_eq!(
        one_pair.preds.get(&p).unwrap().array_positions,
        vec![0, 1, 2, 3, 4],
        "five-array invariants need one independently indexed value per array"
    );

    let two_pairs = GhostPairSpec::analyze(&problem, 2);
    assert!(
        !two_pairs.preds.contains_key(&p),
        "ten ghost slots exceed the bounded abstraction budget"
    );
}

#[test]
fn transformer_extends_signatures_and_preserves_predicate_ids() {
    let problem = const_zero_array_problem();
    let original_pred = problem.predicates()[0].clone();

    let result = Box::new(ArrayGhostPairTransformer::new(1)).transform(problem);
    let transformed = &result.problem;

    let pred = &transformed.predicates()[0];
    assert_eq!(pred.id, original_pred.id, "predicate ids preserved");
    assert_eq!(
        pred.arg_sorts,
        vec![int_array_sort(), ChcSort::Int, ChcSort::Int, ChcSort::Int],
        "one (idx, val) ghost pair appended"
    );

    // Every head occurrence carries fresh ghost variables coupled to the
    // array through a `val = select(arr, idx)` conjunct in the constraint.
    for clause in transformed.clauses() {
        if let ClauseHead::Predicate(_, args) = &clause.head {
            assert_eq!(args.len(), 4);
            let idx = &args[2];
            let val = &args[3];
            assert!(matches!(idx, ChcExpr::Var(v) if v.name.starts_with("__gpi")));
            assert!(matches!(val, ChcExpr::Var(v) if v.name.starts_with("__gpv")));
            let expected_coupling =
                ChcExpr::eq(val.clone(), ChcExpr::select(args[0].clone(), idx.clone()));
            let constraint = clause
                .body
                .constraint
                .as_ref()
                .expect("ghost head clause must carry a coupling constraint");
            assert!(
                constraint
                    .conjuncts()
                    .iter()
                    .any(|c| **c == expected_coupling),
                "coupling conjunct `val = select(arr, idx)` missing from {constraint}"
            );
        }
        // Body atoms are instantiated copies with full ghost arity.
        for (_, args) in &clause.body.predicates {
            assert_eq!(args.len(), 4);
        }
    }

    // LINEARITY PIN: each original body atom maps to exactly ONE instantiated
    // copy — multiple copies of the same predicate would make the clause
    // nonlinear, which the PDR core cannot push lemmas through (it stalls at
    // frame 1 and the lane never fires).
    let transition = &transformed.clauses()[1];
    assert_eq!(
        transition.body.predicates.len(),
        1,
        "expected exactly one (pass-through) body instantiation, got {}",
        transition.body.predicates.len()
    );
    // The pass-through instance probes the head's fresh ghost index.
    if let ClauseHead::Predicate(_, head_args) = &transition.head {
        let (_, body_args) = &transition.body.predicates[0];
        assert_eq!(
            body_args[2], head_args[2],
            "body ghost index must pass through to the head ghost index"
        );
    }
}

#[test]
fn transformer_reserves_source_uf_names_before_allocating_ghosts() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![int_array_sort()]);
    let array = var("array", int_array_sort());
    let index_uf = ChcExpr::FuncApp("__gpi0".to_string(), ChcSort::Int, vec![]);
    let value_uf = ChcExpr::FuncApp("__gpv0".to_string(), ChcSort::Int, vec![]);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(index_uf, value_uf)),
        ClauseHead::Predicate(p, vec![array]),
    ));

    let transformed = Box::new(ArrayGhostPairTransformer::new(1)).transform(problem);
    let ClauseHead::Predicate(_, args) = &transformed.problem.clauses()[0].head else {
        panic!("expected predicate head");
    };
    assert!(matches!(&args[1], ChcExpr::Var(var) if var.name != "__gpi0"));
    assert!(matches!(&args[2], ChcExpr::Var(var) if var.name != "__gpv0"));
}

#[test]
fn transformer_fails_closed_when_source_variable_discovery_exhausts_depth() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![int_array_sort()]);
    let mut deep_index = var("__gpi0", ChcSort::Int);
    for _ in 0..crate::expr::MAX_EXPR_RECURSION_DEPTH + 8 {
        deep_index = ChcExpr::add(deep_index, ChcExpr::Int(0));
    }
    let array = var("array", int_array_sort());
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(p, vec![ChcExpr::store(array, deep_index, ChcExpr::Int(0))]),
    ));

    let result = Box::new(ArrayGhostPairTransformer::new(1)).transform(problem);
    assert_eq!(result.problem.predicates()[0].arity(), 1);
    assert!(result
        .back_translator
        .transform_memory()
        .is_identity_grade());
}

#[test]
fn transformer_preserves_heterogeneous_model_checker_consumer_key_and_value_sorts() {
    let mut problem = ChcProblem::new();
    let valid_sort = bv_array_sort(32, ChcSort::Bool);
    let size_sort = bv_array_sort(32, ChcSort::BitVec(32));
    let memory_sort = bv_array_sort(64, ChcSort::BitVec(8));
    let p = problem.declare_predicate(
        "Heap",
        vec![valid_sort.clone(), size_sort.clone(), memory_sort.clone()],
    );
    let valid = var("valid", valid_sort);
    let sizes = var("sizes", size_sort);
    let memory = var("memory", memory_sort);
    let object = var("object", ChcSort::BitVec(32));
    let size_object = var("size_object", ChcSort::BitVec(32));
    let address = var("address", ChcSort::BitVec(64));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![valid.clone(), sizes.clone(), memory.clone()])],
        Some(ChcExpr::and_all(vec![
            ChcExpr::select(valid, object.clone()),
            ChcExpr::eq(
                ChcExpr::select(sizes, size_object.clone()),
                ChcExpr::BitVec(1, 32),
            ),
            ChcExpr::eq(
                ChcExpr::select(memory, address.clone()),
                ChcExpr::BitVec(0x42, 8),
            ),
        ])),
    )));

    let transformed = Box::new(ArrayGhostPairTransformer::new(1)).transform(problem);
    assert_eq!(
        transformed.problem.predicates()[0].arg_sorts,
        vec![
            bv_array_sort(32, ChcSort::Bool),
            bv_array_sort(32, ChcSort::BitVec(32)),
            bv_array_sort(64, ChcSort::BitVec(8)),
            ChcSort::BitVec(32),
            ChcSort::Bool,
            ChcSort::BitVec(32),
            ChcSort::BitVec(32),
            ChcSort::BitVec(64),
            ChcSort::BitVec(8),
        ]
    );
    let (_, args) = &transformed.problem.clauses()[0].body.predicates[0];
    assert_eq!(args[3], object);
    assert_eq!(args[5], size_object);
    assert_eq!(args[7], address);
}

#[test]
fn transformer_does_not_reuse_incompatible_head_ghosts_for_body() {
    let mut problem = ChcProblem::new();
    let array32 = bv_array_sort(32, ChcSort::Bool);
    let array64 = bv_array_sort(64, ChcSort::Bool);
    let p = problem.declare_predicate("P", vec![array32.clone()]);
    let q = problem.declare_predicate("Q", vec![array64.clone()]);
    let a = var("a", array32);
    let b = var("b", array64);
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(q, vec![b])], None),
        ClauseHead::Predicate(p, vec![a]),
    ));

    let transformed = Box::new(ArrayGhostPairTransformer::new(1)).transform(problem);
    let clause = &transformed.problem.clauses()[0];
    let ClauseHead::Predicate(_, head_args) = &clause.head else {
        panic!("expected predicate head");
    };
    let (_, body_args) = &clause.body.predicates[0];
    assert_eq!(head_args[1].sort(), ChcSort::BitVec(32));
    assert_eq!(body_args[1], ChcExpr::BitVec(0, 64));
    assert_ne!(head_args[1], body_args[1]);
}

#[test]
fn transformer_is_identity_without_supported_indexed_arrays() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(p, vec![ChcExpr::Int(0)]),
    ));

    let result = Box::new(ArrayGhostPairTransformer::new(1)).transform(problem);
    assert_eq!(result.problem.predicates()[0].arity(), 1);
    assert!(result
        .back_translator
        .transform_memory()
        .is_identity_grade());
}

#[test]
fn index_terms_are_collected_from_selects_and_stores() {
    let problem = const_zero_array_problem();
    let transition = &problem.clauses()[1];
    let terms = collect_index_terms(transition, 6);
    // store(a, n, 0) contributes `n`.
    assert!(terms.contains(&var("n", ChcSort::Int)));

    let query = &problem.clauses()[2];
    let terms = collect_index_terms(query, 6);
    assert!(terms.contains(&var("q", ChcSort::Int)));
}

#[test]
fn symbolic_index_and_trigger_scan_retain_a_late_distinct_sort() {
    let array32 = var("array32", bv_array_sort(32, ChcSort::Bool));
    let array64 = var("array64", bv_array_sort(64, ChcSort::BitVec(8)));
    let address = var("address", ChcSort::BitVec(64));
    let mut conjuncts: Vec<ChcExpr> = (0..4)
        .map(|index| ChcExpr::select(array32.clone(), ChcExpr::BitVec(index, 32)))
        .collect();
    conjuncts.push(ChcExpr::eq(
        ChcExpr::select(array64, address.clone()),
        ChcExpr::BitVec(0, 8),
    ));
    let clause = HornClause::query(ClauseBody::constraint(ChcExpr::and_all(conjuncts)));

    assert!(
        clause_has_symbolic_index(&clause),
        "an existential route gate must scan past a literal-key prefix"
    );
    let terms = collect_index_terms(&clause, 4);
    assert_eq!(terms.len(), 4, "the trigger cap remains enforced");
    assert!(
        terms.contains(&address),
        "a later BV64 trigger must replace a duplicate BV32 representative"
    );
}

#[test]
fn instantiation_tuples_cover_identity_diagonal_and_pairs() {
    let f0 = var("f0", ChcSort::Int);
    let f1 = var("f1", ChcSort::Int);
    let t = var("t", ChcSort::Int);

    // slots=1: identity == diagonal over the fresh var, plus candidates.
    let tuples = instantiation_tuples(&[ChcSort::Int], &[f0.clone()], &[t.clone()], 8);
    assert!(tuples.contains(&vec![f0.clone()]));
    assert!(tuples.contains(&vec![t.clone()]));

    // slots=2: identity tuple, diagonals, and ordered pairs.
    let tuples = instantiation_tuples(
        &[ChcSort::Int, ChcSort::Int],
        &[f0.clone(), f1.clone()],
        &[t.clone()],
        12,
    );
    assert!(tuples.contains(&vec![f0.clone(), f1.clone()]), "identity");
    assert!(tuples.contains(&vec![t.clone(), t.clone()]), "diagonal");
    assert!(
        tuples.contains(&vec![f0.clone(), t.clone()])
            || tuples.contains(&vec![t.clone(), f0.clone()]),
        "ordered pairs"
    );

    // Cap is respected and a fallback tuple exists without any triggers.
    assert!(instantiation_tuples(&[ChcSort::Int, ChcSort::Int], &[], &[], 4).len() <= 4);
    assert_eq!(
        instantiation_tuples(&[ChcSort::Int], &[], &[], 4),
        vec![vec![ChcExpr::Int(0)]]
    );
}

#[test]
fn instantiation_tuples_never_cross_bv_widths() {
    let i32 = var("i32", ChcSort::BitVec(32));
    let i64 = var("i64", ChcSort::BitVec(64));
    let wrong32 = var("wrong32", ChcSort::BitVec(32));
    let sorts = [ChcSort::BitVec(32), ChcSort::BitVec(64)];

    let tuples = instantiation_tuples(&sorts, &[i32.clone(), i64.clone()], &[wrong32], 8);
    assert!(tuples.contains(&vec![i32, i64]), "typed identity tuple");
    assert!(tuples.iter().all(|tuple| {
        tuple.len() == sorts.len()
            && tuple
                .iter()
                .zip(&sorts)
                .all(|(term, sort)| term.sort() == *sort)
    }));

    assert_eq!(
        instantiation_tuples(&sorts, &[], &[], 8),
        vec![vec![ChcExpr::BitVec(0, 32), ChcExpr::BitVec(0, 64)]],
        "fallback constants must retain each slot's width"
    );
}

#[test]
fn instantiation_tuples_reserve_an_alternate_for_every_allowed_slot() {
    let sorts = vec![ChcSort::BitVec(32); 8];
    let fresh: Vec<ChcExpr> = (0..8)
        .map(|slot| var(&format!("fresh{slot}"), ChcSort::BitVec(32)))
        .collect();
    let first = var("first", ChcSort::BitVec(32));
    let alternate = var("alternate", ChcSort::BitVec(32));
    let tuples = instantiation_tuples(
        &sorts,
        &fresh,
        &[first.clone(), alternate.clone()],
        BODY_INSTANCE_CAP,
    );

    assert!(tuples.len() <= BODY_INSTANCE_CAP);
    for slot in 0..sorts.len() {
        let mut expected = vec![first.clone(); sorts.len()];
        expected[slot] = alternate.clone();
        assert!(
            tuples.contains(&expected),
            "bounded assembly must reserve the alternate for slot {slot}"
        );
    }
    assert!(
        instantiation_tuples(&sorts, &fresh, &[first], 0).is_empty(),
        "a zero tuple budget must stay empty"
    );
}

#[test]
fn instantiation_tuples_cover_heterogeneous_slots_within_cap() {
    let object = var("object", ChcSort::BitVec(32));
    let size_object = var("size_object", ChcSort::BitVec(32));
    let address = var("address", ChcSort::BitVec(64));
    let sorts = [
        ChcSort::BitVec(32),
        ChcSort::BitVec(32),
        ChcSort::BitVec(64),
    ];

    let tuples = instantiation_tuples(
        &sorts,
        &[],
        &[object.clone(), size_object.clone(), address.clone()],
        3,
    );
    assert_eq!(
        tuples,
        vec![
            vec![object.clone(), object.clone(), address.clone()],
            vec![size_object.clone(), object.clone(), address.clone()],
            vec![object, size_object, address],
        ],
        "the bounded seed variations must cover every compatible BV32 slot"
    );
}

#[test]
fn false_query_uses_array_specific_cross_array_triggers() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate(
        "P",
        vec![int_array_sort(), int_array_sort(), int_array_sort()],
    );
    let a = var("a", int_array_sort());
    let b = var("b", int_array_sort());
    let c = var("c", int_array_sort());
    let ia = var("ia", ChcSort::Int);
    let ib = var("ib", ChcSort::Int);
    let ic = var("ic", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![a.clone(), b.clone(), c.clone()])],
        Some(ChcExpr::ne(
            ChcExpr::select(c, ic.clone()),
            ChcExpr::add(
                ChcExpr::select(a, ia.clone()),
                ChcExpr::select(b, ib.clone()),
            ),
        )),
    )));

    let transformed = Box::new(ArrayGhostPairTransformer::new(1)).transform(problem);
    let (_, args) = &transformed.problem.clauses()[0].body.predicates[0];
    assert_eq!(args[3], ia, "first array must use its own observed address");
    assert_eq!(
        args[5], ib,
        "second array must use its own observed address"
    );
    assert_eq!(args[7], ic, "third array must use its own observed address");
}

#[test]
fn false_query_preserves_partial_heterogeneous_observations() {
    let mut problem = ChcProblem::new();
    let valid_sort = bv_array_sort(32, ChcSort::Bool);
    let size_sort = bv_array_sort(32, ChcSort::BitVec(32));
    let memory_sort = bv_array_sort(64, ChcSort::BitVec(8));
    let p = problem.declare_predicate(
        "Heap",
        vec![valid_sort.clone(), size_sort.clone(), memory_sort.clone()],
    );
    let valid = var("valid", valid_sort);
    let sizes = var("sizes", size_sort);
    let memory = var("memory", memory_sort);
    let object = ChcExpr::BitVec(7, 32);
    let address = ChcExpr::BitVec(9, 64);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![valid.clone(), sizes.clone(), memory.clone()])],
        Some(ChcExpr::and(
            ChcExpr::select(valid.clone(), object.clone()),
            ChcExpr::ne(
                ChcExpr::select(memory.clone(), address.clone()),
                ChcExpr::BitVec(0, 8),
            ),
        )),
    )));

    let transformed = Box::new(ArrayGhostPairTransformer::new(1)).transform(problem);
    let (_, args) = &transformed.problem.clauses()[0].body.predicates[0];
    let zero_size_index = ChcExpr::BitVec(0, 32);
    assert_eq!(
        args,
        &vec![
            valid.clone(),
            sizes.clone(),
            memory.clone(),
            object.clone(),
            ChcExpr::select(valid, object),
            zero_size_index.clone(),
            ChcExpr::select(sizes, zero_size_index),
            address.clone(),
            ChcExpr::select(memory, address),
        ],
        "unobserved size-array slot must use BV32 zero without discarding the observed BV32/BV64 slots"
    );
}

#[test]
fn non_query_transform_retains_late_heterogeneous_body_trigger() {
    let mut problem = ChcProblem::new();
    let valid_sort = bv_array_sort(32, ChcSort::Bool);
    let memory_sort = bv_array_sort(64, ChcSort::BitVec(8));
    let p = problem.declare_predicate("P", vec![valid_sort.clone(), memory_sort.clone()]);
    let q = problem.declare_predicate("Q", vec![valid_sort.clone()]);
    let valid = var("valid", valid_sort);
    let memory = var("memory", memory_sort);
    let address = var("address", ChcSort::BitVec(64));
    let mut conjuncts: Vec<ChcExpr> = (0..16)
        .map(|index| ChcExpr::select(valid.clone(), ChcExpr::BitVec(index, 32)))
        .collect();
    conjuncts.push(ChcExpr::eq(
        ChcExpr::select(memory.clone(), address.clone()),
        ChcExpr::BitVec(0x42, 8),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![valid.clone(), memory])],
            Some(ChcExpr::and_all(conjuncts)),
        ),
        ClauseHead::Predicate(q, vec![valid]),
    ));

    let transformed = Box::new(ArrayGhostPairTransformer::new(1)).transform(problem);
    let (_, body_args) = &transformed.problem.clauses()[0].body.predicates[0];
    assert_eq!(
        body_args[4], address,
        "sixteen leading BV32 keys must not evict the sole BV64 body trigger"
    );
}

#[test]
fn false_query_n2_uses_two_observed_indices_of_one_array() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![int_array_sort()]);
    let a = var("a", int_array_sort());
    let k = var("k", ChcSort::Int);
    let previous = ChcExpr::add(k.clone(), ChcExpr::Int(-1));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![a.clone()])],
        Some(ChcExpr::not(ChcExpr::le(
            ChcExpr::select(a.clone(), previous.clone()),
            ChcExpr::select(a, k.clone()),
        ))),
    )));

    let transformed = Box::new(ArrayGhostPairTransformer::new(2)).transform(problem);
    let (_, args) = &transformed.problem.clauses()[0].body.predicates[0];
    assert_eq!(args[1], previous, "first pair must probe k - 1");
    assert_eq!(args[3], k, "second pair must probe k");
}

#[test]
fn certificate_budget_scheduler_has_no_eighty_clause_floor() {
    let total = Duration::from_secs(8);
    let budget = per_rule_budget(Some(total), 81);

    assert_eq!(budget, total / 81);
    assert!(
        budget < Duration::from_millis(100),
        "an easy rule must still be attempted when its fair share is below the retired 100ms floor"
    );
    assert!(!budget.is_zero());
}

#[test]
fn certificate_budget_scheduler_never_exceeds_the_remaining_envelope() {
    let short_remaining = Duration::from_millis(37);
    assert_eq!(
        per_rule_budget(Some(Duration::ZERO), 81),
        Duration::ZERO,
        "an exhausted total deadline must not mint per-rule time"
    );
    assert_eq!(
        per_rule_budget(Some(short_remaining), 1),
        short_remaining,
        "the last rule may use all, but no more than, the remaining deadline"
    );
    assert_eq!(
        per_rule_budget(Some(Duration::from_secs(30)), 2),
        Duration::from_secs(5),
        "the per-rule ceiling must still bound a large fair share"
    );
    assert_eq!(
        per_rule_budget(None, 81),
        Duration::from_secs(5),
        "an unbounded total envelope still uses the per-rule ceiling"
    );
    assert!(
        bounded_executor_budget(Duration::from_micros(1999), 2).is_none(),
        "a sub-millisecond half-share must fail closed, not launch an unbounded executor"
    );
    assert_eq!(
        bounded_executor_budget(Duration::from_millis(2), 2),
        Some(Duration::from_millis(1)),
        "the smallest representable bounded half-share remains usable"
    );
}

/// Regression for the former `8s / clause_count >= 100ms` structural gate.
/// Every retained rule has a satisfiable scalar guard and a head that already
/// satisfies the candidate invariant, so 81 rules must not reject the
/// certificate before trying any obligation.
#[test]
fn certify_seals_eighty_one_easy_rules_with_an_eight_second_total_budget() {
    const CLAUSE_COUNT: usize = 81;

    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![int_array_sort(), ChcSort::Int]);
    for rule in 0..CLAUSE_COUNT {
        let guard = var(&format!("guard_{rule}"), ChcSort::Int);
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(guard, ChcExpr::Int(rule as i128))),
            ClauseHead::Predicate(
                p,
                vec![
                    ChcExpr::const_array(ChcSort::Int, ChcExpr::Int(0)),
                    ChcExpr::Int(0),
                ],
            ),
        ));
    }

    assert_eq!(problem.clauses().len(), CLAUSE_COUNT);
    let seeded_model = val_is_zero_ghost_model(p);
    let vars = seeded_model
        .get(&p)
        .expect("seeded model contains P")
        .vars
        .clone();
    let mut easy_model = InvariantModel::new();
    easy_model.set(p, PredicateInterpretation::new(vars, ChcExpr::Bool(true)));
    assert!(
        GhostPairCertificate::certify_and_seal(
            &problem,
            GhostPairSpec::analyze(&problem, 1),
            easy_model,
            Some(Duration::from_secs(8)),
        )
        .is_some(),
        "easy rules above the old 80-clause threshold must be attempted under the shared deadline"
    );
}

/// Compiler wrapper graphs contain long runs of identity forwarding rules.
/// Their finite discharge is exactly `I(k) /\ !I(k)`: after the mandatory
/// quantified-replay preflight, the bounded syntactic simplifier must close
/// them without constructing one executor per wrapper.
#[test]
fn certify_closes_ninety_nine_forwarders_inside_one_shared_deadline() {
    const CLAUSE_COUNT: usize = 99;

    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![int_array_sort(), ChcSort::Int]);
    let initial_array = var("initial_array", int_array_sort());
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(
            initial_array.clone(),
            ChcExpr::const_array(ChcSort::Int, ChcExpr::Int(0)),
        )),
        ClauseHead::Predicate(p, vec![initial_array, ChcExpr::Int(0)]),
    ));
    for rule in 0..CLAUSE_COUNT {
        let array = var(&format!("array_{rule}"), int_array_sort());
        let scalar = var(&format!("scalar_{rule}"), ChcSort::Int);
        let args = vec![array, scalar];
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(p, args.clone())]),
            ClauseHead::Predicate(p, args),
        ));
    }
    let query_array = var("query_array", int_array_sort());
    let query_scalar = var("query_scalar", ChcSort::Int);
    let query_index = var("query_index", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![query_array.clone(), query_scalar])],
        Some(ChcExpr::ne(
            ChcExpr::select(query_array, query_index),
            ChcExpr::Int(0),
        )),
    )));

    let mut conjunctive_model = val_is_zero_ghost_model(p);
    let vars = conjunctive_model
        .get(&p)
        .expect("seeded model contains P")
        .vars
        .clone();
    let value = ChcExpr::var(vars[3].clone());
    conjunctive_model.set(
        p,
        PredicateInterpretation::new(
            vars,
            ChcExpr::and(
                ChcExpr::eq(value.clone(), ChcExpr::Int(0)),
                ChcExpr::le(value, ChcExpr::Int(0)),
            ),
        ),
    );
    assert!(
        GhostPairCertificate::certify_and_seal(
            &problem,
            GhostPairSpec::analyze(&problem, 1),
            conjunctive_model,
            Some(Duration::from_secs(5)),
        )
        .is_some(),
        "conjunctive identity-forwarding obligations must use the bounded exact contradiction fast path"
    );
}

#[test]
fn certify_seals_a_valid_quantified_ghost_model() {
    let problem = const_zero_array_problem();
    let p = problem.predicates()[0].id;
    let spec = GhostPairSpec::analyze(&problem, 1);
    let model = val_is_zero_ghost_model(p);

    let certificate = GhostPairCertificate::certify_and_seal(
        &problem,
        spec,
        model,
        Some(Duration::from_secs(30)),
    );
    let certificate = certificate.expect("val=0 ghost model must certify on the original clauses");
    assert_eq!(certificate.ghost_pairs_per_array(), 1);

    // Re-checks (finalize boundary: all clauses; runner gate: query clauses).
    assert!(recheck_ghost_pair_certificate(
        &problem,
        &certificate,
        Some(Duration::from_secs(30)),
        false,
    ));
    assert!(recheck_ghost_pair_certificate(
        &problem,
        &certificate,
        Some(Duration::from_secs(30)),
        true,
    ));
}

#[test]
fn certify_and_replay_seal_bv32_and_bv64_quantified_models() {
    for width in [32, 64] {
        let problem = bv_indexed_const_zero_problem(width);
        let p = problem.predicates()[0].id;
        let certificate = GhostPairCertificate::certify_and_seal(
            &problem,
            GhostPairSpec::analyze(&problem, 1),
            bv_val_is_zero_ghost_model(p, width),
            Some(Duration::from_secs(30)),
        )
        .unwrap_or_else(|| panic!("BV{width}-indexed quantified model must certify"));

        let mut model = InvariantModel::new();
        model.set_ghost_pair_certificate(certificate);
        let obligations = crate::engines::chc_safe_replay_obligations(&problem, &model)
            .expect("BV-indexed certificate must export replay obligations");
        let binder_sort = format!("(_ BitVec {width})");
        assert!(
            obligations
                .iter()
                .any(|obligation| obligation.smtlib.contains(&binder_sort)),
            "replay must quantify the original BV{width} key sort"
        );
        assert!(obligations.iter().all(|obligation| {
            crate::smt::executor_adapter::check_unsat_smtlib_via_executor(&obligation.smtlib)
        }));
    }
}

#[test]
fn certification_rejects_a_wrong_width_interpretation_before_discharge() {
    let problem = bv_indexed_const_zero_problem(32);
    let p = problem.predicates()[0].id;
    let mut model = bv_val_is_zero_ghost_model(p, 32);
    let mut wrong = model.get(&p).expect("model contains P").clone();
    wrong.vars[1].sort = ChcSort::BitVec(64);
    model.set(p, wrong);

    assert!(
        GhostPairCertificate::certify_and_seal(
            &problem,
            GhostPairSpec::analyze(&problem, 1),
            model,
            Some(Duration::from_secs(30)),
        )
        .is_none(),
        "a wrong-width ghost parameter must fail the structural gate"
    );
}

/// SOUNDNESS PIN: a ghost model that is NOT a solution of the original system
/// must never seal. A naive lane that trusted the transformed-problem verdict
/// without the original-clause quantified discharge would emit a wrong `sat`
/// here; the certification gate forces unknown instead.
#[test]
fn certify_rejects_a_non_solution_ghost_model() {
    let problem = const_zero_array_problem();
    let p = problem.predicates()[0].id;
    let spec = GhostPairSpec::analyze(&problem, 1);

    // `true` is inductive for init/transition clauses but does NOT discharge
    // the query clause — accepting it would be a false SAFE.
    let vars = vec![
        ChcVar::new("__p0_a0", int_array_sort()),
        ChcVar::new("__p0_a1", ChcSort::Int),
        ChcVar::new("__p0_a2", ChcSort::Int),
        ChcVar::new("__p0_a3", ChcSort::Int),
    ];
    let mut model = InvariantModel::new();
    model.set(p, PredicateInterpretation::new(vars, ChcExpr::Bool(true)));

    assert!(
        GhostPairCertificate::certify_and_seal(
            &problem,
            spec,
            model,
            Some(Duration::from_secs(30)),
        )
        .is_none(),
        "non-solution ghost model must fail certification (fail-closed)"
    );
}

/// Regression pin for the #8734-class CLI aborts on ghost-pair SAFEs: the
/// Safe model carried by a sealed certificate has an EMPTY per-predicate
/// interpretation map, so the standard invariant replay exporter used to fail
/// with "missing invariant interpretation" and the CLI exited 1 on genuinely
/// SAFE array CHCs. `chc_safe_replay_obligations` must instead export the
/// certificate's own per-clause quantified discharge queries, each of which
/// is independently UNSAT.
#[test]
fn ghost_pair_certificate_exports_unsat_replay_obligations() {
    let problem = const_zero_array_problem();
    let p = problem.predicates()[0].id;
    let spec = GhostPairSpec::analyze(&problem, 1);
    let certificate = GhostPairCertificate::certify_and_seal(
        &problem,
        spec,
        val_is_zero_ghost_model(p),
        Some(Duration::from_secs(30)),
    )
    .expect("val=0 ghost model must certify on the original clauses");

    let mut model = InvariantModel::new();
    model.set_ghost_pair_certificate(certificate);

    let obligations = crate::engines::chc_safe_replay_obligations(&problem, &model)
        .expect("ghost-pair Safe must export replay obligations, not a hard error");

    assert_eq!(
        obligations.len(),
        problem.clauses().len(),
        "one obligation per original clause"
    );
    assert_eq!(
        obligations
            .iter()
            .map(|o| o.kind)
            .collect::<Vec<ChcReplayObligationKind>>(),
        vec![
            ChcReplayObligationKind::Initiation,
            ChcReplayObligationKind::Consecution,
            ChcReplayObligationKind::Safety,
        ],
    );
    for (clause_index, obligation) in obligations.iter().enumerate() {
        assert_eq!(obligation.clause_index, clause_index);
        assert!(obligation.smtlib.contains("(check-sat)"));
        assert!(
            !obligation.smtlib.contains(":timeout"),
            "replay artifacts must not embed solver-local timeouts"
        );
        assert!(
            crate::smt::executor_adapter::check_unsat_smtlib_via_executor(&obligation.smtlib),
            "obligation {} must be independently UNSAT; got sat/unknown for:\n{}",
            obligation.name,
            obligation.smtlib,
        );
    }
    // The quantified body hypothesis appears wherever a ghost-carrying
    // predicate occurs in the clause body (consecution + safety).
    assert!(obligations[1].smtlib.contains("(forall ("));
    assert!(obligations[2].smtlib.contains("(forall ("));
}

#[test]
fn ghost_pair_replay_reconstructs_scalar_uf_declarations() {
    let mut problem = const_zero_array_problem();
    let f_zero = ChcExpr::FuncApp("f".to_string(), ChcSort::Int, vec![ChcExpr::Int(0).into()]);
    problem.clauses_mut()[0].body.constraint = Some(ChcExpr::eq(f_zero.clone(), f_zero));

    let p = problem.predicates()[0].id;
    let certificate = GhostPairCertificate::certify_and_seal(
        &problem,
        GhostPairSpec::analyze(&problem, 1),
        val_is_zero_ghost_model(p),
        Some(Duration::from_secs(30)),
    )
    .expect("tautological ordinary UF premise must preserve certification");
    let mut model = InvariantModel::new();
    model.set_ghost_pair_certificate(certificate);

    let obligations = crate::engines::chc_safe_replay_obligations(&problem, &model)
        .expect("ghost-pair replay should remain self-contained with a scalar UF");
    assert!(
        obligations[0].smtlib.contains("(declare-fun f (Int) Int)"),
        "quantified replay must reconstruct f's declaration: {}",
        obligations[0].smtlib
    );
}

#[test]
fn ghost_pair_replay_declares_uninterpreted_sorts_before_use() {
    let (problem, ghost_model) = opaque_cell_problem_and_model("OpaqueCell");
    let certificate = GhostPairCertificate::certify_and_seal(
        &problem,
        GhostPairSpec::analyze(&problem, 1),
        ghost_model,
        Some(Duration::from_secs(30)),
    )
    .expect("opaque-cell quantified invariant must certify");
    let mut model = InvariantModel::new();
    model.set_ghost_pair_certificate(certificate);
    let obligations = crate::engines::chc_safe_replay_obligations(&problem, &model)
        .expect("opaque-cell certificate must export replay obligations");
    assert!(obligations.iter().all(|obligation| {
        obligation.smtlib.contains("(declare-sort OpaqueCell 0)")
            && crate::smt::executor_adapter::check_unsat_smtlib_via_executor(&obligation.smtlib)
    }));
}

#[test]
fn sealing_rejects_an_unserializable_sort_even_when_finite_discharge_succeeds() {
    for sort_name in ["opaque cell", "Int", "String", "Float64"] {
        let (problem, ghost_model) = opaque_cell_problem_and_model(sort_name);
        assert!(
            GhostPairCertificate::certify_and_seal(
                &problem,
                GhostPairSpec::analyze(&problem, 1),
                ghost_model,
                Some(Duration::from_secs(30)),
            )
            .is_none(),
            "unserializable sort {sort_name} must prevent sealing"
        );
    }
}

#[test]
fn replay_declares_expression_local_uninterpreted_sorts() {
    let problem = const_zero_array_problem();
    let p = problem.predicates()[0].id;
    let mut model = val_is_zero_ghost_model(p);
    let interp = model.get(&p).expect("model contains P").clone();
    let local_array = ChcExpr::const_array(
        ChcSort::Uninterpreted("LocalIndex".to_string()),
        ChcExpr::Int(0),
    );
    model.set(
        p,
        PredicateInterpretation::new(
            interp.vars,
            ChcExpr::and(
                interp.formula,
                ChcExpr::eq(local_array.clone(), local_array),
            ),
        ),
    );

    let certificate = GhostPairCertificate::certify_and_seal(
        &problem,
        GhostPairSpec::analyze(&problem, 1),
        model,
        Some(Duration::from_secs(30)),
    )
    .expect("expression-local sort annotations must remain replayable");
    let mut sealed_model = InvariantModel::new();
    sealed_model.set_ghost_pair_certificate(certificate);
    let obligations = crate::engines::chc_safe_replay_obligations(&problem, &sealed_model)
        .expect("sealed certificate must export every obligation");
    assert!(obligations.iter().all(|obligation| {
        obligation.smtlib.contains("(declare-sort LocalIndex 0)")
            && crate::smt::executor_adapter::check_unsat_smtlib_via_executor(&obligation.smtlib)
    }));
}

/// SOUNDNESS PIN: SMT-LIB quantifier binders share the term namespace with
/// nullary UFs. If the generated `__gpb0` binder shadows the source UF of the
/// same name, `forall i. a[i] = c` is silently changed to `forall i. a[i] = i`
/// and this genuinely unsafe system can be mis-certified Safe.
#[test]
fn certification_reserves_nullary_uf_names_from_quantified_binders() {
    let mut problem = ChcProblem::new();
    let array_sort = int_array_sort();
    let p = problem.declare_predicate("P", vec![array_sort.clone(), ChcSort::Int]);
    let source_constant = ChcExpr::FuncApp("__gpb0".to_string(), ChcSort::Int, vec![]);
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(
            p,
            vec![
                ChcExpr::const_array(ChcSort::Int, source_constant.clone()),
                source_constant.clone(),
            ],
        ),
    ));
    let array = var("array", array_sort.clone());
    let query_index = var("query_index", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![array.clone(), source_constant])],
        Some(ChcExpr::ne(
            ChcExpr::select(array, query_index.clone()),
            query_index,
        )),
    )));

    let params = vec![
        ChcVar::new("array_param", array_sort),
        ChcVar::new("scalar_param", ChcSort::Int),
        ChcVar::new("ghost_index", ChcSort::Int),
        ChcVar::new("ghost_value", ChcSort::Int),
    ];
    let formula = ChcExpr::eq(
        ChcExpr::var(params[3].clone()),
        ChcExpr::var(params[1].clone()),
    );
    let mut model = InvariantModel::new();
    model.set(p, PredicateInterpretation::new(params, formula));

    assert!(
        GhostPairCertificate::certify_and_seal(
            &problem,
            GhostPairSpec::analyze(&problem, 1),
            model,
            Some(Duration::from_secs(30)),
        )
        .is_none(),
        "source UF names must remain global inside quantified discharge"
    );
}

#[test]
fn certification_rejects_clause_variable_and_model_uf_namespace_collision() {
    let mut problem = const_zero_array_problem();
    let p = problem.predicates()[0].id;
    let colliding_uf = ChcExpr::FuncApp("q".to_string(), ChcSort::Int, vec![]);
    problem.clauses_mut()[0].body.constraint =
        Some(ChcExpr::eq(colliding_uf.clone(), ChcExpr::Int(0)));
    let mut model = val_is_zero_ghost_model(p);
    let interp = model.get(&p).expect("model contains P").clone();
    model.set(
        p,
        PredicateInterpretation::new(
            interp.vars,
            ChcExpr::and(
                interp.formula,
                ChcExpr::or(
                    ChcExpr::eq(colliding_uf.clone(), ChcExpr::Int(0)),
                    ChcExpr::ne(colliding_uf, ChcExpr::Int(0)),
                ),
            ),
        ),
    );

    assert!(
        GhostPairCertificate::certify_and_seal(
            &problem,
            GhostPairSpec::analyze(&problem, 1),
            model,
            Some(Duration::from_secs(30)),
        )
        .is_none(),
        "replay cannot declare the query variable q and a nullary UF q in one scope"
    );
}

#[test]
fn certification_rejects_deep_source_argument_before_quantifier_capture() {
    let mut problem = const_zero_array_problem();
    let p = problem.predicates()[0].id;
    let mut hidden_index = var("__gpb0", ChcSort::Int);
    for _ in 0..crate::expr::MAX_EXPR_RECURSION_DEPTH + 8 {
        hidden_index = ChcExpr::add(hidden_index, ChcExpr::Int(0));
    }
    let hidden_array = var("hidden_array", int_array_sort());
    problem.clauses_mut()[1].body.predicates[0].1[0] =
        ChcExpr::store(hidden_array, hidden_index, ChcExpr::Int(0));

    assert!(
        GhostPairCertificate::certify_and_seal(
            &problem,
            GhostPairSpec::analyze(&problem, 1),
            val_is_zero_ghost_model(p),
            Some(Duration::from_secs(30)),
        )
        .is_none(),
        "a hidden __gpb0 source variable must never be captured by a generated forall"
    );
}

/// Structural fail-closed pins: missing interpretations, arity mismatches,
/// free variables, and malformed expression types are rejected before SMT.
#[test]
fn certify_rejects_structurally_broken_models() {
    let problem = const_zero_array_problem();
    let p = problem.predicates()[0].id;
    let spec = GhostPairSpec::analyze(&problem, 1);

    // Missing interpretation.
    assert!(GhostPairCertificate::certify_and_seal(
        &problem,
        spec.clone(),
        InvariantModel::new(),
        Some(Duration::from_secs(5)),
    )
    .is_none());

    // Arity mismatch (original arity, no ghost slots).
    let mut short_model = InvariantModel::new();
    short_model.set(
        p,
        PredicateInterpretation::new(
            vec![
                ChcVar::new("__p0_a0", int_array_sort()),
                ChcVar::new("__p0_a1", ChcSort::Int),
            ],
            ChcExpr::Bool(true),
        ),
    );
    assert!(GhostPairCertificate::certify_and_seal(
        &problem,
        spec.clone(),
        short_model,
        Some(Duration::from_secs(5)),
    )
    .is_none());

    // Free non-parameter variable in the formula.
    let mut free_var_model = val_is_zero_ghost_model(p);
    let interp = free_var_model.get(&p).unwrap().clone();
    free_var_model.set(
        p,
        PredicateInterpretation::new(
            interp.vars,
            ChcExpr::eq(var("stray", ChcSort::Int), ChcExpr::Int(0)),
        ),
    );
    assert!(GhostPairCertificate::certify_and_seal(
        &problem,
        spec.clone(),
        free_var_model,
        Some(Duration::from_secs(5)),
    )
    .is_none());

    // Top-level Bool shape is insufficient: `not` must have one Bool child.
    let mut malformed_model = val_is_zero_ghost_model(p);
    let interp = malformed_model.get(&p).unwrap().clone();
    malformed_model.set(
        p,
        PredicateInterpretation::new(interp.vars, ChcExpr::not(ChcExpr::Int(0))),
    );
    assert!(GhostPairCertificate::certify_and_seal(
        &problem,
        spec.clone(),
        malformed_model,
        Some(Duration::from_secs(5)),
    )
    .is_none());
}

#[test]
fn certify_rejects_non_positive_rational_denominators() {
    let problem = const_zero_array_problem();
    let p = problem.predicates()[0].id;
    let spec = GhostPairSpec::analyze(&problem, 1);
    for denominator in [0, -2] {
        let mut model = val_is_zero_ghost_model(p);
        let interp = model.get(&p).unwrap().clone();
        model.set(
            p,
            PredicateInterpretation::new(
                interp.vars,
                ChcExpr::eq(ChcExpr::Real(1, denominator), ChcExpr::Real(1, denominator)),
            ),
        );
        assert!(GhostPairCertificate::certify_and_seal(
            &problem,
            spec.clone(),
            model,
            Some(Duration::from_secs(5)),
        )
        .is_none());
    }
}

/// SOUNDNESS PIN: parameter membership is typed, not name-only. Otherwise the
/// Bool `capture` in the candidate below survives substitution for the
/// same-named Array parameter and captures each clause's Bool variable. That
/// makes both contradictory clauses discharge independently even though no
/// closed interpretation of `P` can satisfy the original problem.
#[test]
fn certify_rejects_same_name_wrong_sort_clause_capture() {
    let mut problem = ChcProblem::new();
    let array_sort = int_array_sort();
    let p = problem.declare_predicate("P", vec![array_sort.clone()]);

    let array = var("array", array_sort.clone());
    let capture = var("capture", ChcSort::Bool);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(capture.clone()),
        ClauseHead::Predicate(p, vec![array.clone()]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![array])],
        Some(ChcExpr::not(capture)),
    )));

    let params = vec![
        ChcVar::new("capture", array_sort),
        ChcVar::new("ghost_index", ChcSort::Int),
        ChcVar::new("ghost_value", ChcSort::Int),
    ];
    let mut model = InvariantModel::new();
    model.set(
        p,
        PredicateInterpretation::new(params.clone(), var("capture", ChcSort::Bool)),
    );

    assert!(
        GhostPairCertificate::certify_and_seal(
            &problem,
            GhostPairSpec::analyze(&problem, 1),
            model,
            Some(Duration::from_secs(5)),
        )
        .is_none(),
        "a same-name, wrong-sort free variable must not capture a clause variable"
    );

    // The generic vars/substitution helpers are intentionally best-effort at
    // extreme depth. Certificate sealing must instead reject the whole model,
    // so a hidden same-name variable can never survive and capture a rule var.
    let mut deep_capture = var("capture", ChcSort::Bool);
    for _ in 0..crate::expr::MAX_EXPR_RECURSION_DEPTH + 8 {
        deep_capture = ChcExpr::not(deep_capture);
    }
    let mut deep_model = InvariantModel::new();
    deep_model.set(p, PredicateInterpretation::new(params, deep_capture));
    assert!(
        GhostPairCertificate::certify_and_seal(
            &problem,
            GhostPairSpec::analyze(&problem, 1),
            deep_model,
            Some(Duration::from_secs(5)),
        )
        .is_none(),
        "depth exhaustion at the proof boundary must reject the whole certificate"
    );
}

/// A depth-limited best-effort substitution would leave the Bool formal named
/// `capture` in place. The rule-local variable of the same name would then make
/// both an unsafe initiation/query pair tautological. Sealing must reject the
/// entire over-depth interpretation before any discharge query is emitted.
#[test]
fn certify_rejects_depth_exhaustion_before_formal_capture() {
    let mut problem = ChcProblem::new();
    let array_sort = int_array_sort();
    let p = problem.declare_predicate("P", vec![array_sort.clone(), ChcSort::Bool]);
    let array = var("array", array_sort.clone());
    let capture = var("capture", ChcSort::Bool);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(capture.clone()),
        ClauseHead::Predicate(p, vec![array.clone(), ChcExpr::Bool(true)]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![array, ChcExpr::Bool(true)])],
        Some(ChcExpr::not(capture)),
    )));

    let formal = ChcVar::new("capture", ChcSort::Bool);
    let params = vec![
        ChcVar::new("array_param", array_sort),
        formal.clone(),
        ChcVar::new("ghost_index", ChcSort::Int),
        ChcVar::new("ghost_value", ChcSort::Int),
    ];
    let mut formula = ChcExpr::var(formal);
    for _ in 0..crate::expr::MAX_EXPR_RECURSION_DEPTH + 8 {
        formula = ChcExpr::and(ChcExpr::Bool(true), formula);
    }
    let mut model = InvariantModel::new();
    model.set(p, PredicateInterpretation::new(params, formula));

    assert!(
        GhostPairCertificate::certify_and_seal(
            &problem,
            GhostPairSpec::analyze(&problem, 1),
            model,
            Some(Duration::from_secs(5)),
        )
        .is_none(),
        "all-or-nothing certificate substitution must reject depth exhaustion"
    );
}

#[test]
fn certify_rejects_duplicate_parameter_names() {
    let problem = const_zero_array_problem();
    let p = problem.predicates()[0].id;
    let mut model = val_is_zero_ghost_model(p);
    let mut interp = model.get(&p).expect("model contains P").clone();
    interp.vars[2].name = interp.vars[1].name.clone();
    model.set(p, interp);

    assert!(
        GhostPairCertificate::certify_and_seal(
            &problem,
            GhostPairSpec::analyze(&problem, 1),
            model,
            Some(Duration::from_secs(5)),
        )
        .is_none(),
        "duplicate parameter symbols must fail the structural gate"
    );
}

#[test]
fn certified_model_passes_external_validation_gates() {
    let problem = const_zero_array_problem();
    let p = problem.predicates()[0].id;
    let spec = GhostPairSpec::analyze(&problem, 1);
    let certificate = GhostPairCertificate::certify_and_seal(
        &problem,
        spec,
        val_is_zero_ghost_model(p),
        Some(Duration::from_secs(30)),
    )
    .expect("model must certify");

    let mut model = InvariantModel::new();
    model.set_ghost_pair_certificate(certificate);
    assert!(model.has_quantified_array_certificate());

    let config = crate::PdrConfig {
        solve_timeout: Some(Duration::from_secs(30)),
        ..crate::PdrConfig::default()
    };
    assert!(
        crate::engines::validate_external_invariant_model(&problem, &model, &config).unwrap(),
        "full validation gate must accept the sealed certificate"
    );
    assert!(
        crate::engines::external_invariant_model_excludes_error(&problem, &model, &config).unwrap(),
        "excludes-error gate must accept the sealed certificate"
    );
}

#[test]
fn invalidity_backtranslation_strips_ghost_assignments() {
    use crate::pdr::counterexample::{Counterexample, CounterexampleStep};
    use ay_core::kani_compat::DetHashMap as FxHashMap;

    let problem = const_zero_array_problem();
    let p = problem.predicates()[0].id;
    let result = Box::new(ArrayGhostPairTransformer::new(1)).transform(problem);

    let mut assignments = FxHashMap::default();
    assignments.insert(format!("__p{}_a1", p.index()), 3i64);
    assignments.insert(format!("__p{}_a2", p.index()), 7i64); // ghost idx
    assignments.insert(format!("__p{}_a3", p.index()), 9i64); // ghost val
    let cex = Counterexample {
        steps: vec![CounterexampleStep::new(p, assignments)],
        witness: None,
        ground_derivation: None,
    };

    let translated = result.back_translator.translate_invalidity(cex);
    let step = &translated.steps[0];
    assert!(step
        .assignments
        .contains_key(&format!("__p{}_a1", p.index())));
    assert!(!step
        .assignments
        .contains_key(&format!("__p{}_a2", p.index())));
    assert!(!step
        .assignments
        .contains_key(&format!("__p{}_a3", p.index())));
}
