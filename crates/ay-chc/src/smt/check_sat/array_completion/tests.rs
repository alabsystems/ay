// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original array models must retain the bindings the consumer replays.

use super::*;
use std::cell::Cell;

fn array(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(
        name,
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    ))
}

fn constant(value: i128) -> ChcExpr {
    ChcExpr::const_array(ChcSort::Int, ChcExpr::Int(value))
}

fn partial(name: &str, value: SmtValue) -> FxHashMap<String, SmtValue> {
    let mut model = FxHashMap::default();
    model.insert(name.to_owned(), value);
    model
}

fn zero() -> SmtValue {
    SmtValue::ConstArray(Box::new(SmtValue::Int(0)))
}

#[test]
fn actual_array_executor_route_restores_an_eliminated_alias() {
    let a = array("__model_checker_consumer_direct_smt_alpha_0_c0_v0");
    let b = array("__model_checker_consumer_direct_smt_alpha_0_c1_v0");
    let original = ChcExpr::and_all([
        ChcExpr::eq(a.clone(), b.clone()),
        ChcExpr::eq(a, constant(7)),
        ChcExpr::eq(ChcExpr::select(b, ChcExpr::Int(2)), ChcExpr::Int(7)),
    ]);
    let SmtResult::Sat(model) =
        SmtContext::new().check_sat_with_timeout(&original, Duration::from_secs(5))
    else {
        panic!("a ground-backed array alias must have a replayable SAT model");
    };
    assert_eq!(model.len(), 2);
    assert_eq!(
        model.get("__model_checker_consumer_direct_smt_alpha_0_c0_v0"),
        model.get("__model_checker_consumer_direct_smt_alpha_0_c1_v0")
    );
    assert_eq!(
        verify_sat_model_strict(&original, &model),
        ModelVerifyResult::Valid
    );
}

#[test]
fn actual_array_route_keeps_scalar_aliases_and_ssa_store_bindings() {
    let key = ChcSort::BitVec(64);
    let element = ChcSort::BitVec(8);
    let sort = ChcSort::Array(Box::new(key.clone()), Box::new(element));
    let var = |name| ChcExpr::var(ChcVar::new(name, sort.clone()));
    let i = ChcExpr::var(ChcVar::new("i", key.clone()));
    let j = ChcExpr::var(ChcVar::new("threaded_i", key.clone()));
    let base = ChcExpr::const_array(key, ChcExpr::BitVec(7, 8));
    let stored = ChcExpr::store(var("a"), i.clone(), ChcExpr::BitVec(9, 8));
    let original = ChcExpr::and_all([
        ChcExpr::eq(i.clone(), j.clone()),
        ChcExpr::eq(i, ChcExpr::BitVec(1, 64)),
        ChcExpr::eq(var("a"), base),
        ChcExpr::eq(var("b"), stored),
        ChcExpr::eq(var("b"), var("threaded_b")),
        ChcExpr::eq(ChcExpr::select(var("threaded_b"), j), ChcExpr::BitVec(9, 8)),
    ]);
    let SmtResult::Sat(model) =
        SmtContext::new().check_sat_with_timeout(&original, Duration::from_secs(5))
    else {
        panic!("SSA store aliases must return exact original scalar and array values");
    };
    for name in ["i", "threaded_i", "a", "b", "threaded_b"] {
        assert!(model.contains_key(name), "{name}");
    }
    assert_eq!(model["i"], SmtValue::BitVec(1, 64));
    assert_eq!(model["threaded_i"], model["i"]);
    assert_eq!(model["threaded_b"], model["b"]);
    assert_eq!(
        verify_sat_model_strict(&original, &model),
        ModelVerifyResult::Valid
    );
}

#[test]
fn original_nested_array_definitions_resolve_to_fixpoint() {
    let row_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let grid_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(row_sort.clone()));
    let row = ChcExpr::var(ChcVar::new("row", row_sort));
    let grid = ChcExpr::var(ChcVar::new("grid", grid_sort));
    let original = ChcExpr::and_all([
        ChcExpr::eq(
            grid.clone(),
            ChcExpr::const_array(ChcSort::Int, row.clone()),
        ),
        ChcExpr::eq(row, constant(0)),
        ChcExpr::eq(
            ChcExpr::select(ChcExpr::select(grid, ChcExpr::Int(1)), ChcExpr::Int(2)),
            ChcExpr::Int(0),
        ),
    ]);
    let model = reconstruct(&original, FxHashMap::default(), &mut || true)
        .expect("both original definitions resolve");
    assert_eq!(model.len(), 2);
    assert_eq!(
        verify_sat_model_strict(&original, &model),
        ModelVerifyResult::Valid
    );
}

#[test]
fn a_conflicting_definition_or_existing_binding_is_not_overwritten() {
    let a = array("a");
    let original = ChcExpr::and_all([
        ChcExpr::eq(a.clone(), constant(0)),
        ChcExpr::eq(a, constant(1)),
    ]);
    assert!(reconstruct(&original, FxHashMap::default(), &mut || true).is_none());
    let original = ChcExpr::eq(array("a"), constant(1));
    assert!(reconstruct(&original, partial("a", zero()), &mut || true).is_none());
}

#[test]
fn definitions_under_negation_or_disjunction_cannot_fill_a_model() {
    let binding = ChcExpr::eq(array("a"), constant(0));
    let guard = ChcExpr::var(ChcVar::new("guard", ChcSort::Bool));
    for original in [
        ChcExpr::not(binding.clone()),
        ChcExpr::or(binding.clone(), guard),
    ] {
        assert!(original.vars().iter().any(|var| var.name == "a"));
        assert!(reconstruct(&original, FxHashMap::default(), &mut || true).is_none());
    }
    // The canonical constructor erases this tautology's variables before
    // reconstruction. A valid empty model must not become a false refusal.
    let tautology = ChcExpr::or(binding, ChcExpr::Bool(true));
    assert_eq!(tautology, ChcExpr::Bool(true));
    assert!(reconstruct(&tautology, FxHashMap::default(), &mut || true)
        .expect("constant true has a complete empty model")
        .is_empty());
}

#[test]
fn cyclic_or_free_arrays_are_not_default_completed() {
    let original = ChcExpr::and_all([
        ChcExpr::eq(array("a"), array("b")),
        ChcExpr::eq(array("b"), array("a")),
    ]);
    assert!(reconstruct(&original, FxHashMap::default(), &mut || true).is_none());
    let original = ChcExpr::eq(
        ChcExpr::select(array("a"), ChcExpr::Int(0)),
        ChcExpr::Int(7),
    );
    assert!(reconstruct(&original, FxHashMap::default(), &mut || true).is_none());
}

#[test]
fn malformed_store_and_wrong_typed_array_values_are_refused() {
    let original = ChcExpr::eq(
        array("a"),
        ChcExpr::store(constant(0), ChcExpr::Bool(true), ChcExpr::Int(1)),
    );
    assert!(reconstruct(&original, FxHashMap::default(), &mut || true).is_none());
    let original = ChcExpr::eq(array("a"), array("b"));
    let wrong = SmtValue::ConstArray(Box::new(SmtValue::Bool(false)));
    assert!(reconstruct(&original, partial("a", wrong), &mut || true).is_none());
}

#[test]
fn same_name_with_different_sorts_is_refused_before_name_only_insertion() {
    let original = ChcExpr::and_all([
        ChcExpr::eq(array("same"), constant(0)),
        ChcExpr::eq(
            ChcExpr::var(ChcVar::new("same", ChcSort::Int)),
            ChcExpr::Int(0),
        ),
    ]);
    assert!(reconstruct(&original, FxHashMap::default(), &mut || true).is_none());
}

#[test]
fn the_original_not_only_the_normalized_expression_must_verify() {
    let original = ChcExpr::and_all([
        ChcExpr::eq(array("a"), array("b")),
        ChcExpr::eq(
            ChcExpr::select(array("b"), ChcExpr::Int(0)),
            ChcExpr::Int(1),
        ),
    ]);
    // A producer's normalized partial model cannot authorize a changed
    // original read. Aliases can be derived, but its ORIGINAL read is false.
    assert!(reconstruct(&original, partial("a", zero()), &mut || true).is_none());
}

#[test]
fn source_depth_pending_edges_and_value_payload_share_refusal_limits() {
    let mut deep = ChcExpr::eq(array("a"), constant(0));
    for _ in 0..crate::expr::MAX_EXPR_RECURSION_DEPTH / 2 {
        deep = ChcExpr::Op(ChcOp::And, vec![deep.into()]);
    }
    assert!(reconstruct(&deep, FxHashMap::default(), &mut || true).is_none());
    let wide = ChcExpr::Op(ChcOp::And, vec![ChcExpr::Bool(true).into(); 9]);
    let mut live = || true;
    let mut budget = Budget {
        remaining: 8,
        poll: &mut live,
    };
    assert!(
        source(&wide, &mut budget).is_none(),
        "pre-admit pending edges"
    );
    let value = SmtValue::ArrayMap {
        default: Box::new(SmtValue::Int(0)),
        entries: vec![(SmtValue::Int(0), SmtValue::Int(1)); 4],
    };
    let sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let mut budget = Budget {
        remaining: 8,
        poll: &mut live,
    };
    assert!(
        values::typed(&value, &sort, &mut budget).is_none(),
        "pre-admit value entries"
    );
}

#[test]
fn every_observed_stop_ends_reconstruction_without_callback_reentry() {
    let original = ChcExpr::and_all([
        ChcExpr::eq(array("a"), array("b")),
        ChcExpr::eq(array("b"), constant(0)),
    ]);
    let calls = Cell::new(0usize);
    assert!(reconstruct(&original, FxHashMap::default(), &mut || {
        calls.set(calls.get() + 1);
        true
    })
    .is_some());
    for stop in 1..=calls.get() {
        let mut actual = 0;
        assert!(reconstruct(&original, FxHashMap::default(), &mut || {
            actual += 1;
            actual != stop
        })
        .is_none());
        assert_eq!(actual, stop, "no poll after a refused checkpoint");
    }
}

#[test]
fn original_timeout_and_scoped_deadline_cannot_be_renewed_by_completion() {
    let context = SmtContext::new();
    let original = ChcExpr::eq(array("a"), constant(0));
    let result = context.restore_preprocessed_array_model(
        &original,
        SmtResult::Sat(FxHashMap::default()),
        Instant::now(),
        Some(Duration::ZERO),
    );
    assert!(matches!(result, SmtResult::Unknown));
    let _scope = super::super::super::deadline::ScopedSmtDeadline::install(Duration::ZERO);
    let result = context.restore_preprocessed_array_model(
        &original,
        SmtResult::Sat(FxHashMap::default()),
        Instant::now(),
        None,
    );
    assert!(matches!(result, SmtResult::Unknown));
}

#[test]
fn a_128_alias_chain_uses_local_carriers_and_keeps_original_public_route() {
    let names: Vec<String> = (0..128).map(|index| format!("a{index}")).collect();
    let mut conjuncts = vec![ChcExpr::eq(array(&names[0]), constant(7))];
    for pair in names.windows(2) {
        // The source walk visits the last definition first, so this also
        // exercises bounded fixpoint replay in the unfavorable order.
        conjuncts.push(ChcExpr::eq(array(&pair[1]), array(&pair[0])));
    }
    let original = ChcExpr::and_all(conjuncts);
    let model = reconstruct(&original, FxHashMap::default(), &mut || true)
        .expect("128 grounded aliases fit the unchanged shared logical cap");
    assert_eq!(model.len(), 128);
    for name in &names {
        assert_eq!(
            model.get(name),
            Some(&SmtValue::ConstArray(Box::new(SmtValue::Int(7))))
        );
    }
    assert_eq!(
        verify_sat_model_strict(&original, &model),
        ModelVerifyResult::Valid
    );
    // 386 source occurrences and 128 two-node constant-array values made the
    // old global square exceed the cap despite O(1) local comparisons.
    let global_carrier = 128usize * 2 + 1;
    let old_global_price = 386usize * (386 + global_carrier * global_carrier);
    assert!(old_global_price > crate::expr::MAX_PREPROCESSING_NODES);
    let SmtResult::Sat(published) =
        SmtContext::new().check_sat_with_timeout(&original, Duration::from_secs(5))
    else {
        panic!("the actual original-array route must preserve all 128 aliases");
    };
    assert_eq!(published.len(), 128);
    assert_eq!(
        verify_sat_model_strict(&original, &published),
        ModelVerifyResult::Valid
    );
}

#[test]
fn array_projection_drops_only_auxiliary_keys_and_keeps_refusals_and_scalar_models() {
    let original = ChcExpr::and_all([
        ChcExpr::eq(array("a"), array("b")),
        ChcExpr::eq(array("a"), constant(7)),
    ]);
    let candidate = || {
        let mut model = partial("a", SmtValue::ConstArray(Box::new(SmtValue::Int(7))));
        model.insert("__ay_aux_array".to_owned(), zero());
        model.insert(
            "__ay_aux_marker".to_owned(),
            SmtValue::Opaque("native metadata".to_owned()),
        );
        model.insert(
            "__ay_aux_datatype".to_owned(),
            SmtValue::Datatype("internal".to_owned(), vec![SmtValue::Int(0)]),
        );
        model
    };
    let calls = Cell::new(0usize);
    let projected = reconstruct(&original, candidate(), &mut || {
        calls.set(calls.get() + 1);
        true
    })
    .expect("only exact original array variables remain");
    assert_eq!(projected.len(), 2);
    assert!(projected.contains_key("a") && projected.contains_key("b"));
    assert_eq!(
        verify_sat_model_strict(&original, &projected),
        ModelVerifyResult::Valid
    );
    // Dropping auxiliaries never hides an incorrect ORIGINAL binding.
    let mut wrong = candidate();
    wrong.insert("a".to_owned(), zero());
    assert!(reconstruct(&original, wrong, &mut || true).is_none());
    let mut deep = SmtValue::Int(0);
    for _ in 0..crate::expr::MAX_EXPR_RECURSION_DEPTH / 2 {
        deep = SmtValue::ConstArray(Box::new(deep));
    }
    let mut malformed_cleanup = candidate();
    malformed_cleanup.insert("__ay_aux_deep".to_owned(), deep);
    assert!(
        reconstruct(&original, malformed_cleanup, &mut || true).is_none(),
        "foreign cleanup depth is admitted before destructive projection"
    );
    let mut oversized_cleanup = candidate();
    oversized_cleanup.insert(
        "__ay_aux_large".to_owned(),
        SmtValue::Opaque("x".repeat(crate::expr::MAX_PREPROCESSING_NODES)),
    );
    assert!(
        reconstruct(&original, oversized_cleanup, &mut || true).is_none(),
        "foreign payload cannot bypass the unchanged shared logical cap"
    );
    for stop in 1..=calls.get() {
        let mut actual = 0;
        assert!(reconstruct(&original, candidate(), &mut || {
            actual += 1;
            actual != stop
        })
        .is_none());
        assert_eq!(actual, stop, "projection never re-enters a refused owner");
    }
    let scalar = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("i", ChcSort::Int)),
        ChcExpr::Int(1),
    );
    let mut model = partial("i", SmtValue::Int(1));
    model.insert("__scalar_aux".to_owned(), SmtValue::Int(2));
    let SmtResult::Sat(unchanged) = SmtContext::new().restore_preprocessed_array_model(
        &scalar,
        SmtResult::Sat(model),
        Instant::now(),
        None,
    ) else {
        panic!("healthy scalar/no-array model behavior is unchanged");
    };
    assert_eq!(unchanged.len(), 2);
    assert_eq!(unchanged.get("__scalar_aux"), Some(&SmtValue::Int(2)));
}

mod scalar_candidates;
