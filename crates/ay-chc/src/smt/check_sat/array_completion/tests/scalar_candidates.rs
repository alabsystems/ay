// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Candidate defaults never authorize an original array witness by themselves.

use super::*;
use num_bigint::BigUint;
use num_rational::BigRational;
use std::sync::Arc;

fn scalar(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, sort))
}

fn bv_array(name: &str) -> ChcExpr {
    scalar(
        name,
        ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::BitVec(32))),
    )
}

fn bv_compare(op: ChcOp, left: ChcExpr, right: ChcExpr) -> ChcExpr {
    ChcExpr::Op(op, vec![left.into(), right.into()])
}

/// A source-derived reduced shape, NOT a recovered raw consumer transaction.
/// The fixed-201 bounds failure precedes the store that would use x, while
/// relation threading transports x through positive scalar alias equalities.
fn bounds_201() -> ChcExpr {
    let i = scalar("entry_i", ChcSort::BitVec(8));
    let threaded_i = scalar("body_i", ChcSort::BitVec(8));
    let x = scalar("entry_x", ChcSort::BitVec(32));
    let threaded_x = scalar("body_x", ChcSort::BitVec(32));
    ChcExpr::and_all([
        ChcExpr::eq(
            bv_array("entry_a"),
            ChcExpr::const_array(ChcSort::BitVec(64), ChcExpr::BitVec(7, 32)),
        ),
        ChcExpr::eq(bv_array("entry_a"), bv_array("body_a")),
        ChcExpr::eq(i.clone(), threaded_i.clone()),
        ChcExpr::eq(x, threaded_x),
        bv_compare(ChcOp::BvULt, i, ChcExpr::BitVec(201, 8)),
        ChcExpr::not(bv_compare(
            ChcOp::BvULt,
            threaded_i,
            ChcExpr::BitVec(200, 8),
        )),
    ])
}

#[test]
fn actual_bounds_201_shape_returns_original_free_scalar_aliases() {
    let original = bounds_201();
    let SmtResult::Sat(model) =
        SmtContext::new().check_sat_with_timeout(&original, Duration::from_secs(10))
    else {
        panic!("a bounds witness must include the transported unconstrained x class");
    };
    assert_eq!(model.len(), 6);
    assert_eq!(model.get("entry_i"), Some(&SmtValue::BitVec(200, 8)));
    assert_eq!(model.get("body_i"), model.get("entry_i"));
    assert!(matches!(
        model.get("entry_x"),
        Some(SmtValue::BitVec(_, 32))
    ));
    assert_eq!(model.get("body_x"), model.get("entry_x"));
    assert_eq!(model.get("body_a"), model.get("entry_a"));
    assert_eq!(
        verify_sat_model_strict(&original, &model),
        ModelVerifyResult::Valid
    );
}

#[test]
fn actual_grounded_array_query_restores_an_unanchored_scalar_class() {
    let original = ChcExpr::and_all([
        ChcExpr::eq(array("a"), constant(7)),
        ChcExpr::eq(array("a"), array("b")),
        ChcExpr::eq(scalar("x", ChcSort::Int), scalar("y", ChcSort::Int)),
    ]);
    let SmtResult::Sat(model) =
        SmtContext::new().check_sat_with_timeout(&original, Duration::from_secs(10))
    else {
        panic!("eliminated unconstrained scalars must not hide a grounded array witness");
    };
    assert_eq!(model.len(), 4);
    assert!(model.contains_key("x") && model.contains_key("y"));
    assert_eq!(model.get("x"), model.get("y"));
    assert_eq!(model.get("a"), model.get("b"));
    assert_eq!(
        verify_sat_model_strict(&original, &model),
        ModelVerifyResult::Valid
    );
}

#[test]
fn actual_distinct_reads_require_nonconstant_original_array_witness() {
    let i = scalar("i", ChcSort::BitVec(64));
    let j = scalar("j", ChcSort::BitVec(64));
    let original = ChcExpr::and_all([
        ChcExpr::eq(bv_array("a"), bv_array("threaded_a")),
        ChcExpr::eq(i.clone(), ChcExpr::BitVec(0, 64)),
        ChcExpr::eq(j.clone(), ChcExpr::BitVec(1, 64)),
        ChcExpr::ne(
            ChcExpr::select(bv_array("a"), i),
            ChcExpr::select(bv_array("threaded_a"), j),
        ),
    ]);
    let SmtResult::Sat(model) =
        SmtContext::new().check_sat_with_timeout(&original, Duration::from_secs(10))
    else {
        panic!("the two distinct reads cannot be witnessed by a constant array");
    };
    assert_eq!(model.len(), 4);
    assert!(matches!(model.get("a"), Some(SmtValue::ArrayMap { .. })));
    assert_eq!(model.get("a"), model.get("threaded_a"));
    let first = crate::expr::evaluate_expr(
        &ChcExpr::select(bv_array("a"), ChcExpr::BitVec(0, 64)),
        &model,
    );
    let second = crate::expr::evaluate_expr(
        &ChcExpr::select(bv_array("a"), ChcExpr::BitVec(1, 64)),
        &model,
    );
    assert!(first.is_some() && second.is_some());
    assert_ne!(first, second);
    assert_eq!(
        verify_sat_model_strict(&original, &model),
        ModelVerifyResult::Valid
    );
}

#[test]
fn typed_scalar_candidates_replay_store_definitions_without_array_defaults() {
    let cases = [
        (ChcSort::Bool, SmtValue::Bool(false)),
        (ChcSort::Int, SmtValue::Int(0)),
        (
            ChcSort::Real,
            SmtValue::Real(BigRational::from_integer(0.into())),
        ),
        (ChcSort::BitVec(1), SmtValue::BitVec(0, 1)),
        (ChcSort::BitVec(128), SmtValue::BitVec(0, 128)),
        (
            ChcSort::BitVec(129),
            SmtValue::BigBitVec(Arc::new(BigUint::from(0u8)), 129),
        ),
    ];
    for (sort, expected) in cases {
        let x = scalar("x", sort.clone());
        let y = scalar("y", sort.clone());
        let array_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(sort));
        let base = scalar("base", array_sort.clone());
        let a = scalar("a", array_sort);
        let original = ChcExpr::and_all([
            ChcExpr::eq(x.clone(), y),
            ChcExpr::eq(base.clone(), ChcExpr::const_array(ChcSort::Int, x.clone())),
            ChcExpr::eq(a, ChcExpr::store(base, ChcExpr::Int(0), x)),
        ]);
        let model = reconstruct(&original, FxHashMap::default(), &mut || true)
            .expect("scalar candidates make original array definitions evaluable");
        assert_eq!(model.len(), 4);
        assert_eq!(model.get("x"), Some(&expected));
        assert_eq!(model.get("y"), Some(&expected));
        assert_eq!(
            model.get("base"),
            Some(&SmtValue::ConstArray(Box::new(expected)))
        );
        assert!(model.contains_key("a"));
        assert_eq!(
            verify_sat_model_strict(&original, &model),
            ModelVerifyResult::Valid
        );
    }
}

#[test]
fn scalar_candidates_do_not_overwrite_anchors_or_authorize_changed_original() {
    let x = scalar("x", ChcSort::Int);
    let y = scalar("y", ChcSort::Int);
    let original = ChcExpr::and_all([
        ChcExpr::eq(array("a"), constant(7)),
        ChcExpr::eq(x.clone(), y.clone()),
        ChcExpr::eq(x.clone(), ChcExpr::Int(9)),
    ]);
    let model = reconstruct(&original, partial("x", SmtValue::Int(9)), &mut || true)
        .expect("forced scalar anchors are preserved before default candidates");
    assert_eq!(model.get("x"), Some(&SmtValue::Int(9)));
    assert_eq!(model.get("y"), Some(&SmtValue::Int(9)));
    assert!(reconstruct(&original, partial("x", SmtValue::Int(8)), &mut || true).is_none());
    let changed = ChcExpr::and_all([
        ChcExpr::eq(array("a"), constant(7)),
        ChcExpr::eq(x.clone(), y),
        ChcExpr::ne(x, ChcExpr::Int(0)),
    ]);
    assert!(
        reconstruct(&changed, FxHashMap::default(), &mut || true).is_none(),
        "zero is only a candidate; a false ORIGINAL constraint must refuse"
    );
}

#[test]
fn scalar_candidates_preserve_missing_array_payload_and_homonym_refusals() {
    let x = scalar("x", ChcSort::Int);
    let y = scalar("y", ChcSort::Int);
    let missing = ChcExpr::and_all([
        ChcExpr::eq(array("a"), array("b")),
        ChcExpr::eq(x.clone(), y.clone()),
    ]);
    assert!(reconstruct(&missing, FxHashMap::default(), &mut || true).is_none());
    let homonym = ChcExpr::and_all([
        ChcExpr::eq(array("same"), constant(7)),
        ChcExpr::eq(scalar("same", ChcSort::Int), x.clone()),
    ]);
    assert!(reconstruct(&homonym, FxHashMap::default(), &mut || true).is_none());
    for width in [0, crate::MAX_BITVECTOR_WIDTH + 1] {
        let malformed = ChcExpr::and_all([
            ChcExpr::eq(array("a"), constant(7)),
            ChcExpr::eq(
                scalar("bad", ChcSort::BitVec(width)),
                scalar("other", ChcSort::BitVec(width)),
            ),
        ]);
        assert!(reconstruct(&malformed, FxHashMap::default(), &mut || true).is_none());
    }
    let original = ChcExpr::and_all([
        ChcExpr::eq(array("a"), constant(7)),
        ChcExpr::eq(x.clone(), y),
    ]);
    assert!(reconstruct(&original, partial("x", SmtValue::Bool(false)), &mut || true).is_none());
    let oversized = scalar(
        &"x".repeat(crate::expr::MAX_PREPROCESSING_NODES),
        ChcSort::Int,
    );
    let original = ChcExpr::and_all([
        ChcExpr::eq(array("a"), constant(7)),
        ChcExpr::eq(oversized, x),
    ]);
    assert!(reconstruct(&original, FxHashMap::default(), &mut || true).is_none());
}

#[test]
fn scalar_candidate_admission_precedes_creation_and_shares_sticky_stop() {
    let var = ChcVar::new("x", ChcSort::Real);
    let source = Source {
        variables: FxHashMap::from_iter([("x", &var)]),
        bindings: Vec::new(),
    };
    let mut model = FxHashMap::default();
    let mut live = || true;
    let mut budget = Budget {
        remaining: 4,
        poll: &mut live,
    };
    assert!(propose_missing_scalars(&source, &mut model, &mut budget).is_none());
    assert!(
        model.is_empty(),
        "insufficient logical admission inserts nothing"
    );
    let original = bounds_201();
    let seed = || {
        let mut model = partial("entry_i", SmtValue::BitVec(200, 8));
        model.insert(
            "entry_a".to_owned(),
            SmtValue::ConstArray(Box::new(SmtValue::BitVec(7, 32))),
        );
        model
    };
    let calls = Cell::new(0usize);
    let completed = reconstruct(&original, seed(), &mut || {
        calls.set(calls.get() + 1);
        true
    })
    .expect("the deliberately partial model requires scalar candidates");
    assert_eq!(completed.get("entry_x"), Some(&SmtValue::BitVec(0, 32)));
    assert_eq!(completed.get("body_x"), completed.get("entry_x"));
    assert_eq!(
        verify_sat_model_strict(&original, &completed),
        ModelVerifyResult::Valid
    );
    for stop in 1..=calls.get() {
        let mut actual = 0;
        assert!(reconstruct(&original, seed(), &mut || {
            actual += 1;
            actual != stop
        })
        .is_none());
        assert_eq!(actual, stop, "no callback reentry after candidate refusal");
    }
    let context = SmtContext::new();
    let result = context.restore_preprocessed_array_model(
        &original,
        SmtResult::Sat(seed()),
        Instant::now(),
        Some(Duration::ZERO),
    );
    assert!(matches!(result, SmtResult::Unknown));
}

// The historical name is not a sort restriction: equality propagation
// recovers ANY missing evaluable binding, including explicitly defined arrays.
// Only unconstrained candidate defaults remain scalar-only.
fn check_legacy_completion_contract(original: &ChcExpr) {
    let (completed, _) = super::super::super::complete_model_with_scalar_defaults(
        std::iter::once(original),
        &FxHashMap::default(),
    )
    .expect("missing original bindings must be recovered");
    assert_eq!(completed.len(), 4);
    let array_value = SmtValue::ConstArray(Box::new(SmtValue::Int(7)));
    assert_eq!(completed.get("a"), Some(&array_value));
    assert_eq!(completed.get("b"), Some(&array_value));
    assert_eq!(completed.get("x"), Some(&SmtValue::Int(0)));
    assert_eq!(completed.get("y"), Some(&SmtValue::Int(0)));
    assert_eq!(
        verify_sat_model_strict(original, &completed),
        ModelVerifyResult::Valid
    );

    let free = ChcExpr::and_all([
        ChcExpr::eq(array("free_a"), array("free_b")),
        ChcExpr::eq(scalar("x", ChcSort::Int), scalar("y", ChcSort::Int)),
    ]);
    let (still_missing, _) = super::super::super::complete_model_with_scalar_defaults(
        std::iter::once(&free),
        &FxHashMap::default(),
    )
    .expect("only scalar candidate defaults exist for this free-array source");
    assert!(!still_missing.contains_key("free_a") && !still_missing.contains_key("free_b"));
    assert_eq!(
        verify_sat_model_strict(&free, &still_missing),
        ModelVerifyResult::Indeterminate
    );
    assert!(reconstruct(&free, still_missing, &mut || true).is_none());

    let mut wrong = completed;
    wrong.insert("a".to_owned(), SmtValue::Bool(false));
    assert_ne!(
        verify_sat_model_strict(original, &wrong),
        ModelVerifyResult::Valid
    );
    assert!(matches!(
        SmtContext::new().restore_preprocessed_array_model(
            original,
            SmtResult::Sat(wrong),
            Instant::now(),
            None,
        ),
        SmtResult::Unknown
    ));
}

// An empty reconstruction candidate and a fresh public solve are different
// contracts: only the latter can supply a genuinely assigned free array.
fn check_free_array_candidate_contract() {
    let original = ChcExpr::and_all([
        ChcExpr::eq(array("a"), array("a")),
        ChcExpr::eq(scalar("x", ChcSort::Int), scalar("y", ChcSort::Int)),
    ]);
    assert!(matches!(
        original.propagate_constants(),
        ChcExpr::Bool(true)
    ));
    assert!(reconstruct(&original, FxHashMap::default(), &mut || true).is_none());
    assert!(matches!(
        SmtContext::new().finish_trivial_preprocessed_candidate(
            &original,
            FxHashMap::default(),
            "constant propagation",
            Instant::now(),
            None,
        ),
        SmtResult::Unknown
    ));

    let actual = SmtContext::new().check_sat_with_timeout(&original, Duration::from_secs(10));
    let SmtResult::Sat(model) = &actual else {
        panic!("the public solve must return a complete original array witness: {actual:?}");
    };
    assert_eq!(model.len(), 3, "actual original model: {model:?}");
    let mut live = || true;
    let mut budget = Budget {
        remaining: crate::expr::MAX_PREPROCESSING_NODES,
        poll: &mut live,
    };
    for variable in original.vars() {
        let value = model
            .get(&variable.name)
            .unwrap_or_else(|| panic!("missing original binding {}: {model:?}", variable.name));
        assert!(
            super::super::values::typed(value, &variable.sort, &mut budget).is_some(),
            "wrong original carrier for {}: {model:?}",
            variable.name,
        );
    }
    assert_eq!(model.get("x"), model.get("y"));
    assert_eq!(
        verify_sat_model_strict(&original, model),
        ModelVerifyResult::Valid,
        "actual original model: {model:?}",
    );

    let changed = ChcExpr::and_all([
        original.clone(),
        ChcExpr::ne(scalar("x", ChcSort::Int), scalar("y", ChcSort::Int)),
    ]);
    assert_eq!(
        verify_sat_model_strict(&changed, model),
        ModelVerifyResult::Invalid
    );
    assert!(reconstruct(&changed, model.clone(), &mut || true).is_none());
    assert!(reconstruct(&original, model.clone(), &mut || false).is_none());
}

#[test]
fn trivial_array_candidate_composition_precedes_the_scalar_only_gate() {
    let original = ChcExpr::and_all([
        ChcExpr::eq(array("a"), constant(7)),
        ChcExpr::eq(array("a"), array("b")),
        ChcExpr::eq(scalar("x", ChcSort::Int), scalar("y", ChcSort::Int)),
    ]);
    check_legacy_completion_contract(&original);
    let context = SmtContext::new();
    for source in [
        "constant propagation",
        "empty conjuncts",
        "all-true conjuncts",
    ] {
        let SmtResult::Sat(model) = context.finish_trivial_preprocessed_candidate(
            &original,
            FxHashMap::default(),
            source,
            Instant::now(),
            None,
        ) else {
            panic!("positive candidate composition must restore arrays before scalar refusal");
        };
        assert_eq!(model.len(), 4);
        assert_eq!(model.get("x"), Some(&SmtValue::Int(0)));
        assert_eq!(model.get("y"), Some(&SmtValue::Int(0)));
        assert_eq!(
            verify_sat_model_strict(&original, &model),
            ModelVerifyResult::Valid
        );
    }
    check_free_array_candidate_contract();
    let expired = context.finish_trivial_preprocessed_candidate(
        &original,
        FxHashMap::default(),
        "constant propagation",
        Instant::now(),
        Some(Duration::ZERO),
    );
    assert!(matches!(expired, SmtResult::Unknown));
    assert!(matches!(
        context.restore_preprocessed_array_model(
            &original,
            SmtResult::Unknown,
            Instant::now(),
            None
        ),
        SmtResult::Unknown
    ));
    assert!(matches!(
        context.restore_preprocessed_array_model(&original, SmtResult::Unsat, Instant::now(), None),
        SmtResult::Unsat
    ));
}
