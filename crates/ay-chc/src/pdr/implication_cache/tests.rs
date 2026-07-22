// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{ChcSort, ChcVar};
use std::sync::Arc;

fn int_var(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::Int)
}

fn bool_var(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::Bool)
}

fn binary_op(op: ChcOp, left: ChcExpr, right: ChcExpr) -> ChcExpr {
    ChcExpr::Op(op, vec![Arc::new(left), Arc::new(right)])
}

#[test]
fn test_trusted_native_true_classifier_accepts_raw_bool_int_subset() {
    let x = ChcExpr::var(int_var("x"));
    let y = ChcExpr::var(int_var("y"));
    let b = ChcExpr::var(bool_var("b"));
    let c = ChcExpr::var(bool_var("c"));
    let y_le_10 = ChcExpr::le(y, ChcExpr::int(10));
    let iff = ChcExpr::Op(
        ChcOp::Iff,
        vec![
            Arc::new(y_le_10),
            Arc::new(ChcExpr::eq(c.clone(), ChcExpr::Bool(true))),
        ],
    );
    let formula = ChcExpr::and_vec(vec![
        ChcExpr::ge(x, ChcExpr::int(0)),
        ChcExpr::or(b.clone(), ChcExpr::not(c)),
        ChcExpr::implies(b, iff),
    ]);

    assert!(
        trusted_native_true_formula(&formula),
        "raw Bool/Int leaves, boolean connectives, and raw comparisons should be trusted"
    );
}

#[test]
fn test_trusted_native_true_classifier_rejects_composite_and_high_risk_terms() {
    let x = ChcExpr::var(int_var("x"));
    let arithmetic = ChcExpr::eq(ChcExpr::add(x.clone(), ChcExpr::int(1)), ChcExpr::int(2));
    assert!(
        !trusted_native_true_formula(&arithmetic),
        "arithmetic inside a comparison must not be trusted"
    );

    let ite = ChcExpr::ite(
        ChcExpr::Bool(true),
        ChcExpr::ge(x.clone(), ChcExpr::int(0)),
        ChcExpr::Bool(false),
    );
    assert!(
        !trusted_native_true_formula(&ite),
        "ITE stays outside the trusted-native-true grammar"
    );

    let bv = ChcExpr::eq(ChcExpr::BitVec(1, 1), ChcExpr::BitVec(1, 1));
    assert!(
        !trusted_native_true_formula(&bv),
        "bitvector terms are high-risk for CHC native true trust"
    );

    let bool_x = ChcExpr::var(bool_var("x"));
    let sort_collision = ChcExpr::and(bool_x, ChcExpr::ge(x, ChcExpr::int(0)));
    assert!(
        !trusted_native_true_formula(&sort_collision),
        "a variable name used at both Bool and Int sort must fail closed"
    );
}

#[test]
fn test_native_code_helper_competition_modes_control_dispatch() {
    // Default (no env) is ON again: the #18 pc==lr==fp crash class was
    // root-caused to the aarch64 expr-eval codegen's unbalanced register
    // spill (fixed by positional register allocation + the fail-closed
    // peak-depth gate in ay_jit::expr_eval), not to JIT slot ownership.
    assert!(native_code_helpers_enabled_for_modes(None, None));
    assert!(native_code_helpers_enabled_for_modes(None, Some("current")));
    assert!(!native_code_helpers_enabled_for_modes(None, Some("off")));
    assert!(!native_code_helpers_enabled_for_modes(
        None,
        Some("profile-only")
    ));
    assert!(!native_code_helpers_enabled_for_modes(
        None,
        Some("solver-program")
    ));
    assert!(
        !native_code_helpers_enabled_for_modes(None, Some("future-mode")),
        "unsupported competition JIT modes must fail closed"
    );

    assert!(native_code_helpers_enabled_for_modes(Some("on"), None));
    assert!(!native_code_helpers_enabled_for_modes(
        Some("disabled"),
        None
    ));
    assert!(
        !native_code_helpers_enabled_for_modes(Some("enabled-typo"), None),
        "unsupported explicit helper modes must fail closed"
    );
    assert!(native_code_helpers_enabled_for_modes(
        Some("disabled"),
        Some("current")
    ));
    assert!(!native_code_helpers_enabled_for_modes(
        Some("on"),
        Some("off")
    ));
}

#[test]
#[cfg(target_arch = "x86_64")]
fn test_x86_64_native_helper_requires_reuse_before_compile() {
    assert_eq!(JIT_COMPILE_THRESHOLD, 4);
}

#[test]
#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
fn test_jit_compile_caches_trusted_native_true_classification() {
    let mut cache = ImplicationCache::new();
    let x = ChcExpr::var(int_var("x"));

    let trusted_formula = ChcExpr::ge(x.clone(), ChcExpr::int(0));
    let trusted_hash = trusted_formula.structural_hash();
    cache.try_jit_compile(trusted_hash, &trusted_formula);
    assert!(
        matches!(
            cache.jit_cache.get(&trusted_hash),
            Some(Some(cached)) if cached.trusted_native_true
        ),
        "raw Int comparison should store a trusted native-true classification"
    );

    let untrusted_formula = ChcExpr::eq(ChcExpr::add(x, ChcExpr::int(1)), ChcExpr::int(2));
    let untrusted_hash = untrusted_formula.structural_hash();
    cache.try_jit_compile(untrusted_hash, &untrusted_formula);
    assert!(
        matches!(
            cache.jit_cache.get(&untrusted_hash),
            Some(Some(cached)) if !cached.trusted_native_true
        ),
        "arithmetic comparison should store an untrusted native-true classification"
    );
}

#[test]
fn test_small_model_evaluate_int() {
    let mut int_assignments = FxHashMap::default();
    int_assignments.insert("x".to_string(), 5);
    int_assignments.insert("y".to_string(), 3);
    let model = SmallModel {
        projection_id: 0,
        int_assignments,
        bool_assignments: FxHashMap::default(),
    };
    let x = ChcExpr::var(int_var("x"));
    let y = ChcExpr::var(int_var("y"));
    assert_eq!(
        model.evaluate_int(&ChcExpr::add(x.clone(), y.clone())),
        Some(8)
    );
    assert_eq!(
        model.evaluate(&ChcExpr::gt(x.clone(), y.clone())),
        Some(true)
    );
    assert_eq!(model.evaluate(&ChcExpr::lt(x, y)), Some(false));
}

#[test]
fn test_small_model_evaluate_int_euclidean_div() {
    // SMT-LIB div is Euclidean: result rounds toward -infinity, remainder is non-negative.
    let mut int_assignments = FxHashMap::default();
    int_assignments.insert("a".to_string(), -7);
    int_assignments.insert("b".to_string(), 2);
    int_assignments.insert("c".to_string(), 7);
    int_assignments.insert("d".to_string(), -2);
    let model = SmallModel {
        projection_id: 0,
        int_assignments,
        bool_assignments: FxHashMap::default(),
    };
    let a = ChcExpr::var(int_var("a"));
    let b = ChcExpr::var(int_var("b"));
    let c = ChcExpr::var(int_var("c"));
    let d = ChcExpr::var(int_var("d"));

    // div(-7, 2) = -4 (Euclidean), not -3 (truncation)
    assert_eq!(
        model.evaluate_int(&ChcExpr::Op(
            ChcOp::Div,
            vec![Arc::new(a.clone()), Arc::new(b.clone())]
        )),
        Some(-4)
    );
    // div(7, -2) = -3
    assert_eq!(
        model.evaluate_int(&ChcExpr::Op(
            ChcOp::Div,
            vec![Arc::new(c), Arc::new(d.clone())]
        )),
        Some(-3)
    );
    // div(-7, -2) = 4 (Euclidean), not 3 (truncation)
    assert_eq!(
        model.evaluate_int(&ChcExpr::Op(
            ChcOp::Div,
            vec![Arc::new(a.clone()), Arc::new(d)]
        )),
        Some(4)
    );
    // mod(-7, 2) = 1 (Euclidean, always non-negative), not -1 (truncation)
    assert_eq!(
        model.evaluate_int(&ChcExpr::Op(
            ChcOp::Mod,
            vec![Arc::new(a.clone()), Arc::new(b)]
        )),
        Some(1)
    );
    // div by zero returns None
    let zero = ChcExpr::int(0);
    assert_eq!(
        model.evaluate_int(&ChcExpr::Op(ChcOp::Div, vec![Arc::new(a), Arc::new(zero)])),
        None
    );
}

#[test]
fn test_small_model_from_smt_model() {
    let mut smt_model = FxHashMap::default();
    smt_model.insert("a".to_string(), SmtValue::Int(10));
    smt_model.insert("b".to_string(), SmtValue::Bool(true));
    let model = SmallModel::from_smt_model(&smt_model);
    assert_eq!(model.int_assignments.get("a"), Some(&10));
    assert_eq!(model.bool_assignments.get("b"), Some(&true));
}

#[test]
fn test_implication_cache_hit() {
    let mut cache = ImplicationCache::new();
    let x = ChcExpr::var(int_var("x"));
    let ant = ChcExpr::ge(x.clone(), ChcExpr::int(0));
    let cons = ChcExpr::ge(x, ChcExpr::int(-1));
    cache.record_result(&ant, &cons, ImplicationResult::Valid, None);
    assert_eq!(
        cache.check_with_hints(&ant, &cons),
        Some(ImplicationResult::Valid)
    );
    assert_eq!(cache.cache_hits, 1);
}

#[test]
fn test_implication_cache_model_rejection() {
    let mut cache = ImplicationCache::new();
    let x = ChcExpr::var(int_var("x"));
    let ant = ChcExpr::ge(x.clone(), ChcExpr::int(0));
    let mut countermodel = FxHashMap::default();
    countermodel.insert("x".to_string(), SmtValue::Int(0));
    let cons1 = ChcExpr::gt(x.clone(), ChcExpr::int(0));
    cache.record_result(
        &ant,
        &cons1,
        ImplicationResult::Invalid,
        Some(&countermodel),
    );
    let cons2 = ChcExpr::gt(x.clone(), ChcExpr::int(-1));
    assert_eq!(cache.check_with_hints(&ant, &cons2), None);
    let cons3 = ChcExpr::ge(x, ChcExpr::int(1));
    assert_eq!(
        cache.check_with_hints(&ant, &cons3),
        Some(ImplicationResult::Invalid)
    );
    assert_eq!(cache.model_rejections, 1);
}

#[test]
fn test_implication_cache_clear() {
    let mut cache = ImplicationCache::new();
    let x = ChcExpr::var(int_var("x"));
    let ant = ChcExpr::ge(x.clone(), ChcExpr::int(0));
    let cons = ChcExpr::ge(x, ChcExpr::int(-1));
    cache.record_result(&ant, &cons, ImplicationResult::Valid, None);
    assert_eq!(cache.result_cache.len(), 1);
    cache.clear();
    assert_eq!(cache.result_cache.len(), 0);
    assert_eq!(cache.implication_countermodels.len(), 0);
    assert_eq!(cache.blocking_countermodels.len(), 0);
}

#[test]
fn test_implication_cache_respects_max_models() {
    // Test with custom max_models limit of 4
    let max = 4;
    let mut cache = ImplicationCache::with_max_models(max);
    let x = ChcExpr::var(int_var("x"));
    let ant = ChcExpr::ge(x.clone(), ChcExpr::int(0));

    // Add more than max models for same antecedent
    for i in 0..=(max + 2) {
        let mut model = FxHashMap::default();
        model.insert("x".to_string(), SmtValue::Int(i as i128));
        let cons = ChcExpr::gt(x.clone(), ChcExpr::int(i as i64));
        cache.record_result(&ant, &cons, ImplicationResult::Invalid, Some(&model));
    }

    // Verify only max models are stored (via stats)
    let stats = cache.stats();
    assert_eq!(
        stats.countermodel_count, max,
        "Expected exactly {} models, got {}",
        max, stats.countermodel_count
    );
}

#[test]
fn test_blocking_cache_respects_max_models() {
    // Test blocking API's model limit
    let max = 4;
    let mut cache = ImplicationCache::with_max_models(max);

    // Add more than max models for same (predicate, level)
    for i in 0..=(max + 2) {
        let mut model = FxHashMap::default();
        model.insert("x".to_string(), SmtValue::Int(i as i128));
        cache.record_blocking_countermodel(0, 1, &model);
    }

    // Verify only max models are stored (via stats)
    let stats = cache.stats();
    assert_eq!(
        stats.countermodel_count, max,
        "Expected exactly {} models, got {}",
        max, stats.countermodel_count
    );
}

#[test]
fn test_blocking_cache_model_rejection() {
    // Test the blocking-specific API (used in PDR push phase)
    let mut cache = ImplicationCache::new();

    // Record a model where x=5
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    cache.record_blocking_countermodel(0, 1, &model);

    // Formula x >= 5 should be rejected (satisfied by model where x=5)
    let x = ChcExpr::var(int_var("x"));
    let blocking1 = ChcExpr::ge(x.clone(), ChcExpr::int(5));
    assert!(
        cache.blocking_rejected_by_cache(0, 1, &blocking1),
        "Model x=5 should satisfy x >= 5"
    );

    // Formula x > 5 should NOT be rejected (model x=5 doesn't satisfy x > 5)
    let blocking2 = ChcExpr::gt(x, ChcExpr::int(5));
    assert!(
        !cache.blocking_rejected_by_cache(0, 1, &blocking2),
        "Model x=5 should not satisfy x > 5"
    );

    // Different predicate/level should not be affected
    assert!(
        !cache.blocking_rejected_by_cache(1, 1, &blocking1),
        "Different predicate should have no cached models"
    );
    assert!(
        !cache.blocking_rejected_by_cache(0, 2, &blocking1),
        "Different level should have no cached models"
    );
}

#[test]
fn test_blocking_cache_frame_epoch_invalidates_countermodels() {
    // #pdr-chain: countermodels are only valid relative to the frame state
    // they were recorded against. A frame-epoch change must drop them so
    // stale states cannot fast-reject lemmas that became inductive after the
    // frames were strengthened.
    let mut cache = ImplicationCache::new();
    cache.note_frame_epoch(1);

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    cache.record_blocking_countermodel(0, 1, &model);

    let x = ChcExpr::var(int_var("x"));
    let blocking = ChcExpr::ge(x, ChcExpr::int(5));
    assert!(
        cache.blocking_rejected_by_cache(0, 1, &blocking),
        "same epoch: cached model x=5 should reject x >= 5"
    );

    // Same epoch re-published: cache must survive.
    cache.note_frame_epoch(1);
    assert!(
        cache.blocking_rejected_by_cache(0, 1, &blocking),
        "re-publishing the same epoch must not clear the cache"
    );

    // Epoch changed (a lemma was added somewhere): stale models are dropped.
    cache.note_frame_epoch(2);
    assert!(
        !cache.blocking_rejected_by_cache(0, 1, &blocking),
        "epoch change must drop countermodels recorded against older frames"
    );
}

#[test]
fn test_blocking_cache_jit_deopts_on_missing_model_var() {
    let mut cache = ImplicationCache::new();

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    cache.record_blocking_countermodel(0, 1, &model);

    let mut complete_non_rejecting_model = FxHashMap::default();
    complete_non_rejecting_model.insert("y".to_string(), SmtValue::Int(1));
    cache.record_blocking_countermodel(0, 1, &complete_non_rejecting_model);

    // One cached model has no value for y. The JIT var array must not treat
    // that missing binding as y=0 and reject from cache after compilation.
    // The second model keeps this test on the native evaluation path while
    // still returning false for y == 0.
    let y = ChcExpr::var(int_var("y"));
    let formula = ChcExpr::eq(y, ChcExpr::int(0));

    for _ in 0..(JIT_COMPILE_THRESHOLD + 2) {
        assert!(
            !cache.blocking_rejected_by_cache(0, 1, &formula),
            "partial cached model must be skipped instead of defaulting y to 0"
        );
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    {
        assert_eq!(cache.jit_compile_attempts, 1);
        assert_eq!(cache.jit_compile_successes, 1);
        assert_eq!(cache.jit_compile_failures, 0);
        assert!(
            cache.jit_evaluations > 0,
            "expected test to exercise the native JIT path"
        );
        assert_eq!(cache.jit_missing_var_fallbacks, 0);
        assert_eq!(cache.jit_fallbacks, 0);
        assert_eq!(cache.native_helper_applications, 0);
        assert_eq!(cache.jit_trusted_true_results, 0);
        assert_eq!(cache.dense_projection_cache.len(), 2);
        assert!(cache
            .dense_projection_cache
            .values()
            .any(|projection| matches!(projection, DenseProjection::MissingVariable)));
        assert!(cache
            .dense_projection_cache
            .values()
            .any(|projection| matches!(projection, DenseProjection::Complete(_))));
    }
}

#[test]
fn test_blocking_cache_confirms_overflow_risk_before_rejecting() {
    let mut cache = ImplicationCache::new();

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(i128::from(i64::MAX)));
    cache.record_blocking_countermodel(0, 1, &model);

    // Native expression evaluation uses machine arithmetic. Composite
    // arithmetic formulas can run natively only when a native true result is
    // confirmed by the SmallModel oracle before rejecting from the cache.
    let x = ChcExpr::var(int_var("x"));
    let formula = ChcExpr::eq(ChcExpr::add(x, ChcExpr::int(1)), ChcExpr::int(i64::MIN));

    for _ in 0..(JIT_COMPILE_THRESHOLD + 2) {
        assert!(
            !cache.blocking_rejected_by_cache(0, 1, &formula),
            "overflow-risk formula must not reject from the cache"
        );
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    {
        assert_eq!(cache.jit_compile_attempts, 1);
        assert_eq!(cache.jit_compile_successes, 1);
        assert_eq!(cache.jit_compile_failures, 0);
        assert!(cache.jit_evaluations > 0);
        assert_eq!(cache.native_helper_applications, 0);
        assert!(cache.jit_interpreter_confirmations > 0);
        assert_eq!(cache.jit_trusted_true_results, 0);
        assert!(cache.jit_deopts > 0);
        assert!(cache.jit_fallbacks > 0);
    }
}

#[test]
fn test_blocking_cache_confirmed_arithmetic_native_true_counts_as_application() {
    let mut cache = ImplicationCache::new();

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(4));
    cache.record_blocking_countermodel(0, 1, &model);

    let x = ChcExpr::var(int_var("x"));
    let formula = ChcExpr::eq(ChcExpr::add(x, ChcExpr::int(1)), ChcExpr::int(5));

    for _ in 0..(JIT_COMPILE_THRESHOLD + 2) {
        assert!(
            cache.blocking_rejected_by_cache(0, 1, &formula),
            "confirmed arithmetic native true should reject from the blocking cache"
        );
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    {
        assert_eq!(cache.jit_compile_attempts, 1);
        assert_eq!(cache.jit_compile_successes, 1);
        assert!(cache.native_helper_applications > 0);
        assert_eq!(
            cache.native_helper_applications,
            cache.jit_interpreter_confirmations
        );
        assert_eq!(cache.jit_trusted_true_results, 0);
        assert_eq!(cache.jit_deopts, 0);
        assert_eq!(cache.jit_fallbacks, 0);
    }
}

#[test]
fn test_blocking_cache_native_false_does_not_count_as_application() {
    let mut cache = ImplicationCache::new();

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    cache.record_blocking_countermodel(0, 1, &model);

    let x = ChcExpr::var(int_var("x"));
    let formula = ChcExpr::gt(x, ChcExpr::int(5));

    for _ in 0..(JIT_COMPILE_THRESHOLD + 2) {
        assert!(
            !cache.blocking_rejected_by_cache(0, 1, &formula),
            "native false should not reject from the blocking cache"
        );
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    {
        assert_eq!(cache.jit_compile_attempts, 1);
        assert_eq!(cache.jit_compile_successes, 1);
        assert_eq!(cache.native_helper_applications, 0);
        assert_eq!(cache.jit_deopts, 0);
        assert_eq!(cache.jit_fallbacks, 0);
    }
}

#[test]
fn test_blocking_cache_native_indeterminate_does_not_count_as_application() {
    let mut cache = ImplicationCache::new();

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    cache.record_blocking_countermodel(0, 1, &model);

    let formula = ChcExpr::int(1);

    for _ in 0..(JIT_COMPILE_THRESHOLD + 2) {
        assert!(
            !cache.blocking_rejected_by_cache(0, 1, &formula),
            "non-boolean formula should stay off the native helper path"
        );
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    {
        assert_eq!(cache.jit_compile_attempts, 0);
        assert_eq!(cache.jit_compile_successes, 0);
        assert_eq!(cache.jit_evaluations, 0);
        assert_eq!(cache.native_helper_applications, 0);
        assert_eq!(cache.jit_deopts, 0);
        assert_eq!(cache.jit_fallbacks, 0);
    }
}

#[test]
fn test_blocking_cache_accepted_native_true_counts_as_application() {
    let mut cache = ImplicationCache::new();

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    cache.record_blocking_countermodel(0, 1, &model);

    let x = ChcExpr::var(int_var("x"));
    let formula = ChcExpr::ge(x, ChcExpr::int(5));

    for _ in 0..(JIT_COMPILE_THRESHOLD + 2) {
        assert!(
            cache.blocking_rejected_by_cache(0, 1, &formula),
            "accepted native true should reject from the blocking cache"
        );
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    {
        assert_eq!(cache.jit_compile_attempts, 1);
        assert_eq!(cache.jit_compile_successes, 1);
        assert!(cache.native_helper_applications > 0);
        assert_eq!(
            cache.native_helper_applications,
            cache.jit_trusted_true_results
        );
        assert_eq!(cache.jit_deopts, 0);
        assert_eq!(cache.jit_fallbacks, 0);
    }
}

#[test]
#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
fn test_blocking_cache_reuses_dense_projection_for_same_mapping() {
    let mut cache = ImplicationCache::new();

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    cache.record_blocking_countermodel(0, 1, &model);

    let x = ChcExpr::var(int_var("x"));
    let lower_bound = ChcExpr::ge(x.clone(), ChcExpr::int(5));
    let upper_bound = ChcExpr::le(x, ChcExpr::int(10));

    for _ in 0..(JIT_COMPILE_THRESHOLD + 2) {
        assert!(cache.blocking_rejected_by_cache(0, 1, &lower_bound));
    }

    assert_eq!(cache.jit_compile_successes, 1);
    assert_eq!(cache.dense_projection_mapping_ids.len(), 1);
    assert_eq!(cache.dense_projection_cache.len(), 1);

    for _ in 0..(JIT_COMPILE_THRESHOLD + 2) {
        assert!(cache.blocking_rejected_by_cache(0, 1, &upper_bound));
    }

    assert_eq!(cache.jit_compile_successes, 2);
    assert_eq!(
        cache.dense_projection_mapping_ids.len(),
        1,
        "same variable mapping should reuse the mapping identity"
    );
    assert_eq!(
        cache.dense_projection_cache.len(),
        1,
        "same model and mapping identity should reuse one dense projection"
    );
}

#[test]
fn test_blocking_cache_div_mod_bypasses_native_helper() {
    let mut cache = ImplicationCache::new();

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(6));
    model.insert("y".to_string(), SmtValue::Int(3));
    cache.record_blocking_countermodel(0, 1, &model);

    let x = ChcExpr::var(int_var("x"));
    let y = ChcExpr::var(int_var("y"));
    let div = binary_op(ChcOp::Div, x.clone(), y.clone());
    let modulo = binary_op(ChcOp::Mod, x, y);
    let formula = ChcExpr::and(
        ChcExpr::eq(div, ChcExpr::int(2)),
        ChcExpr::eq(modulo, ChcExpr::int(0)),
    );
    let formula_hash = formula.structural_hash();

    for _ in 0..(JIT_COMPILE_THRESHOLD + 2) {
        assert!(
            cache.blocking_rejected_by_cache(0, 1, &formula),
            "div/mod formula should still be evaluated by SmallModel fallback"
        );
    }

    assert_eq!(
        cache.jit_evaluations, 0,
        "non-compilable div/mod formula must not enter the JIT evaluation path"
    );
    assert_eq!(cache.jit_compile_attempts, 0);
    assert_eq!(cache.jit_compile_successes, 0);
    assert_eq!(cache.jit_compile_failures, 0);
    assert_eq!(cache.jit_fallbacks, 0);
    assert!(
        !cache.jit_cache.contains_key(&formula_hash),
        "div/mod formula should bypass native-helper caching"
    );
}

#[test]
fn test_blocking_cache_div_mod_by_zero_does_not_reject() {
    let mut cache = ImplicationCache::new();

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(6));
    model.insert("z".to_string(), SmtValue::Int(0));
    cache.record_blocking_countermodel(0, 1, &model);

    let x = ChcExpr::var(int_var("x"));
    let z = ChcExpr::var(int_var("z"));
    let div_formula = ChcExpr::eq(binary_op(ChcOp::Div, x.clone(), z.clone()), ChcExpr::int(0));
    let mod_formula = ChcExpr::eq(binary_op(ChcOp::Mod, x, z), ChcExpr::int(0));

    for formula in [&div_formula, &mod_formula] {
        for _ in 0..(JIT_COMPILE_THRESHOLD + 2) {
            assert!(
                !cache.blocking_rejected_by_cache(0, 1, formula),
                "division or modulo by zero should be indeterminate, not a cache rejection"
            );
        }
        assert!(
            !cache.jit_cache.contains_key(&formula.structural_hash()),
            "div/mod by zero formula should bypass native-helper caching"
        );
    }

    assert_eq!(
        cache.jit_evaluations, 0,
        "div/mod by zero formulas must stay on the SmallModel fallback path"
    );
    assert_eq!(cache.model_rejections, 0);
    assert_eq!(cache.jit_compile_attempts, 0);
    assert_eq!(cache.jit_compile_successes, 0);
    assert_eq!(cache.jit_compile_failures, 0);
}

#[test]
fn test_stats_tracking() {
    let mut cache = ImplicationCache::new();
    let x = ChcExpr::var(int_var("x"));
    let ant = ChcExpr::ge(x.clone(), ChcExpr::int(0));

    // Initial stats
    let stats = cache.stats();
    assert_eq!(stats.cache_hits, 0);
    assert_eq!(stats.model_rejections, 0);
    assert_eq!(stats.solver_calls, 0);
    assert_eq!(stats.native_helper_applications, 0);

    // Record a result with countermodel
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(0));
    let cons = ChcExpr::gt(x.clone(), ChcExpr::int(0));
    cache.record_result(&ant, &cons, ImplicationResult::Invalid, Some(&model));

    let stats = cache.stats();
    assert_eq!(stats.solver_calls, 1);
    assert_eq!(stats.countermodel_count, 1);

    // Check with hints - cache hit
    let _ = cache.check_with_hints(&ant, &cons);
    let stats = cache.stats();
    assert_eq!(stats.cache_hits, 1);

    // New consequent rejected by cached model
    let cons2 = ChcExpr::ge(x, ChcExpr::int(1)); // x=0 doesn't satisfy x >= 1
    let _ = cache.check_with_hints(&ant, &cons2);
    let stats = cache.stats();
    assert_eq!(stats.model_rejections, 1);
}

#[test]
fn test_native_code_helper_statistics_snapshot() {
    let mut cache = ImplicationCache::new();

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    cache.record_blocking_countermodel(0, 1, &model);

    let x = ChcExpr::var(int_var("x"));
    let formula = ChcExpr::ge(x, ChcExpr::int(5));
    for _ in 0..(JIT_COMPILE_THRESHOLD + 2) {
        assert!(cache.blocking_rejected_by_cache(0, 1, &formula));
    }

    let stats = cache.native_code_helper_statistics();
    assert_eq!(stats.compile_attempts, 1);
    assert_eq!(stats.compile_successes, 1);
    assert_eq!(stats.compile_failures, 0);
    assert_eq!(stats.evaluations, cache.jit_evaluations as u64);
    assert_eq!(
        stats.interpreter_confirmations,
        cache.jit_interpreter_confirmations as u64
    );
    assert_eq!(
        stats.trusted_true_results,
        cache.jit_trusted_true_results as u64
    );
    assert_eq!(stats.applications, cache.native_helper_applications as u64);

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    {
        assert!(stats.evaluations > 0);
        assert!(stats.applications > 0);
        assert_eq!(stats.interpreter_confirmations, 0);
        assert_eq!(stats.trusted_true_results, stats.applications);
    }
}

#[test]
fn test_record_time_native_helper_requires_formula_reuse_before_dispatch() {
    let mut cache = ImplicationCache::with_max_models(1);

    for formula_idx in 0..10 {
        let name = format!("x{formula_idx}");
        let x = ChcExpr::var(int_var(&name));
        let formula = ChcExpr::ge(x, ChcExpr::int(0));
        for value in 0..(JIT_COMPILE_THRESHOLD - 1) {
            let mut model = FxHashMap::default();
            model.insert(name.clone(), SmtValue::Int(value as i128));
            cache.record_blocking_countermodel_with_native_helper_validation(
                formula_idx,
                1,
                &model,
                &formula,
            );
        }
    }

    let stats = cache.native_code_helper_statistics();
    assert_eq!(
        stats.compile_attempts, 0,
        "record-time helpers must not compile formulas without reuse evidence"
    );
    assert_eq!(stats.evaluations, 0);
    assert_eq!(stats.applications, 0);
    assert_eq!(stats.trusted_true_results, 0);
    assert_eq!(stats.interpreter_confirmations, 0);
}

#[test]
fn test_record_time_native_helper_requires_row_local_reuse_before_compile() {
    let mut cache = ImplicationCache::with_max_models(1);

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(7));
    let x = ChcExpr::var(int_var("x"));
    let formula = ChcExpr::ge(x, ChcExpr::int(5));

    for row in 0..(JIT_COMPILE_THRESHOLD * 3) {
        cache.record_blocking_countermodel_with_native_helper_validation(row, 1, &model, &formula);
        cache.record_blocking_countermodel_with_native_helper_validation(row, 1, &model, &formula);
    }

    let stats = cache.native_code_helper_statistics();
    assert_eq!(
        stats.compile_attempts, 0,
        "many cold saturated rows must not collectively admit record-time native compilation"
    );
    assert_eq!(stats.evaluations, 0);
    assert_eq!(stats.applications, 0);
    assert_eq!(cache.jit_eval_counts.get(&formula.structural_hash()), None);
    assert_eq!(cache.record_time_native_helper_compile_admissions, 0);
}

#[test]
fn test_record_time_native_helper_hot_row_admits_after_cold_rows() {
    let mut cache = ImplicationCache::with_max_models(1);

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(7));
    let x = ChcExpr::var(int_var("x"));
    let formula = ChcExpr::ge(x, ChcExpr::int(5));

    for row in 0..(JIT_COMPILE_THRESHOLD * 3) {
        cache.record_blocking_countermodel_with_native_helper_validation(row, 1, &model, &formula);
        cache.record_blocking_countermodel_with_native_helper_validation(row, 1, &model, &formula);
    }

    let hot_row = JIT_COMPILE_THRESHOLD * 4;
    cache.record_blocking_countermodel_with_native_helper_validation(hot_row, 1, &model, &formula);
    for _ in 0..JIT_COMPILE_THRESHOLD {
        cache.record_blocking_countermodel_with_native_helper_validation(
            hot_row, 1, &model, &formula,
        );
    }

    let stats = cache.native_code_helper_statistics();
    assert_eq!(
        stats.compile_attempts, 1,
        "a repeated saturated row should still admit one record-time native compile"
    );

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    {
        assert_eq!(stats.compile_successes, 1);
        assert_eq!(stats.evaluations, 1);
        assert_eq!(stats.applications, 1);
        assert_eq!(stats.trusted_true_results, 1);
        assert_eq!(stats.deopts, 0);
        assert_eq!(stats.fallbacks, 0);
    }
}

#[test]
fn test_record_time_native_helper_waits_for_saturated_slot_before_dispatch() {
    let mut cache = ImplicationCache::new();

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(7));
    let x = ChcExpr::var(int_var("x"));
    let formula = ChcExpr::ge(x, ChcExpr::int(5));

    for _ in 0..JIT_COMPILE_THRESHOLD {
        cache.record_blocking_countermodel_with_native_helper_validation(0, 1, &model, &formula);
    }

    let stats = cache.native_code_helper_statistics();
    assert_eq!(
        stats.compile_attempts, 0,
        "record-time helpers must not compile while the model slot can store directly"
    );
    assert_eq!(stats.evaluations, 0);
    assert_eq!(stats.applications, 0);
    assert_eq!(cache.jit_eval_counts.get(&formula.structural_hash()), None);
}

#[test]
fn test_record_blocking_countermodel_runs_validated_native_helper_slice() {
    let mut cache = ImplicationCache::with_max_models(1);

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(7));
    let x = ChcExpr::var(int_var("x"));
    let formula = ChcExpr::ge(x, ChcExpr::int(5));

    cache.record_blocking_countermodel_with_native_helper_validation(0, 1, &model, &formula);
    for _ in 0..(JIT_COMPILE_THRESHOLD - 1) {
        cache.record_blocking_countermodel_with_native_helper_validation(0, 1, &model, &formula);
    }

    let stats = cache.native_code_helper_statistics();
    assert_eq!(
        stats.compile_attempts, 0,
        "record-time validation waits for formula reuse before compiling"
    );
    assert_eq!(stats.evaluations, 0);
    assert_eq!(stats.applications, 0);

    cache.record_blocking_countermodel_with_native_helper_validation(0, 1, &model, &formula);

    let stats = cache.native_code_helper_statistics();
    assert_eq!(stats.compile_attempts, 1);

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    {
        assert_eq!(stats.compile_successes, 1);
        assert_eq!(stats.compile_failures, 0);
        assert_eq!(stats.evaluations, 1);
        assert_eq!(stats.applications, 1);
        assert_eq!(stats.interpreter_confirmations, 0);
        assert_eq!(stats.trusted_true_results, 1);
        assert_eq!(stats.deopts, 0);
        assert_eq!(stats.fallbacks, 0);
    }

    #[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
    {
        assert_eq!(stats.compile_successes, 0);
        assert_eq!(stats.compile_failures, 1);
        assert_eq!(stats.evaluations, 0);
        assert_eq!(stats.applications, 0);
        assert_eq!(stats.trusted_true_results, 0);
        assert!(stats.fallbacks > 0);
    }
}

#[test]
#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
fn test_record_blocking_countermodel_replaces_saturated_slot_after_native_true() {
    let mut cache = ImplicationCache::with_max_models(1);

    let x = ChcExpr::var(int_var("x"));
    let formula = ChcExpr::ge(x, ChcExpr::int(5));

    let mut first_model = FxHashMap::default();
    first_model.insert("x".to_string(), SmtValue::Int(7));
    for _ in 0..JIT_COMPILE_THRESHOLD {
        cache.record_blocking_countermodel_with_native_helper_validation(
            0,
            1,
            &first_model,
            &formula,
        );
    }

    let mut saturated_model = FxHashMap::default();
    saturated_model.insert("x".to_string(), SmtValue::Int(9));
    cache.record_blocking_countermodel_with_native_helper_validation(
        0,
        1,
        &saturated_model,
        &formula,
    );

    let stored_models = cache
        .blocking_countermodels
        .get(&(0, 1))
        .expect("replacement model should be stored");
    assert_eq!(stored_models.len(), 1, "store cap remains enforced");
    let stored_x = ChcExpr::var(int_var("x"));
    assert_eq!(
        stored_models[0].evaluate(&ChcExpr::eq(stored_x, ChcExpr::int(9))),
        Some(true),
        "helper-confirmed saturated model should replace the oldest slot"
    );

    let stats = cache.native_code_helper_statistics();
    assert_eq!(stats.compile_attempts, 1);
    assert_eq!(stats.compile_successes, 1);
    assert_eq!(stats.evaluations, 1);
    assert_eq!(stats.applications, 1);
    assert_eq!(stats.trusted_true_results, 1);
    assert_eq!(stats.deopts, 0);
    assert_eq!(stats.fallbacks, 0);
}

#[test]
#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
fn test_record_blocking_countermodel_does_not_replace_on_overflow_native_true() {
    let mut cache = ImplicationCache::with_max_models(1);

    let mut first_model = FxHashMap::default();
    first_model.insert("x".to_string(), SmtValue::Int(0));
    cache.record_blocking_countermodel(0, 1, &first_model);

    let mut overflow_model = FxHashMap::default();
    overflow_model.insert("x".to_string(), SmtValue::Int(i128::from(i64::MAX)));
    let x = ChcExpr::var(int_var("x"));
    let formula = ChcExpr::eq(ChcExpr::add(x, ChcExpr::int(1)), ChcExpr::int(i64::MIN));

    for _ in 0..JIT_COMPILE_THRESHOLD {
        cache.record_blocking_countermodel_with_native_helper_validation(
            0,
            1,
            &overflow_model,
            &formula,
        );
    }

    let stored_models = cache
        .blocking_countermodels
        .get(&(0, 1))
        .expect("original model should remain stored");
    assert_eq!(stored_models.len(), 1, "store cap remains enforced");
    let stored_x = ChcExpr::var(int_var("x"));
    assert_eq!(
        stored_models[0].evaluate(&ChcExpr::eq(stored_x, ChcExpr::int(0))),
        Some(true),
        "overflow-risk native true must not replace the stored model"
    );

    let stats = cache.native_code_helper_statistics();
    assert_eq!(stats.compile_attempts, 1);
    assert_eq!(stats.compile_successes, 1);
    assert_eq!(stats.applications, 0);
    assert_eq!(stats.trusted_true_results, 0);
    assert!(stats.interpreter_confirmations > 0);
    assert!(stats.deopts > 0);
    assert!(stats.fallbacks > 0);
}

#[test]
fn test_record_blocking_countermodel_validation_fails_closed_on_missing_var() {
    let mut cache = ImplicationCache::new();

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(7));
    let y = ChcExpr::var(int_var("y"));
    let formula = ChcExpr::ge(y, ChcExpr::int(5));

    for _ in 0..JIT_COMPILE_THRESHOLD {
        cache.record_blocking_countermodel_with_native_helper_validation(0, 1, &model, &formula);
    }

    let stats = cache.native_code_helper_statistics();
    assert_eq!(stats.compile_attempts, 0);
    assert_eq!(stats.compile_successes, 0);
    assert_eq!(stats.compile_failures, 0);
    assert_eq!(stats.evaluations, 0);
    assert_eq!(stats.applications, 0);
    assert_eq!(stats.trusted_true_results, 0);
    assert_eq!(cache.jit_eval_counts.get(&formula.structural_hash()), None);
    assert_eq!(cache.record_time_native_helper_compile_admissions, 0);

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    {
        assert_eq!(stats.missing_var_fallbacks, 0);
        assert_eq!(stats.fallbacks, 0);
    }
}

#[test]
fn test_record_blocking_countermodel_complete_model_admits_native_helper_after_missing_var() {
    let mut cache = ImplicationCache::with_max_models(1);

    let mut partial_model = FxHashMap::default();
    partial_model.insert("x".to_string(), SmtValue::Int(7));
    let y = ChcExpr::var(int_var("y"));
    let formula = ChcExpr::ge(y, ChcExpr::int(5));

    for _ in 0..JIT_COMPILE_THRESHOLD {
        cache.record_blocking_countermodel_with_native_helper_validation(
            0,
            1,
            &partial_model,
            &formula,
        );
    }
    assert_eq!(cache.jit_eval_counts.get(&formula.structural_hash()), None);

    let mut complete_model = FxHashMap::default();
    complete_model.insert("y".to_string(), SmtValue::Int(7));
    for _ in 0..JIT_COMPILE_THRESHOLD {
        cache.record_blocking_countermodel_with_native_helper_validation(
            0,
            1,
            &complete_model,
            &formula,
        );
    }

    let stats = cache.native_code_helper_statistics();
    assert_eq!(stats.compile_attempts, 1);

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    {
        assert_eq!(stats.compile_successes, 1);
        assert_eq!(stats.compile_failures, 0);
        assert_eq!(stats.evaluations, 1);
        assert_eq!(stats.applications, 1);
        assert_eq!(stats.trusted_true_results, 1);
        assert_eq!(stats.deopts, 0);
        assert_eq!(stats.fallbacks, 0);
    }
}

#[test]
fn test_blocking_key_no_collision() {
    // Test that (predicate=1, level=10000) and (predicate=2, level=0) don't collide.
    // With the old formula (predicate * 10000 + level), both would produce key=20000.
    // Using (predicate_idx, level) as the map key prevents this.
    let mut cache = ImplicationCache::new();

    // Add model for (predicate=1, level=10000)
    let mut model1 = FxHashMap::default();
    model1.insert("x".to_string(), SmtValue::Int(100));
    cache.record_blocking_countermodel(1, 10000, &model1);

    // Add model for (predicate=2, level=0)
    let mut model2 = FxHashMap::default();
    model2.insert("x".to_string(), SmtValue::Int(200));
    cache.record_blocking_countermodel(2, 0, &model2);

    // Verify both models are stored (2 distinct keys)
    let stats = cache.stats();
    assert_eq!(
        stats.countermodel_count, 2,
        "Should have 2 models for 2 distinct keys"
    );

    // Verify (predicate=1, level=10000) only sees model with x=100
    let x = ChcExpr::var(int_var("x"));
    let formula_100 = ChcExpr::eq(x.clone(), ChcExpr::int(100));
    let formula_200 = ChcExpr::eq(x, ChcExpr::int(200));

    assert!(
        cache.blocking_rejected_by_cache(1, 10000, &formula_100),
        "(1, 10000) should see x=100 model"
    );
    assert!(
        !cache.blocking_rejected_by_cache(1, 10000, &formula_200),
        "(1, 10000) should NOT see x=200 model (different key)"
    );

    // Verify (predicate=2, level=0) only sees model with x=200
    assert!(
        !cache.blocking_rejected_by_cache(2, 0, &formula_100),
        "(2, 0) should NOT see x=100 model (different key)"
    );
    assert!(
        cache.blocking_rejected_by_cache(2, 0, &formula_200),
        "(2, 0) should see x=200 model"
    );
}

/// Verify blocking_countermodels accumulation under the eviction cap.
/// With 20×50=1000 keys (under MAX_BLOCKING_COUNTERMODEL_KEYS), all entries
/// should be retained.
///
/// Reference: #2924 finding 2c, #3077 finding 4 (eviction cap added)
#[test]
fn test_blocking_countermodels_unbounded_key_growth() {
    let mut cache = ImplicationCache::new();
    let num_predicates = 20;
    let num_levels = 50;

    // Simulate PDR exploring many predicate×level combinations
    for pred in 0..num_predicates {
        for level in 0..num_levels {
            let mut model = FxHashMap::default();
            model.insert("x".to_string(), SmtValue::Int((pred * 100 + level) as i128));
            cache.record_blocking_countermodel(pred, level, &model);
        }
    }

    let stats = cache.stats();
    // Each (predicate, level) pair stores exactly 1 model → total = P * L
    assert_eq!(
        stats.countermodel_count,
        num_predicates * num_levels,
        "Total models should equal num_predicates * num_levels = {} with no eviction",
        num_predicates * num_levels,
    );

    // Prove there is no production clear/evict mechanism:
    // Add more models — they accumulate, never shrink.
    for pred in 0..num_predicates {
        for level in 0..num_levels {
            let mut model = FxHashMap::default();
            model.insert("y".to_string(), SmtValue::Int(999));
            cache.record_blocking_countermodel(pred, level, &model);
        }
    }

    let stats2 = cache.stats();
    // Now each key has 2 models (max_models_per_key=8, so both fit)
    assert_eq!(
        stats2.countermodel_count,
        num_predicates * num_levels * 2,
        "Under cap: {} keys * 2 models each should all be retained",
        num_predicates * num_levels,
    );
}

/// Verify that blocking_countermodels evicts when key count exceeds cap (#3077).
#[test]
fn test_blocking_countermodels_eviction_at_cap() {
    let mut cache = ImplicationCache::new();
    cache.dense_projection_cache.insert(
        DenseProjectionCacheKey {
            model_id: 1,
            mapping_id: 1,
        },
        DenseProjection::MissingVariable,
    );

    // Fill to exactly the cap
    for i in 0..MAX_BLOCKING_COUNTERMODEL_KEYS {
        let mut model = FxHashMap::default();
        model.insert("x".to_string(), SmtValue::Int(i as i128));
        cache.record_blocking_countermodel(i, 0, &model);
    }
    assert_eq!(
        cache.blocking_countermodels.len(),
        MAX_BLOCKING_COUNTERMODEL_KEYS,
    );

    // Adding one more distinct key triggers eviction (clear + insert)
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(999_999));
    cache.record_blocking_countermodel(999_999, 0, &model);

    // After eviction: only the newly inserted key remains
    assert_eq!(cache.blocking_countermodels.len(), 1);
    assert!(cache.blocking_countermodels.contains_key(&(999_999, 0)));
    assert!(
        cache.dense_projection_cache.is_empty(),
        "blocking countermodel eviction must clear dense model projections"
    );
}

#[test]
fn test_jit_cache_eviction_clears_dense_projections() {
    let mut cache = ImplicationCache::new();
    let stale_signature = vec![("stale".to_string(), 0_u32)].into_boxed_slice();
    cache
        .dense_projection_mapping_ids
        .insert(stale_signature.clone(), 1);
    cache.dense_projection_cache.insert(
        DenseProjectionCacheKey {
            model_id: 1,
            mapping_id: 1,
        },
        DenseProjection::MissingVariable,
    );
    for i in 0..MAX_JIT_CACHE_ENTRIES {
        cache.jit_cache.insert(i as u64, None);
    }

    let x = ChcExpr::var(int_var("x"));
    let formula = ChcExpr::ge(x, ChcExpr::int(0));
    cache.try_jit_compile(u64::MAX, &formula);

    assert!(
        cache.dense_projection_cache.is_empty(),
        "JIT cache eviction must clear dense model projections"
    );
    assert!(
        !cache
            .dense_projection_mapping_ids
            .contains_key(stale_signature.as_ref()),
        "JIT cache eviction must drop stale mapping identities"
    );
}
