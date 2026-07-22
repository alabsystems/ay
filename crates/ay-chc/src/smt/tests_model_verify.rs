// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-verification behavior tests for the SMT backend.

use super::context::SmtContext;
use super::incremental::{IncrementalCheckResult, IncrementalQueryContext};
use super::model_verify::{
    collect_theory_atoms_into, verify_sat_model, verify_sat_model_conjunction,
    verify_sat_model_conjunction_strict, verify_sat_model_conjunction_strict_with_mod_retry,
    verify_sat_model_strict, verify_sat_model_strict_with_mod_retry,
};
use super::types::{ModelVerifyResult, SmtResult, SmtValue};
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::term::Symbol;
use ay_core::{Sort, TermStore};
use std::sync::Arc;

#[test]
fn test_collect_theory_atoms_descends_through_theory_atom_root_6881() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let b_alias = terms.mk_var("b_alias", Sort::Bool);

    let eq_xy = terms.mk_eq(x, y);
    let eq_alias_atom = terms.mk_eq(b_alias, eq_xy);

    let mut collected = ay_core::kani_compat::DetHashSet::default();
    collect_theory_atoms_into(&terms, [eq_alias_atom], &mut collected);

    assert!(collected.contains(&eq_alias_atom));
    assert!(
        collected.contains(&eq_xy),
        "nested equality must be collected even when the root itself is a theory atom"
    );
}

#[test]
fn test_collect_theory_atoms_includes_bool_uf_arguments_6881() {
    let mut terms = TermStore::new();
    let b_alias = terms.mk_var("b_alias", Sort::Bool);
    let uf_bool = terms.mk_app(Symbol::named("pred"), vec![b_alias], Sort::Bool);

    let mut collected = ay_core::kani_compat::DetHashSet::default();
    collect_theory_atoms_into(&terms, [uf_bool], &mut collected);

    assert!(collected.contains(&uf_bool));
    assert!(
        collected.contains(&b_alias),
        "Bool arguments to reachable UF applications must stay visible for routing parity"
    );
}

#[test]
fn test_verify_sat_model_conjunction_detects_violated_member() {
    let x = ChcVar::new("x", ChcSort::Int);
    let background = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let assumption = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(1));

    assert!(
        !verify_sat_model_conjunction([&background, &assumption], &model),
        "conjunction should fail when any member is definitely false"
    );
}

#[test]
fn test_verify_sat_model_conjunction_fails_on_indeterminate_member() {
    let x = ChcVar::new("x", ChcSort::Int);
    let predicate = ChcExpr::predicate_app("P", PredicateId::new(0), vec![ChcExpr::var(x.clone())]);
    let arithmetic = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(3));

    assert!(
        !verify_sat_model_conjunction([&predicate, &arithmetic], &model),
        "indeterminate members must not silently pass model verification"
    );
    assert_eq!(
        verify_sat_model_conjunction_strict([&predicate, &arithmetic], &model),
        ModelVerifyResult::Indeterminate,
        "strict conjunction verification must report Indeterminate"
    );
}

#[test]
fn test_verify_sat_model_conjunction_strict_reports_invalid_when_any_member_fails() {
    let x = ChcVar::new("x", ChcSort::Int);
    let predicate = ChcExpr::predicate_app("P", PredicateId::new(0), vec![ChcExpr::var(x.clone())]);
    let violated = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(0));

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(3));

    assert_eq!(
        verify_sat_model_conjunction_strict([&predicate, &violated], &model),
        ModelVerifyResult::Invalid,
        "strict conjunction verification must prioritize Invalid over Indeterminate"
    );
}

#[test]
fn test_verify_sat_model_strict_returns_indeterminate_for_predicates() {
    let x = ChcVar::new("x", ChcSort::Int);
    let predicate = ChcExpr::predicate_app("P", PredicateId::new(0), vec![ChcExpr::var(x.clone())]);

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(3));

    assert_eq!(
        verify_sat_model_strict(&predicate, &model),
        ModelVerifyResult::Indeterminate,
        "predicate expressions should return Indeterminate, not Valid"
    );

    let arithmetic = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));
    assert_eq!(
        verify_sat_model_strict(&arithmetic, &model),
        ModelVerifyResult::Valid,
        "satisfied arithmetic should return Valid"
    );

    let violated = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::int(0),
    );
    assert_eq!(
        verify_sat_model_strict(&violated, &model),
        ModelVerifyResult::Invalid,
        "violated arithmetic should return Invalid"
    );
}

#[test]
fn test_verify_sat_model_mod_retry_rechecks_eliminated_form() {
    let x = ChcVar::new("x", ChcSort::Int);
    let mod_expr = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::int(3)),
        ChcExpr::int(0),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(4));

    assert_eq!(
        verify_sat_model_strict(&mod_expr, &model),
        ModelVerifyResult::Invalid,
        "original strict verification should see the violated mod constraint"
    );
    assert!(
        !matches!(
            verify_sat_model_strict_with_mod_retry(&mod_expr, &model),
            ModelVerifyResult::Invalid
        ),
        "mod-aware retry should re-check the eliminated form instead of hard-rejecting"
    );
    assert!(
        !matches!(
            verify_sat_model_conjunction_strict_with_mod_retry([&mod_expr], &model),
            ModelVerifyResult::Invalid
        ),
        "conjunction helper should use the same mod-aware retry policy"
    );
}

#[test]
fn test_verify_sat_model_wrapper_returns_false_on_invalid() {
    let x = ChcVar::new("x", ChcSort::Int);
    let violated = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(0));

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(3));

    assert!(
        !verify_sat_model(&violated, &model),
        "verify_sat_model must return false when model violates expression"
    );
}

#[test]
fn test_verify_sat_model_wrapper_returns_true_on_valid() {
    let x = ChcVar::new("x", ChcSort::Int);
    let satisfied = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));

    assert!(
        verify_sat_model(&satisfied, &model),
        "verify_sat_model must return true when model satisfies expression"
    );
}

#[test]
fn test_verify_sat_model_wrapper_returns_false_on_indeterminate() {
    let predicate = ChcExpr::predicate_app(
        "P",
        PredicateId::new(0),
        vec![ChcExpr::var(ChcVar::new("x", ChcSort::Int))],
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(1));

    assert!(
        !verify_sat_model(&predicate, &model),
        "verify_sat_model must fail closed on indeterminate expressions"
    );
}

#[test]
fn test_check_sat_accepts_indeterminate_as_sat() {
    // After #4712: Indeterminate model verification is accepted as Sat.
    // Indeterminate means evaluation is incomplete (uninterpreted predicates),
    // not that the model is wrong.
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let predicate = ChcExpr::predicate_app("P", PredicateId::new(0), vec![ChcExpr::var(x)]);

    assert!(
        matches!(ctx.check_sat(&predicate), SmtResult::Sat(_)),
        "indeterminate model verification must return Sat (not Unknown) per #4712"
    );
}

#[test]
fn test_assumption_mode_accepts_indeterminate_as_sat() {
    // After #4712: Indeterminate model verification is accepted as Sat.
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let background = vec![ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0))];
    let assumptions = vec![ChcExpr::predicate_app(
        "P",
        PredicateId::new(0),
        vec![ChcExpr::var(x)],
    )];

    let result = ctx.check_sat_with_assumption_conjuncts(&background, &assumptions);
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "indeterminate assumption-model verification must return Sat per #4712"
    );
}

#[test]
fn test_incremental_mode_accepts_indeterminate_as_sat() {
    // After #4712: Indeterminate model verification is accepted as Sat.
    let mut smt = SmtContext::new();
    let mut inc = IncrementalQueryContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let background = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let assumption = ChcExpr::predicate_app("P", PredicateId::new(0), vec![ChcExpr::var(x)]);

    inc.assert_background(&background, &mut smt);
    inc.finalize_background(&smt);
    inc.push();
    let result = inc.check_sat_incremental(std::slice::from_ref(&assumption), &mut smt, None);
    inc.pop();

    assert!(
        matches!(result, IncrementalCheckResult::Sat(_)),
        "indeterminate incremental-model verification must return Sat per #4712"
    );
}

#[test]
fn test_assumption_mode_mod_div_by_zero_remains_sat() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let background = vec![ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5))];
    let assumptions = vec![
        ChcExpr::eq(
            ChcExpr::mod_op(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::int(5),
        ),
        ChcExpr::eq(
            ChcExpr::Op(
                ChcOp::Div,
                vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::int(0))],
            ),
            ChcExpr::int(0),
        ),
    ];

    let result = ctx.check_sat_with_assumption_conjuncts(&background, &assumptions);
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "assumption SAT path should honor SMT-LIB total semantics for mod/div by zero, got {result:?}"
    );
}

#[test]
fn test_incremental_mode_mod_div_by_zero_remains_sat() {
    let mut smt = SmtContext::new();
    let mut inc = IncrementalQueryContext::new();
    let x = ChcVar::new("x", ChcSort::Int);

    let background = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let assumptions = vec![
        ChcExpr::eq(
            ChcExpr::mod_op(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::int(5),
        ),
        ChcExpr::eq(
            ChcExpr::Op(
                ChcOp::Div,
                vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::int(0))],
            ),
            ChcExpr::int(0),
        ),
    ];

    inc.assert_background(&background, &mut smt);
    inc.finalize_background(&smt);
    inc.push();
    let result = inc.check_sat_incremental(&assumptions, &mut smt, None);
    inc.pop();

    assert!(
        matches!(result, IncrementalCheckResult::Sat(_)),
        "incremental SAT path should honor SMT-LIB total semantics for mod/div by zero, got {result:?}"
    );
}

#[test]
fn test_verify_sat_model_conjunction_strict_all_valid() {
    let x = ChcVar::new("x", ChcSort::Int);
    let ge_zero = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let le_ten = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(10));

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));

    assert_eq!(
        verify_sat_model_conjunction_strict([&ge_zero, &le_ten], &model),
        ModelVerifyResult::Valid,
        "conjunction of all-satisfied expressions must return Valid"
    );
}

#[test]
fn test_verify_sat_model_conjunction_strict_empty_is_valid() {
    let model = FxHashMap::default();
    let empty: Vec<&ChcExpr> = vec![];
    assert_eq!(
        verify_sat_model_conjunction_strict(empty, &model),
        ModelVerifyResult::Valid,
        "empty conjunction must return Valid (vacuous truth)"
    );
}

#[test]
fn test_verify_sat_model_strict_accepts_array_overwrite_model_1753() {
    let lhs = ChcVar::new(
        "lhs",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let rhs = ChcVar::new(
        "rhs",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let expr = ChcExpr::eq(ChcExpr::var(lhs.clone()), ChcExpr::var(rhs.clone()));

    let mut model = FxHashMap::default();
    model.insert(
        lhs.name,
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            entries: vec![
                (SmtValue::Int(1), SmtValue::Int(10)),
                (SmtValue::Int(1), SmtValue::Int(20)),
            ],
        },
    );
    model.insert(
        rhs.name,
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            entries: vec![(SmtValue::Int(1), SmtValue::Int(20))],
        },
    );

    assert_eq!(
        verify_sat_model_strict(&expr, &model),
        ModelVerifyResult::Valid
    );
}

#[test]
fn test_verify_sat_model_strict_symbolic_array_default_is_indeterminate_9699() {
    let arr = ChcVar::new(
        "arr",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let expr = ChcExpr::eq(
        ChcExpr::select(ChcExpr::var(arr.clone()), ChcExpr::int(6)),
        ChcExpr::int(0),
    );

    let mut model = FxHashMap::default();
    model.insert(
        arr.name,
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Opaque("A!0".to_string())),
            entries: vec![(SmtValue::Int(5), SmtValue::Int(99))],
        },
    );

    assert_eq!(
        verify_sat_model_strict(&expr, &model),
        ModelVerifyResult::Indeterminate,
        "unstored selects over symbolic array defaults must fail closed, not become false"
    );
}

// Regression (foreach_enumerate COMPLETENESS): the SMT-LIB parser encodes
// integer literals that exceed `i64` (e.g. the `u64::MAX = 18446744073709551615`
// loop-index bound emitted for `_i#s7_0`) as an i64-arithmetic tree
// (`ChcParser::encode_large_int`: `(+ (* 18446744073 1000000000) 709551615)`).
// Evaluating that tree in `i64` overflows mid-product (`1.84e19 > i64::MAX`), so
// the bound atom — and therefore the WHOLE conjunction containing it — used to
// evaluate to Indeterminate, suppressing real overflow refutations: a genuine
// `t + x > u32::MAX` counterexample model verified Indeterminate instead of
// Valid, so check_sat/ay-chc returned Unknown/Inconclusive and the mutant
// SURVIVED. The widened i128 integer evaluator (eval_int_i128) decides the
// bound correctly while still REJECTING a non-satisfying (spurious) model.
#[test]
fn verify_conjunction_large_int_bound_does_not_poison_genuine_overflow() {
    // (0 <= v1 <= u64::MAX) AND (v3 + v4 < 0 OR v3 + v4 > u32::MAX)
    let smt2 = "(set-logic HORN)(declare-fun error () Bool)\
(assert (forall ((v1 Int)(v3 Int)(v4 Int)) (=> (and \
(and (<= 0 v1) (<= v1 18446744073709551615)) \
(or (< (+ v3 v4) 0) (> (+ v3 v4) 4294967295))) error)))(query error)";
    let problem = crate::ChcParser::parse(smt2).expect("CHC fixture must parse");
    let constraint = problem.clauses()[0]
        .body
        .constraint
        .clone()
        .expect("error clause carries a body constraint");
    let conjuncts: Vec<ChcExpr> = constraint.collect_conjuncts();

    // Genuine overflow: v3 = u32::MAX, v4 = 1 → sum = u32::MAX + 1 (> u32::MAX),
    // with v1 satisfying its u64::MAX bound. Must verify Valid (real refutation).
    let mut genuine = FxHashMap::default();
    genuine.insert("v1".to_string(), SmtValue::Int(0));
    genuine.insert("v3".to_string(), SmtValue::Int(4_294_967_295));
    genuine.insert("v4".to_string(), SmtValue::Int(1));
    assert_eq!(
        verify_sat_model_conjunction_strict(conjuncts.iter(), &genuine),
        ModelVerifyResult::Valid,
        "genuine overflow model must verify Valid; the large-int bound must not poison it"
    );

    // Spurious: v3 + v4 = 2 (in range) → the violation disjunct is false.
    // SOUNDNESS: a non-satisfying model must still be REJECTED (Invalid).
    let mut spurious = FxHashMap::default();
    spurious.insert("v1".to_string(), SmtValue::Int(0));
    spurious.insert("v3".to_string(), SmtValue::Int(1));
    spurious.insert("v4".to_string(), SmtValue::Int(1));
    assert_eq!(
        verify_sat_model_conjunction_strict(conjuncts.iter(), &spurious),
        ModelVerifyResult::Invalid,
        "non-overflow (spurious) model must be rejected as Invalid"
    );
}

// Direct unit guard for the widened evaluator: a comparison against a
// parser-encoded large-int literal must be decided (not Indeterminate), and a
// genuinely out-of-i128 value still fails closed.
#[test]
fn eval_large_int_comparison_is_determinate() {
    let smt2 = "(set-logic HORN)(declare-fun error () Bool)\
(assert (forall ((v1 Int)) (=> (<= v1 18446744073709551615) error)))(query error)";
    let problem = crate::ChcParser::parse(smt2).expect("parse");
    let bound = problem.clauses()[0]
        .body
        .constraint
        .clone()
        .expect("constraint");
    let mut model = FxHashMap::default();
    model.insert("v1".to_string(), SmtValue::Int(5));
    assert_eq!(
        verify_sat_model_strict(&bound, &model),
        ModelVerifyResult::Valid,
        "v1=5 <= u64::MAX must be Valid, not Indeterminate"
    );
    model.insert("v1".to_string(), SmtValue::Int(i128::from(i64::MAX)));
    assert_eq!(
        verify_sat_model_strict(&bound, &model),
        ModelVerifyResult::Valid,
        "v1=i64::MAX <= u64::MAX must be Valid"
    );
}

// 2026-07-08 fail-open closure (the development design notes
// rank 1): `sat_or_unknown` must NOT accept an Indeterminate verification as Sat
// when the model is missing an assignment for a free variable and completion
// cannot construct a witness that strictly verifies the original expression.
// That shape is the signature of an upstream abstraction dropping the variable's
// defining conjunct — in the model-checker-consumer midpoint repro the quotient
// `q = bvudiv(d, 2)` was absent from the model and the accepted Sat surfaced as a
// spurious CHC refutation. Equality-based completion is intentionally unavailable
// here because the defining conjunct is absent.
#[test]
fn test_sat_or_unknown_underivable_missing_free_var_returns_unknown() {
    let q = ChcVar::new("q", ChcSort::Int);
    let d = ChcVar::new("d", ChcSort::Int);
    // q >= d ∧ d >= 0 — `q` is ABSENT from the model and has NO functional
    // defining equality, so model-completion cannot derive it. Verification is
    // Indeterminate and the verdict must still fail closed to Unknown (the
    // fail-closed net is intact; FIX 5 only tightens the DERIVABLE case).
    let expr = ChcExpr::and_vec(vec![
        ChcExpr::ge(ChcExpr::var(q), ChcExpr::var(d.clone())),
        ChcExpr::ge(ChcExpr::var(d), ChcExpr::int(0)),
    ]);
    let mut model = FxHashMap::default();
    model.insert("d".to_string(), SmtValue::Int(5));
    assert!(
        matches!(
            SmtContext::sat_or_unknown(&expr, model, "test"),
            SmtResult::Unknown
        ),
        "a model missing a free variable must not be accepted as Sat"
    );
}

/// Precision (FIX 5, aychc-completeness): when the missing evaluable-position
/// variable HAS an SSA defining equality whose RHS is evaluable under the model
/// (the dropped head-arg binding `q = bvudiv(d, 2)` class), model-completion
/// derives it, the completed model strict-verifies Valid, and the verdict is a
/// genuine fully-witnessed Sat — not a spurious Unknown. The derived value must
/// appear in the returned model so downstream (SAT = CHC refutation) can rebuild
/// a concrete counterexample.
#[test]
fn test_sat_or_unknown_derivable_missing_free_var_completes_to_sat() {
    let q = ChcVar::new("q", ChcSort::Int);
    let d = ChcVar::new("d", ChcSort::Int);
    // q = d ∧ d >= 0 — `q` ABSENT, but its binding `q = d` is evaluable (d=5),
    // so completion derives q=5 and the full model is a strict-Valid witness.
    let expr = ChcExpr::and_vec(vec![
        ChcExpr::eq(ChcExpr::var(q), ChcExpr::var(d.clone())),
        ChcExpr::ge(ChcExpr::var(d), ChcExpr::int(0)),
    ]);
    let mut model = FxHashMap::default();
    model.insert("d".to_string(), SmtValue::Int(5));
    let result = SmtContext::sat_or_unknown(&expr, model, "test");
    let SmtResult::Sat(completed) = result else {
        panic!("a completable model must be accepted as Sat, not demoted to Unknown");
    };
    assert!(
        matches!(completed.get("q"), Some(SmtValue::Int(5))),
        "q must be DERIVED from its binding `q = d` (d=5), never default-assigned"
    );
}

/// Model-completion-then-strict-reverify (2026-07): a model missing ONE
/// evaluable-position BV variable is completed with the type-appropriate
/// default (BitVec→0 of the right width), and — because the completed model
/// strictly verifies the ORIGINAL expression to Bool(true) — accepted as Sat,
/// with the RETURNED model containing the default-filled variable.
#[test]
fn test_sat_or_unknown_missing_bv_var_default_completion_valid_returns_sat() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let d = ChcVar::new("d", ChcSort::BitVec(8));
    // x = 0 ∧ d = 5 — `x` is ABSENT from the model; the default x=0bv8
    // satisfies the whole expression.
    let expr = ChcExpr::and_vec(vec![
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(0, 8)),
        ChcExpr::eq(ChcExpr::var(d), ChcExpr::BitVec(5, 8)),
    ]);
    let mut model = FxHashMap::default();
    model.insert("d".to_string(), SmtValue::BitVec(5, 8));
    match SmtContext::sat_or_unknown(&expr, model, "test") {
        SmtResult::Sat(m) => {
            assert_eq!(
                m.get("x"),
                Some(&SmtValue::BitVec(0, 8)),
                "returned model must contain the default-filled BV variable"
            );
            assert_eq!(m.get("d"), Some(&SmtValue::BitVec(5, 8)));
        }
        other => panic!("default-completed strictly-Valid witness must be Sat, got {other:?}"),
    }
}

/// The completion is a GUESS gated exclusively on strict Valid: when the
/// completion falsifies the expression (x must be nonzero but the default is
/// 0, and no equality conjunct defines x for propagation), the verdict must
/// stay Unknown — never Sat, never Unsat.
#[test]
fn test_sat_or_unknown_missing_bv_var_default_completion_invalid_stays_unknown() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    // `x = 1 AND x = 2` — genuinely UNSAT, so NO completion (neither the
    // FIX 5 bindings derivation, which derives x=1 and then fails the second
    // conjunct under strict re-verification, nor the scalar default x=0) can
    // produce a Valid witness; the verdict must stay the fail-closed Unknown.
    // (The previous single-conjunct `x = 1` shape is now CORRECTLY accepted as
    // Sat by the bindings derivation — x=1 is a forced, strict-verified
    // witness — so it can no longer pin the fail-closed path.)
    let expr = ChcExpr::and_vec(vec![
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(1, 8)),
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(2, 8)),
    ]);
    let model = FxHashMap::default();
    assert!(
        matches!(
            SmtContext::sat_or_unknown(&expr, model, "test"),
            SmtResult::Unknown
        ),
        "a completion that fails strict re-verification must stay Unknown"
    );
}

/// Regression: the model-checker-consumer `bbN_thr_vK` threading wobble. check_sat
/// preprocessing eliminates the threaded var through a `(= a thr)` conjunct
/// and only var=CONST eliminations are transported back — the model arrives
/// missing `thr`. Equality propagation must reconstruct `thr := a`'s value so
/// the strictly-verified witness is accepted as Sat (previously Unknown).
#[test]
fn test_sat_or_unknown_var_var_equality_propagates_missing_binding() {
    let a = ChcVar::new("a", ChcSort::BitVec(8));
    let thr = ChcVar::new("bb1_thr_v0", ChcSort::BitVec(8));
    let expr = ChcExpr::and_vec(vec![
        ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::var(thr)),
        ChcExpr::Op(
            ChcOp::BvULe,
            vec![Arc::new(ChcExpr::BitVec(1, 8)), Arc::new(ChcExpr::var(a))],
        ),
    ]);
    let mut model = FxHashMap::default();
    model.insert("a".to_string(), SmtValue::BitVec(5, 8));
    match SmtContext::sat_or_unknown(&expr, model, "test") {
        SmtResult::Sat(m) => {
            assert_eq!(
                m.get("bb1_thr_v0"),
                Some(&SmtValue::BitVec(5, 8)),
                "the threaded variable must be bound through the equality, not defaulted"
            );
        }
        other => panic!("equality-propagated verified witness must be Sat, got {other:?}"),
    }
}

/// Chained propagation: x = y ∧ y = z with only x assigned must fill both y
/// and z (fixpoint), and the witness must strictly verify.
#[test]
fn test_sat_or_unknown_var_var_equality_chain_propagates_to_fixpoint() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let y = ChcVar::new("y", ChcSort::BitVec(8));
    let z = ChcVar::new("z", ChcSort::BitVec(8));
    let expr = ChcExpr::and_vec(vec![
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
        ChcExpr::eq(ChcExpr::var(y), ChcExpr::var(z)),
        ChcExpr::Op(
            ChcOp::BvULe,
            vec![Arc::new(ChcExpr::BitVec(7, 8)), Arc::new(ChcExpr::var(x))],
        ),
    ]);
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::BitVec(9, 8));
    match SmtContext::sat_or_unknown(&expr, model, "test") {
        SmtResult::Sat(m) => {
            assert_eq!(m.get("y"), Some(&SmtValue::BitVec(9, 8)));
            assert_eq!(m.get("z"), Some(&SmtValue::BitVec(9, 8)));
        }
        other => panic!("chained equality propagation must yield Sat, got {other:?}"),
    }
}

/// Evaluable var=term definition: `q = d udiv 2` with d assigned must bind q
/// to the evaluated quotient (the historical dropped-defining-conjunct shape),
/// gated on strict verification as always.
#[test]
fn test_sat_or_unknown_var_term_equality_propagates_evaluated_definition() {
    let q = ChcVar::new("q", ChcSort::BitVec(8));
    let d = ChcVar::new("d", ChcSort::BitVec(8));
    let expr = ChcExpr::and_vec(vec![
        ChcExpr::eq(
            ChcExpr::var(q),
            ChcExpr::Op(
                ChcOp::BvUDiv,
                vec![
                    Arc::new(ChcExpr::var(d.clone())),
                    Arc::new(ChcExpr::BitVec(2, 8)),
                ],
            ),
        ),
        ChcExpr::eq(ChcExpr::var(d), ChcExpr::BitVec(6, 8)),
    ]);
    let mut model = FxHashMap::default();
    model.insert("d".to_string(), SmtValue::BitVec(6, 8));
    match SmtContext::sat_or_unknown(&expr, model, "test") {
        SmtResult::Sat(m) => {
            assert_eq!(
                m.get("q"),
                Some(&SmtValue::BitVec(3, 8)),
                "q must be bound to the evaluated definition d udiv 2"
            );
        }
        other => panic!("evaluable-definition propagation must yield Sat, got {other:?}"),
    }
}

/// Accept ONLY on Valid: a completed model whose re-verification is still
/// Indeterminate (an uninterpreted predicate atom remains unevaluable) must
/// stay Unknown — the #4712 fully-assigned acceptance does NOT extend to
/// guessed assignments.
#[test]
fn test_sat_or_unknown_missing_var_completion_indeterminate_stays_unknown() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::and_vec(vec![
        ChcExpr::predicate_app("P", PredicateId::new(0), vec![ChcExpr::var(x.clone())]),
        ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0)),
    ]);
    let model = FxHashMap::default();
    assert!(
        matches!(
            SmtContext::sat_or_unknown(&expr, model, "test"),
            SmtResult::Unknown
        ),
        "an Indeterminate completion must not be accepted as Sat"
    );
}

/// ALL missing evaluable-position scalars are completed in one pass, each with
/// its sort's default (Bool→false, Int→0, Real→0, BitVec→0 of the right width).
/// The Real conjunct is a reflexive equality because the strict evaluator has
/// no arm for `ChcExpr::Real` LITERALS (a Real-literal comparison stays
/// Indeterminate and thus fail-closed Unknown); `r = r` still requires the
/// Real default to be inserted for the conjunct to evaluate at all.
#[test]
fn test_sat_or_unknown_completes_all_missing_scalar_sorts() {
    let b = ChcVar::new("b", ChcSort::Bool);
    let i = ChcVar::new("i", ChcSort::Int);
    let r = ChcVar::new("r", ChcSort::Real);
    let x = ChcVar::new("x", ChcSort::BitVec(4));
    let expr = ChcExpr::and_vec(vec![
        ChcExpr::not(ChcExpr::var(b)),
        ChcExpr::eq(ChcExpr::var(i), ChcExpr::int(0)),
        ChcExpr::eq(ChcExpr::var(r.clone()), ChcExpr::var(r)),
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(0, 4)),
    ]);
    let model = FxHashMap::default();
    match SmtContext::sat_or_unknown(&expr, model, "test") {
        SmtResult::Sat(m) => {
            assert_eq!(m.get("b"), Some(&SmtValue::Bool(false)));
            assert_eq!(m.get("i"), Some(&SmtValue::Int(0)));
            assert_eq!(m.get("x"), Some(&SmtValue::BitVec(0, 4)));
            assert!(m.contains_key("r"), "Real default must be filled in");
        }
        other => panic!("all-sorts default completion must verify and be Sat, got {other:?}"),
    }
}

/// Guard for the #4712 behavior this fix deliberately KEEPS: when every free
/// variable is assigned and Indeterminate comes only from an uninterpreted
/// predicate application (which the DPLL(T) solve itself decided), the model is
/// still accepted as Sat.
#[test]
fn test_sat_or_unknown_predicate_with_full_model_still_sat() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::and_vec(vec![
        ChcExpr::predicate_app("P", PredicateId::new(0), vec![ChcExpr::var(x.clone())]),
        ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0)),
    ]);
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(3));
    assert!(
        matches!(
            SmtContext::sat_or_unknown(&expr, model, "test"),
            SmtResult::Sat(_)
        ),
        "fully-assigned model with only predicate-caused indeterminacy stays Sat (#4712)"
    );
}

/// A fully-assigned, fully-evaluable Valid model stays Sat (no over-demotion).
#[test]
fn test_sat_or_unknown_valid_model_stays_sat() {
    let d = ChcVar::new("d", ChcSort::Int);
    let expr = ChcExpr::ge(ChcExpr::var(d), ChcExpr::int(0));
    let mut model = FxHashMap::default();
    model.insert("d".to_string(), SmtValue::Int(5));
    assert!(matches!(
        SmtContext::sat_or_unknown(&expr, model, "test"),
        SmtResult::Sat(_)
    ));
}

// --- Phase-2 BigInt escape: strict verification of beyond-i128 witnesses ---

/// A beyond-i128 witness (SmtValue::BigInt) is decided EXACTLY by strict
/// model verification against the parser's Horner-encoded literal: the true
/// witness verifies Valid, and a mutated witness (value ± 1) is REJECTED as
/// Invalid — no new unverified Sat channel.
#[test]
fn verify_sat_model_strict_bigint_witness_valid_and_mutated_rejected() {
    use num_bigint::BigInt;
    let big: BigInt = (BigInt::from(1u8) << 128) + 1; // 2^128 + 1

    // The clause shape of the measured probe: (and (= x BIG) (> x 0)).
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::from_bigint(big.clone())),
        ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(0)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::int_from_bigint(big.clone()));
    assert_eq!(
        verify_sat_model_strict(&expr, &model),
        ModelVerifyResult::Valid,
        "the exact beyond-i128 witness must verify Valid"
    );

    // Negative controls: mutated witnesses must be rejected, not accepted.
    model.insert("x".to_string(), SmtValue::int_from_bigint(big.clone() + 1));
    assert_eq!(
        verify_sat_model_strict(&expr, &model),
        ModelVerifyResult::Invalid,
        "witness + 1 must be rejected Invalid"
    );
    model.insert("x".to_string(), SmtValue::int_from_bigint(big - 1));
    assert_eq!(
        verify_sat_model_strict(&expr, &model),
        ModelVerifyResult::Invalid,
        "witness - 1 must be rejected Invalid"
    );
}
