// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Focused contracts for the positive-context ITE model repair.

use super::*;

fn install_lia_model(
    executor: &mut Executor,
    sat_assignments: &[(TermId, bool)],
    int_values: &[(TermId, i64)],
) {
    let mut model = model_with_sat_assignments(sat_assignments);
    model.lia_model = Some(LiaModel {
        values: int_values
            .iter()
            .map(|&(term, value)| (term, BigInt::from(value)))
            .collect(),
    });
    executor.last_model = Some(model);
}

fn lia_value(executor: &Executor, term: TermId) -> BigInt {
    executor
        .last_model
        .as_ref()
        .and_then(|model| model.lia_model.as_ref())
        .and_then(|model| model.values.get(&term))
        .cloned()
        .expect("test variable must have an LIA value")
}

#[test]
fn ite_fixup_repairs_only_the_sat_active_or_branch() {
    let mut executor = Executor::new();
    let y = executor.ctx.terms.mk_var("ite_fixup_y", Sort::Int);
    let active_cond = executor
        .ctx
        .terms
        .mk_var("ite_fixup_active_cond", Sort::Bool);
    let inactive_cond = executor
        .ctx
        .terms
        .mk_var("ite_fixup_inactive_cond", Sort::Bool);
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let two = executor.ctx.terms.mk_int(BigInt::from(2));
    let otherwise = executor.ctx.terms.mk_bool(true);
    let y_eq_one = executor.ctx.terms.mk_eq(y, one);
    let y_eq_two = executor.ctx.terms.mk_eq(y, two);
    let active = executor
        .ctx
        .terms
        .mk_ite_raw(active_cond, y_eq_one, otherwise);
    let inactive = executor
        .ctx
        .terms
        .mk_ite_raw(inactive_cond, y_eq_two, otherwise);
    let assertion =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("or"), vec![active, inactive], Sort::Bool);
    executor.ctx.assertions.push(assertion);
    install_lia_model(
        &mut executor,
        &[
            (assertion, true),
            (active, true),
            (inactive, false),
            (active_cond, true),
            (inactive_cond, true),
        ],
        &[(y, 9)],
    );

    executor.fix_ite_model_values();

    assert_eq!(lia_value(&executor, y), BigInt::from(1));
}

#[test]
fn ite_fixup_prefers_raw_sat_assignment_for_the_ite_condition() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("ite_fixup_x", Sort::Int);
    let y = executor.ctx.terms.mk_var("ite_fixup_y", Sort::Int);
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let two = executor.ctx.terms.mk_int(BigInt::from(2));
    let condition = executor.ctx.terms.mk_eq(x, zero);
    let y_eq_one = executor.ctx.terms.mk_eq(y, one);
    let y_eq_two = executor.ctx.terms.mk_eq(y, two);
    let assertion = executor.ctx.terms.mk_ite_raw(condition, y_eq_one, y_eq_two);
    executor.ctx.assertions.push(assertion);
    // The stale arithmetic model says the condition is false, while the SAT
    // skeleton that selected the ITE branch says true.
    install_lia_model(
        &mut executor,
        &[(assertion, true), (condition, true)],
        &[(x, 7), (y, 9)],
    );

    executor.fix_ite_model_values();

    assert_eq!(lia_value(&executor, y), BigInt::from(1));
}

#[test]
fn ite_fixup_conflicting_active_patches_roll_back_both_arithmetic_models() {
    let mut executor = Executor::new();
    let y = executor.ctx.terms.mk_var("ite_fixup_y", Sort::Int);
    let c1 = executor.ctx.terms.mk_var("ite_fixup_c1", Sort::Bool);
    let c2 = executor.ctx.terms.mk_var("ite_fixup_c2", Sort::Bool);
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let two = executor.ctx.terms.mk_int(BigInt::from(2));
    let otherwise = executor.ctx.terms.mk_bool(true);
    let y_eq_one = executor.ctx.terms.mk_eq(y, one);
    let y_eq_two = executor.ctx.terms.mk_eq(y, two);
    let first = executor.ctx.terms.mk_ite_raw(c1, y_eq_one, otherwise);
    let second = executor.ctx.terms.mk_ite_raw(c2, y_eq_two, otherwise);
    let assertion =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("and"), vec![first, second], Sort::Bool);
    executor.ctx.assertions.push(assertion);
    install_lia_model(
        &mut executor,
        &[
            (assertion, true),
            (first, true),
            (second, true),
            (c1, true),
            (c2, true),
        ],
        &[(y, 9)],
    );
    executor.last_model.as_mut().expect("installed").lra_model = Some(LraModel {
        values: HashMap::from_iter([(y, BigRational::from(BigInt::from(9)))]),
    });

    executor.fix_ite_model_values();

    assert_eq!(lia_value(&executor, y), BigInt::from(9));
    assert_eq!(
        executor
            .last_model
            .as_ref()
            .and_then(|model| model.lra_model.as_ref())
            .and_then(|model| model.values.get(&y)),
        Some(&BigRational::from(BigInt::from(9)))
    );
}

#[test]
fn ite_fixup_nonintegral_int_patch_rolls_back_other_repairs() {
    let mut executor = Executor::new();
    let y = executor.ctx.terms.mk_var("ite_fixup_y", Sort::Int);
    let z = executor.ctx.terms.mk_var("ite_fixup_z", Sort::Int);
    let c1 = executor.ctx.terms.mk_var("ite_fixup_c1", Sort::Bool);
    let c2 = executor.ctx.terms.mk_var("ite_fixup_c2", Sort::Bool);
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let half = executor
        .ctx
        .terms
        .mk_rational(BigRational::new(BigInt::from(1), BigInt::from(2)));
    let otherwise = executor.ctx.terms.mk_bool(true);
    let y_eq_one = executor.ctx.terms.mk_eq(y, one);
    // This raw adversarial equality models a malformed/nonintegral candidate
    // arriving at the optional completion boundary. It must poison the whole
    // repair transaction, not merely skip z and commit the earlier y patch.
    let z_eq_half = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![z, half], Sort::Bool);
    let first = executor.ctx.terms.mk_ite_raw(c1, y_eq_one, otherwise);
    let second = executor.ctx.terms.mk_ite_raw(c2, z_eq_half, otherwise);
    let assertion =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("and"), vec![first, second], Sort::Bool);
    executor.ctx.assertions.push(assertion);
    install_lia_model(
        &mut executor,
        &[
            (assertion, true),
            (first, true),
            (second, true),
            (c1, true),
            (c2, true),
        ],
        &[(y, 9), (z, 9)],
    );

    executor.fix_ite_model_values();

    assert_eq!(lia_value(&executor, y), BigInt::from(9));
    assert_eq!(lia_value(&executor, z), BigInt::from(9));
}

#[test]
fn ite_fixup_charges_repeated_exact_payload_before_deduplication() {
    let mut executor = Executor::new();
    let y = executor.ctx.terms.mk_var("ite_fixup_y", Sort::Real);
    let c1 = executor.ctx.terms.mk_var("ite_fixup_c1", Sort::Bool);
    let c2 = executor.ctx.terms.mk_var("ite_fixup_c2", Sort::Bool);
    let huge_value = BigRational::from(BigInt::from(1) << 8192usize);
    let huge = executor.ctx.terms.mk_rational(huge_value.clone());
    let otherwise = executor.ctx.terms.mk_bool(true);
    // Distinct raw equality terms share the same large value and propose the
    // same patch in opposite orientations. The second proposal is a duplicate
    // semantically, but still incurs a large clone and exact comparison.
    let forward = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![y, huge], Sort::Bool);
    let reverse = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![huge, y], Sort::Bool);
    let first = executor.ctx.terms.mk_ite_raw(c1, forward, otherwise);
    let second = executor.ctx.terms.mk_ite_raw(c2, reverse, otherwise);
    let assertion =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("and"), vec![first, second], Sort::Bool);
    executor.ctx.assertions.push(assertion);
    let mut model = model_with_sat_assignments(&[
        (assertion, true),
        (first, true),
        (second, true),
        (c1, true),
        (c2, true),
    ]);
    let zero = BigRational::from(BigInt::from(0));
    model.lra_model = Some(LraModel {
        values: HashMap::from_iter([(y, zero.clone())]),
    });
    executor.last_model = Some(model);
    let one_candidate = ite_fixup_limits::patch_candidate_bytes_for_test(&huge_value);

    // Exactly one candidate fits: the repeated value must be charged before
    // map deduplication and abort the whole transaction.
    executor.fix_ite_model_values_with_limits_for_test(one_candidate, 8);
    assert_eq!(
        executor
            .last_model
            .as_ref()
            .and_then(|model| model.lra_model.as_ref())
            .and_then(|model| model.values.get(&y)),
        Some(&zero)
    );

    // The independent candidate-count cap likewise counts duplicate proposals.
    executor.fix_ite_model_values_with_limits_for_test(
        one_candidate.checked_mul(2).expect("tiny test cap fits"),
        1,
    );
    assert_eq!(
        executor
            .last_model
            .as_ref()
            .and_then(|model| model.lra_model.as_ref())
            .and_then(|model| model.values.get(&y)),
        Some(&zero)
    );
}

#[test]
fn ite_fixup_inconsistent_not_literal_aborts_the_whole_transaction() {
    let mut executor = Executor::new();
    let y = executor.ctx.terms.mk_var("ite_fixup_y", Sort::Int);
    let cond = executor.ctx.terms.mk_var("ite_fixup_cond", Sort::Bool);
    let q = executor.ctx.terms.mk_var("ite_fixup_q", Sort::Bool);
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let otherwise = executor.ctx.terms.mk_bool(true);
    let y_eq_one = executor.ctx.terms.mk_eq(y, one);
    let repair = executor.ctx.terms.mk_ite_raw(cond, y_eq_one, otherwise);
    let not_q = executor.ctx.terms.mk_not_raw(q);
    let disjunction =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("or"), vec![not_q, otherwise], Sort::Bool);
    executor.ctx.assertions.extend([repair, disjunction]);
    // `not_q=true` conflicts with its Tseitin representation `q=true`.
    install_lia_model(
        &mut executor,
        &[
            (repair, true),
            (cond, true),
            (disjunction, true),
            (not_q, true),
            (q, true),
        ],
        &[(y, 9)],
    );

    executor.fix_ite_model_values();

    assert_eq!(lia_value(&executor, y), BigInt::from(9));
}

#[test]
fn ite_fixup_selects_inverted_not_literal_without_semantic_fallback() {
    let mut executor = Executor::new();
    let y = executor.ctx.terms.mk_var("ite_fixup_y", Sort::Int);
    let q = executor.ctx.terms.mk_var("ite_fixup_q", Sort::Bool);
    let cond = executor.ctx.terms.mk_var("ite_fixup_cond", Sort::Bool);
    let two = executor.ctx.terms.mk_int(BigInt::from(2));
    let y_eq_two = executor.ctx.terms.mk_eq(y, two);
    let false_branch = executor.ctx.terms.mk_bool(false);
    let clobber = executor.ctx.terms.mk_ite_raw(cond, y_eq_two, false_branch);
    let semantic_true = executor.ctx.terms.mk_bool(true);
    let stale_other = executor.ctx.terms.mk_app(
        Symbol::named("or"),
        vec![semantic_true, clobber],
        Sort::Bool,
    );
    let not_q = executor.ctx.terms.mk_not_raw(q);
    let assertion =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("or"), vec![not_q, stale_other], Sort::Bool);
    executor.ctx.assertions.push(assertion);
    install_lia_model(
        &mut executor,
        &[
            (assertion, true),
            // `not_q` has no direct Tseitin entry. Its only raw authority is
            // the ordinary encoding of `q=false`.
            (q, false),
            // This stale top-level assignment must dominate its semantic
            // value: the child is semantically true, but is not SAT-active.
            (stale_other, false),
            (clobber, true),
            (cond, true),
        ],
        &[(y, 9)],
    );
    assert!(matches!(
        executor.evaluate_term(
            executor.last_model.as_ref().expect("installed"),
            stale_other
        ),
        EvalValue::Bool(true)
    ));
    let before = eval_node_visits();

    executor.fix_ite_model_values();

    // Raw inversion selects only `(not q)`, which is a stop context. No
    // semantic fallback runs, and the stale inactive child cannot clobber y.
    assert_eq!(eval_node_visits(), before);
    assert_eq!(lia_value(&executor, y), BigInt::from(9));
}

#[test]
fn ite_fixup_stops_under_negative_and_unknown_polarity_contexts() {
    let mut executor = Executor::new();
    let y = executor.ctx.terms.mk_var("ite_fixup_y", Sort::Int);
    let cond = executor.ctx.terms.mk_var("ite_fixup_cond", Sort::Bool);
    let p = executor.ctx.terms.mk_var("ite_fixup_p", Sort::Bool);
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let otherwise = executor.ctx.terms.mk_bool(true);
    let y_eq_one = executor.ctx.terms.mk_eq(y, one);
    let ite = executor.ctx.terms.mk_ite_raw(cond, y_eq_one, otherwise);
    let negated = executor.ctx.terms.mk_not_raw(ite);
    let implication = executor
        .ctx
        .terms
        .mk_app(Symbol::named("=>"), vec![p, ite], Sort::Bool);
    executor.ctx.assertions.extend([negated, implication]);
    install_lia_model(
        &mut executor,
        &[
            (negated, true),
            (implication, true),
            (cond, true),
            (p, true),
        ],
        &[(y, 9)],
    );

    executor.fix_ite_model_values();

    assert_eq!(lia_value(&executor, y), BigInt::from(9));
}

#[test]
fn ite_fixup_or_without_a_true_witness_rolls_back_prior_patches() {
    let mut executor = Executor::new();
    let y = executor.ctx.terms.mk_var("ite_fixup_y", Sort::Int);
    let cond = executor.ctx.terms.mk_var("ite_fixup_cond", Sort::Bool);
    let p = executor.ctx.terms.mk_var("ite_fixup_p", Sort::Bool);
    let q = executor.ctx.terms.mk_var("ite_fixup_q", Sort::Bool);
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let otherwise = executor.ctx.terms.mk_bool(true);
    let y_eq_one = executor.ctx.terms.mk_eq(y, one);
    let repair = executor.ctx.terms.mk_ite_raw(cond, y_eq_one, otherwise);
    let no_witness = executor
        .ctx
        .terms
        .mk_app(Symbol::named("or"), vec![p, q], Sort::Bool);
    executor.ctx.assertions.extend([repair, no_witness]);
    install_lia_model(
        &mut executor,
        &[
            (repair, true),
            (cond, true),
            (no_witness, true),
            (p, false),
            (q, false),
        ],
        &[(y, 9)],
    );

    executor.fix_ite_model_values();

    assert_eq!(lia_value(&executor, y), BigInt::from(9));
}

#[test]
fn ite_fixup_work_cap_aborts_before_mutating_the_model() {
    let mut executor = Executor::new();
    let y = executor.ctx.terms.mk_var("ite_fixup_y", Sort::Int);
    let cond = executor.ctx.terms.mk_var("ite_fixup_cond", Sort::Bool);
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let otherwise = executor.ctx.terms.mk_bool(true);
    let y_eq_one = executor.ctx.terms.mk_eq(y, one);
    let assertion = executor.ctx.terms.mk_ite_raw(cond, y_eq_one, otherwise);
    executor.ctx.assertions.push(assertion);
    install_lia_model(&mut executor, &[(assertion, true), (cond, true)], &[(y, 9)]);

    // The structural root costs one unit. Without charging the equality
    // evaluator's node visits, the extraction itself would fit in the second
    // unit and mutate `y`; the evaluator must exhaust this tiny budget first.
    executor.fix_ite_model_values_with_work_limit_for_test(2);

    assert_eq!(lia_value(&executor, y), BigInt::from(9));
}

#[test]
fn eval_work_budget_expires_before_a_node_and_restores_after_nested_drop() {
    let mut executor = Executor::new();
    let p = executor.ctx.terms.mk_var("ite_fixup_budget_p", Sort::Bool);
    let q = executor.ctx.terms.mk_var("ite_fixup_budget_q", Sort::Bool);
    let conjunction = executor
        .ctx
        .terms
        .mk_app(Symbol::named("and"), vec![p, q], Sort::Bool);
    let model = model_with_sat_assignments(&[(p, true), (q, true)]);
    let _memo = EvalMemoSession::new();
    let before = eval_node_visits();
    let outer = EvalWorkBudget::new(8);
    {
        let inner = EvalWorkBudget::new(1);
        assert!(matches!(
            executor.evaluate_term(&model, conjunction),
            EvalValue::Unknown
        ));
        assert!(inner.exhausted());
        // The root consumed the sole permitted node; the first child was
        // refused before it could increment the actual-work clock.
        assert_eq!(eval_node_visits(), before + 1);
    }

    // Dropping the tighter nested guard restores the outer deadline. The
    // prior budget-induced Unknown was not memoized, so the same term now
    // evaluates completely instead of returning the poisoned result.
    assert!(matches!(
        executor.evaluate_term(&model, conjunction),
        EvalValue::Bool(true)
    ));
    assert!(eval_node_visits() > before + 1);
    drop(outer);
}
