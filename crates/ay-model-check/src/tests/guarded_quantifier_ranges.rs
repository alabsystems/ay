// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `finite_quantifiers` to preserve test FQNs.

#[cfg(test)]
fn finite_quantifier_half_open_guard(
    terms: &mut TermStore,
    variable: TermId,
    lower: TermId,
    upper: TermId,
) -> TermId {
    let (ge, lt) = match terms.sort(variable) {
        Sort::Int => (">=", "<"),
        Sort::BitVec(_) => ("bvuge", "bvult"),
        _ => panic!("test range requires Int or BV"),
    };
    let lower = app(terms, ge, &[variable, lower], Sort::Bool);
    let upper = app(terms, lt, &[variable, upper], Sort::Bool);
    app(terms, "and", &[lower, upper], Sort::Bool)
}

#[test]
fn finite_quantifier_guarded_int_range_preserves_negative_and_excluded_endpoints() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let lower = terms.mk_int(int(-2));
    let last = terms.mk_int(int(2));
    let upper = terms.mk_int(int(3));
    let guard = finite_quantifier_half_open_guard(&mut terms, i, lower, upper);
    let before_upper = app(&mut terms, "<", &[i, upper], Sort::Bool);
    let before_last = app(&mut terms, "<", &[i, last], Sort::Bool);
    let at_last = app(&mut terms, "=", &[i, last], Sort::Bool);
    let at_lower = app(&mut terms, "=", &[i, lower], Sort::Bool);
    let at_upper = app(&mut terms, "=", &[i, upper], Sort::Bool);
    let all_good = app(&mut terms, "=>", &[guard, before_upper], Sort::Bool);
    let all_bad = app(&mut terms, "=>", &[guard, before_last], Sort::Bool);
    let some_good = app(&mut terms, "and", &[guard, at_last], Sort::Bool);
    let some_negative = app(&mut terms, "and", &[guard, at_lower], Sort::Bool);
    let some_bad = app(&mut terms, "and", &[guard, at_upper], Sort::Bool);
    let all_good = terms.mk_forall(vec![("i".to_string(), Sort::Int)], all_good);
    let all_bad = terms.mk_forall(vec![("i".to_string(), Sort::Int)], all_bad);
    let some_good = terms.mk_exists(vec![("i".to_string(), Sort::Int)], some_good);
    let some_negative = terms.mk_exists(vec![("i".to_string(), Sort::Int)], some_negative);
    let some_bad = terms.mk_exists(vec![("i".to_string(), Sort::Int)], some_bad);
    assert_confirmed(&verdict(
        &terms,
        &StubModel::new(),
        &[all_good, some_good, some_negative],
    ));
    assert_violates(&verdict(&terms, &StubModel::new(), &[all_bad]));
    assert_violates(&verdict(&terms, &StubModel::new(), &[some_bad]));
}

#[test]
fn finite_quantifier_guarded_bv64_inclusive_maximum_does_not_wrap() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::bitvec(64));
    let maximum = terms.mk_bitvec(BigInt::from(u64::MAX), 64);
    let previous = terms.mk_bitvec(BigInt::from(u64::MAX - 1), 64);
    let lower = app(&mut terms, "bvule", &[previous, i], Sort::Bool);
    let upper = app(&mut terms, "bvuge", &[maximum, i], Sort::Bool);
    let guard = app(&mut terms, "and", &[lower, upper], Sort::Bool);
    let at_max = app(&mut terms, "=", &[maximum, i], Sort::Bool);
    let all = app(&mut terms, "=>", &[guard, at_max], Sort::Bool);
    let some = app(&mut terms, "and", &[guard, at_max], Sort::Bool);
    let all = terms.mk_forall(vec![("i".to_string(), Sort::bitvec(64))], all);
    let some = terms.mk_exists(vec![("i".to_string(), Sort::bitvec(64))], some);
    assert_violates(&verdict(&terms, &StubModel::new(), &[all]));
    assert_confirmed(&verdict(&terms, &StubModel::new(), &[some]));
}

#[test]
fn finite_quantifier_guarded_slice_relation_uses_model_length_and_concrete_cells() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::bitvec(64));
    let len = terms.mk_var("len", Sort::bitvec(64));
    let array = terms.mk_var("array", Sort::array(Sort::bitvec(64), Sort::Int));
    let read = app(&mut terms, "select", &[array, i], Sort::Int);
    let seven = terms.mk_int(int(7));
    let equal = app(&mut terms, "=", &[read, seven], Sort::Bool);
    let guard = app(&mut terms, "bvult", &[i, len], Sort::Bool);
    let body = app(&mut terms, "=>", &[guard, equal], Sort::Bool);
    let all = terms.mk_forall(vec![("i".to_string(), Sort::bitvec(64))], body);
    let cells = ModelValue::Array(Box::new(ArrayValue {
        default: ModelValue::Int(int(7)),
        store: vec![(ModelValue::bitvec(int(3), 64), ModelValue::Int(int(8)))],
    }));
    let short = StubModel::new()
        .with(array, cells.clone())
        .with(len, ModelValue::bitvec(int(3), 64));
    let long = StubModel::new()
        .with(array, cells)
        .with(len, ModelValue::bitvec(int(4), 64));
    assert_confirmed(&verdict(&terms, &short, &[all]));
    assert_violates(&verdict(&terms, &long, &[all]));
}

#[test]
fn finite_quantifier_guarded_resize_preserves_prefix_even_when_new_length_shrinks() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::bitvec(64));
    let old_len = terms.mk_bitvec(int(6), 64);
    let new_len = terms.mk_bitvec(int(2), 64);
    let array = terms.mk_var("resized", Sort::array(Sort::bitvec(64), Sort::Int));
    let read = app(&mut terms, "select", &[array, i], Sort::Int);
    let one = terms.mk_int(int(1));
    let fill = terms.mk_int(int(9));
    let prefix_eq = app(&mut terms, "=", &[read, one], Sort::Bool);
    let fill_eq = app(&mut terms, "=", &[read, fill], Sort::Bool);
    let prefix_guard = app(&mut terms, "bvult", &[i, old_len], Sort::Bool);
    let fill_guard = finite_quantifier_half_open_guard(&mut terms, i, old_len, new_len);
    let prefix = app(&mut terms, "=>", &[prefix_guard, prefix_eq], Sort::Bool);
    let suffix = app(&mut terms, "=>", &[fill_guard, fill_eq], Sort::Bool);
    let body = app(&mut terms, "and", &[prefix, suffix], Sort::Bool);
    let all = terms.mk_forall(vec![("i".to_string(), Sort::bitvec(64))], body);
    let wrong_prefix = StubModel::new().with(
        array,
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Int(int(1)),
            store: vec![(ModelValue::bitvec(int(5), 64), ModelValue::Int(int(2)))],
        })),
    );
    // The empty fill range does not erase the separately guarded prefix, nor
    // does new_len truncate the old_len guard in the producer's exact formula.
    assert_violates(&verdict(&terms, &wrong_prefix, &[all]));
}

#[test]
fn finite_quantifier_guarded_conjunction_retains_distant_disjoint_counterexample() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::bitvec(64));
    let zero = terms.mk_bitvec(int(0), 64);
    let two = terms.mk_bitvec(int(2), 64);
    let far = terms.mk_bitvec(int(1_000_000), 64);
    let far_end = terms.mk_bitvec(int(1_000_002), 64);
    let first = finite_quantifier_half_open_guard(&mut terms, i, zero, two);
    let second = finite_quantifier_half_open_guard(&mut terms, i, far, far_end);
    let array = terms.mk_var("array", Sort::array(Sort::bitvec(64), Sort::Int));
    let read = app(&mut terms, "select", &[array, i], Sort::Int);
    let value = terms.mk_int(int(0));
    let property = app(&mut terms, "=", &[read, value], Sort::Bool);
    let first = app(&mut terms, "=>", &[first, property], Sort::Bool);
    let second = app(&mut terms, "=>", &[second, property], Sort::Bool);
    let body = app(&mut terms, "and", &[first, second], Sort::Bool);
    let all = terms.mk_forall(vec![("i".to_string(), Sort::bitvec(64))], body);
    let model = StubModel::new().with(
        array,
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Int(int(0)),
            store: vec![(
                ModelValue::bitvec(int(1_000_001), 64),
                ModelValue::Int(int(1)),
            )],
        })),
    );
    assert_violates(&verdict(&terms, &model, &[all]));
}

#[test]
fn finite_quantifier_guarded_exists_unions_alternative_witness_ranges() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let zero = terms.mk_int(int(0));
    let two = terms.mk_int(int(2));
    let far = terms.mk_int(int(1000));
    let end = terms.mk_int(int(1002));
    let witness = terms.mk_int(int(1001));
    let first = finite_quantifier_half_open_guard(&mut terms, i, zero, two);
    let second = finite_quantifier_half_open_guard(&mut terms, i, far, end);
    let equal = app(&mut terms, "=", &[i, witness], Sort::Bool);
    let first = app(&mut terms, "and", &[first, equal], Sort::Bool);
    let second = app(&mut terms, "and", &[second, equal], Sort::Bool);
    let body = app(&mut terms, "or", &[first, second], Sort::Bool);
    let some = terms.mk_exists(vec![("i".to_string(), Sort::Int)], body);
    assert_confirmed(&verdict(&terms, &StubModel::new(), &[some]));
}

#[test]
fn finite_quantifier_guarded_support_cannot_reverse_quantifier_polarity() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let zero = terms.mk_int(int(0));
    let one = terms.mk_int(int(1));
    let at_zero = app(&mut terms, "=", &[i, zero], Sort::Bool);
    let at_one = app(&mut terms, "=", &[i, one], Sort::Bool);
    let either = app(&mut terms, "or", &[at_zero, at_one], Sort::Bool);
    let all = terms.mk_forall(vec![("i".to_string(), Sort::Int)], either);
    let no = terms.mk_bool(false);
    let implication = app(&mut terms, "=>", &[at_zero, no], Sort::Bool);
    let some = terms.mk_exists(vec![("i".to_string(), Sort::Int)], implication);
    // Universal counterexamples and existential witnesses live OUTSIDE the
    // apparent finite positive equality guards in these two formulas. The
    // equality-only planner (#eq-only-quantifier-eval) decides both EXACTLY
    // because its candidates include a fresh value outside every guard:
    // `∀i. i = 0 ∨ i = 1` is false (i = 2) and `∃i. i = 0 ⇒ false` is true.
    assert_violates(&verdict(&terms, &StubModel::new(), &[all]));
    assert_confirmed(&verdict(&terms, &StubModel::new(), &[some]));
    // With a non-equality occurrence (`i < i` is false, so the truth values
    // are unchanged) only the guarded-range support could apply, and it must
    // still refuse rather than reverse polarity.
    let irreflexive = app(&mut terms, "<", &[i, i], Sort::Bool);
    let either = app(&mut terms, "or", &[either, irreflexive], Sort::Bool);
    let all = terms.mk_forall(vec![("i".to_string(), Sort::Int)], either);
    let not_irreflexive = terms.mk_not(irreflexive);
    let implication = app(
        &mut terms,
        "and",
        &[implication, not_irreflexive],
        Sort::Bool,
    );
    let some = terms.mk_exists(vec![("i".to_string(), Sort::Int)], implication);
    assert_cannot(&verdict(&terms, &StubModel::new(), &[all]));
    assert_cannot(&verdict(&terms, &StubModel::new(), &[some]));
}

#[test]
fn finite_quantifier_guarded_endpoints_follow_outer_lexical_bindings() {
    let mut terms = TermStore::new();
    let outer = terms.mk_var("outer", Sort::Int);
    let i = terms.mk_var("i", Sort::Int);
    let zero = terms.mk_int(int(0));
    let upper = terms.mk_int(int(2));
    let inner_guard = finite_quantifier_half_open_guard(&mut terms, i, outer, upper);
    let equal = app(&mut terms, "=", &[i, outer], Sort::Bool);
    let inner = app(&mut terms, "and", &[inner_guard, equal], Sort::Bool);
    let inner = terms.mk_exists(vec![("i".to_string(), Sort::Int)], inner);
    let outer_guard = finite_quantifier_half_open_guard(&mut terms, outer, zero, upper);
    let body = app(&mut terms, "=>", &[outer_guard, inner], Sort::Bool);
    let all = terms.mk_forall(vec![("outer".to_string(), Sort::Int)], body);
    let model = StubModel::new().with(outer, ModelValue::Int(int(100)));
    assert_confirmed(&verdict(&terms, &model, &[all]));
}

#[test]
fn finite_quantifier_guarded_endpoints_refuse_same_name_unknown_and_wrong_sort() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let alias = terms.mk_fresh_named_var("i", Sort::Int);
    let unknown = terms.mk_var("unknown", Sort::Int);
    let zero = terms.mk_int(int(0));
    let upper = terms.mk_int(int(2));
    let yes = terms.mk_bool(true);
    for (lower, upper) in [(alias, upper), (zero, unknown)] {
        let guard = finite_quantifier_half_open_guard(&mut terms, i, lower, upper);
        let body = app(&mut terms, "and", &[guard, yes], Sort::Bool);
        let some = terms.mk_exists(vec![("i".to_string(), Sort::Int)], body);
        let model = StubModel::new().with(alias, ModelValue::Int(int(0)));
        assert_cannot(&verdict(&terms, &model, &[some]));
        let ill_typed = model.with(unknown, ModelValue::Bool(false));
        assert_cannot(&verdict(&terms, &ill_typed, &[some]));
    }
}

#[test]
fn finite_quantifier_guarded_support_respects_model_projection_precedence() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::bitvec(64));
    let zero = terms.mk_bitvec(int(0), 64);
    let seven = terms.mk_bitvec(int(7), 64);
    let at_seven = app(&mut terms, "=", &[i, seven], Sort::Bool);
    let yes = terms.mk_bool(true);
    let not_seven = terms.mk_not(at_seven);
    let connective = app(&mut terms, "or", &[not_seven, yes], Sort::Bool);
    let all = terms.mk_forall(vec![("i".to_string(), Sort::bitvec(64))], connective);
    let projected = UfStubModel::new().projection(connective, 0);
    // Structural OR would prove this vacuous; its actual projected value has
    // a counterexample at seven. Refuse to mint the structural range theorem.
    assert_cannot(&verdict(&terms, &projected, &[all]));
    let errored = UfStubModel::new().projection_error(connective, "stale projection");
    assert_cannot(&verdict(&terms, &errored, &[all]));

    let comparison = app(&mut terms, "bvuge", &[i, zero], Sort::Bool);
    let all = terms.mk_forall(vec![("i".to_string(), Sort::bitvec(64))], comparison);
    assert_confirmed(&verdict(&terms, &StubModel::new(), &[all]));
    // A projection selects a BV argument for a Bool result here; ordinary
    // evaluation rejects that mismatch, so empty support cannot launder it.
    let projected = UfStubModel::new().projection(comparison, 0);
    assert_cannot(&verdict(&terms, &projected, &[all]));
}

#[test]
fn finite_quantifier_guarded_support_refuses_compound_and_oversized_signed_bounds() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::bitvec(64));
    let zero = terms.mk_bitvec(int(0), 64);
    let one = terms.mk_bitvec(int(1), 64);
    let upper = terms.mk_bitvec(int(3), 64);
    let shifted = app(&mut terms, "bvadd", &[i, one], Sort::bitvec(64));
    let wrapped_guard = app(&mut terms, "bvult", &[shifted, upper], Sort::Bool);
    // Signed order is supported, but i < 3 includes the entire negative
    // half-carrier: deriving support must still refuse the assignment budget.
    let signed_guard = app(&mut terms, "bvslt", &[i, upper], Sort::Bool);
    let property = app(&mut terms, "=", &[i, zero], Sort::Bool);
    for guard in [wrapped_guard, signed_guard] {
        let body = app(&mut terms, "=>", &[guard, property], Sort::Bool);
        let all = terms.mk_forall(vec![("i".to_string(), Sort::bitvec(64))], body);
        assert_cannot(&verdict(&terms, &StubModel::new(), &[all]));
    }
}

#[test]
fn finite_quantifier_guarded_analysis_spends_outermost_work_and_assignment_budgets() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::bitvec(64));
    let upper = terms.mk_bitvec(int(65_537), 64);
    let unknown = terms.mk_var("unknown", Sort::Bool);
    let guard = app(&mut terms, "bvult", &[i, upper], Sort::Bool);
    let body = app(&mut terms, "=>", &[guard, unknown], Sort::Bool);
    let too_many = terms.mk_forall(vec![("i".to_string(), Sort::bitvec(64))], body);
    assert!(matches!(
        evaluate_term(&terms, &StubModel::new(), too_many),
        EvalOutcome::Unevaluable(reason) if reason.contains("assignment budget")
    ));
    let zero = terms.mk_bitvec(int(0), 64);
    let mut wide_dag = app(&mut terms, "bvuge", &[i, zero], Sort::Bool);
    // Only twenty new term nodes, but naive repeated support traversal exceeds
    // the shared work envelope before its empty support can be accepted.
    for _ in 0..20 {
        wide_dag = app(&mut terms, "and", &[wide_dag, wide_dag], Sort::Bool);
    }
    let all = terms.mk_forall(vec![("i".to_string(), Sort::bitvec(64))], wide_dag);
    assert!(matches!(
        evaluate_term(&terms, &StubModel::new(), all),
        EvalOutcome::Unevaluable(reason) if reason.contains("evaluation work budget")
    ));
}

#[test]
fn finite_quantifier_guarded_support_depth_cap_rejects_65_and_accepts_64() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let zero = terms.mk_int(int(0));
    let mut body = app(&mut terms, "=", &[i, zero], Sort::Bool);
    for _ in 0..64 {
        // Keep the linear support-analysis depth: mk_not folds double negations.
        body = terms.mk_not_raw(body);
    }
    let at_limit = terms.mk_exists(vec![("i".to_string(), Sort::Int)], body);
    body = terms.mk_not_raw(body);
    let over_limit = terms.mk_exists(vec![("i".to_string(), Sort::Int)], body);
    let model = StubModel::new();
    let evaluator = Evaluator::new(&terms, &model);
    assert!(matches!(
        evaluator.evaluate(over_limit),
        EvalOutcome::Unevaluable(reason) if reason.contains("nesting or native evaluation depth")
    ));
    // This fresh root also proves the failed analysis restored nesting; its
    // source evaluation stays below the separate 128-native-call backstop.
    assert!(matches!(
        evaluator.evaluate(at_limit),
        EvalOutcome::Value(ModelValue::Bool(true))
    ));
}

#[test]
fn finite_quantifier_guarded_endpoint_bit_cap_is_inclusive() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let at_limit = terms.mk_int(BigInt::from(1u8) << 4095usize);
    let over_limit = terms.mk_int(BigInt::from(1u8) << 4096usize);
    let at_limit = app(&mut terms, "=", &[i, at_limit], Sort::Bool);
    let over_limit = app(&mut terms, "=", &[i, over_limit], Sort::Bool);
    let at_limit = terms.mk_exists(vec![("i".to_string(), Sort::Int)], at_limit);
    let over_limit = terms.mk_exists(vec![("i".to_string(), Sort::Int)], over_limit);
    let model = StubModel::new();
    let evaluator = Evaluator::new(&terms, &model);
    // Each endpoint costs only about 512 bytes. Both supports are singletons,
    // so this isolates numeric-size refusal from the assignment limit.
    assert!(matches!(
        evaluator.evaluate(over_limit),
        EvalOutcome::Unevaluable(reason) if reason.contains("evaluation work budget")
    ));
    assert!(matches!(
        evaluator.evaluate(at_limit),
        EvalOutcome::Value(ModelValue::Bool(true))
    ));
}

#[test]
fn finite_quantifier_guarded_support_refuses_257_disjoint_singletons() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::bitvec(64));
    let mut layer: Vec<_> = (0..257)
        .map(|value| {
            // Leave a gap between singletons so interval normalization cannot
            // merge them into one contiguous range.
            let endpoint = terms.mk_bitvec(int(value * 2), 64);
            app(&mut terms, "=", &[i, endpoint], Sort::Bool)
        })
        .collect();
    // Balance the OR tree so the interval-count cap is reached before the
    // quadratic work charges of a sequential 257-way fold would exhaust work.
    while layer.len() > 1 {
        let mut next = Vec::new();
        for children in layer.chunks(2) {
            next.push(match children {
                [left, right] => app(&mut terms, "or", &[*left, *right], Sort::Bool),
                [only] => *only,
                _ => unreachable!("nonempty chunks of at most two"),
            });
        }
        layer = next;
    }
    let body = *layer.first().expect("nonempty disjunction");
    let some = terms.mk_exists(vec![("i".to_string(), Sort::bitvec(64))], body);
    assert!(matches!(
        evaluate_term(&terms, &StubModel::new(), some),
        EvalOutcome::Unevaluable(reason) if reason.contains("evaluation work budget")
    ));
}

#[test]
fn finite_quantifier_guarded_bv_width_cap_accepts_128_and_refuses_129() {
    let mut terms = TermStore::new();
    let mut cases = Vec::new();
    for width in [128, 129] {
        let name = format!("i_{width}");
        let i = terms.mk_var(&name, Sort::bitvec(width));
        let endpoint = terms.mk_bitvec(BigInt::from(1u8) << 127usize, width);
        let body = app(&mut terms, "=", &[i, endpoint], Sort::Bool);
        let some = terms.mk_exists(vec![(name, Sort::bitvec(width))], body);
        cases.push((width, some));
    }
    let model = StubModel::new();
    let evaluator = Evaluator::new(&terms, &model);
    for (width, some) in cases {
        let actual = evaluator.evaluate(some);
        if width == 128 {
            assert!(matches!(actual, EvalOutcome::Value(ModelValue::Bool(true))));
        } else {
            // Unsupported range width retains the original full-carrier
            // assignment-budget refusal, even though this guard is a singleton.
            assert!(matches!(
                actual,
                EvalOutcome::Unevaluable(reason) if reason.contains("assignment budget")
            ));
        }
    }
}
