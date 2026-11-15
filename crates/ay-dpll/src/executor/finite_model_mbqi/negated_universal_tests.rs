// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Negated-universal guards for the finite-model MBQI lane, included in
// `finite_model_mbqi::refinable_contract_tests` so they share its fixtures
// (`f32_sort`, `atom`, `forall_p`, `leaf_flags`) and keep stable test names.

/// The BEHAVIOUR the `refinable` flag exists to control, driven through
/// `try_finite_model_forall_refinement` itself on a `NOT forall x. P(x)`
/// problem. This bypasses the upstream `has_unsafe_partial_quantifiers` guard
/// on purpose: a fix that holds only because something upstream blocks the
/// path is not a fix.
///
/// CONTRACT: on a problem asserting `NOT forall x. P(x)`, the lane never pushes
/// a ground instance onto `ctx.assertions` and never returns `Unsat`. `P(v)` is
/// not a consequence of `NOT forall x. P(x)`, so a re-solve refuting it would
/// publish a wrong `Unsat`.
#[test]
fn lane_never_asserts_an_instance_of_a_negated_universal() {
    let mut executor = Executor::new();
    // `forall x:Float32. (or (fp.isNaN x) q)`, with `q` a nullary Bool symbol.
    // `q` is an `App`, not a `Var`, so `collect_finite_var_leaves` never pins
    // it: the pin set is empty (and total), and the universal stays
    // UNDETERMINED under it, which drives `finite_model_truth_value` to the
    // `Refine` arm this guard protects.
    let forall = {
        let t = &mut executor.ctx.terms;
        let x = t.mk_var("x", f32_sort());
        let is_nan = t.mk_app(Symbol::named("fp.isNaN"), [x], Sort::Bool);
        let q = t.mk_app(Symbol::named("q"), [], Sort::Bool);
        let body = t.mk_or(vec![is_nan, q]);
        t.mk_forall(vec![("x".to_string(), f32_sort())], body)
    };
    let root = executor.ctx.terms.mk_not(forall);
    assert!(
        matches!(executor.ctx.terms.get(root), TermData::Not(inner) if *inner == forall),
        "fixture must stay a literal Not(Forall)"
    );
    // A fresh Executor has no authored-root window, so
    // `independent_gate_query_roots` falls back to `ctx.assertions`.
    executor.ctx.assertions.push(root);
    executor.last_model = Some(crate::executor::model::Model::empty());

    // NON-VACUITY: the fixture must reach the `Refine` arm the guard protects.
    // Without this the test passes whenever the lane declines for an unrelated
    // reason (a partial pin set, a closed lane, a determined truth value).
    {
        let budget = executor
            .finite_model_lane_open()
            .expect("fresh session has seed capital");
        let leaves =
            authored_universal_leaves_impl(&mut executor, &[root]).expect("leaves classify");
        let mut completions = Vec::new();
        let (pins, total) = executor.finite_model_pins(&leaves, &mut completions);
        assert!(
            total,
            "pin set not total: the pass would decline before the guard, so the \
             test would be vacuous"
        );
        assert!(
            matches!(
                executor.finite_model_truth_value(&leaves[0], &pins, budget),
                TruthOutcome::Refine(_)
            ),
            "fixture no longer reaches TruthOutcome::Refine, so it no longer \
             exercises the guard; repair the fixture rather than the assertion"
        );
    }

    let before = executor.ctx.assertions.clone();
    let result = executor.try_finite_model_forall_refinement(&[forall], LogicCategory::Other);

    assert_eq!(
        executor.ctx.assertions, before,
        "#quant-alternation: the lane asserted a ground instance of a universal \
         that sits under a `not`. `P(v)` is NOT a consequence of \
         `NOT forall x. P(x)`, and a re-solve refuting it publishes a wrong Unsat."
    );
    assert!(
        !matches!(result, Some(Ok(SolveResult::Unsat(_)))),
        "the lane refuted a query it has no refutation of"
    );
}

/// `NOT (p => forall x. P(x))`, equivalently `p AND NOT forall x. P(x)`: a
/// negated universal reached through a negated implication. Not a
/// consequence, so not refinable.
///
/// This guards a shape the shared classifier
/// (`forall_ids_in_conjunctive_position`, `quantifier_loop/result_mapping.rs`)
/// falls through on: a negated `=>` takes none of its descent arms, so no id
/// under it is in the conjunctive set. It is NOT a reproduction of the
/// 36d902d8ee bug; it pins that the flag stays false however the classifier
/// later learns to descend here.
#[test]
fn negated_universal_under_an_implication_is_never_refinable() {
    let mut executor = Executor::new();
    let forall = forall_p(&mut executor.ctx.terms);
    let p = atom(&mut executor.ctx.terms, "p");
    let implication = executor
        .ctx
        .terms
        .mk_app(Symbol::named("=>"), [p, forall], Sort::Bool);
    let root = executor.ctx.terms.mk_not(implication);
    assert!(
        matches!(executor.ctx.terms.get(root), TermData::Not(inner) if *inner == implication),
        "fixture must stay a literal Not(=>); mk_not rewrote it instead"
    );

    let (_, refinable) = leaf_flags(&mut executor, &[root], forall);
    assert!(
        !refinable,
        "#quant-alternation: `NOT (p => forall x. P(x))` entails no instance of P"
    );
}

/// A universal reached only through an `ite` branch is not a conjunct.
///
/// Like the implication case, this guards a shape the shared classifier
/// (`forall_ids_in_conjunctive_position`) falls through on — an `Ite` node
/// takes no descent arm — rather than reproducing the 36d902d8ee bug.
#[test]
fn universal_under_an_ite_is_never_refinable() {
    let mut executor = Executor::new();
    let forall = forall_p(&mut executor.ctx.terms);
    let c = atom(&mut executor.ctx.terms, "c");
    let d = atom(&mut executor.ctx.terms, "d");
    let root = executor.ctx.terms.mk_ite(c, forall, d);
    assert!(
        matches!(executor.ctx.terms.get(root), TermData::Ite(..)),
        "fixture must stay a literal Ite; mk_ite simplified it instead"
    );

    let (_, refinable) = leaf_flags(&mut executor, &[root], forall);
    assert!(!refinable, "an `ite` branch is not a top-level conjunct");
}
