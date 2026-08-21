// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `proof_tracker::tests` to preserve the regression FQN.

#[cfg(test)]
struct NormalizedForallFixture {
    terms: TermStore,
    x: TermId,
    k: TermId,
    n: TermId,
    zero: TermId,
    cond: TermId,
    p_x: TermId,
    q_x: TermId,
    ite_x: TermId,
    not_nonnegative_x: TermId,
    not_in_upper_bound_x: TermId,
    authored_body: TermId,
    authored: TermId,
    below_zero_x: TermId,
    at_or_above_n_x: TermId,
    normalized: TermId,
    p_k: TermId,
    q_k: TermId,
    ite_k: TermId,
    below_zero_k: TermId,
    at_or_above_n_k: TermId,
    target: TermId,
}

#[cfg(test)]
impl NormalizedForallFixture {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let x = terms.mk_var("normalized_forall_x", Sort::Int);
        let k = terms.mk_var("normalized_forall_k", Sort::Int);
        let n = terms.mk_var("normalized_forall_n", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let cond = terms.mk_var("normalized_forall_cond", Sort::Bool);
        let p_x = terms.mk_app(Symbol::named("normalized_forall_p"), [x], Sort::Bool);
        let q_x = terms.mk_app(Symbol::named("normalized_forall_q"), [x], Sort::Bool);
        let ite_x = terms.mk_ite_raw(cond, p_x, q_x);
        let nonnegative_x = terms.mk_le(zero, x);
        let in_upper_bound_x = terms.mk_lt(x, n);
        let not_nonnegative_x = terms.mk_not_raw(nonnegative_x);
        let not_in_upper_bound_x = terms.mk_not_raw(in_upper_bound_x);
        let authored_body = terms.mk_or(vec![ite_x, not_nonnegative_x, not_in_upper_bound_x]);
        let authored = terms.mk_forall(
            vec![("normalized_forall_x".to_string(), Sort::Int)],
            authored_body,
        );
        let below_zero_x = terms.mk_lt(x, zero);
        let at_or_above_n_x = terms.mk_le(n, x);
        let normalized_body = terms.mk_or(vec![ite_x, below_zero_x, at_or_above_n_x]);
        let normalized = terms.mk_forall(
            vec![("normalized_forall_x".to_string(), Sort::Int)],
            normalized_body,
        );
        let p_k = terms.mk_app(Symbol::named("normalized_forall_p"), [k], Sort::Bool);
        let q_k = terms.mk_app(Symbol::named("normalized_forall_q"), [k], Sort::Bool);
        let ite_k = terms.mk_ite_raw(cond, p_k, q_k);
        let below_zero_k = terms.mk_lt(k, zero);
        let at_or_above_n_k = terms.mk_le(n, k);
        let target = terms.mk_or(vec![ite_k, below_zero_k, at_or_above_n_k]);
        Self {
            terms,
            x,
            k,
            n,
            zero,
            cond,
            p_x,
            q_x,
            ite_x,
            not_nonnegative_x,
            not_in_upper_bound_x,
            authored_body,
            authored,
            below_zero_x,
            at_or_above_n_x,
            normalized,
            p_k,
            q_k,
            ite_k,
            below_zero_k,
            at_or_above_n_k,
            target,
        }
    }
}

#[cfg(test)]
fn assert_normalized_forall_rejected(
    authored: TermId,
    normalized: TermId,
    values: &[TermId],
    target: TermId,
    reason: &str,
    terms: &mut TermStore,
) {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    assert!(
        tracker
            .add_normalized_forall_instantiated_assertion(
                terms, authored, normalized, values, target,
            )
            .is_none(),
        "{reason}"
    );
    assert_eq!(
        tracker.num_steps(),
        0,
        "{reason}: rejection must precede proof emission"
    );
}

#[cfg(test)]
fn assert_normalized_forall_happy_path(fixture: &mut NormalizedForallFixture) {
    let authored = fixture.authored;
    let normalized = fixture.normalized;
    let k = fixture.k;
    let target = fixture.target;
    let mut tracker = ProofTracker::new();
    tracker.enable();
    let derived = tracker
        .add_normalized_forall_instantiated_assertion(
            &mut fixture.terms,
            authored,
            normalized,
            &[k],
            target,
        )
        .expect("exact NNF arithmetic normalization must have a checked derivation");
    let mut proof = tracker.take_proof();
    assert!(
        matches!(
            proof.get_step(derived),
            Some(ProofStep::Resolution { clause, .. }) if clause == &[target]
        ),
        "tracker must derive the exact E-matching target"
    );
    let not_target = fixture.terms.mk_not_raw(target);
    let negated = proof.add_assume(not_target, None);
    proof.add_resolution(Vec::new(), target, derived, negated);
    let quality = ay_proof::check_proof_strict_with_context(
        &proof,
        &fixture.terms,
        None,
        None,
        Some(&[authored, not_target]),
    )
    .expect("normalized forall derivation must pass the independent strict checker");
    assert!(quality.is_complete());
    assert_eq!(quality.trust_count, 0);
}

#[cfg(test)]
fn assert_primary_normalization_rejections(f: &mut NormalizedForallFixture) {
    let minus_one = f.terms.mk_int(BigInt::from(-1));
    let forged_below_minus_one_x = f.terms.mk_lt(f.x, minus_one);
    let forged_normalized_body =
        f.terms
            .mk_or(vec![f.ite_x, forged_below_minus_one_x, f.at_or_above_n_x]);
    let forged_normalized = f.terms.mk_forall(
        vec![("normalized_forall_x".to_string(), Sort::Int)],
        forged_normalized_body,
    );
    let forged_below_minus_one = f.terms.mk_lt(f.k, minus_one);
    let forged_bound = f
        .terms
        .mk_or(vec![f.ite_k, forged_below_minus_one, f.at_or_above_n_k]);
    assert_normalized_forall_rejected(
        f.authored,
        forged_normalized,
        &[f.k],
        forged_bound,
        "a changed arithmetic bound must fail the Farkas gate",
        &mut f.terms,
    );

    let forged_eq_zero_x = f.terms.mk_eq(f.x, f.zero);
    let forged_operator_body = f
        .terms
        .mk_or(vec![f.ite_x, forged_eq_zero_x, f.at_or_above_n_x]);
    let forged_operator_quantified = f.terms.mk_forall(
        vec![("normalized_forall_x".to_string(), Sort::Int)],
        forged_operator_body,
    );
    let forged_eq_zero_k = f.terms.mk_eq(f.k, f.zero);
    let forged_operator_target = f
        .terms
        .mk_or(vec![f.ite_k, forged_eq_zero_k, f.at_or_above_n_k]);
    assert_normalized_forall_rejected(
        f.authored,
        forged_operator_quantified,
        &[f.k],
        forged_operator_target,
        "a changed comparison operator must fail the Farkas gate",
        &mut f.terms,
    );

    let forged_p_x = f.terms.mk_app(
        Symbol::named("normalized_forall_forged_p"),
        [f.x],
        Sort::Bool,
    );
    let forged_ite_x = f.terms.mk_ite_raw(f.cond, forged_p_x, f.q_x);
    let forged_branch_body = f
        .terms
        .mk_or(vec![forged_ite_x, f.below_zero_x, f.at_or_above_n_x]);
    let forged_branch_quantified = f.terms.mk_forall(
        vec![("normalized_forall_x".to_string(), Sort::Int)],
        forged_branch_body,
    );
    let forged_p_k = f.terms.mk_app(
        Symbol::named("normalized_forall_forged_p"),
        [f.k],
        Sort::Bool,
    );
    let forged_ite_k = f.terms.mk_ite_raw(f.cond, forged_p_k, f.q_k);
    let forged_branch_target = f
        .terms
        .mk_or(vec![forged_ite_k, f.below_zero_k, f.at_or_above_n_k]);
    assert_normalized_forall_rejected(
        f.authored,
        forged_branch_quantified,
        &[f.k],
        forged_branch_target,
        "a changed Boolean branch must not be admitted as arithmetic normalization",
        &mut f.terms,
    );
    assert_normalized_forall_rejected(
        f.authored,
        f.normalized,
        &[f.cond],
        f.target,
        "a wrong-sort positional binding must fail closed",
        &mut f.terms,
    );
}

#[cfg(test)]
fn assert_source_and_trigger_rejections(f: &mut NormalizedForallFixture) {
    let other_p_x = f.terms.mk_app(
        Symbol::named("normalized_forall_other_source"),
        [f.x],
        Sort::Bool,
    );
    let other_ite_x = f.terms.mk_ite_raw(f.cond, other_p_x, f.q_x);
    let other_authored_body = f.terms.mk_or(vec![
        other_ite_x,
        f.not_nonnegative_x,
        f.not_in_upper_bound_x,
    ]);
    let other_authored = f.terms.mk_forall(
        vec![("normalized_forall_x".to_string(), Sort::Int)],
        other_authored_body,
    );
    assert_normalized_forall_rejected(
        other_authored,
        f.normalized,
        &[f.k],
        f.target,
        "a forged authored source mapping must fail exact/Farkas validation",
        &mut f.terms,
    );

    let triggered_authored = f.terms.mk_forall_with_triggers(
        vec![("normalized_forall_x".to_string(), Sort::Int)],
        f.authored_body,
        vec![vec![f.p_x]],
    );
    assert_normalized_forall_rejected(
        triggered_authored,
        f.normalized,
        &[f.k],
        f.target,
        "source and normalized trigger groups must agree exactly",
        &mut f.terms,
    );
}

#[cfg(test)]
fn assert_order_and_shape_rejections(f: &mut NormalizedForallFixture) {
    let z = f.terms.mk_var("normalized_forall_z", Sort::Int);
    let pair_x_z = f.terms.mk_app(
        Symbol::named("normalized_forall_pair"),
        [f.x, z],
        Sort::Bool,
    );
    let ordered_authored_body = f.terms.mk_or(vec![pair_x_z, f.not_nonnegative_x]);
    let ordered_authored = f.terms.mk_forall(
        vec![
            ("normalized_forall_x".to_string(), Sort::Int),
            ("normalized_forall_z".to_string(), Sort::Int),
        ],
        ordered_authored_body,
    );
    let ordered_normalized_body = f.terms.mk_or(vec![pair_x_z, f.below_zero_x]);
    let ordered_normalized = f.terms.mk_forall(
        vec![
            ("normalized_forall_x".to_string(), Sort::Int),
            ("normalized_forall_z".to_string(), Sort::Int),
        ],
        ordered_normalized_body,
    );
    let pair_k_n = f.terms.mk_app(
        Symbol::named("normalized_forall_pair"),
        [f.k, f.n],
        Sort::Bool,
    );
    let ordered_target = f.terms.mk_or(vec![pair_k_n, f.below_zero_k]);
    assert_normalized_forall_rejected(
        ordered_authored,
        ordered_normalized,
        &[f.n, f.k],
        ordered_target,
        "same-sort binding values in the wrong positional order must fail closed",
        &mut f.terms,
    );

    let short_normalized_body = f.terms.mk_or(vec![f.ite_x, f.below_zero_x]);
    let short_normalized = f.terms.mk_forall(
        vec![("normalized_forall_x".to_string(), Sort::Int)],
        short_normalized_body,
    );
    let short_target = f.terms.mk_or(vec![f.ite_k, f.below_zero_k]);
    assert_normalized_forall_rejected(
        f.authored,
        short_normalized,
        &[f.k],
        short_target,
        "a normalized target with changed disjunct arity must fail closed",
        &mut f.terms,
    );

    let nonflat_normalized = f
        .terms
        .mk_forall(vec![("normalized_forall_x".to_string(), Sort::Int)], f.p_x);
    assert_normalized_forall_rejected(
        f.authored,
        nonflat_normalized,
        &[f.k],
        f.p_k,
        "a non-disjunctive normalized target must fail closed",
        &mut f.terms,
    );
}

#[cfg(test)]
fn assert_nested_binder_behavior(f: &mut NormalizedForallFixture) {
    let y = f.terms.mk_var("normalized_forall_y", Sort::Int);
    let nested_p_y = f
        .terms
        .mk_app(Symbol::named("normalized_forall_nested"), [y], Sort::Bool);
    let nested = f.terms.mk_forall(
        vec![("normalized_forall_y".to_string(), Sort::Int)],
        nested_p_y,
    );
    let nested_authored_body = f.terms.mk_or(vec![nested, f.not_nonnegative_x]);
    let nested_authored = f.terms.mk_forall(
        vec![("normalized_forall_x".to_string(), Sort::Int)],
        nested_authored_body,
    );
    let nested_normalized_body = f.terms.mk_or(vec![nested, f.below_zero_x]);
    let nested_normalized = f.terms.mk_forall(
        vec![("normalized_forall_x".to_string(), Sort::Int)],
        nested_normalized_body,
    );
    let nested_target = f.terms.mk_or(vec![nested, f.below_zero_k]);
    let mut nested_tracker = ProofTracker::new();
    nested_tracker.enable();
    let nested_derived = nested_tracker
        .add_normalized_forall_instantiated_assertion(
            &mut f.terms,
            nested_authored,
            nested_normalized,
            &[f.k],
            nested_target,
        )
        .expect("capture-free substitution below a preserved nested binder must derive");
    let mut nested_proof = nested_tracker.take_proof();
    assert!(
        matches!(
            nested_proof.get_step(nested_derived),
            Some(ProofStep::Resolution { clause, .. }) if clause == &[nested_target]
        ),
        "tracker must derive the exact nested-binder E-matching target"
    );
    let not_nested_target = f.terms.mk_not_raw(nested_target);
    let nested_negated = nested_proof.add_assume(not_nested_target, None);
    nested_proof.add_resolution(Vec::new(), nested_target, nested_derived, nested_negated);
    let nested_quality = ay_proof::check_proof_strict_with_context(
        &nested_proof,
        &f.terms,
        None,
        None,
        Some(&[nested_authored, not_nested_target]),
    )
    .expect("the independent checker must accept the capture-free nested-binder proof");
    assert!(nested_quality.is_complete());
    assert_eq!(nested_quality.trust_count, 0);

    let below_zero_y = f.terms.mk_lt(y, f.zero);
    let captured_target = f.terms.mk_or(vec![nested, below_zero_y]);
    assert_normalized_forall_rejected(
        nested_authored,
        nested_normalized,
        &[y],
        captured_target,
        "an argument sharing a nested binder name must fail closed before capture",
        &mut f.terms,
    );
}

#[test]
fn test_normalized_forall_instance_uses_strict_farkas_rewrites() {
    let mut fixture = NormalizedForallFixture::new();
    assert_normalized_forall_happy_path(&mut fixture);
    assert_primary_normalization_rejections(&mut fixture);
    assert_source_and_trigger_rejections(&mut fixture);
    assert_order_and_shape_rejections(&mut fixture);
    assert_nested_binder_behavior(&mut fixture);
}
