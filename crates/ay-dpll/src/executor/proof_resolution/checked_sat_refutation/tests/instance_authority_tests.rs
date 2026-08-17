// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn changed_source_stamp_retires_checked_sidecar() {
    let (mut executor, _, _) = contradictory_unit_executor();
    let mut trust_proof = Proof::new();
    trust_proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    executor.last_proof = Some(trust_proof);

    executor
        .ctx
        .process_command(&Command::Push(1))
        .expect("direct frontend mutation succeeds");
    let result = executor.certify_unsat_for_publication(SolveResult::unsat(), &[]);
    assert!(result.is_unknown());
    assert!(executor.take_unsat_certificate().is_none());
}

#[test]
fn missing_authoritative_namespace_and_nonempty_assumptions_decline() {
    let (mut unstamped, _) = unstamped_contradictory_unit_executor();
    unstamped.refresh_checked_sat_refutation();
    assert!(unstamped.last_checked_sat_refutation.is_none());

    let (mut assuming, proposition) = unstamped_contradictory_unit_executor();
    assuming.bind_unsat_query_assumptions(&[proposition]);
    assuming.refresh_checked_sat_refutation();
    assert!(assuming.last_checked_sat_refutation.is_none());
}

#[test]
fn finite_replay_limits_remain_explicit() {
    let executor = Executor::new();
    let limits = validation_limits(&executor);
    assert!(limits.max_original_clauses < usize::MAX);
    assert!(limits.max_derived_steps < usize::MAX);
    assert!(limits.max_work < u64::MAX);
    assert!(limits.max_bytes < usize::MAX);
}

/// Well-formed positive-`exists` Skolemization record over a fresh executor:
/// `exists x. P(x)` with a registered choice witness and the exact raw
/// substituted instance (#quant-unit-authority).
fn sealed_skolem_record_fixture() -> (Executor, SkolemInstanceRecord) {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("sse_x", Sort::Int);
    let body = executor
        .ctx
        .terms
        .mk_app(ay_core::Symbol::named("sse_p"), [x], Sort::Bool);
    let quantified = executor
        .ctx
        .terms
        .mk_exists(vec![("sse_x".to_string(), Sort::Int)], body);
    let witness = executor.ctx.terms.mk_var("sk!sse_x", Sort::Int);
    executor.ctx.terms.mark_skolem_symbol("sk!sse_x");
    executor.ctx.terms.register_skolem_choice(
        witness,
        ay_core::SkolemChoice {
            binder: "sse_x".to_string(),
            sort: Sort::Int,
            body,
        },
    );
    let mut substitution = HashMap::default();
    substitution.insert("sse_x".to_string(), witness);
    let instance =
        crate::ematching::subst_vars_exact_qf(&mut executor.ctx.terms, body, &substitution)
            .expect("closed single-binder substitution succeeds");
    let record = SkolemInstanceRecord {
        source: quantified,
        quantified,
        witness,
        instance,
        asserted: instance,
        positive: true,
    };
    (executor, record)
}

#[test]
fn live_epoch_skolem_instance_record_seals_and_consumes() {
    let (mut executor, record) = sealed_skolem_record_fixture();
    let token = CheckedSkolemDerivation::seal(&mut executor, &record)
        .expect("well-formed record must seal");
    assert!(
        token.into_current(&executor).is_some(),
        "a live-epoch token must consume into a fragment derivation"
    );
}

#[test]
fn stale_epoch_skolem_instance_record_seals_to_none() {
    let (mut executor, record) = sealed_skolem_record_fixture();
    let token = CheckedSkolemDerivation::seal(&mut executor, &record)
        .expect("well-formed record must seal");
    executor.query_authority_epoch = QueryAuthorityEpoch::fresh();
    assert!(
        token.into_current(&executor).is_none(),
        "a stale-epoch record must seal to None"
    );
}

/// Well-formed BV-MBQI eval-folded-`false` instance record over a fresh
/// executor (#bv-mbqi-false-instance-authority, P3b): the evil broadcast body
/// `bvslt (bvmul x x) #x00` at `x = 0` is definitively false.
fn bv_mbqi_false_record_fixture() -> (Executor, crate::executor::BvMbqiFalseInstanceRecord) {
    let mut executor = Executor::new();
    let width = 8u32;
    let bv_sort = Sort::BitVec(ay_core::BitVecSort::new(width));
    let x = executor.ctx.terms.mk_var("bmf_x", bv_sort.clone());
    let square =
        executor
            .ctx
            .terms
            .mk_app(ay_core::Symbol::named("bvmul"), [x, x], bv_sort.clone());
    let zero = executor
        .ctx
        .terms
        .mk_bitvec(num_bigint::BigInt::ZERO, width);
    let body =
        executor
            .ctx
            .terms
            .mk_app(ay_core::Symbol::named("bvslt"), [square, zero], Sort::Bool);
    let quantifier = executor
        .ctx
        .terms
        .mk_forall(vec![("bmf_x".to_string(), bv_sort)], body);
    let mut substitution = HashMap::default();
    substitution.insert("bmf_x".to_string(), zero);
    let instance =
        crate::ematching::subst_vars_exact_qf(&mut executor.ctx.terms, body, &substitution)
            .expect("closed single-binder substitution succeeds");
    let asserted = executor.ctx.terms.false_term();
    let record = crate::executor::BvMbqiFalseInstanceRecord {
        quantifier,
        values: vec![zero],
        instance,
        asserted,
    };
    (executor, record)
}

#[test]
fn live_epoch_bv_mbqi_false_instance_record_seals_and_consumes() {
    let (mut executor, record) = bv_mbqi_false_record_fixture();
    let token = CheckedInstanceDerivation::seal(
        &mut executor,
        record.quantifier,
        &record.values,
        record.instance,
        record.asserted,
    )
    .expect("well-formed eval-folded-false record must seal");
    let (key, derivation) = token
        .into_current(&executor)
        .expect("a live-epoch token must consume");
    assert_eq!(key, executor.ctx.terms.false_term());
    assert_eq!(derivation.quantifier, record.quantifier);
    assert_eq!(derivation.instance, record.instance);
}

#[test]
fn stale_epoch_bv_mbqi_false_instance_record_seals_to_none() {
    let (mut executor, record) = bv_mbqi_false_record_fixture();
    let token = CheckedInstanceDerivation::seal(
        &mut executor,
        record.quantifier,
        &record.values,
        record.instance,
        record.asserted,
    )
    .expect("well-formed eval-folded-false record must seal");
    executor.query_authority_epoch = QueryAuthorityEpoch::fresh();
    assert!(
        token.into_current(&executor).is_none(),
        "a stale-epoch record must fail consumption"
    );
}

#[test]
fn bv_mbqi_record_keyed_by_wrong_term_is_refused() {
    let (mut executor, record) = bv_mbqi_false_record_fixture();
    let wrong_key = executor.ctx.terms.true_term();
    assert!(
        CheckedInstanceDerivation::seal(
            &mut executor,
            record.quantifier,
            &record.values,
            record.instance,
            wrong_key,
        )
        .is_none(),
        "a record keyed by a non-false fold target must be refused"
    );
}

#[test]
fn bv_mbqi_record_with_non_false_instance_is_refused() {
    let (mut executor, record) = bv_mbqi_false_record_fixture();
    let TermData::Forall(bindings, body, _) = executor.ctx.terms.get(record.quantifier).clone()
    else {
        unreachable!("fixture quantifier is a forall");
    };
    let negated_body = executor.ctx.terms.mk_not_raw(body);
    let negated_quantifier = executor
        .ctx
        .terms
        .mk_forall(bindings.to_vec(), negated_body);
    let mut substitution = HashMap::default();
    substitution.insert("bmf_x".to_string(), record.values[0]);
    let true_instance =
        crate::ematching::subst_vars_exact_qf(&mut executor.ctx.terms, negated_body, &substitution)
            .expect("closed substitution succeeds");
    let false_key = executor.ctx.terms.false_term();
    assert!(
        CheckedInstanceDerivation::seal(
            &mut executor,
            negated_quantifier,
            &record.values,
            true_instance,
            false_key,
        )
        .is_none(),
        "a fold claim whose instance does not evaluate to false must be refused"
    );
}
