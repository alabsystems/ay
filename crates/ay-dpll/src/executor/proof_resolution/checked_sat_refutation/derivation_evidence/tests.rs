// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{SkolemChoice, Sort, Symbol};

use super::*;

fn sealed_skolem_record_fixture() -> (Executor, SkolemInstanceRecord) {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("sse_x", Sort::Int);
    let body = executor
        .ctx
        .terms
        .mk_app(Symbol::named("sse_p"), [x], Sort::Bool);
    let quantified = executor
        .ctx
        .terms
        .mk_exists(vec![("sse_x".to_string(), Sort::Int)], body);
    let witness = executor.ctx.terms.mk_var("sk!sse_x", Sort::Int);
    executor.ctx.terms.mark_skolem_symbol("sk!sse_x");
    executor.ctx.terms.register_skolem_choice(
        witness,
        SkolemChoice {
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
    assert!(token.into_current(&executor).is_some());
}

#[test]
fn stale_epoch_skolem_instance_record_seals_to_none() {
    let (mut executor, record) = sealed_skolem_record_fixture();
    let token = CheckedSkolemDerivation::seal(&mut executor, &record)
        .expect("well-formed record must seal");
    executor.query_authority_epoch = QueryAuthorityEpoch::fresh();
    assert!(token.into_current(&executor).is_none());
}

fn bv_mbqi_false_record_fixture() -> (Executor, crate::executor::BvMbqiFalseInstanceRecord) {
    let mut executor = Executor::new();
    let width = 8u32;
    let bv_sort = Sort::BitVec(ay_core::BitVecSort::new(width));
    let x = executor.ctx.terms.mk_var("bmf_x", bv_sort.clone());
    let square = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvmul"), [x, x], bv_sort.clone());
    let zero = executor
        .ctx
        .terms
        .mk_bitvec(num_bigint::BigInt::ZERO, width);
    let body = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvslt"), [square, zero], Sort::Bool);
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
    (
        executor,
        crate::executor::BvMbqiFalseInstanceRecord {
            quantifier,
            values: vec![zero],
            instance,
            asserted,
        },
    )
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
    assert!(token.into_current(&executor).is_none());
}

#[test]
fn bv_mbqi_record_keyed_by_wrong_term_is_refused() {
    let (mut executor, record) = bv_mbqi_false_record_fixture();
    let wrong_key = executor.ctx.terms.true_term();
    assert!(CheckedInstanceDerivation::seal(
        &mut executor,
        record.quantifier,
        &record.values,
        record.instance,
        wrong_key,
    )
    .is_none());
}

/// L2 (#ppp-c7) fixture: `src = (= (f 1) 2)` licenses the rewrite
/// `(g (f 1)) -> (g 2)` at stamp 1.
fn propagation_record_fixture() -> (
    Executor,
    PropagatedRewriteRecord,
    Vec<PropagatedEntrySource>,
) {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let one = terms.mk_int(num_bigint::BigInt::from(1));
    let two = terms.mk_int(num_bigint::BigInt::from(2));
    let f_one = terms.mk_app(Symbol::named("ppd_f"), [one], Sort::Int);
    let src = terms.mk_app(Symbol::named("="), [f_one, two], Sort::Bool);
    let before = terms.mk_app(Symbol::named("ppd_g"), [f_one], Sort::Bool);
    let after = terms.mk_app(Symbol::named("ppd_g"), [two], Sort::Bool);
    let record = PropagatedRewriteRecord {
        before,
        after,
        stamp: 1,
    };
    let entries = vec![PropagatedEntrySource {
        expr: f_one,
        value: two,
        source_assertion: src,
        stamp: 1,
    }];
    (executor, record, entries)
}

#[test]
fn live_epoch_propagation_record_seals_and_consumes() {
    let (mut executor, record, entries) = propagation_record_fixture();
    let token = CheckedPropagationDerivation::seal(&mut executor, &record, &entries)
        .expect("a faithfully recorded rewrite must seal");
    let (after, (before, stamp)) = token
        .into_current(&executor)
        .expect("a live-epoch token must consume");
    assert_eq!(after, record.after);
    assert_eq!(before, record.before);
    assert_eq!(stamp, record.stamp);
}

#[test]
fn stale_epoch_propagation_record_seals_to_none() {
    let (mut executor, record, entries) = propagation_record_fixture();
    let token = CheckedPropagationDerivation::seal(&mut executor, &record, &entries)
        .expect("a faithfully recorded rewrite must seal");
    executor.query_authority_epoch = QueryAuthorityEpoch::fresh();
    assert!(token.into_current(&executor).is_none());
}

/// The seal replay must catch a tampered substitution: a record whose
/// claimed `after` differs from the seeded throwaway `PropagateValues`
/// replay is refused.
#[test]
fn tampered_propagation_record_after_is_refused() {
    let (mut executor, mut record, entries) = propagation_record_fixture();
    let three = executor.ctx.terms.mk_int(num_bigint::BigInt::from(3));
    record.after = executor
        .ctx
        .terms
        .mk_app(Symbol::named("ppd_g"), [three], Sort::Bool);
    assert!(CheckedPropagationDerivation::seal(&mut executor, &record, &entries).is_none());
}

/// A record whose stamped licensing entries do NOT license the rewrite
/// (entry harvested strictly later) fails the seal replay.
#[test]
fn propagation_record_with_later_entry_stamp_is_refused() {
    let (mut executor, record, mut entries) = propagation_record_fixture();
    entries[0].stamp = record.stamp + 1;
    assert!(CheckedPropagationDerivation::seal(&mut executor, &record, &entries).is_none());
}

/// The entry seal independently replays the harvest: a claimed value the
/// asserted defining equality does not define is refused.
#[test]
fn tampered_propagation_entry_value_is_refused() {
    let (executor, _record, entries) = propagation_record_fixture();
    let mut forged = entries[0].clone();
    let mut executor = executor;
    forged.value = executor.ctx.terms.mk_int(num_bigint::BigInt::from(3));
    assert!(CheckedPropagationEntry::seal(&executor, &forged).is_none());
    // The faithful entry still seals and consumes (isolating the guard).
    let token = CheckedPropagationEntry::seal(&executor, &entries[0])
        .expect("the faithful harvest must seal");
    assert!(token.into_current(&executor).is_some());
}

/// L2 (#ppp-c7) qpf instance-root fixture:
/// `F = forall x:BV8. (or (and (= (h x) 1) (= (h2 x) 2)) (not (= x 1)))`
/// instantiated at `x := 1`.
fn qpf_instance_root_fixture() -> (Executor, QpfPremiseForcedInstanceRecord) {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let width = 8u32;
    let bv_sort = Sort::BitVec(ay_core::BitVecSort::new(width));
    let x = terms.mk_var("qir_x", bv_sort.clone());
    let one = terms.mk_bitvec(num_bigint::BigInt::from(1), width);
    let two = terms.mk_bitvec(num_bigint::BigInt::from(2), width);
    let h_x = terms.mk_app(Symbol::named("qir_h"), [x], bv_sort.clone());
    let h2_x = terms.mk_app(Symbol::named("qir_h2"), [x], bv_sort.clone());
    let c1 = terms.mk_app(Symbol::named("="), [h_x, one], Sort::Bool);
    let c2 = terms.mk_app(Symbol::named("="), [h2_x, two], Sort::Bool);
    let conjunction = terms.mk_app(Symbol::named("and"), [c1, c2], Sort::Bool);
    let x_eq_one = terms.mk_app(Symbol::named("="), [x, one], Sort::Bool);
    let premise = terms.mk_not_raw(x_eq_one);
    let body = terms.mk_app(Symbol::named("or"), [conjunction, premise], Sort::Bool);
    let quantifier = terms.mk_forall(vec![("qir_x".to_string(), bv_sort)], body);
    let mut substitution = HashMap::default();
    substitution.insert("qir_x".to_string(), one);
    let instance =
        crate::ematching::subst_vars_exact_qf(&mut executor.ctx.terms, body, &substitution)
            .expect("closed substitution succeeds");
    let asserted = crate::ematching::subst_vars(&mut executor.ctx.terms, body, &substitution);
    (
        executor,
        QpfPremiseForcedInstanceRecord {
            quantifier,
            values: vec![one],
            instance,
            asserted,
        },
    )
}

#[test]
fn live_epoch_qpf_instance_root_seals_and_consumes() {
    let (mut executor, record) = qpf_instance_root_fixture();
    let token = CheckedInstanceRootDerivation::seal(&mut executor, &record)
        .expect("a faithfully recorded qpf instance must seal");
    let derivation = token
        .into_current(&executor)
        .expect("a live-epoch token must consume");
    assert_eq!(derivation.quantifier, record.quantifier);
    assert_eq!(derivation.instance, record.instance);
    assert_eq!(
        derivation.refuted_disjuncts.len(),
        1,
        "the closed premise disjunct is sealed as refuted"
    );
    assert_ne!(derivation.survivor, derivation.instance);
}

#[test]
fn stale_epoch_qpf_instance_root_seals_to_none() {
    let (mut executor, record) = qpf_instance_root_fixture();
    let token = CheckedInstanceRootDerivation::seal(&mut executor, &record)
        .expect("a faithfully recorded qpf instance must seal");
    executor.query_authority_epoch = QueryAuthorityEpoch::fresh();
    assert!(token.into_current(&executor).is_none());
}

/// The seal replay must catch a tampered substitution: an `instance`
/// that is not the exact raw simultaneous substitution of the recorded
/// binder values is refused.
#[test]
fn tampered_qpf_instance_root_substitution_is_refused() {
    let (mut executor, mut record) = qpf_instance_root_fixture();
    let width = 8u32;
    let three = executor
        .ctx
        .terms
        .mk_bitvec(num_bigint::BigInt::from(3), width);
    // Claim the binder value was 3 while keeping the instance minted at 1.
    record.values = vec![three];
    assert!(CheckedInstanceRootDerivation::seal(&mut executor, &record).is_none());
}

/// A premise disjunct that does NOT model-free evaluate to `false`
/// (here: over a second, unpinned binder application) makes the raw
/// instance a two-survivor `or` — the seal must refuse rather than elect
/// either disjunct.
#[test]
fn qpf_instance_root_with_satisfiable_disjunct_is_refused() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let width = 8u32;
    let bv_sort = Sort::BitVec(ay_core::BitVecSort::new(width));
    let x = terms.mk_var("qis_x", bv_sort.clone());
    let one = terms.mk_bitvec(num_bigint::BigInt::from(1), width);
    let h_x = terms.mk_app(Symbol::named("qis_h"), [x], bv_sort.clone());
    let c1 = terms.mk_app(Symbol::named("="), [h_x, one], Sort::Bool);
    // The "premise" disjunct mentions the UF, so it cannot model-free
    // evaluate to false at the pinned point.
    let h_eq_x = terms.mk_app(Symbol::named("="), [h_x, x], Sort::Bool);
    let premise = terms.mk_not_raw(h_eq_x);
    let body = terms.mk_app(Symbol::named("or"), [c1, premise], Sort::Bool);
    let quantifier = terms.mk_forall(vec![("qis_x".to_string(), bv_sort)], body);
    let mut substitution = HashMap::default();
    substitution.insert("qis_x".to_string(), one);
    let instance =
        crate::ematching::subst_vars_exact_qf(&mut executor.ctx.terms, body, &substitution)
            .expect("closed substitution succeeds");
    let asserted = crate::ematching::subst_vars(&mut executor.ctx.terms, body, &substitution);
    let record = QpfPremiseForcedInstanceRecord {
        quantifier,
        values: vec![one],
        instance,
        asserted,
    };
    assert!(CheckedInstanceRootDerivation::seal(&mut executor, &record).is_none());
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
    assert!(CheckedInstanceDerivation::seal(
        &mut executor,
        negated_quantifier,
        &record.values,
        true_instance,
        false_key,
    )
    .is_none());
}

/// (#mbqi-sidecar-instance) Fixture: `forall x. 0 <= x`, refuted at `x := -1`
/// with the exact structural instance the generic-MBQI refinement now pushes
/// and records.
fn mbqi_refinement_record_fixture() -> (Executor, crate::ematching::ForallInstantiationProvenance) {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let x = terms.mk_var("mri_x", Sort::Int);
    let zero = terms.mk_int(num_bigint::BigInt::ZERO);
    let body = terms.mk_app(Symbol::named("<="), [zero, x], Sort::Bool);
    let quantifier = terms.mk_forall(vec![("mri_x".to_string(), Sort::Int)], body);
    let minus_one = terms.mk_int(num_bigint::BigInt::from(-1));
    let mut substitution = HashMap::default();
    substitution.insert("mri_x".to_string(), minus_one);
    let instance =
        crate::ematching::subst_vars_exact_qf(&mut executor.ctx.terms, body, &substitution)
            .expect("closed single-binder substitution succeeds");
    (
        executor,
        crate::ematching::ForallInstantiationProvenance {
            quantifier,
            binding: vec![minus_one],
            instance,
        },
    )
}

/// (#mbqi-sidecar-instance) A faithfully recorded generic-MBQI refinement
/// instance is consumed by the sealed fragment derivation maps, keyed by the
/// pushed (exact) instance itself.
#[test]
fn mbqi_refinement_record_feeds_sealed_instance_map() {
    let (mut executor, record) = mbqi_refinement_record_fixture();
    let asserted = record.instance;
    let quantifier = record.quantifier;
    executor.mbqi_refinement_instance_records.push(record);
    let (instances, _skolems) = sealed_fragment_derivation_maps(&mut executor);
    let derivation = instances
        .get(&asserted)
        .expect("the exact pushed instance must gain a sealed derivation");
    assert_eq!(derivation.quantifier, quantifier);
    assert_eq!(derivation.instance, asserted);
}

/// (#mbqi-sidecar-instance) GUARD-REMOVAL PROOF: the seal replays the exact
/// substitution itself, so a record whose instance is NOT the recorded
/// binding's structural substitution (e.g. a semantically folded or forged
/// term) is refused — the producer's record carries no authority of its own.
#[test]
fn tampered_mbqi_refinement_record_is_refused_by_the_seal() {
    let (mut executor, mut record) = mbqi_refinement_record_fixture();
    record.instance = executor.ctx.terms.false_term();
    let asserted = record.instance;
    executor.mbqi_refinement_instance_records.push(record);
    let (instances, _skolems) = sealed_fragment_derivation_maps(&mut executor);
    assert!(
        !instances.contains_key(&asserted),
        "a record whose instance is not the exact substitution must not seal"
    );
}

/// (#mbqi-sidecar-instance) Kill-switch coverage: with
/// `--no-quant-unit-authority` the sealed maps are empty regardless of any
/// recorded MBQI provenance, restoring the baseline sidecar starvation.
#[test]
fn mbqi_refinement_record_is_starved_by_the_kill_switch() {
    let (mut executor, record) = mbqi_refinement_record_fixture();
    executor.mbqi_refinement_instance_records.push(record);
    let guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_quant_unit_authority: true,
        ..Default::default()
    });
    let (instances, skolems) = sealed_fragment_derivation_maps(&mut executor);
    drop(guard);
    assert!(instances.is_empty() && skolems.is_empty());
}
