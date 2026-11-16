// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn app(terms: &mut TermStore, head: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(head), args, sort)
}

fn ordinary() -> (TermStore, Proof) {
    let (mut terms, mut proof) = sparse_fixture();
    let ProofStep::TheoryLemma { clause, .. } = &mut proof.steps[0] else {
        panic!("fixture");
    };
    let word = terms.mk_var("guard-word", Sort::bitvec(64));
    let zero = terms.mk_bitvec(0.into(), 64);
    let guard = app(&mut terms, "bvuge", &[word, zero], Sort::Bool);
    let negative = terms.mk_not_raw(clause[0]);
    let root = app(&mut terms, "and", &[guard, negative], Sort::Bool);
    clause[0] = terms.mk_not_raw(root);
    (terms, proof)
}

#[test]
fn ge_ordinary_original_route_is_authenticated_without_search_or_native_credit_lending() {
    let (terms, proof) = ordinary();
    let payloads = capture(&terms, &proof);
    let before = producer_test_counter::count();
    let snapshot = terms.entries_snapshot();
    let refined = plan(&terms, &proof)
        .refine_replay(&payloads, end(), None, &mut |_, _| true)
        .unwrap();
    let price = refined
        .entries
        .iter()
        .flatten()
        .next()
        .unwrap()
        .replay_price
        .unwrap();
    let expression = price.expression_work().unwrap();
    assert!(price.work > expression);
    let mut credits = refined.prepay(end(), &mut |_, _| true).unwrap();
    {
        let allowance = credits
            .take(ProofId(0), &mut |_, _| true)
            .unwrap()
            .into_allowance();
        assert_eq!(allowance.work_limit(), expression as u64);
    }
    credits.finish().unwrap();
    assert_eq!(terms.entries_snapshot(), snapshot);
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn ge_original_route_stops_deadlines_and_malformed_wire_keep_legacy_strict_boundaries() {
    let (terms, proof) = ordinary();
    let mut payloads = capture(&terms, &proof);
    let mut total = 0;
    plan(&terms, &proof)
        .refine_replay(&payloads, end(), None, &mut |_, _| {
            total += 1;
            true
        })
        .unwrap();
    for stop in 1..=total {
        let mut calls = 0;
        assert!(plan(&terms, &proof)
            .refine_replay(&payloads, end(), None, &mut |_, _| {
                calls += 1;
                calls != stop
            })
            .is_err());
        assert_eq!(calls, stop);
    }
    payloads[0].payload = b"null".to_vec();
    let old = legacy_replay_error(&terms, &proof, &payloads);
    let new = plan(&terms, &proof)
        .refine_replay(&payloads, end(), None, &mut |_, _| true)
        .err()
        .unwrap();
    assert_eq!(invalid_step_and_reason(old), invalid_step_and_reason(new));
    let mut wire = transport_wire_limits(end());
    wire.deadline = Instant::now().checked_sub(Duration::from_secs(1)).unwrap();
    let mut calls = 0;
    assert!(plan(&terms, &proof)
        .refine_replay(&payloads, end(), Some(wire), &mut |_, _| {
            calls += 1;
            true
        })
        .is_err());
    assert_eq!(calls, 0);
}

fn outside() -> (TermStore, Proof) {
    let mut terms = TermStore::new();
    let word = Sort::bitvec(9);
    let array = Sort::array(word.clone(), Sort::bitvec(8));
    let stack = terms.mk_var("stack", word.clone());
    let observe = terms.mk_var("observe", word.clone());
    let size = terms.mk_bitvec(1.into(), 9);
    let start = app(&mut terms, "bvsub", &[stack, size], word);
    let guard = app(&mut terms, "bvuge", &[stack, size], Sort::Bool);
    let below = app(&mut terms, "bvult", &[observe, start], Sort::Bool);
    let above = app(&mut terms, "bvuge", &[observe, stack], Sort::Bool);
    let out = app(&mut terms, "or", &[below, above], Sort::Bool);
    let not_out = terms.mk_not_raw(out);
    let base = terms.mk_var("memory", array.clone());
    let value = terms.mk_var("value", Sort::bitvec(8));
    let stored = app(&mut terms, "store", &[base, start, value], array);
    let after = app(&mut terms, "select", &[stored, observe], Sort::bitvec(8));
    let before = app(&mut terms, "select", &[base, observe], Sort::bitvec(8));
    let equal = app(&mut terms, "=", &[after, before], Sort::Bool);
    let property = app(&mut terms, "or", &[not_out, equal], Sort::Bool);
    let negative = terms.mk_not_raw(property);
    let root = app(&mut terms, "and", &[guard, negative], Sort::Bool);
    let clause = terms.mk_not_raw(root);
    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("BV", vec![clause], TheoryLemmaKind::BvBitBlast);
    (terms, proof)
}

#[test]
fn outside_original_route_keeps_old_aggregate_and_its_independent_prerequisites() {
    let (terms, proof) = outside();
    let payloads = capture(&terms, &proof); // existing conditional capture/prerequisites
    let before = plan(&terms, &proof).aggregate_charge();
    let producers = producer_test_counter::count();
    let kept = plan(&terms, &proof)
        .refine_replay(&payloads, end(), None, &mut |_, _| true)
        .unwrap();
    assert_eq!(kept.aggregate_charge(), before);
    assert!(kept
        .entries
        .iter()
        .flatten()
        .next()
        .unwrap()
        .replay_price
        .is_none());
    assert_eq!(producer_test_counter::count(), producers);
}

#[test]
fn source_annotations_on_ge_sources_never_issue_native_grants() {
    let (terms, mut proof) = ordinary();
    let payloads = capture(&terms, &proof);
    let ProofStep::TheoryLemma { farkas, .. } = &mut proof.steps[0] else {
        panic!("fixture");
    };
    *farkas = Some(ay_core::FarkasAnnotation::new(vec![]));
    let original = plan(&terms, &proof).aggregate_charge();
    let kept = plan(&terms, &proof)
        .refine_replay(&payloads, end(), None, &mut |_, _| true)
        .unwrap();
    assert_eq!(kept.aggregate_charge(), original);
    assert!(kept
        .entries
        .iter()
        .flatten()
        .next()
        .unwrap()
        .replay_price
        .is_none());
}

fn disjoint_fixture(last_start: u16) -> (TermStore, Proof) {
    let mut terms = TermStore::new();
    let word = Sort::bitvec(9);
    let a = terms.mk_var("a", word.clone());
    let b = terms.mk_var("b", word.clone());
    let size = terms.mk_bitvec(1.into(), 9);
    let end_a = app(&mut terms, "bvadd", &[a, size], word.clone());
    let end_b = app(&mut terms, "bvadd", &[b, size], word.clone());
    let after_b = app(&mut terms, "bvuge", &[a, end_b], Sort::Bool);
    let after_a = app(&mut terms, "bvuge", &[b, end_a], Sort::Bool);
    let separate = app(&mut terms, "or", &[after_b, after_a], Sort::Bool);
    let bound = terms.mk_bitvec(last_start.into(), 9);
    let nowrap_a = app(&mut terms, "bvule", &[a, bound], Sort::Bool);
    let nowrap_b = app(&mut terms, "bvule", &[b, bound], Sort::Bool);
    let array = terms.mk_var("memory", Sort::array(word, Sort::bitvec(8)));
    let read = app(&mut terms, "select", &[array, b], Sort::bitvec(8));
    let equal = app(&mut terms, "=", &[read, read], Sort::Bool);
    let negative = terms.mk_not_raw(equal);
    let root = app(
        &mut terms,
        "and",
        &[separate, nowrap_a, nowrap_b, negative],
        Sort::Bool,
    );
    let clause = terms.mk_not_raw(root);
    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("BV", vec![clause], TheoryLemmaKind::BvBitBlast);
    (terms, proof)
}

#[test]
fn affordable_disjoint_source_keeps_old_fees_and_all_original_prerequisites() {
    // Both exclusive endpoints must remain nonzero. The selector permits 511
    // for a singleton, but its independent separation prerequisite then fails.
    let (terms, proof) = disjoint_fixture(510);
    let payloads = capture(&terms, &proof);
    let before = plan(&terms, &proof).aggregate_charge();
    let producers = producer_test_counter::count();
    let kept = plan(&terms, &proof)
        .refine_replay(&payloads, end(), None, &mut |_, _| true)
        .unwrap();
    assert_eq!(kept.aggregate_charge(), before);
    assert!(kept
        .entries
        .iter()
        .flatten()
        .next()
        .unwrap()
        .replay_price
        .is_none());
    assert_eq!(producer_test_counter::count(), producers);
}

#[test]
fn wrapping_disjoint_candidate_cannot_capture_or_publish_without_prerequisite() {
    let (terms, proof) = disjoint_fixture(511);
    let snapshot = terms.entries_snapshot();
    let original_plan = plan(&terms, &proof);
    let clause = original_plan
        .entries
        .iter()
        .flatten()
        .next()
        .unwrap()
        .ordinary_clause()
        .unwrap();
    let shape = disjoint::Shape::recognize(&terms, clause).unwrap();
    assert_eq!(shape.width, 9);
    assert!(shape.spans.iter().all(|span| span.length == 1));
    let before = original_plan.aggregate_charge();
    let credit = original_plan.prepay(end(), &mut |_, _| true).unwrap();
    let mut session =
        RetainedSession::new(credit, RetainedOperation::Capture, &mut |_, _| true).unwrap();
    // At a=b=511 both endpoints are zero: the selected separation premise is
    // true, yet offset i=j=0 denotes the same byte. Recognition grants no fact.
    let error = session
        .validate_step(ProofId(0), &mut |_, _| true)
        .unwrap_err();
    let (step, reason) = invalid_step_and_reason(error);
    assert_eq!(step, ProofId(0));
    assert_eq!(reason, "source-bound retained BV refutation refused");
    assert!(matches!(
        session.validate_step(ProofId(0), &mut |_, _| true),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert!(matches!(
        session.finish(&mut |_, _| true),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert_eq!(terms.entries_snapshot(), snapshot);
    assert_eq!(plan(&terms, &proof).aggregate_charge(), before);
}

#[derive(Clone, Copy)]
enum ExitPhase {
    AfterStore,
    AtExit,
}

/// Mirror the measured capsule topology, not its unavailable Var IDs/stamps.
/// This private fixture creates no producer/journal/proof credentials.
fn exit_topology(phase: ExitPhase) -> (TermStore, Proof) {
    let mut terms = TermStore::new();
    let array = terms.mk_var("memory", Sort::array(Sort::bitvec(64), Sort::bitvec(32)));
    let index = terms.mk_var("index", Sort::bitvec(64));
    let key = terms.mk_bitvec(1.into(), 64);
    let end = terms.mk_bitvec(4.into(), 64);
    let value = terms.mk_bitvec(9.into(), 32);
    let before = app(&mut terms, "select", &[array, key], Sort::bitvec(32));
    let equal_before = app(&mut terms, "=", &[before, value], Sort::Bool);
    let negative_before = terms.mk_not_raw(equal_before);
    let ge = app(&mut terms, "bvuge", &[index, end], Sort::Bool);
    let invariant_body = app(&mut terms, "and", &[ge, negative_before], Sort::Bool);
    let invariant = terms.mk_not_raw(invariant_body);
    let (guard, negative) = match phase {
        ExitPhase::AtExit => (ge, negative_before),
        ExitPhase::AfterStore => {
            let sort = terms.sort(array).clone();
            let stored = app(&mut terms, "store", &[array, key, value], sort);
            let read = app(&mut terms, "select", &[stored, key], Sort::bitvec(32));
            let equal = app(&mut terms, "=", &[read, value], Sort::Bool);
            (
                app(&mut terms, "bvult", &[index, end], Sort::Bool),
                terms.mk_not_raw(equal),
            )
        }
    };
    let root = app(&mut terms, "and", &[invariant, guard, negative], Sort::Bool);
    let clause = terms.mk_not_raw(root);
    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("BV", vec![clause], TheoryLemmaKind::BvBitBlast);
    (terms, proof)
}

#[test]
fn captured_w2_exit_topologies_use_original_ordinary_selector_and_checked_refinement() {
    for phase in [ExitPhase::AfterStore, ExitPhase::AtExit] {
        let (terms, proof) = exit_topology(phase);
        // Capture is the unchanged original route/proof pipeline, not a guessed
        // capsule payload. Exact replay/source/RUP checks remain independent.
        let payloads = capture(&terms, &proof);
        let before = producer_test_counter::count();
        let old = plan(&terms, &proof).aggregate_charge();
        let refined = plan(&terms, &proof)
            .refine_replay(&payloads, end(), None, &mut |_, _| true)
            .unwrap();
        let price = refined
            .entries
            .iter()
            .flatten()
            .next()
            .unwrap()
            .replay_price
            .unwrap();
        assert!(price.work < old.work && price.bytes <= old.bytes);
        assert!(price.expression_work().unwrap() < price.work);
        assert_eq!(producer_test_counter::count(), before);
    }
}

#[test]
fn captured_w2_exit_topologies_still_run_original_strict_reader_after_refinement() {
    for phase in [ExitPhase::AfterStore, ExitPhase::AtExit] {
        let (terms, proof) = exit_topology(phase);
        let payloads = capture(&terms, &proof);
        let refined = plan(&terms, &proof)
            .refine_replay(&payloads, end(), None, &mut |_, _| true)
            .unwrap();
        let credits = refined.prepay(end(), &mut |_, _| true).unwrap();
        let mut session = RetainedSession::new(
            credits,
            RetainedOperation::Replay(&payloads),
            &mut |_, _| true,
        )
        .unwrap();
        assert!(session
            .validate_step(ProofId(0), &mut |_, _| true)
            .unwrap()
            .is_some());
        session.finish(&mut |_, _| true).unwrap();
    }
}
