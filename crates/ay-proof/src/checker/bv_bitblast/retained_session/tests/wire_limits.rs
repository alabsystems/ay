// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::bv_blast_solver::retained::wire;
use crate::quality::retained::{self as quality, Request};

fn defaults(end: Instant) -> WireLimits {
    super::super::inventory::wire_limits(&counted_limits_until(end), end)
}

fn assert_limits(actual: WireLimits, expected: WireLimits) {
    assert_eq!(actual.max_json_bytes, expected.max_json_bytes);
    assert_eq!(actual.max_rows, expected.max_rows);
    assert_eq!(actual.max_literals, expected.max_literals);
    assert_eq!(actual.max_hints, expected.max_hints);
    assert_eq!(actual.max_work, expected.max_work);
    assert_eq!(actual.max_storage_bytes, expected.max_storage_bytes);
    assert_eq!(actual.deadline, expected.deadline);
}

fn bounded_replay(
    terms: &TermStore,
    proof: &Proof,
    payloads: &[RetainedStepPayload],
    end: Instant,
    wire: Option<WireLimits>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let mut session = RetainedSession::new_with_wire_limits(
        credits(proof, terms, end),
        RetainedOperation::Replay(payloads),
        wire,
        progress,
    )?;
    for index in 0..proof.steps.len() {
        session.validate_step(ProofId(index as u32), progress)?;
    }
    assert!(session.finish(progress)?.is_empty());
    Ok(())
}

#[test]
fn every_field_intersects_once_and_loose_limits_cannot_raise_source_caps() {
    let end = deadline();
    let trusted = defaults(end);
    let effective = super::super::inventory::effective_wire_limits;
    assert_limits(effective(end, None), trusted);
    let loose = WireLimits {
        max_json_bytes: usize::MAX,
        max_rows: usize::MAX,
        max_literals: usize::MAX,
        max_hints: usize::MAX,
        max_work: u64::MAX,
        max_storage_bytes: usize::MAX,
        deadline: end + Duration::from_secs(1),
    };
    assert_limits(effective(end, Some(loose)), trusted);
    let tight = WireLimits {
        max_json_bytes: 0,
        max_rows: 1,
        max_literals: 2,
        max_hints: 3,
        max_work: 4,
        max_storage_bytes: 5,
        deadline: end - Duration::from_secs(1),
    };
    assert_limits(effective(end, Some(tight)), tight);
}

#[test]
fn inventory_uses_the_stored_json_and_actual_owner_capacity_limits() {
    let (terms, clause) = identity(0);
    let proof = proof(clause, 1);
    let payloads = [RetainedStepPayload {
        step: 0,
        payload: b"{}".to_vec(),
    }];
    let end = deadline();
    let mut exact = defaults(end);
    exact.max_json_bytes = payloads[0].payload.len();
    exact.max_storage_bytes = payloads[0].payload.capacity();
    let calls = producer_test_counter::count();
    let session = RetainedSession::new_with_wire_limits(
        credits(&proof, &terms, end),
        RetainedOperation::Replay(&payloads),
        Some(exact),
        &mut |_, _| true,
    )
    .unwrap();
    assert_limits(session.wire, exact);
    drop(session); // Shape admission alone did not authenticate the payload.
    for field in 0..2 {
        let mut short = exact;
        if field == 0 {
            short.max_json_bytes -= 1;
        } else {
            short.max_storage_bytes -= 1;
        }
        assert!(matches!(
            RetainedSession::new_with_wire_limits(
                credits(&proof, &terms, end),
                RetainedOperation::Replay(&payloads),
                Some(short),
                &mut |_, _| true,
            ),
            Err(ProofCheckError::ResourceLimit)
        ));
    }
    assert_eq!(producer_test_counter::count(), calls);
}

#[test]
fn absent_override_preserves_the_legacy_complete_callback_sequence() {
    let (terms, clause) = identity(0);
    let proof = proof(clause, 1);
    let payloads = capture(&terms, &proof);
    let end = deadline();
    let calls = producer_test_counter::count();
    let mut old_trace = Vec::new();
    let mut old_progress = |work, bytes| {
        old_trace.push((work, bytes));
        true
    };
    let mut session = RetainedSession::new(
        credits(&proof, &terms, end),
        RetainedOperation::Replay(&payloads),
        &mut old_progress,
    )
    .unwrap();
    session
        .validate_step(ProofId(0), &mut old_progress)
        .unwrap();
    assert!(session.finish(&mut old_progress).unwrap().is_empty());
    let mut new_trace = Vec::new();
    bounded_replay(&terms, &proof, &payloads, end, None, &mut |w, b| {
        new_trace.push((w, b));
        true
    })
    .unwrap();
    assert_eq!(new_trace, old_trace);
    assert_eq!(producer_test_counter::count(), calls);
}

#[test]
fn replay_wire_work_and_storage_exact_short_and_zero_caps_reach_the_codec() {
    let (terms, clause) = identity(0);
    let proof = proof(clause, 1);
    let payloads = capture(&terms, &proof);
    let end = deadline();
    let limits = counted_limits_until(end);
    let gates = proof_replay_limits(&limits);
    let decoded = wire::decode(
        &payloads[0].payload,
        &defaults(end),
        &limits,
        &gates,
        &mut || true,
    );
    assert!(decoded.result.is_ok());
    let work = u64::try_from(decoded.usage.charged_work).unwrap();
    let storage = decoded
        .usage
        .peak_storage_bytes
        .max(payloads[0].payload.capacity());
    assert!(work > 0 && storage > 0);
    let mut exact = defaults(end);
    exact.max_json_bytes = payloads[0].payload.len();
    exact.max_work = work;
    exact.max_storage_bytes = storage;
    let calls = producer_test_counter::count();
    bounded_replay(&terms, &proof, &payloads, end, Some(exact), &mut |_, _| {
        true
    })
    .unwrap();
    for (work, storage) in [
        (work - 1, storage),
        (0, storage),
        (work, storage - 1),
        (work, 0),
    ] {
        let mut short = exact;
        short.max_work = work;
        short.max_storage_bytes = storage;
        assert!(matches!(
            bounded_replay(&terms, &proof, &payloads, end, Some(short), &mut |_, _| {
                true
            }),
            Err(ProofCheckError::ResourceLimit)
        ));
    }
    assert_eq!(producer_test_counter::count(), calls);
}

#[test]
fn capture_also_obeys_the_wire_ceiling_and_failure_poison_is_terminal() {
    let (terms, clause) = identity(0);
    let proof = proof(clause, 1);
    let end = deadline();
    let mut wire = defaults(end);
    wire.max_rows = 0; // Every retained refutation has a terminal empty row.
    let mut session = RetainedSession::new_with_wire_limits(
        credits(&proof, &terms, end),
        RetainedOperation::Capture,
        Some(wire),
        &mut |_, _| true,
    )
    .unwrap();
    assert_eq!(
        session.validate_step(ProofId(0), &mut |_, _| true),
        Err(ProofCheckError::ResourceLimit)
    );
    assert!(session.output.is_empty());
    let calls = producer_test_counter::count();
    assert!(session.validate_step(ProofId(0), &mut |_, _| true).is_err());
    assert!(session.finish(&mut |_, _| true).is_err());
    assert_eq!(producer_test_counter::count(), calls);
}

#[test]
fn every_optional_wire_constructor_callback_refusal_remains_sticky() {
    let (terms, clause) = identity(0);
    let proof = proof(clause, 1);
    let end = deadline();
    let total = Cell::new(0);
    drop(
        RetainedSession::new_with_wire_limits(
            credits(&proof, &terms, end),
            RetainedOperation::Capture,
            Some(defaults(end)),
            &mut |_, _| {
                total.set(total.get() + 1);
                true
            },
        )
        .unwrap(),
    );
    assert!(total.get() > 2);
    for stop in 1..=total.get() {
        let seen = Cell::new(0);
        assert!(matches!(
            RetainedSession::new_with_wire_limits(
                credits(&proof, &terms, end),
                RetainedOperation::Capture,
                Some(defaults(end)),
                &mut |_, _| {
                    seen.set(seen.get() + 1);
                    seen.get() != stop
                },
            ),
            Err(ProofCheckError::ResourceLimit)
        ));
        assert_eq!(seen.get(), stop);
    }
}

#[test]
fn expired_wire_deadline_refuses_before_session_or_whole_proof_callbacks() {
    let (terms, clause) = identity(0);
    let proof = proof(clause, 1);
    let end = deadline();
    let mut wire = defaults(end);
    wire.deadline = Instant::now() - Duration::from_secs(1);
    assert!(matches!(
        RetainedSession::new_with_wire_limits(
            credits(&proof, &terms, end),
            RetainedOperation::Capture,
            Some(wire),
            &mut |_, _| panic!("expired session clock"),
        ),
        Err(ProofCheckError::Cancelled)
    ));
    let request = Request {
        operation: RetainedOperation::Capture,
        deadline: end,
        wire_limits: Some(wire),
    };
    assert_eq!(request.effective_deadline(), wire.deadline);
    assert!(matches!(
        quality::check(
            &proof,
            quality::Context {
                terms: &terms,
                dt_decls: None,
                ctor_selectors: None,
                datatype_member_signatures: &[],
                problem_assertions: &[],
            },
            request,
            &mut |_, _| panic!("expired prepass clock"),
        ),
        Err(ProofCheckError::ResourceLimit)
    ));
}

#[test]
fn shorter_wire_clock_is_not_renewed_after_constructor_or_before_finish() {
    let (terms, clause) = identity(0);
    let proof = proof(clause, 1);
    let credit_end = deadline();
    let mut wire = defaults(credit_end);
    wire.deadline = Instant::now() + Duration::from_secs(1);
    let mut session = RetainedSession::new_with_wire_limits(
        credits(&proof, &terms, credit_end),
        RetainedOperation::Capture,
        Some(wire),
        &mut |_, _| true,
    )
    .unwrap();
    assert_eq!(session.credits.deadline(), credit_end);
    assert_eq!(session.original_deadline(), wire.deadline);
    while Instant::now() < wire.deadline {
        std::thread::sleep(wire.deadline.saturating_duration_since(Instant::now()));
    }
    let calls = producer_test_counter::count();
    assert_eq!(
        session.validate_step(ProofId(0), &mut |_, _| panic!("expired step clock")),
        Err(ProofCheckError::Cancelled)
    );
    assert_eq!(
        session.finish(&mut |_, _| panic!("expired finish clock")),
        Err(ProofCheckError::Cancelled)
    );
    assert_eq!(producer_test_counter::count(), calls);
}
