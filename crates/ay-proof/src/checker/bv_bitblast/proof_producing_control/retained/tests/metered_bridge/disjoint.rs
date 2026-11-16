// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual private source-derived chains, not accepting prover spies or public
//! bundle adoption. Every positive uses real capture and independent replay.

use super::*;
use crate::bv_blast_solver::retained::producer_test_counter;

mod fixtures;
use fixtures::{fixture, Route, Source};

const ROUTES: [Route; 2] = [Route::Disjoint, Route::Combined];

fn replay_wire(
    terms: &TermStore,
    clause: TermId,
    input: &[u8],
) -> Result<WorkUsage, MeteredBridgeError> {
    let end = deadline();
    let (mut proof, gates) = limits(end);
    proof.resolution.max_conflicts = Some(0);
    proof.resolution.max_decisions = Some(0);
    proof.resolution.max_backward_reconstruction_bytes = 0;
    proof.resolution.max_pending_deletions = 0;
    invoke(
        Operation::Replay,
        terms,
        clause,
        input,
        &proof,
        &gates,
        &wire_limits(end),
        WorkAllowance::new(GRANT, end),
        &mut || true,
    )
}

#[test]
fn ordered_source_frames_survive_producer_drop_and_fresh_replay_without_search() {
    for route in ROUTES {
        let calls = producer_test_counter::count();
        let input = {
            let (terms, clause) = fixture(route, Source::Valid);
            let before = terms.entries_snapshot();
            let input = bytes(&terms, clause);
            assert_eq!(terms.entries_snapshot(), before);
            input
        };
        assert_eq!(producer_test_counter::count(), calls + route.roles().len());
        let json: serde_json::Value = serde_json::from_slice(&input).unwrap();
        let frames = json.as_array().unwrap();
        assert_eq!(frames.len(), route.roles().len());
        for (frame, role) in frames.iter().zip(route.roles()) {
            assert_eq!(frame.as_object().unwrap().len(), 1);
            assert!(frame[*role]["rows"]
                .as_array()
                .is_some_and(|rows| !rows.is_empty()));
        }
        let (terms, clause) = fixture(route, Source::Valid);
        let before = terms.entries_snapshot();
        let calls = producer_test_counter::count();
        let attempts =
            crate::checker::bv_bitblast::proof_producing_control::ATTEMPTS.with(Cell::get);
        for _ in 0..2 {
            let usage = replay_wire(&terms, clause, &input).unwrap();
            assert_eq!(usage.producer_validation, 0);
            assert!(
                usage.retained_prefix > 0 && usage.gates > 0 && usage.dag > 0 && usage.wire > 0
            );
        }
        assert_eq!(producer_test_counter::count(), calls);
        assert_eq!(
            crate::checker::bv_bitblast::proof_producing_control::ATTEMPTS.with(Cell::get),
            attempts
        );
        assert_eq!(terms.entries_snapshot(), before);
    }
}

#[test]
fn every_role_order_cardinality_and_inner_proof_is_mandatory_even_after_memo() {
    for route in ROUTES {
        let (terms, clause) = fixture(route, Source::Valid);
        let input = bytes(&terms, clause);
        replay_wire(&terms, clause, &input).unwrap();
        terms.record_strict_bv_semantics_validated(&[clause]);
        let calls = producer_test_counter::count();
        let frames: serde_json::Value = serde_json::from_slice(&input).unwrap();
        for mutation in 0..5 {
            let mut bad = frames.clone();
            let array = bad.as_array_mut().unwrap();
            match mutation {
                0 => {
                    array.remove(0);
                }
                1 => {
                    array.pop();
                }
                2 => array.push(array[0].clone()),
                3 => array.swap(0, 1),
                4 => {
                    let role = route.roles()[0];
                    let payload = array[0].as_object_mut().unwrap().remove(role).unwrap();
                    array[0] = serde_json::json!({"outside_free_offset": payload});
                }
                _ => unreachable!(),
            }
            assert!(replay_wire(&terms, clause, &serde_json::to_vec(&bad).unwrap()).is_err());
        }
        for (index, role) in route.roles().iter().enumerate() {
            for mutation in 0..2 {
                let mut bad = frames.clone();
                match mutation {
                    0 => bad[index][*role]["empty_clause_id"] = serde_json::json!(u64::MAX),
                    1 => bad[index][*role]["rows"] = serde_json::json!([]),
                    _ => unreachable!(),
                }
                assert!(replay_wire(&terms, clause, &serde_json::to_vec(&bad).unwrap()).is_err());
            }
        }
        replay_wire(&terms, clause, &input).unwrap();
        assert_eq!(producer_test_counter::count(), calls);
    }
}

#[test]
fn source_selects_disjoint_or_combined_inventory_not_the_wire() {
    let (disjoint, d) = fixture(Route::Disjoint, Source::Valid);
    let (combined, c) = fixture(Route::Combined, Source::Valid);
    let d_bytes = bytes(&disjoint, d);
    let c_bytes = bytes(&combined, c);
    let calls = producer_test_counter::count();
    assert!(replay_wire(&disjoint, d, &c_bytes).is_err());
    assert!(replay_wire(&combined, c, &d_bytes).is_err());
    assert_eq!(producer_test_counter::count(), calls);
}

#[test]
fn proved_prerequisites_do_not_authorize_sat_final_neighbors_or_reused_ids() {
    for route in ROUTES {
        let (terms, clause) = fixture(route, Source::Valid);
        let input = bytes(&terms, clause);
        let (neighbor, changed) = fixture(route, Source::FalseConclusion);
        assert_eq!(clause, changed);
        // Disjoint: a=0,b=2. Combined: a=2,b=2,output=2. With zero
        // memory/value the positive guards and property all hold, so negating
        // their conjunction is false. The prerequisite remains a theorem.
        let calls = producer_test_counter::count();
        assert!(replay_wire(&neighbor, changed, &input).is_err());
        assert_eq!(producer_test_counter::count(), calls);
        let end = deadline();
        let (proof, gates) = limits(end);
        assert!(invoke(
            Operation::Capture,
            &neighbor,
            changed,
            b"",
            &proof,
            &gates,
            &wire_limits(end),
            WorkAllowance::new(GRANT, end),
            &mut || true,
        )
        .is_err());
        assert!(!neighbor.strict_bv_semantics_validated(&[changed]));
    }
}

#[test]
fn overwritten_malformed_values_are_checked_before_any_success_can_escape() {
    for route in ROUTES {
        let (terms, clause) = fixture(route, Source::Valid);
        let input = bytes(&terms, clause);
        let (malformed, clause) = fixture(route, Source::MalformedOverwritten);
        let before = malformed.entries_snapshot();
        let calls = producer_test_counter::count();
        assert!(replay_wire(&malformed, clause, &input).is_err());
        assert_eq!(producer_test_counter::count(), calls);
        let end = deadline();
        let (proof, gates) = limits(end);
        assert!(invoke(
            Operation::Capture,
            &malformed,
            clause,
            b"",
            &proof,
            &gates,
            &wire_limits(end),
            WorkAllowance::new(GRANT, end),
            &mut || true,
        )
        .is_err());
        assert_eq!(malformed.entries_snapshot(), before);
        assert!(!malformed.strict_bv_semantics_validated(&[clause]));
    }
}

#[test]
fn all_frames_spend_one_exact_or_one_short_credit_without_phase_renewal() {
    for route in ROUTES {
        let (terms, clause) = fixture(route, Source::Valid);
        let input = bytes(&terms, clause);
        for operation in [Operation::Capture, Operation::Replay] {
            let end = deadline();
            let (proof, gates) = limits(end);
            let wire = wire_limits(end);
            let run = |grant| {
                invoke(
                    operation,
                    &terms,
                    clause,
                    &input,
                    &proof,
                    &gates,
                    &wire,
                    WorkAllowance::new(grant, end),
                    &mut || true,
                )
            };
            let usage = run(GRANT).unwrap();
            let exact = total(usage);
            let largest = [
                usage.producer_validation,
                usage.retained_prefix,
                usage.gates,
                usage.dag,
                usage.wire,
            ]
            .into_iter()
            .max()
            .unwrap();
            assert!(largest > 0 && largest < exact);
            assert_eq!(run(exact).unwrap(), usage);
            for grant in [0, largest, exact - 1] {
                assert!(
                    run(grant).is_err(),
                    "{route:?}/{operation:?}: {grant}/{exact}"
                );
            }
        }
    }
}

#[test]
fn wire_limits_cover_every_frame_and_the_role_wrapper() {
    for route in ROUTES {
        let (terms, clause) = fixture(route, Source::Valid);
        let input = bytes(&terms, clause);
        let end = deadline();
        let (proof, gates) = limits(end);
        let frames = wire::pair::decode_frames(
            route.frames(),
            &input,
            &wire_limits(end),
            &proof,
            &gates,
            &mut || true,
        )
        .result
        .unwrap();
        let payloads: Vec<_> = frames[..route.roles().len()]
            .iter()
            .map(|frame| {
                wire::decode(frame, &wire_limits(end), &proof, &gates, &mut || true)
                    .result
                    .unwrap()
            })
            .collect();
        let mut exact = wire_limits(end);
        exact.max_json_bytes = input.len();
        exact.max_rows = payloads.iter().map(|p| p.rows.len()).sum();
        exact.max_literals = payloads
            .iter()
            .flat_map(|p| &p.rows)
            .map(|r| r.literals.len())
            .sum();
        exact.max_hints = payloads
            .iter()
            .flat_map(|p| &p.rows)
            .map(|r| r.hints.len())
            .sum();
        assert!(exact.max_rows >= route.roles().len() && exact.max_hints > 0);
        assert!(input.len() > frames.iter().map(|frame| frame.len()).sum::<usize>());
        for operation in [Operation::Capture, Operation::Replay] {
            let run = |wire: &WireLimits| {
                invoke(
                    operation,
                    &terms,
                    clause,
                    &input,
                    &proof,
                    &gates,
                    wire,
                    WorkAllowance::new(GRANT, end),
                    &mut || true,
                )
            };
            run(&exact).unwrap();
            for cap in 0..4 {
                let mut short = exact;
                match cap {
                    0 => short.max_json_bytes -= 1,
                    1 => short.max_rows -= 1,
                    2 if short.max_literals > 0 => short.max_literals -= 1,
                    2 => continue,
                    3 => short.max_hints -= 1,
                    _ => unreachable!(),
                }
                assert!(run(&short).is_err(), "{route:?}/{operation:?}: cap {cap}");
            }
        }
    }
}

#[test]
fn entry_interior_and_restricted_subsetup_stops_are_sticky_for_both_routes() {
    for route in ROUTES {
        let (terms, clause) = fixture(route, Source::Valid);
        let input = bytes(&terms, clause);
        for operation in [Operation::Capture, Operation::Replay] {
            let end = deadline();
            let (proof, gates) = limits(end);
            let wire = wire_limits(end);
            let calls = Cell::new(0);
            let run = |stop_at| {
                calls.set(0);
                invoke(
                    operation,
                    &terms,
                    clause,
                    &input,
                    &proof,
                    &gates,
                    &wire,
                    WorkAllowance::new(GRANT, end),
                    &mut || {
                        calls.set(calls.get() + 1);
                        calls.get() != stop_at
                    },
                )
            };
            run(0).unwrap();
            let count = calls.get();
            assert!(count > 10);
            // Actual SAT capture is intentionally not repeated at every poll.
            for stop_at in [1, count / 2, count] {
                let producers = producer_test_counter::count();
                assert!(matches!(
                    run(stop_at),
                    Err(MeteredBridgeError::Bridge(BridgeError::Cancelled))
                ));
                assert_eq!(calls.get(), stop_at);
                if matches!(operation, Operation::Replay) || stop_at == 1 {
                    assert_eq!(producer_test_counter::count(), producers);
                }
            }
        }
    }
}

#[test]
fn every_original_deadline_refuses_before_source_walk_or_callback() {
    let past = Instant::now().checked_sub(Duration::from_secs(1)).unwrap();
    let calls = producer_test_counter::count();
    for route in ROUTES {
        let (terms, clause) = fixture(route, Source::Valid);
        for operation in [Operation::Capture, Operation::Replay] {
            for expired in 0..5 {
                let end = deadline();
                let (mut proof, mut gates) = limits(end);
                let mut wire = wire_limits(end);
                let credit_end = if expired == 0 { past } else { end };
                match expired {
                    1 => wire.deadline = past,
                    2 => proof.resolution.deadline = Some(past),
                    3 => proof.resolution.validation.deadline = Some(past),
                    4 => gates.deadline = Some(past),
                    _ => {}
                }
                assert!(matches!(
                    invoke(
                        operation,
                        &terms,
                        clause,
                        b"",
                        &proof,
                        &gates,
                        &wire,
                        WorkAllowance::new(GRANT, credit_end),
                        &mut || panic!("expired before poll"),
                    ),
                    Err(MeteredBridgeError::Bridge(BridgeError::Deadline))
                ));
            }
        }
    }
    assert_eq!(producer_test_counter::count(), calls);
}

#[test]
fn full_quality_session_captures_each_chain_once_and_replays_fresh_without_producer() {
    use crate::checker::bv_bitblast::retained_session::RetainedOperation;
    use crate::checker::bv_bitblast::{
        MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA, MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA,
    };
    use crate::quality::retained::{check, Context, Request};
    use ay_core::{Proof, TheoryLemmaKind};

    let full = |route| {
        let (mut terms, clause) = fixture(route, Source::Valid);
        let assertion = terms.mk_not(clause);
        let mut proof = Proof::new();
        let assume = proof.add_assume(assertion, None);
        let lemma =
            proof.add_theory_lemma_with_kind("bv", vec![clause], TheoryLemmaKind::BvBitBlast);
        proof.add_resolution(vec![], assertion, assume, lemma);
        (terms, proof, assertion)
    };
    for route in ROUTES {
        let calls = producer_test_counter::count();
        let prepayments = Cell::new(0);
        let mut progress = |work, bytes| {
            if (work, bytes)
                == (
                    MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA as usize,
                    MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA,
                )
            {
                prepayments.set(prepayments.get() + 1);
            }
            true
        };
        let (quality, payloads) = {
            let (terms, proof, assertion) = full(route);
            check(
                &proof,
                Context {
                    terms: &terms,
                    dt_decls: None,
                    ctor_selectors: None,
                    datatype_member_signatures: &[],
                    problem_assertions: &[assertion],
                },
                Request {
                    operation: RetainedOperation::Capture,
                    deadline: deadline(),
                    wire_limits: None,
                },
                &mut progress,
            )
            .unwrap()
        };
        assert!(quality.is_complete());
        assert_eq!(quality.total_steps, 3);
        assert_eq!(payloads.len(), 1);
        assert_eq!(payloads[0].step, 1);
        assert_eq!(prepayments.get(), 1);
        assert_eq!(producer_test_counter::count(), calls + route.roles().len());
        let calls = producer_test_counter::count();
        let (terms, proof, assertion) = full(route);
        let (quality, output) = check(
            &proof,
            Context {
                terms: &terms,
                dt_decls: None,
                ctor_selectors: None,
                datatype_member_signatures: &[],
                problem_assertions: &[assertion],
            },
            Request {
                operation: RetainedOperation::Replay(&payloads),
                deadline: deadline(),
                wire_limits: None,
            },
            &mut progress,
        )
        .unwrap();
        assert!(quality.is_complete());
        assert_eq!(output, []);
        assert_eq!(
            prepayments.get(),
            2,
            "one whole-lemma reservation per independent check"
        );
        assert_eq!(producer_test_counter::count(), calls);
    }
}
