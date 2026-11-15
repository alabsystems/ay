// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn retained_reader_preserves_every_transient_stop_including_final_publication() {
    let a = expression();
    let payload = payload();
    let limits = limits();
    let gates = gate_limits(&limits);
    let mut total = 0;
    replay_bv_expr_refutation(&a, &a, Some(&payload), &limits, &gates, &mut || {
        total += 1;
        true
    })
    .unwrap();
    assert!(total > 20);
    for stop in 1..=total {
        let mut calls = 0;
        assert_eq!(
            replay_bv_expr_refutation(&a, &a, Some(&payload), &limits, &gates, &mut || {
                calls += 1;
                calls != stop
            }),
            Err(BvExprExportError::Cancelled),
            "stop {stop}/{total}"
        );
        assert_eq!(calls, stop, "observed refusal cannot restart work");
    }
    read(&payload, &limits).unwrap();
}

#[test]
fn retained_capture_preserves_every_transient_stop_and_can_be_retried_fresh() {
    let a = expression();
    let limits = limits();
    let gates = gate_limits(&limits);
    let mut total = 0;
    capture_bv_expr_refutation(&a, &a, &limits, &gates, &mut || {
        total += 1;
        true
    })
    .unwrap();
    for stop in 1..=total {
        let mut calls = 0;
        assert_eq!(
            capture_bv_expr_refutation(&a, &a, &limits, &gates, &mut || {
                calls += 1;
                calls != stop
            }),
            Err(BvExprExportError::Cancelled),
            "stop {stop}/{total}"
        );
        assert_eq!(calls, stop);
    }
    let produced = capture_bv_expr_refutation(&a, &a, &limits, &gates, &mut || true).unwrap();
    read(&produced, &limits).unwrap();
}

#[test]
fn retained_all_deadlines_and_cumulative_caller_grants_remain_in_force() {
    let a = expression();
    let payload = payload();
    for expired in 0..4 {
        let mut limits = limits();
        let mut gates = gate_limits(&limits);
        match expired {
            0 => limits.resolution.deadline = None,
            1 => limits.resolution.deadline = Some(Instant::now()),
            2 => limits.resolution.validation.deadline = Some(Instant::now()),
            3 => gates.deadline = Some(Instant::now()),
            _ => unreachable!(),
        }
        assert!(
            replay_bv_expr_refutation(&a, &a, Some(&payload), &limits, &gates, &mut || true)
                .is_err()
        );
        assert!(capture_bv_expr_refutation(&a, &a, &limits, &gates, &mut || true).is_err());
    }
    let limits = limits();
    let gates = gate_limits(&limits);
    let mut used = 0;
    replay_bv_expr_refutation(&a, &a, Some(&payload), &limits, &gates, &mut || {
        used += 1;
        true
    })
    .unwrap();
    let grant = used;
    assert_eq!(
        replay_bv_expr_refutation(&a, &a, Some(&payload), &limits, &gates, &mut || {
            used += 1;
            used <= grant
        }),
        Err(BvExprExportError::Cancelled)
    );
    assert_eq!(used, grant + 1);
}

#[test]
fn retained_source_shape_transport_gate_and_dag_caps_each_refuse() {
    for capped in 0..19 {
        let mut limits = limits();
        match capped {
            0 => limits.max_expr_nodes = 0,
            1 => limits.max_estimated_gate_work = 0,
            2 => limits.max_construction_bytes = 0,
            3 => limits.resolution.max_num_vars = 0,
            4 => limits.resolution.max_input_clauses = 0,
            5 => limits.resolution.max_input_literals = 0,
            6 => limits.resolution.max_input_clause_literals = 0,
            7 => limits.resolution.max_input_bytes = 0,
            8 => limits.resolution.max_derived_steps = 0,
            9 => limits.resolution.max_derived_literals = 0,
            10 => limits.resolution.max_hints = 0,
            11 => limits.resolution.max_proof_output_bytes = 0,
            12 => limits.resolution.max_codec_bytes = 0,
            13 => limits.resolution.validation.max_work = 0,
            14 => limits.resolution.validation.max_bytes = 0,
            15 => limits.resolution.validation.max_derived_steps = 0,
            16 => limits.resolution.validation.max_derived_literals = 0,
            17 => limits.resolution.validation.max_hints = 0,
            18 => limits.resolution.validation.max_original_clauses = 0,
            _ => unreachable!(),
        }
        assert!(read(&payload(), &limits).is_err(), "cap {capped}");
    }
    let limits = limits();
    let mut gates = gate_limits(&limits);
    gates.max_work = 0;
    let a = expression();
    assert!(
        replay_bv_expr_refutation(&a, &a, Some(&payload()), &limits, &gates, &mut || true).is_err()
    );
}

fn set_cap(limits: &mut BvExprProofLimits, which: usize, value: usize) {
    match which {
        0 => limits.resolution.validation.max_work = value as u64,
        1 => limits.resolution.validation.max_bytes = value,
        2 => limits.resolution.max_codec_bytes = value,
        3 => limits.resolution.max_input_bytes = value,
        _ => unreachable!(),
    }
}

#[test]
fn retained_exact_and_one_short_work_and_byte_limits_are_deterministic() {
    let payload = payload();
    for which in 0..4 {
        let mut limits = limits();
        let mut low = 0;
        let mut high = 1_000_000;
        set_cap(&mut limits, which, high);
        read(&payload, &limits).unwrap();
        // Search only bounded replay, never rerun SAT production.
        while low < high {
            let middle = low + (high - low) / 2;
            set_cap(&mut limits, which, middle);
            if read(&payload, &limits).is_ok() {
                high = middle;
            } else {
                low = middle + 1;
            }
        }
        assert!(low > 0);
        set_cap(&mut limits, which, low);
        read(&payload, &limits).unwrap();
        set_cap(&mut limits, which, low - 1);
        assert!(read(&payload, &limits).is_err(), "cap {which}, exact {low}");
    }
    let mut limits = limits();
    limits.resolution.max_proof_output_bytes = 104; // 20 + 2*24 + 1*4 + 4*8
    read(&payload, &limits).unwrap();
    limits.resolution.max_proof_output_bytes -= 1;
    assert!(read(&payload, &limits).is_err());
}

#[test]
fn retained_prefix_is_subtracted_once_and_all_live_owners_are_admitted() {
    let limits = limits();
    let a = expression();
    let graph = cnf::build_bv_expr_cnf(&a, &a, &limits, &mut || true)
        .unwrap()
        .into_graph();
    let payload = payload();
    let mut control = Control::new(&limits);
    let shape = control.payload(&payload, &mut || true).unwrap();
    let payload_bytes = control.bytes;
    let graph_bytes = control.graph(&graph, &mut || true).unwrap();
    let dag = codec::decode(&payload, shape, &graph, &mut control, &mut || true).unwrap();
    let retained = control.bytes;
    assert!(retained > payload_bytes + graph_bytes);
    let reduced = control
        .replay_limits(&graph, graph_bytes, payload_bytes, &mut || true)
        .unwrap();
    assert_eq!(
        reduced.resolution.validation.max_work + control.work,
        limits.resolution.validation.max_work
    );
    assert_eq!(
        reduced.resolution.validation.max_bytes + graph_bytes + payload_bytes,
        limits.resolution.validation.max_bytes
    );
    compact::ExprRefutation { graph, dag }
        .validate(&reduced, &gate_limits(&limits), &mut || true)
        .unwrap();
    assert_eq!(control.bytes, retained); // no refund after the replay grant
    assert!(accounting::add(usize::MAX, 1).is_err());
    assert!(accounting::product(usize::MAX, 2).is_err());
    control.work = u64::MAX;
    assert!(control.charge(1, &mut || true).is_err());
}

#[test]
fn retained_callback_unwind_does_not_poison_a_later_independent_reader() {
    let a = expression();
    let limits = limits();
    let payload = payload();
    let mut calls = 0;
    let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = replay_bv_expr_refutation(
            &a,
            &a,
            Some(&payload),
            &limits,
            &gate_limits(&limits),
            &mut || {
                calls += 1;
                assert_ne!(calls, 25, "test callback unwind");
                true
            },
        );
    }));
    assert!(caught.is_err());
    assert_eq!(calls, 25);
    read(&payload, &limits).unwrap();
}

fn encode_peak(
    graph: &BvBlastProof,
    dag: &ResolutionDag,
    limits: &BvExprProofLimits,
) -> Result<(RetainedBvRefutation, usize, u64), BvExprExportError> {
    let mut control = Control::new(limits);
    control.graph(graph, &mut || true)?;
    let shape = control.dag(dag, &mut || true)?;
    let encoded = codec::encode(dag, shape, &mut control, &mut || true)?;
    Ok((encoded, control.bytes, control.work))
}

#[test]
fn retained_encoding_admits_the_distinct_graph_dag_and_payload_peak() {
    let limits = limits();
    let a = expression();
    let graph = cnf::build_bv_expr_cnf(&a, &a, &limits, &mut || true)
        .unwrap()
        .into_graph();
    let expected = payload();
    let mut control = Control::new(&limits);
    let shape = control.payload(&expected, &mut || true).unwrap();
    control.graph(&graph, &mut || true).unwrap();
    let dag = codec::decode(&expected, shape, &graph, &mut control, &mut || true).unwrap();
    let (encoded, bytes, work) = encode_peak(&graph, &dag, &limits).unwrap();
    assert_eq!(encoded, expected);
    read(&encoded, &limits).unwrap();
    let mut exact = limits.clone();
    exact.resolution.max_codec_bytes = bytes;
    exact.resolution.validation.max_work = work;
    assert_eq!(encode_peak(&graph, &dag, &exact).unwrap().0, expected);
    exact.resolution.max_codec_bytes -= 1;
    assert!(encode_peak(&graph, &dag, &exact).is_err());
    exact.resolution.max_codec_bytes = bytes;
    exact.resolution.validation.max_work -= 1;
    assert!(encode_peak(&graph, &dag, &exact).is_err());
}
