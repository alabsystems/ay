// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn cnf_only_every_transient_refusal_including_publication_is_terminal() {
    let expression = BvExpr::add(BvExpr::leaf("a", 2), BvExpr::leaf("b", 2));
    let limits = limits();
    let mut polls = 0;
    let expected = build_bv_expr_cnf(&expression, &expression, &limits, &mut || {
        polls += 1;
        true
    })
    .unwrap();
    assert!(polls > 10);
    for stop in 1..=polls {
        let mut calls = 0;
        assert_eq!(
            build_bv_expr_cnf(&expression, &expression, &limits, &mut || {
                calls += 1;
                calls != stop
            }),
            Err(BvExprExportError::Cancelled)
        );
        assert_eq!(calls, stop);
    }
    assert_eq!(
        build_bv_expr_cnf(&expression, &expression, &limits, &mut || true),
        Ok(expected)
    );
}

#[test]
fn cnf_only_keeps_cumulative_caller_control_between_reconstructions() {
    let a = BvExpr::leaf("a", 1);
    let limits = limits();
    let mut first_polls = 0;
    build_bv_expr_cnf(&a, &a, &limits, &mut || {
        first_polls += 1;
        true
    })
    .unwrap();
    let mut calls = 0;
    let mut shared = || {
        calls += 1;
        calls <= first_polls
    };
    build_bv_expr_cnf(&a, &a, &limits, &mut shared).unwrap();
    assert_eq!(
        build_bv_expr_cnf(&a, &a, &limits, &mut shared),
        Err(BvExprExportError::Cancelled)
    );
    assert_eq!(calls, first_polls + 1);
}

#[test]
fn cnf_only_missing_expired_and_earlier_replay_deadlines_refuse() {
    let a = BvExpr::leaf("a", 1);
    let mut missing = limits();
    missing.resolution.deadline = None;
    assert_eq!(
        build_bv_expr_cnf(&a, &a, &missing, &mut || panic!("missing deadline")),
        Err(BvExprExportError::ResourceLimit {
            resource: "absolute proof deadline",
            limit: 1,
            actual: 0,
        })
    );
    for replay_expires in [false, true] {
        let mut expired = limits();
        if replay_expires {
            expired.resolution.validation.deadline = Some(Instant::now());
        } else {
            expired.resolution.deadline = Some(Instant::now());
        }
        assert!(matches!(
            build_bv_expr_cnf(&a, &a, &expired, &mut || panic!("expired deadline")),
            Err(BvExprExportError::ResourceLimit {
                resource: "expression preflight deadline",
                ..
            })
        ));
    }
}

#[test]
fn cnf_only_preserves_all_preflight_and_actual_shape_limits() {
    let a = BvExpr::leaf("a", 1);
    for resource in 0..11 {
        let mut capped = limits();
        match resource {
            10 => capped.max_expr_occurrences = 0,
            0 => capped.max_expr_nodes = 0,
            1 => capped.max_expr_depth = 0,
            2 => capped.max_leaf_name_bytes = 0,
            3 => capped.max_internal_width = 0,
            4 => capped.max_estimated_gate_work = 0,
            5 => capped.max_construction_bytes = 0,
            6 => capped.resolution.max_num_vars = 0,
            7 => capped.resolution.max_input_clauses = 0,
            8 => capped.resolution.max_input_literals = 0,
            9 => capped.resolution.max_input_clause_literals = 1,
            _ => unreachable!(),
        }
        assert!(
            matches!(
                build_bv_expr_cnf(&a, &a, &capped, &mut || true),
                Err(BvExprExportError::ResourceLimit { .. }
                    | BvExprExportError::UnsupportedWidth { .. })
            ),
            "resource {resource}"
        );
    }
    for malformed in [
        BvExpr::const_val(2, 1),
        BvExpr::leaf("a", 0),
        BvExpr::extract(a.clone(), 1, 0),
    ] {
        assert!(build_bv_expr_cnf(&malformed, &a, &limits(), &mut || true).is_err());
    }
}

#[test]
fn cnf_only_exact_construction_envelope_and_one_short_are_distinct() {
    let a = BvExpr::leaf("a", 1);
    let mut exact = limits();
    let preflight = preflight_bv_equality(&a, &a, &exact, &mut || true).unwrap();
    // `a == a`: two occurrences of one distinct node.
    assert_eq!(
        (
            preflight.occurrences,
            preflight.nodes,
            preflight.estimated_gate_work,
            preflight.top_width
        ),
        (2, 1, 2, 1)
    );
    // Obtain the old reservation formula's required bytes without allocating
    // its graph. The successful public route still performs its own preflight.
    exact.max_construction_bytes = 0;
    let required = match build(&a, &a, Some((&exact, preflight)), &mut || true) {
        Err(BvExprExportError::ResourceLimit {
            resource: "expression construction bytes",
            actual,
            ..
        }) => actual,
        other => panic!("expected construction refusal, got {other:?}"),
    };
    assert!(required > 0 && required < usize::MAX);
    exact.max_construction_bytes = required;
    exact.max_expr_nodes = 1;
    exact.max_expr_occurrences = 2;
    exact.max_expr_depth = 1;
    exact.max_leaf_name_bytes = 2;
    exact.max_internal_width = 1;
    exact.max_estimated_gate_work = 2;
    exact.resolution.max_num_vars = 2;
    exact.resolution.max_input_clauses = 17;
    exact.resolution.max_input_literals = 65;
    exact.resolution.max_input_clause_literals = 2;
    assert_eq!(
        build_bv_expr_cnf(&a, &a, &exact, &mut || true).unwrap(),
        build_cnf(&a, &a)
    );
    for resource in 0..9 {
        let mut short = exact.clone();
        match resource {
            8 => short.max_expr_occurrences -= 1,
            0 => short.max_construction_bytes -= 1,
            1 => short.max_expr_nodes -= 1,
            2 => short.max_leaf_name_bytes -= 1,
            3 => short.max_estimated_gate_work -= 1,
            4 => short.resolution.max_num_vars -= 1,
            5 => short.resolution.max_input_clauses -= 1,
            6 => short.resolution.max_input_literals -= 1,
            7 => short.resolution.max_input_clause_literals -= 1,
            _ => unreachable!(),
        }
        assert!(
            matches!(
                build_bv_expr_cnf(&a, &a, &short, &mut || true),
                Err(BvExprExportError::ResourceLimit { .. })
            ),
            "resource {resource}"
        );
    }
}
