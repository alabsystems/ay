// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver-free controls. Golden shapes and charge formulas below are derived
//! from the pre-cancellation implementation, not a claimed executed baseline.

use super::*;

mod construction;
mod rup;

#[test]
fn final_export_refusal_is_terminal_and_old_deadline_wins_before_callback() {
    assert_eq!(
        finish_expr_export(None, &mut || false),
        Err(BvExprExportError::Cancelled)
    );
    let mut limits = expression_limits();
    limits.resolution.deadline = Some(Instant::now());
    assert_eq!(
        finish_expr_export(Some(&limits), &mut || panic!("already expired")),
        Err(BvExprExportError::ResourceLimit {
            resource: "proof export deadline",
            limit: 0,
            actual: 1,
        })
    );
    assert_eq!(finish_expr_export(None, &mut || true), Ok(()));
}

#[test]
fn export_cancellation_latch_survives_refusal_and_caught_panic() {
    let mut calls = 0;
    cancellation::run(
        &mut || {
            calls += 1;
            false
        },
        |poll| {
            assert!(!poll());
            assert!(!poll());
        },
    );
    assert_eq!(calls, 1);
    cancellation::run(&mut || panic!("callback panic"), |poll| {
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| poll())).is_err());
        assert!(!poll());
    });
}

fn expression_limits() -> BvExprProofLimits {
    BvExprProofLimits::conservative_external(Instant::now() + Duration::from_secs(60), 1_000)
}

#[test]
fn preflight_counts_shared_gates_and_every_source_node_can_refuse() {
    let a = BvExpr::leaf("a", 8);
    let b = BvExpr::leaf("b", 8);
    let expr = BvExpr::Xor(
        Box::new(BvExpr::Mul(Box::new(a.clone()), Box::new(b.clone()))),
        Box::new(BvExpr::Shl(Box::new(a), Box::new(b))),
    );
    let limits = expression_limits();
    let mut census = BvExprPreflight::default();
    let mut polls = 0;
    assert_eq!(
        preflight_bv_expr_with_cancellation(&expr, &limits, &mut census, 1, &mut || {
            polls += 1;
            true
        },),
        Ok(8)
    );
    // Seven occurrences; `a` and `b` repeat, so five distinct nodes. The
    // estimate is 8 + 8 leaf inputs, the product's and the barrel shifter's
    // topology bounds (142 and 136) and one gate per bit of the xor.
    assert_eq!(
        (
            census.occurrences,
            census.nodes,
            census.leaf_name_bytes,
            census.estimated_gate_work
        ),
        (7, 5, 4, 302)
    );
    assert_eq!(census.leaf_widths.len(), 2);
    assert_eq!(census.leaf_widths.get("a"), Some(&8));
    assert_eq!(census.leaf_widths.get("b"), Some(&8));
    assert_eq!(polls, 7);
    for stop in 1..=polls {
        let mut calls = 0;
        assert_eq!(
            preflight_bv_expr_with_cancellation(
                &expr,
                &limits,
                &mut BvExprPreflight::default(),
                1,
                &mut || {
                    calls += 1;
                    calls != stop
                },
            ),
            Err(BvExprExportError::Cancelled)
        );
        assert_eq!(calls, stop);
    }
    let mut capped = expression_limits();
    capped.max_estimated_gate_work = 301;
    assert_eq!(
        preflight_bv_expr_with_cancellation(
            &expr,
            &capped,
            &mut BvExprPreflight::default(),
            1,
            &mut || true,
        ),
        Err(BvExprExportError::ResourceLimit {
            resource: "estimated bit-blast gates",
            limit: 301,
            actual: 302,
        })
    );
}

#[test]
fn missing_deadline_and_typed_sat_refusals_keep_their_boundaries() {
    let mut limits = expression_limits();
    limits.resolution.deadline = None;
    let expression = BvExpr::const_val(1, 1);
    assert_eq!(
        export_bv_blast_proof_expr_with_limits_and_cancellation(
            &expression,
            &expression,
            &limits,
            &mut || panic!("already invalid limits"),
        ),
        Err(BvExprExportError::ResourceLimit {
            resource: "absolute proof deadline",
            limit: 1,
            actual: 0,
        })
    );
    for refusal in [
        ResolutionProofError::Cancelled,
        ResolutionProofError::Validation(ResolutionValidationError::Cancelled),
    ] {
        assert_eq!(
            map_bounded_resolution_error(refusal, &limits.resolution),
            BvExprExportError::Cancelled
        );
    }
    assert_eq!(
        map_bounded_resolution_error(ResolutionProofError::Satisfiable, &limits.resolution),
        BvExprExportError::NoRefutation
    );
}

#[test]
fn sat_materialization_keeps_literal_order_caps_and_inner_refusal() {
    let clauses = vec![
        Clause {
            id: 0,
            lits: vec![Lit::pos(1), Lit::neg(0), Lit::pos(1)],
            provenance: ClauseProvenance::Disequality,
        },
        Clause {
            id: 1,
            lits: vec![],
            provenance: ClauseProvenance::Disequality,
        },
    ];
    let limits = ResolutionProofLimits {
        max_input_clauses: 2,
        max_input_clause_literals: 3,
        max_input_literals: 3,
        max_input_bytes: 1_024,
        ..ResolutionProofLimits::default()
    };
    let expected = vec![
        vec![
            Literal::positive(Variable::new(1)),
            Literal::negative(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
        vec![],
    ];
    let mut polls = 0;
    assert_eq!(
        materialize_sat_clauses_with_cancellation(&clauses, &limits, &mut || {
            polls += 1;
            true
        }),
        Ok(expected.clone())
    );
    assert!(polls >= 9); // entry + two census + two records + three literals + final
    for stop in 1..=polls {
        let mut calls = 0;
        assert_eq!(
            materialize_sat_clauses_with_cancellation(&clauses, &limits, &mut || {
                calls += 1;
                calls != stop
            }),
            Err(BvExprExportError::Cancelled)
        );
        assert_eq!(calls, stop);
    }
    assert_eq!(
        materialize_sat_clauses_with_cancellation(&clauses, &limits, &mut || true),
        Ok(expected)
    );
    let capped = ResolutionProofLimits {
        max_input_literals: 2,
        ..limits
    };
    assert_eq!(
        materialize_sat_clauses_with_cancellation(&clauses, &capped, &mut || true),
        Err(BvExprExportError::ResourceLimit {
            resource: "SAT input literals",
            limit: 2,
            actual: 3,
        })
    );
}
