// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Focused resource-boundary tests for bounded BvExpr proof production.

use std::{mem::size_of, time::Duration};

use crate::bv_blast_export::BvBlastValidateLimits;

use super::*;

fn finite_replay_limits(proof: &BvBlastProof) -> BvBlastValidateLimits {
    BvBlastValidateLimits {
        deadline: Some(Instant::now() + Duration::from_secs(5)),
        max_vars: proof.vars.len(),
        max_bit_lemmas: proof.bit_lemmas.len(),
        max_clauses: proof.clauses.len(),
        max_clause_literals: proof
            .clauses
            .iter()
            .map(|clause| clause.lits.len())
            .max()
            .unwrap_or(0),
        max_original_literals: proof.clauses.iter().map(|clause| clause.lits.len()).sum(),
        max_resolution_steps: proof.refutation.steps.len(),
        max_derived_literals: proof
            .refutation
            .steps
            .iter()
            .map(|step| step.clause.len())
            .sum(),
        max_work: 50_000_000,
    }
}

fn expression_limits(depth: usize) -> BvExprProofLimits {
    let resolution = ResolutionProofLimits {
        deadline: Some(Instant::now() + Duration::from_secs(1)),
        ..ResolutionProofLimits::default()
    };
    BvExprProofLimits {
        max_expr_nodes: 4096,
        max_expr_depth: depth,
        max_leaf_name_bytes: 1024 * 1024,
        max_internal_width: 128,
        max_estimated_gate_work: 100_000,
        max_construction_bytes: 128 * 1024 * 1024,
        max_resolution_steps: 250_000,
        max_expanded_literals: 2_000_000,
        max_expansion_work: 50_000_000,
        max_expansion_bytes: 128 * 1024 * 1024,
        resolution,
    }
}

fn nested_not(depth: usize) -> BvExpr {
    let mut expression = BvExpr::leaf("depth_leaf", 1);
    for _ in 1..depth {
        expression = BvExpr::not(expression);
    }
    expression
}

fn public_budget(max_resolution_steps: usize) -> BvExprProofBudget {
    BvExprProofBudget::conservative(Duration::from_secs(5), max_resolution_steps)
        .expect("test budget is conservative")
}

fn clean_shift_identity(width: u32) -> (BvExpr, BvExpr) {
    let value = BvExpr::leaf("clean_value", width);
    let amount = BvExpr::leaf("clean_amount", width);
    let shift = BvExpr::shl(value, amount);
    (
        BvExpr::or(BvExpr::const_val(0, width), shift.clone()),
        shift,
    )
}

fn clean_mul_widening_readout(width: u32) -> (BvExpr, BvExpr) {
    let a = BvExpr::leaf("A0", width);
    let b = BvExpr::leaf("B0", width);
    let product = BvExpr::mul(a, b);
    (
        BvExpr::extract(BvExpr::zero_ext(product.clone(), width), width - 1, 0),
        product,
    )
}

#[test]
fn public_budget_rejects_zero_or_oversized_controls() {
    assert_eq!(
        BvExprProofBudget::conservative(Duration::ZERO, 4096),
        Err(BvExprProofBudgetError::ZeroTimeout)
    );
    let too_long = BvExprProofBudget::MAX_TIMEOUT + Duration::from_nanos(1);
    assert_eq!(
        BvExprProofBudget::conservative(too_long, 4096),
        Err(BvExprProofBudgetError::TimeoutTooLong {
            requested: too_long,
            maximum: BvExprProofBudget::MAX_TIMEOUT,
        })
    );
    assert_eq!(
        BvExprProofBudget::conservative(Duration::from_secs(1), 0),
        Err(BvExprProofBudgetError::ZeroResolutionSteps)
    );
    assert_eq!(
        BvExprProofBudget::conservative(
            Duration::from_secs(1),
            BvExprProofBudget::MAX_RESOLUTION_STEPS + 1,
        ),
        Err(BvExprProofBudgetError::TooManyResolutionSteps {
            requested: BvExprProofBudget::MAX_RESOLUTION_STEPS + 1,
            maximum: BvExprProofBudget::MAX_RESOLUTION_STEPS,
        })
    );
}

#[test]
fn public_budget_binds_every_resolution_step_layer_without_bypass() {
    let budget = public_budget(4096);
    let deadline = Instant::now() + budget.timeout();
    let limits = BvExprProofLimits::conservative_external(deadline, budget.max_resolution_steps());
    assert_eq!(limits.max_resolution_steps, 4096);
    assert_eq!(limits.resolution.max_derived_steps, 4096);
    assert_eq!(limits.resolution.validation.max_derived_steps, 4096);
    assert_eq!(limits.resolution.deadline, Some(deadline));
    assert_eq!(limits.resolution.validation.deadline, Some(deadline));
    assert_eq!(limits.max_expanded_literals, BOUNDED_MAX_EXPANDED_LITERALS);
    assert_eq!(limits.max_expanded_literals, 2_000_000);
}

#[test]
fn public_bounded_export_rejects_oversized_tree_during_preflight() {
    let expression = nested_not(BOUNDED_MAX_EXPR_DEPTH + 1);
    assert!(matches!(
        export_bv_blast_proof_expr_bounded(&expression, &expression, &public_budget(4096)),
        Err(BvExprExportError::ResourceLimit {
            resource: "expression depth",
            limit: BOUNDED_MAX_EXPR_DEPTH,
            actual,
        }) if actual == BOUNDED_MAX_EXPR_DEPTH + 1
    ));
}

#[test]
fn bounded_preflight_rejects_one_leaf_name_at_different_widths() {
    let wide = BvExpr::leaf("same", 128);
    let narrow = BvExpr::leaf("same", 1);
    let lhs = BvExpr::eq(wide.clone(), wide);
    let rhs = BvExpr::eq(narrow.clone(), narrow);
    assert!(matches!(
        export_bv_blast_proof_expr_bounded(&lhs, &rhs, &public_budget(4096)),
        Err(BvExprExportError::Malformed(message))
            if message.contains("used at both 128 and 1 bits")
    ));
}

#[test]
fn bounded_top_level_equality_storage_includes_exporter_gates() {
    let lhs = BvExpr::leaf("lhs", 1);
    let rhs = BvExpr::leaf("rhs", 1);
    assert_eq!(
        export_bv_blast_proof_expr_bounded(&lhs, &rhs, &public_budget(4096)),
        Err(BvExprExportError::NoRefutation)
    );
}

#[test]
fn bounded_preflight_charges_top_level_equality_before_construction() {
    let lhs = BvExpr::leaf("lhs", 1);
    let rhs = BvExpr::leaf("rhs", 1);
    let mut limits = expression_limits(16);
    // Two one-bit leaves cost two work units; the exporter-added XNOR is the
    // third and must be rejected before any retained construction allocation.
    limits.max_estimated_gate_work = 2;
    assert!(matches!(
        export_bv_blast_proof_expr_with_limits(&lhs, &rhs, &limits),
        Err(BvExprExportError::ResourceLimit {
            resource: "estimated bit-blast gates",
            limit: 2,
            actual: 3,
        })
    ));
}

#[test]
fn bounded_export_rejects_a_missing_or_expired_deadline() {
    let expression = BvExpr::leaf("deadline", 1);

    // Public budgets use relative timeouts and cannot omit or retain a stale
    // deadline. Retain defensive checks for the crate-internal limits path.
    let mut missing =
        BvExprProofLimits::conservative_external(Instant::now() + Duration::from_secs(1), 4096);
    missing.resolution.deadline = None;
    assert!(matches!(
        export_bv_blast_proof_expr_with_limits(&expression, &expression, &missing),
        Err(BvExprExportError::ResourceLimit {
            resource: "absolute proof deadline",
            limit: 1,
            actual: 0,
        })
    ));

    let expired = BvExprProofLimits::conservative_external(Instant::now(), 4096);
    assert!(matches!(
        export_bv_blast_proof_expr_with_limits(&expression, &expression, &expired),
        Err(BvExprExportError::ResourceLimit {
            resource: "expression preflight deadline",
            ..
        })
    ));
}

#[test]
fn bounded_export_rejects_resolution_work_instead_of_bypassing_tight_budget() {
    let (lhs, rhs) = clean_shift_identity(4);
    assert!(matches!(
        export_bv_blast_proof_expr_bounded(&lhs, &rhs, &public_budget(1)),
        Err(BvExprExportError::ResourceLimit {
            resource: "resolution derived steps" | "expanded resolution steps",
            limit: 1,
            actual,
        }) if actual > 1
    ));
}

#[test]
fn public_bounded_export_returns_a_clean_style_valid_proof_within_4096_steps() {
    let (lhs, rhs) = clean_shift_identity(4);
    let proof = export_bv_blast_proof_expr_bounded(&lhs, &rhs, &public_budget(4096))
        .expect("Clean's bounded shift identity fits the public preset");
    assert!(proof.refutation.steps.len() <= 4096);
    proof
        .validate_with_limits(&finite_replay_limits(&proof))
        .expect("surfaced proof independently replays");
}

#[test]
fn clean_width8_fused_mul_readout_fits_4096_producer_steps() {
    let (lhs, rhs) = clean_mul_widening_readout(8);
    let budget = BvExprProofBudget::conservative(BvExprProofBudget::MAX_TIMEOUT, 4096)
        .expect("Clean's producer budget is public and finite");
    let proof = export_bv_blast_proof_expr_bounded(&lhs, &rhs, &budget)
        .expect("the exact fused width-8 Clean multiply readout fits 4096 steps");
    assert!(!proof.refutation.steps.is_empty());
    assert!(proof.refutation.steps.len() <= 4096);
    proof
        .validate_with_limits(&finite_replay_limits(&proof))
        .expect("fused multiply proof replays");
}

#[test]
fn clean_width8_mul_by_zero_fits_4096_producer_steps() {
    let width = 8;
    let x = BvExpr::leaf("X0", width);
    let zero = BvExpr::const_val(0, width);
    let lhs = BvExpr::mul(x, zero.clone());
    let budget = BvExprProofBudget::conservative(BvExprProofBudget::MAX_TIMEOUT, 4096)
        .expect("Clean's producer budget is public and finite");
    let proof = export_bv_blast_proof_expr_bounded(&lhs, &zero, &budget)
        .expect("the exact width-8 Clean multiply-by-zero proof fits 4096 steps");
    assert!(!proof.refutation.steps.is_empty());
    assert!(proof.refutation.steps.len() <= 4096);
    proof
        .validate_with_limits(&finite_replay_limits(&proof))
        .expect("multiply-by-zero proof replays");
}

#[test]
fn clean_width4_non_fusing_mul_commutativity_stops_at_4096_producer_steps() {
    let width = 4;
    let a = BvExpr::leaf("A0", width);
    let b = BvExpr::leaf("B0", width);
    let lhs = BvExpr::mul(a.clone(), b.clone());
    let rhs = BvExpr::mul(b, a);
    let budget = BvExprProofBudget::conservative(BvExprProofBudget::MAX_TIMEOUT, 4096)
        .expect("Clean's producer budget is public and finite");
    let started = Instant::now();
    assert!(matches!(
        export_bv_blast_proof_expr_bounded(&lhs, &rhs, &budget),
        Err(BvExprExportError::ResourceLimit {
            resource: "resolution derived steps" | "resolution replay derived steps"
                | "expanded resolution steps",
            limit: 4096,
            actual,
        }) if actual > 4096
    ));
    assert!(
        started.elapsed() <= BvExprProofBudget::MAX_TIMEOUT,
        "the producer must reject at its step cap before the wall deadline"
    );
}

#[test]
fn public_bounded_export_preserves_sat_no_refutation() {
    let variable = BvExpr::leaf("sat", 1);
    let zero = BvExpr::const_val(0, 1);
    assert_eq!(
        export_bv_blast_proof_expr_bounded(&variable, &zero, &public_budget(4096)),
        Err(BvExprExportError::NoRefutation)
    );
}

#[test]
fn preflight_accepts_depth_257_and_enforces_the_512_stack_boundary() {
    let limits = expression_limits(512);

    let measured = nested_not(257);
    let mut state = BvExprPreflight::default();
    assert_eq!(preflight_bv_expr(&measured, &limits, &mut state, 1), Ok(1));

    let boundary = nested_not(512);
    let mut state = BvExprPreflight::default();
    assert_eq!(preflight_bv_expr(&boundary, &limits, &mut state, 1), Ok(1));

    let above = nested_not(513);
    let mut state = BvExprPreflight::default();
    assert!(matches!(
        preflight_bv_expr(&above, &limits, &mut state, 1),
        Err(BvExprExportError::ResourceLimit {
            resource: "expression depth",
            limit: 512,
            actual: 513,
        })
    ));
}

#[test]
fn preflight_observes_an_expired_deadline_before_traversal() {
    let expression = BvExpr::leaf("expired", 1);
    let mut limits = expression_limits(512);
    limits.resolution.deadline = Some(Instant::now());
    let mut state = BvExprPreflight::default();
    assert!(matches!(
        preflight_bv_expr(&expression, &limits, &mut state, 1),
        Err(BvExprExportError::ResourceLimit {
            resource: "expression preflight deadline",
            ..
        })
    ));
    assert_eq!(state.nodes, 0);
}

#[test]
fn sat_materialization_enforces_the_exact_record_and_literal_bytes() {
    let clauses = vec![Clause {
        id: 0,
        lits: vec![Lit::pos(0)],
        provenance: ClauseProvenance::Disequality,
    }];
    let exact = size_of::<Vec<Literal>>() + size_of::<Literal>();
    let mut limits = ResolutionProofLimits {
        deadline: Some(Instant::now() + Duration::from_secs(1)),
        max_input_clauses: 1,
        max_input_literals: 1,
        max_input_clause_literals: 1,
        max_input_bytes: exact,
        ..ResolutionProofLimits::default()
    };

    let materialized = materialize_sat_clauses_bounded(&clauses, &limits)
        .expect("one exact clause fits its record plus literal envelope");
    assert_eq!(materialized.len(), 1);
    assert_eq!(materialized[0].len(), 1);

    limits.max_input_bytes = exact - 1;
    assert!(matches!(
        materialize_sat_clauses_bounded(&clauses, &limits),
        Err(BvExprExportError::ResourceLimit {
            resource: "SAT input materialization",
            limit,
            actual,
        }) if limit == exact - 1 && actual == exact
    ));
}
