// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Focused resource and capability boundaries for proof-producing BV replay.

use std::time::Duration;

use super::*;

fn expression_shape(root: &BvExpr) -> (usize, usize) {
    let mut stack = vec![(root, 1_usize)];
    let mut nodes = 0_usize;
    let mut max_depth = 0_usize;
    while let Some((expression, depth)) = stack.pop() {
        nodes += 1;
        max_depth = max_depth.max(depth);
        match expression {
            BvExpr::Leaf { .. } | BvExpr::Const { .. } => {}
            BvExpr::ZeroExt(inner, _)
            | BvExpr::Extract { inner, .. }
            | BvExpr::SignExt(inner, _)
            | BvExpr::Not(inner) => stack.push((inner, depth + 1)),
            BvExpr::CarryOut { lhs, rhs, .. }
            | BvExpr::Add(lhs, rhs)
            | BvExpr::Sub(lhs, rhs)
            | BvExpr::Or(lhs, rhs)
            | BvExpr::And(lhs, rhs)
            | BvExpr::Xor(lhs, rhs)
            | BvExpr::Shl(lhs, rhs)
            | BvExpr::Lshr(lhs, rhs)
            | BvExpr::Ashr(lhs, rhs)
            | BvExpr::Eq(lhs, rhs)
            | BvExpr::Mul(lhs, rhs) => {
                stack.push((rhs, depth + 1));
                stack.push((lhs, depth + 1));
            }
        }
    }
    (nodes, max_depth)
}

#[test]
fn proof_producing_limits_keep_finite_internal_resource_envelope() {
    let (limits, _) = proof_producing_limits(None);
    assert_eq!(limits.max_expr_nodes, 4096);
    assert_eq!(limits.max_expr_depth, 512);
    assert_eq!(limits.max_estimated_gate_work, 100_000);
    assert_eq!(
        limits.max_expanded_literals,
        MAX_PROOF_PRODUCING_EXPANDED_LITERALS
    );
    assert_eq!(limits.max_expanded_literals, 4_000_000);
    assert_eq!(limits.max_expansion_work, 50_000_000);
    assert_eq!(
        limits.max_expansion_bytes,
        PROOF_PRODUCING_REPLAY_BYTES_PER_LEMMA
    );
    assert_eq!(limits.max_resolution_steps, 250_000);
    assert_eq!(PROOF_PRODUCING_DEADLINE, Duration::from_secs(3));
    assert_eq!(PROOF_PRODUCING_REPLAY_BYTES_PER_LEMMA, 128 * 1024 * 1024);
    assert!(limits.resolution.deadline.is_some());
    assert_eq!(
        limits.resolution.deadline,
        limits.resolution.validation.deadline
    );
    assert_eq!(limits.resolution.max_num_vars, 150_000);
    assert_eq!(limits.resolution.max_input_clauses, 700_000);
    assert_eq!(limits.resolution.max_input_literals, 3_000_000);
    assert_eq!(limits.resolution.max_input_bytes, 64 * 1024 * 1024);
    assert_eq!(MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA, 50_000_000);
    assert_eq!(MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA, 768 * 1024 * 1024);
    const { assert!(MAX_PROOF_PRODUCING_TERM_EDGES >= 2 * MAX_PROOF_PRODUCING_TERM_NODES) };
    assert_eq!(
        limits.resolution.validation.max_bytes,
        PROOF_PRODUCING_REPLAY_BYTES_PER_LEMMA
    );
}

#[test]
fn width32_add_associativity_crosses_public_literal_cap_but_fits_internal() {
    const WIDTH: u32 = 32;
    let mut terms = TermStore::new();
    let sort = Sort::bitvec(WIDTH);
    let a = terms.mk_var("assoc_a", sort.clone());
    let b = terms.mk_var("assoc_b", sort.clone());
    let c = terms.mk_var("assoc_c", sort);
    let ab = terms.mk_bvadd(vec![a, b]);
    let left = terms.mk_bvadd(vec![ab, c]);
    let bc = terms.mk_bvadd(vec![b, c]);
    let right = terms.mk_bvadd(vec![a, bc]);
    let equality = terms.mk_eq(left, right);
    let disequality = terms.mk_not(equality);

    // Lower the exact source query once, then prove that the former/internal
    // two-million preset really exercises this regression instead of passing
    // through a simplification or a smaller proof after solver drift.
    let (mut old_limits, old_deadline) = proof_producing_limits(None);
    old_limits.max_expanded_literals = 2_000_000;
    let mut lowerer = ProofProducingLowerer::new(&terms, old_deadline);
    let lowered = lowerer
        .lower_bool_terms(&[disequality])
        .expect("addition associativity is in the source Bool/BV fragment");
    let conjunction = balanced_bool_expr(lowered, true, BvExpr::and)
        .expect("one lowered root forms a conjunction");
    let false_expr = BvExpr::const_val(0, 1);
    assert!(matches!(
        export_bv_blast_proof_expr_with_limits(&conjunction, &false_expr, &old_limits),
        Err(BvExprExportError::ResourceLimit {
            resource: "expanded literals",
            limit: 2_000_000,
            actual,
        }) if actual > 2_000_000
    ));

    let (limits, _) = proof_producing_limits(None);
    let proof = export_bv_blast_proof_expr_with_limits(&conjunction, &false_expr, &limits)
        .expect("the internal four-million-literal envelope must surface the refutation");
    proof
        .validate_with_limits(&proof_replay_limits(&limits))
        .expect("the surfaced refutation must independently replay");

    let evidence = authenticate_bool_bv_unsat_query(&terms, &[disequality], None)
        .expect("32-bit modular addition associativity must have a bounded checked refutation");
    assert!(evidence.is_current_for(&terms, &[disequality]));
}

#[test]
fn source_lowering_accepts_the_measured_depth_257_shape() {
    let mut terms = TermStore::new();
    let mut root = terms.mk_var("depth_257_leaf", Sort::Bool);
    for _ in 1..257 {
        root = terms.mk_not_raw(root);
    }
    let deadline = Instant::now() + Duration::from_secs(1);
    let mut lowerer = ProofProducingLowerer::new(&terms, deadline);
    let expression = lowerer
        .lower_bool(root)
        .expect("the measured depth-257 shape must clear the 512 stack bound");
    assert_eq!(expression_shape(&expression), (257, 257));
}

#[test]
fn nary_boolean_lowering_is_balanced_instead_of_linear_depth() {
    const ROOTS: usize = 1024;
    let mut terms = TermStore::new();
    let args: Vec<_> = (0..ROOTS)
        .map(|index| terms.mk_var(format!("balanced_{index}"), Sort::Bool))
        .collect();
    let root = terms.mk_app(Symbol::named("and"), args, Sort::Bool);
    let deadline = Instant::now() + Duration::from_secs(1);
    let mut lowerer = ProofProducingLowerer::new(&terms, deadline);
    let expression = lowerer
        .lower_bool(root)
        .expect("a 1024-way source conjunction must lower as a balanced tree");
    assert_eq!(expression_shape(&expression), (2 * ROOTS - 1, 11));
}

#[test]
fn expired_deadline_stops_lowering_before_visiting_a_term() {
    let mut terms = TermStore::new();
    let root = terms.mk_var("expired_lowering", Sort::Bool);
    let mut lowerer = ProofProducingLowerer::new(&terms, Instant::now());
    let error = lowerer
        .lower_bool(root)
        .expect_err("an expired caller deadline must stop before source traversal");
    assert!(error.contains("lowering deadline"));
    assert_eq!(lowerer.visited_nodes, 0);
    assert!(lowerer.resource_exhausted);

    let error = authenticate_bool_bv_unsat_query(&terms, &[root], Some(Instant::now()))
        .expect_err("resource exhaustion must not be reported as unsupported syntax");
    assert!(matches!(
        error,
        BoolBvUnsatAuthenticationError::ResourceLimit { .. }
    ));
    // An exhausted envelope carries no semantic information, so this lane must
    // DECLINE and let the remaining certification routes run.
    assert!(error.is_capability_decline());
}

/// The decline introduced for exhausted envelopes must NOT extend to the two
/// errors that are positive evidence the claimed UNSAT is wrong. If either of
/// these ever starts declining, a refuted verdict would be published.
#[test]
fn satisfiable_and_replay_failures_are_never_capability_declines() {
    let satisfiable = BoolBvUnsatAuthenticationError::Satisfiable;
    assert!(!satisfiable.is_capability_decline());
    assert!(!satisfiable.is_unsupported_fragment());

    let replay = BoolBvUnsatAuthenticationError::Replay {
        reason: "gate clause 7 does not follow".to_string(),
    };
    assert!(!replay.is_capability_decline());
    assert!(!replay.is_unsupported_fragment());

    let refutation = BoolBvUnsatAuthenticationError::Refutation {
        reason: "not surfaceable as pure-RUP resolution".to_string(),
    };
    assert!(!refutation.is_capability_decline());

    let exhausted = BoolBvUnsatAuthenticationError::ResourceLimit {
        reason: "proof resource `expression nodes` exceeds limit 4096".to_string(),
    };
    assert!(exhausted.is_capability_decline());
}
