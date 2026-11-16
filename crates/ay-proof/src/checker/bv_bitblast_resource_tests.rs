// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Focused resource and capability boundaries for proof-producing BV replay.

use std::time::Duration;

use super::producer_limits::strict_producer_limits;
use super::*;
use crate::bv_blast_solver::export_bv_blast_proof_expr_with_limits;

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
            | BvExpr::Ult(lhs, rhs)
            | BvExpr::Eq(lhs, rhs)
            | BvExpr::Mul(lhs, rhs)
            | BvExpr::UDiv(lhs, rhs)
            | BvExpr::URem(lhs, rhs) => {
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
    assert_eq!(
        limits.resolution.max_conflicts,
        Some(producer_limits::PRODUCER_MAX_CONFLICTS)
    );
    assert_eq!(
        limits.resolution.max_proof_output_bytes,
        producer_limits::PRODUCER_MAX_PROOF_OUTPUT_BYTES
    );
    assert_eq!(
        producer_limits::PRODUCER_HANG_GUARD,
        Duration::from_secs(300)
    );
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
    // The extracted source word keeps this test on actual adder/SAT replay,
    // rather than the new affine full-cancellation polynomial bridge.
    let wide_a = terms.mk_var("assoc_a", Sort::bitvec(64));
    let a = terms.mk_bvextract(31, 0, wide_a);
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

/// One set of counted caps serves the strict checker and the authentication
/// lanes; the wall clock only stops them. Without a caller deadline both end at
/// the hang guard; with one, the authentication envelope ends at it (the
/// solve's own budget), never at a local wall of its own.
#[test]
fn both_envelopes_are_the_counted_caps_with_only_an_outer_stop() {
    let before = Instant::now();
    let (strict, guard) = strict_producer_limits();
    assert!(guard >= before + producer_limits::PRODUCER_HANG_GUARD);
    assert_eq!(strict.resolution.deadline, Some(guard));
    assert_eq!(strict.resolution.validation.deadline, Some(guard));

    let (unbounded, unbounded_deadline) = proof_producing_limits(None);
    assert!(unbounded_deadline >= before + producer_limits::PRODUCER_HANG_GUARD);

    let caller = Instant::now() + Duration::from_millis(1_500);
    let (mut bounded, bounded_deadline) = proof_producing_limits(Some(caller));
    assert_eq!(
        bounded_deadline, caller,
        "the caller's deadline, not a local wall"
    );
    assert_eq!(bounded.resolution.deadline, Some(caller));

    let far = Instant::now() + Duration::from_secs(3_600);
    let (_, clamped) = proof_producing_limits(Some(far));
    assert!(
        clamped < far,
        "a caller deadline past the guard is clamped to it"
    );

    // Apart from where the wall stops them, the three are one envelope.
    let mut unbounded = unbounded;
    for envelope in [&mut bounded, &mut unbounded] {
        envelope.resolution.deadline = Some(guard);
        envelope.resolution.validation.deadline = Some(guard);
        assert_eq!(format!("{strict:?}"), format!("{envelope:?}"));
    }
}

/// Exhausting a counted cap is a counted refusal, never a deadline: under the
/// strict envelope, with its hang guard minutes away, 7-bit multiplication
/// distributivity (about 80,000 conflicts to refute) stops at a 1,000-conflict
/// budget with the conflict cap named. `validate` turns every such refusal into
/// a rejected lemma, as the gate-budget tests in `theory_forgery_tests` pin.
#[test]
fn strict_envelope_exhaustion_is_a_counted_refusal() {
    const WIDTH: u32 = 7;
    let [a, b, c] = ["dist_a", "dist_b", "dist_c"].map(|name| BvExpr::leaf(name, WIDTH));
    let lhs = BvExpr::mul(a.clone(), BvExpr::add(b.clone(), c.clone()));
    let rhs = BvExpr::add(BvExpr::mul(a.clone(), b), BvExpr::mul(a, c));
    let (mut limits, _) = strict_producer_limits();
    limits.resolution.max_conflicts = Some(1_000);
    let error = crate::bv_blast_solver::validate_bv_expr_compact(
        &lhs,
        &rhs,
        &limits,
        &proof_replay_limits(&limits),
        &mut || true,
    )
    .expect_err("a refutation beyond the conflict budget must not be accepted");
    assert!(
        matches!(
            error,
            BvExprExportError::ResourceLimit {
                resource: "resolution conflicts",
                limit: 1_000,
                ..
            }
        ),
        "{error:?}"
    );
}

/// The counted caps accept what the retired three-second wall accepted.
/// 7-bit multiplication distributivity refutes in about 80,800 conflicts and
/// an 11.9 MB proof; the wall accepted it in 1.6 s (release, 2026-09-24), and
/// the 64,000-conflict cap this envelope briefly carried refused it. Through
/// the whole strict checker the production envelope accepts it, and the same
/// envelope with only the old conflict cap refuses it on that cap, so the
/// acceptance is the cap's doing.
#[test]
fn strict_checker_accepts_what_the_retired_wall_accepted() {
    const WIDTH: u32 = 7;
    let mut terms = TermStore::new();
    let sort = Sort::bitvec(WIDTH);
    let [x, y, z] = ["wall_x", "wall_y", "wall_z"].map(|name| terms.mk_var(name, sort.clone()));
    let mut op = |name: &str, args: Vec<TermId>| {
        terms.mk_app(Symbol::named(name), args, Sort::bitvec(WIDTH))
    };
    let sum = op("bvadd", vec![y, z]);
    let lhs = op("bvmul", vec![x, sum]);
    let (xy, xz) = (op("bvmul", vec![x, y]), op("bvmul", vec![x, z]));
    let rhs = op("bvadd", vec![xy, xz]);
    let identity = terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool);
    let negation = terms.mk_not_raw(identity);
    let mut proof = Proof::new();
    let assumption = proof.add_assume(negation, None);
    let lemma = proof.add_theory_lemma_with_kind("BV", vec![identity], TheoryLemmaKind::BvBitBlast);
    proof.add_resolution(vec![], identity, assumption, lemma);
    crate::check_proof_strict(&proof, &terms)
        .expect("the production strict envelope must accept 7-bit distributivity");

    let [a, b, c] = ["wall_a", "wall_b", "wall_c"].map(|name| BvExpr::leaf(name, WIDTH));
    let lhs = BvExpr::mul(a.clone(), BvExpr::add(b.clone(), c.clone()));
    let rhs = BvExpr::add(BvExpr::mul(a.clone(), b), BvExpr::mul(a, c));
    let (mut limits, _) = strict_producer_limits();
    limits.resolution.max_conflicts = Some(64_000);
    let error = crate::bv_blast_solver::validate_bv_expr_compact(
        &lhs,
        &rhs,
        &limits,
        &proof_replay_limits(&limits),
        &mut || true,
    )
    .expect_err("the retired 64,000-conflict cap refused this lemma");
    assert!(
        matches!(
            error,
            BvExprExportError::ResourceLimit {
                resource: "resolution conflicts",
                limit: 64_000,
                ..
            }
        ),
        "{error:?}"
    );
}
