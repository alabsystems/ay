// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

const AFFINE_OPTIMAL_MPS: &str = "NAME          AFFINE_OPTIMAL\n\
                    ROWS\n\
                    \x20N  COST\n\
                    \x20E  LINK\n\
                    COLUMNS\n\
                    \x20   MARK0000  'MARKER'              'INTORG'\n\
                    \x20   X         COST      1          LINK      1\n\
                    \x20   Y         COST      2          LINK     -1\n\
                    \x20   MARK0001  'MARKER'              'INTEND'\n\
                    RHS\n\
                    \x20   RHS       LINK      0\n\
                    BOUNDS\n\
                    \x20LO BND       X         0\n\
                    \x20UP BND       X         2\n\
                    \x20LO BND       Y         0\n\
                    \x20UP BND       Y         2\n\
                    ENDATA\n";

const AFFINE_INFEASIBLE_MPS: &str = "NAME          AFFINE_INFEASIBLE\n\
                    ROWS\n\
                    \x20N  COST\n\
                    \x20E  R0\n\
                    \x20E  R1\n\
                    \x20E  FIXZ\n\
                    COLUMNS\n\
                    \x20   X         R0        1          R1        1\n\
                    \x20   Y         R0        1          R1        1\n\
                    \x20   MARK0000  'MARKER'              'INTORG'\n\
                    \x20   Z         FIXZ      1\n\
                    \x20   MARK0001  'MARKER'              'INTEND'\n\
                    RHS\n\
                    \x20   RHS       R0        0          R1        1\n\
                    \x20   RHS       FIXZ      0\n\
                    BOUNDS\n\
                    \x20FR BND       X\n\
                    \x20FR BND       Y\n\
                    \x20FX BND       Z         0\n\
                    ENDATA\n";

fn affine_optimal_fixture(
    with_inner_proof: bool,
) -> (crate::MpsProblem, AffineAggregationCertificate, Outcome) {
    let problem = crate::read_mps(AFFINE_OPTIMAL_MPS).expect("affine fixture parses");
    let (reduced, post) = crate::presolve::implied_free::aggregate_implied_free_equalities(
        &problem.model,
        None,
        None,
    )
    .expect("the exact equality aggregates");
    assert_eq!(reduced.num_cols(), 1);
    let reduced_point = vec![BigRational::zero()];
    let inner = with_inner_proof.then(|| {
        let coefficient = reduced.obj_coeff_exact_at(0, reduced.obj_coeff(Col(0)));
        let certificate = OptimalityCertificate {
            sense: Sense::Minimize,
            objective: vec![(0, coefficient.clone())],
            bound: BigRational::zero(),
            multipliers: vec![Multiplier {
                fact: FactRef::ColBound {
                    col: Col(0),
                    side: BoundSide::Lower,
                },
                coeff: coefficient,
            }],
        };
        certificate
            .verify(&reduced)
            .expect("reduced lower-bound proof verifies");
        certificate
    });
    let reduced_outcome = Outcome::Optimal {
        value: reduced.objective_value_at(&reduced_point),
        model_values: reduced_point,
        cert: inner,
    };
    let certificate = post
        .certificate_for_outcome(&reduced_outcome, &reduced, &problem.model, None, None)
        .expect("affine artifact is built");
    certificate
        .verify(&problem.model)
        .expect("producer artifact self-verifies");
    let AffineAggregationClaim::Optimal { value } = certificate.claim() else {
        panic!("objective fixture must claim optimality");
    };
    let source_values = certificate.source_primal().expect("source primal").to_vec();
    let outcome = Outcome::Optimal {
        value: value.clone(),
        model_values: source_values,
        cert: None,
    };
    (problem, certificate, outcome)
}

fn emit_affine_fixture(
    problem: &crate::MpsProblem,
    certificate: &AffineAggregationCertificate,
    outcome: &Outcome,
) -> String {
    emit_affine_fixture_with(problem, Some(certificate), outcome, None)
}

fn emit_affine_fixture_with(
    problem: &crate::MpsProblem,
    certificate: Option<&AffineAggregationCertificate>,
    outcome: &Outcome,
    max_bytes: Option<usize>,
) -> String {
    emit(
        &EmitCtx {
            model: &problem.model,
            model_text: AFFINE_OPTIMAL_MPS,
            col_names: &problem.col_names,
            obj_scale: &problem.obj_scale,
            provenance: "affine-codec-test",
            replay_claims: &[],
            affine_aggregation_certificate: certificate,
            block_angular_optimality_certificate: None,
            sat_relu_infeasibility_certificate: None,
            parity_infeasibility_certificate: None,
            network_design_infeasibility_certificate: None,
            network_design_optimality_certificate: None,
            single_machine_scheduling_optimality_certificate: None,
            single_row_dp_infeasibility_certificate: None,
            multi_row_bdd_infeasibility_certificate: None,
            open_domain_single_row_dp_infeasibility_certificate: None,
            open_domain_multi_row_bdd_infeasibility_certificate: None,
            open_domain_hybrid_pb_lp_infeasibility_certificate: None,
            open_domain_hybrid_integer_lift_infeasibility_certificate: None,
            hybrid_pb_lp_infeasibility_certificate: None,
            hybrid_integer_lift_infeasibility_certificate: None,
            max_bytes,
        },
        outcome,
    )
}

fn tiny() -> (Model, String) {
    // minimize x + y, x + y >= 3, 0 <= x,y <= 10, both integer.
    let text = "NAME          TINY\n\
                    ROWS\n\
                    \x20N  COST\n\
                    \x20G  R1\n\
                    COLUMNS\n\
                    \x20   MARKER                 'MARKER'                 'INTORG'\n\
                    \x20   X         COST      1.0        R1        1.0\n\
                    \x20   Y         COST      1.0        R1        1.0\n\
                    \x20   MARKER                 'MARKER'                 'INTEND'\n\
                    RHS\n\
                    \x20   RHS       R1        3.0\n\
                    BOUNDS\n\
                    \x20UP BND       X         10.0\n\
                    \x20UP BND       Y         10.0\n\
                    ENDATA\n";
    let p = crate::read_mps(text).expect("parses");
    (p.model, text.to_string())
}

mod affine;
mod affine_infeasible;
mod network;
mod replay;
mod sat_relu;
mod wire;

#[test]
fn sat_relu_rup_parser_enforces_caps_before_body_allocation() {
    sat_relu::sat_relu_rup_parser_enforces_caps_before_body_allocation();
}

#[test]
fn affine_optimality_wire_round_trips_and_checks_end_to_end() {
    affine::affine_optimality_wire_round_trips_and_checks_end_to_end();
}

#[test]
fn sat_relu_rup_emitter_refuses_noncanonical_internal_dags() {
    affine::sat_relu_rup_emitter_refuses_noncanonical_internal_dags();
}

#[test]
fn affine_farkas_wire_checks_in_the_rebuilt_reduced_frame() {
    affine_infeasible::affine_farkas_wire_checks_in_the_rebuilt_reduced_frame();
}

#[test]
fn affine_tree_wire_checks_in_the_rebuilt_reduced_frame() {
    affine_infeasible::affine_tree_wire_checks_in_the_rebuilt_reduced_frame();
}

#[test]
fn unsupported_affine_optimality_stays_partial_but_replays() {
    affine::unsupported_affine_optimality_stays_partial_but_replays();
}

#[test]
fn unsupported_affine_infeasibility_is_unverified_and_cannot_be_promoted() {
    affine::unsupported_affine_infeasibility_is_unverified_and_cannot_be_promoted();
}

#[test]
fn affine_codec_caps_are_atomic_and_legacy_v1_stays_readable() {
    affine::affine_codec_caps_are_atomic_and_legacy_v1_stays_readable();
}

#[test]
fn affine_parser_rejects_oversized_rationals_and_tree_depth_before_building() {
    affine::affine_parser_rejects_oversized_rationals_and_tree_depth_before_building();
}

#[test]
fn affine_wire_checker_rejects_every_tampered_boundary() {
    affine::affine_wire_checker_rejects_every_tampered_boundary();
}

#[test]
fn network_pattern_count_wire_round_trips_and_rejects_duplicate_variables() {
    network::network_pattern_count_wire_round_trips_and_rejects_duplicate_variables();
}

#[test]
fn emitted_pattern_count_optimum_parses_and_checks_end_to_end() {
    network::emitted_pattern_count_optimum_parses_and_checks_end_to_end();
}

#[test]
fn the_leaf_weight_estimate_is_the_bytes_the_writer_emits() {
    network::the_leaf_weight_estimate_is_the_bytes_the_writer_emits();
}

#[test]
fn rational_wire_form_round_trips_and_rejects_non_canonical() {
    wire::rational_wire_form_round_trips_and_rejects_non_canonical();
}

#[test]
fn bounded_rational_parser_preflights_decimal_size_and_checks_exact_bits() {
    wire::bounded_rational_parser_preflights_decimal_size_and_checks_exact_bits();
}

#[test]
fn canonical_digest_is_stable_and_shape_sensitive() {
    wire::canonical_digest_is_stable_and_shape_sensitive();
}

#[test]
fn sat_relu_emission_reuses_its_model_bound_digest() {
    wire::sat_relu_emission_reuses_its_model_bound_digest();
}

#[test]
fn block_angular_wire_round_trips_and_is_bounded() {
    wire::block_angular_wire_round_trips_and_is_bounded();
}

#[test]
fn exact_reduction_replay_ids_back_only_the_claim_they_proved() {
    replay::exact_pb_replay_ids_back_only_the_claim_they_proved();
    replay::exact_hybrid_replay_ids_back_only_the_claim_they_proved();
    replay::exact_projection_aliases_back_only_the_claim_they_proved();
}
