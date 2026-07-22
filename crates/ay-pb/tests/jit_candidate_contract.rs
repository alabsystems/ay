// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_pb::{
    extract_first_jit_candidate, profile_jit_candidate_telemetry, profile_jit_kernel_shapes,
    PbConstraint, PbInstance, PbJitBackend, PbJitExtraction, PbJitRejection, PbKernelKind, PbLit,
    PbObjective, PbRel, PbTerm,
};

fn lit(var: u32) -> PbLit {
    PbLit {
        var,
        negated: false,
    }
}

fn term(coeff: i128, var: u32) -> PbTerm {
    PbTerm {
        coeff,
        lits: vec![lit(var)],
    }
}

fn product_term(coeff: i128, lhs: u32, rhs: u32) -> PbTerm {
    PbTerm {
        coeff,
        lits: vec![lit(lhs), lit(rhs)],
    }
}

fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
    PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs,
    }
}

fn instance(constraints: Vec<PbConstraint>) -> PbInstance {
    PbInstance {
        num_vars: 16,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: None,
    }
}

fn pbo_instance(constraints: Vec<PbConstraint>, objective_terms: Vec<PbTerm>) -> PbInstance {
    PbInstance {
        objective: Some(PbObjective {
            terms: objective_terms,
        }),
        ..instance(constraints)
    }
}

#[test]
fn accepts_repeated_unit_cardinality_shape_as_metadata_only_contract() {
    let input = pbo_instance(
        vec![
            ge(vec![term(1, 1), term(1, 2), term(1, 3)], 2),
            ge(vec![term(1, 4), term(1, 5), term(1, 6)], 2),
            ge(vec![term(1, 7), term(1, 8), term(1, 9)], 2),
            ge(vec![term(1, 10), term(1, 11), term(1, 12)], 2),
            ge(vec![term(1, 13), term(1, 14)], 1),
        ],
        vec![term(5, 1), term(-1, 2), product_term(2, 3, 4)],
    );

    let profile = profile_jit_kernel_shapes(&input).expect("profile should not overflow");
    let objective_profile = profile
        .objective_bound_update
        .expect("PBO objective profile should be present");
    assert_eq!(objective_profile.terms, 3);
    assert_eq!(objective_profile.single_lit_terms, 2);
    assert_eq!(objective_profile.unit_weight_terms, 1);
    assert_eq!(objective_profile.max_abs_coeff, 5);
    assert_eq!(objective_profile.total_abs_weight, 8);

    let cardinality_shape = profile
        .shapes
        .iter()
        .find(|shape| shape.kind == PbKernelKind::UnitCardinalityPropagation)
        .expect("unit-cardinality shape should be profiled");
    assert_eq!(cardinality_shape.terms, 3);
    assert_eq!(cardinality_shape.degree, 2);
    assert_eq!(cardinality_shape.coefficients, vec![1, 1, 1]);
    assert_eq!(cardinality_shape.repetitions, 4);
    assert_eq!(cardinality_shape.constraint_indices, vec![0, 1, 2, 3]);

    let extraction = extract_first_jit_candidate(&input);
    let PbJitExtraction::Candidate(candidate) = extraction else {
        panic!("expected accepted candidate, got {extraction:?}");
    };

    assert_eq!(candidate.contract_version, 1);
    assert_eq!(candidate.backend, PbJitBackend::ExternalCodegenBackend);
    assert_eq!(candidate.kind, PbKernelKind::UnitCardinalityPropagation);
    assert_eq!(candidate.terms, 3);
    assert_eq!(candidate.degree, 2);
    assert_eq!(candidate.repetitions, 4);
    assert_eq!(candidate.constraint_indices, vec![0, 1, 2, 3]);
    assert!(candidate.exact_i64_arithmetic);
    assert!(candidate.interpreter_fallback_required);
    assert_eq!(candidate.generated_code_execution_allowed, false);
    assert!(candidate.external_codegen_backend_backend_required);

    let telemetry = profile_jit_candidate_telemetry(&input);
    assert_eq!(telemetry.profile_attempts, 1);
    assert_eq!(telemetry.profiled_candidates, 2);
    assert_eq!(telemetry.selected_candidates, 1);
    assert_eq!(telemetry.rejected_candidates, 0);
    assert_eq!(telemetry.rejection_reason, None);
    assert_eq!(
        telemetry.kernel_kind,
        Some(PbKernelKind::UnitCardinalityPropagation)
    );
    assert_eq!(telemetry.kernel_terms, 3);
    assert_eq!(telemetry.kernel_repetitions, 4);
    assert_eq!(telemetry.pb_pbo_candidate_applications, 4);
    assert_eq!(telemetry.pb_native_code_helper_applications, 0);
    assert!(telemetry.objective_profile.is_some());
}

#[test]
fn accepts_repeated_clause_shape_as_metadata_only_contract() {
    let input = instance(vec![
        ge(vec![term(1, 1), term(1, 2), term(1, 3)], 1),
        ge(vec![term(1, 4), term(1, 5), term(1, 6)], 1),
        ge(vec![term(1, 7), term(1, 8), term(1, 9)], 1),
        ge(vec![term(1, 10), term(1, 11), term(1, 12)], 1),
        ge(vec![term(1, 13), term(1, 14), term(1, 15)], 2),
    ]);

    let profile = profile_jit_kernel_shapes(&input).expect("profile should not overflow");
    let clause_shape = profile
        .shapes
        .iter()
        .find(|shape| shape.kind == PbKernelKind::ClausePropagation)
        .expect("clause shape should be profiled");
    assert_eq!(clause_shape.terms, 3);
    assert_eq!(clause_shape.degree, 1);
    assert_eq!(clause_shape.coefficients, vec![1, 1, 1]);
    assert_eq!(clause_shape.repetitions, 4);
    assert_eq!(clause_shape.constraint_indices, vec![0, 1, 2, 3]);

    let extraction = extract_first_jit_candidate(&input);
    let PbJitExtraction::Candidate(candidate) = extraction else {
        panic!("expected accepted clause candidate, got {extraction:?}");
    };

    assert_eq!(candidate.contract_version, 1);
    assert_eq!(candidate.backend, PbJitBackend::ExternalCodegenBackend);
    assert_eq!(candidate.kind, PbKernelKind::ClausePropagation);
    assert_eq!(candidate.terms, 3);
    assert_eq!(candidate.degree, 1);
    assert_eq!(candidate.coefficients, vec![1, 1, 1]);
    assert_eq!(candidate.repetitions, 4);
    assert_eq!(candidate.constraint_indices, vec![0, 1, 2, 3]);
    assert!(candidate.exact_i64_arithmetic);
    assert!(candidate.interpreter_fallback_required);
    assert!(!candidate.generated_code_execution_allowed);
    assert!(candidate.external_codegen_backend_backend_required);

    let telemetry = profile_jit_candidate_telemetry(&input);
    assert_eq!(telemetry.profile_attempts, 1);
    assert_eq!(telemetry.profiled_candidates, 2);
    assert_eq!(telemetry.selected_candidates, 1);
    assert_eq!(telemetry.rejected_candidates, 0);
    assert_eq!(telemetry.rejection_reason, None);
    assert_eq!(telemetry.kernel_kind, Some(PbKernelKind::ClausePropagation));
    assert_eq!(telemetry.kernel_terms, 3);
    assert_eq!(telemetry.kernel_repetitions, 4);
    assert_eq!(telemetry.pb_pbo_candidate_applications, 4);
    assert_eq!(telemetry.pb_native_code_helper_applications, 0);
    assert!(telemetry.objective_profile.is_none());
}

#[test]
fn rejects_when_only_weighted_or_nonlinear_shapes_repeat() {
    let input = instance(vec![
        ge(vec![term(2, 1), term(1, 2), term(1, 3)], 2),
        ge(vec![term(2, 4), term(1, 5), term(1, 6)], 2),
        ge(vec![term(2, 7), term(1, 8), term(1, 9)], 2),
        ge(vec![term(2, 10), term(1, 11), term(1, 12)], 2),
        ge(vec![product_term(1, 13, 14), term(1, 15)], 1),
    ]);

    let profile = profile_jit_kernel_shapes(&input).expect("profile should not overflow");
    assert_eq!(profile.nonlinear_constraints, 1);
    assert!(profile
        .shapes
        .iter()
        .any(|shape| shape.kind == PbKernelKind::WeightedPropagation && shape.repetitions == 4));

    assert_eq!(
        extract_first_jit_candidate(&input),
        PbJitExtraction::Rejected(PbJitRejection::NoRepeatedSafeShape)
    );

    let telemetry = profile_jit_candidate_telemetry(&input);
    assert_eq!(telemetry.selected_candidates, 0);
    assert_eq!(telemetry.rejected_candidates, 1);
    assert_eq!(
        telemetry.rejection_reason,
        Some(PbJitRejection::NoRepeatedSafeShape)
    );
    assert_eq!(telemetry.kernel_kind, None);
    assert_eq!(telemetry.pb_pbo_candidate_applications, 0);
    assert_eq!(telemetry.pb_native_code_helper_applications, 0);
}

#[test]
fn normalization_overflow_fails_closed() {
    // The negative single-lit term is normalized via `degree - coeff`, i.e.
    // `i128::MAX - (-1) = i128::MAX + 1`, which overflows. With the i64->i128
    // widening the old `i64::MAX` rhs is now comfortably in range and would
    // succeed, so the fail-closed boundary moves to the i128 edge.
    let input = instance(vec![ge(vec![term(-1, 1)], i128::MAX)]);

    assert_eq!(
        profile_jit_kernel_shapes(&input),
        Err(PbJitRejection::ArithmeticOverflow)
    );
    assert_eq!(
        extract_first_jit_candidate(&input),
        PbJitExtraction::Rejected(PbJitRejection::ArithmeticOverflow)
    );

    let telemetry = profile_jit_candidate_telemetry(&input);
    assert_eq!(telemetry.profile_attempts, 1);
    assert_eq!(telemetry.profiled_candidates, 0);
    assert_eq!(telemetry.selected_candidates, 0);
    assert_eq!(telemetry.rejected_candidates, 1);
    assert_eq!(
        telemetry.rejection_reason,
        Some(PbJitRejection::ArithmeticOverflow)
    );
    assert_eq!(telemetry.pb_pbo_candidate_applications, 0);
    assert_eq!(telemetry.pb_native_code_helper_applications, 0);
}

#[test]
fn literal_out_of_range_fails_closed() {
    let input = instance(vec![ge(
        vec![PbTerm {
            coeff: 1,
            lits: vec![lit(i32::MAX as u32 + 1)],
        }],
        1,
    )]);

    assert_eq!(
        profile_jit_kernel_shapes(&input),
        Err(PbJitRejection::LiteralOutOfRange)
    );
    assert_eq!(
        extract_first_jit_candidate(&input),
        PbJitExtraction::Rejected(PbJitRejection::LiteralOutOfRange)
    );

    let telemetry = profile_jit_candidate_telemetry(&input);
    assert_eq!(
        telemetry.rejection_reason,
        Some(PbJitRejection::LiteralOutOfRange)
    );
    assert_eq!(telemetry.selected_candidates, 0);
    assert_eq!(telemetry.rejected_candidates, 1);
    assert_eq!(telemetry.pb_native_code_helper_applications, 0);
}

#[test]
fn native_helper_applications_stay_zero_until_solve_path_dispatch() {
    let mut constraints = Vec::new();
    for offset in 0..20 {
        let base = 1 + offset * 3;
        constraints.push(ge(
            vec![term(1, base), term(1, base + 1), term(1, base + 2)],
            2,
        ));
    }
    let input = PbInstance {
        num_vars: 60,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: None,
    };

    let telemetry = profile_jit_candidate_telemetry(&input);
    assert_eq!(telemetry.pb_pbo_candidate_applications, 20);
    assert_eq!(
        telemetry.pb_native_code_helper_applications, 0,
        "startup/profile candidates must not count as PB solve-path external code generation native-helper applications"
    );
}
