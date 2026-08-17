// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// The array clause schemas are quadratic in the step's own unfolded payload.
///
/// The payload is the one measured on
/// `QF_AX/storecomm/storecomm_t1_np_nf_ai_00030_005.cvc`, where the old cubic
/// estimate demanded 31,294,711,733 work (89x the work envelope) and
/// 457,121,101,264 bytes (340x the byte envelope) for a single step.
#[test]
fn array_clause_schema_charge_is_quadratic_not_cubic() {
    let terms = TermStore::new();
    let payload = PayloadStats {
        work: 14_134,
        bytes: 206_455,
        unfolded_work: 1_488,
        order_assignments: 0,
    };
    for kind in [
        TheoryLemmaKind::ArrayStorePermutation,
        TheoryLemmaKind::ArrayRowChain,
    ] {
        let step = ProofStep::TheoryLemma {
            theory: "AX".to_string(),
            clause: Vec::new(),
            farkas: None,
            kind,
            lia: None,
        };
        assert_eq!(
            select_semantic_charge_class(&step, &terms),
            SemanticChargeClass::ArrayClauseSchema,
            "{kind:?} must use the array schema cost model"
        );
        let (work, bytes) =
            semantic_validator_charge(&step, payload, SemanticChargeClass::ArrayClauseSchema)
                .expect("quadratic array charge fits usize");

        let square = payload.unfolded_work * payload.unfolded_work;
        assert_eq!(
            work,
            (square + payload.unfolded_work + payload.work) * ARRAY_SCHEMA_WORK_FACTOR
        );
        assert_eq!(
            bytes,
            payload.bytes * 4 + payload.unfolded_work * ARRAY_SCHEMA_ENTRY_BYTES
        );

        // The step that used to be unverifiable by construction now fits, and
        // the charge is still strictly above the payload it bounds.
        assert!(work < 350_000_000);
        assert!(bytes < 512 * 1024 * 1024);
        assert!(work > square);
        assert!(bytes > payload.bytes);
    }
}

/// CHARGE PARITY: the new cost models must still exhaust a budget when the work
/// they bound is genuinely large. Both the array schemas' quadratic and the
/// per-step trust-family clone keep growing with the payload, so a wide enough
/// lemma is still refused.
#[test]
fn rebounded_charges_still_exhaust_a_genuinely_wide_lemma() {
    let array_step = ProofStep::TheoryLemma {
        theory: "AX".to_string(),
        clause: Vec::new(),
        farkas: None,
        kind: TheoryLemmaKind::ArrayStorePermutation,
        lia: None,
    };
    // 40k unfolded nodes is 1.6e9 pairwise probes: real work, and it must
    // still be refused by a 350M work envelope.
    let wide = PayloadStats {
        work: 1,
        bytes: 1,
        unfolded_work: 40_000,
        order_assignments: 0,
    };
    let (work, _) =
        semantic_validator_charge(&array_step, wide, SemanticChargeClass::ArrayClauseSchema)
            .expect("charge fits usize");
    assert!(
        work > 350_000_000,
        "a genuinely quadratic array lemma must still exhaust the envelope: {work}"
    );

    // Byte parity: the array byte charge scales with the payload the validator
    // actually copies, so a 1 GiB clause payload still exceeds the 512 MiB
    // general byte reserve.
    let heavy = PayloadStats {
        work: 1,
        bytes: 1024 * 1024 * 1024,
        unfolded_work: 1,
        order_assignments: 0,
    };
    let (_, bytes) =
        semantic_validator_charge(&array_step, heavy, SemanticChargeClass::ArrayClauseSchema)
            .expect("charge fits usize");
    assert!(bytes > 512 * 1024 * 1024);

    // Overflow still fails closed rather than wrapping into a small charge.
    let overflow = PayloadStats {
        work: usize::MAX,
        bytes: usize::MAX,
        unfolded_work: usize::MAX,
        order_assignments: 0,
    };
    assert_eq!(
        semantic_validator_charge(
            &array_step,
            overflow,
            SemanticChargeClass::ArrayClauseSchema
        ),
        Err(ProofCheckError::ResourceLimit)
    );
}

/// STEP PARITY: no cross-step amortization. N array lemmas of the same shape
/// cost exactly N times one lemma, so a budgeted run cannot be talked past its
/// envelope by repeating a step.
#[test]
fn rebounded_charges_are_levied_once_per_step() {
    let payload = PayloadStats {
        work: 14_134,
        bytes: 206_455,
        unfolded_work: 1_488,
        order_assignments: 0,
    };
    let step = ProofStep::TheoryLemma {
        theory: "AX".to_string(),
        clause: Vec::new(),
        farkas: None,
        kind: TheoryLemmaKind::ArrayStorePermutation,
        lia: None,
    };
    let one = semantic_validator_charge(&step, payload, SemanticChargeClass::ArrayClauseSchema)
        .expect("charge fits usize");
    let mut total = (0_usize, 0_usize);
    for _ in 0..5 {
        let each =
            semantic_validator_charge(&step, payload, SemanticChargeClass::ArrayClauseSchema)
                .expect("charge fits usize");
        total = (total.0 + each.0, total.1 + each.1);
    }
    assert_eq!(total, (one.0 * 5, one.1 * 5));
}

/// BOTH array schemas now meter their ACTUAL validation work inside their
/// validators (`validate_array_row_chain` / `validate_array_store_permutation`)
/// through the strict-check progress callback, so `strict_step_charge` levies NO
/// up-front `ArrayClauseSchema` quadratic precharge for either. The former
/// precharge (`~8 * unfolded_work^2`) is quadratic in the unfolded payload —
/// hence quartic in the store-chain length for the store-commutativity clause,
/// whose `O(P^2)` index-pair literals make `unfolded_work` itself `Θ(P^2)` — and
/// withheld correctly-decided `storecomm` UNSATs. The fail-closed guarantee now
/// lives in the validators; see `charge_store_permutation_validation`'s
/// refusing-meter test in the array-axiom suite.
#[test]
fn strict_step_charge_meters_both_array_schemas_without_a_quadratic_precharge() {
    let terms = TermStore::new();
    let derived: Vec<Option<Vec<TermId>>> = Vec::new();
    // A wide payload whose OLD quadratic precharge (8 * unfolded_work^2) was well
    // above the 350M strict-check work envelope; neither schema now precharges it.
    let wide = PayloadStats {
        work: 1,
        bytes: 1,
        unfolded_work: 40_000,
        order_assignments: 0,
    };
    let make = |kind| ProofStep::TheoryLemma {
        theory: "AX".to_string(),
        clause: Vec::new(),
        farkas: None,
        kind,
        lia: None,
    };

    for kind in [
        TheoryLemmaKind::ArrayStorePermutation,
        TheoryLemmaKind::ArrayRowChain,
    ] {
        let step = make(kind);
        let (work, bytes) = strict_step_charge(&terms, &step, &derived, 0, wide)
            .expect("array-schema charge fits usize");
        // Only the per-step base clause charge remains; the quadratic semantic
        // precharge is gone (metered in the validator instead).
        assert!(
            work < 1_000,
            "{kind:?} must take no up-front quadratic precharge: {work}"
        );
        assert!(
            bytes < 1_000,
            "{kind:?} up-front bytes must be negligible: {bytes}"
        );
    }
}

#[test]
fn repeated_generic_lemmas_are_charged_against_one_progress_envelope() {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(0.into());
    let x = terms.mk_var("generic_meter_x", Sort::Int);
    let equality = terms.mk_eq(x, zero);
    let not_equality = terms.mk_not_raw(equality);
    let generic = ProofStep::TheoryLemma {
        theory: "NIA".to_string(),
        clause: vec![not_equality, equality],
        farkas: None,
        kind: TheoryLemmaKind::Generic,
        lia: None,
    };
    let one = Proof::from_steps(vec![generic.clone()]);
    let mut one_lemma_monomial_charges = 0_usize;
    authenticate_premise_clauses_strict_with_context_and_progress(
        &one,
        &terms,
        None,
        None,
        &[],
        &mut |work, bytes| {
            if work == crate::checker::GENERIC_MONOMIAL_WORK
                && bytes == crate::checker::GENERIC_MONOMIAL_BYTES
            {
                one_lemma_monomial_charges += 1;
            }
            true
        },
    )
    .expect("one small equality-span lemma should fit the dynamic envelope");
    assert!(one_lemma_monomial_charges > 0);

    let proof = Proof::from_steps(vec![generic.clone(), generic]);
    let mut generic_private_charges = 0_usize;
    let error = authenticate_premise_clauses_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        &[],
        &mut |work, bytes| {
            if work == crate::checker::GENERIC_MONOMIAL_WORK
                && bytes == crate::checker::GENERIC_MONOMIAL_BYTES
            {
                generic_private_charges += 1;
                return generic_private_charges <= one_lemma_monomial_charges;
            }
            true
        },
    )
    .expect_err("the second private validator must debit the same proof-wide envelope");

    assert_eq!(error, ProofCheckError::ResourceLimit);
    assert_eq!(generic_private_charges, one_lemma_monomial_charges + 1);
}

#[test]
fn generic_linear_ideal_polls_cancellation_inside_private_work() {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(0.into());
    let x = terms.mk_var("generic_cancel_x", Sort::Int);
    let equality = terms.mk_eq(x, zero);
    let not_equality = terms.mk_not_raw(equality);
    let proof = Proof::from_steps(vec![ProofStep::TheoryLemma {
        theory: "NIA".to_string(),
        clause: vec![not_equality, equality],
        farkas: None,
        kind: TheoryLemmaKind::Generic,
        lia: None,
    }]);
    let mut entered_private_work = false;
    let mut refused_private_poll = false;
    let error = authenticate_premise_clauses_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        &[],
        &mut |work, bytes| {
            if work == crate::checker::GENERIC_MONOMIAL_WORK
                && bytes == crate::checker::GENERIC_MONOMIAL_BYTES
            {
                entered_private_work = true;
            } else if entered_private_work && (work, bytes) == (0, 0) {
                refused_private_poll = true;
                return false;
            }
            true
        },
    )
    .expect_err("private equality-span work must observe caller cancellation");

    assert_eq!(error, ProofCheckError::ResourceLimit);
    assert!(entered_private_work);
    assert!(refused_private_poll);
}

#[test]
fn generic_linear_ideal_scratch_refusal_is_typed_resource_limit() {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(0.into());
    let x = terms.mk_var("generic_scratch_x", Sort::Int);
    let x_plus_x = terms.mk_add(vec![x, x]);
    let equality = terms.mk_eq(x_plus_x, zero);
    let not_equality = terms.mk_not_raw(equality);
    let proof = Proof::from_steps(vec![ProofStep::TheoryLemma {
        theory: "NIA".to_string(),
        clause: vec![not_equality, equality],
        farkas: None,
        kind: TheoryLemmaKind::Generic,
        lia: None,
    }]);
    // `1 + 1` is the first occupied-coefficient operation in this fixture.
    let scratch = crate::checker::generic_rational_scratch_bytes(5)
        .expect("tiny rational scratch bound fits usize");
    let mut refused = false;
    let error = authenticate_premise_clauses_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        &[],
        &mut |work, bytes| {
            if (work, bytes) == (0, scratch) {
                refused = true;
                return false;
            }
            true
        },
    )
    .expect_err("scratch refusal must escape Generic fallback as ResourceLimit");

    assert_eq!(error, ProofCheckError::ResourceLimit);
    assert!(refused, "fixture must reach rational scratch precharge");
}

#[test]
fn test_datatype_registry_meter_covers_active_declaration_backed_kinds() {
    let payload = PayloadStats {
        work: 11,
        bytes: 128,
        unfolded_work: 7,
        order_assignments: 0,
    };
    let datatype_registry = RegistryPayloadStats {
        work: 37,
        bytes: 512,
    };
    let selector_registry = RegistryPayloadStats {
        work: 19,
        bytes: 256,
    };

    for kind in [
        TheoryLemmaKind::DatatypeDistinct,
        TheoryLemmaKind::DatatypeSelectorProject,
        TheoryLemmaKind::DatatypeTesterEval,
        TheoryLemmaKind::DatatypeExhaustive,
        TheoryLemmaKind::DatatypeConstructorReconstruct,
    ] {
        let step = ProofStep::TheoryLemma {
            theory: "DT".to_string(),
            clause: Vec::new(),
            farkas: None,
            kind,
            lia: None,
        };
        let (work, bytes) =
            datatype_registry_charge(&step, payload, datatype_registry, selector_registry)
                .expect("small registry products should fit usize");
        assert_eq!(work, (37 + 19) * payload.work);
        assert_eq!(bytes, payload.bytes * 8);
    }
}

#[test]
fn test_string_ground_meter_covers_decoding_clones_and_tables() {
    let step = ProofStep::TheoryLemma {
        theory: "Strings".to_string(),
        clause: Vec::new(),
        farkas: None,
        kind: TheoryLemmaKind::StringGroundEval,
        lia: None,
    };
    let payload = PayloadStats {
        work: 23,
        bytes: 4096,
        unfolded_work: 23,
        order_assignments: 0,
    };
    let (work, bytes) = semantic_validator_charge(&step, payload, SemanticChargeClass::General)
        .expect("small string payload products should fit usize");
    let table_overhead = crate::checker::STRING_EVAL_WORK_LIMIT * 96;
    let char_allocation = crate::checker::STRING_CHAR_ALLOCATION_LIMIT * size_of::<char>();
    let numeric_allocation = crate::checker::STRING_NUMERIC_BIT_ALLOCATION_LIMIT.div_ceil(8);
    let private_work = crate::checker::STRING_EVAL_WORK_LIMIT
        + crate::checker::STRING_CHAR_ALLOCATION_LIMIT
        + crate::checker::STRING_NUMERIC_WORK_LIMIT;

    assert!(work >= private_work);
    assert!(bytes >= table_overhead + char_allocation + numeric_allocation + payload.bytes * 16);
    assert!(bytes >= table_overhead + char_allocation + numeric_allocation + payload.bytes * 12);
}

#[test]
fn test_order_ite_meter_uses_complete_preorder_enumeration_factor() {
    let step = ProofStep::TheoryLemma {
        theory: "Order".to_string(),
        clause: Vec::new(),
        farkas: None,
        kind: TheoryLemmaKind::OrderIteTautology,
        lia: None,
    };
    let payload = PayloadStats {
        work: 17,
        bytes: 31,
        unfolded_work: 13,
        order_assignments: crate::checker::order_ite_assignment_count(3),
    };
    let base_work =
        (payload.work * payload.unfolded_work).max(payload.unfolded_work * payload.unfolded_work);
    let (work, bytes) = semantic_validator_charge(&step, payload, SemanticChargeClass::General)
        .expect("small order-ITE products should fit usize");

    let assignments = crate::checker::order_ite_assignment_count(3);
    assert_eq!(assignments, 27);
    assert_eq!(work, base_work * assignments);
    assert_eq!(bytes, payload.bytes * assignments);
}

#[test]
fn test_ext_diff_meter_multiplies_reachable_payload_per_binding() {
    let mut terms = TermStore::new();
    let array_sort = Sort::Array(Box::new(ay_core::ArraySort::new(Sort::Int, Sort::Bool)));
    let witness = terms.mk_var("metered_ext_witness", Sort::Int);
    let left = terms.mk_var("metered_ext_left", array_sort.clone());
    let right = terms.mk_var("metered_ext_right", array_sort);
    let proof = Proof::from_steps(vec![ProofStep::Step {
        rule: AletheRule::ArrayExtDiffIntro,
        clause: Vec::new(),
        premises: Vec::new(),
        args: vec![witness, left, right],
    }]);
    let payload = PayloadStats {
        work: 100,
        bytes: 200,
        unfolded_work: 100,
        order_assignments: 0,
    };

    let (work, bytes) = ext_diff_registry_charge(&proof, &terms, payload)
        .expect("small checked products should fit usize");
    assert!(work > 2 * payload.work);
    assert!(bytes >= 2 * payload.bytes);
}
