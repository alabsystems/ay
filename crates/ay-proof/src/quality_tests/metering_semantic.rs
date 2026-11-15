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
        fp_assignments: 0,
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
        fp_assignments: 0,
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
        fp_assignments: 0,
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
        fp_assignments: 0,
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
        fp_assignments: 0,
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
        fp_assignments: 0,
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
        fp_assignments: 0,
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
        fp_assignments: 0,
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
        fp_assignments: 0,
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
        fp_assignments: 0,
        order_assignments: 0,
    };

    let (work, bytes) = ext_diff_registry_charge(&proof, &terms, payload, &mut |_, _| true)
        .expect("small checked products should fit usize");
    assert!(work > 2 * payload.work);
    assert!(bytes >= 2 * payload.bytes);
}

/// The read-over-write and extensionality classes charge a constant number of
/// slot reads per reachable-DAG node and are capped by the `General` product
/// they replace, so they are tightenings at every payload.
///
/// The payloads are the ones `--probe-strict-check` reported on
/// `QF_AX/swap/swap_t3_np_nf_ai_00008_005` (unbudgeted, explicit proof
/// demand): the widest `ArraySelectStore` lemma and one `ArrayExtensionality`
/// lemma. Under the `General` product those two steps alone precharged
/// 22_335_076 and 89_151_364 work; 268 such lemmas summed 2.68G against a
/// 350M envelope and withheld a complete, trust-free refutation.
#[test]
fn array_row_and_extensionality_shape_charges_are_linear_and_capped() {
    let terms = TermStore::new();
    let lemma = |kind| ProofStep::TheoryLemma {
        theory: "AX".to_string(),
        clause: Vec::new(),
        farkas: None,
        kind,
        lia: None,
    };

    let row_payload = PayloadStats {
        work: 1_278,
        bytes: 15_553,
        unfolded_work: 4_726,
        fp_assignments: 0,
        order_assignments: 0,
    };
    for index_eq in [true, false] {
        let step = lemma(TheoryLemmaKind::ArraySelectStore { index_eq });
        assert_eq!(
            select_semantic_charge_class(&step, &terms),
            SemanticChargeClass::ArrayRowShape
        );
        let (work, bytes) =
            semantic_validator_charge(&step, row_payload, SemanticChargeClass::ArrayRowShape)
                .expect("linear charge fits usize");
        assert_eq!(
            work,
            row_payload.work * semantic_charge::ARRAY_ROW_SHAPE_WORK_FACTOR
                + semantic_charge::ARRAY_ROW_SHAPE_WORK_FACTOR
        );
        assert_eq!(bytes, row_payload.bytes);
        // The product this replaces is the probe's reported 22_335_076.
        assert_eq!(
            semantic_charge::replaced_general_product(row_payload, 1),
            22_335_076
        );
        assert!(work < 100_000, "{work}");
    }

    let ext_payload = PayloadStats {
        work: 2_146,
        bytes: 25_777,
        unfolded_work: 9_442,
        fp_assignments: 0,
        order_assignments: 0,
    };
    let step = lemma(TheoryLemmaKind::ArrayExtensionality);
    assert_eq!(
        select_semantic_charge_class(&step, &terms),
        SemanticChargeClass::ArrayExtensionalityShape
    );
    let (work, bytes) = semantic_validator_charge(
        &step,
        ext_payload,
        SemanticChargeClass::ArrayExtensionalityShape,
    )
    .expect("linear charge fits usize");
    assert_eq!(
        work,
        ext_payload.work * semantic_charge::ARRAY_EXTENSIONALITY_SHAPE_WORK_FACTOR
            + semantic_charge::ARRAY_EXTENSIONALITY_SHAPE_WORK_FACTOR
    );
    // Bytes: the binding vector on top of the payload, capped by the private
    // model's `2 * bytes` it replaces.
    assert_eq!(
        bytes,
        ext_payload.bytes + ext_payload.work * 3 * size_of::<TermId>()
    );
    assert!(bytes <= ext_payload.bytes * 2, "{bytes}");
    assert_eq!(
        semantic_charge::replaced_general_product(ext_payload, 1),
        89_151_364
    );
    assert!(work < 200_000, "{work}");

    // The cap: where the `General` product is already below the linear model
    // the class charges the product, never more.
    let tiny = PayloadStats {
        work: 1,
        bytes: 8,
        unfolded_work: 1,
        fp_assignments: 0,
        order_assignments: 0,
    };
    let (work, _) = semantic_validator_charge(
        &lemma(TheoryLemmaKind::ArraySelectStore { index_eq: true }),
        tiny,
        SemanticChargeClass::ArrayRowShape,
    )
    .expect("tiny charge fits usize");
    assert_eq!(work, semantic_charge::replaced_general_product(tiny, 1));
}

/// Mutation differential for the `ArrayRowShape` class, end to end through
/// the metered strict walk.
///
/// A twelve-level swap chain cites the previous array twice per level, so the
/// literal's TREE unfolds about 2^12-fold while its DAG grows by three nodes
/// per level — the shape of every `QF_AX/swap` file. Under the `General`
/// product the ROW1 lemma's precharge alone exceeds a 1M envelope by two
/// orders of magnitude (asserted below from the same payload meter the walk
/// uses), so on the previous charge model this walk is refused with
/// `ResourceLimit`. With the class the whole refutation checks inside 1M —
/// and the SAME envelope still refuses the forged twin (the read-back equated
/// with an unrelated `w`) with a typed `InvalidTheoryLemma`, i.e. the
/// validator ran and the meter did not decide the verdict.
#[test]
fn shared_store_chain_row_lemma_checks_under_a_tight_envelope_and_a_forgery_is_refused() {
    use ay_core::{ArraySort, Proof, ProofId};

    const ENVELOPE: usize = 1_000_000;

    let mut terms = TermStore::new();
    let array_sort = Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)));
    let mut chain = terms.mk_var("a", array_sort.clone());
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    for _ in 0..12 {
        let read = terms.mk_app(Symbol::named("select"), vec![chain, j], Sort::Int);
        chain = terms.mk_app(
            Symbol::named("store"),
            vec![chain, i, read],
            array_sort.clone(),
        );
    }
    let v = terms.mk_var("v", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let stored = terms.mk_app(Symbol::named("store"), vec![chain, i, v], array_sort);
    let read_back = terms.mk_app(Symbol::named("select"), vec![stored, i], Sort::Int);
    let row1 = terms.mk_app(Symbol::named("="), vec![read_back, v], Sort::Bool);
    let forged = terms.mk_app(Symbol::named("="), vec![read_back, w], Sort::Bool);

    let refutation = |terms: &mut TermStore, lemma: TermId| -> Proof {
        let negated = terms.mk_not_raw(lemma);
        let mut proof = Proof::new();
        proof.steps.push(ProofStep::Assume(negated));
        proof.steps.push(ProofStep::TheoryLemma {
            theory: "arrays".to_string(),
            clause: vec![lemma],
            farkas: None,
            kind: TheoryLemmaKind::ArraySelectStore { index_eq: true },
            lia: None,
        });
        proof.steps.push(ProofStep::Resolution {
            clause: Vec::new(),
            pivot: lemma,
            clause1: ProofId(0),
            clause2: ProofId(1),
        });
        proof
    };
    let run = |proof: &Proof, terms: &TermStore, budget: usize| {
        let mut spent = 0usize;
        let outcome = check_proof_strict_with_context_and_progress(
            proof,
            terms,
            None,
            None,
            None,
            &mut |work, _bytes| {
                spent += work;
                spent <= budget
            },
        );
        (outcome.map(|_| ()), spent)
    };

    let valid = refutation(&mut terms, row1);

    // The replaced product for the lemma step, from the walk's own payload
    // meter: far above the envelope the whole walk fits in below.
    let negated_row1 = terms.mk_not_raw(row1);
    let derived: Vec<Option<Vec<TermId>>> = vec![Some(vec![negated_row1])];
    let payload = meter_step_term_payload(
        &valid.steps[1],
        &terms,
        &derived,
        &mut TermCostMemo::default(),
        &mut |_, _| true,
    )
    .expect("payload meter fits usize");
    assert!(
        semantic_charge::replaced_general_product(payload, 1) > 100 * ENVELOPE,
        "the fixture must be one the General product refuses: {payload:?}"
    );

    let (outcome, spent) = run(&valid, &terms, usize::MAX);
    assert!(
        outcome.is_ok(),
        "the ROW1 refutation must check: {outcome:?}"
    );
    assert!(
        spent < ENVELOPE,
        "whole walk must fit the envelope: {spent}"
    );
    let (outcome, _) = run(&valid, &terms, ENVELOPE);
    assert!(outcome.is_ok(), "under the envelope: {outcome:?}");

    // Mutation: same shape, same envelope, wrong stored value.
    let forged_proof = refutation(&mut terms, forged);
    let (outcome, _) = run(&forged_proof, &terms, ENVELOPE);
    assert!(
        matches!(outcome, Err(ProofCheckError::InvalidTheoryLemma { .. })),
        "the forged ROW1 lemma must be refused by the validator, not the meter: {outcome:?}"
    );
}
