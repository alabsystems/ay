// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact-shape and fail-closed tests for the bounded shift-monotonicity
//! Alethe lowering.
//!
//! These tests live in a `*_tests.rs` file rather than inline in
//! `shift_monotonicity.rs` on purpose. `tests/wire_rule_coverage.rs` scans the
//! printer modules for every `:rule` name AY can emit and excludes test code by
//! FILENAME. An inline `#[cfg(test)]` module puts assertion strings such as
//! `assert!(!output.contains(":rule trust"))` into that scan, which registers a
//! rule AY deliberately never emits (#8821) as if the printer produced it.

use super::*;
use crate::{try_export_alethe_with_problem_scope_overrides_and_budget, AlethePrintError};
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, ProofStep, TermStore, TheoryLemmaKind};
use num_bigint::BigInt;

struct RawShiftStep {
    terms: TermStore,
    step: ProofStep,
    literal: TermId,
    root: TermId,
    positive: TermId,
    non_strict: TermId,
    shifted: TermId,
}

fn raw_shift_step(width: u32, shift: u32) -> RawShiftStep {
    let mut terms = TermStore::new();
    let sort = Sort::bitvec(width);
    let value = terms.mk_var("x", sort.clone());
    let zero = terms.mk_bitvec(BigInt::from(0), width);
    let high_zero = terms.mk_bitvec(BigInt::from(0), shift);
    // Build the post-normalization surface RAW so invalid boundary shapes
    // (shift == width) can be tested without asking a simplifying builder
    // to construct an invalid extract.
    let extract_width = width.saturating_sub(shift).max(1);
    let extract = terms.mk_app(
        Symbol::indexed("extract", vec![width.saturating_sub(1), shift]),
        vec![value],
        Sort::bitvec(extract_width),
    );
    let shifted = terms.mk_app(
        Symbol::named("concat"),
        vec![high_zero, extract],
        sort.clone(),
    );
    let positive = terms.mk_app(Symbol::named("bvult"), vec![zero, value], Sort::Bool);
    let non_strict = terms.mk_app(Symbol::named("bvule"), vec![value, shifted], Sort::Bool);
    let root = terms.mk_app(Symbol::named("and"), vec![positive, non_strict], Sort::Bool);
    let literal = terms.mk_not_raw(root);
    let step = ProofStep::TheoryLemma {
        theory: "bv".to_string(),
        clause: vec![literal],
        farkas: None,
        kind: TheoryLemmaKind::BvBitBlast,
        lia: None,
    };
    RawShiftStep {
        terms,
        step,
        literal,
        root,
        positive,
        non_strict,
        shifted,
    }
}

fn assert_honest_hole(case: &RawShiftStep) {
    let output = AlethePrinter::new(&case.terms)
        .format_step(&case.step, ProofId(3))
        .expect("unsupported bit-blast shapes retain the diagnostic artifact");
    assert!(output.contains(":rule hole"), "{output}");
    assert!(!output.contains(":rule drat"), "{output}");
    assert!(!output.contains(":rule trust"), "{output}");
}

#[test]
fn exact_bounded_shift_shape_exports_checked_carcara_rules() {
    for width in 2_u32..=8 {
        for shift in 1..width {
            let case = raw_shift_step(width, shift);
            let output = AlethePrinter::new(&case.terms)
                .format_step(&case.step, ProofId(7))
                .expect("ratified bounded shape renders");
            for rule in [
                "bitblast_const",
                "bitblast_extract",
                "bitblast_concat",
                "bitblast_ult",
                "pbblast_bvule",
                "pbblast_bvult",
                "drat",
                "subproof",
            ] {
                assert!(output.contains(&format!(":rule {rule}")), "{output}");
            }
            assert!(!output.contains(":rule hole"), "{output}");
            assert!(!output.contains(":rule trust"), "{output}");
        }
    }
}

#[test]
fn shift_shape_declines_outside_exact_width_and_shift_envelope() {
    for (width, shift) in [(9, 1), (8, 0), (8, 8), (8, 9)] {
        assert_honest_hole(&raw_shift_step(width, shift));
    }
}

#[test]
fn shift_shape_declines_connective_operand_and_clause_drift() {
    let mut signed = raw_shift_step(8, 1);
    let TermData::App(_, args) = signed.terms.get(signed.positive).clone() else {
        unreachable!()
    };
    let signed_positive = signed
        .terms
        .mk_app(Symbol::named("bvslt"), args, Sort::Bool);
    let signed_root = signed.terms.mk_app(
        Symbol::named("and"),
        vec![signed_positive, signed.non_strict],
        Sort::Bool,
    );
    let signed_literal = signed.terms.mk_not_raw(signed_root);
    signed.step = ProofStep::TheoryLemma {
        theory: "bv".to_string(),
        clause: vec![signed_literal],
        farkas: None,
        kind: TheoryLemmaKind::BvBitBlast,
        lia: None,
    };
    assert_honest_hole(&signed);

    let mut non_unit = raw_shift_step(8, 1);
    let extra = non_unit.terms.mk_var("p", Sort::Bool);
    let ProofStep::TheoryLemma { clause, .. } = &mut non_unit.step else {
        unreachable!()
    };
    clause.push(extra);
    assert_honest_hole(&non_unit);

    let mut reversed_and = raw_shift_step(8, 1);
    let reversed_root = reversed_and.terms.mk_app(
        Symbol::named("and"),
        vec![reversed_and.non_strict, reversed_and.positive],
        Sort::Bool,
    );
    let reversed_literal = reversed_and.terms.mk_not_raw(reversed_root);
    reversed_and.step = ProofStep::TheoryLemma {
        theory: "bv".to_string(),
        clause: vec![reversed_literal],
        farkas: None,
        kind: TheoryLemmaKind::BvBitBlast,
        lia: None,
    };
    assert_honest_hole(&reversed_and);
}

#[test]
fn shift_shape_declines_malformed_comparison_and_extract_sorts() {
    let mut bad_positive = raw_shift_step(8, 1);
    let TermData::App(_, positive_args) = bad_positive.terms.get(bad_positive.positive).clone()
    else {
        unreachable!()
    };
    let malformed_positive =
        bad_positive
            .terms
            .mk_app(Symbol::named("bvult"), positive_args, Sort::bitvec(1));
    let root = bad_positive.terms.mk_app(
        Symbol::named("and"),
        vec![malformed_positive, bad_positive.non_strict],
        Sort::Bool,
    );
    let literal = bad_positive.terms.mk_not_raw(root);
    bad_positive.step = ProofStep::TheoryLemma {
        theory: "bv".to_string(),
        clause: vec![literal],
        farkas: None,
        kind: TheoryLemmaKind::BvBitBlast,
        lia: None,
    };
    assert_honest_hole(&bad_positive);

    let mut bad_non_strict = raw_shift_step(8, 1);
    let TermData::App(_, non_strict_args) =
        bad_non_strict.terms.get(bad_non_strict.non_strict).clone()
    else {
        unreachable!()
    };
    let malformed_non_strict =
        bad_non_strict
            .terms
            .mk_app(Symbol::named("bvule"), non_strict_args, Sort::bitvec(1));
    let root = bad_non_strict.terms.mk_app(
        Symbol::named("and"),
        vec![bad_non_strict.positive, malformed_non_strict],
        Sort::Bool,
    );
    let literal = bad_non_strict.terms.mk_not_raw(root);
    bad_non_strict.step = ProofStep::TheoryLemma {
        theory: "bv".to_string(),
        clause: vec![literal],
        farkas: None,
        kind: TheoryLemmaKind::BvBitBlast,
        lia: None,
    };
    assert_honest_hole(&bad_non_strict);

    let mut bad_extract = raw_shift_step(8, 1);
    let TermData::App(_, shifted_args) = bad_extract.terms.get(bad_extract.shifted).clone() else {
        unreachable!()
    };
    let [high_zero, extract] = shifted_args.as_slice() else {
        unreachable!()
    };
    let TermData::App(extract_op, extract_args) = bad_extract.terms.get(*extract).clone() else {
        unreachable!()
    };
    let malformed_extract = bad_extract
        .terms
        .mk_app(extract_op, extract_args, Sort::bitvec(8));
    let malformed_shifted = bad_extract.terms.mk_app(
        Symbol::named("concat"),
        vec![*high_zero, malformed_extract],
        Sort::bitvec(8),
    );
    let TermData::App(_, non_strict_args) = bad_extract.terms.get(bad_extract.non_strict).clone()
    else {
        unreachable!()
    };
    let malformed_non_strict = bad_extract.terms.mk_app(
        Symbol::named("bvule"),
        vec![non_strict_args[0], malformed_shifted],
        Sort::Bool,
    );
    let root = bad_extract.terms.mk_app(
        Symbol::named("and"),
        vec![bad_extract.positive, malformed_non_strict],
        Sort::Bool,
    );
    let literal = bad_extract.terms.mk_not_raw(root);
    bad_extract.step = ProofStep::TheoryLemma {
        theory: "bv".to_string(),
        clause: vec![literal],
        farkas: None,
        kind: TheoryLemmaKind::BvBitBlast,
        lia: None,
    };
    assert_honest_hole(&bad_extract);
}

#[test]
fn shift_shape_declines_authenticated_surface_drift() {
    let case = raw_shift_step(8, 1);
    for (term, surface) in [
        (case.shifted, "((_ zero_extend 1) ((_ extract 7 1) x))"),
        (
            case.root,
            "(and (bvule x (concat #b0 ((_ extract 7 1) x))) (bvult #x00 x))",
        ),
        (case.literal, "false"),
    ] {
        let mut overrides = DetHashMap::default();
        overrides.insert(term, surface.to_string());
        let output = AlethePrinter::new_with_overrides(&case.terms, Some(&overrides))
            .format_step(&case.step, ProofId(3))
            .expect("surface mismatch stays on honest hole path");
        assert!(output.contains(":rule hole"), "{output}");
        assert!(!output.contains(":rule drat"), "{output}");
    }
}

#[test]
fn shift_proof_emission_obeys_output_budget() {
    let case = raw_shift_step(8, 1);
    let mut proof = Proof::new();
    proof.steps.push(case.step.clone());
    let error = try_export_alethe_with_problem_scope_overrides_and_budget(
        &proof,
        &case.terms,
        &[case.root],
        None,
        Some(1),
    )
    .expect_err("the exhaustive checked derivation must be budgeted");
    assert!(matches!(
        error,
        AlethePrintError::EmissionBudgetExhausted { budget: 1, .. }
    ));
}

#[test]
fn exact_shape_is_specific_to_bv_bitblast_theory_steps() {
    let mut case = raw_shift_step(8, 1);
    case.step = ProofStep::Step {
        rule: AletheRule::Hole,
        clause: vec![case.literal],
        premises: vec![],
        args: vec![],
    };
    assert_honest_hole(&case);
}
