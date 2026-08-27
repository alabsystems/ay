// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact-shape and fail-closed tests for bounded `bvmul`-zero Alethe lowering.

use super::*;
use crate::ProofStep;
use ay_core::kani_compat::DetHashMap;
use ay_core::{Sort, Symbol, TermStore, TheoryLemmaKind};
use num_bigint::BigInt;

fn raw_mul_zero_step(
    width: u32,
    zero_operand: usize,
    reversed: bool,
) -> (TermStore, ProofStep, TermId, TermId) {
    let mut terms = TermStore::new();
    let sort = Sort::bitvec(width);
    let x = terms.mk_var("x", sort.clone());
    let zero = terms.mk_bitvec(BigInt::from(0), width);
    let operands = if zero_operand == 0 {
        [zero, x]
    } else {
        [x, zero]
    };
    // `mk_app` is deliberately raw here: `mk_bvmul` would fold the identity
    // before the proof-printer shape can be exercised.
    let product = terms.mk_app(Symbol::named("bvmul"), operands, sort);
    let equality_operands = if reversed {
        [zero, product]
    } else {
        [product, zero]
    };
    let equality = terms.mk_app(Symbol::named("="), equality_operands, Sort::Bool);
    let step = ProofStep::TheoryLemma {
        theory: "bv".to_string(),
        clause: vec![equality],
        farkas: None,
        kind: TheoryLemmaKind::BvBitBlast,
        lia: None,
    };
    (terms, step, equality, product)
}

#[test]
fn bounded_mul_zero_orientations_export_checked_multiplier_circuits() {
    for width in [1_u32, 8, 32] {
        for zero_operand in [0_usize, 1] {
            for reversed in [false, true] {
                // Width 32 is the production CEGIS carrier. One orientation
                // there suffices for the output-size-heavy endpoint; smaller
                // widths exhaustively cover both independent reversals.
                if width == 32 && (zero_operand != 1 || reversed) {
                    continue;
                }
                let (terms, step, _, _) = raw_mul_zero_step(width, zero_operand, reversed);
                let output = AlethePrinter::new(&terms)
                    .format_step(&step, ProofId(7))
                    .expect("the exact shape renders");
                assert!(output.contains(":rule bitblast_mult"), "{output}");
                assert!(output.contains(":rule bitblast_const"), "{output}");
                assert!(
                    output.contains("(define-fun __ay_bvmul_zero_7_0!"),
                    "{output}"
                );
                assert!(!output.contains(":rule hole"), "{output}");
                assert!(!output.contains(":rule trust"), "{output}");
                let final_rule = if reversed {
                    ":rule symm"
                } else {
                    ":rule trans"
                };
                assert!(
                    output
                        .lines()
                        .last()
                        .is_some_and(|line| line.contains("(step t7 ") && line.contains(final_rule)),
                    "{output}"
                );
            }
        }
    }
}

#[test]
fn mul_zero_lowering_declines_over_cap_and_surface_drift() {
    let (terms, step, _, _) = raw_mul_zero_step(33, 1, false);
    let output = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(0))
        .expect("unsupported shapes retain an honest hole");
    assert!(output.contains(":rule hole"), "{output}");
    assert!(!output.contains(":rule bitblast_mult"), "{output}");

    let (terms, step, equality, product) = raw_mul_zero_step(8, 1, false);
    for (overridden, spelling) in [
        (product, "(bvmul x #x01)"),
        (equality, "(= (bvmul #x00 x) #x00)"),
    ] {
        let mut overrides = DetHashMap::default();
        overrides.insert(overridden, spelling.to_string());
        let output = AlethePrinter::new_with_overrides(&terms, Some(&overrides))
            .format_step(&step, ProofId(0))
            .expect("surface drift retains an honest hole");
        assert!(output.contains(":rule hole"), "{output}");
        assert!(!output.contains(":rule bitblast_mult"), "{output}");
    }
}

#[test]
fn mul_zero_definition_namespace_skips_problem_symbol_collisions() {
    let (mut terms, step, _, _) = raw_mul_zero_step(2, 1, false);
    // User declarations starting with `__ay_` are normally rejected by the
    // frontend, but the printer also protects callers that construct a store
    // directly or install an authenticated surface override.
    let _collision = terms.mk_var("__ay_bvmul_zero_9_0!d0", Sort::Bool);
    let output = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(9))
        .expect("fresh namespace renders");
    assert!(
        output.contains("(define-fun __ay_bvmul_zero_9_1!"),
        "{output}"
    );
    assert!(
        !output.contains("(define-fun __ay_bvmul_zero_9_0!"),
        "{output}"
    );
    assert!(!output.contains(":rule hole"), "{output}");
}
