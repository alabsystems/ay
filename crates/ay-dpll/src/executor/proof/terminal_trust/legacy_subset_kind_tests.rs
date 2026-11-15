// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Legacy BV shape checks share the printer's kind and surface preconditions.

use super::*;
use ay_core::{Symbol, TheoryLemmaKind};

fn constant_disequality(executor: &mut Executor) -> (TermId, TermId) {
    let terms = &mut executor.ctx.terms;
    let one = terms.mk_bitvec(1_u8.into(), 2);
    let two = terms.mk_bitvec(2_u8.into(), 2);
    let equality = terms.mk_app(Symbol::named("="), [one, two], Sort::Bool);
    (terms.mk_not_raw(equality), two)
}

#[test]
fn a_constant_bv_shape_does_not_grant_an_unrelated_lemma_kind_authority() {
    let mut executor = Executor::new();
    let (clause, _) = constant_disequality(&mut executor);
    assert!(executor.bv_constant_disequality_is_fixed_wire_evaluate(&[clause], None));
    let mut bitblast = Proof::new();
    bitblast.add_theory_lemma_with_kind("bv", vec![clause], TheoryLemmaKind::BvBitBlast);
    assert!(!executor.proof_has_known_wire_gap(&bitblast));
    for kind in [TheoryLemmaKind::Generic, TheoryLemmaKind::ArrayRowChain] {
        let mut unrelated = Proof::new();
        unrelated.add_theory_lemma_with_kind("control", vec![clause], kind);
        assert!(executor.proof_has_known_wire_gap(&unrelated));
    }
}

#[test]
fn an_overridden_or_false_constant_disequality_stays_outside_the_exact_subset() {
    let mut executor = Executor::new();
    let (clause, two) = constant_disequality(&mut executor);
    let mut overrides = DetHashMap::default();
    overrides.insert(two, "#b01".to_string());
    assert!(!executor.bv_constant_disequality_is_fixed_wire_evaluate(&[clause], Some(&overrides),));
    assert!(!ay_proof::checked_bv_bitblast_lowering_supported_asking(
        &executor.ctx.terms,
        &TheoryLemmaKind::BvBitBlast,
        &[clause],
        Some(&overrides),
        ay_proof::CompleteBlastAsk::NotAsked,
    ));
    let equality = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), [two, two], Sort::Bool);
    let false_literal = executor.ctx.terms.mk_not_raw(equality);
    assert!(!executor.bv_constant_disequality_is_fixed_wire_evaluate(&[false_literal], None));
    let mut false_proof = Proof::new();
    false_proof.add_theory_lemma_with_kind("bv", vec![false_literal], TheoryLemmaKind::BvBitBlast);
    assert!(executor.proof_has_known_wire_gap(&false_proof));
}
