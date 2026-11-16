// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A whole-query bit-vector lemma reaches the wire as the complete bit-blast
//! refutation, through the printed-text judgements every step passes, and
//! for both kinds that certify one.
//!
//! Measured on external-codegen's queries (AY c6a80496e, `-smt2 F --strict-proofs
//! --proof F.alethe --proof-format alethe`): `(assert (not (= (bvsub xa
//! (bvmul xn (_ bv0 8))) xa)))` answered `unknown (incomplete
//! proof-trusted)` because its certificate was
//! `(step t1 (cl (not (not (= (bvsub xa (bvmul xn #b00000000)) xa)))) :rule hole)`,
//! while `format_bv_complete_blast_refutation` alone rendered it (73,956
//! bytes). Two defects stood between them:
//!
//! * the printed `poly_simp` judgement read the lowering's
//!   `(= @ay_cbb_t1_0_w6 @ay_cbb_t1_0_w5)` — two of the step's own word
//!   definitions — as free atoms, decided their difference was nonzero, and
//!   declined the whole step to `hole`;
//! * the lemma is a `BvLiaTautology` (AY's bounded BV/LIA interpreter), and
//!   only `BvBitBlast` lemmas were offered to the checked bit-blast lowerings.
//!
//! Lifting the first exposed a third: the doubling re-spelling of `x * 2^k`
//! accepted a factor whose BITS are `2^k` but which is not a literal the
//! checker's polynomial normalizer reads as a constant.

use super::*;
use ay_core::{ProofStep, TermStore, TheoryLemmaKind};

fn whole_query_lemma(terms: &mut TermStore) -> TermId {
    let xa = terms.mk_var("xa", Sort::bitvec(8));
    let xn = terms.mk_var("xn", Sort::bitvec(8));
    let zero = terms.mk_bitvec(0.into(), 8);
    let product = terms.mk_app(Symbol::named("bvmul"), vec![xn, zero], Sort::bitvec(8));
    let difference = terms.mk_app(Symbol::named("bvsub"), vec![xa, product], Sort::bitvec(8));
    let equality = terms.mk_app(Symbol::named("="), vec![difference, xa], Sort::Bool);
    let assertion = terms.mk_not_raw(equality);
    terms.mk_not_raw(assertion)
}

#[test]
fn a_whole_query_bit_vector_lemma_prints_its_complete_refutation() {
    for kind in [TheoryLemmaKind::BvBitBlast, TheoryLemmaKind::BvLiaTautology] {
        let mut terms = TermStore::new();
        let literal = whole_query_lemma(&mut terms);
        let step = ProofStep::TheoryLemma {
            theory: "bv".to_string(),
            clause: vec![literal],
            farkas: None,
            kind,
            lia: None,
        };
        let printer = AlethePrinter::new(&terms);
        let text = printer
            .format_step(&step, ProofId(1))
            .unwrap_or_else(|error| panic!("{kind:?}: the lemma must print: {error:?}"));
        assert!(
            !text.contains(":rule hole") && !text.contains(":rule trust"),
            "{kind:?}: a lemma the complete bit-blast refutes must not print a hole:\n{}",
            &text[..text.len().min(400)]
        );
        assert!(
            text.contains(":rule poly_simp") && text.contains(":rule bitblast_mult"),
            "{kind:?}: the refutation re-spells `bvsub` through `poly_simp` over its word \
             definitions and blasts the product"
        );
        assert!(
            text.contains("(step t1 (cl (not (not (= (bvsub xa (bvmul xn #b00000000)) xa)))) "),
            "{kind:?}: the lowering must conclude the lemma's own clause"
        );
    }
}

#[test]
fn the_poly_simp_judgement_does_not_decide_over_a_steps_own_definitions() {
    let rendered = "\
(define-fun @w6 () (_ BitVec 8) (bvsub xa (bvmul xn #b00000000)))
(define-fun @w5 () (_ BitVec 8) (bvadd xa (bvneg (bvmul xn #b00000000))))
(step t1.pr (cl (= @w6 @w5)) :rule poly_simp)
(step t1.int (cl (= (+ i 1) (+ 1 i 0))) :rule poly_simp)
(step t1.bad (cl (= (+ i 1) i)) :rule poly_simp)
";
    let commands = super::super::la_generic_surface::printed_arith_commands(rendered)
        .expect("the step reads as commands");
    let judged: Vec<(&str, Option<bool>)> = commands
        .iter()
        .map(|command| match command {
            super::super::la_generic_surface::PrintedArithCommand::PolySimp {
                name,
                left,
                right,
            } => (
                *name,
                super::super::la_generic_surface::printed_poly_simp_holds(left, right),
            ),
            _ => panic!("only poly_simp commands are printed here"),
        })
        .collect();
    // The definitions are the checker's to expand; the two readable steps are
    // still judged, and the wrong one is still refused.
    assert_eq!(judged, [("t1.int", Some(true)), ("t1.bad", Some(false))]);
}

/// Only a LITERAL `2^k` factor is re-spelled as a doubling chain.
///
/// external-codegen's `cegis_iter_0` query multiplies by `((_ extract 31 0) (_
/// bv8589934594 64))`, whose bits are those of 2 but which the checker's
/// polynomial normalizer reads as an opaque atom: the doubling rewrite
/// `(= (bvmul w8 x) (bvadd x x))` was refused by Carcara 9a352ee and Clean
/// 414913cce. The product must go through `bitblast_mult` instead.
#[test]
fn a_constant_valued_non_literal_factor_is_blasted_not_respelled() {
    let mut terms = TermStore::new();
    let v = terms.mk_var("v", Sort::bitvec(64));
    let wide = terms.mk_bitvec(8_589_934_594_u64.into(), 64);
    let factor = terms.mk_app(
        Symbol::indexed("extract", vec![31, 0]),
        vec![wide],
        Sort::bitvec(32),
    );
    let low = terms.mk_app(
        Symbol::indexed("extract", vec![31, 0]),
        vec![v],
        Sort::bitvec(32),
    );
    let product = terms.mk_app(Symbol::named("bvmul"), vec![factor, low], Sort::bitvec(32));
    let one = terms.mk_bitvec(1.into(), 32);
    let shifted = terms.mk_app(Symbol::named("bvshl"), vec![low, one], Sort::bitvec(32));
    let equality = terms.mk_app(Symbol::named("="), vec![product, shifted], Sort::Bool);
    let assertion = terms.mk_not_raw(equality);
    let literal = terms.mk_not_raw(assertion);
    let step = ProofStep::TheoryLemma {
        theory: "bv".to_string(),
        clause: vec![literal],
        farkas: None,
        kind: TheoryLemmaKind::BvBitBlast,
        lia: None,
    };
    let printer = AlethePrinter::new(&terms);
    let text = printer
        .format_step(&step, ProofId(1))
        .expect("the lemma prints");
    assert!(
        !text.contains(":rule hole"),
        "the product is refutable by blasting it"
    );
    assert!(
        text.contains(":rule bitblast_mult") && !text.contains(":rule poly_simp"),
        "a non-literal factor must be blasted, never re-spelled through poly_simp"
    );
}
