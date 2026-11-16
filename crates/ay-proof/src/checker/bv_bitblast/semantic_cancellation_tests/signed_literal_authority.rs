// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! These original SMT goals carry no independently rechecked Lean relation
//! from signed division to the rewritten circuit. A Rust shortcut must not
//! turn their wide symbolic identities into strict proof authority.
use super::*;

fn clause(width: u32, operator: &str, divisor: u128, false_twin: bool) -> (TermStore, TermId) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("signed-original", Sort::bitvec(width));
    let zero = terms.mk_bitvec(0.into(), width);
    let one = terms.mk_bitvec(1.into(), width);
    let mask = (1u128 << width) - 1;
    let all_ones = terms.mk_bitvec(mask.into(), width);
    let d = terms.mk_bitvec(divisor.into(), width);
    let original = terms.mk_app(Symbol::named(operator), [x, d], Sort::bitvec(width));
    let expected = if operator != "bvsdiv" {
        if divisor == 0 {
            x
        } else {
            zero
        }
    } else if divisor == 0 {
        let negative = terms.mk_app(Symbol::named("bvslt"), [x, zero], Sort::Bool);
        terms.mk_ite(negative, one, all_ones)
    } else if divisor == mask {
        terms.mk_app(Symbol::named("bvneg"), [x], Sort::bitvec(width))
    } else {
        x
    };
    let expected = if false_twin {
        terms.mk_app(Symbol::named("bvadd"), [expected, one], Sort::bitvec(width))
    } else {
        expected
    };
    let equality = terms.mk_app(Symbol::named("="), [original, expected], Sort::Bool);
    (terms, equality)
}

fn strict_complete(terms: &mut TermStore, equality: TermId) -> bool {
    let negative = terms.mk_not_raw(equality);
    let mut proof = Proof::new();
    let assumed = proof.add_assume(negative, None);
    let lemma = proof.add_theory_lemma_with_kind("bv", vec![equality], TheoryLemmaKind::BvBitBlast);
    proof.add_resolution(Vec::new(), equality, lemma, assumed);
    crate::check_proof_strict(&proof, terms).is_ok_and(|checked| checked.is_complete())
}

#[test]
fn signed_literal_goals_without_lean_semantic_authority_do_not_close_strict_proofs() {
    let mut accepted = Vec::new();
    for width in [32, 64] {
        for operator in ["bvsdiv", "bvsrem", "bvsmod"] {
            for divisor in [0, 1, (1u128 << width) - 1] {
                let (mut terms, equality) = clause(width, operator, divisor, false);
                if strict_complete(&mut terms, equality) {
                    accepted.push((width, operator, divisor));
                }
            }
        }
    }
    assert!(
        accepted.is_empty(),
        "Rust-only signed semantics closed original goals: {accepted:?}"
    );
}

#[test]
fn signed_literal_false_twins_do_not_close_strict_proofs() {
    for width in [32, 64] {
        for operator in ["bvsdiv", "bvsrem", "bvsmod"] {
            for divisor in [0, 1, (1u128 << width) - 1] {
                let (mut terms, equality) = clause(width, operator, divisor, true);
                assert!(
                    !strict_complete(&mut terms, equality),
                    "{operator}/{divisor} at {width}"
                );
            }
        }
    }
}

#[test]
fn signed_power_and_nonpower_literals_keep_the_original_opaque_lowering() {
    for width in [32, 64] {
        for operator in ["bvsdiv", "bvsrem", "bvsmod"] {
            for divisor in [0, 1, 2, 3, (1u128 << width) - 1, (1u128 << width) - 3] {
                let mut terms = TermStore::new();
                let x = terms.mk_var("signed-original", Sort::bitvec(width));
                let d = terms.mk_bitvec(divisor.into(), width);
                let mut lowerer = ProofProducingLowerer::new_for_lemma_validation(
                    &terms,
                    Instant::now() + Duration::from_secs(10),
                );
                assert!(
                    matches!(
                        lowerer.lower_bv_app(&Symbol::named(operator), &[x, d]),
                        Ok(BvApplicationLowering::Abstractable(actual)) if actual == width
                    ),
                    "{operator}/{divisor} at {width}"
                );
            }
        }
    }
}

#[test]
fn original_generic_signed_occurrence_identity_and_unsigned_units_still_close() {
    for width in [32, 64] {
        for operator in ["bvsdiv", "bvsrem", "bvsmod"] {
            for divisor in [0, 1, 2, 3, (1u128 << width) - 1] {
                let mut terms = TermStore::new();
                let x = terms.mk_var("signed-original", Sort::bitvec(width));
                let d = terms.mk_bitvec(divisor.into(), width);
                let value = terms.mk_app(Symbol::named(operator), [x, d], Sort::bitvec(width));
                let same = terms.mk_app(Symbol::named("="), [value, value], Sort::Bool);
                assert!(strict_complete(&mut terms, same));
            }
        }
        for operator in ["bvudiv", "bvurem"] {
            let mut terms = TermStore::new();
            let x = terms.mk_var("unsigned-original", Sort::bitvec(width));
            let unit = terms.mk_bitvec(1.into(), width);
            let value = terms.mk_app(Symbol::named(operator), [x, unit], Sort::bitvec(width));
            let expected = if operator == "bvudiv" {
                x
            } else {
                terms.mk_bitvec(0.into(), width)
            };
            let same = terms.mk_app(Symbol::named("="), [value, expected], Sort::Bool);
            assert!(strict_complete(&mut terms, same));
        }
    }
}
