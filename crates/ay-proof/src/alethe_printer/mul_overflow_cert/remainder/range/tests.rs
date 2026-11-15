// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::super::term::{Op, Terms};
use super::super::super::{clean, div::DivStage, div_lemma::zero_test, div_spec};
use super::*;

mod resources;
mod semantics;

fn proof() -> Proof<'static> {
    Proof::new("range.".into(), "@range".into())
}

fn free_bits(p: &mut Proof<'_>, tag: &str, n: u32) -> Vec<T> {
    (0..n)
        .map(|i| p.t.var(&format!("{tag}{i}"), Sort::Bool))
        .collect()
}

#[test]
fn range_stage_has_no_product_cap_or_quotient_obligation() {
    for n in [1, 3, 5] {
        let mut p = proof();
        let stage = RangeStage::new(&mut p, n, "@s").expect("real range lemma");
        let quantified = p.unit(stage.fact);
        assert!(matches!(p.t.op(quantified), Op::Forall));
        assert_eq!(p.t.args(quantified).len(), 3 * n as usize + 1);
        assert_eq!(p.t.args(stage.invp).len(), 2);
        assert_eq!(p.t.args(stage.invc).len(), 2);
        for id in 0..p.t.len() as u32 {
            assert!(!matches!(p.t.op(id), Op::Mul | Op::Udiv | Op::Urem));
            assert!(p.t.width(id) <= n);
        }
        assert!(!p.out.contains(":rule poly_simp"));
        assert!(!p.out.contains(":rule hole") && !p.out.contains(":rule trust"));
    }
}

#[test]
fn range_stage_structurally_removes_work_from_the_complete_division_stage() {
    for n in [1, 3] {
        let mut full = proof();
        let _full_stage = DivStage::new(&mut full, n, "@s").expect("original complete stage");
        let mut range = proof();
        RangeStage::new(&mut range, n, "@s").expect("same checked range obligations");
        assert!(range.t.len() < full.t.len(), "n={n}: actual DAG size");
        assert!(
            range.out.len() < full.out.len(),
            "n={n}: actual emitted bytes"
        );
        assert!(range.out.lines().count() < full.out.lines().count());
        // Structural generated-work comparison, not a wall-time claim.
        assert!(
            range.budget > full.budget,
            "n={n}: fewer local proof operations"
        );
    }
}

#[test]
fn range_specification_proves_the_same_actual_range_as_complete_specification() {
    for n in [1, 3] {
        let mut p = proof();
        let x = p.t.var("x", Sort::Bv(n));
        let y = p.t.var("d", Sort::Bv(n));
        let (xb, yb) = (p.t.bits(x), p.t.bits(y));
        let yz = zero_test(&mut p, y);
        let nz = p.t.not(yz);
        let assumption = p.assume(nz);
        let full = DivStage::new(&mut p, n, "@full").expect("original stage");
        let (_, old_rem, old_fact) =
            div_spec::division_spec(&mut p, &full, &xb, &yb, assumption).expect("original chain");
        let range = RangeStage::new(&mut p, n, "@new").expect("range stage");
        let (new_rem, new_fact) = range
            .specification(&mut p, &xb, &yb, assumption)
            .expect("same genuine range proof");
        assert_eq!(new_rem, old_rem, "identical exact circuit TermIds");
        let old_parts = p.t.args(p.unit(old_fact));
        let new_parts = p.t.args(p.unit(new_fact));
        assert_eq!(new_parts, &old_parts[1..3]);
    }
}

#[test]
fn remainder_projection_preserves_exact_circuit_for_all_public_widths() {
    for n in [1, 3, 32, 64, 128] {
        let mut p = proof();
        let (x, y) = (free_bits(&mut p, "x", n), free_bits(&mut p, "y", n));
        let projected = specification::remainder_stages(&mut p, &x, &y).unwrap();
        let full = clean::udiv_stages(&mut p.t, &x, &y);
        assert_eq!(projected.len(), full.len());
        for (new, (_, old)) in projected.iter().zip(&full) {
            assert_eq!(
                new, old,
                "width {n}: every actual stage, not sampled semantics"
            );
        }
    }
}

#[test]
fn remainder_projection_keeps_ground_zero_shortcut_and_every_small_constant_divisor() {
    for n in 1..=4 {
        let mut p = proof();
        let free = free_bits(&mut p, "x", n);
        for constant in 0..1u64 << n {
            let y: Vec<_> = (0..n)
                .map(|i| {
                    if constant & (1 << i) == 0 {
                        p.t.ff
                    } else {
                        p.t.tt
                    }
                })
                .collect();
            for leading_zeroes in 0..=n {
                let mut x = free.clone();
                for bit in &mut x[(n - leading_zeroes) as usize..] {
                    *bit = p.t.ff;
                }
                let projected = specification::remainder_stages(&mut p, &x, &y).unwrap();
                let full = clean::udiv_stages(&mut p.t, &x, &y);
                assert_eq!(
                    projected,
                    full.into_iter().map(|(_, r)| r).collect::<Vec<_>>()
                );
            }
        }
    }
}

#[test]
fn malformed_dimensions_and_unsupported_stage_width_are_refused() {
    let mut p = proof();
    for width in [0, 129] {
        assert!(RangeStage::new(&mut p, width, "@bad").is_none());
    }
    assert!(specification::remainder_stages(&mut p, &[], &[]).is_none());
    let x = free_bits(&mut p, "x", 2);
    let y = free_bits(&mut p, "y", 1);
    assert!(specification::remainder_stages(&mut p, &x, &y).is_none());
    let stage = RangeStage::new(&mut p, 1, "@s").unwrap();
    let dummy = p.assume(p.t.tt);
    assert!(stage.specification(&mut p, &x, &y, dummy).is_none());
}

#[test]
fn ground_zero_dividend_reuses_only_the_exact_proved_zero_base() {
    let mut p = proof();
    let stage = RangeStage::new(&mut p, 1, "@s").unwrap();
    let x = vec![p.t.ff];
    let y = p.t.var("d", Sort::Bv(1));
    let yb = p.t.bits(y);
    let is_zero = zero_test(&mut p, y);
    let nonzero = p.t.not(is_zero);
    let hypothesis = p.assume(nonzero);
    let (remainder, fact) = stage.specification(&mut p, &x, &yb, hypothesis).unwrap();
    assert_eq!(remainder, x);
    let expected = invariant(&mut p, &x, &x, &yb);
    assert_eq!(p.unit(fact), expected);
}

#[test]
fn false_zero_divisor_hypothesis_cannot_prove_the_base_range() {
    let mut p = proof();
    let stage = RangeStage::new(&mut p, 1, "@s").unwrap();
    let x = free_bits(&mut p, "x", 1);
    let y = p.t.var("d", Sort::Bv(1));
    let yb = p.t.bits(y);
    let is_zero = zero_test(&mut p, y);
    let wrong = p.assume(is_zero);
    assert!(stage.specification(&mut p, &x, &yb, wrong).is_none());
}

#[test]
fn actual_constant_ten_source_theorem_keeps_the_original_clause() {
    use ay_core::{ProofId, Sort as CoreSort, Symbol, TermStore};
    let mut terms = TermStore::new();
    let x = terms.mk_var("original_digits", CoreSort::bitvec(32));
    let d = terms.mk_bitvec(10.into(), 32);
    let zero = terms.mk_bitvec(0.into(), 32);
    let r = terms.mk_app(Symbol::named("bvurem"), [x, d], CoreSort::bitvec(32));
    let is_zero = terms.mk_app(Symbol::named("="), [d, zero], CoreSort::Bool);
    let less = terms.mk_app(Symbol::named("bvult"), [r, d], CoreSort::Bool);
    let theorem = terms.mk_app(Symbol::named("or"), [is_zero, less], CoreSort::Bool);
    let printer = crate::alethe_printer::AlethePrinter::new(&terms);
    let expected = printer.format_clause(&[theorem]);
    let document = printer
        .format_urem_bound(ProofId(17), &[theorem])
        .expect("actual source path");
    let last = document.lines().last().unwrap();
    assert!(
        last.contains(&expected),
        "exact original theorem, not a reduced input"
    );
    assert!(document.contains(":rule bitblast_urem") && document.contains(":rule forall_inst"));
    assert!(!document.contains("bvmul") && !document.contains(":rule poly_simp"));
    assert!(!document.contains(":rule hole") && !document.contains(":rule trust"));
    // Full original rem_u32_digits and external Clean remain required separate
    // controls; this verifies the actual source-bound export route only.
}
