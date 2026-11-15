// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The ring lane (`Normalizer::ring_identity`): nonlinear identities of the
//! polynomial ring over Z/(2^width), decided on Carcara's integer expansion.
//!
//! Measured on the external-codegen corpus (AY `--strict-proofs`): `(bvmul a b) =
//! (bvmul b a)` (`CSE commutative`) and the `ReductionSplit` product regroups
//! such as `((((acc*t0)*t1)*t2)*t3) = ((acc*t0)*t1)*(t2*t3)` answered
//! `unknown`: elaboration folds both sides to one term, and the collapse
//! reconstruction found no lemma route because the affine form keeps each
//! product as its own atom. One `poly_simp` step proves each of them.

use super::*;
use ay_core::{Proof, TheoryLemmaKind};

fn app(terms: &mut TermStore, op: &str, a: TermId, b: TermId, width: u32) -> TermId {
    terms.mk_app(Symbol::named(op), [a, b], Sort::bitvec(width))
}

fn eq(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [a, b], Sort::Bool)
}

fn product(terms: &mut TermStore, factors: &[TermId], width: u32) -> TermId {
    let mut factors = factors.iter().copied();
    let first = factors.next().expect("a product has a factor");
    factors.fold(first, |acc, factor| app(terms, "bvmul", acc, factor, width))
}

fn accepted_everywhere(terms: &TermStore, equality: TermId) {
    assert!(check(terms, &[equality], &mut |_, _| true).unwrap());
    assert!(check_native(terms, &[equality], &mut |_, _| true).unwrap());
    assert!(crate::recognize_arith_poly_simp(terms, &[equality]));
    assert!(crate::recognize_arith_clause_tautology(terms, &[equality]));
}

/// The measured external-codegen shapes, at the widths they were measured at, are
/// accepted by the wire and native lanes, pass the strict proof checker as an
/// `ArithClauseTautology` lemma, and print as one hole-free `poly_simp` step.
#[test]
fn commuted_and_regrouped_products_are_ring_identities() {
    for width in [8, 64] {
        let mut terms = TermStore::new();
        let names = ["acc", "t0", "t1", "t2", "t3", "t4", "t5", "t6", "t7"];
        let v = names.map(|name| terms.mk_var(name, Sort::bitvec(width)));
        let ab = app(&mut terms, "bvmul", v[0], v[1], width);
        let ba = app(&mut terms, "bvmul", v[1], v[0], width);
        let commuted = eq(&mut terms, ab, ba);
        // mul regroup N=4 M=4.
        let chain = product(&mut terms, &v[..5], width);
        let head = product(&mut terms, &v[..3], width);
        let tail = product(&mut terms, &v[3..5], width);
        let regrouped = app(&mut terms, "bvmul", head, tail, width);
        let regroup = eq(&mut terms, chain, regrouped);
        // mul regroup N=4 M=8: four interleaved partial products.
        let long_chain = product(&mut terms, &v, width);
        let lanes = [
            product(&mut terms, &[v[0], v[1], v[5]], width),
            product(&mut terms, &[v[2], v[6]], width),
            product(&mut terms, &[v[3], v[7]], width),
            product(&mut terms, &[v[4], v[8]], width),
        ];
        let first = app(&mut terms, "bvmul", lanes[0], lanes[1], width);
        let second = app(&mut terms, "bvmul", lanes[2], lanes[3], width);
        let interleaved = app(&mut terms, "bvmul", first, second, width);
        let interleave = eq(&mut terms, long_chain, interleaved);
        for equality in [commuted, regroup, interleave] {
            accepted_everywhere(&terms, equality);
            let negated = terms.mk_not_raw(equality);
            let mut proof = Proof::new();
            let assume = proof.add_assume(negated, None);
            let lemma = proof.add_theory_lemma_with_kind(
                "bv",
                vec![equality],
                TheoryLemmaKind::ArithClauseTautology,
            );
            proof.add_resolution(vec![], equality, assume, lemma);
            crate::check_proof_strict(&proof, &terms).expect("independent native proof check");
            let text = crate::try_export_alethe_with_problem_scope_and_overrides(
                &proof,
                &terms,
                &[negated],
                None,
            )
            .unwrap();
            assert!(
                text.contains(":rule poly_simp") && !text.contains(":rule hole"),
                "{text}"
            );
        }
        // A dropped or duplicated factor is not an identity.
        let short = product(&mut terms, &v[..4], width);
        let dropped = eq(&mut terms, chain, short);
        let squared = app(&mut terms, "bvmul", chain, v[4], width);
        let duplicated = eq(&mut terms, chain, squared);
        for equality in [dropped, duplicated] {
            assert!(!check(&terms, &[equality], &mut |_, _| true).unwrap());
            assert!(!check_native(&terms, &[equality], &mut |_, _| true).unwrap());
            assert!(!crate::recognize_arith_clause_tautology(
                &terms,
                &[equality]
            ));
        }
    }
}

/// A product whose coefficient wraps to zero is a true identity that
/// `poly_simp` refuses (it keeps the monomial), so no lane claims it here.
#[test]
fn a_wrapped_nonlinear_coefficient_is_refused() {
    let width = 8;
    let mut terms = TermStore::new();
    let [x, y] = ["x", "y"].map(|name| terms.mk_var(name, Sort::bitvec(width)));
    let half = terms.mk_bitvec(0x80u8.into(), width);
    let xy = app(&mut terms, "bvmul", x, y, width);
    let yx = app(&mut terms, "bvmul", y, x, width);
    let left_half = app(&mut terms, "bvmul", half, xy, width);
    let right_half = app(&mut terms, "bvmul", yx, half, width);
    let wrapped = app(&mut terms, "bvadd", left_half, right_half, width);
    let zero = terms.mk_bitvec(0u8.into(), width);
    let equality = eq(&mut terms, wrapped, zero);
    assert!(!check(&terms, &[equality], &mut |_, _| true).unwrap());
    assert!(!crate::recognize_arith_poly_simp(&terms, &[equality]));
}

/// Every nonlinear candidate over two 3-bit words, built from a small
/// grammar, is accepted ONLY if it holds for all 64 assignments, and the
/// known ring identities among them are accepted.
#[test]
fn ring_answers_are_sound_on_exhaustive_small_domains() {
    const WIDTH: u32 = 3;
    const MASK: u64 = (1 << WIDTH) - 1;
    #[derive(Clone)]
    enum E {
        X,
        Y,
        K(u64),
        Add(Box<E>, Box<E>),
        Sub(Box<E>, Box<E>),
        Mul(Box<E>, Box<E>),
        Neg(Box<E>),
    }
    fn eval(e: &E, x: u64, y: u64) -> u64 {
        match e {
            E::X => x,
            E::Y => y,
            E::K(k) => *k,
            E::Add(a, b) => (eval(a, x, y) + eval(b, x, y)) & MASK,
            E::Sub(a, b) => (eval(a, x, y) + (MASK + 1) - eval(b, x, y)) & MASK,
            E::Mul(a, b) => (eval(a, x, y) * eval(b, x, y)) & MASK,
            E::Neg(a) => ((MASK + 1) - eval(a, x, y)) & MASK,
        }
    }
    fn build(terms: &mut TermStore, e: &E) -> TermId {
        let sort = Sort::bitvec(WIDTH);
        match e {
            E::X => terms.mk_var("x", sort),
            E::Y => terms.mk_var("y", sort),
            E::K(k) => terms.mk_bitvec((*k).into(), WIDTH),
            E::Add(a, b) | E::Sub(a, b) | E::Mul(a, b) => {
                let op = match e {
                    E::Add(..) => "bvadd",
                    E::Sub(..) => "bvsub",
                    _ => "bvmul",
                };
                let (a, b) = (build(terms, a), build(terms, b));
                app(terms, op, a, b, WIDTH)
            }
            E::Neg(a) => {
                let a = build(terms, a);
                terms.mk_app(Symbol::named("bvneg"), [a], sort)
            }
        }
    }
    let leaves = [E::X, E::Y, E::K(1), E::K(3), E::K(4)];
    let mut level: Vec<E> = leaves.to_vec();
    for a in &leaves {
        level.push(E::Neg(Box::new(a.clone())));
        for b in &leaves {
            level.push(E::Add(Box::new(a.clone()), Box::new(b.clone())));
            level.push(E::Sub(Box::new(a.clone()), Box::new(b.clone())));
            level.push(E::Mul(Box::new(a.clone()), Box::new(b.clone())));
        }
    }
    let products: Vec<E> = level
        .iter()
        .flat_map(|a| {
            [
                E::Mul(Box::new(a.clone()), Box::new(E::X)),
                E::Mul(Box::new(E::Y), Box::new(a.clone())),
            ]
        })
        .collect();
    let (mut accepted, mut identities) = (0, 0);
    for left in &products {
        for right in products.iter().chain(&level) {
            let holds =
                (0..=MASK).all(|x| (0..=MASK).all(|y| eval(left, x, y) == eval(right, x, y)));
            let mut terms = TermStore::new();
            let (l, r) = (build(&mut terms, left), build(&mut terms, right));
            let equality = eq(&mut terms, l, r);
            let native = check_native(&terms, &[equality], &mut |_, _| true).unwrap();
            let wire = check(&terms, &[equality], &mut |_, _| true).unwrap();
            assert!(!native || holds, "native accepted a false identity");
            assert!(
                !wire || native,
                "the wire lane is a subset of the native one"
            );
            identities += usize::from(holds);
            accepted += usize::from(wire);
        }
    }
    // Not vacuous: the sweep holds ring identities the lane accepts.
    assert!(accepted > 0, "{accepted} of {identities}");
}

/// A slice, an extension or a `concat` is one opaque factor, as `poly_simp`
/// reads it: the limb lane's ring step `(S*Z(a1) + Z(a0)) * B = Z(a1) *
/// (S * B) + Z(a0) * B` over the atoms `Z(a1)`, `Z(a0)` and the concat `B` is
/// an identity, and dropping the shift is not.
#[test]
fn slices_extensions_and_concats_are_opaque_factors() {
    let (width, half) = (16, 8);
    let mut terms = TermStore::new();
    let [a1, a0, b1, b0] =
        ["a1", "a0", "b1", "b0"].map(|name| terms.mk_var(name, Sort::bitvec(half)));
    let widen = |terms: &mut TermStore, word: TermId| {
        let symbol = Symbol::indexed("zero_extend", vec![half]);
        terms.mk_app(symbol, [word], Sort::bitvec(width))
    };
    let (za1, za0) = (widen(&mut terms, a1), widen(&mut terms, a0));
    let b = app(&mut terms, "concat", b1, b0, width);
    let shift = terms.mk_bitvec(256u32.into(), width);
    let shifted = app(&mut terms, "bvmul", shift, za1, width);
    let sum = app(&mut terms, "bvadd", shifted, za0, width);
    let left = app(&mut terms, "bvmul", sum, b, width);
    let shifted_b = app(&mut terms, "bvmul", shift, b, width);
    let high = app(&mut terms, "bvmul", za1, shifted_b, width);
    let low = app(&mut terms, "bvmul", za0, b, width);
    let right = app(&mut terms, "bvadd", high, low, width);
    let identity = eq(&mut terms, left, right);
    accepted_everywhere(&terms, identity);
    let unshifted = app(&mut terms, "bvmul", za1, b, width);
    let wrong = app(&mut terms, "bvadd", unshifted, low, width);
    let false_identity = eq(&mut terms, left, wrong);
    assert!(!check(&terms, &[false_identity], &mut |_, _| true).unwrap());
    assert!(!check_native(&terms, &[false_identity], &mut |_, _| true).unwrap());
}
