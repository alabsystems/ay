// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{Proof, TheoryLemmaKind};

#[path = "polynomial_tests.rs"]
mod polynomial_tests;
#[path = "shift_tests.rs"]
mod shift_tests;

fn app(terms: &mut TermStore, op: &str, a: TermId, b: TermId, width: u32) -> TermId {
    terms.mk_app(Symbol::named(op), [a, b], Sort::bitvec(width))
}

fn eq(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [a, b], Sort::Bool)
}

#[test]
fn modular_subtractor_exports_checked_original_equalities() {
    for width in [1, 9, 32, 64, 128] {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::bitvec(width));
        let b = terms.mk_var("b", Sort::bitvec(width));
        let c = terms.mk_var("c", Sort::bitvec(width));
        let sum = app(&mut terms, "bvadd", a, c, width);
        let left = app(&mut terms, "bvsub", sum, b, width);
        let difference = app(&mut terms, "bvsub", c, b, width);
        let right = app(&mut terms, "bvadd", difference, a, width);
        let equality = eq(&mut terms, left, right);
        assert!(check(&terms, &[equality], &mut |_, _| true).unwrap());
        assert!(crate::recognize_arith_clause_tautology(&terms, &[equality]));
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
        assert!(text.contains(":rule poly_simp") && !text.contains(":rule hole"));
        let mut overrides = ay_core::kani_compat::DetHashMap::default();
        overrides.insert(difference, "(bvadd c b)".to_string());
        if let Ok(forged) = crate::try_export_alethe_with_problem_scope_and_overrides(
            &proof,
            &terms,
            &[negated],
            Some(&overrides),
        ) {
            assert!(
                forged.contains(":rule hole"),
                "divergent source must decline"
            );
        }
        let problem = format!("(set-logic QF_BV)\n(declare-const a (_ BitVec {width}))\n(declare-const b (_ BitVec {width}))\n(declare-const c (_ BitVec {width}))\n(assert {})\n(check-sat)\n", crate::format_term_alethe(&terms, negated));
        let path =
            std::env::temp_dir().join(format!("ay-affine-{}-{width}.json", std::process::id()));
        std::fs::write(&path, serde_json::to_vec(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":problem,"proof":text})).unwrap()).unwrap();
        println!("independent replay certificate: {}", path.display());
    }
}

fn linear(terms: &mut TermStore, x: TermId, a: u128, b: u128, width: u32) -> TermId {
    // The low `width` bits; a width of 128 or more keeps all of `b`.
    let mask = 1u128
        .checked_shl(width)
        .map_or(u128::MAX, |bit| bit.saturating_sub(1));
    let mut term = terms.mk_bitvec((b & mask).into(), width);
    for _ in 0..a {
        term = app(terms, "bvadd", term, x, width);
    }
    term
}

#[test]
fn modular_affine_answers_match_exhaustive_small_domains() {
    for width in 1..=4 {
        for a in 0u128..4 {
            for b in 0u128..4 {
                for c in 0u128..4 {
                    for d in 0u128..4 {
                        let mut terms = TermStore::new();
                        let x = terms.mk_var("x", Sort::bitvec(width));
                        let left = linear(&mut terms, x, a, b, width);
                        let right = linear(&mut terms, x, c, d, width);
                        let equality = eq(&mut terms, left, right);
                        let modulus = 1 << width;
                        let expected =
                            (0..modulus).all(|x| (a * x + b) % modulus == (c * x + d) % modulus);
                        assert_eq!(
                            check_native(&terms, &[equality], &mut |_, _| true).unwrap(),
                            expected,
                            "{width}: {a}x+{b}={c}x+{d}"
                        );
                        // The wire lane additionally declines a coefficient
                        // that must wrap to zero, which `poly_simp` keeps.
                        let wraps = [a, c].iter().any(|&k| k != 0 && k % modulus == 0);
                        assert_eq!(
                            check(&terms, &[equality], &mut |_, _| true).unwrap(),
                            expected && !wraps,
                            "{width}: {a}x+{b}={c}x+{d} (wire)"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn malformed_hidden_terms_and_wrong_equalities_are_rejected() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(64));
    let y = terms.mk_var("y", Sort::bitvec(64));
    let wrong = eq(&mut terms, x, y);
    assert!(!check(&terms, &[wrong], &mut |_, _| true).unwrap());
    let other = terms.mk_var("other", Sort::bitvec(32));
    for term in [
        terms.mk_app(Symbol::named("bvadd"), [x, other], Sort::bitvec(64)),
        terms.mk_app(Symbol::named("bvadd"), [x], Sort::bitvec(64)),
        terms.mk_app(Symbol::named("unmodeled"), [x], Sort::bitvec(64)),
    ] {
        let equality = eq(&mut terms, term, term);
        assert!(!check(&terms, &[equality], &mut |_, _| true).unwrap());
    }
    let too_wide = terms.mk_var("too_wide", Sort::bitvec(129));
    let equality = eq(&mut terms, too_wide, too_wide);
    assert!(!check(&terms, &[equality], &mut |_, _| true).unwrap());
    assert!(!check(&terms, &[wrong, wrong], &mut |_, _| true).unwrap());
    assert!(!check(&terms, &[TermId(u32::MAX)], &mut |_, _| true).unwrap());
}

#[test]
fn failed_and_cancelled_candidates_obey_bounded_work() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(64));
    let y = terms.mk_var("y", Sort::bitvec(64));
    let wrong = eq(&mut terms, x, y);
    let mut charges = Vec::new();
    assert!(!check(&terms, &[wrong], &mut |work, bytes| {
        charges.push((work, bytes));
        true
    })
    .unwrap());
    assert_eq!(
        charges,
        [
            (PRICE_SCAN_WORK, 0),
            (MAX_WORK - PRICE_SCAN_WORK, SMALL_LINEAR_ALLOCATION)
        ]
    );
    assert!(matches!(
        check(&terms, &[wrong], &mut |_, _| false),
        Err(ProofCheckError::ResourceLimit)
    ));
    let mut deep = x;
    for _ in 0..=MAX_DEPTH {
        deep = app(&mut terms, "bvadd", deep, x, 64);
    }
    let equality = eq(&mut terms, deep, deep);
    assert!(!check(&terms, &[equality], &mut |_, _| true).unwrap());
}

fn constant(terms: &mut TermStore, value: u128, width: u32) -> TermId {
    terms.mk_bitvec(value.into(), width)
}

/// The ExternalCodegen Faulhaber step: a 64-bit sum with small constant multipliers
/// (`group_bv::bv_performance_diagnostic`). The solver decides it by
/// normalization. While `bvmul` by a literal was an opaque atom here, no
/// certificate lane could state it, and each one instead re-proved it by a
/// proof-producing bit-blast that ran out its three-second deadline: the
/// default CLI publication took about 30 s and certified nothing.
#[test]
fn literal_constant_multiples_are_scaled_and_export_as_poly_simp() {
    let width = 64;
    let mut terms = TermStore::new();
    let [acc, a2, a1, a0] =
        ["acc", "a2", "a1", "a0"].map(|name| terms.mk_var(name, Sort::bitvec(width)));
    let mut scaled =
        |terms: &mut TermStore, factor: u128, operand: TermId, constant_first: bool| {
            let factor = constant(terms, factor, width);
            let (left, right) = if constant_first {
                (factor, operand)
            } else {
                (operand, factor)
            };
            app(terms, "bvmul", left, right, width)
        };
    let mut left = scaled(&mut terms, 2, a1, true);
    let four_a2 = scaled(&mut terms, 4, a2, true);
    left = app(&mut terms, "bvadd", left, four_a2, width);
    for addend in [a0, a0, a0, a1, a2, acc] {
        left = app(&mut terms, "bvadd", left, addend, width);
    }
    let right_with = |terms: &mut TermStore,
                      scaled: &mut dyn FnMut(&mut TermStore, u128, TermId, bool) -> TermId,
                      a2_factor: u128,
                      constant_first: bool| {
        let three_a0 = scaled(terms, 3, a0, constant_first);
        let three_a1 = scaled(terms, 3, a1, constant_first);
        let k_a2 = scaled(terms, a2_factor, a2, constant_first);
        let mut right = app(terms, "bvadd", three_a0, three_a1, width);
        right = app(terms, "bvadd", right, k_a2, width);
        app(terms, "bvadd", right, acc, width)
    };
    let right = right_with(&mut terms, &mut scaled, 5, true);
    let equality = eq(&mut terms, left, right);
    assert!(check(&terms, &[equality], &mut |_, _| true).unwrap());
    assert!(crate::recognize_arith_clause_tautology(&terms, &[equality]));
    assert!(crate::recognize_arith_poly_simp(&terms, &[equality]));
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
    let text =
        crate::try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[negated], None)
            .unwrap();
    assert!(
        text.contains(":rule poly_simp") && !text.contains(":rule hole"),
        "{text}"
    );

    // The constant may be either operand.
    let swapped = right_with(&mut terms, &mut scaled, 5, false);
    let equality = eq(&mut terms, left, swapped);
    assert!(check(&terms, &[equality], &mut |_, _| true).unwrap());
    // One wrong coefficient is refuted.
    let wrong = right_with(&mut terms, &mut scaled, 6, true);
    let equality = eq(&mut terms, left, wrong);
    assert!(!check(&terms, &[equality], &mut |_, _| true).unwrap());
    assert!(!crate::recognize_arith_clause_tautology(
        &terms,
        &[equality]
    ));
}

#[test]
fn scaled_affine_answers_match_exhaustive_small_domains() {
    for width in 1..=4u32 {
        let modulus = 1u128 << width;
        for a in 0..modulus {
            for c in 0..modulus {
                for b in 0..modulus.min(2) {
                    for d in 0..modulus.min(2) {
                        let mut terms = TermStore::new();
                        let x = terms.mk_var("x", Sort::bitvec(width));
                        let (a_term, c_term) = (
                            constant(&mut terms, a, width),
                            constant(&mut terms, c, width),
                        );
                        let (b_term, d_term) = (
                            constant(&mut terms, b, width),
                            constant(&mut terms, d, width),
                        );
                        let ax = app(&mut terms, "bvmul", a_term, x, width);
                        let xc = app(&mut terms, "bvmul", x, c_term, width);
                        let left = app(&mut terms, "bvadd", ax, b_term, width);
                        let right = app(&mut terms, "bvadd", xc, d_term, width);
                        let equality = eq(&mut terms, left, right);
                        let expected =
                            (0..modulus).all(|x| (a * x + b) % modulus == (c * x + d) % modulus);
                        let got = check(&terms, &[equality], &mut |_, _| true).unwrap();
                        if a != 0 && c != 0 {
                            assert_eq!(got, expected, "{width}: {a}*x+{b} = x*{c}+{d}");
                        } else {
                            // Zero products stay atoms: never more than the truth.
                            assert!(!got || expected, "{width}: {a}*x+{b} = x*{c}+{d}");
                        }
                    }
                }
            }
        }
    }
}

/// Elaboration rewrites `bvmul` by a constant into shifts and additions
/// (`TermStore::mk_bvmul`), and a session without a retained surface has only
/// that form. The strict checker reads the shift as a scalar; the wire lane
/// does not, because Carcara's `poly_simp` has no `concat`, and neither does the
/// shared recognizer, so no lane that prefers a printable lemma picks it up.
#[test]
fn elaborated_power_of_two_shifts_are_native_only() {
    let width = 64;
    let mut terms = TermStore::new();
    let [acc, a2, a1, a0] =
        ["acc", "a2", "a1", "a0"].map(|name| terms.mk_var(name, Sort::bitvec(width)));
    let times = |terms: &mut TermStore, factor: u128, operand: TermId| {
        let factor = constant(terms, factor, width);
        terms.mk_bvmul(vec![factor, operand])
    };
    let mut left = times(&mut terms, 2, a1);
    let four_a2 = times(&mut terms, 4, a2);
    left = app(&mut terms, "bvadd", left, four_a2, width);
    for addend in [a0, a0, a0, a1, a2, acc] {
        left = app(&mut terms, "bvadd", left, addend, width);
    }
    let three_a0 = times(&mut terms, 3, a0);
    let three_a1 = times(&mut terms, 3, a1);
    let five_a2 = times(&mut terms, 5, a2);
    let mut right = app(&mut terms, "bvadd", three_a0, three_a1, width);
    right = app(&mut terms, "bvadd", right, five_a2, width);
    right = app(&mut terms, "bvadd", right, acc, width);
    let rendered = crate::format_term_alethe(&terms, right);
    assert!(
        rendered.contains("concat") && !rendered.contains("bvmul"),
        "elaboration no longer shifts; this test no longer pins its form: {rendered}"
    );
    let equality = eq(&mut terms, left, right);
    assert!(check_native(&terms, &[equality], &mut |_, _| true).unwrap());
    assert!(crate::recognize_native_bv_affine_identity(
        &terms,
        &[equality]
    ));
    assert!(!check(&terms, &[equality], &mut |_, _| true).unwrap());
    assert!(!crate::recognize_arith_poly_simp(&terms, &[equality]));
    assert!(!crate::recognize_arith_clause_tautology(
        &terms,
        &[equality]
    ));
    let negated = terms.mk_not_raw(equality);
    let mut proof = Proof::new();
    let assume = proof.add_assume(negated, None);
    let lemma = proof.add_theory_lemma_with_kind(
        "bv",
        vec![equality],
        TheoryLemmaKind::ArithClauseTautology,
    );
    proof.add_resolution(vec![], equality, assume, lemma);
    crate::check_proof_strict(&proof, &terms).expect("the strict checker reads the shifts");

    let six_a2 = times(&mut terms, 6, a2);
    let mut wrong = app(&mut terms, "bvadd", three_a0, three_a1, width);
    wrong = app(&mut terms, "bvadd", wrong, six_a2, width);
    wrong = app(&mut terms, "bvadd", wrong, acc, width);
    let equality = eq(&mut terms, left, wrong);
    assert!(!check_native(&terms, &[equality], &mut |_, _| true).unwrap());
    let negated = terms.mk_not_raw(equality);
    let mut proof = Proof::new();
    let assume = proof.add_assume(negated, None);
    let lemma = proof.add_theory_lemma_with_kind(
        "bv",
        vec![equality],
        TheoryLemmaKind::ArithClauseTautology,
    );
    proof.add_resolution(vec![], equality, assume, lemma);
    assert!(crate::check_proof_strict(&proof, &terms).is_err());
}

fn shifted(terms: &mut TermStore, x: TermId, top: u32, low_width: u32, low: u128) -> TermId {
    let extracted = terms.mk_app(
        Symbol::indexed("extract", vec![top, 0]),
        [x],
        Sort::bitvec(top + 1),
    );
    let low = constant(terms, low, low_width);
    terms.mk_app(
        Symbol::named("concat"),
        [extracted, low],
        Sort::bitvec(top + 1 + low_width),
    )
}

#[test]
fn elaborated_shift_answers_match_exhaustive_small_domains() {
    for width in 2..=5u32 {
        let modulus = 1u128 << width;
        for shift in 1..width {
            for factor in 1..modulus {
                let mut terms = TermStore::new();
                let x = terms.mk_var("x", Sort::bitvec(width));
                let left = shifted(&mut terms, x, width - shift - 1, shift, 0);
                let factor_term = constant(&mut terms, factor, width);
                let right = app(&mut terms, "bvmul", factor_term, x, width);
                let equality = eq(&mut terms, left, right);
                let expected = (0..modulus).all(|x| (x << shift) % modulus == factor * x % modulus);
                assert_eq!(
                    check_native(&terms, &[equality], &mut |_, _| true).unwrap(),
                    expected,
                    "{width}: x<<{shift} = {factor}*x"
                );
            }
        }
    }
}

#[test]
fn only_the_exact_elaborated_shift_shape_is_read_as_a_scalar() {
    let width = 8;
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(width));
    let wide = terms.mk_var("wide", Sort::bitvec(16));
    let doubled = app(&mut terms, "bvadd", x, x, width);
    let exact = shifted(&mut terms, x, 6, 1, 0);
    let equality = eq(&mut terms, exact, doubled);
    assert!(check_native(&terms, &[equality], &mut |_, _| true).unwrap());
    // A nonzero low literal is `2x + 1`, not `2x`.
    let plus_one = shifted(&mut terms, x, 6, 1, 1);
    let equality = eq(&mut terms, plus_one, doubled);
    assert!(!check_native(&terms, &[equality], &mut |_, _| true).unwrap());
    // Bits taken from a wider operand are not a multiple of it.
    let from_wide = shifted(&mut terms, wide, 6, 1, 0);
    let wide_low = terms.mk_app(
        Symbol::indexed("extract", vec![7, 0]),
        [wide],
        Sort::bitvec(width),
    );
    let wide_doubled = app(&mut terms, "bvadd", wide_low, wide_low, width);
    let equality = eq(&mut terms, from_wide, wide_doubled);
    assert!(!check_native(&terms, &[equality], &mut |_, _| true).unwrap());
    // Zeros in the HIGH position are a zero extension of a slice, not a shift.
    let low_bits = terms.mk_app(Symbol::indexed("extract", vec![6, 0]), [x], Sort::bitvec(7));
    let zero = constant(&mut terms, 0, 1);
    let extended = terms.mk_app(
        Symbol::named("concat"),
        [zero, low_bits],
        Sort::bitvec(width),
    );
    let equality = eq(&mut terms, extended, doubled);
    assert!(!check_native(&terms, &[equality], &mut |_, _| true).unwrap());
}

/// Carcara's `poly_simp` normalizes over the integers and keeps a monomial
/// whose coefficient reduces to zero, so an identity that needs one to vanish
/// modulo `2^width` is refuted there. Measured on carcara 1.1.0: the first two
/// equalities below are `invalid` under `poly_simp` and the last two `valid`.
/// AY printed the first as a `poly_simp` step it claimed was checkable.
#[test]
fn a_coefficient_that_wraps_to_zero_is_native_only() {
    let mut terms = TermStore::new();
    let bit = terms.mk_var("bit", Sort::bitvec(1));
    let x = terms.mk_var("x", Sort::bitvec(8));
    let doubled_bit = app(&mut terms, "bvadd", bit, bit, 1);
    let zero_bit = constant(&mut terms, 0, 1);
    let doubled = app(&mut terms, "bvadd", x, x, 8);
    let half = constant(&mut terms, 128, 8);
    let product = app(&mut terms, "bvmul", half, doubled, 8);
    let zero = constant(&mut terms, 0, 8);
    for (left, right) in [(doubled_bit, zero_bit), (product, zero)] {
        let equality = eq(&mut terms, left, right);
        assert!(check_native(&terms, &[equality], &mut |_, _| true).unwrap());
        assert!(!check(&terms, &[equality], &mut |_, _| true).unwrap());
        assert!(!crate::recognize_arith_poly_simp(&terms, &[equality]));
        assert!(!crate::recognize_arith_clause_tautology(
            &terms,
            &[equality]
        ));
    }
    let negated = terms.mk_app(Symbol::named("bvneg"), [x], Sort::bitvec(8));
    let cancelled = app(&mut terms, "bvadd", x, negated, 8);
    let three = constant(&mut terms, 3, 8);
    let minus_two = constant(&mut terms, 254, 8);
    let three_x = app(&mut terms, "bvmul", three, x, 8);
    let minus_two_x = app(&mut terms, "bvmul", minus_two, x, 8);
    let one_x = app(&mut terms, "bvadd", three_x, minus_two_x, 8);
    for (left, right) in [(cancelled, zero), (one_x, x)] {
        let equality = eq(&mut terms, left, right);
        assert!(check(&terms, &[equality], &mut |_, _| true).unwrap());
        assert!(crate::recognize_arith_poly_simp(&terms, &[equality]));
    }
}

#[test]
fn small_linear_price_keeps_full_work_and_general_product_reserve() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(64));
    let y = terms.mk_var("y", Sort::bitvec(64));
    let zero = constant(&mut terms, 0, 64);
    let sum = app(&mut terms, "bvadd", x, zero, 64);
    let identity = eq(&mut terms, sum, x);
    let mut charges = Vec::new();
    assert!(check(&terms, &[identity], &mut |w, b| {
        charges.push((w, b));
        true
    })
    .unwrap());
    assert_eq!(charges.iter().map(|x| x.0).sum::<usize>(), MAX_WORK);
    assert_eq!(
        charges.iter().map(|x| x.1).sum::<usize>(),
        SMALL_LINEAR_ALLOCATION
    );
    let xy = app(&mut terms, "bvmul", x, y, 64);
    let yx = app(&mut terms, "bvmul", y, x, 64);
    let identity = eq(&mut terms, xy, yx);
    charges.clear();
    assert!(check(&terms, &[identity], &mut |w, b| {
        charges.push((w, b));
        true
    })
    .unwrap());
    assert_eq!(charges.iter().map(|x| x.0).sum::<usize>(), MAX_WORK);
    assert_eq!(charges.iter().map(|x| x.1).sum::<usize>(), MAX_ALLOCATION);
}

#[test]
fn small_linear_price_obeys_occurrence_boundary_and_sticky_refusal() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(64));
    let one = constant(&mut terms, 1, 64);
    let mut source = x;
    for _ in 0..15 {
        source = app(&mut terms, "bvadd", source, one, 64);
    }
    let mut remaining = SMALL_LINEAR_SOURCE_NODES;
    assert!(small_linear_source(&terms, source, 64, &mut remaining));
    assert!(small_linear_source(&terms, x, 64, &mut remaining));
    assert_eq!(remaining, 0);
    source = app(&mut terms, "bvadd", source, one, 64);
    let mut remaining = SMALL_LINEAR_SOURCE_NODES;
    assert!(!small_linear_source(&terms, source, 64, &mut remaining));
    let identity = eq(&mut terms, x, x);
    for stop_at in [1, 2] {
        let mut calls = 0;
        assert!(matches!(
            check(&terms, &[identity], &mut |_, _| {
                calls += 1;
                calls != stop_at
            }),
            Err(ProofCheckError::ResourceLimit)
        ));
        assert_eq!(calls, stop_at);
    }
}
