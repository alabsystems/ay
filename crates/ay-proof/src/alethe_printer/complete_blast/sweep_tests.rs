// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The swept refutation (`sweep.rs`) on the shapes whose monolithic
//! refutation transported past the document budget.

use super::*;

fn power_of_two_fold(width: u32, divide: bool) -> Option<String> {
    let mut f = Fixture::new();
    let x = f.bv("x", width);
    let four = f.constant(4, width);
    let two = f.constant(2, width);
    let (left, right) = if divide {
        (
            f.op("bvudiv", &[x, four], width),
            f.op("bvlshr", &[x, two], width),
        )
    } else {
        (
            f.op("bvmul", &[four, x], width),
            f.op("bvshl", &[x, two], width),
        )
    };
    let equality = f.equals(left, right);
    let assertion = f.not(equality);
    f.refute(assertion)
}

/// `x * 4 = x << 2` at 64 bits: about 80 MB monolithically, over budget.
#[test]
fn a_sixty_four_bit_power_of_two_product_is_swept_into_budget() {
    let document = power_of_two_fold(64, false).expect("the swept refutation fits the budget");
    assert_complete(&document);
    assert!(document.len() < 8 * 1024 * 1024, "{} bytes", document.len());
}

/// `x / 4 = x >> 2`: the checker's divider against a shift.
#[test]
fn a_power_of_two_quotient_is_swept_into_budget() {
    for width in [8, 32] {
        let document =
            power_of_two_fold(width, true).unwrap_or_else(|| panic!("{width}-bit quotient"));
        assert_complete(&document);
        assert!(
            document.len() < 16 * 1024 * 1024,
            "{width}-bit: {} bytes",
            document.len()
        );
    }
}

/// A false lemma stays refused: the sweep never closes a satisfiable CNF.
#[test]
fn a_false_power_of_two_identity_is_never_swept_closed() {
    let mut f = Fixture::new();
    let x = f.bv("x", 32);
    let four = f.constant(4, 32);
    let three = f.constant(3, 32);
    let left = f.op("bvudiv", &[x, four], 32);
    let right = f.op("bvlshr", &[x, three], 32);
    let equality = f.equals(left, right);
    let assertion = f.not(equality);
    assert!(f.refute(assertion).is_none());
}

/// A POSITIVE unit lemma `(cl P)` is refuted through the gate-level negation
/// of `P` — the shape a definitional `bvsdiv` query records — and a false one
/// is still refused.
#[test]
fn a_positive_unit_lemma_is_refuted_through_its_negation() {
    let mut f = Fixture::new();
    let x = f.bv("x", 8);
    let doubled = f.op("bvadd", &[x, x], 8);
    let two = f.constant(2, 8);
    let product = f.op("bvmul", &[two, x], 8);
    let equality = f.equals(doubled, product);
    let printer = AlethePrinter::new(&f.terms);
    let document = printer
        .format_bv_complete_blast_refutation(ProofId(1), &[equality])
        .expect("x + x = 2x renders as a positive lemma");
    assert_complete(&document);
    // `x xor x = 0`, once listed as a near miss no lowering could print.
    let cancelled = f.op("bvxor", &[x, x], 8);
    let zero = f.constant(0, 8);
    let cancellation = f.equals(cancelled, zero);
    let printer = AlethePrinter::new(&f.terms);
    let document = printer
        .format_bv_complete_blast_refutation(ProofId(1), &[cancellation])
        .expect("x xor x = 0 renders as a positive lemma");
    assert_complete(&document);
    let wrong = f.equals(doubled, x);
    let printer = AlethePrinter::new(&f.terms);
    assert!(printer
        .format_bv_complete_blast_refutation(ProofId(1), &[wrong])
        .is_none());
}

/// The whole-query lemma of external-codegen's `(a / b) ^ c` gate obligation: its
/// AArch64 lowering's divide-by-zero guard `ite(b = 0, 0, a / b)` against the
/// plain quotient, under the gate's `b != 0` precondition. The operands are
/// the `width`-bit words of 64-bit registers, as the gate reads `W0..W2` out
/// of `X0..X2`.
fn guarded_quotient_lemma(width: u32) -> Option<String> {
    let mut f = Fixture::new();
    let word = |f: &mut Fixture, name: &str| {
        let register = f.bv(name, 64);
        if width == 64 {
            register
        } else {
            f.indexed("extract", vec![width - 1, 0], register, width)
        }
    };
    let (a, b, c) = (word(&mut f, "X0"), word(&mut f, "X1"), word(&mut f, "X2"));
    let zero = f.constant(0, width);
    let quotient = f.op("bvudiv", &[a, b], width);
    let divisor_is_zero = f.equals(zero, b);
    let lowered = f.terms.mk_ite_raw(divisor_is_zero, zero, quotient);
    let machine = f.op("bvxor", &[lowered, c], width);
    let intended = f.op("bvxor", &[quotient, c], width);
    let equality = f.equals(machine, intended);
    let differ = f.not(equality);
    let nonzero = f.not(divisor_is_zero);
    let assertion = f.predicate("and", differ, nonzero);
    f.refute(assertion)
}

/// A large circuit whose two sides SHARE their arithmetic refutes directly.
/// The lemma blasts one divider under both sides, past `SWEEP_FIRST_GATES`
/// (17,531 gates at 32 bits, 68,651 at 64), and its root refutes in 129 and
/// 393 conflicts. Swept first, the divider's candidates used up the sweep's
/// wall before its closing refutation ran, at every render of the lemma, and
/// external-codegen's gate answered `unknown` at its 120 s budget.
#[test]
fn a_miter_over_one_shared_divider_refutes_without_sweeping() {
    for width in [32, 64] {
        let document = guarded_quotient_lemma(width)
            .unwrap_or_else(|| panic!("the {width}-bit guarded lemma is refutable"));
        assert_complete(&document);
    }
}

/// A sweep refutes its CNF over the gates the CNF was PLANNED over. A case
/// split's chain shortcuts mint gates after the plan (`ite.rs`); the sweep's
/// refutation, and so the key it is retained under across renders
/// (`transport.rs`), must not depend on whether a render minted them.
#[test]
fn a_sweep_reads_only_the_gates_its_cnf_was_planned_over() {
    let mut circuit = Circuit::new("@t_".to_string());
    let x = circuit.atom("x".to_string());
    let y = circuit.atom("y".to_string());
    let both = circuit.and(vec![x, y]);
    let lit = |reference: SRef, negative: bool| {
        crate::sat_sweep::literal(reference.gate as usize, negative)
    };
    // `(and x y)` with `x` false, the conjunction the transported root.
    let cnf = vec![
        vec![lit(both, true), lit(x, false)],
        vec![lit(both, true), lit(y, false)],
        vec![lit(both, false), lit(x, true), lit(y, true)],
        vec![lit(x, true)],
        vec![lit(both, false)],
    ];
    let root = cnf.len() as u64;
    let planned = circuit.len();
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    let before =
        sweep::refute_planned(&printer, &circuit, planned, &[], &cnf, root).expect("refuted");
    let _minted = circuit.or(vec![x, y]);
    let after =
        sweep::refute_planned(&printer, &circuit, planned, &[], &cnf, root).expect("refuted");
    assert_eq!(before.num_vars, planned);
    assert_eq!(before, after);
    // A count past the circuit is refused, never read out of bounds.
    assert!(
        sweep::refute_planned(&printer, &circuit, circuit.len() + 1, &[], &cnf, root).is_none()
    );
    // A caller that has stopped is refuted nothing.
    let stopped =
        AlethePrinter::new(&terms).asking_complete_blast(CompleteBlastAsk::AskedUntil(&|| true));
    assert!(sweep::refute_planned(&stopped, &circuit, planned, &[], &cnf, root).is_none());
}

#[test]
fn a_blast_lane_requires_both_its_emission_owner_and_support_question() {
    let terms = TermStore::new();
    let mut circuit = Circuit::new("@ay_merged_owners_".to_string());
    circuit.constant(false);
    let cnf = vec![
        vec![crate::sat_sweep::literal(0, true)],
        vec![crate::sat_sweep::literal(0, false)],
    ];
    for emission_allowed in [false, true] {
        for question_stopped in [false, true] {
            let mut emission = || emission_allowed;
            let stop = || question_stopped;
            let printer = AlethePrinter::new(&terms)
                .with_emission_progress(&mut emission)
                .asking_complete_blast(CompleteBlastAsk::AskedUntil(&stop));
            let expected = emission_allowed && !question_stopped;
            let direct = sweep::refute_directly(&printer, &circuit, &[], &cnf, 2);
            let swept = sweep::refute(&printer, &circuit, &[], &cnf, 2);
            assert_eq!(direct.is_some(), expected);
            assert_eq!(swept.is_some(), expected);
            if let (Some(direct), Some(swept)) = (direct, swept) {
                direct.validate().expect("direct independent replay");
                swept.validate().expect("sweep independent replay");
            }
        }
    }
}

#[test]
fn a_nested_printer_cannot_reset_the_support_question() {
    let terms = TermStore::new();
    let stop = || true;
    for ask in [
        CompleteBlastAsk::NotAsked,
        CompleteBlastAsk::AskedUntil(&stop),
    ] {
        let parent = AlethePrinter::new(&terms).asking_complete_blast(ask);
        let nested = AlethePrinter::new(&terms).with_parent_emission_progress(&parent);
        assert!(nested.complete_blast_progress().is_none());
    }
}
