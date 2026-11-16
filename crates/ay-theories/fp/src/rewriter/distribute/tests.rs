// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::rewriter::tests::{app, mode, random_leaf, real, to_fp, value_of, Stream};
use crate::rewriter::FpRewriter;
use crate::tests_support::solve_fp_clauses;
use crate::{exact, FpSolver, RoundingMode};
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};
use num_rational::BigRational;

fn rm_var(terms: &mut TermStore) -> TermId {
    terms.mk_var("rm", Sort::Uninterpreted("RoundingMode".to_string()))
}

/// Whether any subterm of `term` applies `name`.
fn mentions(terms: &TermStore, term: TermId, name: &str) -> bool {
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        match terms.get(t) {
            TermData::App(sym, args) => {
                if sym.name() == name {
                    return true;
                }
                stack.extend(args);
            }
            TermData::Not(x) => stack.push(*x),
            TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
            _ => {}
        }
    }
    false
}

/// `Double_div_bad`: `1.0 / ((_ to_fp 11 53) rm 1.6) == 1.0` under a declared
/// mode is a Boolean combination of `(= rm MODE)`, with no divider left.
#[test]
fn a_constant_quotient_under_a_symbolic_mode_becomes_a_mode_test() {
    let mut terms = TermStore::new();
    let rm = rm_var(&mut terms);
    let one_real = real(&mut terms, 1, 1);
    let one = to_fp(&mut terms, (11, 53), rm, one_real);
    let eight_fifths = real(&mut terms, 8, 5);
    let divisor = to_fp(&mut terms, (11, 53), rm, eight_fifths);
    let q = app(
        &mut terms,
        "fp.div",
        vec![rm, one, divisor],
        Sort::FloatingPoint(11, 53),
    );
    let eq = app(&mut terms, "fp.eq", vec![q, one], Sort::Bool);
    let rewritten = FpRewriter::new().rewrite(&mut terms, eq);
    assert!(
        !mentions(&terms, rewritten, "fp.div"),
        "{:?}",
        terms.get(rewritten)
    );
    assert!(!mentions(&terms, rewritten, "to_fp"));
    // 1/1.6 is never 1.0 under any mode.
    assert_eq!(rewritten, terms.mk_bool(false));
}

#[test]
fn value_ites_distribute_and_symbolic_operands_are_never_duplicated() {
    let mut terms = TermStore::new();
    let f32s = Sort::FloatingPoint(8, 24);
    let rne = mode(&mut terms, RoundingMode::RNE);
    let b = terms.mk_var("b", Sort::Bool);
    let x = terms.mk_var("x", f32s.clone());
    let constant = |terms: &mut TermStore, v: i64| {
        let r = real(terms, v, 1);
        to_fp(terms, (8, 24), rne, r)
    };
    let (one, two, three) = (
        constant(&mut terms, 1),
        constant(&mut terms, 2),
        constant(&mut terms, 3),
    );
    let choice = terms.mk_ite(b, one, two);
    let sum = app(&mut terms, "fp.add", vec![rne, choice, three], f32s.clone());
    let mut rewriter = FpRewriter::new();
    let rewritten = rewriter.rewrite(&mut terms, sum);
    let TermData::Ite(c, t, e) = terms.get(rewritten).clone() else {
        panic!("{:?}", terms.get(rewritten));
    };
    assert_eq!(c, b);
    assert_eq!(
        exact::to_real(&value_of(&terms, t)),
        Some(BigRational::from_integer(4.into()))
    );
    assert_eq!(
        exact::to_real(&value_of(&terms, e)),
        Some(BigRational::from_integer(5.into()))
    );
    let symbolic = app(&mut terms, "fp.add", vec![rne, choice, x], f32s.clone());
    let rewritten_choice = rewriter.rewrite(&mut terms, choice);
    let kept = app(&mut terms, "fp.add", vec![rne, rewritten_choice, x], f32s);
    assert_eq!(rewriter.rewrite(&mut terms, symbolic), kept);
}

#[test]
fn distribution_stops_at_the_leaf_bound() {
    let mut terms = TermStore::new();
    let f16 = Sort::FloatingPoint(5, 11);
    let rm = rm_var(&mut terms);
    let rne = mode(&mut terms, RoundingMode::RNE);
    let leaf = |terms: &mut TermStore, v: i64| {
        let r = real(terms, v, 1);
        to_fp(terms, (5, 11), rne, r)
    };
    // (ite b1 1 2) and (ite b2 3 4) under a symbolic mode: 2 * 2 * 5 = 20 leaves.
    let mut args = vec![rm];
    for (i, (p, q)) in [(1, 2), (3, 4)].into_iter().enumerate() {
        let b = terms.mk_var(format!("b{i}"), Sort::Bool);
        let (p, q) = (leaf(&mut terms, p), leaf(&mut terms, q));
        args.push(terms.mk_ite(b, p, q));
    }
    let within = app(&mut terms, "fp.div", args.clone(), f16.clone());
    let rewritten = FpRewriter::new().rewrite(&mut terms, within);
    assert!(!mentions(&terms, rewritten, "fp.div"));
    // A third choice for the fma addend makes 2 * 2 * 2 * 5 = 40 > 32.
    let b = terms.mk_var("b2", Sort::Bool);
    let (p, q) = (leaf(&mut terms, 5), leaf(&mut terms, 6));
    args.push(terms.mk_ite(b, p, q));
    let beyond = app(&mut terms, "fp.fma", args, f16);
    let rewritten = FpRewriter::new().rewrite(&mut terms, beyond);
    assert!(
        mentions(&terms, rewritten, "fp.fma"),
        "left for the bit-blaster"
    );
}

fn random_value_tree(
    terms: &mut TermStore,
    stream: &mut Stream,
    format: (u32, u32),
    conditions: &[TermId],
    rm: TermId,
    depth: u32,
) -> TermId {
    let sort = Sort::FloatingPoint(format.0, format.1);
    if depth == 0 || stream.next() % 3 == 0 {
        if stream.next() % 2 == 0 {
            let c = conditions[(stream.next() % conditions.len() as u64) as usize];
            let (a, b) = (
                random_leaf(terms, stream, format),
                random_leaf(terms, stream, format),
            );
            return terms.mk_ite(c, a, b);
        }
        return random_leaf(terms, stream, format);
    }
    let modes = [RoundingMode::RNE, RoundingMode::RTP, RoundingMode::RTZ];
    let mode_term = if stream.next() % 2 == 0 {
        rm
    } else {
        mode(terms, modes[(stream.next() % 3) as usize])
    };
    let mut sub =
        |terms: &mut TermStore| random_value_tree(terms, stream, format, conditions, rm, depth - 1);
    let (a, b) = (sub(terms), sub(terms));
    match stream.next() % 4 {
        0 => app(terms, "fp.add", vec![mode_term, a, b], sort),
        1 => app(terms, "fp.mul", vec![mode_term, a, b], sort),
        2 => app(terms, "fp.div", vec![mode_term, a, b], sort),
        _ => app(terms, "fp.sqrt", vec![mode_term, a], sort),
    }
}

/// The truth of a Boolean term under pinned conditions and mode, by the
/// bit-blaster.
fn bit_blasted_truth(
    terms: &TermStore,
    term: TermId,
    conditions: &[(TermId, bool)],
    rm: TermId,
    mode_value: RoundingMode,
) -> bool {
    let mut solver = FpSolver::new(terms);
    let out = solver.encode_bool_condition(term);
    for &(c, value) in conditions {
        let lit = solver.encode_bool_condition(c);
        solver.add_clause(ay_core::CnfClause::unit(if value { lit } else { -lit }));
    }
    if let Some(bits) = solver.rm_terms().get(&rm).copied() {
        let code = crate::RM_ORDER
            .iter()
            .position(|&m| m == mode_value)
            .expect("a mode");
        for (i, &bit) in bits.bits().iter().enumerate() {
            let set = (code >> i) & 1 == 1;
            solver.add_clause(ay_core::CnfClause::unit(if set { bit } else { -bit }));
        }
    }
    assert!(!solver.has_encoding_gap());
    let model = solve_fp_clauses(&solver);
    crate::tests_support::extract_lit(&model, out)
}

#[test]
fn distribution_preserves_the_truth_of_every_case() {
    let mut stream = Stream(0xC0FF_EE00_1234_5678);
    let format = (3, 4);
    for _ in 0..60 {
        let mut terms = TermStore::new();
        let rm = rm_var(&mut terms);
        let conditions: Vec<TermId> = (0..2)
            .map(|i| terms.mk_var(format!("c{i}"), Sort::Bool))
            .collect();
        let a = random_value_tree(&mut terms, &mut stream, format, &conditions, rm, 2);
        let b = random_value_tree(&mut terms, &mut stream, format, &conditions, rm, 2);
        let predicate = ["fp.eq", "fp.lt", "fp.leq", "="][(stream.next() % 4) as usize];
        let original = app(&mut terms, predicate, vec![a, b], Sort::Bool);
        let rewritten = FpRewriter::new().rewrite(&mut terms, original);
        for mode_value in crate::RM_ORDER {
            for bits in 0..4u32 {
                let pins: Vec<(TermId, bool)> = conditions
                    .iter()
                    .enumerate()
                    .map(|(i, &c)| (c, (bits >> i) & 1 == 1))
                    .collect();
                assert_eq!(
                    bit_blasted_truth(&terms, original, &pins, rm, mode_value),
                    bit_blasted_truth(&terms, rewritten, &pins, rm, mode_value),
                    "{predicate} under {mode_value:?}, conditions {bits:02b}"
                );
            }
        }
    }
}
