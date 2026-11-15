// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A symbolic mode pinned to `m` computes what mode `m` computes; an unpinned
//! one ranges over exactly the five modes.

use super::*;
use crate::tests_support::{extract_fp, extract_lit, solve_fp_result};
use crate::{exact, FpModelValue};
use ay_core::term::Symbol;
use ay_core::{Sort, TermStore};
use ay_sat::SatResult;
use num_rational::BigRational;

fn rm_sort() -> Sort {
    Sort::Uninterpreted("RoundingMode".to_string())
}

#[test]
fn rounding_names_keep_free_mode_variables_symbolic() {
    for name in ["RNE", "RTP", "roundNearestTiesToEven"] {
        for mode in RM_ORDER {
            let mut terms = TermStore::new();
            let free = terms.mk_var(name, rm_sort());
            let literal = terms.mk_app(Symbol::named(mode.name()), [], rm_sort());
            let mut solver = FpSolver::new(&terms);
            let equality = solver.bitblast_rm_eq(free, literal);
            solver.add_clause(CnfClause::unit(equality));
            assert!(!solver.has_encoding_gap());
            assert!(
                matches!(solve_fp_result(&solver), SatResult::Sat(_)),
                "{name} = {mode:?}"
            );
        }
    }
}

#[test]
fn rounding_names_do_not_hide_a_malformed_operand_sort() {
    let mut terms = TermStore::new();
    let malformed = terms.mk_app(Symbol::named("RNE"), [], Sort::Bool);
    let literal = terms.mk_app(Symbol::named("RTP"), [], rm_sort());
    let mut solver = FpSolver::new(&terms);
    let _ = solver.bitblast_rm_eq(malformed, literal);
    assert!(solver.has_encoding_gap());
}

#[test]
fn rounding_names_do_not_assign_a_literal_to_registered_constants() {
    for mode in RM_ORDER {
        let mut terms = TermStore::new();
        let free = terms.mk_app(Symbol::named("RNE"), [], rm_sort());
        let literal = terms.mk_app(Symbol::named(mode.name()), [], rm_sort());
        terms.register_declared_function("RNE");
        let mut solver = FpSolver::new(&terms);
        let equality = solver.bitblast_rm_eq(free, literal);
        solver.add_clause(CnfClause::unit(equality));
        assert!(!solver.has_encoding_gap());
        assert!(
            matches!(solve_fp_result(&solver), SatResult::Sat(_)),
            "mode {mode:?}"
        );
    }
}

fn pin_mode(solver: &mut FpSolver<'_>, rm: TermId, mode: RoundingMode) {
    let bits = solver.rm_terms()[&rm].bits();
    for (i, &bit) in bits.iter().enumerate() {
        let set = (code(mode) >> i) & 1 == 1;
        solver.add_clause(CnfClause::unit(if set { bit } else { -bit }));
    }
}

fn pin_fp(solver: &mut FpSolver<'_>, term: TermId, (s, e, m): (bool, u64, u128)) {
    let fp = solver.get_fp(term);
    solver.add_clause(CnfClause::unit(if s { fp.sign } else { -fp.sign }));
    for (i, &bit) in fp.exponent.iter().enumerate() {
        solver.add_clause(CnfClause::unit(if (e >> i) & 1 == 1 { bit } else { -bit }));
    }
    for (i, &bit) in fp.significand.iter().enumerate() {
        solver.add_clause(CnfClause::unit(if (m >> i) & 1 == 1 { bit } else { -bit }));
    }
}

fn patterns(eb: u32, sb: u32) -> Vec<(bool, u64, u128)> {
    let mut all = Vec::new();
    for s in [false, true] {
        for e in 0..(1u64 << eb) {
            for m in 0..(1u128 << (sb - 1)) {
                all.push((s, e, m));
            }
        }
    }
    all
}

fn value((eb, sb): (u32, u32), (s, e, m): (bool, u64, u128)) -> FpModelValue {
    FpModelValue::from_fields(s, e, m, eb, sb).expect("small format")
}

/// `name(rm, x[, y])` under a symbolic `rm` pinned to `mode`, on pinned
/// operands.
fn symbolic(
    format: (u32, u32),
    name: &str,
    mode: RoundingMode,
    operands: &[(bool, u64, u128)],
) -> FpModelValue {
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(format.0, format.1);
    let rm = terms.mk_var("rm", rm_sort());
    let vars: Vec<TermId> = ["x", "y"]
        .iter()
        .take(operands.len())
        .map(|n| terms.mk_var(*n, sort.clone()))
        .collect();
    let mut args = vec![rm];
    args.extend(&vars);
    let op = terms.mk_app(Symbol::named(name), args, sort);
    let mut solver = FpSolver::new(&terms);
    let result = solver.get_fp(op);
    assert!(!solver.has_encoding_gap());
    pin_mode(&mut solver, rm, mode);
    for (&var, &bits) in vars.iter().zip(operands) {
        pin_fp(&mut solver, var, bits);
    }
    let SatResult::Sat(model) = solve_fp_result(&solver) else {
        panic!("a pinned circuit is satisfiable");
    };
    let (s, e, m) = extract_fp(&model, &result);
    value(format, (s, e, u128::from(m)))
}

fn expected(name: &str, mode: RoundingMode, args: &[FpModelValue]) -> Option<FpModelValue> {
    match name {
        "fp.add" => exact::add(mode, &args[0], &args[1]),
        "fp.sub" => exact::sub(mode, &args[0], &args[1]),
        "fp.mul" => exact::mul(mode, &args[0], &args[1]),
        "fp.div" => exact::div(mode, &args[0], &args[1]),
        "fp.sqrt" => exact::sqrt(mode, &args[0]),
        "fp.roundToIntegral" => exact::round_to_integral(mode, &args[0]),
        other => panic!("{other}"),
    }
}

#[test]
fn a_pinned_symbolic_mode_rounds_like_the_literal_mode() {
    let format = (2, 3);
    let all = patterns(format.0, format.1);
    for name in ["fp.add", "fp.sub", "fp.mul", "fp.div"] {
        for mode in RM_ORDER {
            for (i, &x) in all.iter().enumerate() {
                // Every x against a third of the ys keeps this to seconds.
                for &y in all.iter().skip(i % 3).step_by(3) {
                    let args = [value(format, x), value(format, y)];
                    let Some(want) = expected(name, mode, &args) else {
                        continue;
                    };
                    let got = symbolic(format, name, mode, &[x, y]);
                    assert_eq!(
                        exact::same_element(&got, &want),
                        Some(true),
                        "{name} {mode:?} {args:?}: {got:?} vs {want:?}"
                    );
                }
            }
        }
    }
    for name in ["fp.sqrt", "fp.roundToIntegral"] {
        for format in [(2, 3), (3, 4)] {
            for mode in RM_ORDER {
                for &x in &patterns(format.0, format.1) {
                    let Some(want) = expected(name, mode, &[value(format, x)]) else {
                        continue;
                    };
                    let got = symbolic(format, name, mode, &[x]);
                    assert_eq!(
                        exact::same_element(&got, &want),
                        Some(true),
                        "{name} {mode:?} {x:?}"
                    );
                }
            }
        }
    }
}

/// `(= (fp.roundToIntegral rm 2.5) 3.0)` holds exactly under RNA and RTP.
#[test]
fn an_unpinned_mode_ranges_over_exactly_the_five_modes() {
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(8, 24);
    let rm = terms.mk_var("rm", rm_sort());
    let x = terms.mk_var("x", sort.clone());
    let rti = terms.mk_app(Symbol::named("fp.roundToIntegral"), vec![rm, x], sort);
    let mut solver = FpSolver::new(&terms);
    let result = solver.get_fp(rti);
    let bits = |v: f32| {
        let b = v.to_bits();
        (
            b >> 31 == 1,
            u64::from((b >> 23) & 0xff),
            u128::from(b & 0x7f_ffff),
        )
    };
    pin_fp(&mut solver, x, bits(2.5));
    let three = bits(3.0);
    let rm_bits = solver.rm_terms()[&rm];
    solver.add_clause(CnfClause::unit(if three.0 {
        result.sign
    } else {
        -result.sign
    }));
    for (i, &bit) in result.exponent.iter().enumerate() {
        let set = (three.1 >> i) & 1 == 1;
        solver.add_clause(CnfClause::unit(if set { bit } else { -bit }));
    }
    for (i, &bit) in result.significand.iter().enumerate() {
        let set = (three.2 >> i) & 1 == 1;
        solver.add_clause(CnfClause::unit(if set { bit } else { -bit }));
    }
    let mut seen = Vec::new();
    loop {
        let model = match solve_fp_result(&solver) {
            SatResult::Sat(model) => model,
            _ => break,
        };
        let mode = rm_bits
            .decode(|lit| Some(extract_lit(&model, lit)))
            .expect("the bits are one of the five codes");
        seen.push(mode);
        // Block this mode and look for another.
        let block = rm_bits
            .bits()
            .iter()
            .enumerate()
            .map(|(i, &bit)| {
                if (code(mode) >> i) & 1 == 1 {
                    -bit
                } else {
                    bit
                }
            })
            .collect();
        solver.add_clause(CnfClause::new(block));
    }
    seen.sort_by_key(|m| code(*m));
    assert_eq!(seen, vec![RoundingMode::RNA, RoundingMode::RTP]);
}

#[test]
fn the_three_bits_admit_no_sixth_mode() {
    let mut terms = TermStore::new();
    let rm = terms.mk_var("rm", rm_sort());
    let rne = terms.mk_app(Symbol::named("RNE"), vec![], rm_sort());
    let mut solver = FpSolver::new(&terms);
    let _ = solver.bitblast_rm_eq(rm, rne);
    let bits = solver.rm_terms()[&rm].bits();
    for code in 5..8u32 {
        let mut pinned = FpSolver::new(&terms);
        let _ = pinned.bitblast_rm_eq(rm, rne);
        for (i, &bit) in bits.iter().enumerate() {
            let set = (code >> i) & 1 == 1;
            pinned.add_clause(CnfClause::unit(if set { bit } else { -bit }));
        }
        assert!(
            matches!(solve_fp_result(&pinned), SatResult::Unsat(_)),
            "code {code}"
        );
    }
}

#[test]
fn an_ite_of_modes_and_a_constant_conversion_follow_the_selected_mode() {
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(11, 53);
    let b = terms.mk_var("b", Sort::Bool);
    let rtp = terms.mk_app(Symbol::named("RTP"), vec![], rm_sort());
    let rtz = terms.mk_app(Symbol::named("RTZ"), vec![], rm_sort());
    let rm = terms.mk_ite(b, rtp, rtz);
    let tenth = terms.mk_rational(BigRational::new(1.into(), 10.into()));
    let conv = terms.mk_app(
        Symbol::indexed("to_fp", vec![11, 53]),
        vec![rm, tenth],
        sort,
    );
    for (b_value, mode) in [(true, RoundingMode::RTP), (false, RoundingMode::RTZ)] {
        let mut solver = FpSolver::new(&terms);
        let result = solver.get_fp(conv);
        assert!(!solver.has_encoding_gap());
        let lit = solver.encode_bool_condition(b);
        solver.add_clause(CnfClause::unit(if b_value { lit } else { -lit }));
        let SatResult::Sat(model) = solve_fp_result(&solver) else {
            panic!("satisfiable");
        };
        let (s, e, m) = extract_fp(&model, &result);
        let got = value((11, 53), (s, e, u128::from(m)));
        let want = exact::to_fp_from_rational(mode, &BigRational::new(1.into(), 10.into()), 11, 53)
            .expect("binary64");
        assert_eq!(exact::same_element(&got, &want), Some(true), "{mode:?}");
    }
}

fn symbolic_operand(solver: &mut FpSolver<'_>, terms: &TermStore, rm: TermId) -> RmOperand {
    let rne = terms
        .find_app(&Symbol::named("RNE"), &[])
        .expect("the test interned RNE");
    let _ = solver.bitblast_rm_eq(rm, rne);
    RmOperand::Symbolic(solver.rm_terms()[&rm])
}

#[test]
fn to_ubv_rounds_under_the_pinned_mode_and_relates_nan_sites_only_under_equal_modes() {
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(8, 24);
    let _rne = terms.mk_app(Symbol::named("RNE"), vec![], rm_sort());
    let (r1, r2) = (terms.mk_var("r1", rm_sort()), terms.mk_var("r2", rm_sort()));
    let x = terms.mk_var("x", sort);
    let two_and_a_half = (false, 128, 0x20_0000);
    for (mode, want) in [
        (RoundingMode::RNE, 2),
        (RoundingMode::RNA, 3),
        (RoundingMode::RTP, 3),
        (RoundingMode::RTN, 2),
        (RoundingMode::RTZ, 2),
    ] {
        let mut solver = FpSolver::new(&terms);
        let rm = symbolic_operand(&mut solver, &terms, r1);
        let bits = solver.bitblast_to_bv(x, rm, 8, false);
        pin_fp(&mut solver, x, two_and_a_half);
        pin_mode(&mut solver, r1, mode);
        let SatResult::Sat(model) = solve_fp_result(&solver) else {
            panic!("satisfiable");
        };
        assert_eq!(
            crate::tests_support::extract_bv(&model, &bits),
            want,
            "{mode:?}"
        );
    }
    // On NaN both results are unspecified: they must agree when the modes do,
    // and may differ when the modes differ.
    for (modes_equal, satisfiable) in [(true, false), (false, true)] {
        let mut solver = FpSolver::new(&terms);
        let (m1, m2) = (
            symbolic_operand(&mut solver, &terms, r1),
            symbolic_operand(&mut solver, &terms, r2),
        );
        let u1 = solver.bitblast_to_bv(x, m1, 8, false);
        let u2 = solver.bitblast_to_bv(x, m2, 8, false);
        pin_fp(&mut solver, x, (false, 255, 1));
        let same_mode = solver.bitblast_rm_eq(r1, r2);
        solver.add_clause(CnfClause::unit(if modes_equal {
            same_mode
        } else {
            -same_mode
        }));
        let same_value = solver.make_bits_equal(&u1, &u2);
        solver.add_clause(CnfClause::unit(-same_value));
        let result = solve_fp_result(&solver);
        assert_eq!(
            matches!(result, SatResult::Sat(_)),
            satisfiable,
            "modes equal: {modes_equal}"
        );
    }
}

/// `fp.fma` (whose exact-zero sign has its own symbolic branch) and the
/// FP-to-FP and signed-integer conversions under a pinned symbolic mode.
#[test]
fn fma_and_conversions_under_a_pinned_symbolic_mode_match_the_exact_values() {
    let format = (2, 3);
    let all = patterns(format.0, format.1);
    let mut state = 0x2545_F491_4F6C_DD1Du64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for _ in 0..600 {
        let pick = |n: u64| all[(n % all.len() as u64) as usize];
        let (x, y, z) = (pick(next()), pick(next()), pick(next()));
        let mode = RM_ORDER[(next() % 5) as usize];
        let args: Vec<FpModelValue> = [x, y, z].iter().map(|&p| value(format, p)).collect();
        let want = exact::fma(mode, &args[0], &args[1], &args[2]).expect("defined");
        let mut terms = TermStore::new();
        let sort = Sort::FloatingPoint(format.0, format.1);
        let rm = terms.mk_var("rm", rm_sort());
        let vars: Vec<TermId> = ["x", "y", "z"]
            .iter()
            .map(|n| terms.mk_var(*n, sort.clone()))
            .collect();
        let op = terms.mk_app(
            Symbol::named("fp.fma"),
            vec![rm, vars[0], vars[1], vars[2]],
            sort,
        );
        let mut solver = FpSolver::new(&terms);
        let result = solver.get_fp(op);
        pin_mode(&mut solver, rm, mode);
        for (&var, &bits) in vars.iter().zip(&[x, y, z]) {
            pin_fp(&mut solver, var, bits);
        }
        let SatResult::Sat(model) = solve_fp_result(&solver) else {
            panic!("satisfiable");
        };
        let (s, e, m) = extract_fp(&model, &result);
        let got = value(format, (s, e, u128::from(m)));
        assert_eq!(
            exact::same_element(&got, &want),
            Some(true),
            "fma {mode:?} {args:?}"
        );
    }
    // FP-to-FP narrowing (3,4) -> (2,3), every source value, every mode.
    for mode in RM_ORDER {
        for &x in &patterns(3, 4) {
            let source = value((3, 4), x);
            let want = exact::to_fp_from_fp(mode, &source, 2, 3).expect("defined");
            let mut terms = TermStore::new();
            let rm = terms.mk_var("rm", rm_sort());
            let var = terms.mk_var("x", Sort::FloatingPoint(3, 4));
            let conv = terms.mk_app(
                Symbol::indexed("to_fp", vec![2, 3]),
                vec![rm, var],
                Sort::FloatingPoint(2, 3),
            );
            let mut solver = FpSolver::new(&terms);
            let result = solver.get_fp(conv);
            pin_mode(&mut solver, rm, mode);
            pin_fp(&mut solver, var, x);
            let SatResult::Sat(model) = solve_fp_result(&solver) else {
                panic!("satisfiable");
            };
            let (s, e, m) = extract_fp(&model, &result);
            let got = value((2, 3), (s, e, u128::from(m)));
            assert_eq!(
                exact::same_element(&got, &want),
                Some(true),
                "{mode:?} {source:?}"
            );
        }
    }
}
