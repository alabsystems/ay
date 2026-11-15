// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_core::term::{Symbol, TermId, TermStore};
use ay_core::{CnfClause, Sort};
use ay_sat::SatResult;

use crate::tests_support::{extract_bv, solve_fp_clauses, solve_fp_result};
use crate::FpSolver;

const WIDTH: u32 = 6;
const MASK: u64 = (1 << WIDTH) - 1;

fn pin(solver: &mut FpSolver<'_>, var: TermId, width: usize, value: u64) {
    let bits = solver
        .bitblast_bv_value(var, width)
        .expect("a BV variable bit-blasts");
    for (i, &bit) in bits.iter().enumerate() {
        let lit = if (value >> i) & 1 == 1 { bit } else { -bit };
        solver.add_clause(CnfClause::unit(lit));
    }
}

/// `op` applied to `WIDTH`-bit variables pinned to `values`, decoded from the
/// SAT model; `None` when the value encoder declined the term. The circuit
/// must also force that value: with the output additionally required to
/// differ from it, the clauses are unsatisfiable.
fn eval(symbol: Symbol, values: &[u64], result_width: u32) -> Option<u64> {
    let mut terms = TermStore::new();
    let vars: Vec<TermId> = ["x", "y"][..values.len()]
        .iter()
        .map(|name| terms.mk_var(*name, Sort::bitvec(WIDTH)))
        .collect();
    let term = terms.mk_app(symbol, vars.clone(), Sort::bitvec(result_width));
    let mut solver = FpSolver::new(&terms);
    for (&var, &value) in vars.iter().zip(values) {
        pin(&mut solver, var, WIDTH as usize, value);
    }
    let bits = solver.bitblast_bv_value(term, result_width as usize)?;
    assert!(!solver.has_encoding_gap());
    let value = extract_bv(&solve_fp_clauses(&solver), &bits);
    let differs = bits
        .iter()
        .enumerate()
        .map(|(i, &bit)| if (value >> i) & 1 == 1 { -bit } else { bit })
        .collect();
    solver.add_clause(CnfClause::new(differs));
    assert!(
        matches!(solve_fp_result(&solver), SatResult::Unsat(_)),
        "pinned operands {values:?} leave the output free beyond {value}"
    );
    Some(value)
}

fn ashr(x: u64, s: u64) -> u64 {
    let signed = ((x << (64 - WIDTH)) as i64) >> (64 - WIDTH);
    (signed >> s.min(63)) as u64 & MASK
}

fn rotate_left(x: u64, turn: u32) -> u64 {
    let turn = u64::from(turn % WIDTH);
    ((x << turn) | (x >> ((u64::from(WIDTH) - turn) % u64::from(WIDTH)))) & MASK
}

/// Every operand pair, every shift amount (including those at and past the
/// width): sign-filling shift, exactly as SMT-LIB defines `bvashr`.
#[test]
fn symbolic_bvashr_is_exact() {
    for x in 0..=MASK {
        for s in 0..=MASK {
            let got = eval(Symbol::named("bvashr"), &[x, s], WIDTH);
            assert_eq!(got, Some(ashr(x, s)), "(bvashr #b{x:06b} #b{s:06b})");
        }
    }
}

/// Every operand and index, including indices at and past the width.
#[test]
fn rotations_are_exact() {
    for turn in 0..=2 * WIDTH {
        for x in 0..=MASK {
            let left = eval(Symbol::indexed("rotate_left", vec![turn]), &[x], WIDTH);
            assert_eq!(
                left,
                Some(rotate_left(x, turn)),
                "rotate_left {turn} of {x}"
            );
            let right = eval(Symbol::indexed("rotate_right", vec![turn]), &[x], WIDTH);
            let want = rotate_left(x, (WIDTH - turn % WIDTH) % WIDTH);
            assert_eq!(right, Some(want), "rotate_right {turn} of {x}");
        }
    }
}

/// `repeat` over a symbolic operand (constant operands fold in the term
/// store): every operand, counts 2 and 3.
#[test]
fn repeat_is_exact() {
    for count in [2u32, 3] {
        for x in 0..=MASK {
            let got = eval(Symbol::indexed("repeat", vec![count]), &[x], WIDTH * count);
            let want = (0..count).fold(0u64, |acc, _| (acc << WIDTH) | x);
            assert_eq!(got, Some(want), "repeat {count} of {x}");
        }
    }
}

#[test]
fn bvcomp_is_exact() {
    for x in 0..=MASK {
        for y in 0..=MASK {
            let got = eval(Symbol::named("bvcomp"), &[x, y], 1);
            assert_eq!(got, Some(u64::from(x == y)), "(bvcomp {x} {y})");
        }
    }
}

/// Negative twin: an operand with no exact encoding (an uninterpreted
/// application) still makes each new operator decline, and the predicate
/// path then refuses rather than bit-blasting a free value.
#[test]
fn extra_ops_over_unencodable_operand_decline() {
    let ops = [
        (Symbol::named("bvashr"), 2, WIDTH),
        (Symbol::indexed("rotate_left", vec![1]), 1, WIDTH),
        (Symbol::indexed("rotate_right", vec![1]), 1, WIDTH),
        (Symbol::named("bvcomp"), 2, 1),
        (Symbol::indexed("repeat", vec![2]), 1, 2 * WIDTH),
    ];
    for (symbol, arity, result_width) in ops {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(WIDTH));
        let g_x = terms.mk_app(Symbol::named("g"), vec![x], Sort::bitvec(WIDTH));
        let args = vec![g_x; arity];
        let name = symbol.name().to_string();
        let term = terms.mk_app(symbol, args, Sort::bitvec(result_width));
        let zero = terms.mk_var("z", Sort::bitvec(result_width));
        let atom = terms.mk_app(Symbol::named("="), vec![term, zero], Sort::Bool);
        let mut solver = FpSolver::new(&terms);
        assert_eq!(
            solver.bitblast_bv_value(term, result_width as usize),
            None,
            "{name}"
        );
        assert_eq!(solver.bitblast_bv_predicate(atom), None, "{name}");
    }
}
