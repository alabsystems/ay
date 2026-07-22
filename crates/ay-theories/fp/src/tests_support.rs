// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_sat::{Literal, SatResult, Solver};

pub(crate) fn solve_fp_result(solver: &FpSolver<'_>) -> SatResult {
    let num_vars = solver.num_vars() as usize;
    let mut sat_solver = Solver::new(num_vars);

    for clause in solver.clauses() {
        let lits: Vec<Literal> = clause
            .literals()
            .iter()
            .map(|&l| Literal::from_dimacs(l))
            .collect();
        sat_solver.add_clause(lits);
    }

    sat_solver.solve().into_inner()
}

pub(crate) fn solve_fp_clauses(solver: &FpSolver<'_>) -> Vec<bool> {
    match solve_fp_result(solver) {
        SatResult::Sat(model) => model,
        SatResult::Unsat(_) => panic!("Expected SAT, got UNSAT"),
        SatResult::Unknown => panic!("Expected SAT, got Unknown"),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

pub(crate) fn extract_lit(model: &[bool], lit: CnfLit) -> bool {
    let var_idx = (lit.unsigned_abs() - 1) as usize;
    let val = model.get(var_idx).copied().unwrap_or(false);
    if lit > 0 {
        val
    } else {
        !val
    }
}

pub(crate) fn extract_bv(model: &[bool], bits: &[CnfLit]) -> u64 {
    let mut value = 0u64;
    for (i, &bit) in bits.iter().enumerate() {
        if extract_lit(model, bit) && i < 64 {
            value |= 1u64 << i;
        }
    }
    value
}

pub(crate) fn extract_fp(model: &[bool], fp: &FpDecomposed) -> (bool, u64, u64) {
    let sign = extract_lit(model, fp.sign);
    let exp = extract_bv(model, &fp.exponent);
    let sig = extract_bv(model, &fp.significand);
    (sign, exp, sig)
}

pub(crate) fn make_concrete_f16(
    solver: &mut FpSolver<'_>,
    sign: bool,
    exp: u32,
    sig: u32,
) -> FpDecomposed {
    let fp = solver.fresh_decomposed(FpPrecision::Float16);
    solver.constrain_constant(&fp, sign, |i| (exp >> i) & 1 == 1, |i| (sig >> i) & 1 == 1);
    fp
}
