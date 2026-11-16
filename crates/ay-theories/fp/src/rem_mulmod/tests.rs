// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Symbolic CNF checks against independent small unsigned integer arithmetic.

use super::*;
use ay_core::TermStore;
use std::time::{Duration, Instant};

mod ownership;

struct Owner {
    end: Instant,
    work: usize,
    stopped: bool,
    cnf_limit: Option<(u32, usize)>,
    trace: Vec<crate::FpBuildProgress>,
}

impl Owner {
    fn new() -> Self {
        Self {
            end: Instant::now() + Duration::from_secs(20),
            work: 100_000_000,
            stopped: false,
            cnf_limit: None,
            trace: Vec::new(),
        }
    }

    fn charge(&mut self, units: usize) -> Result<(), ()> {
        if self.stopped || Instant::now() >= self.end || units > self.work {
            self.stopped = true;
            return Err(());
        }
        self.work -= units;
        Ok(())
    }
}

impl BuildControl for Owner {
    type Error = ();

    fn checkpoint(&mut self, progress: crate::FpBuildProgress) -> Result<(), ()> {
        self.charge(1)?;
        if self.cnf_limit.is_some_and(|(variables, clauses)| {
            progress.variables > variables || progress.clauses > clauses
        }) {
            self.stopped = true;
            return Err(());
        }
        assert!(i32::try_from(progress.variables).is_ok());
        self.trace.push(progress);
        Ok(())
    }
}

fn fresh(solver: &mut FpSolver<'_>, width: usize) -> Vec<CnfLit> {
    (0..width).map(|_| solver.fresh_var()).collect()
}

fn pins(bits: &[CnfLit], value: u64) -> Vec<(CnfLit, bool)> {
    bits.iter()
        .enumerate()
        .map(|(i, &lit)| (lit, value >> i & 1 != 0))
        .collect()
}

fn literal(model: &[Option<bool>], lit: CnfLit) -> Option<bool> {
    assert!(lit != 0 && lit != i32::MIN);
    model[(lit.unsigned_abs() - 1) as usize].map(|value| value == (lit > 0))
}

fn clause(
    lits: &[CnfLit],
    model: &mut [Option<bool>],
    changed: &mut bool,
    owner: &mut Owner,
) -> bool {
    owner.charge(lits.len() + 1).unwrap();
    let mut open = 0;
    let mut pending = 0;
    for &lit in lits {
        match literal(model, lit) {
            Some(true) => return true,
            Some(false) => {}
            None => {
                open += 1;
                pending = lit;
            }
        }
    }
    if open == 0 {
        return false;
    }
    if open == 1 {
        model[(pending.unsigned_abs() - 1) as usize] = Some(pending > 0);
        *changed = true;
    }
    true
}

fn propagate(
    solver: &FpSolver<'_>,
    inputs: &[(CnfLit, bool)],
    extra: Option<&[CnfLit]>,
    owner: &mut Owner,
) -> Option<Vec<Option<bool>>> {
    owner
        .charge(solver.num_vars() as usize + inputs.len())
        .unwrap();
    let mut model = vec![None; solver.num_vars() as usize];
    for &(lit, value) in inputs {
        assert!(lit > 0);
        model[(lit - 1) as usize] = Some(value);
    }
    loop {
        let mut changed = false;
        for row in solver.clauses() {
            if !clause(row.literals(), &mut model, &mut changed, owner) {
                return None;
            }
        }
        if let Some(row) = extra {
            if !clause(row, &mut model, &mut changed, owner) {
                return None;
            }
        }
        if !changed {
            return Some(model);
        }
    }
}

fn exact(
    solver: &FpSolver<'_>,
    inputs: &[(CnfLit, bool)],
    output: &[CnfLit],
    expected: u64,
    owner: &mut Owner,
) {
    owner.charge(output.len() + solver.clauses().len()).unwrap();
    let model = propagate(solver, inputs, None, owner).expect("healthy complete gates");
    for row in solver.clauses() {
        assert!(row
            .literals()
            .iter()
            .any(|&lit| literal(&model, lit) == Some(true)));
    }
    for (i, &lit) in output.iter().enumerate() {
        assert_eq!(literal(&model, lit), Some(expected >> i & 1 != 0));
    }
    // One disjunction REQUIRES a word different from the independent expected
    // integer. A conflict therefore rules out EVERY such wrong word. It is
    // an independent unit-propagation UNSAT derivation here,
    // not a timing comparison or a third-party solver oracle.
    let different: Vec<_> = output
        .iter()
        .enumerate()
        .map(|(i, &lit)| if expected >> i & 1 != 0 { -lit } else { lit })
        .collect();
    assert!(propagate(solver, inputs, Some(&different), owner).is_none());
    drop((model, different));
    owner.charge(0).unwrap();
}

#[test]
fn full_product_is_exact_for_every_pair_at_widths_one_through_four() {
    let mut owner = Owner::new();
    let terms = TermStore::new();
    for width in 1..=4 {
        let mut solver = FpSolver::new(&terms);
        let a = fresh(&mut solver, width);
        let b = fresh(&mut solver, width);
        let product = solver
            .rem_full_product_with_control(&a, &b, &mut owner)
            .unwrap();
        assert_eq!(product.len(), 2 * width);
        for x in 0..1u64 << width {
            for y in 0..1u64 << width {
                let mut inputs = pins(&a, x);
                inputs.extend(pins(&b, y));
                exact(&solver, &inputs, &product, x * y, &mut owner);
            }
        }
        drop((solver, a, b, product));
        owner.charge(0).unwrap();
    }
}

#[test]
fn direct_scale_replays_all_small_symbolic_operands_and_nonnegative_exponents() {
    let terms = TermStore::new();
    let mut owner = Owner::new();
    for width in 1..=3 {
        let mut solver = FpSolver::new(&terms);
        let a = fresh(&mut solver, width);
        let exponent = fresh(&mut solver, 3);
        let modulus = fresh(&mut solver, width);
        let numerator_width = FpSolver::rem_direct_shift_width(width, exponent.len()).unwrap();
        let result = solver
            .rem_direct_scale_with_control(&a, &exponent, &modulus, numerator_width, &mut owner)
            .unwrap();
        let mask = (1u64 << width) - 1;
        for value in 0..=mask {
            for divisor in 0..=mask {
                for shift in 0..4 {
                    let mut inputs = pins(&a, value);
                    inputs.extend(pins(&exponent, shift));
                    inputs.extend(pins(&modulus, divisor));
                    let shifted = value << shift;
                    let expected = if divisor == 0 {
                        shifted & mask
                    } else {
                        shifted % divisor
                    };
                    exact(&solver, &inputs, &result, expected, &mut owner);
                }
            }
        }
    }
    let mut solver = FpSolver::new(&terms);
    let a = fresh(&mut solver, 3);
    let exponent = fresh(&mut solver, 3);
    let m = fresh(&mut solver, 3);
    let width = FpSolver::rem_direct_shift_width(3, 3).unwrap();
    owner.work = 0;
    assert!(solver
        .rem_direct_scale_with_control(&a, &exponent, &m, width, &mut owner)
        .is_err());
    assert!(owner.stopped);
    assert_eq!(FpSolver::rem_direct_shift_width(204, 10), Some(715));
    assert_eq!(FpSolver::rem_direct_shift_width(57, 13), None);
    assert_eq!(
        FpSolver::rem_direct_shift_width(204, usize::BITS as usize + 2),
        None
    );
}

#[test]
fn known_prefix_remainder_preserves_symbolic_values_without_new_cnf_allowance() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let numerator = fresh(&mut solver, 4);
    let mut modulus = fresh(&mut solver, 4);
    modulus.push(solver.const_true());
    solver.const_false();
    // Every four-bit numerator is below every modulus with this leading one.
    // Keep all lower divisor bits symbolic and allow no extra CNF at all.
    let boundary = solver.construction_progress(FpBuildStage::DivideRow);
    let mut owner = Owner::new();
    owner.cnf_limit = Some((boundary.variables, boundary.clauses));
    let remainder = solver
        .rem_narrow_remainder_with_control(&numerator, &modulus, &mut owner)
        .unwrap();
    for value in 0..16 {
        for lower_divisor in 0..16 {
            let mut inputs = pins(&numerator, value);
            inputs.extend(pins(&modulus, 16 | lower_divisor));
            exact(&solver, &inputs, &remainder, value, &mut owner);
        }
    }
}

#[test]
fn narrow_remainder_is_exact_for_all_small_numerators_including_zero_modulus() {
    let mut owner = Owner::new();
    let terms = TermStore::new();
    for width in 1..=3 {
        let mut solver = FpSolver::new(&terms);
        let n = fresh(&mut solver, 2 * width);
        let m = fresh(&mut solver, width);
        let remainder = solver
            .rem_narrow_remainder_with_control(&n, &m, &mut owner)
            .unwrap();
        let mask = (1u64 << width) - 1;
        for numerator in 0..1u64 << (2 * width) {
            for modulus in 0..=mask {
                let mut inputs = pins(&n, numerator);
                inputs.extend(pins(&m, modulus));
                let expected = if modulus == 0 {
                    numerator & mask
                } else {
                    numerator % modulus
                };
                exact(&solver, &inputs, &remainder, expected, &mut owner);
            }
        }
        drop((solver, n, m, remainder));
        owner.charge(0).unwrap();
    }
}

#[test]
fn constant_power_moduli_project_exactly_without_candidate_assignments() {
    let mut owner = Owner::new();
    let terms = TermStore::new();
    for width in 1..=4 {
        for power in 0..width {
            for complemented in [false, true] {
                let mut solver = FpSolver::new(&terms);
                let numerator = fresh(&mut solver, 2 * width);
                let mut modulus = solver.const_bv(1u64 << power, width);
                if complemented {
                    let zero = solver.const_false();
                    let one = solver.const_true();
                    for bit in &mut modulus {
                        *bit = if *bit == zero { -one } else { -zero };
                    }
                }
                let result = solver
                    .rem_narrow_remainder_with_control(&numerator, &modulus, &mut owner)
                    .unwrap();
                let mut inputs: Vec<u64> = if width <= 3 {
                    (0..1u64 << (2 * width)).collect()
                } else {
                    vec![0, 1, (1u64 << (2 * width)) - 1]
                };
                inputs.extend([(1u64 << power) - 1, 1u64 << power, (1u64 << power) + 1]);
                for value in inputs {
                    exact(
                        &solver,
                        &pins(&numerator, value),
                        &result,
                        value % (1u64 << power),
                        &mut owner,
                    );
                }
            }
        }
    }
}

#[test]
fn constant_modulus_scan_retains_the_original_refusal() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let numerator = fresh(&mut solver, 32);
    let modulus = solver.const_bv(8, 16);
    let mut owner = Owner::new();
    owner.work = 2;
    assert!(solver
        .rem_narrow_remainder_with_control(&numerator, &modulus, &mut owner)
        .is_err());
    owner.work = 100_000_000;
    assert!(solver
        .rem_narrow_remainder_with_control(&numerator, &modulus, &mut owner)
        .is_err());
}

#[test]
fn sb200_modulus_preserves_high_symbolic_bits_and_rejects_wrong_output() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let width = 204; // The IEEE SB200 remainder's 16*b_sig modulus width.
    let numerator = fresh(&mut solver, 2 * width);
    let zero = solver.const_false();
    let one = solver.const_true();
    let mut modulus = vec![zero; width];
    modulus[203] = one;
    let before_vars = solver.num_vars();
    let before_clauses = solver.clauses().len();
    let mut owner = Owner::new();
    let output = solver
        .rem_narrow_remainder_with_control(&numerator, &modulus, &mut owner)
        .unwrap();
    eprintln!(
        "SB200 modular reduction: new_variables={} new_clauses={}",
        solver.num_vars() - before_vars,
        solver.clauses().len() - before_clauses,
    );
    // N = 2^407 + 2^203 + 2^202 + 1; N mod 2^203 = 2^202 + 1.
    let inputs: Vec<_> = numerator
        .iter()
        .enumerate()
        .map(|(i, &lit)| (lit, matches!(i, 0 | 202 | 203 | 407)))
        .collect();
    let model = propagate(&solver, &inputs, None, &mut owner).unwrap();
    let mut different = Vec::new();
    for (i, &lit) in output.iter().enumerate() {
        let expected = matches!(i, 0 | 202);
        assert_eq!(literal(&model, lit), Some(expected));
        different.push(if expected { -lit } else { lit });
    }
    assert!(propagate(&solver, &inputs, Some(&different), &mut owner).is_none());
}

#[test]
fn composed_mulmod_is_exact_for_all_small_words_and_zero_divisors() {
    let mut owner = Owner::new();
    let terms = TermStore::new();
    for width in 1..=3 {
        let mut solver = FpSolver::new(&terms);
        let x = fresh(&mut solver, width);
        let y = fresh(&mut solver, width);
        let m = fresh(&mut solver, width);
        let product = solver
            .rem_full_product_with_control(&x, &y, &mut owner)
            .unwrap();
        let remainder = solver
            .rem_narrow_remainder_with_control(&product, &m, &mut owner)
            .unwrap();
        let mask = (1u64 << width) - 1;
        for a in 0..=mask {
            for b in 0..=mask {
                for modulus in 0..=mask {
                    let mut inputs = pins(&x, a);
                    inputs.extend(pins(&y, b));
                    inputs.extend(pins(&m, modulus));
                    let expected = if modulus == 0 {
                        (a * b) & mask
                    } else {
                        a * b % modulus
                    };
                    exact(&solver, &inputs, &remainder, expected, &mut owner);
                }
            }
        }
        drop((solver, x, y, m, product, remainder));
        owner.charge(0).unwrap();
    }
}

#[test]
fn extra_remainder_bit_handles_high_numerators_and_nonpower_moduli() {
    let mut owner = Owner::new();
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let n = fresh(&mut solver, 8);
    let m = fresh(&mut solver, 4);
    let result = solver
        .rem_narrow_remainder_with_control(&n, &m, &mut owner)
        .unwrap();
    for numerator in [0, 127, 128, 254, 255] {
        for modulus in [0, 1, 8, 9, 15] {
            let mut inputs = pins(&n, numerator);
            inputs.extend(pins(&m, modulus));
            let expected = if modulus == 0 {
                numerator & 15
            } else {
                numerator % modulus
            };
            exact(&solver, &inputs, &result, expected, &mut owner);
        }
    }
    drop((solver, n, m, result));
    owner.charge(0).unwrap();
}

#[test]
fn every_format_width_fits_conservative_request_envelope() {
    let mut owner = Owner::new();
    let terms = TermStore::new();
    for width in [6, 15, 28, 57, 117] {
        owner.trace.clear();
        let mut solver = FpSolver::new(&terms);
        let x = fresh(&mut solver, width);
        let y = fresh(&mut solver, width);
        let m = fresh(&mut solver, width);
        let before = solver.num_vars();
        let product = solver
            .rem_full_product_with_control(&x, &y, &mut owner)
            .unwrap();
        let remainder = solver
            .rem_narrow_remainder_with_control(&product, &m, &mut owner)
            .unwrap();
        let requests = 18 * width * width + 12 * width;
        assert!(solver.num_vars() - before <= requests as u32 + 2);
        assert!(solver.clauses().len() <= 4 * requests + 2);
        for pair in owner.trace.windows(2) {
            assert!(pair[0].variables <= pair[1].variables);
            assert!(pair[0].clauses <= pair[1].clauses);
        }
        assert_eq!(product.len(), 2 * width);
        assert_eq!(remainder.len(), width);
        drop((solver, x, y, m, product, remainder));
        owner.charge(0).unwrap();
    }
}

#[test]
fn empty_private_words_still_poll_both_entry_and_completion() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let mut owner = Owner::new();
    assert_eq!(
        solver
            .rem_full_product_with_control(&[], &[], &mut owner)
            .unwrap()
            .len(),
        0
    );
    assert_eq!(
        solver
            .rem_narrow_remainder_with_control(&[], &[], &mut owner)
            .unwrap()
            .len(),
        0
    );
    assert_eq!(owner.trace.len(), 4);
    assert_eq!(solver.num_vars(), 0);
    assert_eq!(solver.clauses().len(), 0);
    drop(solver);
    owner.charge(0).unwrap();
}

#[test]
fn low_product_matches_integer_modulus_for_all_small_inputs() {
    let mut owner = Owner::new();
    let terms = TermStore::new();
    for width in 1..=4 {
        for power in 0..width {
            let mut solver = FpSolver::new(&terms);
            let a = fresh(&mut solver, width);
            let b = fresh(&mut solver, width);
            let product = solver
                .rem_low_product_with_control(&a, &b, power, &mut owner)
                .unwrap();
            for x in 0..1u64 << width {
                for y in 0..1u64 << width {
                    let mut inputs = pins(&a, x);
                    inputs.extend(pins(&b, y));
                    exact(
                        &solver,
                        &inputs,
                        &product,
                        (x * y) % (1 << power),
                        &mut owner,
                    );
                }
            }
        }
    }
}

#[test]
fn power_scale_matches_integer_modulus_including_overflowing_exponents() {
    let mut owner = Owner::new();
    let terms = TermStore::new();
    for width in 1..=4 {
        for power in 0..width {
            let mut solver = FpSolver::new(&terms);
            let word = fresh(&mut solver, width);
            let exponent = fresh(&mut solver, 4);
            let result = solver
                .rem_power_scale_with_control(&word, &exponent, power, &mut owner)
                .unwrap();
            for a in 0..1u64 << width {
                for e in 0..16 {
                    let mut inputs = pins(&word, a);
                    inputs.extend(pins(&exponent, e));
                    let expected = if e >= power as u64 {
                        0
                    } else {
                        (a << e) % (1 << power)
                    };
                    exact(&solver, &inputs, &result, expected, &mut owner);
                }
            }
        }
    }
    // High symbolic exponent bits must zero the result without a host shift.
    let mut solver = FpSolver::new(&terms);
    let word = fresh(&mut solver, 4);
    let exponent = fresh(&mut solver, 128);
    let result = solver
        .rem_power_scale_with_control(&word, &exponent, 3, &mut owner)
        .unwrap();
    for a in 0..16 {
        let mut inputs = pins(&word, a);
        inputs.extend(exponent.iter().enumerate().map(|(i, &bit)| (bit, i == 127)));
        exact(&solver, &inputs, &result, 0, &mut owner);
    }
}

#[test]
fn literal_ieee_divisor_survives_decomposition_as_a_known_power_modulus() {
    let mut terms = TermStore::new();
    // Exact IEEE encoding of 2.0 in (8,200): biased exponent 128, fraction 0.
    let pattern = terms.mk_bitvec(num_bigint::BigInt::from(128u32) << 199usize, 208);
    let two = terms.mk_app(
        ay_core::Symbol::indexed("to_fp", vec![8, 200]),
        vec![pattern],
        ay_core::Sort::FloatingPoint(8, 200),
    );
    let mut solver = FpSolver::new(&terms);
    let mut owner = Owner::new();
    let fp = solver.get_fp_with_control(two, &mut owner).unwrap();
    let (_, significand, _, _) = solver.unpack(&fp, true);
    let mut modulus = solver.const_bv(0, 4);
    modulus.extend_from_slice(&significand);
    assert_eq!(
        solver
            .rem_literal_power_with_control(&modulus, &mut owner)
            .unwrap(),
        Some(203),
        "literal FP fields must remain visible to the exact modular reduction"
    );
}

#[test]
fn known_zero_divisor_finishes_under_the_original_linear_cnf_restriction() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let precision = crate::FpPrecision::Custom { eb: 8, sb: 200 };
    let x = solver.fresh_decomposed(precision);
    let zero = solver.make_zero(precision, false);
    let width = precision.exponent_bits() + precision.significand_bits();
    let mut owner = Owner::new();
    // Classifiers and the six existing result selectors use linear gates.
    // 32 variables / 96 clauses per field bit conservatively covers those
    // gates and final signed-zero selection, without budgeting normal division.
    owner.cnf_limit = Some((
        solver.num_vars() + 32 * width,
        solver.clauses().len() + 96 * width as usize,
    ));
    let result = solver.make_rem_with_control(&x, &zero, &mut owner).unwrap();
    let nan = solver.is_nan(&result);
    assert!(propagate(&solver, &[], Some(&[-nan]), &mut owner).is_none());
}
