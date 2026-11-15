// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `bvudiv` / `bvurem` as a restoring divider over the existing independently
//! checked gates (`Not`, `Xor3`, `FullAdderCarry`, `And2`, `Or2`).
//!
//! For `i` from the most significant bit down, the partial remainder `r`
//! (n bits) is shifted left with `x_i` entering at bit 0, giving the
//! (n+1)-bit `s`; `s - (0 ‖ d)` is formed as `s + (1 ‖ ~d) + 1`, and its
//! carry out is `1` exactly when `s >= d`. That carry is quotient bit `i`,
//! and the new remainder is the difference when it is set and `s` otherwise.
//! When `d != 0` the invariant `r < d` keeps both choices within n bits.
//!
//! SMT-LIB's zero divisor needs no special case: with `d = 0` every step
//! finds `s >= 0`, so the quotient is all ones, and the difference is `s`
//! itself, so after n steps the remainder is `x` — exactly `bvudiv x 0 =
//! #b1..1` and `bvurem x 0 = x`.

use super::*;

impl ExprBlaster<'_> {
    /// The quotient and remainder bits (LSB first) of `left / right`.
    pub(super) fn blast_division(
        &mut self,
        left: &BvExpr,
        right: &BvExpr,
        vars: &mut VarTable,
        lemmas: &mut Vec<BitLemma>,
        clauses: &mut Vec<Clause>,
    ) -> Result<(Vec<u32>, Vec<u32>), BvExprExportError> {
        let x = self.blast(left, vars, lemmas, clauses)?;
        let d = self.blast(right, vars, lemmas, clauses)?;
        if x.len() != d.len() {
            return Err(BvExprExportError::WidthMismatch {
                lhs: x.len() as u32,
                rhs: d.len() as u32,
            });
        }
        if x.is_empty() {
            return Err(BvExprExportError::Malformed(
                "division of zero-width operands".into(),
            ));
        }
        let width = x.len();
        let zero = self.zero(vars, lemmas, clauses);
        let mut payload = width;
        while payload > 1 {
            self.check_deadline()?;
            if x[payload - 1] != zero || d[payload - 1] != zero {
                break;
            }
            payload -= 1;
        }
        // These are already reflected constant wires, not guessed source
        // ranges or newly assumed equalities. The low divider uses the same
        // input IDs and gate cache as an independently requested narrow one.
        let (mut quotient, mut remainder) =
            self.blast_division_bits(&x[..payload], &d[..payload], vars, lemmas, clauses)?;
        if payload < width {
            // A nonzero divisor yields a quotient below 2^payload. A ZERO
            // divisor yields all ones at the ORIGINAL width. Its high bits
            // are therefore exactly this Boolean predicate, never plain zero.
            let mut nonzero = zero;
            for &bit in &d[..payload] {
                self.check_deadline()?;
                nonzero = build_gate(
                    BitLemmaKind::Or2,
                    vec![nonzero, bit],
                    VarRole::Aux { bit: 0 },
                    vars,
                    lemmas,
                    clauses,
                    &mut self.cache,
                );
            }
            self.check_deadline()?;
            let is_zero = build_gate(
                BitLemmaKind::Not,
                vec![nonzero],
                VarRole::Aux { bit: 0 },
                vars,
                lemmas,
                clauses,
                &mut self.cache,
            );
            for bits in [&mut quotient, &mut remainder] {
                bits.try_reserve_exact(width - payload).map_err(|_| {
                    BvExprExportError::ResourceLimit {
                        resource: "division output allocation",
                        limit: width,
                        actual: width.saturating_add(1),
                    }
                })?;
            }
            for _ in payload..width {
                self.check_deadline()?;
                quotient.push(is_zero);
                remainder.push(zero);
            }
        }
        Ok((quotient, remainder))
    }

    /// The unchanged restoring core, shared by full and zero-padded words.
    fn blast_division_bits(
        &mut self,
        x: &[u32],
        d: &[u32],
        vars: &mut VarTable,
        lemmas: &mut Vec<BitLemma>,
        clauses: &mut Vec<Clause>,
    ) -> Result<(Vec<u32>, Vec<u32>), BvExprExportError> {
        let n = x.len();
        let zero = self.zero(vars, lemmas, clauses);
        let one = self.one(vars, lemmas, clauses);
        let mut not_d = Vec::with_capacity(n + 1);
        for (bit, &divisor_bit) in d.iter().enumerate() {
            self.check_deadline()?;
            not_d.push(build_gate(
                BitLemmaKind::Not,
                vec![divisor_bit],
                VarRole::Aux { bit: bit as u32 },
                vars,
                lemmas,
                clauses,
                &mut self.cache,
            ));
        }
        // The complement of the zero-extended divisor's top bit.
        not_d.push(one);
        let mut remainder = vec![zero; n];
        let mut quotient = vec![zero; n];
        for step in (0..n).rev() {
            self.check_deadline()?;
            let mut gate = |kind, inputs, bit: usize| {
                build_gate(
                    kind,
                    inputs,
                    VarRole::Aux { bit: bit as u32 },
                    vars,
                    lemmas,
                    clauses,
                    &mut self.cache,
                )
            };
            let mut shifted = Vec::with_capacity(n + 1);
            shifted.push(x[step]);
            shifted.extend_from_slice(&remainder);
            let mut carry = one;
            let mut difference = Vec::with_capacity(n + 1);
            for bit in 0..=n {
                let operands = vec![shifted[bit], not_d[bit], carry];
                difference.push(gate(BitLemmaKind::Xor3, operands.clone(), bit));
                carry = gate(BitLemmaKind::FullAdderCarry, operands, bit);
            }
            let keep = carry;
            quotient[step] = keep;
            let discard = gate(BitLemmaKind::Not, vec![keep], step);
            remainder = (0..n)
                .map(|bit| {
                    let subtracted = gate(BitLemmaKind::And2, vec![keep, difference[bit]], bit);
                    let kept = gate(BitLemmaKind::And2, vec![discard, shifted[bit]], bit);
                    gate(BitLemmaKind::Or2, vec![subtracted, kept], bit)
                })
                .collect();
        }
        Ok((quotient, remainder))
    }
}

#[cfg(test)]
#[path = "divide_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "divide_zero_padding_tests.rs"]
mod zero_padding_tests;
