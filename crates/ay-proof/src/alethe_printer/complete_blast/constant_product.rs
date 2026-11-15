// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A product by a literal that is NOT a power of two, re-spelled as a signed
//! sum of power-of-two products.
//!
//! ## Why this exists
//!
//! `bitblast_mult` spells a full `w²` shift-and-add array even when one
//! operand is a literal, and its internal signals line up with nothing a
//! compiler writes instead: external-codegen's `x * (2^a - 1) == (x << a) - x`,
//! `x * 31 == (x << 5) - x` and `x * 17 == (x << 4) + x` were holes (measured
//! 2026-09-28), an adder array against a subtractor whose only common signals
//! are the outputs.
//!
//! ## What is printed
//!
//! The literal's non-adjacent form `c = Σ ±2^k` (a digit at `k ≥ w` is `0`
//! modulo `2^w` and dropped, so `2^64 - 1` is `-1`) selects the terms. Every
//! `2^k · x` is a word of the doubling chain [`Blaster::build_multiplication`]
//! already prints — each named by its own polynomial `(bvmul 2^k x)` and
//! proved by one `poly_simp` per doubling — and the terms are combined with
//! `bvadd` and the `bvsub` re-spelling. The authored `(bvmul c x)` is bound to
//! that sum by one more `poly_simp`: both sides are the same polynomial modulo
//! `2^w`, which is exactly what the checker's normalizer decides. Nothing is
//! assumed, and `x * 127` against `(x << 7) - x` becomes two structurally
//! aligned circuits the sweep merges gate by gate.

use super::*;
use crate::non_adjacent_form::non_adjacent_form;

/// Largest literal width handled here; the literal is read into a `u128`.
const MAX_LITERAL_WIDTH: u32 = 128;

impl Blaster<'_, '_> {
    /// `(bvmul c x)` re-spelled through the non-adjacent form of `c`, or
    /// `None` when neither operand is such a literal.
    pub(super) fn constant_product(&mut self, operands: &[usize], width: u32) -> Option<usize> {
        let &[first, second] = operands else {
            return None;
        };
        if width == 0 || width > MAX_LITERAL_WIDTH {
            return None;
        }
        for (constant, x) in [(first, second), (second, first)] {
            // A word a case binds is constant-valued but spelled as its
            // variable: `poly_simp` would read the variable (`case_split.rs`).
            if self.case_words.contains_key(&constant) {
                continue;
            }
            let Some(value) = self.literal_value(constant) else {
                continue;
            };
            let digits = non_adjacent_form(value, width);
            if digits.len() < 2 && digits.first().is_none_or(|&(_, negative)| !negative) {
                // Zero or a single power of two: the caller's lanes.
                continue;
            }
            let top = digits.iter().map(|&(power, _)| power).max()?;
            let powers = self.doubling_chain(x, top, width)?;
            let mut terms = digits.iter();
            let &(power, negative) = terms.next()?;
            let mut sum = if negative {
                let body = self.application("bvneg", &[powers[power as usize]]);
                self.new_word(body, width, WordOp::Neg(powers[power as usize]))?
            } else {
                powers[power as usize]
            };
            for &(power, negative) in terms {
                let term = powers[power as usize];
                sum = if negative {
                    self.build_subtraction(&[sum, term], width)?
                } else {
                    let body = self.application("bvadd", &[sum, term]);
                    self.new_word(body, width, WordOp::Add(vec![sum, term]))?
                };
            }
            let body = self.application("bvmul", operands);
            return self.rewritten_word(body, width, sum);
        }
        None
    }

    /// The words `2^0·x … 2^top·x`, each named by its own polynomial and
    /// proved from the one before by a doubling.
    pub(super) fn doubling_chain(&mut self, x: usize, top: u32, width: u32) -> Option<Vec<usize>> {
        if top > MAX_MUL_DOUBLINGS || top >= width {
            return None;
        }
        let mut powers = vec![x];
        let mut current = x;
        for step in 1..=top {
            let body = self.application("bvadd", &[current, current]);
            let sum = self.new_word(body, width, WordOp::Add(vec![current, current]))?;
            let product = format!(
                "(bvmul (_ bv{} {width}) {})",
                1_u128.checked_shl(step)?,
                self.word_ref(x)
            );
            current = self.rewritten_word(product, width, sum)?;
            powers.push(current);
        }
        Some(powers)
    }

    /// The value of a word whose every bit is a constant.
    fn literal_value(&self, word: usize) -> Option<u128> {
        let mut value = 0_u128;
        for (index, bit) in self.words[word].bits.iter().enumerate() {
            match self.circuit.kind(bit.gate) {
                circuit::GateKind::Const(constant) => {
                    if *constant != bit.negative() {
                        value |= 1_u128.checked_shl(u32::try_from(index).ok()?)?;
                    }
                }
                _ => return None,
            }
        }
        Some(value)
    }
}
