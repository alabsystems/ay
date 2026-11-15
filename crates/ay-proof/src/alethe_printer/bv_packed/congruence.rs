// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Normalize operands before applying congruence to expensive BV operations.
//! Projection uses the checked identity t = @bbterm(@bit_of(0,t), ...).
//! The complete operation remains in every projected bit: no fresh operand,
//! arithmetic axiom, or assumption replaces its semantics.

use super::super::dialect::{self, CleanOnlySpelling};
use super::*;

impl PackedProof<'_, '_> {
    pub(super) fn literal_or_symbolic_shift(
        &mut self,
        op: &str,
        args: &[TermId],
        width: usize,
        depth: usize,
    ) -> Option<Value> {
        let [_, amount] = args else { return None };
        if matches!(self.printer.terms.get(*amount), TermData::Const(_)) {
            self.literal_shift(op, args, width, depth)
        } else {
            self.application_bits(op, args, width, depth)
        }
    }

    pub(super) fn application_bits(
        &mut self,
        op: &str,
        args: &[TermId],
        width: usize,
        depth: usize,
    ) -> Option<Value> {
        let [left, right] = args else { return None };
        let left = self.vector(*left, depth + 1)?;
        let right = self.vector(*right, depth + 1)?;
        if left.bits.len() != width || right.bits.len() != width {
            return None;
        }
        self.define_word(&left.bits)?;
        self.define_word(&right.bits)?;
        let changed = self.congruence(op, &[left.equality, right.equality])?;
        let name = self.define_term(&changed.right, &format!("(_ BitVec {width})"))?;
        let bits = (0..width)
            .map(|i| format!("((_ @bit_of {i}) {name})"))
            .collect();
        let projected = self.blast(&changed.right, bits, "bitblast_var")?;
        Some(Value {
            equality: self.chain(changed, projected.equality)?,
            bits: projected.bits,
        })
    }

    pub(super) fn extended_vector(&mut self, source: Value, extra: usize) -> Option<Value> {
        let original = format!("((_ zero_extend {extra}) {})", source.equality.left);
        // Each `refl` below is the identity Clean's consumer rule
        // `dialect:expand_zero_extend` admits (`CleanOnlySpelling::consumer_rule`;
        // Clean from `ba5e28ff5`); pinned Carcara 9a352ee keeps the indexed
        // operator and refuses it (`dialect`).
        if extra == 0 {
            let identity = self.equality(&original, &source.equality.left, "refl", &[])?;
            dialect::note_clean_only(CleanOnlySpelling::ZeroExtendAsConcat);
            return Some(Value {
                equality: self.chain(identity, source.equality)?,
                bits: source.bits,
            });
        }
        // The identity's right side is the definition itself; standard rules
        // check the bits from there.
        let zero = format!("(_ bv0 {extra})");
        let expanded = format!("(concat {zero} {})", source.equality.left);
        let identity = self.equality(&original, &expanded, "refl", &[])?;
        let zeros = vec!["false".into(); extra];
        let zero = self.blast(&zero, zeros, "bitblast_const")?;
        let changed = self.congruence("concat", &[zero.equality, source.equality])?;
        let mut bits = source.bits;
        bits.extend(zero.bits);
        self.define_word(&bits)?;
        let blasted = self.blast(&changed.right, bits, "bitblast_concat")?;
        let equality = self.chain(identity, changed)?;
        dialect::note_clean_only(CleanOnlySpelling::ZeroExtendAsConcat);
        Some(Value {
            equality: self.chain(equality, blasted.equality)?,
            bits: blasted.bits,
        })
    }
}
