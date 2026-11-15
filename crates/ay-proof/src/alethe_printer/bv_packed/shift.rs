// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Literal shifts using the consumer's bounded barrel-shifter rules. Every
//! stage is reduced by congruence and checked constant-condition evaluation.

use super::super::dialect::{self, AletheDialect, CleanOnlySpelling};
use super::*;

impl PackedProof<'_, '_> {
    pub(super) fn bitblast_literal_shift(
        &mut self,
        op: &str,
        source: Value,
        literal: Value,
        amount: usize,
    ) -> Option<Value> {
        let width = source.bits.len();
        let rule = match op {
            "bvshl" => "bitblast_shl",
            "bvlshr" => "bitblast_lshr",
            // `bitblast_ashr` only for an amount below the width: there the
            // pinned zero fill is true, and never elsewhere. A literal
            // overshift is left to the separate closed-case derivation.
            "bvashr" if amount < width => "bitblast_ashr",
            _ => return None,
        };
        let changed = self.congruence(op, &[source.equality, literal.equality])?;
        let mut stages = source
            .bits
            .iter()
            .map(|bit| self.equality(bit, bit, "refl", &[]))
            .collect::<Option<Vec<_>>>()?;
        let zero = self.equality("false", "false", "refl", &[])?;
        let sign = stages.last()?.clone();
        let phase_count = width.next_power_of_two().trailing_zeros() as usize;
        for phase in 0..phase_count {
            let threshold = 1usize << phase;
            let condition = literal.bits.get(phase)?;
            let previous = stages.clone();
            for (i, bit) in stages.iter_mut().enumerate() {
                let (condition, yes, no) = match op {
                    "bvshl" => (
                        condition.clone(),
                        i.checked_sub(threshold).map_or(&zero, |j| &previous[j]),
                        &previous[i],
                    ),
                    _ if i + threshold >= width => (
                        condition.clone(),
                        if op == "bvashr" { &sign } else { &zero },
                        &previous[i],
                    ),
                    _ => (
                        format!("(not {condition})"),
                        &previous[i],
                        &previous[i + threshold],
                    ),
                };
                *bit = self.shift_selection(&condition, yes, no)?;
            }
        }
        let guard = self.shift_range_guard(&literal.bits)?;
        let guard = self.equality(&guard, &(amount < width).to_string(), "evaluate", &[])?;
        // The overshift fill: zero for the logical shifts. For `bvashr` Clean's
        // Carcara (DOWNSTREAM fix 2) fills with the sign bit, as SMT-LIB
        // requires, and upstream Carcara 9a352ee with zero (`dialect`). The
        // guard above is proved `true`, so the fill never selects and both
        // spellings are true; `amount < width` is what makes the zero fill so.
        let clean = op == "bvashr" && dialect::current() == AletheDialect::Clean;
        let clean_only = clean && sign.left != zero.left;
        let fill = if clean { sign } else { zero };
        for bit in &mut stages {
            *bit = self.shift_selection_checked(guard.clone(), bit, &fill)?;
        }
        let raw: Vec<_> = stages.iter().map(|bit| bit.left.clone()).collect();
        let bits: Vec<_> = stages.iter().map(|bit| bit.right.clone()).collect();
        self.define_word(&raw)?;
        self.define_word(&bits)?;
        let blasted = self.equality(&changed.right, &bbterm(&raw), rule, &[])?;
        if clean_only {
            dialect::note_clean_only(CleanOnlySpelling::SignFilledAshrOvershift);
        }
        let premises: Vec<_> = stages.iter().map(|bit| bit.step.as_str()).collect();
        let reduced = self.equality(&bbterm(&raw), &bbterm(&bits), "cong", &premises)?;
        let equality = self.chain(changed, blasted)?;
        Some(Value {
            equality: self.chain(equality, reduced)?,
            bits,
        })
    }

    fn shift_selection(
        &mut self,
        condition: &str,
        yes: &Equality,
        no: &Equality,
    ) -> Option<Equality> {
        // Stage selectors are literal bits or their logical negations.
        let value = if condition == "true" || condition == "(not false)" {
            "true"
        } else if condition == "false" || condition == "(not true)" {
            "false"
        } else {
            return None;
        };
        let condition = self.equality(condition, value, "evaluate", &[])?;
        self.shift_selection_checked(condition, yes, no)
    }

    fn shift_selection_checked(
        &mut self,
        condition: Equality,
        yes: &Equality,
        no: &Equality,
    ) -> Option<Equality> {
        let target = match condition.right.as_str() {
            "true" => &yes.right,
            "false" => &no.right,
            _ => return None,
        };
        let changed = self.congruence("ite", &[condition, yes.clone(), no.clone()])?;
        let reduced = self.equality(&changed.right, target, "ite_simplify", &[])?;
        let mut equality = self.chain(changed, reduced)?;
        equality.left = self.define_term(&equality.left, "Bool")?;
        Some(equality)
    }

    fn shift_range_guard(&mut self, bits: &[String]) -> Option<String> {
        let width = bits.len();
        let size_bit = |i| format!("((_ @bit_of {i}) (_ bv{width} {width}))");
        let mut guard = format!("(and (not {}) {})", bits.first()?, size_bit(0));
        for (i, bit) in bits.iter().enumerate().skip(1) {
            let previous = self.define_term(&guard, "Bool")?;
            let size = size_bit(i);
            guard = format!("(or (and (= {bit} {size}) {previous}) (and (not {bit}) {size}))");
        }
        self.define_term(&guard, "Bool")
    }
}
