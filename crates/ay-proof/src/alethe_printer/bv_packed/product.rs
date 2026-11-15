// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact checked multiplication DAGs with shared lower product prefixes.

use super::super::dialect::{self, AletheDialect};
use super::*;

impl PackedProof<'_, '_> {
    pub(super) fn product(&mut self, args: &[TermId], width: usize, depth: usize) -> Option<Value> {
        let [a, b] = args else { return None };
        let a = self.vector(*a, depth + 1)?;
        let b = self.vector(*b, depth + 1)?;
        if a.bits.len() != width || b.bits.len() != width {
            return None;
        }
        self.checked_product(a, b)
    }

    pub(super) fn extended_term(
        &mut self,
        op: &str,
        indices: &[u32],
        args: &[TermId],
        width: usize,
        depth: usize,
    ) -> Option<Value> {
        let [source] = args else { return None };
        let [extra] = indices else { return None };
        let source = self.vector(*source, depth + 1)?;
        if source.bits.len().checked_add(*extra as usize)? != width {
            return None;
        }
        let operation = format!("(_ {op} {extra})");
        if op == "sign_extend" {
            let mut bits = source.bits;
            let sign = bits.last()?.clone();
            bits.resize(width, sign);
            let changed = self.congruence(&operation, &[source.equality])?;
            let blasted = self.blast(&changed.right, bits, "bitblast_sign_extend")?;
            return Some(Value {
                equality: self.chain(changed, blasted.equality)?,
                bits: blasted.bits,
            });
        }
        // Pinned Carcara 9a352ee has no rule for `zero_extend` over a
        // symbolic word (`dialect`); it checks only the closed cases
        // `wire_operation` evaluates. Clean's `refl` to `concat` takes every
        // source wider than a byte. The pinned dialect keeps the cases
        // wherever their unchanged bound admits them, however wide the word:
        // at most `MAX_CASE_BITS` symbolic bits (ground and partly constant
        // words).
        let pinned_cases = dialect::current() == AletheDialect::PinnedCarcara
            && wire::admits_wire_cases(&source.bits);
        if source.bits.len() > 8 && !pinned_cases {
            self.extended_vector(source, *extra as usize)
        } else {
            let mut bits = source.bits.clone();
            bits.resize(width, "false".into());
            self.wire_operation(&operation, source, None, bits)
        }
    }

    fn product_node(&mut self, op: &str, a: &str, b: &str) -> Option<String> {
        self.printer.charge(1);
        if self.printer.work_budget_exhausted() {
            return None;
        }
        self.define_term(&format!("({op} {a} {b})"), "Bool")
    }

    fn product_row(
        &mut self,
        previous: &[String],
        a: &[String],
        multiplier: &str,
        row: usize,
    ) -> Option<Vec<String>> {
        let mut output = previous.to_vec();
        let mut carry = "false".to_string();
        for i in row..a.len() {
            if i > row {
                let partial = self.product_node("and", multiplier, &a[i - row - 1])?;
                let generated = self.product_node("and", &previous[i - 1], &partial)?;
                let parity = self.product_node("xor", &previous[i - 1], &partial)?;
                let propagated = self.product_node("and", &parity, &carry)?;
                carry = self.product_node("or", &generated, &propagated)?;
            }
            let partial = self.product_node("and", multiplier, &a[i - row])?;
            let parity = self.product_node("xor", &previous[i], &partial)?;
            output[i] = self.product_node("xor", &parity, &carry)?;
        }
        Some(output)
    }

    fn checked_product(&mut self, a: Value, b: Value) -> Option<Value> {
        let width = a.bits.len();
        if width == 0 || width > MAX_WIDTH || b.bits.len() != width {
            return None;
        }
        self.define_word(&a.bits)?;
        self.define_word(&b.bits)?;
        let changed = self.congruence("bvmul", &[a.equality, b.equality])?;
        let mut bits = a
            .bits
            .iter()
            .map(|bit| self.product_node("and", &b.bits[0], bit))
            .collect::<Option<Vec<_>>>()?;
        for j in 1..width {
            bits = self.product_row(&bits, &a.bits, &b.bits[j], j)?;
        }
        self.define_word(&bits)?;
        let blasted = self.blast(&changed.right, bits, "bitblast_mult")?;
        Some(Value {
            equality: self.chain(changed, blasted.equality)?,
            bits: blasted.bits,
        })
    }
}
