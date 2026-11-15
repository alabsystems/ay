// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::super::dialect::{self, CleanOnlySpelling};
use super::*;

impl Circuit<'_, '_, '_> {
    pub(super) fn indexed(
        &mut self,
        op: &str,
        indices: &[u32],
        args: &[TermId],
        width: usize,
        depth: usize,
    ) -> Option<Word> {
        let [arg] = args else { return None };
        let arg = self.word(*arg, depth + 1)?;
        match (op, indices) {
            ("extract", [high, low]) => {
                if low > high || *high as usize >= arg.bits.len() {
                    return None;
                }
                let bits = arg.bits[*low as usize..=*high as usize].to_vec();
                self.wired(
                    &format!("(_ extract {high} {low})"),
                    &[arg.equality],
                    bits,
                    "bitblast_extract",
                )
            }
            ("sign_extend", [extra]) => {
                if arg.bits.len().checked_add(*extra as usize)? != width {
                    return None;
                }
                let sign = *arg.bits.last()?;
                let mut bits = arg.bits;
                bits.resize(width, sign);
                self.wired(
                    &format!("(_ sign_extend {extra})"),
                    &[arg.equality],
                    bits,
                    "bitblast_sign_extend",
                )
            }
            ("zero_extend", [extra]) => {
                if arg.bits.len().checked_add(*extra as usize)? != width {
                    return None;
                }
                self.zero_extend(arg, *extra as usize)
            }
            _ => None,
        }
    }

    fn zero_extend(&mut self, arg: Word, extra: usize) -> Option<Word> {
        // A circuit word uses SAT literal IDs, but its source equality and
        // bit spellings have the same contract as the packed word lane.
        // Reuse that lane's discharged CLOSED evaluations where its existing
        // eight-symbolic-bit admission holds, in either dialect. The checker
        // derives the extension from constants in every Boolean case; there
        // is no symbolic zero_extend/concat identity admitted as an axiom.
        let width = arg.bits.len().checked_add(extra)?;
        if arg.bits.is_empty() || width > MAX_WIDTH {
            return None;
        }
        let input = self.bit_text(&arg.bits)?;
        if super::super::wire::admits_wire_cases(&input) {
            let source = Value {
                bits: input,
                equality: arg.equality,
            };
            let checked = self.checked_zero_extend(source, extra)?;
            // A refusal propagates above; it never falls through to a cheaper
            // Clean-only spelling after the checked-case budget is spent.
            return self.from_value(checked);
        }
        // Outside the existing case admission, keep the honest Clean-only
        // representation and its disclosure unchanged.
        let source = format!("((_ zero_extend {extra}) {})", arg.equality.left);
        // Each `refl` is the identity Clean's consumer rule
        // `dialect:expand_zero_extend` admits (`CleanOnlySpelling::consumer_rule`;
        // Clean from `ba5e28ff5`), followed by ordinary checked constant/concat
        // bitblast steps. Pinned Carcara 9a352ee refuses it (`dialect`).
        if extra == 0 {
            let identity = self
                .proof
                .equality(&source, &arg.equality.left, "refl", &[])?;
            dialect::note_clean_only(CleanOnlySpelling::ZeroExtendAsConcat);
            return Some(Word {
                bits: arg.bits,
                equality: self.proof.chain(identity, arg.equality)?,
            });
        }
        let zero = format!("(_ bv0 {extra})");
        let expanded = format!("(concat {zero} {})", arg.equality.left);
        let identity = self.proof.equality(&source, &expanded, "refl", &[])?;
        let zeros = vec!["false".to_string(); extra];
        let zero = self
            .proof
            .equality(&zero, &bbterm(&zeros), "bitblast_const", &[])?;
        let mut bits = arg.bits;
        let zero_bit = self.atom("false")?;
        bits.resize(bits.len().checked_add(extra)?, zero_bit);
        let mut value = self.wired("concat", &[zero, arg.equality], bits, "bitblast_concat")?;
        value.equality = self.proof.chain(identity, value.equality)?;
        dialect::note_clean_only(CleanOnlySpelling::ZeroExtendAsConcat);
        Some(value)
    }
}
