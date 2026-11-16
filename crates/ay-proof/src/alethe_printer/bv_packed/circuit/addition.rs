// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Share the carry network of reassociated constant offsets. The original
//! spelling reaches the result only through a checked polynomial equality.

use super::*;
use ay_core::Constant;
use num_bigint::BigInt;
use num_traits::{One, Zero};

impl Circuit<'_, '_, '_> {
    pub(super) fn addition(&mut self, term: TermId, width: usize, depth: usize) -> Option<Word> {
        if !self.nested_constant_offset(term) {
            let TermData::App(_, args) = self.proof.printer.terms.get(term).clone() else {
                return None;
            };
            let [a, b] = args.as_slice() else { return None };
            let a = self.word(*a, depth + 1)?;
            let b = self.word(*b, depth + 1)?;
            return self.add(a, b);
        }
        let mut operands = Vec::new();
        let mut constant = BigInt::zero();
        self.collect_addition(term, width, depth, &mut operands, &mut constant)?;
        let mut result = None;
        for operand in operands {
            let word = self.word(operand, depth + 1)?;
            result = Some(match result {
                Some(previous) => self.add(previous, word)?,
                None => word,
            });
        }
        constant &= (BigInt::one() << width) - 1u8;
        if !constant.is_zero() || result.is_none() {
            let word = self.literal_word(&constant, width)?;
            result = Some(match result {
                Some(previous) => self.add(previous, word)?,
                None => word,
            });
        }
        let mut result = result?;
        let source = self.proof.printer.format_term(term);
        if !literal_spelling::prints_alike(&source, &result.equality.left) {
            // The same bounded printed-linear reader used by the offset
            // bridge decides this identity modulo2^width. No DAG reading can
            // authorize a polynomial step over different authored text.
            let zero = format!("(_ bv0 {width})");
            crate::alethe_printer::offset_bridge::printed_factor(
                &source,
                &result.equality.left,
                &zero,
                &zero,
                width as u32,
            )?;
            let bridge = self
                .proof
                .equality(&source, &result.equality.left, "poly_simp", &[])?;
            result.equality = self.proof.chain(bridge, result.equality)?;
        }
        Some(result)
    }

    fn nested_constant_offset(&self, term: TermId) -> bool {
        let terms = self.proof.printer.terms;
        let TermData::App(Symbol::Named(op), args) = terms.get(term) else {
            return false;
        };
        let [left, right] = args.as_slice() else {
            return false;
        };
        if op != "bvadd" || matches!(terms.get(*right), TermData::Const(_)) {
            return false;
        }
        matches!(terms.get(*left), TermData::App(Symbol::Named(inner), operands)
            if inner == "bvadd" && operands.len() == 2
                && operands.iter().any(|&part| matches!(terms.get(part),
                    TermData::Const(Constant::BitVec { .. }))))
    }

    fn collect_addition(
        &mut self,
        term: TermId,
        width: usize,
        depth: usize,
        operands: &mut Vec<TermId>,
        constant: &mut BigInt,
    ) -> Option<()> {
        self.proof.enter(depth)?;
        let terms = self.proof.printer.terms;
        terms.entry_stamp(term)?;
        if terms.sort(term) != &Sort::bitvec(width as u32) {
            return None;
        }
        match terms.get(term).clone() {
            TermData::App(Symbol::Named(op), args) if op == "bvadd" => {
                let [a, b] = args.as_slice() else { return None };
                self.collect_addition(*a, width, depth + 1, operands, constant)?;
                self.collect_addition(*b, width, depth + 1, operands, constant)
            }
            TermData::Const(Constant::BitVec {
                value,
                width: actual,
            }) => {
                if actual as usize != width
                    || value < BigInt::zero()
                    || value >= BigInt::one() << width
                {
                    return None;
                }
                *constant += value;
                Some(())
            }
            _ => {
                operands.push(term);
                Some(())
            }
        }
    }
}
