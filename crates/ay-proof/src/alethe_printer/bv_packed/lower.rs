// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::alethe_printer::parse_printed_bitvec_literal;
use ay_core::{quote_symbol, Constant};

impl PackedProof<'_, '_> {
    pub(super) fn vector(&mut self, term: TermId, depth: usize) -> Option<Value> {
        self.printer.terms.entry_stamp(term)?;
        if let Some(value) = self.vectors.get(&term) {
            return Some(value.clone());
        }
        self.enter(depth)?;
        let Sort::BitVec(sort) = self.printer.terms.sort(term) else {
            return None;
        };
        let width = sort.width as usize;
        if width == 0 || width > MAX_WIDTH {
            return None;
        }
        let data = self.printer.terms.get(term).clone();
        if self.opaque_words && is_opaque_word(&data) {
            let source = self.printer.format_term(term);
            let bits = (0..width)
                .map(|i| format!("((_ @bit_of {i}) {source})"))
                .collect();
            let result = self.blast(&source, bits, "bitblast_var")?;
            self.vectors.insert(term, result.clone());
            return Some(result);
        }
        let result = match data {
            TermData::Var(name, _) => {
                let source = quote_symbol(&name);
                let bits = (0..width)
                    .map(|i| format!("((_ @bit_of {i}) {source})"))
                    .collect();
                self.blast(&source, bits, "bitblast_var")?
            }
            TermData::Const(Constant::BitVec {
                value,
                width: literal_width,
            }) => {
                if literal_width as usize != width {
                    return None;
                }
                self.literal(term, &value, literal_width)?
            }
            TermData::App(Symbol::Named(op), args) if op == "concat" => {
                let [high, low] = args.as_slice() else {
                    return None;
                };
                let high = self.vector(*high, depth + 1)?;
                let low = self.vector(*low, depth + 1)?;
                let bits = low.bits.iter().chain(&high.bits).cloned().collect();
                let changed = self.congruence("concat", &[high.equality, low.equality])?;
                let blasted = self.blast(&changed.right, bits, "bitblast_concat")?;
                Value {
                    equality: self.chain(changed, blasted.equality)?,
                    bits: blasted.bits,
                }
            }
            TermData::App(Symbol::Indexed(op, indices), args) if op == "extract" => {
                self.vector_extract(&args, &indices, depth)?
            }
            TermData::App(Symbol::Indexed(op, indices), args)
                if matches!(op.as_str(), "zero_extend" | "sign_extend") =>
            {
                self.extended_term(&op, &indices, &args, width, depth)?
            }
            TermData::App(Symbol::Named(op), args)
                if matches!(op.as_str(), "bvshl" | "bvlshr" | "bvashr") =>
            {
                self.literal_or_symbolic_shift(&op, &args, width, depth)?
            }
            TermData::App(Symbol::Named(op), args) if op == "bvmul" => {
                self.product(&args, width, depth)?
            }
            TermData::App(Symbol::Named(op), args) if matches!(op.as_str(), "bvor" | "bvand") => {
                self.bitwise(&op, &args, width, depth)?
            }
            TermData::App(Symbol::Named(op), args) if op == "bvadd" => {
                self.addition(&args, width, depth)?
            }
            TermData::App(Symbol::Named(op), args) if op == "select" => {
                self.sparse_select(&args, width, depth)?
            }
            TermData::Ite(condition, then_term, else_term) => {
                self.vector_conditional(condition, then_term, else_term, width, depth)?
            }
            _ => return None,
        };
        if result.bits.len() != width || self.printer.format_term(term) != result.equality.left {
            return None;
        }
        self.vectors.insert(term, result.clone());
        Some(result)
    }

    fn vector_extract(&mut self, args: &[TermId], indices: &[u32], depth: usize) -> Option<Value> {
        let [source] = args else {
            return None;
        };
        let [high, low] = indices else {
            return None;
        };
        // Normalize the entire source before projecting its bits.
        let source = self.vector(*source, depth + 1)?;
        if high < low || *high as usize >= source.bits.len() {
            return None;
        }
        let bits = source.bits[*low as usize..=*high as usize].to_vec();
        let op = format!("(_ extract {high} {low})");
        let changed = self.congruence(&op, &[source.equality])?;
        let blasted = self.blast(&changed.right, bits, "bitblast_extract")?;
        Some(Value {
            equality: self.chain(changed, blasted.equality)?,
            bits: blasted.bits,
        })
    }

    pub(super) fn blast(&mut self, source: &str, bits: Vec<String>, rule: &str) -> Option<Value> {
        let equality = self.equality(source, &bbterm(&bits), rule, &[])?;
        Some(Value { equality, bits })
    }

    fn literal(&mut self, term: TermId, value: &num_bigint::BigInt, width: u32) -> Option<Value> {
        let source = self.printer.format_term(term);
        let (printed, printed_width) = parse_printed_bitvec_literal(&source)?;
        if printed_width != width || printed != value.to_biguint()? {
            return None;
        }
        let bits = (0..width)
            .map(|i| if value.bit(i as u64) { "true" } else { "false" }.into())
            .collect();
        self.blast(&source, bits, "bitblast_const")
    }

    pub(super) fn boolean(&mut self, term: TermId, depth: usize) -> Option<Equality> {
        self.printer.terms.entry_stamp(term)?;
        if let Some(value) = self.booleans.get(&term) {
            return Some(value.clone());
        }
        self.enter(depth)?;
        if self.printer.terms.sort(term) != &Sort::Bool {
            return None;
        }
        let data = self.printer.terms.get(term).clone();
        let result = match data {
            TermData::Var(name, _) => {
                let source = quote_symbol(&name);
                self.equality(&source, &source, "refl", &[])?
            }
            TermData::Const(Constant::Bool(value)) => {
                let source = value.to_string();
                self.equality(&source, &source, "refl", &[])?
            }
            TermData::App(Symbol::Named(op), args) if op == "=" => {
                let [left, right] = args.as_slice() else {
                    return None;
                };
                let left = self.vector(*left, depth + 1)?;
                let right = self.vector(*right, depth + 1)?;
                self.vector_equality(left, right)?
            }
            // Opaque-word mode: a condition the lane does not read is one
            // leaf, spelled and compared as itself.
            _ if self.opaque_words => {
                let source = self.printer.format_term(term);
                self.equality(&source, &source, "refl", &[])?
            }
            _ => return None,
        };
        if self.printer.format_term(term) != result.left {
            return None;
        }
        self.booleans.insert(term, result.clone());
        Some(result)
    }
}

/// Whether opaque-word mode names `data` as one `bitblast_var` leaf: every
/// application outside the wiring operators `concat`, `extract`,
/// `zero_extend` and `sign_extend`. Variables, literals and `ite` keep their
/// ordinary lowering.
fn is_opaque_word(data: &TermData) -> bool {
    match data {
        TermData::App(Symbol::Named(op), _) => op != "concat",
        TermData::App(Symbol::Indexed(op, _), _) => {
            !matches!(op.as_str(), "extract" | "zero_extend" | "sign_extend")
        }
        _ => false,
    }
}
