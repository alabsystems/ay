// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked Alethe lowering for bounded bit-vector multiplication by zero.

mod circuit;
#[cfg(test)]
#[path = "bv_mul_zero/bv_mul_zero_tests.rs"]
mod tests;

use super::{parse_printed_bitvec_literal, split_application, AlethePrinter};
use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId};
use circuit::{FalseWitness, MulCircuit};
use std::fmt::Write as _;

const MAX_MUL_ZERO_WIDTH: u32 = 32;

#[derive(Clone, Copy)]
struct MulZeroShape {
    equality: TermId,
    product: TermId,
    result_zero: TermId,
    operands: [TermId; 2],
    width: u32,
    zero_operand: usize,
    reversed: bool,
}

struct MulZeroText {
    equality: String,
    product: String,
    result_zero: String,
    operands: [String; 2],
}

impl AlethePrinter<'_> {
    /// Central dispatch for the independently reconstructed bit-blast subset.
    /// Keeping it out of `format_theory_lemma` prevents every new exact lane
    /// from growing that already-large generic dispatcher.
    pub(super) fn format_checked_bv_bitblast_lowering(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        self.format_bv_constant_disequality(id, clause)
            .or_else(|| self.format_bv_mul_zero_bitblast(id, clause))
            .or_else(|| self.format_bv_idempotent_gate_bitblast(id, clause))
            .or_else(|| self.format_bv_double_negation_bitblast(id, clause))
            .or_else(|| self.format_bv_ult_one_zero_equiv(id, clause))
            .or_else(|| self.format_bv_unsigned_compare_duality(id, clause))
    }

    /// Lower the exact unit identity `(= (bvmul X 0_w) 0_w)` (including
    /// operand/equality reversals) through Carcara's checked `bitblast_mult`
    /// circuit. The expansion is capped at 32 bits and DAG-shared with
    /// proof-local `define-fun`s: spelling the shift/add circuit as a tree is
    /// exponentially large even at modest widths.
    ///
    /// Both the internal term and every checker-visible surface endpoint are
    /// re-decoded. A width/value/operator mismatch, a changed surface spelling,
    /// or any circuit bit that cannot be proved false returns `None`, preserving
    /// the ordinary honest `hole` fallback.
    pub(super) fn format_bv_mul_zero_bitblast(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        let [equality] = clause else {
            return None;
        };
        let shape = self.decode_mul_zero_shape(*equality)?;
        if shape.width == 0 || shape.width > MAX_MUL_ZERO_WIDTH {
            return None;
        }
        let text = self.mul_zero_text(shape)?;
        let prefix = self.fresh_mul_zero_prefix(id, &text)?;
        let mut circuit = MulCircuit::new(prefix);
        let bits = circuit.operand_bits(shape.width, shape.zero_operand, &text.operands);
        let result = circuit.build(&bits[0], &bits[1]);

        let bbzero = format!(
            "(@bbterm {})",
            vec!["false"; shape.width as usize].join(" ")
        );
        let bbresult = format!(
            "(@bbterm {})",
            result
                .iter()
                .map(|bit| circuit.reference(bit))
                .collect::<Vec<_>>()
                .join(" ")
        );
        let mut blasted_operands = text.operands.clone();
        blasted_operands[shape.zero_operand] = bbzero.clone();
        let blasted_product = format!("(bvmul {} {})", blasted_operands[0], blasted_operands[1]);

        let mut out = String::new();
        circuit.append_definitions(&mut out);
        let _ = writeln!(
            out,
            "(step {id}.mz.z (cl (= {} {bbzero})) :rule bitblast_const)",
            text.result_zero
        );
        let _ = writeln!(
            out,
            "(step {id}.mz.cg (cl (= {} {blasted_product})) :rule cong :premises ({id}.mz.z))",
            text.product
        );
        let _ = writeln!(
            out,
            "(step {id}.mz.mul (cl (= {blasted_product} {bbresult})) :rule bitblast_mult)"
        );

        let mut memo = ay_core::kani_compat::DetHashMap::default();
        let mut bit_premises = Vec::new();
        for bit in &result {
            match circuit.prove_false(id, bit, &mut out, &mut memo)? {
                FalseWitness::Literal => {}
                FalseWitness::Step(step) => bit_premises.push(step),
            }
        }
        let _ = writeln!(
            out,
            "(step {id}.mz.bits (cl (= {bbresult} {bbzero})) :rule cong :premises ({}))",
            bit_premises.join(" ")
        );
        let _ = writeln!(
            out,
            "(step {id}.mz.zs (cl (= {bbzero} {})) :rule symm :premises ({id}.mz.z))",
            text.result_zero
        );
        let forward = if shape.reversed {
            format!("{id}.mz.forward")
        } else {
            id.to_string()
        };
        let _ = write!(
            out,
            "(step {forward} (cl (= {} {})) :rule trans :premises \
             ({id}.mz.cg {id}.mz.mul {id}.mz.bits {id}.mz.zs))",
            text.product, text.result_zero
        );
        if shape.reversed {
            let _ = write!(
                out,
                "\n(step {id} (cl {}) :rule symm :premises ({forward}))",
                text.equality
            );
        }

        // The synthesized-default streaming lane budgets approximate bytes
        // touched. Account for this intentionally large but bounded lowering;
        // its caller checks the budget before accepting the current step.
        self.charge(out.len() as u64);
        Some(out)
    }

    fn decode_mul_zero_shape(&self, equality: TermId) -> Option<MulZeroShape> {
        let TermData::App(Symbol::Named(eq), equality_args) = self.terms.get(equality) else {
            return None;
        };
        let [left, right] = equality_args.as_slice() else {
            return None;
        };
        if eq != "=" || self.terms.sort(equality) != &Sort::Bool {
            return None;
        }
        self.decode_mul_zero_orientation(equality, *left, *right, false)
            .or_else(|| self.decode_mul_zero_orientation(equality, *right, *left, true))
    }

    fn decode_mul_zero_orientation(
        &self,
        equality: TermId,
        product: TermId,
        result_zero: TermId,
        reversed: bool,
    ) -> Option<MulZeroShape> {
        let TermData::App(Symbol::Named(op), args) = self.terms.get(product) else {
            return None;
        };
        let [first, second] = args.as_slice() else {
            return None;
        };
        if op != "bvmul" {
            return None;
        }
        let Sort::BitVec(bits) = self.terms.sort(product) else {
            return None;
        };
        let width = bits.width;
        let operands = [*first, *second];
        if operands
            .iter()
            .any(|operand| self.terms.sort(*operand) != self.terms.sort(product))
            || !Self::is_internal_bv_zero(self.terms.get(result_zero), width)
        {
            return None;
        }
        let zero_operand = operands
            .iter()
            .position(|operand| Self::is_internal_bv_zero(self.terms.get(*operand), width))?;
        Some(MulZeroShape {
            equality,
            product,
            result_zero,
            operands,
            width,
            zero_operand,
            reversed,
        })
    }

    fn is_internal_bv_zero(term: &TermData, width: u32) -> bool {
        matches!(
            term,
            TermData::Const(Constant::BitVec { value, width: literal_width })
                if *literal_width == width && *value == 0u32.into()
        )
    }

    fn mul_zero_text(&self, shape: MulZeroShape) -> Option<MulZeroText> {
        let product = self.format_term(shape.product);
        let result_zero = self.format_term(shape.result_zero);
        let operands = [
            self.format_term(shape.operands[0]),
            self.format_term(shape.operands[1]),
        ];
        if product != format!("(bvmul {} {})", operands[0], operands[1]) {
            return None;
        }
        let printed_operands = split_application(&product, "bvmul")?;
        if printed_operands.as_slice() != operands {
            return None;
        }
        let (operand_zero, operand_width) =
            parse_printed_bitvec_literal(&operands[shape.zero_operand])?;
        let (result_value, result_width) = parse_printed_bitvec_literal(&result_zero)?;
        if operand_zero != 0u32.into()
            || result_value != 0u32.into()
            || operand_width != shape.width
            || result_width != shape.width
        {
            return None;
        }
        let equality = if shape.reversed {
            format!("(= {result_zero} {product})")
        } else {
            format!("(= {product} {result_zero})")
        };
        if self.format_term(shape.equality) != equality {
            return None;
        }
        Some(MulZeroText {
            equality,
            product,
            result_zero,
            operands,
        })
    }

    fn fresh_mul_zero_prefix(&self, id: ProofId, text: &MulZeroText) -> Option<String> {
        for nonce in 0_u64..=u64::MAX {
            let prefix = format!("__ay_bvmul_zero_{}_{}!", id.0, nonce);
            let printed_collision = [
                text.equality.as_str(),
                text.product.as_str(),
                text.result_zero.as_str(),
                text.operands[0].as_str(),
                text.operands[1].as_str(),
            ]
            .iter()
            .any(|rendered| rendered.contains(&prefix));
            if !printed_collision && !self.mul_zero_term_name_collision(&prefix) {
                return Some(prefix);
            }
        }
        None
    }

    fn mul_zero_term_name_collision(&self, prefix: &str) -> bool {
        (0..self.terms.len()).any(|index| {
            let term = self.terms.get(TermId(index as u32));
            match term {
                TermData::Var(name, _) => name.starts_with(prefix),
                TermData::App(symbol, _) => symbol.name().starts_with(prefix),
                TermData::Let(bindings, _) => {
                    bindings.iter().any(|(name, _)| name.starts_with(prefix))
                }
                TermData::Forall(bindings, ..) | TermData::Exists(bindings, ..) => {
                    bindings.iter().any(|(name, _)| name.starts_with(prefix))
                }
                _ => false,
            }
        }) || self
            .term_overrides
            .is_some_and(|overrides| overrides.values().any(|surface| surface.contains(prefix)))
    }
}
