// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `zero_extend` in the complete bit-blast lane: one `refl` identity per
//! application, the only step that relies on Clean's consumer rule
//! `dialect:expand_zero_extend` (`CleanOnlySpelling::consumer_rule`), as in
//! the two packed lanes.
//!
//! Until 2026-09-30 this lane printed one `cong` from the word's reference,
//! `((_ zero_extend k) x)` behind a `define-fun`, straight to the blasted
//! `concat`: a congruence across two heads that holds only once the consumer
//! has read the operator as its definition. That folded the reliance into a
//! rule application. Now the reliance is a `refl` whose right side IS the
//! definition, `(concat Z x)` over the operands' own references, and the
//! `cong` that follows relates two `concat`s, which standard Alethe checks.

use super::super::dialect::{self, AletheDialect, CleanOnlySpelling};
use super::{Blasted, Blaster};

impl Blaster<'_, '_> {
    /// Clean's zero-amount reading is an identity, not an application on
    /// which to run Cong. Carry the already-built operand's bits through a
    /// disclosed Refl/Trans derivation. The pinned lane stays opaque here.
    pub(super) fn zero_extend_zero_word(&mut self, arg: usize, width: u32) -> Option<usize> {
        let operand = self.words.get(arg)?;
        if dialect::current() != AletheDialect::Clean
            || operand.width != width
            || operand.bits.len() != width as usize
        {
            return None;
        }
        let operand_reference = operand.reference.clone();
        let operand_step = operand.step.clone();
        let bits = operand.bits.clone();
        let reference =
            self.bind_word_reference(format!("((_ zero_extend 0) {operand_reference})"), width)?;
        let identity = self.step_name(".zx0");
        let step = self.step_name("");
        let bbterm = self.bbterm(&bits);
        self.push_step(&format!(
            "(step {identity} (cl (= {reference} {operand_reference})) :rule refl)"
        ))?;
        dialect::note_clean_only(CleanOnlySpelling::ZeroExtendAsConcat);
        self.push_step(&format!(
            "(step {step} (cl (= {reference} {bbterm})) :rule trans :premises ({identity} {operand_step}))"
        ))?;
        self.words.push(super::Word {
            reference,
            width,
            bits,
            step,
        });
        Some(self.words.len() - 1)
    }

    /// The steps proving `(= reference blasted)` for a `zero_extend` word with
    /// already-blasted operands `zero` (the all-zero word) and `arg`:
    ///
    /// * `S.zx`: `(= reference (concat zero_ref arg_ref))` by `refl`, the
    ///   identity the consumer's reading admits;
    /// * `congruence`: `(= (concat zero_ref arg_ref) blasted)` by `cong` over
    ///   the operands' bit-blasting steps;
    /// * `S.zxcg`: their `trans`, the step returned for the rest of the word's
    ///   derivation to use.
    pub(super) fn zero_extend_identity(
        &mut self,
        reference: &str,
        zero: usize,
        arg: usize,
        congruence: &str,
        blasted: &Blasted,
    ) -> Option<String> {
        let definition = format!("(concat {} {})", self.word_ref(zero), self.word_ref(arg));
        let identity = self.step_name(".zx");
        self.push_step(&format!(
            "(step {identity} (cl (= {reference} {definition})) :rule refl)"
        ))?;
        dialect::note_clean_only(CleanOnlySpelling::ZeroExtendAsConcat);
        let premises = blasted.operand_steps.join(" ");
        self.push_step(&format!(
            "(step {congruence} (cl (= {definition} {})) :rule cong :premises ({premises}))",
            blasted.blasted_application
        ))?;
        let joined = self.step_name(".zxcg");
        self.push_step(&format!(
            "(step {joined} (cl (= {reference} {})) :rule trans :premises ({identity} {congruence}))",
            blasted.blasted_application
        ))?;
        Some(joined)
    }
}
