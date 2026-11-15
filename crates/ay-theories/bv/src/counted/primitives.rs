// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Paid continuation operations for later theory refinements, not theory axioms.

use super::*;

impl CountedBvEncoder<'_> {
    /// Allocate a new word under the same variable namespace and ledger.
    /// Its value is unconstrained until source/theory constraints establish it.
    pub fn fresh_bits(&mut self, width: usize) -> Result<BvBits> {
        if width == 0 {
            return Err(self.refuse(CountedBvError::Invalid));
        }
        let owner = self.owner.clone();
        owner.with_work(|_| {
            let bits = self.solver.counted_fresh_bits(width);
            Ok(self.check().map(|()| bits))
        })?
    }

    /// Append a clause whose literals all belong to this encoder's namespace.
    /// The caller must justify theory/refinement clauses; this supplies no proof.
    pub fn add_clause(&mut self, literals: &[CnfLit]) -> Result<()> {
        self.validate_literals(literals)?;
        let owner = self.owner.clone();
        owner.with_work(|_| {
            self.solver.emit_clause(literals);
            Ok(self.check())
        })?
    }

    /// Build the existing exact word-equality circuit, with paid input copies.
    /// This can connect late array-read words without replacing the owner.
    pub fn equal_words(&mut self, left: &[CnfLit], right: &[CnfLit]) -> Result<CnfLit> {
        if left.is_empty() || left.len() != right.len() {
            return Err(self.refuse(CountedBvError::Invalid));
        }
        self.validate_literals(left)?;
        self.validate_literals(right)?;
        let owner = self.owner.clone();
        owner.with_work(|_| {
            let result = (|| {
                let left = self.copy_word(left)?;
                let right = self.copy_word(right)?;
                let literal = self.solver.bitblast_eq(&left, &right);
                self.check()?;
                Ok(literal)
            })();
            Ok(result)
        })?
    }

    /// Build an exact conditional word using already-owned literal identities.
    pub fn mux_words(
        &mut self,
        then_word: &[CnfLit],
        else_word: &[CnfLit],
        selector: CnfLit,
    ) -> Result<BvBits> {
        if then_word.is_empty() || then_word.len() != else_word.len() {
            return Err(self.refuse(CountedBvError::Invalid));
        }
        self.validate_literals(then_word)?;
        self.validate_literals(else_word)?;
        self.validate_literals(&[selector])?;
        let owner = self.owner.clone();
        owner.with_work(|_| {
            let result = (|| {
                let then_word = self.copy_word(then_word)?;
                let else_word = self.copy_word(else_word)?;
                let result = self.solver.bitwise_mux(&then_word, &else_word, selector);
                self.check()?;
                Ok(result)
            })();
            Ok(result)
        })?
    }

    fn copy_word(&self, bits: &[CnfLit]) -> Result<BvBits> {
        self.solver.counted_copy_bits(bits).ok_or_else(|| {
            let error = self
                .owner
                .check()
                .err()
                .unwrap_or(CountedAdmissionError::StorageExhausted);
            self.refuse(CountedBvError::Stopped(error))
        })
    }

    fn validate_literals(&self, literals: &[CnfLit]) -> Result<()> {
        self.owner.admit(
            literals
                .len()
                .checked_add(1)
                .ok_or_else(|| self.refuse(CountedBvError::Invalid))?,
            0,
        )?;
        for &literal in literals {
            if literal == 0 || literal == i32::MIN || literal.unsigned_abs() >= self.solver.next_var
            {
                return Err(self.refuse(CountedBvError::Invalid));
            }
        }
        self.check()
    }
}
