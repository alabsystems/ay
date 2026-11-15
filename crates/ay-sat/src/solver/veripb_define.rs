// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-veripb-hints` for factoring's dividers (x ∨ f_1) … (x ∨ f_n): one
//! pseudo-Boolean definition of the fresh x instead of one `red` per divider
//! (`VeripbWriter::add_conjunction_dividers`). Each `red` costs the official
//! check a scan of its database; on aes_equiv_encry_3_rounds factoring wrote
//! 142,653 of them in the first minute, more than any other pass.

use super::*;
use std::io;

impl Solver {
    /// Whether factoring's `dividers`, each `[x, f]` for one fresh `x`, go
    /// through one definition (`proof_emit_veripb_dividers`): hints on and at
    /// least two dividers. The caller then writes the blocked clause
    /// (¬x ∨ ¬f_1 ∨ … ∨ ¬f_n) first, so the definition's witness finds it
    /// and nothing else.
    pub(super) fn veripb_dividers_definable(&mut self, dividers: &[Vec<Literal>]) -> bool {
        let Some(&fresh) = dividers.first().and_then(|d| d.first()) else {
            return false;
        };
        dividers.len() >= 2
            && dividers
                .iter()
                .all(|d| matches!(d.as_slice(), [x, _] if *x == fresh))
            && self.veripb_hints_active()
    }

    /// Write factoring's `dividers` through one definition, with the
    /// bookkeeping of a trusted-transform addition for each. `Ok(false)`:
    /// nothing written.
    pub(super) fn proof_emit_veripb_dividers(
        &mut self,
        dividers: &[Vec<Literal>],
    ) -> io::Result<bool> {
        if !self.veripb_dividers_definable(dividers) {
            return Ok(false);
        }
        let mut lits: Vec<Literal> = Vec::with_capacity(1 + dividers.len());
        for d in dividers {
            if let [x, f] = d.as_slice() {
                if lits.is_empty() {
                    lits.push(*x);
                }
                lits.push(*f);
            }
        }
        if self.cold.proof_vars_compacted {
            lits = self.externalize_lits_for_proof(&lits);
        }
        let Some((&fresh, factors)) = lits.split_first() else {
            return Ok(false);
        };
        self.veripb_drop_antecedents();
        let Some(manager) = self.proof_manager.as_mut() else {
            return Ok(false);
        };
        if !manager.emit_veripb_conjunction_dividers(fresh, factors)? {
            return Ok(false);
        }
        self.note_unhinted_add();
        for d in dividers {
            self.triage_on_emission(d);
            if let Some(checker) = self.cold.forward_checker.as_mut() {
                checker.add_trusted_transform(d);
            }
            self.note_proof_add();
        }
        Ok(true)
    }
}
