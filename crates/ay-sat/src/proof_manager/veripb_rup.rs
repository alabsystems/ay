// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Annotated RUP emission for `--sat-veripb-hints` (`solver/veripb_hints.rs`).

use super::*;

impl ProofManager {
    /// `--sat-veripb-hints`: emit a derived clause as annotated RUP on the
    /// VeriPB output (`rup <C> : <ids> ;`), with the bookkeeping a non-LRAT
    /// derived `emit_add` does. Refused (an error) on any other format.
    pub(crate) fn emit_add_veripb_rup(
        &mut self,
        clause: &[Literal],
        hints: &[u64],
    ) -> io::Result<()> {
        debug_assert!(
            !self.lrat_mode,
            "BUG: annotated VeriPB RUP on an LRAT proof"
        );
        #[cfg(debug_assertions)]
        self.checker.add_derived(clause);
        self.output.add_veripb_rup(clause, hints)?;
        self.last_add = Some(LastAdd::new(0, clause));
        Ok(())
    }

    /// `--sat-veripb-hints`: a fresh variable's clauses `[fresh, f]` for each
    /// `f` of `factors` (proof-surface literals), written through one
    /// pseudo-Boolean definition (`VeripbWriter::add_conjunction_dividers`)
    /// with the bookkeeping of trusted-transform additions. `Ok(false)`:
    /// nothing written; the caller writes the clauses one by one.
    pub(crate) fn emit_veripb_conjunction_dividers(
        &mut self,
        fresh: Literal,
        factors: &[Literal],
    ) -> io::Result<bool> {
        debug_assert!(!self.lrat_mode, "BUG: VeriPB definition on an LRAT proof");
        if !self
            .output
            .add_veripb_conjunction_dividers(fresh, factors)?
        {
            return Ok(false);
        }
        for &f in factors {
            #[cfg(debug_assertions)]
            self.checker.add_trusted_transform(&[fresh, f]);
            self.last_add = Some(LastAdd::new(0, &[fresh, f]));
        }
        Ok(true)
    }
}
