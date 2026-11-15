// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native SOS has no stock Alethe inference. Never relabel it as one: a
//! certificate the strict checker accepts is LOWERED into pinned-checker rules
//! (`la_mult_pos`, `la_mult_neg`, `la_generic`, `poly_simp`, ..., see
//! [`lowering`]); a certificate the lowering cannot render stays an honest
//! `hole`.

use ay_core::{NraSosCertificate, NraSosOrigin};

use super::*;

mod lowering;
#[cfg(test)]
mod tests;

/// Whether one native SOS step has the checked Alethe lowering the printer
/// emits for it. This is the printer's own answer, built and discarded, so the
/// publication wire-gap screen and the exporter cannot disagree about what a
/// given override channel renders.
#[must_use]
pub fn nra_sos_lowering_supported(
    terms: &TermStore,
    clause: &[TermId],
    certificate: &NraSosCertificate,
    term_overrides: Option<&HashMap<TermId, String>>,
) -> bool {
    let printer = AlethePrinter::new_with_overrides(terms, term_overrides);
    printer
        .preflight_nra_sos_step(ProofId(0), clause, certificate)
        .is_ok()
        && printer
            .format_nra_sos_lowering(ProofId(0), clause, certificate)
            .is_some()
}

impl AlethePrinter<'_> {
    pub(super) fn preflight_nra_sos_step(
        &self,
        id: ProofId,
        clause: &[TermId],
        certificate: &NraSosCertificate,
    ) -> Result<(), AlethePrintError> {
        if clause.len() > NraSosCertificate::MAX_CLAUSE_SLOTS
            || certificate.validate_shape().is_err()
        {
            return Err(AlethePrintError::UnsupportedStep { id });
        }
        self.charge(
            (clause.len()
                + certificate.basis.len()
                + certificate.terms.len()
                + certificate.gram.len().pow(2)) as u64,
        );
        if self.work_budget_exhausted() {
            return Err(self.work_budget_error(id.0));
        }
        if clause
            .iter()
            .any(|term| term.index() >= self.terms.len() || self.terms.sort(*term) != &Sort::Bool)
            || certificate.basis.iter().flatten().any(|term| {
                term.index() >= self.terms.len()
                    || !matches!(self.terms.sort(*term), Sort::Int | Sort::Real)
                    || !matches!(self.terms.get(*term), TermData::Var(..))
            })
            || certificate.terms.iter().any(|term| match term.origin {
                NraSosOrigin::ClauseLiteral { position } => position as usize >= clause.len(),
                NraSosOrigin::Product { left, right } => {
                    left as usize >= clause.len() || right as usize >= clause.len()
                }
            })
        {
            return Err(AlethePrintError::UnsupportedStep { id });
        }
        Ok(())
    }

    pub(super) fn format_nra_sos_step(
        &self,
        id: ProofId,
        clause: &[TermId],
        certificate: &NraSosCertificate,
    ) -> Result<String, AlethePrintError> {
        self.preflight_nra_sos_step(id, clause, certificate)?;
        let lowered = self.format_nra_sos_lowering(id, clause, certificate);
        if self.work_budget_exhausted() {
            return Err(self.work_budget_error(id.0));
        }
        if let Some(lowered) = lowered {
            return Ok(lowered);
        }
        let rendered_clause = self.format_clause(clause);
        if self.work_budget_exhausted() {
            return Err(self.work_budget_error(id.0));
        }
        Ok(format!(
            "; {id} ay-nra-sos: native certificate retained in AY bundle; no Alethe lowering\n(step {id} {rendered_clause} :rule {})",
            ay_core::UNPROVED_STEP_RULE,
        ))
    }
}
