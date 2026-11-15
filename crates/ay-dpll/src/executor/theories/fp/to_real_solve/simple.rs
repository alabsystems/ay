// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The no-site mixed lane shares construction, SAT and final publication stops.

use super::super::super::ChainSpend;
use super::super::to_real::build_lra_model_from_fp_to_real;
use super::*;

#[cfg(test)]
mod tests;

impl Executor {
    pub(super) fn encode_and_solve_fp_simple(
        &mut self,
        fp_assertions: &[TermId],
        mixed_assertions: &[TermId],
        stop: &FpStop,
        observe: &impl Fn(FpRealPhase),
    ) -> RealResult<SolveResult> {
        let encoding = self.encode_fp_assertions_controlled(fp_assertions, &[], stop, observe)?;
        let mut spent = ChainSpend::NONE;
        let result = self.solve_fp_sat_controlled(
            &encoding.base_clauses,
            &[],
            encoding.total_vars,
            &mut spent,
            stop,
            observe,
            FpRealPhase::SimpleSearch,
        )?;
        self.finish_fp_simple(result, &encoding, mixed_assertions, stop, observe)
    }

    fn finish_fp_simple(
        &mut self,
        result: SatResult,
        encoding: &FpEncoding,
        mixed_assertions: &[TermId],
        stop: &FpStop,
        observe: &impl Fn(FpRealPhase),
    ) -> RealResult<SolveResult> {
        if encoding.congruence_incomplete && matches!(result, SatResult::Sat(_)) {
            return Ok(self.admit_fp_real_sat(encoding));
        }
        let (fp_model, lra_model) = if let SatResult::Sat(ref bits) = result {
            let fp = Self::extract_fp_model_from_bits_controlled(
                bits,
                &encoding.term_to_fp,
                &encoding.rm_terms,
                encoding.var_offset,
                &self.ctx.terms,
                &mut || !stop.should_stop(),
            );
            let Some(fp) = fp else {
                self.fp_real_checkpoint(stop, observe, FpRealPhase::ModelExtracted)?;
                return Err(FpRealError::ModelDecode);
            };
            let lra = build_lra_model_from_fp_to_real(&self.ctx.terms, &fp, mixed_assertions);
            (Some(fp), (!lra.values.is_empty()).then_some(lra))
        } else {
            (None, None)
        };
        self.fp_real_checkpoint(stop, observe, FpRealPhase::ModelExtracted)?;
        let proposed = self.solve_and_store_model_full(
            result,
            &encoding.tseitin_result,
            None,
            None,
            lra_model,
            None,
            None,
            fp_model,
            None,
            None,
        );
        self.fp_real_checkpoint(stop, observe, FpRealPhase::ModelExtracted)?;
        Ok(proposed?)
    }
}
