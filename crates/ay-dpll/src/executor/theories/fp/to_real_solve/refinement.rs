// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Preserve exact/binade refinement semantics under one terminal stop owner.

use super::super::super::ChainSpend;
use super::super::support::{is_pure_fp_assertion, partition_fp_assertions};
use super::super::to_real::{
    block_decided_modes, choose_blocking_clause, collect_child_mode_dependencies,
    collect_fp_to_real_sites, rewrite_fp_to_real_for_model,
};
use super::*;

#[cfg(test)]
mod tests;

impl Executor {
    pub(super) fn run_fp_to_real(
        &mut self,
        stop: &FpStop,
        observe: &impl Fn(FpRealPhase),
    ) -> RealResult<SolveResult> {
        stop.check()?;
        let (fp_assertions, mixed_assertions) =
            partition_fp_assertions(&self.ctx.terms, &self.ctx.assertions);
        let sites = collect_fp_to_real_sites(&self.ctx.terms, &mixed_assertions);
        stop.check()?;
        if sites.is_empty() {
            return self.encode_and_solve_fp_simple(
                &fp_assertions,
                &mixed_assertions,
                stop,
                observe,
            );
        }
        let encoding =
            self.encode_fp_assertions_controlled(&fp_assertions, &sites, stop, observe)?;
        let mut spent = ChainSpend::NONE;
        let target = self.compute_real_guided_fp_target(
            &fp_assertions,
            &mixed_assertions,
            &sites,
            &encoding,
            stop,
            observe,
        )?;
        if let Some(target_clauses) = target {
            let fp_result = self.solve_fp_sat_controlled(
                &encoding.base_clauses,
                &target_clauses,
                encoding.total_vars,
                &mut spent,
                stop,
                observe,
                FpRealPhase::TargetedSearch,
            )?;
            if let SatResult::Sat(ref sat_model) = fp_result {
                let mixed = self.try_fp_real_candidate(
                    sat_model,
                    &encoding,
                    &mixed_assertions,
                    stop,
                    observe,
                );
                // Ordinary unavailable targets retain refinement. A child stop
                // must propagate before discarding an optional result/error.
                stop.check()?;
                match mixed {
                    Ok(FpRefinementStep::Sat) => return Ok(self.admit_fp_real_sat(&encoding)),
                    // A malformed SAT assignment cannot license a new target
                    // or refinement solve. Ordinary unavailable targets still can.
                    Err(FpRealError::ModelDecode) => return Err(FpRealError::ModelDecode),
                    _ => {}
                }
            }
        }
        self.refine_fp_real(
            &encoding,
            &sites,
            &mixed_assertions,
            &mut spent,
            stop,
            observe,
        )
    }

    fn refine_fp_real(
        &mut self,
        encoding: &FpEncoding,
        sites: &[super::super::to_real::FpToRealSite],
        mixed_assertions: &[TermId],
        spent: &mut ChainSpend,
        stop: &FpStop,
        observe: &impl Fn(FpRealPhase),
    ) -> RealResult<SolveResult> {
        const MAX_REFINEMENTS: usize = 64;
        const EXACT_PER_BINADE: usize = 4;
        let mut blocking_clauses: Vec<CnfClause> = Vec::new();
        let mut binade_attempts = HashMap::default();
        let mut used_binade_blocking = false;
        for _round in 0..MAX_REFINEMENTS {
            let fp_result = self.solve_fp_sat_controlled(
                &encoding.base_clauses,
                &blocking_clauses,
                encoding.total_vars,
                spent,
                stop,
                observe,
                FpRealPhase::RefinementSearch,
            )?;
            match fp_result {
                SatResult::Unsat(_) | SatResult::Unknown => {
                    // Binade blocking excludes possible witnesses; its UNSAT
                    // cannot refute the original problem.
                    let safe = if used_binade_blocking && matches!(fp_result, SatResult::Unsat(_)) {
                        SatResult::Unknown
                    } else {
                        fp_result
                    };
                    return Ok(self.store_unknown_or_unsat(safe, &encoding.tseitin_result)?);
                }
                SatResult::Sat(ref sat_model) => {
                    match self.try_fp_real_candidate(
                        sat_model,
                        encoding,
                        mixed_assertions,
                        stop,
                        observe,
                    )? {
                        FpRefinementStep::Sat => return Ok(self.admit_fp_real_sat(encoding)),
                        FpRefinementStep::Unknown => {
                            return Ok(self.store_unknown_or_unsat(
                                SatResult::Unknown,
                                &encoding.tseitin_result,
                            )?);
                        }
                        FpRefinementStep::Block(modes) => {
                            stop.check()?;
                            let (blocking, is_binade) = choose_blocking_clause(
                                sat_model,
                                sites,
                                &encoding.term_to_fp,
                                encoding.var_offset,
                                &mut binade_attempts,
                                EXACT_PER_BINADE,
                            );
                            stop.check()?;
                            used_binade_blocking |= is_binade;
                            if blocking.literals().is_empty() {
                                return Ok(self.store_unknown_or_unsat(
                                    SatResult::Unknown,
                                    &encoding.tseitin_result,
                                )?);
                            }
                            blocking_clauses.push(block_decided_modes(
                                blocking,
                                &modes,
                                &encoding.rm_terms,
                                sat_model,
                                encoding.var_offset,
                            ));
                        }
                    }
                }
                _ => {
                    return Ok(
                        self.store_unknown_or_unsat(SatResult::Unknown, &encoding.tseitin_result)?
                    )
                }
            }
        }
        Ok(self.store_unknown_or_unsat(SatResult::Unknown, &encoding.tseitin_result)?)
    }

    fn try_fp_real_candidate(
        &mut self,
        sat_model: &[bool],
        encoding: &FpEncoding,
        mixed_assertions: &[TermId],
        stop: &FpStop,
        observe: &impl Fn(FpRealPhase),
    ) -> RealResult<FpRefinementStep> {
        stop.check()?;
        let fp_model = Self::extract_fp_model_from_bits_controlled(
            sat_model,
            &encoding.term_to_fp,
            &encoding.rm_terms,
            encoding.var_offset,
            &self.ctx.terms,
            &mut || !stop.should_stop(),
        );
        self.fp_real_checkpoint(stop, observe, FpRealPhase::ModelExtracted)?;
        let fp_model = fp_model.ok_or(FpRealError::ModelDecode)?;
        self.try_mixed_subproblem(
            &fp_model,
            mixed_assertions,
            sat_model,
            &encoding.tseitin_result,
            stop,
            observe,
        )
    }

    fn try_mixed_subproblem(
        &mut self,
        fp_model: &FpModel,
        mixed_assertions: &[TermId],
        sat_model: &[bool],
        tseitin_result: &ay_core::TseitinResult,
        stop: &FpStop,
        observe: &impl Fn(FpRealPhase),
    ) -> RealResult<FpRefinementStep> {
        let mut non_fp_assertions = Vec::new();
        for &assertion in &self.ctx.assertions {
            stop.check()?;
            if !is_pure_fp_assertion(&self.ctx.terms, assertion) {
                non_fp_assertions.push(assertion);
            }
        }
        let (rewritten, undef_vars, decided_modes) =
            self.rewrite_mixed_roots(&non_fp_assertions, fp_model, stop, observe)?;
        let proposed = self.solve_rewritten_mixed_subproblem(&rewritten, stop, observe);
        stop.check()?;
        let mixed = proposed?;
        match mixed.result {
            SolveResult::Sat => {
                self.build_merged_fp_real_model(
                    fp_model,
                    mixed,
                    mixed_assertions,
                    sat_model,
                    tseitin_result,
                    &undef_vars,
                );
                self.fp_real_checkpoint(stop, observe, FpRealPhase::ModelExtracted)?;
                Ok(FpRefinementStep::Sat)
            }
            SolveResult::Unknown => Ok(FpRefinementStep::Unknown),
            SolveResult::Unsat(_) => Ok(FpRefinementStep::Block(self.modes_the_refutation_needs(
                &non_fp_assertions,
                fp_model,
                decided_modes,
                stop,
                observe,
            )?)),
        }
    }

    /// The Real subproblem's roots under `fp_model`: every `fp.to_real` and
    /// every decided rounding mode replaced by its value, with the modes those
    /// roots read (`collect_child_mode_dependencies`).
    fn rewrite_mixed_roots(
        &mut self,
        roots: &[TermId],
        fp_model: &FpModel,
        stop: &FpStop,
        observe: &impl Fn(FpRealPhase),
    ) -> RealResult<(Vec<TermId>, HashMap<String, TermId>, Vec<TermId>)> {
        let mut rewrite_cache = HashMap::default();
        let mut undef_vars = HashMap::default();
        let mut rewritten = Vec::new();
        let mut decided_modes = Vec::new();
        for &assertion in roots {
            self.fp_real_checkpoint(stop, observe, FpRealPhase::Rewrite)?;
            collect_child_mode_dependencies(
                &self.ctx.terms,
                assertion,
                fp_model,
                &mut decided_modes,
            );
            rewritten.push(rewrite_fp_to_real_for_model(
                &mut self.ctx.terms,
                assertion,
                fp_model,
                &mut rewrite_cache,
                &mut undef_vars,
            ));
            self.fp_real_checkpoint(stop, observe, FpRealPhase::Rewrite)?;
        }
        Ok((rewritten, undef_vars, decided_modes))
    }

    /// The decided modes an UNSAT Real subproblem's block must carry.
    ///
    /// None when the subproblem stays UNSAT with every mode left free: the
    /// site values alone refute it, and the block over the site bits is the
    /// one this loop always used. Otherwise all of `decided_modes`, whose
    /// literals made it UNSAT. The second solve runs only for a formula whose
    /// Real side reads a decided mode, so the site-only block, and with it the
    /// exact-block `unsat`, survives a mode that `(or (= r RNE) b)` merely
    /// mentions.
    fn modes_the_refutation_needs(
        &mut self,
        roots: &[TermId],
        fp_model: &FpModel,
        decided_modes: Vec<TermId>,
        stop: &FpStop,
        observe: &impl Fn(FpRealPhase),
    ) -> RealResult<Vec<TermId>> {
        if decided_modes.is_empty() {
            return Ok(decided_modes);
        }
        let free = FpModel {
            values: fp_model.values.clone(),
            rm_values: Default::default(),
        };
        let (rewritten, _, _) = self.rewrite_mixed_roots(roots, &free, stop, observe)?;
        let proposed = self.solve_rewritten_mixed_subproblem(&rewritten, stop, observe);
        stop.check()?;
        Ok(match proposed?.result {
            SolveResult::Unsat(_) => Vec::new(),
            SolveResult::Sat | SolveResult::Unknown => decided_modes,
        })
    }
}
