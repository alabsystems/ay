// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Optional Real-guided targets may decline, but cannot swallow a resource stop.

use ay_core::Sort;

use super::super::support::is_pure_fp_assertion;
use super::super::to_real::{
    build_fp_target_unit_clauses, extract_fp_to_real_targets, rational_to_f64,
    rewrite_fp_to_real_with_vars, FpToRealSite,
};
use super::*;

impl Executor {
    pub(super) fn compute_real_guided_fp_target(
        &mut self,
        fp_assertions: &[TermId],
        mixed_assertions: &[TermId],
        sites: &[FpToRealSite],
        encoding: &FpEncoding,
        stop: &FpStop,
        observe: &impl Fn(FpRealPhase),
    ) -> RealResult<Option<Vec<CnfClause>>> {
        self.fp_real_checkpoint(stop, observe, FpRealPhase::TargetPreparation)?;
        if sites.is_empty() {
            return Ok(None);
        }
        let mut targets = HashMap::default();
        for &assertion in mixed_assertions {
            stop.check()?;
            extract_fp_to_real_targets(&self.ctx.terms, assertion, &mut targets);
        }
        stop.check()?;
        if targets.is_empty() {
            return self.compute_real_guided_fp_target_via_solver(
                fp_assertions,
                mixed_assertions,
                sites,
                encoding,
                stop,
                observe,
            );
        }
        target_clauses(sites, &targets, encoding, stop)
    }

    fn compute_real_guided_fp_target_via_solver(
        &mut self,
        fp_assertions: &[TermId],
        mixed_assertions: &[TermId],
        sites: &[FpToRealSite],
        encoding: &FpEncoding,
        stop: &FpStop,
        observe: &impl Fn(FpRealPhase),
    ) -> RealResult<Option<Vec<CnfClause>>> {
        let mut fp_arg_to_real_var = HashMap::default();
        for (i, site) in sites.iter().enumerate() {
            self.fp_real_checkpoint(stop, observe, FpRealPhase::Rewrite)?;
            fp_arg_to_real_var.entry(site.arg).or_insert_with(|| {
                self.ctx
                    .terms
                    .mk_var(&format!("__fp_target_{i}"), Sort::Real)
            });
            self.fp_real_checkpoint(stop, observe, FpRealPhase::Rewrite)?;
        }

        // Preserve the Real-only context that partitioning leaves on the FP
        // side; it can constrain variables used by mixed assertions.
        let mut all_presolve = Vec::new();
        for &assertion in fp_assertions {
            stop.check()?;
            if !is_pure_fp_assertion(&self.ctx.terms, assertion) {
                all_presolve.push(assertion);
            }
        }
        for &assertion in mixed_assertions {
            self.fp_real_checkpoint(stop, observe, FpRealPhase::Rewrite)?;
            all_presolve.push(rewrite_fp_to_real_with_vars(
                &mut self.ctx.terms,
                assertion,
                &fp_arg_to_real_var,
                &mut HashMap::default(),
            ));
            self.fp_real_checkpoint(stop, observe, FpRealPhase::Rewrite)?;
        }
        let proposed = self.solve_rewritten_mixed_subproblem(&all_presolve, stop, observe);
        // Check the attempt owner before converting an ordinary optional
        // failure into None. Restoration has already retained any child stop.
        stop.check()?;
        let mixed = match proposed {
            Ok(mixed) if matches!(mixed.result, SolveResult::Sat) => mixed,
            _ => return Ok(None),
        };
        let Some(lra_model) = mixed.lra_model else {
            return Ok(None);
        };
        let mut targets = HashMap::default();
        for site in sites {
            stop.check()?;
            if let Some(target) = fp_arg_to_real_var
                .get(&site.arg)
                .and_then(|variable| lra_model.values.get(variable))
            {
                targets.insert(site.arg, rational_to_f64(target));
            }
        }
        target_clauses(sites, &targets, encoding, stop)
    }
}

fn target_clauses(
    sites: &[FpToRealSite],
    targets: &HashMap<TermId, f64>,
    encoding: &FpEncoding,
    stop: &FpStop,
) -> RealResult<Option<Vec<CnfClause>>> {
    let mut units = Vec::new();
    for site in sites {
        stop.check()?;
        let Some(&target) = targets.get(&site.arg) else {
            continue;
        };
        let Some(decomposed) = encoding.term_to_fp.get(&site.arg) else {
            continue;
        };
        if let Some(clauses) = build_fp_target_unit_clauses(
            decomposed,
            encoding.var_offset,
            target,
            decomposed.precision.exponent_bits(),
            decomposed.precision.significand_bits(),
        ) {
            for clause in clauses {
                stop.check()?;
                units.push(clause);
            }
        }
    }
    stop.check()?;
    Ok((!units.is_empty()).then_some(units))
}
