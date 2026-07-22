// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Formula composition for TRL trace ranges.
//!
//! This module implements the composition pipeline used when TRL detects a loop
//! in the execution trace. It chains per-step transition formulas into a single
//! composed transition, then specialises and projects away temporaries.
//!
//! Key operations:
//! - [`TrlSolver::chain_formulas`]: Compose two transition formulas by wiring
//!   post-state variables of the first to pre-state variables of the second.
//! - [`TrlSolver::compress`]: Chain all steps in a trace range into one formula.
//! - [`TrlSolver::specialize`]: SIP + MBP pipeline to eliminate temporaries.
//!
//! Reference: LoAT `trputil.cpp:147-239`, `formulapreprocessing.cpp:53-79`.

use crate::cvp::sip;
use crate::expr_vars::expr_var_names;
use crate::smt::SmtValue;
use crate::{ChcExpr, ChcVar};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

use super::TrlSolver;

/// Result type for chain_formulas:
/// (chained_formula, fst_rename_map, snd_rename_map, fst_vars, snd_vars)
pub(super) type ChainFormulasResult = (
    ChcExpr,
    FxHashMap<String, String>,
    FxHashMap<String, String>,
    FxHashSet<String>,
    FxHashSet<String>,
);

impl TrlSolver {
    /// Compose two transition formulas (fst . snd) by wiring fst's post-vars to snd's pre-vars.
    ///
    /// Returns:
    /// - `chained`: the composed formula
    /// - `sigma1_inv`: mapping from fresh vars to the corresponding vars from `fst`
    /// - `sigma2_inv`: mapping from fresh vars to the corresponding vars from `snd`
    /// - `fst_var_names`: variable names occurring in `sigma1(fst)`
    /// - `snd_var_names`: variable names occurring in `sigma2(snd)`
    ///
    /// This is the AY analogue of LoAT's `Preprocess::chain` for formulas.
    /// Reference: `reference/loat/src/lib/preprocessing/formulapreprocessing.cpp:53-79`.
    pub(super) fn chain_formulas(&self, fst: &ChcExpr, snd: &ChcExpr) -> ChainFormulasResult {
        let fst_vars_vec = fst.vars();
        let snd_vars_vec = snd.vars();

        let fst_vars: FxHashSet<ChcVar> = fst_vars_vec.iter().cloned().collect();
        let snd_vars: FxHashSet<ChcVar> = snd_vars_vec.iter().cloned().collect();

        let mut used_names: FxHashSet<String> = fst_vars_vec
            .iter()
            .chain(&snd_vars_vec)
            .map(|v| v.name.clone())
            .collect();

        let mut fresh_id: usize = 0;
        let mut fresh_var_name = |prefix: &str, used: &mut FxHashSet<String>| -> String {
            loop {
                let name = format!("{prefix}_{fresh_id}");
                fresh_id += 1;
                if used.insert(name.clone()) {
                    return name;
                }
            }
        };

        // sigma1: rename fst post-vars to fresh intermediates
        // sigma2: rename snd pre-vars to the same intermediates; also rename colliding temps in snd
        let mut sigma1: Vec<(ChcVar, ChcExpr)> = Vec::new();
        let mut sigma2: Vec<(ChcVar, ChcExpr)> = Vec::new();

        // Inverse maps (fresh -> original) for model composition.
        let mut sigma1_inv: FxHashMap<String, String> = FxHashMap::default();
        let mut sigma2_inv: FxHashMap<String, String> = FxHashMap::default();

        // Wire each state var's post to next step's pre.
        for pre in &self.ts.vars {
            let post = ChcVar::new(format!("{}_next", pre.name), pre.sort.clone());

            // Only wire vars that actually occur.
            if !(fst_vars.contains(pre)
                || fst_vars.contains(&post)
                || snd_vars.contains(pre)
                || snd_vars.contains(&post))
            {
                continue;
            }

            let fresh_name = fresh_var_name(&format!("__trl_chain_{}", pre.name), &mut used_names);
            let fresh = ChcVar::new(fresh_name, pre.sort.clone());

            sigma1.push((post.clone(), ChcExpr::var(fresh.clone())));
            sigma2.push((pre.clone(), ChcExpr::var(fresh.clone())));

            sigma1_inv.insert(fresh.name.clone(), post.name.clone());
            sigma2_inv.insert(fresh.name.clone(), pre.name.clone());
        }

        // Rename any temp vars in snd that clash with fst (e.g., trace_id).
        for v in snd_vars_vec {
            if self.is_temp_var(&v) && fst_vars.contains(&v) {
                let fresh_name =
                    fresh_var_name(&format!("__trl_chain_tmp_{}", v.name), &mut used_names);
                let fresh = ChcVar::new(fresh_name, v.sort.clone());
                sigma2.push((v.clone(), ChcExpr::var(fresh.clone())));
                sigma2_inv.insert(fresh.name.clone(), v.name.clone());
            }
        }

        let fst_renamed = fst.substitute(&sigma1);
        let snd_renamed = snd.substitute(&sigma2);

        let fst_var_names: FxHashSet<String> = expr_var_names(&fst_renamed);
        let snd_var_names: FxHashSet<String> = expr_var_names(&snd_renamed);

        (
            ChcExpr::and_all(vec![fst_renamed, snd_renamed]),
            sigma1_inv,
            sigma2_inv,
            fst_var_names,
            snd_var_names,
        )
    }

    /// Compress a trace range into a single composed transition formula.
    ///
    /// Implements LoAT's `TRPUtil::compress(range)`:
    /// `reference/loat/src/trputil.cpp:147-190`.
    pub(super) fn compress(
        &self,
        start: usize,
        end: usize,
    ) -> (ChcExpr, FxHashMap<String, SmtValue>) {
        if start > end {
            return (ChcExpr::Bool(true), FxHashMap::default());
        }

        let Some(mut loop_formula) = self.get_implicant_for_step(start) else {
            return (ChcExpr::Bool(true), FxHashMap::default());
        };
        let Some(mut loop_model) = self.trace.elements.get(start).map(|e| e.model.clone()) else {
            return (ChcExpr::Bool(true), FxHashMap::default());
        };

        for i in (start + 1)..=end {
            let Some(rule) = self.get_implicant_for_step(i) else {
                break;
            };
            let Some(rule_model) = self.trace.elements.get(i).map(|e| &e.model) else {
                break;
            };

            let (chained, sigma1_inv, sigma2_inv, fst_vars, snd_vars) =
                self.chain_formulas(&loop_formula, &rule);

            // Compose a model for the chained formula by renaming the per-step models.
            let mut chained_model: FxHashMap<String, SmtValue> = FxHashMap::default();

            for name in &fst_vars {
                let src = sigma1_inv.get(name).unwrap_or(name);
                let val = loop_model.get(src).cloned();
                debug_assert!(
                    val.is_some(),
                    "compress: missing fst model value for `{src}` (needed for `{name}`)"
                );
                if let Some(v) = val {
                    chained_model.insert(name.clone(), v);
                }
            }

            for name in &snd_vars {
                let src = sigma2_inv.get(name).unwrap_or(name);
                let val = rule_model.get(src).cloned();
                debug_assert!(
                    val.is_some(),
                    "compress: missing snd model value for `{src}` (needed for `{name}`)"
                );
                if let Some(v) = val {
                    if let Some(prev) = chained_model.get(name) {
                        debug_assert_eq!(
                            prev, &v,
                            "compress: inconsistent value for shared var `{name}`"
                        );
                    }
                    chained_model.insert(name.clone(), v);
                }
            }

            // Validate composed model: Some(false) = definitely wrong (bug),
            // None = incomplete evaluation (missing vars after renaming, expected).
            // LoAT doesn't compose models at all — this is a best-effort guide for SIP.
            debug_assert!(
                self.mbp.eval_bool(&chained, &chained_model) != Some(false),
                "compress: composed model definitively violates composed formula at step {i}"
            );

            loop_formula = chained;
            loop_model = chained_model;
        }

        (loop_formula, loop_model)
    }

    /// Specialize a trace range to a stable transition formula.
    ///
    /// Pipeline (LoAT):
    /// 1. compress(range)
    /// 2. SIP (syntactic implicant)
    /// 3. preprocessFormula (handled in #1515)
    /// 4. MBP eliminate temporary variables
    ///
    /// Reference: `reference/loat/src/trputil.cpp:228-239`.
    pub(super) fn specialize(
        &self,
        start: usize,
        end: usize,
        eliminate: impl Fn(&ChcVar) -> bool,
    ) -> (ChcExpr, FxHashMap<String, SmtValue>) {
        if start > end {
            return (ChcExpr::Bool(true), FxHashMap::default());
        }

        let (transition, model) = self.compress(start, end);

        // SIP: pick a satisfied conjunction (cube) under the model.
        let sip = sip(&transition, &model);

        // #1515: Preprocess formula via Equality Propagation and FM Variable Elimination
        let sip_eq = sip.into_propagate_equalities();

        let vars_to_eliminate: Vec<ChcVar> =
            sip_eq.vars().into_iter().filter(|v| eliminate(v)).collect();
        let preprocessed = if vars_to_eliminate.is_empty() {
            sip_eq
        } else {
            let vars_to_eliminate_names: FxHashSet<&str> =
                vars_to_eliminate.iter().map(|v| v.name.as_str()).collect();

            let conjuncts = sip_eq.conjuncts().into_iter().cloned().collect::<Vec<_>>();
            crate::proof_interpolation::try_fourier_motzkin_elimination(
                &conjuncts,
                &vars_to_eliminate_names,
            )
            .unwrap_or(sip_eq)
        };

        // MBP eliminate any remaining vars.
        let vars_to_eliminate: Vec<ChcVar> = preprocessed
            .vars()
            .into_iter()
            .filter(|v| eliminate(v))
            .collect();

        if vars_to_eliminate.is_empty() {
            return (preprocessed, model);
        }

        let projected = self.mbp.project(&preprocessed, &vars_to_eliminate, &model);
        (projected, model)
    }
}
