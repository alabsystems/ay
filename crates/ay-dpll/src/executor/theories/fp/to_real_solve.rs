// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! FP-to-Real refinement loop and real-guided target computation.
//!
//! Handles `fp.to_real` solve pipeline: partition assertions, encode FP
//! side as CNF, then iterate SAT → model → rewrite → mixed solve → block.
//! Also computes real-guided FP target values for pre-solving.
//!
//! Extracted from `fp.rs` for code health (#5970).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{CnfClause, Sort, TermId};
use ay_fp::FpModel;
use ay_lra::LraModel;
use ay_sat::SatResult;

use crate::executor_types::{Result, SolveResult, UnknownReason};
use crate::features::StaticFeatures;

use super::super::super::Executor;
use super::support::{is_pure_fp_assertion, partition_fp_assertions};
use super::to_real::{
    build_fp_target_unit_clauses, build_lra_model_from_fp_to_real, choose_blocking_clause,
    collect_fp_to_real_sites, extract_fp_to_real_targets, pin_undefined_fp_to_real,
    rational_to_f64, rewrite_fp_to_real_for_model, rewrite_fp_to_real_with_vars, FpEncoding,
    FpRefinementStep, FpToRealSite, MixedSubproblemResult,
};

#[path = "to_real_solve/sat_instance.rs"]
mod sat_instance;

impl Executor {
    /// Solve FP formulas containing `fp.to_real` via refinement loop (#6241).
    ///
    /// Partitions assertions, encodes FP side as CNF, then iterates:
    /// SAT solve → model extract → rewrite fp.to_real → mixed solve → block.
    pub(super) fn solve_fp_to_real(&mut self) -> Result<SolveResult> {
        let (fp_assertions, mixed_assertions) =
            partition_fp_assertions(&self.ctx.terms, &self.ctx.assertions);
        let sites = collect_fp_to_real_sites(&self.ctx.terms, &mixed_assertions);
        if sites.is_empty() {
            return self.encode_and_solve_fp_simple(&fp_assertions, &mixed_assertions);
        }
        let FpEncoding {
            base_clauses,
            tseitin_result,
            term_to_fp,
            var_offset,
            total_vars,
            congruence_incomplete,
        } = self.encode_fp_assertions(&fp_assertions, &sites)?;

        // Uninterpreted structure the encoder could not represent (see the
        // `congruence` module) makes a model of this encoding no witness for
        // the input, so every `sat` below degrades to `unknown`. The `unsat`
        // exits stay as they are: the encoding only relaxes the input, so a
        // refutation of it refutes the input too.
        let decline_sat = |executor: &mut Self| {
            tracing::warn!(
                "FP to_real path could not encode all uninterpreted structure — degrading sat to unknown"
            );
            executor.last_model = None;
            executor.last_model_validated = false;
            executor.last_unknown_reason = Some(UnknownReason::Incomplete);
            executor.record_unknown_diagnostic(
                UnknownReason::Incomplete,
                "FP `fp.to_real` two-phase lane found a `sat` for a RELAXATION of the input \
                 (uninterpreted structure it could not encode), so only `unsat` transfers",
            );
            Ok(SolveResult::Unknown)
        };
        // Bound the entire fresh-solver chain by the shared `:rlimit` allowance.
        let mut spent = 0;
        // Real-guided pre-solve (#6241): solve the Real side first to find what
        // value fp.to_real must produce, then try an exactly representable target.
        let presolve_target = self.compute_real_guided_fp_target(
            &fp_assertions,
            &mixed_assertions,
            &sites,
            &term_to_fp,
            var_offset,
        );
        if let Some(ref target_clauses) = presolve_target {
            let fp_result =
                self.solve_fp_sat(&base_clauses, target_clauses, total_vars, &mut spent);
            if let SatResult::Sat(ref sat_model) = fp_result {
                let fp_model = Self::extract_fp_model_from_bits(
                    sat_model,
                    &term_to_fp,
                    var_offset,
                    &self.ctx.terms,
                );
                if matches!(
                    self.try_mixed_subproblem(
                        &fp_model,
                        &mixed_assertions,
                        sat_model,
                        &tseitin_result,
                    ),
                    Ok(FpRefinementStep::Sat)
                ) {
                    if congruence_incomplete {
                        return decline_sat(self);
                    }
                    return Ok(SolveResult::Sat);
                }
            }
        }
        // Hybrid refinement (#6241): exact-value blocking first, binade after threshold
        const MAX_REFINEMENTS: usize = 64;
        const EXACT_PER_BINADE: usize = 4;
        let mut blocking_clauses: Vec<CnfClause> = Vec::new();
        let mut binade_attempts: HashMap<Vec<bool>, usize> = HashMap::default();
        let mut used_binade_blocking = false;

        for _round in 0..MAX_REFINEMENTS {
            let fp_result =
                self.solve_fp_sat(&base_clauses, &blocking_clauses, total_vars, &mut spent);
            match fp_result {
                SatResult::Unsat(_) | SatResult::Unknown => {
                    // Binade blocking may exclude valid values: downgrade to Unknown (#6241)
                    let safe = if used_binade_blocking && matches!(fp_result, SatResult::Unsat(_)) {
                        SatResult::Unknown
                    } else {
                        fp_result
                    };
                    return self.store_unknown_or_unsat(safe, &tseitin_result);
                }
                SatResult::Sat(ref sat_model) => {
                    let fp_model = Self::extract_fp_model_from_bits(
                        sat_model,
                        &term_to_fp,
                        var_offset,
                        &self.ctx.terms,
                    );
                    match self.try_mixed_subproblem(
                        &fp_model,
                        &mixed_assertions,
                        sat_model,
                        &tseitin_result,
                    )? {
                        FpRefinementStep::Sat => {
                            if congruence_incomplete {
                                return decline_sat(self);
                            }
                            return Ok(SolveResult::Sat);
                        }
                        FpRefinementStep::Unknown => {
                            return self
                                .store_unknown_or_unsat(SatResult::Unknown, &tseitin_result);
                        }
                        FpRefinementStep::Block => {
                            let (blocking, is_binade) = choose_blocking_clause(
                                sat_model,
                                &sites,
                                &term_to_fp,
                                var_offset,
                                &mut binade_attempts,
                                EXACT_PER_BINADE,
                            );
                            used_binade_blocking |= is_binade;
                            if blocking.literals().is_empty() {
                                return self
                                    .store_unknown_or_unsat(SatResult::Unknown, &tseitin_result);
                            }
                            blocking_clauses.push(blocking);
                        }
                    }
                }
                _ => return self.store_unknown_or_unsat(SatResult::Unknown, &tseitin_result),
            }
        }
        self.store_unknown_or_unsat(SatResult::Unknown, &tseitin_result)
    }

    /// Store an Unknown or Unsat result via solve_and_store_model_full.
    fn store_unknown_or_unsat(
        &mut self,
        result: SatResult,
        tseitin_result: &ay_core::TseitinResult,
    ) -> Result<SolveResult> {
        self.solve_and_store_model_full(
            result,
            tseitin_result,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
        )
    }

    /// Try the mixed subproblem for the current FP model. Returns the
    /// refinement action: Sat (done), Unknown (give up), or Block (retry).
    fn try_mixed_subproblem(
        &mut self,
        fp_model: &FpModel,
        mixed_assertions: &[TermId],
        sat_model: &[bool],
        tseitin_result: &ay_core::TseitinResult,
    ) -> Result<FpRefinementStep> {
        // Rewrite non-FP assertions: replace fp.to_real with concrete
        // values. Exclude FP-only assertions (already satisfied by SAT).
        let non_fp_assertions: Vec<TermId> = self
            .ctx
            .assertions
            .iter()
            .filter(|&&a| !is_pure_fp_assertion(&self.ctx.terms, a))
            .copied()
            .collect();
        let mut rewrite_cache = HashMap::default();
        let mut undef_vars = HashMap::default();
        let rewritten: Vec<TermId> = non_fp_assertions
            .iter()
            .map(|&a| {
                rewrite_fp_to_real_for_model(
                    &mut self.ctx.terms,
                    a,
                    fp_model,
                    &mut rewrite_cache,
                    &mut undef_vars,
                )
            })
            .collect();

        let mixed = self.solve_rewritten_mixed_subproblem(&rewritten)?;

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
                Ok(FpRefinementStep::Sat)
            }
            SolveResult::Unknown => Ok(FpRefinementStep::Unknown),
            SolveResult::Unsat(_) => Ok(FpRefinementStep::Block),
        }
    }

    /// Compute Real-guided FP target values by solving the Real side first.
    ///
    /// Replaces `fp.to_real(arg)` with free Real variables, solves the resulting
    /// pure-Real formula, then converts each target value to FP bit-level unit
    /// clauses. Returns `None` if the Real side is UNSAT/Unknown or if no targets
    /// could be converted to FP representations.
    fn compute_real_guided_fp_target(
        &mut self,
        fp_assertions: &[TermId],
        mixed_assertions: &[TermId],
        sites: &[FpToRealSite],
        term_to_fp: &HashMap<TermId, ay_fp::FpDecomposed>,
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        if sites.is_empty() {
            return None;
        }

        // Structural extraction: find target values directly from formula.
        // For each fp.to_real site, scan assertions for patterns like:
        //   (= (fp.to_real arg) constant) or (= constant (fp.to_real arg))
        let mut targets: HashMap<TermId, f64> = HashMap::default();
        for &assertion in mixed_assertions {
            extract_fp_to_real_targets(&self.ctx.terms, assertion, &mut targets);
        }

        // If structural extraction found no targets, try the solver approach
        if targets.is_empty() {
            return self.compute_real_guided_fp_target_via_solver(
                fp_assertions,
                mixed_assertions,
                sites,
                term_to_fp,
                var_offset,
            );
        }

        let mut unit_clauses = Vec::new();

        for site in sites {
            let target_f64 = match targets.get(&site.arg) {
                Some(&v) => v,
                None => continue,
            };
            let decomposed = match term_to_fp.get(&site.arg) {
                Some(d) => d,
                None => continue,
            };
            let eb = decomposed.precision.exponent_bits();
            let sb = decomposed.precision.significand_bits();

            if let Some(clauses) =
                build_fp_target_unit_clauses(decomposed, var_offset, target_f64, eb, sb)
            {
                unit_clauses.extend(clauses);
            }
        }

        if unit_clauses.is_empty() {
            None
        } else {
            Some(unit_clauses)
        }
    }

    /// Solver-based fallback for computing Real-guided FP targets.
    ///
    /// Used when structural extraction finds no targets. Replaces fp.to_real
    /// with free Real variables, solves the resulting formula, and extracts
    /// target values from the LRA model.
    fn compute_real_guided_fp_target_via_solver(
        &mut self,
        fp_assertions: &[TermId],
        mixed_assertions: &[TermId],
        sites: &[FpToRealSite],
        term_to_fp: &HashMap<TermId, ay_fp::FpDecomposed>,
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let mut fp_arg_to_real_var: HashMap<TermId, TermId> = HashMap::default();
        for (i, site) in sites.iter().enumerate() {
            fp_arg_to_real_var.entry(site.arg).or_insert_with(|| {
                let name = format!("__fp_target_{i}");
                self.ctx.terms.mk_var(&name, Sort::Real)
            });
        }

        // Include Real-only context from fp_assertions (e.g., `(= r 2.0)`)
        // that constrain Real variables appearing in mixed assertions.
        let mut all_presolve: Vec<TermId> = Vec::new();
        for &a in fp_assertions {
            if !is_pure_fp_assertion(&self.ctx.terms, a) {
                all_presolve.push(a);
            }
        }
        for &a in mixed_assertions {
            all_presolve.push(rewrite_fp_to_real_with_vars(
                &mut self.ctx.terms,
                a,
                &fp_arg_to_real_var,
                &mut HashMap::default(),
            ));
        }

        let mixed_result = self.solve_rewritten_mixed_subproblem(&all_presolve).ok()?;
        if !matches!(mixed_result.result, SolveResult::Sat) {
            return None;
        }

        let lra_model = match mixed_result.lra_model {
            Some(m) if !m.values.is_empty() => m,
            _ => return None,
        };

        let mut unit_clauses = Vec::new();
        for site in sites {
            let real_var = match fp_arg_to_real_var.get(&site.arg) {
                Some(v) => v,
                None => continue,
            };
            let target_rational = match lra_model.values.get(real_var) {
                Some(r) => r,
                None => continue,
            };
            let target_f64 = rational_to_f64(target_rational);

            let decomposed = match term_to_fp.get(&site.arg) {
                Some(d) => d,
                None => continue,
            };
            let eb = decomposed.precision.exponent_bits();
            let sb = decomposed.precision.significand_bits();

            if let Some(clauses) =
                build_fp_target_unit_clauses(decomposed, var_offset, target_f64, eb, sb)
            {
                unit_clauses.extend(clauses);
            }
        }

        if unit_clauses.is_empty() {
            None
        } else {
            Some(unit_clauses)
        }
    }

    /// Build the final merged model from FP SAT + LRA mixed results.
    ///
    /// Constructs the Model directly instead of going through the generic
    /// solve_and_store_model_full path. The merged model preserves both the FP
    /// model and the rewritten mixed solve's EUF/LRA pieces so
    /// `finalize_sat_model_validation` can validate the original assertions.
    fn build_merged_fp_real_model(
        &mut self,
        fp_model: &FpModel,
        mixed: MixedSubproblemResult,
        mixed_assertions: &[TermId],
        sat_model: &[bool],
        tseitin_result: &ay_core::TseitinResult,
        undef_vars: &HashMap<String, TermId>,
    ) {
        use super::super::super::model::Model;

        let mut lra_model = mixed.lra_model.unwrap_or_else(|| LraModel {
            values: HashMap::default(),
        });
        let fp_to_real_vals =
            build_lra_model_from_fp_to_real(&self.ctx.terms, fp_model, mixed_assertions);
        for (k, v) in fp_to_real_vals.values {
            lra_model.values.entry(k).or_insert(v);
        }
        // `fp.to_real` at NaN or an infinity is unspecified-but-total: the
        // mixed solve chose its value against a substituted variable, and the
        // ORIGINAL application term has to carry that same value for anything
        // re-checking the original assertions to evaluate it.
        let roots: Vec<TermId> = self.ctx.assertions.clone();
        pin_undefined_fp_to_real(
            &self.ctx.terms,
            fp_model,
            undef_vars,
            &roots,
            &mut lra_model.values,
        );

        let term_to_var: HashMap<TermId, u32> = tseitin_result
            .term_to_var
            .iter()
            .map(|(&t, &v)| (t, v - 1))
            .collect();
        let mut model = Model::empty();
        model.sat_model = sat_model.to_vec();
        model.term_to_var = term_to_var;
        model.euf_model = mixed.euf_model;
        model.lra_model = if lra_model.values.is_empty() {
            None
        } else {
            Some(lra_model)
        };
        model.fp_model = Some(fp_model.clone());
        self.last_model = Some(model);
        // #8456: Model validation now runs for FP theories.
        self.last_model_validated = false;
        self.last_result = Some(SolveResult::Sat);
    }

    /// Solve rewritten mixed assertions (no fp.to_real) through normal SMT dispatch.
    ///
    /// Temporarily swaps in the rewritten assertions, infers the logic from
    /// them, runs `check_sat_internal` with isolated incremental solver state,
    /// then restores the original state. The isolation is load-bearing for
    /// push/pop: these rewritten assertions are an internal FP-refinement
    /// query, not assertions in the outer SMT scope, so they must never enter
    /// its persistent SAT/Tseitin state.
    ///
    /// Returns the solve result plus theory models extracted from the mixed
    /// solve (LRA and EUF), which are needed to populate the final merged model.
    fn solve_rewritten_mixed_subproblem(
        &mut self,
        rewritten_assertions: &[TermId],
    ) -> Result<MixedSubproblemResult> {
        // Save state
        let saved_assertions =
            std::mem::replace(&mut self.ctx.assertions, rewritten_assertions.to_vec());
        let saved_model = self.last_model.take();
        let saved_result = self.last_result.take();
        let saved_unknown = self.last_unknown_reason.take();

        // Infer logic for the rewritten (FP-free) assertions.
        //
        // BORROWED, not re-set. A plain `set_logic` out and back advances the
        // context's `source_revision` TWICE, and that counter is half of the
        // `SourceContextStamp` the mandatory UNSAT gate compares against the
        // stamp captured when the public query was bound. This lane restores
        // the logic exactly, so nothing observable changes — but the stamp
        // never came back, and `authenticate_unsat_query_scope` discarded a
        // correct refutation with "the public UNSAT source context is no longer
        // current". Measured on
        // `group_fp::fp_congruence::uf_over_float32_is_congruent_under_fp_to_real`,
        // where these two writes were the ONLY revision movement in the whole
        // solve. The borrow rolls the revision back only when nothing else
        // moved it, so a genuine source change inside the sub-solve still reads
        // as stale.
        let features = StaticFeatures::collect(&self.ctx.terms, &self.ctx.assertions);
        let inferred_logic = features.infer_logic().to_string();
        let logic_borrow = self.ctx.begin_internal_logic_borrow(inferred_logic);

        // Solve the rewritten subproblem without registering its temporary
        // roots in the outer session's persistent incremental state.
        let result = self.with_isolated_incremental_state(None, |this| this.check_sat_internal());

        // Extract theory models from the mixed solve before restoring state.
        // These are needed so the refinement loop can merge them into the
        // final model (the mixed solve determines Real variable values).
        let (mixed_lra_model, mixed_euf_model) = if matches!(&result, Ok(SolveResult::Sat)) {
            let lra = self.last_model.as_mut().and_then(|m| m.lra_model.take());
            let euf = self.last_model.as_mut().and_then(|m| m.euf_model.take());
            (lra, euf)
        } else {
            (None, None)
        };

        // Restore state
        self.ctx.assertions = saved_assertions;
        self.ctx.end_internal_logic_borrow(logic_borrow);
        self.last_model = saved_model;
        self.last_result = saved_result;
        self.last_unknown_reason = saved_unknown;

        result.map(|solve_result| MixedSubproblemResult {
            result: solve_result,
            lra_model: mixed_lra_model,
            euf_model: mixed_euf_model,
        })
    }
}
