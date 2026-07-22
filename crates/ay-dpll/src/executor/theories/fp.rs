// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! FP (IEEE 754 floating-point) solve pipeline via eager bit-blasting.
//!
//! Routes QF_FP formulas through Tseitin encoding + FP bit-blasting + SAT.
//! The FP solver generates CNF clauses at decomposition time; `check()` is
//! trivially SAT. The real work is linking FP predicate results back to
//! Tseitin variables so the SAT solver sees the FP semantics.

mod bitblast;
mod blocking;
mod forward_error;
mod pin_reals;
mod rm_expand;
mod support;
#[cfg(test)]
mod tests;
mod to_fp_const;
mod to_real;
mod to_real_rewrite;
mod to_real_solve;

use ay_core::{CnfClause, Tseitin};
use ay_fp::FpSolver;
use ay_sat::{SatResult, Solver as SatSolver};

use super::super::Executor;
use crate::executor_types::{Result, SolveResult, UnknownReason};

use support::{check_fp_support, FpPredicateResult, FpSupportStatus};
use to_real::offset_cnf_lit;

impl Executor {
    /// Solve QF_FP (quantifier-free IEEE 754 floating-point) using eager bit-blasting.
    ///
    /// Pipeline:
    /// 1. Tseitin encode assertions into CNF
    /// 2. Walk Tseitin terms for FP predicates, bitblast each via `FpSolver`
    /// 3. Link FP predicate results to Tseitin variables
    /// 4. Feed combined CNF to SAT solver
    pub(in crate::executor) fn solve_fp(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        // Fold `((_ to_fp eb sb) <const-rm> <const-real>)` to its IEEE bit
        // pattern (the supported 1-arg `to_fp(<BV>)` form) so the standard
        // FP-literal syntax is solved instead of bailing to `unknown`.
        self.ctx.assertions =
            to_fp_const::fold_to_fp_real_constants(&mut self.ctx.terms, &self.ctx.assertions);

        // Symbolic-RoundingMode finite-domain enumeration (#P0.2, Pass C):
        // declared RM consts case-split over the 5 modes and DECIDE like z3
        // (see rm_expand.rs). Not-applicable shapes fall through to
        // `check_fp_support`, whose strengthened guard fails ANY remaining
        // non-literal RM-sorted term closed to `unknown`.
        if let Some(result) = self.try_solve_fp_symbolic_rm()? {
            return Ok(result);
        }

        // --- Guard: check for unsupported FP operations ---
        // Supported with full bit-blasting (#3586):
        //   fp.add, fp.sub, fp.mul, fp.div, fp.sqrt, fp.fma, fp.roundToIntegral,
        //   fp.rem (Float16/Float32 only), to_fp (constant or variable BV/FP args),
        //   to_fp_unsigned (constant or variable BV args), fp.to_ubv, fp.to_sbv
        // fp.to_real: handled via two-phase solve (FP bit-blast + model eval)
        // Other unsupported ops: returns Unknown
        match check_fp_support(&self.ctx.terms, &self.ctx.assertions) {
            FpSupportStatus::Unsupported => {
                // Tier A (to_fp-from-symbolic-Real, UNSAT-only): if a top-level
                // equality pins a symbolic Real that feeds an unsupported
                // `to_fp`, substitute it — under the asserted equality this is
                // an equivalence, so an UNSAT verdict on the pinned formula
                // transfers to the original. SAT/unknown on the pinned formula
                // are NOT trusted (the substituted-away var has no witness in
                // the FP model → possible falsifying model), so we fall back to
                // `unknown` exactly as before. See `pin_reals` module docs.
                if let Some(result) = self.try_fp_pin_unsat_probe()? {
                    return Ok(result);
                }
                self.last_unknown_reason = Some(UnknownReason::Unsupported);
                return Ok(SolveResult::Unknown);
            }
            FpSupportStatus::OnlyToReal => {
                // FP forward-error tactic: refute `|to_real(dag) - mirror| >= c`
                // rounding-error claims by sound interval propagation before
                // the (incomplete) bit-precise refinement loop runs. Only ever
                // strengthens unknown to unsat; abstains when any side
                // condition (RNE, input normality+bounds, no overflow, exact
                // mirror) is unestablished. See `forward_error` module docs.
                if let Some(refutation) = forward_error::try_refute_forward_error_goal(
                    &self.ctx.terms,
                    &self.ctx.assertions,
                ) {
                    tracing::info!(
                        goal = %refutation.goal,
                        certified_bound = %refutation.bound,
                        "FP forward-error tactic refuted rounding-error claim"
                    );
                    self.last_unknown_reason = None;
                    return Ok(SolveResult::unsat());
                }
                return self.solve_fp_to_real();
            }
            FpSupportStatus::FullySupported => {}
        }

        // --- Phase 1: Tseitin transformation ---
        let mut tseitin = Tseitin::new(&self.ctx.terms);
        for &assertion in &self.ctx.assertions {
            tseitin.assert_term(assertion);
        }
        let tseitin_result = ay_core::TseitinResult::new(
            tseitin.all_clauses().to_vec(),
            tseitin.term_to_var().clone(),
            tseitin.var_to_term().clone(),
            0,
            tseitin.num_vars(),
        );

        // --- Phase 2: FP bit-blasting ---
        let mut fp_solver = FpSolver::new_with_tseitin(&self.ctx.terms, tseitin.term_to_var());

        // Walk Tseitin-encoded terms for FP predicates. Each FP predicate
        // (fp.eq, fp.lt, fp.isNaN, etc.) gets a Tseitin variable that must
        // be linked to the FP bit-blast result.
        let mut linking_pairs: Vec<(i32, i32)> = Vec::new();
        for (&tseitin_var, &term) in &tseitin_result.var_to_term {
            match self.bitblast_fp_predicate(&mut fp_solver, term) {
                FpPredicateResult::Bitblasted(fp_lit) => {
                    linking_pairs.push((tseitin_var as i32, fp_lit));
                }
                FpPredicateResult::NotFpPredicate => {}
                FpPredicateResult::Unsupported => {
                    // Unrecognized FP predicate — return Unknown rather than
                    // leaving the Tseitin variable free (false-SAT risk, #6189).
                    self.last_unknown_reason = Some(UnknownReason::Unsupported);
                    return Ok(SolveResult::Unknown);
                }
            }
        }

        // Check for encoding gaps: ITE conditions that couldn't be resolved
        // as FP predicates or linked via Tseitin map. An unconstrained condition
        // variable would make the SAT result unsound (false-SAT risk).
        if fp_solver.has_encoding_gap() {
            tracing::warn!("FP encoding has unresolvable ITE condition — returning Unknown");
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(SolveResult::Unknown);
        }

        let fp_clauses = fp_solver.take_clauses();
        let condition_links = fp_solver.take_pending_condition_links();
        let fp_num_vars = fp_solver.num_vars();
        let var_offset = tseitin_result.num_vars as i32;

        // --- Phase 3: Combine Tseitin + FP clauses ---
        let mut all_clauses = tseitin_result.clauses.clone();

        // Add FP clauses with variable offset
        for clause in fp_clauses {
            let offset_lits: Vec<i32> = clause
                .literals()
                .iter()
                .map(|&lit| offset_cnf_lit(lit, var_offset))
                .collect();
            all_clauses.push(CnfClause::new(offset_lits));
        }

        // Add linking clauses (bidirectional equivalence)
        for (tseitin_lit, fp_lit) in linking_pairs {
            let fp_lit_offset = offset_cnf_lit(fp_lit, var_offset);
            all_clauses.push(CnfClause::binary(-tseitin_lit, fp_lit_offset));
            all_clauses.push(CnfClause::binary(tseitin_lit, -fp_lit_offset));
        }

        // Add ITE condition linking clauses (#3586): connect FP proxy variables
        // allocated by encode_bool_condition to their Tseitin counterparts.
        for (fp_var, tseitin_var) in condition_links {
            let fp_lit_offset = offset_cnf_lit(fp_var as i32, var_offset);
            let tseitin_lit = tseitin_var as i32;
            all_clauses.push(CnfClause::binary(-tseitin_lit, fp_lit_offset));
            all_clauses.push(CnfClause::binary(tseitin_lit, -fp_lit_offset));
        }

        let total_vars = tseitin_result.num_vars + fp_num_vars;

        // --- Phase 4: SAT solving ---
        let mut solver = SatSolver::new(total_vars as usize);
        self.apply_random_seed_to_sat(&mut solver);
        self.apply_progress_to_sat(&mut solver);
        solver.set_congruence_enabled(false);
        // Adaptive reorder gate for large FP instances (#8118).
        if total_vars as usize > 50_000 {
            solver.set_reorder_enabled(false);
        }
        if let Some(seed) = self.random_seed {
            solver.set_random_seed(seed);
        }

        for clause in &all_clauses {
            let lits: Vec<ay_sat::Literal> = clause
                .literals()
                .iter()
                .map(|&lit| crate::cnf_lit_to_sat(lit))
                .collect();
            solver.add_clause(lits);
        }

        let should_stop = self.make_should_stop();
        let result = solver.solve_interruptible(should_stop).into_inner();

        collect_sat_stats!(self, &solver);

        // Extract FP and BV models from SAT assignment before storing
        let (fp_model, bv_model) = if let SatResult::Sat(ref sat_model) = result {
            let term_to_fp = fp_solver.term_to_fp().clone();
            let fp = Self::extract_fp_model_from_bits(
                sat_model,
                &term_to_fp,
                var_offset,
                &self.ctx.terms,
            );
            // Extract BV model from FP solver's cached BV term bits (#3586).
            // This enables model validation for QF_BVFP formulas where BV
            // variables participate in to_fp/to_fp_unsigned conversions.
            let bv_term_bits = fp_solver.bv_term_bits();
            let bv = if bv_term_bits.is_empty() {
                None
            } else {
                Some(Self::extract_bv_model_from_fp_bits(
                    sat_model,
                    bv_term_bits,
                    var_offset,
                    &self.ctx.terms,
                ))
            };
            (Some(fp), bv)
        } else {
            (None, None)
        };

        self.solve_and_store_model_full(
            result,
            &tseitin_result,
            None,
            None,
            None,
            None,
            bv_model,
            fp_model,
            None,
            None,
        )
    }

    /// Tier A `to_fp`-from-symbolic-Real probe: re-solve with pinned Real
    /// variables and trust ONLY an UNSAT result (see `pin_reals` module docs).
    ///
    /// Returns `Some(unsat)` when the pinned formula is UNSAT; `None` (fall
    /// through to `unknown`) otherwise. A model produced by the pinned re-solve
    /// is invalidated before returning `None`, because the substituted-away Real
    /// variable would otherwise be reported with a default value that need not
    /// satisfy the original assertions.
    fn try_fp_pin_unsat_probe(&mut self) -> Result<Option<SolveResult>> {
        let Some(pinned) =
            pin_reals::pin_real_assertions(&mut self.ctx.terms, &self.ctx.assertions)
        else {
            return Ok(None);
        };
        let saved = std::mem::replace(&mut self.ctx.assertions, pinned);
        // Re-enter the FP pipeline on the pinned assertions. This cannot loop:
        // after substitution the pinned `Var` TermIds no longer occur, so a
        // nested `pin_real_assertions` finds an empty pin map and returns `None`.
        let result = self.solve_fp();
        self.ctx.assertions = saved;
        match result {
            Ok(SolveResult::Unsat(core)) => {
                self.last_unknown_reason = None;
                Ok(Some(SolveResult::Unsat(core)))
            }
            _ => {
                // Do not trust SAT/unknown from the pinned formula, and never
                // leak its model (the pinned var was substituted away).
                self.last_model = None;
                self.last_model_validated = false;
                Ok(None)
            }
        }
    }

    /// Solve QF_BVFP (bitvectors + floating-point).
    ///
    /// For the initial wiring, routes through the FP solver. Pure BV terms
    /// are handled as uninterpreted by the Tseitin encoding. A full BV+FP
    /// integration (shared variable namespace) is a follow-up.
    pub(in crate::executor) fn solve_bvfp(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        self.solve_fp()
    }

    /// Solve QF_ABVFP (arrays + bitvectors + floating-point).
    ///
    /// The production slice supported here lowers read-over-write array terms
    /// before the BVFP path, so symbolic EXTERNAL_CODEGEN memory reads of FP values expose
    /// the BV index guard and FP value equality to the bit-blast solver.
    pub(in crate::executor) fn solve_abvfp(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }

        let false_term = self.ctx.terms.false_term();
        if self.ctx.assertions.contains(&false_term) {
            return Ok(SolveResult::unsat());
        }

        let num_stores = self.count_array_stores_in_assertions();
        let expanded_assertions = self
            .ctx
            .terms
            .expand_select_store_all_adaptive(&self.ctx.assertions, num_stores);
        if expanded_assertions.contains(&false_term) {
            return Ok(SolveResult::unsat());
        }
        if expanded_assertions == self.ctx.assertions {
            return self.solve_bvfp();
        }

        let original_assertions = std::mem::replace(&mut self.ctx.assertions, expanded_assertions);
        let result = self.solve_bvfp();
        self.ctx.assertions = original_assertions;
        result
    }
}
