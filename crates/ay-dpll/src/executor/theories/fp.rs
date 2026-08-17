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
mod congruence;
mod flatten_reads;
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

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{CnfClause, Tseitin};
use ay_fp::FpSolver;
use ay_sat::{SatResult, Solver as SatSolver};

use super::super::Executor;
use crate::executor_types::{Result, SolveResult, UnknownOrigin, UnknownReason};

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
        let mut congruence_plan_clauses: Vec<Vec<congruence::PlanLit>> = Vec::new();
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

        // --- Phase 2b: congruence for symbols this path does not interpret ---
        // A user-declared `f` or an array read over an FP index is only a
        // Tseitin atom here, so without these Ackermann clauses `(= x y)`
        // would not force `(= (f x) (f y))` and the relaxation reports a
        // wrong `sat` (SMT-LIB 2.6 §5.2: `=` is identity and every function
        // symbol is total). Anything the scan could not encode sets
        // `congruence_incomplete`, which fails a later `sat` closed — `unsat`
        // stays valid because the encoding only ever relaxes the input.
        // Snapshot the gap flag BEFORE the congruence pre-pass so the two causes
        // stay distinguishable — see the split check below.
        let gap_before_congruence = fp_solver.has_encoding_gap();

        let foreign = congruence::scan_foreign(&self.ctx.terms, &self.ctx.assertions);
        let mut congruence_incomplete = if foreign.is_empty() {
            false
        } else {
            let plan = congruence::plan_congruence(
                &self.ctx.terms,
                &mut fp_solver,
                &tseitin_result,
                &foreign,
            );
            congruence_plan_clauses = plan.clauses;
            // `solve_fp` owns the whole formula, so a sort it cannot represent
            // anywhere is as disqualifying as an unencodable congruence pair.
            foreign.unencodable || plan.incomplete
        };

        // Encoding gaps: an ITE condition that could not be resolved as an FP
        // predicate or linked via the Tseitin map. The two possible causes carry
        // DIFFERENT consequences and must not be conflated.
        if gap_before_congruence {
            // The BASE encoding is holed: a condition variable is unconstrained
            // in the formula the solver will actually see, which makes a `sat`
            // unsound. Fail closed, as this path always has.
            tracing::warn!("FP encoding has unresolvable ITE condition — returning Unknown");
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            self.record_unknown_diagnostic(
                UnknownReason::Incomplete,
                "FP base encoding left an `ite` condition unresolved (not an FP predicate and not \
                 linkable through the Tseitin map), so a `sat` over it would be unsound",
            );
            return Ok(SolveResult::Unknown);
        }
        if fp_solver.has_encoding_gap() {
            // The gap was introduced by the congruence pre-pass itself, which
            // touches argument terms the base encoder never bit-blasted. That is
            // only a failure to add congruence clauses, i.e. a RELAXATION: fewer
            // constraints than the input, so an `unsat` on it still entails
            // `unsat` of the input, and a `sat` is already downgraded below by
            // `congruence_incomplete`.
            //
            // Returning Unknown here instead DESTROYED correct refutations that
            // the base encoding found on its own — measured on an FP-sorted
            // `ite` beneath an uninterpreted application, where this path went
            // unsat (correct, and z3 agrees) to unknown purely because adding
            // congruence tripped the check.
            tracing::debug!(
                "FP congruence pre-pass could not encode every pair; keeping the \
                 relaxation and downgrading a later `sat`"
            );
            congruence_incomplete = true;
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

        // Add the congruence clauses planned above, resolving each literal's
        // namespace now that the FP offset is known.
        for clause in congruence_plan_clauses {
            let lits: Vec<i32> = clause
                .into_iter()
                .map(|lit| match lit {
                    congruence::PlanLit::Fp(fp_lit) => offset_cnf_lit(fp_lit, var_offset),
                    congruence::PlanLit::Tseitin(tseitin_lit) => tseitin_lit,
                })
                .collect();
            all_clauses.push(CnfClause::new(lits));
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

        // A model of an encoding that dropped structure is not a model of the
        // input: fail the `sat` closed. `unsat` is untouched — the encoding is
        // a relaxation, so its refutation refutes the input too.
        if congruence_incomplete && matches!(result, SatResult::Sat(_)) {
            tracing::warn!(
                "FP path could not encode all uninterpreted structure — degrading sat to unknown"
            );
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            self.record_unknown_diagnostic(
                UnknownReason::Incomplete,
                "FP lane found a `sat` for a RELAXATION of the input: uninterpreted structure \
                 (a declared function, or an array read the lane could not eliminate) has \
                 congruence clauses missing, so the model is not a model of the input. The \
                 relaxation keeps `unsat` valid; only `sat` degrades",
            );
            return Ok(SolveResult::Unknown);
        }

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

        // Constant-index array-read elimination (`flatten_reads`). Runs FIRST,
        // because the read-over-write expansion below is provably INERT on the
        // population this targets: with zero `store`s
        // `expand_select_store_all_adaptive` is the identity, so the
        // `expanded_assertions == self.ctx.assertions` guard sends the file
        // straight to `solve_bvfp` with the array reads still present — which is
        // exactly why nothing fires today.
        //
        // ADDITIVE BY CONSTRUCTION: on `Unknown` the original assertions are
        // restored and the untouched legacy path below runs, so this can only
        // convert an `unknown` into `sat`/`unsat`, never the reverse.
        let flatten_note = match self.try_flatten_constant_index_reads()? {
            FlattenOutcome::Decided(result) => return Ok(result),
            FlattenOutcome::Abstained(reason) => Some(reason.detail()),
            FlattenOutcome::Undecided => None,
        };

        let num_stores = self.count_array_stores_in_assertions();
        let expanded_assertions = self
            .ctx
            .terms
            .expand_select_store_all_adaptive(&self.ctx.assertions, num_stores);
        if expanded_assertions.contains(&false_term) {
            return Ok(SolveResult::unsat());
        }
        // Install the post-expansion window even when the rewrite was an
        // identity. Exact finite-array closure belongs on this final surface,
        // immediately before the BVFP solve; running it on the authored window
        // would retain store/read aliases that this transform removes. Restore
        // the exact original vector because the inner FP pipeline can rewrite
        // assertion contents without changing their length.
        let original_assertions = std::mem::replace(&mut self.ctx.assertions, expanded_assertions);
        let result = self.solve_abvfp_final_array_window();
        self.ctx.assertions = original_assertions;

        // Abstention telemetry: attribute the `unknown` to the specific side
        // condition that stopped the read elimination, instead of letting the
        // whole population land in the "no specific reason recorded" bucket.
        // Only ever refines an `unknown`'s DETAIL — never a verdict, and never a
        // reason more specific than `Incomplete`.
        if let (Some(note), Ok(SolveResult::Unknown)) = (flatten_note, &result) {
            if matches!(
                self.last_unknown_reason,
                None | Some(UnknownReason::Incomplete) | Some(UnknownReason::Unknown)
            ) {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                self.record_unknown_diagnostic(UnknownReason::Incomplete, note);
            }
        }
        result
    }

    /// Solve one final, post-array-transform ABVFP assertion window.
    ///
    /// A bounded finite-array prefix contains only valid tautologies, so an
    /// UNSAT refutation remains authoritative. SAT does not: it is revoked by
    /// the shared lifecycle transition whenever exact closure is incomplete.
    /// An already-Unknown incomplete attempt is terminal for this query too;
    /// retrying another ABVFP transform cannot replenish the cumulative ledger.
    fn solve_abvfp_final_array_window(&mut self) -> Result<SolveResult> {
        let _ = self.add_finite_index_array_closure();
        let result = self.solve_bvfp();
        match result {
            Ok(SolveResult::Sat) => {
                self.fail_close_incomplete_finite_array_sat(Ok(SolveResult::Sat))
            }
            Ok(SolveResult::Unknown) if !self.finite_array_expansion.is_complete() => {
                // Preserve a more specific external stop that fired during
                // closure/solving; otherwise attribute this terminal Unknown
                // to the exhausted deterministic finite-array envelope.
                let origin = match self.unknown_origin() {
                    Some(
                        origin @ (UnknownOrigin::InterruptFlag
                        | UnknownOrigin::SolveDeadline
                        | UnknownOrigin::MemoryBudget),
                    ) => origin,
                    _ => self
                        .external_stop_reason()
                        .map(UnknownReason::origin)
                        .unwrap_or(UnknownOrigin::DeterministicResourceBudget),
                };
                self.publish_unknown_from_origin(origin);
                Ok(SolveResult::Unknown)
            }
            other => other,
        }
    }

    /// Constant-index array-read elimination for the ABVFP lane — see the
    /// `flatten_reads` module docs for the equisatisfiability argument and the
    /// side conditions that make it an equivalence rather than a relaxation.
    ///
    /// Disable with `--dpll-no-abvfp-flatten` (default ON; the pass is additive —
    /// see `FlattenOutcome::Undecided`).
    fn try_flatten_constant_index_reads(&mut self) -> Result<FlattenOutcome> {
        if !flatten_reads_enabled() {
            return Ok(FlattenOutcome::Abstained(
                flatten_reads::FlattenAbstain::NoArrays,
            ));
        }
        let assertions = self.ctx.assertions.clone();
        // Deliberately NO `abstained: <reason>` statistic here. `solve_abvfp` can
        // run more than once per `check-sat` (the symbol-disjoint partition
        // rescue re-solves components), and a per-call status string would report
        // whichever call happened to run LAST while `unknown.detail` reports the
        // one that produced the verdict — two stats disagreeing about the same
        // solve. The abstention cause is carried on the verdict itself, through
        // the `unknown.detail` channel that §3c2 of the 2026-07-26 hand-off
        // established as the reliable one.
        let plan = match flatten_reads::plan(&mut self.ctx.terms, &assertions) {
            Ok(plan) => plan,
            Err(reason) => return Ok(FlattenOutcome::Abstained(reason)),
        };
        self.last_statistics
            .set_string("abvfp_flatten.status", "fired");
        self.last_statistics
            .set_int("abvfp_flatten.cells", plan.cells.len() as u64);

        let saved = std::mem::replace(&mut self.ctx.assertions, plan.assertions);
        // The plan is now the final, array-eliminated assertion window. Run the
        // common exact-closure boundary here so a Decided result cannot bypass
        // it, then restore the authored vector exactly on every outcome.
        let result = self.solve_abvfp_final_array_window();
        self.ctx.assertions = saved;

        match result {
            Ok(SolveResult::Unsat(core)) => {
                self.last_unknown_reason = None;
                Ok(FlattenOutcome::Decided(SolveResult::Unsat(core)))
            }
            Ok(SolveResult::Sat) => {
                // Reconstitute each array from its eliminated cells so the
                // published witness names the ORIGINAL array symbol, and so the
                // downstream validators and the independent model-check gate can
                // evaluate `(select A k)` against the SAME values the flattened
                // solve committed to. Fails closed: if any cell value is missing
                // the model is dropped and the verdict falls through to the
                // legacy path rather than shipping a witness that does not pin
                // the array.
                if self.attach_flattened_array_model(&plan.cells) {
                    self.last_unknown_reason = None;
                    Ok(FlattenOutcome::Decided(SolveResult::Sat))
                } else {
                    self.last_model = None;
                    self.last_model_validated = false;
                    self.last_statistics
                        .set_string("abvfp_flatten.status", "fired: array model incomplete");
                    Ok(FlattenOutcome::Undecided)
                }
            }
            // Finite-array exhaustion is query-cumulative. It is terminal even
            // when the flattened attempt was otherwise Unknown: the untouched
            // fallback cannot replenish exact closure and must not retry.
            Ok(SolveResult::Unknown) if !self.finite_array_expansion.is_complete() => {
                Ok(FlattenOutcome::Decided(SolveResult::Unknown))
            }
            // Unknown from the flattened solve: drop its model (the array reads
            // were substituted away, so it does not pin them) and fall through
            // to the untouched legacy path. This is what makes the pass additive.
            Ok(_) => {
                self.last_model = None;
                self.last_model_validated = false;
                Ok(FlattenOutcome::Undecided)
            }
            Err(e) => Err(e),
        }
    }

    /// Build an [`ay_arrays::ArrayModel`] for the flattened arrays from the
    /// cell constants' bitvector values, and attach it to the stored model.
    ///
    /// Returns `false` (fail closed) when any cell has no value in the model.
    fn attach_flattened_array_model(&mut self, cells: &[flatten_reads::FlatCell]) -> bool {
        use ay_core::Sort;

        let Some(model) = self.last_model.as_ref() else {
            return false;
        };
        let Some(bv) = model.bv_model.as_ref() else {
            return false;
        };
        let mut interps: HashMap<ay_core::TermId, ay_arrays::ArrayInterpretation> =
            HashMap::default();
        for cell in cells {
            let Sort::Array(arr) = self.ctx.terms.sort(cell.array).clone() else {
                return false;
            };
            let (Sort::BitVec(idx_bv), Sort::BitVec(elem_bv)) =
                (&arr.index_sort, &arr.element_sort)
            else {
                return false;
            };
            let Some(value) = bv.values.get(&cell.fresh) else {
                return false;
            };
            let entry =
                interps
                    .entry(cell.array)
                    .or_insert_with(|| ay_arrays::ArrayInterpretation {
                        index_sort: Some(arr.index_sort.clone()),
                        element_sort: Some(arr.element_sort.clone()),
                        // A cell the formula never reads is unconstrained; any
                        // total extension witnesses the original (see the
                        // backward direction in the module docs).
                        default: Some(crate::executor_format::format_bitvec(
                            &num_bigint::BigInt::from(0u32),
                            elem_bv.width,
                        )),
                        ..Default::default()
                    });
            entry.stores.push((
                crate::executor_format::format_bitvec(&cell.index_value, idx_bv.width),
                crate::executor_format::format_bitvec(value, elem_bv.width),
            ));
        }
        let Some(model) = self.last_model.as_mut() else {
            return false;
        };
        model.array_model = Some(ay_arrays::ArrayModel {
            array_values: interps,
            read_conflicted: HashSet::default(),
        });
        true
    }
}

/// Outcome of the constant-index read-elimination pre-pass.
enum FlattenOutcome {
    /// The rewrite fired and produced a verdict to publish.
    Decided(SolveResult),
    /// The side conditions did not hold; nothing was attempted.
    Abstained(flatten_reads::FlattenAbstain),
    /// The rewrite fired but did not decide; the caller must run the legacy
    /// path on the untouched original assertions.
    Undecided,
}

/// Is the constant-index read elimination enabled? Default ON; `=0` disables.
fn flatten_reads_enabled() -> bool {
    // B28: CLI-owned (--dpll-no-abvfp-flatten); env retired.
    !ay_core::theory_disable_flags().no_abvfp_flatten
}
