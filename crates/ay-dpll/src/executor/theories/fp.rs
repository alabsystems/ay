// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! FP (IEEE 754 floating-point) solve pipeline via eager bit-blasting.
//!
//! Routes QF_FP formulas through Tseitin encoding + FP bit-blasting + SAT.
//! The FP solver generates CNF clauses at decomposition time; `check()` is
//! trivially SAT. The real work is linking FP predicate results back to
//! Tseitin variables so the SAT solver sees the FP semantics.

mod abvfp_window;
mod bitblast;
mod blocking;
mod congruence;
mod flatten_reads;
mod forward_error;
mod incremental;
mod namespace;
mod nested_bv_guards;
mod pin_reals;
mod stateless;
mod stop;
pub(in crate::executor) use namespace::FpNamespace;
pub(in crate::executor) use stop::{FpStop, MemoryPollGate};
mod support;
#[cfg(test)]
mod tests;
mod to_real;
mod to_real_rewrite;
mod to_real_solve;
mod unread_arrays;

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};

use super::super::Executor;
use crate::executor_types::{Result, SolveResult, UnknownOrigin, UnknownReason};

use support::{check_fp_support, FpSupportStatus};

impl Executor {
    /// Solve QF_FP (quantifier-free IEEE 754 floating-point) using eager bit-blasting.
    ///
    /// Pipeline:
    /// 1. Tseitin encode assertions into CNF
    /// 2. Walk Tseitin terms for FP predicates, bitblast each via `FpSolver`
    /// 3. Link FP predicate results to Tseitin variables
    /// 4. Feed combined CNF to SAT solver
    pub(in crate::executor) fn solve_fp(&mut self) -> Result<SolveResult> {
        // CONSUME the persistent-lane authorization here, at the single shared
        // entry point, before anything can re-enter. `try_fp_pin_unsat_probe`
        // calls back into `solve_fp` further down this very function with a
        // substituted `ctx.assertions`; taking the flag now guarantees that
        // probe never shares session state with the authored query. See
        // `Executor::fp_persistent_armed`.
        let persistent_authorized = std::mem::take(&mut self.fp_persistent_armed);
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        // The FP word-level rewriter (fpa_rewriter), the first pass of the
        // pipeline: every FP operation over constants folds to the constant it
        // denotes, exactly, and so does one over a symbolic rounding mode when
        // all five modes agree. The standard FP-literal syntax
        // `((_ to_fp eb sb) RNE 0.5)` is the commonest case. Every rule is an
        // equivalence (ay-theories/fp/src/rewriter.rs).
        // A literal definition can already supply a concrete witness. This
        // advisory check runs no solver and cannot refute anything or mint
        // SAT authority. The ordinary funnel still checks ALL original roots.
        let literal_candidate = {
            // Retain the exact input IDs at this rewrite boundary; roots from
            // an earlier preprocessing window must not be inferred by position.
            // Stage in the same one cloned root buffer as the old rewriter.
            // Keep the live assertion stack intact if rewriting unwinds; an
            // FFI caller may catch that failure and continue using its context.
            let mut rewritten_fp_assertions = self.ctx.assertions.clone();
            let mut rewriter = ay_fp::rewriter::FpRewriter::new();
            for root in &mut rewritten_fp_assertions {
                *root = rewriter.rewrite(&mut self.ctx.terms, *root);
            }
            let original_fp_assertions =
                std::mem::replace(&mut self.ctx.assertions, rewritten_fp_assertions);
            self.last_statistics
                .set_int("fp.rewriter.folds", rewriter.folds());
            self.try_literal_fp_model(&original_fp_assertions)
        };
        match literal_candidate {
            Ok(Some(model)) => {
                self.last_statistics.set_int(
                    "fp.literal_model.bindings",
                    model.completed_values.len() as u64,
                );
                self.last_model = Some(model);
                self.last_model_validated = false;
                self.last_unknown_reason = None;
                return Ok(SolveResult::Sat);
            }
            Ok(None) => {}
            Err(origin) => return Ok(self.fp_stopped(origin)),
        }

        if self.try_install_pinned_fp_refutation() {
            self.last_model = None;
            self.last_unknown_reason = None;
            self.last_statistics
                .set_int("fp.pinned.checked_presolve", 1);
            return Ok(SolveResult::unsat());
        }

        // Symbolic rounding modes need no case split: the bit-blaster carries
        // each declared mode as three bits (ay-theories/fp/src/rm.rs), and
        // `check_fp_support` fails closed on a mode it cannot encode.

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

        // --- Persistent incremental lane (fifth incremental subsystem) ---
        // Engages only for an authorized, push/pop-scoped solve whose session
        // state has not opted out. Single-shot solves and declined incremental
        // attempts continue through the cooperatively owned stateless pipeline.
        //
        // The lane is SOUND — 1,820 check-sat indices compared against bitwuzla
        // 0.9.1 AND cvc5 1.3.0 with zero conflicts, plus 3,260 more by the
        // implementer, and ten mutations each from a pristine snapshot. Nothing
        // below questions that.
        //
        // It was parked after proving 14x SLOWER on a real division file, which
        // no corpus average revealed. Measured on
        // `incremental/ABVFPLRA/.../image_filter_true-unreach-call.c.smt2`, same
        // binary, back-to-back, `-T:600 -memory:4096`:
        //
        //     lane ON    real 546.71 s   user 295.29 s
        //     lane OFF   real  39.60 s   user  17.05 s
        //
        // The file finishes in 40 s disarmed and blows a 600 s budget armed. The
        // cost is throughput, not correctness: the armed run emits 453 of 463
        // check-sats — it simply STOPS 10 EARLY — plus one boundary flip. That is
        // -11 definite answers on `image_filter` and -3 on `inv_Newton`, i.e. -14
        // on Inc Equality_MachineArith, the one incremental-FP division there is.
        //
        // The branch's own 1.84x general / 3.59x repro-shaped speedups are real
        // and not in dispute. The lane's effect is simply SHAPE-DEPENDENT with a
        // very wide spread in both directions, and a corpus mean hid the tail.
        //
        // One hypothesis is already REFUTED, recorded so it is not re-tried:
        // clause accumulation. `:num-clauses` / `:num-vars` are IDENTICAL armed
        // and disarmed (1,097,324 / 364,799), so the lane is not growing the
        // database.
        //
        // The admission gate now excludes that exact shape without a tuned
        // threshold: no persistent encoding or SAT solver exists until every
        // current FP-relevant authored TermId was previously observed or
        // encoded (pop/reassert counts). A stable tiny anchor cannot admit a
        // disjoint large batch. Any novel root restarts statelessly; an exact
        // repeat may rebuild persistence on the following query.

        if persistent_authorized
            && self.incremental_mode
            && !ay_core::misc_cli_flags().no_fp_incremental
            && !self
                .incr_fp_state
                .as_ref()
                .is_some_and(|state| state.disabled)
        {
            if let Some(result) = self.try_solve_fp_incremental()? {
                return Ok(result);
            }
        }

        self.solve_fp_stateless()
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
        self.try_fp_pin_unsat_probe_with(&mut |executor| executor.solve_fp())
    }

    fn try_fp_pin_unsat_probe_with(
        &mut self,
        solve: &mut impl FnMut(&mut Self) -> Result<SolveResult>,
    ) -> Result<Option<SolveResult>> {
        let Some(pinned) =
            pin_reals::pin_real_assertions(&mut self.ctx.terms, &self.ctx.assertions)
        else {
            return Ok(None);
        };
        let saved = std::mem::replace(&mut self.ctx.assertions, pinned);
        // Re-enter the FP pipeline on the pinned assertions. This cannot loop:
        // after substitution the pinned `Var` TermIds no longer occur, so a
        // nested `pin_real_assertions` finds an empty pin map and returns `None`.
        let result = solve(self);
        self.ctx.assertions = saved;
        match result {
            Ok(SolveResult::Unsat(core)) => {
                self.last_unknown_reason = None;
                Ok(Some(SolveResult::Unsat(core)))
            }
            Ok(SolveResult::Unknown) if self.fp_recorded_resource_stop() => {
                Ok(Some(SolveResult::Unknown))
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
        // Belt for R3: every route out of this function substitutes
        // `ctx.assertions` before reaching `solve_fp` — unread-array
        // elimination, read-over-write store expansion, constant-index read
        // flattening, finite-array closure. The substituted TermIds are not
        // the authored ones and the flattened set is not model-equivalent to
        // the original, so nothing here may share the session's persistent FP
        // encoding.
        self.fp_persistent_armed = false;
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }

        let false_term = self.ctx.terms.false_term();
        if self.ctx.assertions.contains(&false_term) {
            return Ok(SolveResult::unsat());
        }

        // An array that occurs once, as one side of a positive equality (an
        // unread datatype field, after the frontend splits the datatype into
        // field constants), is dropped before both array transforms below:
        // either would otherwise refuse the window for that single occurrence.
        self.solve_abvfp_eliminating_unread_arrays()
    }

    /// The array transforms and the BVFP solve of one ABVFP window.
    fn solve_abvfp_window(&mut self) -> Result<SolveResult> {
        let false_term = self.ctx.terms.false_term();
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
        let mut flatten_note = match self.try_flatten_constant_index_reads()? {
            FlattenOutcome::Decided(result) => return Ok(result),
            FlattenOutcome::Abstained(reason) => Some(reason),
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
        let expansion_rewrote = expanded_assertions != self.ctx.assertions;
        let original_assertions = std::mem::replace(&mut self.ctx.assertions, expanded_assertions);
        let result = self.solve_abvfp_expanded_window(expansion_rewrote, &mut flatten_note);
        self.ctx.assertions = original_assertions;

        // Abstention telemetry: attribute the `unknown` to the specific side
        // condition that stopped the read elimination, instead of letting the
        // whole population land in the "no specific reason recorded" bucket.
        // Only ever refines an `unknown`'s DETAIL — never a verdict, and never a
        // reason more specific than `Incomplete`; a bit-blaster `unsupported`
        // keeps its reason and gains a detail naming the array gap.
        if let (Some(note), Ok(SolveResult::Unknown)) = (flatten_note, &result) {
            if matches!(
                self.last_unknown_reason,
                None | Some(UnknownReason::Incomplete) | Some(UnknownReason::Unknown)
            ) {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                self.record_unknown_diagnostic(UnknownReason::Incomplete, note.detail());
            } else {
                self.name_abvfp_array_gap(note);
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
        self.try_flatten_constant_index_reads_with(&mut |executor| {
            executor.solve_abvfp_final_array_window()
        })
    }

    fn try_flatten_constant_index_reads_with(
        &mut self,
        solve: &mut impl FnMut(&mut Self) -> Result<SolveResult>,
    ) -> Result<FlattenOutcome> {
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
        let bool_uf_transport = plan.capture_bool_uf_transport(self);
        // Capture can observe a stop whose live flag or memory pressure then
        // clears. Its recorded refusal still owns this transform attempt.
        if self.fp_recorded_resource_stop() || self.should_abort_theory_loop() {
            return Ok(FlattenOutcome::Decided(SolveResult::Unknown));
        }
        self.last_statistics
            .set_string("abvfp_flatten.status", "fired");
        self.last_statistics
            .set_int("abvfp_flatten.cells", plan.cells.len() as u64);

        let saved = std::mem::replace(&mut self.ctx.assertions, plan.assertions);
        // The plan is now the final, array-eliminated assertion window. Run the
        // common exact-closure boundary here so a Decided result cannot bypass
        // it, then restore the authored vector exactly on every outcome.
        let result = solve(self);
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
                // Restoring the roots also restores UF application IDs. Carry
                // only their exact rewritten SAT assignments back; this adds
                // no default interpretation and bypasses no model gate.
                if self.attach_flattened_array_model(&plan.cells)
                    && bool_uf_transport
                        .as_ref()
                        .is_some_and(|transport| transport.install(self))
                {
                    self.last_unknown_reason = None;
                    Ok(FlattenOutcome::Decided(SolveResult::Sat))
                } else {
                    self.last_model = None;
                    self.last_model_validated = false;
                    self.last_statistics.set_string(
                        "abvfp_flatten.status",
                        "fired: array or Boolean-UF model incomplete",
                    );
                    // Dropping the candidate can itself relieve memory
                    // pressure; that cannot revoke an already observed stop.
                    if self.fp_recorded_resource_stop() || self.should_abort_theory_loop() {
                        Ok(FlattenOutcome::Decided(SolveResult::Unknown))
                    } else {
                        Ok(FlattenOutcome::Undecided)
                    }
                }
            }
            // A captured stop survives teardown/reset and is not permission to
            // run another transform. Original assertions are already restored.
            Ok(SolveResult::Unknown) if self.fp_recorded_resource_stop() => {
                Ok(FlattenOutcome::Decided(SolveResult::Unknown))
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
    ///
    /// A SYMBOLIC-index cell has no address until a model exists: its address is
    /// whatever the model assigns to the index term. That value is read out of
    /// the same `bv_model` the cell values come from, so the published array
    /// pins exactly the addresses the flattened solve committed to. If the index
    /// term has no value there, fail closed rather than guess an address — a
    /// witness that pins the wrong cell is worse than no witness.
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
            let index_value = match cell.index_value.as_ref() {
                Some(v) => v.clone(),
                None => match bv.values.get(&cell.index_term) {
                    Some(v) => v.clone(),
                    None => return false,
                },
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
                crate::executor_format::format_bitvec(&index_value, idx_bv.width),
                crate::executor_format::format_bitvec(value, elem_bv.width),
            ));
        }
        let Some(model) = self.last_model.as_mut() else {
            return false;
        };
        model.array_model = Some(ay_arrays::ArrayModel {
            array_values: interps,
            read_conflicted: HashSet::default(),
            pending_definitions: HashMap::default(),
            pending_definition_dependents: HashSet::default(),
            store_chain_class_candidate: None,
            definition_authoritative: HashSet::default(),
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
