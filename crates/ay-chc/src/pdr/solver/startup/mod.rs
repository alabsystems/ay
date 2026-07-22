// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Startup invariant discovery pipeline for the PDR solver.
//!
//! Extracted from `solve()` to improve navigability (#2998, #3301).
//! This module contains the proactive invariant discovery passes that run
//! before the main PDR blocking loop. The pipeline discovers bounds,
//! equalities, sums, differences, parity, affine, relational, and other
//! invariant patterns to seed the frame system.

mod fixpoint;
mod nonfixpoint;

use super::{PdrResult, PdrSolver};
use crate::ChcExpr;

const BV_FAST_STARTUP_SMT_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(5);
const FULL_STARTUP_SMT_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(10);
const STARTUP_FRAME_CONTRADICTION_TIMEOUT: std::time::Duration =
    std::time::Duration::from_millis(200);
const SHORT_STARTUP_PROBE_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(2);

/// Wide-var startup cap (inc-12): minimum max-predicate-arity for a problem
/// to count as "wide-var" (lustre-class transition systems carry dozens of
/// Bool/Int state slots; algebraic/accumulator benchmarks sit at 3-8).
const WIDE_VAR_STARTUP_ARITY: usize = 12;
/// Fraction of the remaining engine window granted to TOTAL startup
/// discovery (fixpoint + nonfixpoint) on wide-var problems. Attribution
/// (inc-12): on lustre/HOLA-class instances the discovery passes consumed
/// the whole engine window (fixpoint 18.1s + nonfixpoint 15.3s vs a 5s
/// budget checked only between passes) and the main PDR loop never ran.
const WIDE_VAR_STARTUP_WINDOW_FRACTION: f64 = 0.25;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum StartupTimeoutCap {
    Disabled,
    Active(std::time::Duration),
    Exhausted,
}

impl PdrSolver {
    fn startup_smt_timeout_cap(&self, requested: std::time::Duration) -> StartupTimeoutCap {
        if self.is_cancelled() {
            return StartupTimeoutCap::Exhausted;
        }
        if self.config.cancellation_token.is_none()
            && self.config.solve_timeout.is_none()
            && self.solve_deadline.is_none()
        {
            return StartupTimeoutCap::Disabled;
        }

        let mut capped = requested;
        if let Some(deadline) = self.solve_deadline {
            let remaining = deadline.saturating_duration_since(ay_core::time::Instant::now());
            if remaining.is_zero() {
                return StartupTimeoutCap::Exhausted;
            }
            capped = capped.min(remaining);
        } else if let Some(solve_timeout) = self.config.solve_timeout {
            if solve_timeout.is_zero() {
                return StartupTimeoutCap::Exhausted;
            }
            capped = capped.min(solve_timeout);
        }

        if capped.is_zero() {
            StartupTimeoutCap::Exhausted
        } else {
            StartupTimeoutCap::Active(capped)
        }
    }

    fn startup_query_timeout(&self, requested: std::time::Duration) -> Option<std::time::Duration> {
        match self.startup_smt_timeout_cap(requested) {
            StartupTimeoutCap::Disabled => Some(requested),
            StartupTimeoutCap::Active(timeout) => Some(timeout),
            StartupTimeoutCap::Exhausted => None,
        }
    }

    /// Total-startup budget for wide-var linear problems (inc-12).
    ///
    /// Returns `Some(budget)` when the problem looks like a wide-var
    /// SimpleLoop/MultiPredLinear transition system (lustre/protocol class):
    /// high-arity scalar predicates, linear clauses, no algebraic structure
    /// (mod/div/multiplication) in any constraint. On these shapes the
    /// startup discovery passes are quadratic in the state width and consume
    /// the entire engine window before the blocking loop starts. The budget
    /// is `WIDE_VAR_STARTUP_WINDOW_FRACTION` of the remaining engine window.
    ///
    /// Returns `None` (full discovery, behavior unchanged) for:
    /// - unbounded solves (no solve_timeout/deadline — nothing to starve),
    /// - narrow predicates (algebraic/accumulator classes where discovery wins),
    /// - mod/div/multiplication constraints (parity/scaled-sum passes win),
    /// - BV/array/datatype problems (they have dedicated startup routes).
    fn wide_var_startup_budget(&self) -> Option<std::time::Duration> {
        let remaining = self
            .solve_deadline
            .map(|d| d.saturating_duration_since(ay_core::time::Instant::now()))
            .or(self.config.solve_timeout)?;
        let max_arity = self
            .problem
            .predicates()
            .iter()
            .map(|p| p.arg_sorts.len())
            .max()
            .unwrap_or(0);
        if max_arity < WIDE_VAR_STARTUP_ARITY {
            return None;
        }
        if self.problem.has_bv_sorts()
            || self.uses_arrays
            || self.problem.has_datatype_sorts()
            || self.problem.has_real_sorts()
        {
            return None;
        }
        // Linear shape only (SimpleLoop/MultiPredLinear): hyperedge problems
        // keep full discovery (edge-summary passes matter there).
        let is_linear = self
            .problem
            .clauses()
            .iter()
            .all(|c| c.body.predicates.len() <= 1);
        if !is_linear {
            return None;
        }
        // Keep full discovery for algebraic/modular classes: mod/div anywhere
        // in the constraints is the existing feature gate for the parity /
        // modular-equality passes that win there (dillig02_m-style ITE(mod)
        // chains). Plain multiplication is NOT an exclusion: lustre-class
        // wide transition systems routinely contain scaled-sum properties
        // (mul=true) and are the primary target of this cap; the narrow-arity
        // gate above already keeps the accumulator families (s_multipl,
        // gj2007, arity 3-8) on full discovery.
        let has_modular = self.problem.clauses().iter().any(|clause| {
            clause
                .body
                .constraint
                .as_ref()
                .is_some_and(ChcExpr::contains_mod_or_div)
        });
        if has_modular {
            return None;
        }
        Some(
            remaining
                .mul_f64(WIDE_VAR_STARTUP_WINDOW_FRACTION)
                .max(std::time::Duration::from_millis(250)),
        )
    }

    /// True when the inc-12 total-startup deadline has passed.
    pub(in crate::pdr::solver) fn startup_budget_exhausted(&self) -> bool {
        self.startup_deadline
            .is_some_and(|d| ay_core::time::Instant::now() >= d)
    }

    fn allow_post_cancel_startup_salvage(&self) -> bool {
        self.config
            .solve_timeout
            .is_none_or(|timeout| timeout > SHORT_STARTUP_PROBE_TIMEOUT)
    }

    fn post_cancel_startup_salvage_budget(&self) -> Option<std::time::Duration> {
        if !self.allow_post_cancel_startup_salvage() {
            return None;
        }

        if self.is_cancelled() {
            return None;
        }

        let mut budget = self
            .config
            .solve_timeout
            .map_or(FULL_STARTUP_SMT_TIMEOUT, |timeout| {
                timeout.min(FULL_STARTUP_SMT_TIMEOUT)
            });

        if let Some(deadline) = self.solve_deadline {
            let remaining = deadline.saturating_duration_since(ay_core::time::Instant::now());
            if remaining.is_zero() {
                return None;
            }
            budget = budget.min(remaining);
        }

        if budget.is_zero() {
            None
        } else {
            Some(budget)
        }
    }

    /// Native BV direct-route problems should reach the blocking loop before we
    /// try to certify safety from startup-discovered frame[1] lemmas.
    ///
    /// On #5877-style benchmarks, startup discovery can produce frame-relative
    /// BV/Bool lemmas that block the query syntactically but are not a stable
    /// proof. Defer the direct safety shortcut so the main PDR loop can do the
    /// backward-reachability work first.
    fn skip_startup_direct_safety_proof(&self) -> bool {
        self.problem.predicates().len() == 1
            && self.problem.has_bv_sorts()
            && self.problem.transitions().count() == 1
            && !self.uses_arrays
            && !self.problem.has_real_sorts()
            && !self.config.bv_to_int_relaxed
    }

    /// Large native-BV simple loops should skip the full startup discovery
    /// pipeline and go straight to the lighter BV startup path.
    ///
    /// The original #5877 fast-path rationale was driven by very large BV
    /// transitions (thousands of AST nodes, e.g. `bist_cell`). Applying that
    /// same shortcut to every native-BV simple loop also starves small BV
    /// problems of the normal discovery passes that can seed the blocking loop
    /// with useful Boolean/relational lemmas. Keep the broad "no startup direct
    /// safety proof" policy, but only use the heavyweight startup skip when the
    /// extracted transition system is actually large.
    fn use_bv_native_fast_startup_path(&self) -> bool {
        if !self.skip_startup_direct_safety_proof() {
            return false;
        }

        const LARGE_BV_NATIVE_TRANSITION_NODES: usize = 256;

        crate::transition_system::TransitionSystem::from_chc_problem(&self.problem)
            .map(|ts| ts.transition.node_count(10_000) > LARGE_BV_NATIVE_TRANSITION_NODES)
            .unwrap_or(true)
    }

    /// Whether this solve call is a quick soundness check with minimal resource budgets.
    ///
    /// Quick checks skip startup invariant discovery to avoid expensive passes.
    /// This is intentionally keyed off existing budget knobs (frames/iterations/obligations)
    /// to avoid introducing new configuration flags.
    pub(in crate::pdr::solver) fn is_quick_check_mode(&self) -> bool {
        self.config.max_frames <= 2
            && self.config.max_iterations <= 10
            && self.config.max_obligations <= 1_000
    }

    /// Run the startup invariant discovery pipeline and direct safety check.
    ///
    /// This discovers invariants proactively (bounds, equalities, sums, differences,
    /// parity, affine, relational, etc.) before entering the main PDR blocking loop.
    ///
    /// Returns `Some(result)` if the solver should return early:
    /// - `Some(PdrResult::Safe(...))` if discovered invariants prove safety directly
    /// - `Some(PdrResult::Unknown)` if cancelled during discovery
    ///
    /// Returns `None` if discovery completed normally and the main loop should proceed.
    pub(in crate::pdr::solver) fn run_startup_discovery(&mut self) -> Option<PdrResult> {
        // Some startup invariant discovery passes can be very expensive. If the caller
        // provides extremely small resource limits (typically for quick soundness checks),
        // skip the discovery pipeline and rely on the bounded main PDR loop instead.
        //
        // inc-12: `skip_startup_discovery` promotes the same early-skip to an
        // explicit config flag for the spacer-mode portfolio PDR engine, which
        // spends its whole window in the blocking loop (interpolant-as-lemma).
        if self.is_quick_check_mode() || self.config.skip_startup_discovery {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Skipping startup invariant discovery (skip_flag={}, max_frames={}, max_iterations={}, max_obligations={})",
                    self.config.skip_startup_discovery,
                    self.config.max_frames, self.config.max_iterations, self.config.max_obligations
                );
            }
        } else if self.use_bv_native_fast_startup_path() {
            // #5877: BV-native single-predicate problems have transition relations
            // with thousands of BV nodes. Each startup discovery pass requires SMT
            // queries involving BV bit-blasting, which is 10-100x more expensive
            // than the LIA queries the startup pipeline was designed for. On
            // bist_cell (10000-node transition), the fixpoint loop (3 iterations ×
            // 7 passes per iteration) consumes the entire portfolio budget before
            // the main PDR blocking loop even starts.
            //
            // Skip the full startup discovery for BV-native problems and run only
            // the lightweight BV range invariant pass (2s budget) to seed basic
            // frame lemmas. The main PDR blocking loop will discover invariants
            // incrementally via counterexample-guided generalization.
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: BV-native fast startup — skipping full discovery pipeline (#5877)"
                );
            }
            let _startup_smt_timeout_guard =
                match self.startup_smt_timeout_cap(BV_FAST_STARTUP_SMT_TIMEOUT) {
                    StartupTimeoutCap::Disabled => None,
                    StartupTimeoutCap::Active(timeout) => {
                        Some(self.smt.scoped_check_timeout(Some(timeout)))
                    }
                    StartupTimeoutCap::Exhausted => {
                        return Some(self.finish_with_result_trace(PdrResult::Unknown));
                    }
                };
            if self.config.verbose {
                if let Some(timeout) = self.smt.current_timeout() {
                    safe_eprintln!("PDR: BV-native startup SMT timeout capped at {:?}", timeout);
                }
            }

            // Lane C fix: run lightweight equality discovery before BV range pass.
            // BV-native equality discovery operates on BV-sorted variables
            // (typically 5-20 per predicate), not expanded Bool variables. The
            // equality pass uses O(n^2) SMT checks where n = BV var count,
            // which is tractable. Without these seeds, the blocking loop produces
            // point lemmas that never converge to inductive invariants.
            if !self.is_cancelled() {
                let eq_start = ay_core::time::Instant::now();
                self.discover_equality_invariants();
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: BV-native equality discovery took {:?}",
                        eq_start.elapsed()
                    );
                }
            }

            self.discover_bv_range_invariants();
        } else {
            // Apply a per-query SMT timeout during startup discovery when cooperative
            // cancellation or a solve timeout is in effect. Without this, a single
            // expensive SMT query inside a discovery pass can block indefinitely
            // because cancellation is checked between passes. The requested 10s cap
            // is clipped to the remaining solve deadline so startup cannot outlive
            // short PDR probe budgets.
            let _startup_smt_timeout_guard =
                match self.startup_smt_timeout_cap(FULL_STARTUP_SMT_TIMEOUT) {
                    StartupTimeoutCap::Disabled => None,
                    StartupTimeoutCap::Active(timeout) => {
                        Some(self.smt.scoped_check_timeout(Some(timeout)))
                    }
                    StartupTimeoutCap::Exhausted => {
                        return Some(self.finish_with_result_trace(PdrResult::Unknown));
                    }
                };
            if self.config.verbose {
                if let Some(timeout) = self.smt.current_timeout() {
                    safe_eprintln!("PDR: Startup SMT timeout capped at {:?}", timeout);
                }
            }

            // inc-12: cap TOTAL startup discovery (fixpoint + nonfixpoint) at a
            // fraction of the engine window for wide-var linear shapes. The
            // thread-local SMT deadline clamps every SMT query INSIDE the
            // discovery passes (their internal loops previously ran to
            // completion, checked only between passes); the
            // `startup_deadline` field is checked at pass boundaries. The
            // guard is dropped before the end-of-startup direct safety check
            // and the main loop, which keep their full budgets. Timing-only:
            // candidates that miss the window are simply not discovered.
            let _startup_total_deadline_guard = self.wide_var_startup_budget().map(|budget| {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: wide-var startup cap — total discovery budget {:?} (inc-12)",
                        budget
                    );
                }
                self.startup_deadline = Some(ay_core::time::Instant::now() + budget);
                crate::smt::ScopedSmtDeadline::install(budget)
            });

            let fixpoint_cancelled = if let Some(result) = self.run_fixpoint_discovery() {
                if !matches!(result, PdrResult::Unknown) {
                    return Some(result);
                }
                // Fixpoint was cancelled (solve_deadline or portfolio). The
                // post-cancel kernel path below is only allowed to continue if
                // the startup timeout helper still finds bounded budget.
                true
            } else {
                false
            };

            if !fixpoint_cancelled {
                // The fixpoint loop can now seed phase-conditional invariants for
                // small ITE loops. Check immediately so a proof-carrying frame does
                // not spend the remaining focused PDR budget in the late discovery
                // tail before strict final validation.
                if !self.skip_startup_direct_safety_proof() {
                    let _t_post_fixpoint = ay_core::time::Instant::now();
                    if let Some(model) = self.check_invariants_prove_safety() {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Post-fixpoint invariants prove safety directly ({:?})",
                                _t_post_fixpoint.elapsed()
                            );
                        }
                        // #4751: on strict-validation demotion, fall through to
                        // nonfixpoint discovery instead of aborting.
                        if let Some(result) =
                            self.finish_safe_or_continue(model, "post-fixpoint startup model")
                        {
                            return Some(result);
                        }
                        // Demoted: prune the poisoned frame and retry once
                        // before the nonfixpoint tail (gj2007_m_3, #4751).
                        if let Some(result) =
                            self.demotion_prune_and_retry("post-prune post-fixpoint startup model")
                        {
                            return Some(result);
                        }
                    }
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Post-fixpoint direct safety check not yet sufficient ({:?})",
                            _t_post_fixpoint.elapsed()
                        );
                    }
                }

                // Normal path: run full nonfixpoint discovery.
                if let Some(result) = self.run_nonfixpoint_discovery() {
                    return Some(result);
                }
            } else {
                // Cancelled path: fail closed if the solve deadline/cancellation
                // budget is exhausted. If a caller reaches this path with bounded
                // budget still available, keep the old kernel salvage path.
                //
                // Temporarily extend the solve_deadline only if there is budget
                // left. Startup must not spend a fresh 10s after the advertised
                // solve_timeout or portfolio cancellation budget is exhausted.
                let saved_deadline = self.solve_deadline;
                let post_cancel_budget = match self.post_cancel_startup_salvage_budget() {
                    Some(timeout) => timeout,
                    None => return Some(self.finish_with_result_trace(PdrResult::Unknown)),
                };
                self.solve_deadline = Some(ay_core::time::Instant::now() + post_cancel_budget);

                let _t_post = ay_core::time::Instant::now();
                self.discover_affine_invariants_via_kernel(None);
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: post-cancel kernel discovery took {:?}",
                        _t_post.elapsed()
                    );
                }

                if self.is_cancelled() {
                    self.solve_deadline = saved_deadline;
                    return Some(self.finish_with_result_trace(PdrResult::Unknown));
                }

                // Check safety BEFORE restoring the original deadline (#5399),
                // but only after re-checking cancellation. The temporary salvage
                // deadline above is clipped to remaining budget, so a post-kernel
                // cancellation must fail closed instead of proving safety late.
                if self.skip_startup_direct_safety_proof() {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Skipping post-cancel startup direct safety proof for native \
                             single-predicate BV; defer to blocking loop (#5877)"
                        );
                    }
                } else {
                    let _t15 = ay_core::time::Instant::now();
                    if let Some(mut model) = self.check_invariants_prove_safety() {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: check_invariants_prove_safety took {:?}",
                                _t15.elapsed()
                            );
                            safe_eprintln!(
                                "PDR: Discovered invariants prove safety directly (post-cancel)!"
                            );
                        }
                        // SOUNDNESS (#5922): Fresh-context confirmation.
                        //
                        // When the startup fixpoint converged without conjunct
                        // filtering, the model is convergence_proven: the full
                        // frame conjunction is inductive by construction. In that
                        // case, fresh query-only validation is the right sound
                        // check; requiring a fresh transition proof is an
                        // unnecessary SMT re-check that can fail spuriously on
                        // gj2007-style phase chains.
                        let fresh_ok = if model.convergence_proven {
                            self.verify_model_fresh_query_only(&model)
                        } else {
                            self.verify_model_fresh(&model)
                        };
                        if !fresh_ok {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: startup post-cancel model fails fresh-context \
                                     verification (#5922); continuing"
                                );
                            }
                        } else {
                            // SOUNDNESS (#5922): Save model before simplification.
                            let original_model = model.clone();
                            let simp = self.simplify_model(&mut model);
                            // Re-verify when simplification modified the model (#5805, #5922).
                            if simp.modified() && !self.verify_model(&model) {
                                if simp.free_vars_sanitized {
                                    // Free-var sanitization modified the model and re-verification
                                    // failed. The original model already passed verify_model_fresh
                                    // at line 180. Accept it directly — re-running query-only
                                    // verification would be redundant and can fail due to SMT
                                    // non-determinism on mod/div query clauses (#1362).
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: simplified startup model fails re-verification \
                                             after free-variable sanitization; falling back to \
                                             original model (verify_model_fresh passed) (#1362)"
                                        );
                                    }
                                    self.solve_deadline = saved_deadline;
                                    return Some(self.finish_safe_with_result_trace(
                                        original_model,
                                        "startup post-cancel pre-simplification fallback",
                                    ));
                                } else {
                                    // Only redundancy removal — fall back (#5922).
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: simplified startup model fails re-verification; \
                                             falling back to pre-simplification model"
                                        );
                                    }
                                    self.solve_deadline = saved_deadline;
                                    return Some(self.finish_safe_with_result_trace(
                                        original_model,
                                        "startup post-cancel pre-simplification fallback",
                                    ));
                                }
                            } else {
                                self.solve_deadline = saved_deadline;
                                return Some(self.finish_safe_with_result_trace(
                                    model,
                                    "startup post-cancel model",
                                ));
                            }
                        }
                    }
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: check_invariants_prove_safety took {:?}",
                            _t15.elapsed()
                        );
                    }
                }

                // Restore original deadline.
                self.solve_deadline = saved_deadline;
            }
        }

        if self.skip_startup_direct_safety_proof() {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Skipping startup direct safety proof for native single-predicate BV; \
                     defer to blocking loop (#5877)"
                );
            }
            return None;
        }

        // Direct safety check: if discovered invariants prove all error states unreachable,
        // return Safe immediately without going through the iterative PDR loop.
        let _t15 = ay_core::time::Instant::now();
        if let Some(mut model) = self.check_invariants_prove_safety() {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: check_invariants_prove_safety took {:?}",
                    _t15.elapsed()
                );
                safe_eprintln!("PDR: Discovered invariants prove safety directly!");
            }
            // SOUNDNESS (#5922): Fresh-context confirmation.
            // #8782: convergence_proven models were built from a converged fixpoint
            // (frame[k] = frame[k+1]) without conjunct filtering. The full frame
            // conjunction is inductive by the PDR convergence theorem. Full
            // transition verification in a fresh context can fail due to SMT
            // budget exhaustion on complex multi-predicate models where some
            // predicates have vacuously-false frames. Query-only validation
            // confirms the invariant blocks the error (soundness-critical).
            // Matches the pattern in nonfixpoint.rs line 114-118.
            // (#8782): Skip expensive fresh-context verification for
            // individually_inductive models. Each lemma was already proven
            // self-inductive independently of the frame. Any Safe returned
            // from this path still passes through strict final validation.
            let fresh_full = if model.individually_inductive {
                true // Skip — already proven at PDR level
            } else if model.convergence_proven {
                self.verify_model_fresh_query_only(&model)
            } else {
                self.verify_model_fresh(&model)
            };
            let fresh_ok = fresh_full || model.individually_inductive;

            // #1362: When verify_model_fresh fails due to SMT incompleteness,
            // fall back to individual lemma verification. If every frame[1]
            // lemma is individually STRICTLY self-inductive (algebraically
            // verified OR SMT-checked WITHOUT frame strengthening), accept the
            // model with the individually_inductive flag (routes to query-only
            // validation at portfolio level).
            //
            // D3 #1362: Uses is_strictly_self_inductive_blocking (no frame
            // context) to match the contract accept.rs expects at lines
            // 168-176. With strict self-inductiveness, the has_algebraic_mod
            // gate is no longer needed — each lemma is verified on its own
            // merits, not relative to other frame lemmas. The D2 frame
            // consistency check remains as defense-in-depth against vacuous
            // inductiveness from contradictory frames.
            // #7469: Hyperedge clauses (>1 body predicate) make per-lemma
            // entry-inductiveness checks unsound — must-summaries/frame
            // constraints for body predicates may be weaker than the actual
            // reachable set. Require full verification for hyperedge problems.
            // Mirror: safety_checks.rs:57-62.
            let has_hyperedge = self
                .problem
                .clauses()
                .iter()
                .any(|c| c.body.predicates.len() > 1);
            let individually_verified = !fresh_ok && self.frames.len() > 1 && !has_hyperedge && {
                // D2 #1362: Check frame[1] consistency before
                // individually_verified bypass. Contradictory frame lemmas
                // can make inductiveness checks vacuously true.
                // Mirror: safety_proof.rs:535-580.
                let frame_has_contradiction = {
                    let mut found = false;
                    let mut checked_preds = ay_core::kani_compat::DetHashSet::default();
                    for lemma in &self.frames[1].lemmas {
                        if !checked_preds.insert(lemma.predicate) {
                            continue;
                        }
                        let pred_lemmas: Vec<ChcExpr> = self.frames[1]
                            .lemmas
                            .iter()
                            .filter(|l| l.predicate == lemma.predicate)
                            .map(|l| l.formula.clone())
                            .collect();
                        if pred_lemmas.len() >= 2 {
                            let conjunction = ChcExpr::and_all(pred_lemmas);
                            let bounded = self.bound_int_vars(conjunction);
                            self.smt.reset();
                            let Some(timeout) =
                                self.startup_query_timeout(STARTUP_FRAME_CONTRADICTION_TIMEOUT)
                            else {
                                found = true;
                                break;
                            };
                            let result = self.smt.check_sat_with_timeout(&bounded, timeout);
                            if result.is_unsat() {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: individually_verified skipped: \
                                             frame[1] pred {} has contradictory \
                                             lemmas (#1362 D2)",
                                        lemma.predicate.index()
                                    );
                                }
                                found = true;
                                break;
                            }
                        }
                    }
                    found
                };
                if frame_has_contradiction {
                    false
                } else {
                    let lemmas: Vec<_> = self.frames[1]
                        .lemmas
                        .iter()
                        .map(|l| {
                            (
                                l.predicate,
                                l.formula.clone(),
                                l.algebraically_verified,
                                l.relative_induction_only,
                            )
                        })
                        .collect();
                    let is_multi_pred = self.problem.predicates().len() > 1;
                    lemmas
                        .iter()
                        .all(|(pred, formula, alg_verified, rel_only)| {
                            if *alg_verified {
                                // Algebraically verified lemmas are sound per-predicate.
                                // For multi-pred, also verify entry-inductiveness to
                                // cover cross-predicate transitions.
                                return !is_multi_pred
                                    || self.is_entry_inductive(formula, *pred, 1);
                            }
                            // Hint lemmas admitted under relative (entry) induction
                            // only can never satisfy the strict per-lemma contract:
                            // their predicate has no self-loop clause, so the strict
                            // oracle rejects vacuously (#8578). Short-circuit.
                            if *rel_only {
                                return false;
                            }
                            // D3 #1362: Strict self-inductiveness WITHOUT frame
                            // strengthening. Each lemma must be self-inductive on
                            // its own, matching the contract accept.rs expects.
                            let blocking = ChcExpr::not(formula.clone());
                            let self_ind =
                                self.is_strictly_self_inductive_blocking(&blocking, *pred);
                            if !self_ind {
                                return false;
                            }
                            // For multi-pred: also require entry-inductiveness to
                            // cover cross-predicate transitions (P1→P0).
                            !is_multi_pred || self.is_entry_inductive(formula, *pred, 1)
                        })
                }
            };

            // NOTE: A query_only_verified fallback was here (#1362) but was
            // UNSOUND — same root cause as safety_checks.rs query-only bypass.
            // Query-only checks only verify the invariant blocks the error;
            // they do not verify inductiveness. Removed for soundness.

            if !fresh_ok && !individually_verified {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: startup-direct model fails fresh-context \
                         verification (#5922); continuing"
                    );
                }
            } else {
                if !fresh_ok && self.config.verbose {
                    safe_eprintln!(
                        "PDR: startup-direct model fails verify_model_fresh but all \
                         {} lemmas individually verified (#1362); accepting",
                        self.frames[1].lemmas.len()
                    );
                }
                // #9227: Preserve the evidence flag for diagnostics, but direct
                // PDR Safe results still pass through strict final validation.
                if individually_verified {
                    model.individually_inductive = true;
                }
                // SOUNDNESS (#5922): Save model before simplification.
                let original_model = model.clone();
                // Simplify the invariant (Z3 Spacer's unconditional solve-completion cleanup).
                // Portfolio always runs full verification (#5745).
                let simp = self.simplify_model(&mut model);
                // Re-verify when simplification modified the model (#5805, #5922).
                // (#8782): Skip re-verification for individually_inductive models.
                // Each lemma was already proven self-inductive independently.
                let reverify_needed =
                    simp.modified() && !model.individually_inductive && !individually_verified;
                if reverify_needed && !self.verify_model(&model) {
                    if individually_verified {
                        // #1362: When individually_verified, simplification may
                        // invalidate the model (e.g., free-var sanitization on
                        // parametric init like 2*A). Fall back to original model.
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: simplified startup-direct model fails re-verification; \
                                 falling back to individually-verified original model (#1362)"
                            );
                        }
                        // #4751: fall through to the main loop on demotion.
                        if let Some(result) = self.finish_safe_or_continue(
                            original_model,
                            "startup-direct individually-verified fallback",
                        ) {
                            return Some(result);
                        }
                    } else if simp.free_vars_sanitized {
                        // Free-var sanitization modified the model and re-verification
                        // failed. The original model already passed fresh verification
                        // (fresh_ok was true at line 275). Accept it directly — re-running
                        // verify_model_fresh_query_only here is redundant and can fail
                        // due to SMT non-determinism on mod/div query clauses (e.g.,
                        // phases_m clause 4 has `mod C 2`). (#1362)
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: simplified startup-direct model fails re-verification \
                                 after free-variable sanitization; falling back to original \
                                 model (fresh_ok already confirmed) (#1362)"
                            );
                        }
                        // #4751: fall through to the main loop on demotion.
                        if let Some(result) = self.finish_safe_or_continue(
                            original_model,
                            "startup-direct pre-simplification fallback",
                        ) {
                            return Some(result);
                        }
                    } else {
                        // Only redundancy removal — fall back (#5922).
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: simplified startup-direct model fails re-verification; \
                                 falling back to pre-simplification model"
                            );
                        }
                        // #4751: fall through to the main loop on demotion.
                        if let Some(result) = self.finish_safe_or_continue(
                            original_model,
                            "startup-direct pre-simplification fallback",
                        ) {
                            return Some(result);
                        }
                    }
                } else if let Some(result) =
                    self.finish_safe_or_continue(model, "startup-direct model")
                {
                    // #4751: fall through to the main loop on demotion.
                    return Some(result);
                }
            }
        }
        if self.config.verbose {
            safe_eprintln!(
                "PDR: check_invariants_prove_safety took {:?}",
                _t15.elapsed()
            );
        }

        // #4751: A strict-validation demotion above means the frame carries
        // lemmas admitted through must-summary-relative oracles that are not
        // globally inductive (dillig12_m: `(mod C 16)=0`, `A=C` at depth<=1).
        // Houdini-prune frame[1] to its relatively-inductive core, then retry
        // the direct safety check once on the clean frame. Sound: removal only
        // weakens the frame, and the retried model still passes strict final
        // validation inside finish_safe_or_continue.
        if self.strict_validation_demotions > 0
            && !self.is_cancelled()
            && self.houdini_prune_frame1_to_inductive_core() > 0
        {
            if let Some(model) = self.check_invariants_prove_safety() {
                if self.config.verbose {
                    safe_eprintln!("PDR: post-prune direct safety check produced a model (#4751)");
                }
                if let Some(result) =
                    self.finish_safe_or_continue(model, "post-prune startup-direct model")
                {
                    return Some(result);
                }
            }
        }

        None
    }
}

#[cfg(test)]
mod tests;
