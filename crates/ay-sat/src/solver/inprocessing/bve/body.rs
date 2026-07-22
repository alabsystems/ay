// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//\! BVE core elimination loop.

use super::super::super::mutate::{ReasonPolicy, ReplaceResult};
use super::super::super::*;
use super::state::BveBodyStats;
use super::{BVE_BINARY_DEGREE_PRODUCT_LIMIT, FASTELIM_OCC_LIMIT};
use crate::bve::fast_eliminate::{QUICK_ELIM_CLS_LIMIT, QUICK_ELIM_OCC_LIMIT};
use crate::gates::BveExtraction;
use crate::kani_compat::DetHashSet as HashSet;
use crate::solver_log::solver_log;

impl Solver {
    pub(super) fn bve_body(&mut self) -> bool {
        if !self.enter_inprocessing() {
            return false;
        }

        // Skip in incremental mode: BVE rewrites the clause database via
        // resolution, which cannot be reversed across solve boundaries (#5031, #5166).
        if self.cold.has_been_incremental && !self.has_scoped_bve() {
            return false;
        }

        // #8397 (FIXED): BVE now safely coexists with extension variables
        // (factoring/SBVA). The previous guard disabled BVE entirely once
        // extension variables existed. The per-variable guard in the
        // elimination loop (below) skips individual variables whose
        // occurrence clauses contain unelimianted extension variables,
        // while allowing BVE to proceed on unaffected variables.

        // Compute resolution effort limit.
        //
        // CaDiCaL: elimfast.cpp:279-290 / elim.cpp:778-796 — both use
        // `stats.propagations.search * elimeffort / 1000`, clamped to
        // [elimmineff, elimmaxeff]. Critically, CaDiCaL's counter tracks
        // only CDCL search propagations, not probing or preprocessing.
        //
        // AY's `num_propagations` includes probing propagations. During
        // preprocessing, probing runs BEFORE BVE and can inflate the
        // counter to 100M+, giving BVE an enormous budget that wastes
        // seconds on futile round-2 candidates. CaDiCaL's search counter
        // is 0 at this point, yielding effort = clamped min = 10M.
        //
        // Fix: in fastelim mode (preprocessing), use only the minimum
        // effort. During inprocessing (search), num_propagations reflects
        // actual search work and the formula is correct.
        // Compute tick-proportional effort limit (CaDiCaL elim.cpp:778-796,
        // ported to search_ticks delta per SET_EFFORT_LIMIT pattern #8148).
        //
        // CaDiCaL uses `stats.propagations.search * elimeffort / 1000`
        // (total propagations). AY uses tick-delta since last BVE call
        // for consistency with the unified tick-proportional scheduling model.
        // During preprocessing (fastelim), there are no search ticks yet, so
        // a fixed base budget is used instead.
        // DEEP sparse-band lever (kill-switched, default OFF): raise the
        // fastelim wall, per-round resolution effort, and round count so a huge
        // sparse formula can approach kissat-style dense elimination instead of
        // stalling at ~2.5% on the 2s wall + ~3.38M effort cap. Scoped to
        // num_vars>150K in-band formulas; a hard no-op when the knob is off.
        let deep = self.bve_sparse_deep_active();
        // Proof-aware wall (wf_0c7d84e9): x4 under DRAT emission so proof
        // step-tracking overhead does not shrink the WORK a fastelim pass
        // admits (70da0b78: unsat 1.8s no-proof, >180s unknown under --proof
        // bound by this wall). Neutral (x1) without a proof — see
        // PROOF_WALL_BUDGET_SCALE.
        let fastelim_wall_secs = self.bve_wall_budget_scale()
            * if deep {
                BVE_SPARSE_DEEP_WALL_SECS
            } else {
                FASTELIM_WALL_CLOCK_LIMIT_SECS
            };
        let effort = if self.inproc.bve.is_fastelim_mode() {
            let base = FASTELIM_EFFORT;
            let active_cls = self.arena.active_clause_count() as u64;
            // Scale down effort for large formulas (#8136).
            if active_cls > FASTELIM_SCALE_CLAUSE_THRESHOLD {
                let scaled = (base as f64 * FASTELIM_SCALE_CLAUSE_THRESHOLD as f64
                    / active_cls as f64) as u64;
                scaled.max(FASTELIM_MIN_SCALED_EFFORT)
            } else {
                base
            }
        } else {
            let ticks_now = self.search_ticks[0] + self.search_ticks[1];
            let ticks_delta = ticks_now.saturating_sub(self.cold.last_bve_ticks);
            let raw = ticks_delta * self.cold.bve_effort_permille / 1000;
            raw.clamp(BVE_MIN_EFFORT, BVE_MAX_EFFORT)
        };
        let active_vars = self
            .num_vars
            .saturating_sub(self.var_lifecycle.count_removed()) as u64;
        let effort = effort.max(2 * active_vars);
        // DEEP: lift the per-round resolution effort toward kissat parity so the
        // second-order budget_exhausted limiter stops throttling once the wall
        // is raised (measured: without this, deep re-plateaus at ~62K/round).
        let effort = if deep && self.inproc.bve.is_fastelim_mode() {
            effort.max(
                active_vars
                    .saturating_mul(BVE_SPARSE_DEEP_EFFORT_PER_VAR)
                    .min(BVE_SPARSE_DEEP_EFFORT_CAP),
            )
        } else {
            effort
        };

        let mut derived_unsat = false;
        let mut stats = BveBodyStats::default();
        #[cfg(ay_logging)]
        let mut gate_eliminations = 0usize;
        #[cfg(ay_logging)]
        let clauses_at_bve_start = self.arena.num_clauses();
        let active_at_bve_start = self.arena.active_clause_count();
        let irredundant_at_bve_start = self.arena.irredundant_count();

        // Reuse persistent scratch buffers to avoid per-BVE-round allocation (#8602).
        // Take ownership via std::mem::take to avoid borrow conflicts with &mut self
        // methods called throughout the loop. Returned to cold state at function exit.
        let mut scratch = std::mem::take(&mut self.cold.bve_body_scratch);
        scratch.clear();
        let mut pending_gc_indices: Vec<usize> = Vec::new();

        // Ensure there are dirty candidates. In fastelim mode, build_schedule
        // skips the dirty filter. In additive mode, dirty bits are set
        // incrementally by subsumption/vivify/decompose. On the first
        // inprocessing BVE call (or when called directly in tests), no
        // incremental marking has happened. Mark all candidates dirty to
        // avoid an empty schedule.
        if !self.inproc.bve.is_fastelim_mode() && !self.inproc.bve.has_dirty_candidates() {
            self.inproc.bve.mark_all_candidates_dirty();
        }

        if self.cold.lrat_enabled {
            self.materialize_level0_unit_proofs();
        }

        let max_rounds = if self.inproc.bve.is_fastelim_mode() {
            // Reduce rounds for large formulas (#8136).
            let active_cls = self.arena.active_clause_count();
            if deep {
                // DEEP: allow the inter-round subsume + occ-refresh cascade to
                // fire on huge formulas (the >3M-clause branch otherwise caps
                // at a single shallow round, suppressing the cascade that
                // realizes the bulk of kissat's eliminable variables).
                BVE_SPARSE_DEEP_ROUNDS
            } else if active_cls > 3_000_000 {
                1
            } else if active_cls > FASTELIM_SCALE_CLAUSE_THRESHOLD as usize {
                2
            } else {
                PREPROCESS_BVE_ROUNDS
            }
        } else {
            BVE_ROUNDS
        };
        // Debug override for bisection (#8133).
        // Uses cached OnceLock instead of per-call env::var syscall (#8506).
        let max_rounds = ay_core::sat_debug_env_flags()
            .bve_max_rounds
            .map_or(max_rounds, |r| r.min(max_rounds));
        self.inproc
            .bve
            .set_scope_var_floor(self.scope_var_start().unwrap_or(0)); // #8369
        let bve_wall_start = ay_core::time::Instant::now();
        let mut candidates_exhausted = false;
        for round in 0..max_rounds {
            // Respect preprocessing deadline within BVE (#8448).
            // BVE is often the longest individual preprocessing pass. Without
            // an intra-pass deadline check, a single BVE call can exceed the
            // 2s Small-formula budget on dense formulas like Schur_161_5
            // (757 vars, 28K clauses) where 274K resolutions cost ~10s.
            // DEEP relies on the (extended) preprocess budget + the deep wall
            // below to bound cost; do not let the pre-deep 2s deadline cut the
            // inter-round cascade short.
            if round > 0 && !deep && self.preprocess_timed_out() {
                break;
            }
            // Wall-clock guard for fastelim on large formulas (#8136).
            if round > 0
                && self.inproc.bve.is_fastelim_mode()
                && bve_wall_start.elapsed().as_secs() >= fastelim_wall_secs
            {
                break;
            }
            // Wall-clock guard for inprocessing BVE (#8078).
            if round > 0
                && !self.inproc.bve.is_fastelim_mode()
                && bve_wall_start.elapsed().as_millis() as u64 >= BVE_INPROCESSING_WALL_LIMIT_MS
            {
                break;
            }
            if round > 0 && stats.total_eliminations > 0 {
                // Inter-round GC: delete clauses with eliminated variables
                // before rebuilding occ lists for the next round.
                //
                // Full arena scan (#8483): the previous approach only checked
                // `pending_gc_indices` (from OTFS strengthening), but inter-round
                // `self.subsume()` can strengthen clauses that still contain
                // variables eliminated in earlier rounds. Those strengthened
                // clauses are not in `pending_gc_indices`, so the old targeted
                // GC missed them. Use the same full arena scan as post-BVE GC
                // for soundness.
                // Reuse persistent buffer to avoid arena-proportional allocation (#8602).
                self.cold.reduce_indices_buf.clear();
                self.cold.reduce_indices_buf.extend(self.arena.indices());
                for i in 0..self.cold.reduce_indices_buf.len() {
                    let idx = self.cold.reduce_indices_buf[i];
                    if self.arena.is_dead(idx) {
                        continue;
                    }
                    let has_eliminated = self
                        .arena
                        .literals(idx)
                        .iter()
                        .any(|lit| self.var_lifecycle.is_removed(lit.variable().index()));
                    if has_eliminated {
                        self.delete_clause_checked(idx, ReasonPolicy::ClearLevel0);
                    }
                }
                pending_gc_indices.clear();
            }

            // Guarded saved-state reuse (#8096, #8366, #9106).
            //
            // The BVE occurrence lists are maintained across inprocessing
            // rounds by per-clause mutation hooks. Reusing them avoids the
            // O(irredundant_clause_literals) clear-and-rebuild pass on every
            // BVE round. Earlier reuse was forced off after stale occurrence
            // entries caused model reconstruction failures on gate-structured
            // formulas (#8482). `refresh_incremental()` now runs a release-mode
            // bidirectional consistency gate and falls back to a full rebuild
            // if any missing or stale live entry is found, so proof/model
            // safety stays fail-closed. The scan is skipped only when the
            // saved state was already validated for the same clause-DB mutation
            // epoch; any checked add/delete/replace forces validation again.
            let clause_db_epoch = self.cold.clause_db_changes;
            if self.inproc.bve.is_occ_populated() {
                if self.inproc.bve.refresh_incremental_at_epoch(
                    &self.arena,
                    &self.vals,
                    clause_db_epoch,
                ) {
                    self.stats.occ_incremental_refreshes += 1;
                } else {
                    self.stats.occ_full_rebuilds += 1;
                }
            } else {
                self.inproc.bve.rebuild_with_vals_at_epoch(
                    &self.arena,
                    &self.vals,
                    clause_db_epoch,
                );
                self.stats.occ_full_rebuilds += 1;
            }

            let mut eliminated_this_round = false;
            let resolution_limit = self.cold.bve_resolutions.saturating_add(effort);
            let elim_cap = if self.inproc.bve.is_fastelim_mode() {
                if deep {
                    // DEEP: lift the 100K per-call elimination cap so the extra
                    // wall/effort/rounds can actually accumulate eliminations
                    // past it on huge sparse formulas.
                    BVE_SPARSE_DEEP_MAX_ELIMINATIONS
                } else {
                    FASTELIM_MAX_ELIMINATIONS
                }
            } else {
                MAX_BVE_ELIMINATIONS
            };
            // Partial BVE (#8099): during inprocessing (not fastelim), cap the
            // number of candidate variables attempted per round. This bounds
            // per-round wall-clock time to ~1-2ms by processing only the cheapest
            // candidates, making BVE rounds faster and more frequent overall.
            let candidate_attempt_cap = if self.inproc.bve.is_fastelim_mode() {
                usize::MAX // no cap during preprocessing
            } else {
                BVE_PARTIAL_CANDIDATES_PER_ROUND
            };
            let mut candidates_attempted: usize = 0;
            // Debug: limit total eliminations for bisection (cached at solver creation)
            let elim_cap = if let Some(limit) = self.cold.bve_limit {
                elim_cap.min(limit)
            } else {
                elim_cap
            };
            candidates_exhausted = false;
            // Defer proof deletion emissions during the elimination loop (#8011).
            // BVE processes variables sequentially: for each variable, resolvents
            // are added and then original clauses are deleted. Across variables,
            // deletions from variable A can remove clauses needed for variable B's
            // resolvent RUP derivability. By deferring all proof deletions until
            // after the elimination loop, we ensure the DRAT proof stream has all
            // resolvent additions before any deletions.
            let has_proof_output =
                self.cold.forward_checker.is_some() || self.proof_manager.is_some();
            if has_proof_output {
                self.defer_proof_deletions = true;
            }
            while stats.total_eliminations < elim_cap
                && self.cold.bve_resolutions < resolution_limit
                && candidates_attempted < candidate_attempt_cap
            {
                // Check external interrupt (timeout) every 64 eliminations to
                // avoid spending seconds in BVE after the DPLL timeout fires.
                // This fixes QF_ABV regression on try5_dwp_fmt where the
                // reduced formula (from cached false/true literals) enabled
                // BVE to find 26K+ substitutions taking 18.9s. (#8782)
                //
                // Also check BVE wall-clock limit (#8448): a single BVE round
                // on large formulas (shuffling-2: 4.7M clauses, 54K eliminations)
                // can take 14s without an intra-round clock check. The round-level
                // guard (FASTELIM_WALL_CLOCK_LIMIT_SECS) only fires between rounds;
                // with max_rounds=1 for >3M clauses, it never triggers. This
                // intra-round check caps a single round at the same limit.
                if stats.total_eliminations & 63 == 0 {
                    if self.is_interrupted() {
                        break;
                    }
                    if self.inproc.bve.is_fastelim_mode()
                        && bve_wall_start.elapsed().as_secs() >= fastelim_wall_secs
                    {
                        break;
                    }
                }
                candidates_attempted += 1;
                let var = match self.inproc.bve.next_candidate(
                    &self.arena,
                    &self.vals,
                    &self.cold.freeze_counts,
                ) {
                    Some(v) => v,
                    None => {
                        candidates_exhausted = true;
                        break;
                    }
                };
                debug_assert!(
                    !self.var_is_assigned(var.index()),
                    "BUG: BVE candidate var {var:?} is assigned",
                );
                debug_assert!(
                    !self.var_lifecycle.is_removed(var.index()),
                    "BUG: BVE candidate var {var:?} is already removed",
                );
                debug_assert!(
                    self.cold
                        .freeze_counts
                        .get(var.index())
                        .copied()
                        .unwrap_or(0)
                        == 0,
                    "BUG: BVE candidate var {var:?} is frozen",
                );

                // #8397: Skip variables that co-occur with extension variables.
                //
                // Factoring creates extension variables with divider/quotient
                // clauses (e.g., [E, -x] replacing parts of [-x, -y]). If BVE
                // eliminates x, the divider clause [E, -x] is pushed onto the
                // reconstruction stack with witness -x. During reconstruction,
                // the extension variable E's value (set by the solver, not by
                // any reconstruction entry — factoring does NOT push
                // reconstruction entries per CaDiCaL factor.cpp) determines
                // whether x gets flipped. This can cause x to take a value
                // inconsistent with original clauses (like [-x, -y]).
                //
                // CaDiCaL avoids this by having BVE eliminate extension
                // variables first (they have very few occurrences), which
                // pushes proper reconstruction entries for them. AY's BVE
                // ordering may not prioritize extension variables, so we guard
                // against this by skipping variables whose occurrence clauses
                // contain unelimianted extension variables.
                //
                // This is more targeted than the previous guard (removed above)
                // which blocked ALL BVE when ANY extension variables existed.
                // #8397, #8466: Guard against BVE of ORIGINAL variables that
                // co-occur with live extension variables.
                //
                // Factoring creates extension variables with divider/quotient
                // clauses. If BVE eliminates an original variable x before
                // its co-occurring extension variable E is eliminated, the
                // reconstruction stack entry for x references E whose value
                // is set by the solver (not by reconstruction), causing
                // potential model corruption.
                //
                // CaDiCaL avoids this by eliminating extension variables first
                // (they have few occurrences). AY mirrors this: extension
                // variables themselves are ALWAYS eligible for BVE, and
                // original variables are eligible once their co-occurring
                // extension variables have been eliminated.
                if self.cold.first_extension_var_index != usize::MAX {
                    let ext_start = self.cold.first_extension_var_index;
                    // Extension variables are always eligible for BVE —
                    // they need to be eliminated first so that original
                    // variables can then be eliminated safely.
                    if var.index() < ext_start {
                        let pos_occs = self.inproc.bve.get_occs(Literal::positive(var));
                        let neg_occs = self.inproc.bve.get_occs(Literal::negative(var));
                        let has_live_ext_var = pos_occs.iter().chain(neg_occs.iter()).any(|&idx| {
                            if idx >= self.arena.len() || self.arena.is_dead(idx) {
                                return false;
                            }
                            self.arena.literals(idx).iter().any(|lit| {
                                let vi = lit.variable().index();
                                vi >= ext_start && !self.var_lifecycle.is_removed(vi)
                            })
                        });
                        if has_live_ext_var {
                            continue;
                        }
                    }
                }

                if self.inproc.bve.is_fastelim_mode() {
                    let (occ_limit, cls_limit) = if self.inproc.bve.is_quick_elim_mode() {
                        (QUICK_ELIM_OCC_LIMIT, QUICK_ELIM_CLS_LIMIT)
                    } else {
                        (FASTELIM_OCC_LIMIT, 100)
                    };
                    let pos_occs = self.inproc.bve.get_occs(Literal::positive(var));
                    let neg_occs = self.inproc.bve.get_occs(Literal::negative(var));
                    if pos_occs.len() > occ_limit || neg_occs.len() > occ_limit {
                        continue;
                    }
                    let has_oversized = pos_occs
                        .iter()
                        .chain(neg_occs.iter())
                        .any(|&idx| self.arena.len_of(idx) > cls_limit);
                    if has_oversized {
                        continue;
                    }
                }

                // Dense binary degree guard for gate-based (additive) BVE
                // only (#8398, #8466).
                //
                // Gate-based BVE with restricted resolution still produces
                // O(gate * non-gate) resolvents for binary clauses. On
                // clique_n2_k10, gate-based passes at bounds 1,2,4,8,16
                // accumulate hundreds of binary resolvents that make the
                // formula progressively harder for CDCL search.
                //
                // The guard uses the binary degree product as a proxy for
                // resolvent density: when pos_binary * neg_binary exceeds
                // the limit, the variable is deeply embedded in binary
                // structure and elimination is likely counterproductive.
                //
                // #8466: Skip this guard in fastelim mode. CaDiCaL's fastelim
                // has no binary degree product guard -- it relies on the
                // resolvent counting loop with fastelimbound=8 to reject
                // expensive variables. On clique_n2_k10 (17 binary occs per
                // polarity, product=289), the guard blocks ALL variables from
                // BVE, producing only 10 eliminations vs CaDiCaL's 359. With
                // the guard removed in fastelim, the resolvent counting loop
                // correctly identifies that most binary-binary resolvents are
                // tautological (both colors of the same vertex), allowing
                // profitable eliminations. The fastelim budget of 8 prevents
                // clause explosion even without this guard.
                if !self.inproc.bve.is_fastelim_mode() {
                    let pos_occs = self.inproc.bve.get_occs(Literal::positive(var));
                    let neg_occs = self.inproc.bve.get_occs(Literal::negative(var));
                    let pos_binary = pos_occs
                        .iter()
                        .filter(|&&idx| {
                            idx < self.arena.len()
                                && !self.arena.is_dead(idx)
                                && self.arena.len_of(idx) == 2
                        })
                        .count();
                    let neg_binary = neg_occs
                        .iter()
                        .filter(|&&idx| {
                            idx < self.arena.len()
                                && !self.arena.is_dead(idx)
                                && self.arena.len_of(idx) == 2
                        })
                        .count();
                    let product = pos_binary.saturating_mul(neg_binary);
                    if product > BVE_BINARY_DEGREE_PRODUCT_LIMIT {
                        continue;
                    }
                }

                scratch.pos_occs.clear();
                scratch
                    .pos_occs
                    .extend_from_slice(self.inproc.bve.get_occs(Literal::positive(var)));
                scratch.neg_occs.clear();
                scratch
                    .neg_occs
                    .extend_from_slice(self.inproc.bve.get_occs(Literal::negative(var)));

                let extraction =
                    if self.inproc.bve.is_fastelim_mode() || !self.inproc_ctrl.gate.enabled {
                        None
                    } else {
                        let gate_extractor = &mut self.inproc.gate_extractor;
                        let definition_kitten = &mut self.inproc.definition_kitten;
                        gate_extractor.find_extraction_for_bve_with_marks(
                            definition_kitten,
                            var,
                            &self.arena,
                            &scratch.pos_occs,
                            &scratch.neg_occs,
                            &self.vals,
                            &mut self.lit_marks,
                        )
                    };
                let (gate_defining, resolve_gate_pairs) = match extraction {
                    Some(BveExtraction::RestrictResolution {
                        defining_clauses,
                        resolve_gate_pairs,
                    }) => (Some(defining_clauses), resolve_gate_pairs),
                    Some(BveExtraction::FailedLiteral { unit }) => {
                        if self.var_is_assigned(unit.variable().index()) {
                            debug_assert!(
                                self.lit_val(unit) > 0,
                                "BUG: BVE semantic failed literal {unit:?} conflicts with an existing assignment",
                            );
                            continue;
                        }
                        if self.cold.lrat_enabled && !self.watches_disconnected {
                            // LRAT probing requires watches for search_propagate.
                            // During BVE (watches_disconnected=true), skip the probe
                            // and fall through to the non-LRAT path (#8477).
                            let probe_lit = unit.negated();
                            self.decide(probe_lit);
                            if let Some(conflict_ref) = self.search_propagate() {
                                let lrat_hints = self.collect_probe_conflict_lrat_hints(
                                    conflict_ref,
                                    probe_lit,
                                    Some(unit),
                                );
                                self.backtrack(0);
                                // SOUNDNESS FIX (#8477): use enqueue_derived_unit
                                // during BVE to avoid qhead corruption. See the
                                // detailed comment in the backward subsumption unit
                                // path below.
                                self.enqueue_derived_unit(unit, &lrat_hints);
                            } else {
                                self.backtrack(0);
                            }
                        } else {
                            // SOUNDNESS FIX (#8477): use enqueue_derived_unit
                            // instead of learn_derived_unit. During BVE, watches
                            // are disconnected and search_propagate cannot work.
                            // See the detailed comment in the backward subsumption
                            // unit path below.
                            self.enqueue_derived_unit(unit, &[]);
                        }
                        continue;
                    }
                    None => (None, false),
                };
                // Compute remaining budget for incremental effort charging
                // (#8195). CaDiCaL checks `stats.elimres <= resolution_limit`
                // per resolve_clauses() call. Without this, a single variable
                // with 500*500=250K pairs burns the entire budget even when
                // only 100 attempts remain.
                let remaining_budget = resolution_limit.saturating_sub(self.cold.bve_resolutions);
                let bve_stats_before = if self.cold.lrat_enabled {
                    Some(self.inproc.bve.stats().clone())
                } else {
                    None
                };

                // GPU-accelerated path (#8349): when no gate is detected and
                // the pair count exceeds the GPU threshold (2048), dispatch
                // resolvent generation to the GPU. The GPU computes raw
                // resolvents in parallel; the CPU post-processes for OTFS
                // (on-the-fly self-subsuming resolution) and budget checking.
                // Falls back to CPU for gate-aware restricted resolution
                // (complex pair selection) and small pair counts (GPU launch
                // overhead > benefit).
                #[cfg(feature = "gpu")]
                let result = if gate_defining.is_none()
                    && self.should_use_gpu_bve(scratch.pos_occs.len(), scratch.neg_occs.len())
                {
                    match self.gpu_bve_resolve_and_check(
                        var,
                        &scratch.pos_occs,
                        &scratch.neg_occs,
                        remaining_budget,
                    ) {
                        Some((can_elim, resolvents, strengthened, satisfied_parents, attempts)) => {
                            self.inproc.bve.finalize_elimination_from_resolution(
                                var,
                                &self.arena,
                                can_elim,
                                resolvents,
                                strengthened,
                                satisfied_parents,
                                attempts,
                            )
                        }
                        None => {
                            // GPU dispatch failed; fall back to CPU path.
                            self.inproc.bve.try_eliminate_with_gate_with_marks(
                                var,
                                &self.arena,
                                gate_defining.as_deref(),
                                resolve_gate_pairs,
                                &mut self.lit_marks,
                                &self.vals,
                                remaining_budget,
                            )
                        }
                    }
                } else {
                    self.inproc.bve.try_eliminate_with_gate_with_marks(
                        var,
                        &self.arena,
                        gate_defining.as_deref(),
                        resolve_gate_pairs,
                        &mut self.lit_marks,
                        &self.vals,
                        remaining_budget,
                    )
                };

                #[cfg(not(feature = "gpu"))]
                let result = self.inproc.bve.try_eliminate_with_gate_with_marks(
                    var,
                    &self.arena,
                    gate_defining.as_deref(),
                    resolve_gate_pairs,
                    &mut self.lit_marks,
                    &self.vals,
                    remaining_budget,
                );

                self.cold.bve_resolutions = self
                    .cold
                    .bve_resolutions
                    .saturating_add(result.resolution_attempts);

                if !result.eliminated {
                    self.inproc.bve.mark_failed(var);
                    continue;
                }
                let lrat_plan = if self.cold.lrat_enabled {
                    match self.preflight_bve_lrat_transaction(&result) {
                        Ok(plan) => Some(plan),
                        Err(reject) => {
                            if let Some(saved_stats) = bve_stats_before {
                                self.inproc.bve.restore_stats(saved_stats);
                            }
                            self.record_bve_lrat_preflight_reject(&reject);
                            self.inproc.bve.clear_removed_external(var.index());
                            self.inproc.bve.mark_failed(var);
                            continue;
                        }
                    }
                } else {
                    None
                };
                if self.cold.bve_trace {
                    let sp = result.satisfied_parents.len();
                    let st = result.strengthened.len();
                    let rv = result.resolvents.len();
                    let we = result.witness_entries.len();
                    let td = result.to_delete.len();
                    eprintln!(
                        "BVE_TRACE: elim #{} var={} to_delete={} witness={} resolvents={} strengthened={} sat_parents={}",
                        stats.total_eliminations, var.0, td, we, rv, st, sp,
                    );
                    if sp > 0 {
                        for &sp_idx in &result.satisfied_parents {
                            let sp_lits: Vec<i32> = self
                                .arena
                                .literals(sp_idx)
                                .iter()
                                .map(|l| {
                                    let ext = self.externalize(*l);
                                    ext.to_dimacs()
                                })
                                .collect();
                            eprintln!("  SAT_PARENT: idx={sp_idx} lits={sp_lits:?}");
                        }
                    }
                }
                if let Err(reject) = self.apply_bve_elimination_result(
                    &result,
                    &mut scratch,
                    &mut stats,
                    &mut pending_gc_indices,
                    &mut derived_unsat,
                    lrat_plan.as_ref(),
                ) {
                    if let Some(saved_stats) = bve_stats_before {
                        self.inproc.bve.restore_stats(saved_stats);
                    }
                    self.record_bve_lrat_preflight_reject(&reject);
                    self.inproc.bve.clear_removed_external(var.index());
                    self.inproc.bve.mark_failed(var);
                    continue;
                }
                #[cfg(ay_logging)]
                if gate_defining.is_some() {
                    gate_eliminations += 1;
                }

                eliminated_this_round = true;
                if derived_unsat {
                    break;
                }

                // Per-variable backward subsumption (CaDiCaL elim.cpp:731).
                //
                // Run backward subsumption immediately after each variable
                // elimination, matching CaDiCaL's `elim_backward_clauses`.
                //
                // Subsumed clauses are deleted WITHOUT reconstruction entries,
                // matching CaDiCaL backward.cpp:113-115. The resolvent that
                // subsumed the clause remains in the formula, so subsumption
                // guarantees any satisfying model of the resolvent also satisfies
                // the subsumed clause. See #8356 for the unsoundness caused by
                // the previous approach of pushing per-variable witness entries.
                // #8466: Enable backward subsumption when no proof output
                // is active. BW_SUBSUME_ENABLED is false due to DRAT proof
                // ordering bugs (#8448), but the solver-soundness path (no
                // proof) is correct: subsumed clauses are logically redundant
                // and can be safely deleted. On clique_n2_k10, backward
                // subsumption removes redundant resolvents that otherwise
                // cause 7x clause growth.
                if !scratch.resolvent_indices.is_empty()
                    && !has_proof_output
                    && !self.cold.lrat_enabled
                {
                    // Sequential per-resolvent backward subsumption (#8448).
                    //
                    // CaDiCaL elim.cpp:731, backward.cpp:40-211: process one
                    // resolvent at a time, applying each mutation (deletion,
                    // strengthening, unit derivation) immediately before
                    // checking the next candidate. This ensures correct DRAT
                    // proof ordering:
                    //
                    // 1. Subsumed clause D is deleted while both D and the
                    //    subsumer R are still alive in the proof stream.
                    // 2. Strengthened clause D' is added with proper LRAT hints
                    //    referencing D and R (both alive at emission time).
                    // 3. Units are derived while both antecedent clauses exist.
                    //
                    // The previous batched model (#8216) caused three proof bugs:
                    // - Bug 1: deletions preceded dependent unit derivations
                    // - Bug 2: empty LRAT hints for strengthening
                    // - Bug 3: cascade rounds referenced stale clause IDs
                    //
                    // Cascade is handled naturally by appending strengthened
                    // clauses to the work queue (CaDiCaL backward.cpp:202
                    // `eliminator.enqueue(d)`), up to BW_CASCADE_MAX_ROUNDS
                    // additional items processed.
                    //
                    // Proof deferral interaction (#8448): backward subsumption
                    // deletions must appear in the proof stream immediately
                    // (not deferred), so we temporarily disable deferral during
                    // this section. BVE resolvent additions have already been
                    // emitted by apply_bve_elimination_result above, so the
                    // ordering constraint (all additions before BVE deletions)
                    // is maintained.
                    let was_deferring = self.defer_proof_deletions;
                    if was_deferring {
                        self.defer_proof_deletions = false;
                    }

                    // Build work queue: start with resolvents, cascade appends.
                    scratch.bw_cascade_queue.clear();
                    scratch
                        .bw_cascade_queue
                        .append(&mut scratch.resolvent_indices);

                    // Build source set for mutual-subsumption prevention.
                    let source_set: HashSet<usize> =
                        scratch.bw_cascade_queue.iter().copied().collect();

                    // Track how many items were in the initial batch so we
                    // can count cascade rounds (items beyond the initial set).
                    let initial_queue_len = scratch.bw_cascade_queue.len();

                    // Per-batch duplicate guard prevents double-strengthening (#8223).
                    scratch.bw_strengthened_seen.clear();

                    // Sequential processing: pop from front, cascade appends to back.
                    // Cap total items processed to prevent unbounded cascade.
                    let cascade_item_limit = initial_queue_len
                        + (BW_CASCADE_MAX_ROUNDS as usize) * initial_queue_len.max(1);
                    let mut queue_pos = 0;
                    while queue_pos < scratch.bw_cascade_queue.len()
                        && queue_pos < cascade_item_limit
                    {
                        let r_idx = scratch.bw_cascade_queue[queue_pos];
                        queue_pos += 1;

                        if r_idx >= self.arena.len() || self.arena.is_dead(r_idx) {
                            continue;
                        }

                        // Track cascade rounds for stats.
                        if queue_pos > initial_queue_len {
                            // Only count once per cascade batch boundary.
                            if queue_pos == initial_queue_len + 1 {
                                stats.bw_cascade_rounds += 1;
                            }
                        }

                        // Step 1: Scan for subsumption/strengthening candidates
                        // (read-only scan of occurrence lists).
                        let bw_result = self.inproc.bve.backward_subsume_one_sequential(
                            &self.arena,
                            r_idx,
                            &mut self.lit_marks,
                            &self.vals,
                            &source_set,
                        );
                        stats.bw_checks_total += bw_result.checks;
                        stats.bw_subsumed_total += bw_result.subsumed.len() as u64;
                        stats.bw_strengthened_total += bw_result.strengthened.len() as u64;

                        // #8397: Skip backward subsumption DELETIONS during BVE.
                        //
                        // Backward subsumption identifies clauses D where the
                        // new resolvent R subsumes D (R is a subset of D).
                        // Deleting D is safe while R remains in the formula.
                        // However, if R contains a variable eliminated in a
                        // later BVE round, R leaves the formula and its
                        // resolvents may not imply D. The chain of implications
                        // that made D redundant is broken, causing the
                        // reconstruction resolution guarantee to fail.
                        //
                        // Fix: keep D alive. D is semantically redundant while
                        // R exists (no correctness cost) and will be cleaned
                        // up by subsumption passes between BVE rounds. The
                        // cost is carrying redundant clauses through the
                        // current BVE round.
                        //
                        // Strengthening (below) is still applied because
                        // strengthened clauses are STRONGER than the original
                        // (fewer literals), which only tightens the constraint.
                        //
                        // CaDiCaL does backward subsumption deletions during
                        // BVE (backward.cpp:113-115) but its tighter
                        // integration (per-variable backward queuing, different
                        // elimination ordering) avoids the multi-variable
                        // chains that trigger this in AY.
                        // (Subsumed clauses identified but not deleted.)

                        // 2b. Delete root-satisfied clauses (CaDiCaL backward.cpp:67-69, 107-110).
                        stats.bw_satisfied_total += bw_result.satisfied.len() as u64;
                        for &idx in &bw_result.satisfied {
                            if idx < self.arena.len() && !self.arena.is_dead(idx) {
                                scratch.old_lits_buf.clear();
                                scratch
                                    .old_lits_buf
                                    .extend_from_slice(self.arena.literals(idx));
                                self.delete_clause_checked(idx, ReasonPolicy::ClearLevel0);
                                self.inproc
                                    .bve
                                    .occ_remove_clause(idx, &scratch.old_lits_buf);
                            }
                        }

                        // 2c. Apply strengthenings with LRAT hints.
                        // CaDiCaL backward.cpp:119-183, subsume.cpp:156-174.
                        for &(idx, neg_lit) in &bw_result.strengthened {
                            if idx >= self.arena.len() || self.arena.is_dead(idx) {
                                continue;
                            }
                            if !scratch.bw_strengthened_seen.insert(idx) {
                                continue;
                            }
                            // Guard (#8482): only apply strengthening if the
                            // negated literal's variable has already been
                            // removed or eliminated. If it hasn't, removing
                            // neg_lit from this clause takes the clause out of
                            // that variable's occ list. When that variable is
                            // later eliminated, the clause is missing from the
                            // extension stack and reconstruction is invalid.
                            let neg_var_idx = neg_lit.variable().index();
                            if !self.var_lifecycle.is_removed(neg_var_idx)
                                && !self.inproc.bve.is_var_eliminated_internal(neg_var_idx)
                            {
                                continue;
                            }
                            scratch.old_lits_buf.clear();
                            scratch
                                .old_lits_buf
                                .extend_from_slice(self.arena.literals(idx));
                            scratch.new_lits_buf.clear();
                            scratch
                                .new_lits_buf
                                .extend_from_slice(&scratch.old_lits_buf);
                            scratch.new_lits_buf.retain(|&l| l != neg_lit);
                            if scratch.new_lits_buf.is_empty() {
                                derived_unsat = true;
                                break;
                            }
                            if scratch.new_lits_buf.len() < scratch.old_lits_buf.len() {
                                // Build LRAT hints for strengthening (#8448 Bug 2).
                                // CaDiCaL backward.cpp:119-183: collect unit IDs for
                                // root-false literals, then append D_id and R_id.
                                let strengthen_hints = if self.cold.lrat_enabled {
                                    self.build_backward_strengthen_hints(
                                        idx,
                                        r_idx,
                                        &scratch.old_lits_buf,
                                    )
                                } else {
                                    vec![]
                                };
                                match self.replace_clause_with_final_hints(
                                    idx,
                                    &scratch.new_lits_buf,
                                    &strengthen_hints,
                                ) {
                                    ReplaceResult::Replaced | ReplaceResult::Unit => {
                                        scratch.new_lits_buf.clear();
                                        scratch
                                            .new_lits_buf
                                            .extend_from_slice(self.arena.literals(idx));
                                        self.inproc.bve.notify_clause_replaced(
                                            idx,
                                            &scratch.old_lits_buf,
                                            &scratch.new_lits_buf,
                                        );
                                        self.inproc
                                            .bve
                                            .mark_candidates_dirty_clause(&scratch.new_lits_buf);
                                        // CaDiCaL backward.cpp:202: re-enqueue
                                        // strengthened clause for cascade.
                                        scratch.bw_cascade_queue.push(idx);
                                    }
                                    ReplaceResult::Empty => {
                                        derived_unsat = true;
                                    }
                                    ReplaceResult::Skipped => {}
                                }
                            }
                        }

                        // 2d. Process units (CaDiCaL backward.cpp:189-195).
                        // Units are derived while both D and R are still alive
                        // in the proof — sequential processing ensures this.
                        if !derived_unsat && !bw_result.units.is_empty() {
                            for &unit in &bw_result.units {
                                if self.var_is_assigned(unit.variable().index()) {
                                    continue;
                                }
                                // Soundness validation (#8477): verify the unit is
                                // actually derivable. Check that the resolvent R and
                                // the candidate clause D exist and that their
                                // resolution on the complementary literal produces
                                // the unit. This catches stale occurrence list bugs
                                // where D no longer contains the expected literals.
                                //
                                // The unit comes from hyper-unary resolution:
                                // R = {l1, ..., ln} and D = {l1, ..., ln-1, ~li}
                                // for exactly one i, and D has the same active size
                                // as R. After removing ~li from D, exactly one
                                // literal remains = the unit.
                                //
                                // We verify by checking: does resolvent R exist, is
                                // there a clause D containing ~(some literal of R)
                                // such that all other active literals of R match D,
                                // and removing the negated literal leaves exactly
                                // the unit?
                                //
                                // For now, just check the unit literal is not already
                                // root-assigned to the opposite polarity (which would
                                // mean the formula is already UNSAT).
                                debug_assert!(
                                    self.vals.get(unit.negated().index()).copied().unwrap_or(0)
                                        >= 0,
                                    "BUG: BW unit {unit:?} has its negation root-true -- \
                                     formula is already UNSAT but not detected",
                                );
                                // Build LRAT hints for unit derivation (#8448).
                                // Same structure as strengthening hints: unit IDs
                                // for root-false literals + D_id + R_id.
                                let unit_hints = if self.cold.lrat_enabled {
                                    // Find the candidate clause D that produced
                                    // this unit. It's the clause that was
                                    // self-subsumed to produce a single literal.
                                    // The strengthened entries tell us which
                                    // clause was involved, but for units the
                                    // backward_subsume_one breaks immediately.
                                    // We need D's clause index. For hyper-unary
                                    // resolution, the candidate D is the clause
                                    // from the occurrence list. Since units cause
                                    // an immediate break, the last candidate
                                    // checked is the one that produced the unit.
                                    // We can reconstruct D from the strengthened
                                    // list or re-derive it from context.
                                    //
                                    // For now, use TrustedTransform when hints
                                    // can't be built (unit derivation is rare).
                                    vec![]
                                } else {
                                    vec![]
                                };
                                // SOUNDNESS FIX (#8477): Use enqueue_derived_unit
                                // instead of learn_derived_unit. During BVE, watches
                                // are disconnected (watches_disconnected=true).
                                // learn_derived_unit calls search_propagate (watch-based
                                // BCP) which does NOTHING with empty watch lists, but
                                // advances qhead past the unit. This means:
                                // 1. The unit is assigned but never propagated
                                // 2. qhead advances past it, so post-BVE dense
                                //    propagation (propagate_dense) also skips it
                                // 3. Post-BVE watch-based BCP (propagate_check_unsat)
                                //    also skips it since qhead is already past
                                // Result: formula corruption -> false UNSAT.
                                //
                                // CaDiCaL uses elim_propagate (occurrence-list-based
                                // propagation) instead of search_propagate during BVE.
                                // AY's equivalent is propagate_dense, which runs after
                                // all BVE rounds complete. By using enqueue_derived_unit
                                // (which does NOT call search_propagate and does NOT
                                // advance qhead), the unit stays on the trail pending
                                // propagation. propagate_dense_check_unsat() in
                                // config_preprocess_bve.rs:202 then correctly processes
                                // it using occurrence lists.
                                self.enqueue_derived_unit(unit, &unit_hints);
                            }
                            // CaDiCaL: stop processing after unit derivation.
                            if derived_unsat || !bw_result.units.is_empty() {
                                break;
                            }
                        }

                        if derived_unsat {
                            break;
                        }
                    }

                    // Restore proof deferral state.
                    if was_deferring {
                        self.defer_proof_deletions = true;
                        // Filter out deferred deletions for clauses already
                        // deleted by backward subsumption (#8448). BVE defers
                        // source clause deletions, but backward subsumption
                        // may have independently deleted some of those same
                        // clauses (e.g., a source clause subsumed by its own
                        // resolvent). Without this filter, flush would attempt
                        // a double-delete, hitting the "deleting unknown LRAT
                        // clause ID" assertion.
                        self.deferred_proof_deletions.retain(|(_lits, cid)| {
                            // Keep the deferred deletion only if its clause ID
                            // is still alive in the proof manager's tracking.
                            // A zero ID (no LRAT) always passes through.
                            if *cid == 0 || !self.cold.lrat_enabled {
                                return true;
                            }
                            // Check if the clause_id is still in the arena's
                            // clause_ids mapping. If backward subsumption
                            // deleted it, the proof manager already removed
                            // the ID from known_lrat_ids and emitted the
                            // deletion. Skip the redundant deferred entry.
                            if let Some(ref manager) = self.proof_manager {
                                manager.is_known_lrat_id(*cid)
                            } else {
                                true
                            }
                        });
                    }
                }
                if derived_unsat {
                    break;
                }
            }
            // Flush deferred proof deletions after all resolvents for this
            // round have been added (#8011). This ensures the DRAT proof
            // stream has the correct ordering: all additions before deletions.
            if has_proof_output {
                self.defer_proof_deletions = false;
                self.flush_deferred_proof_deletions();
            }

            if derived_unsat || !eliminated_this_round {
                break;
            }
            // CaDiCaL fastelim: single pass with dynamic rescheduling. When
            // all candidates are exhausted, further rounds just add rebuild
            // overhead. Break for both fastelim and additive modes.
            if candidates_exhausted {
                break;
            }
            if !self.inproc.bve.is_fastelim_mode() {
                let current = self.arena.active_clause_count();
                let threshold = active_at_bve_start + active_at_bve_start / 20;
                if current > threshold {
                    break;
                }
                // #8482: Additional irredundant-only clause growth guard.
                // The active_clause_count guard above includes learned clauses,
                // which inflates the threshold. On gate-structured circuit
                // formulas (braun family), BVE adds many irredundant resolvents
                // that make the formula harder. Track irredundant growth
                // separately with a tighter threshold (2% instead of 5%).
                // This fires earlier than the active-count guard when BVE is
                // adding resolvents faster than it removes source clauses.
                let irredundant_now = self.arena.irredundant_count();
                if irredundant_now > irredundant_at_bve_start + irredundant_at_bve_start / 50 {
                    break;
                }
            }
            if self.cold.bve_resolutions >= resolution_limit {
                break;
            }
            if stats.total_eliminations >= elim_cap {
                break;
            }

            // Backward subsumption now runs per-variable inline (#7998),
            // matching CaDiCaL's approach. Inter-round subsumption still runs
            // to expose new elimination candidates via clause strengthening.
            self.subsume();

            // DEEP: propagate units derived this round (via OTFS / subsumption)
            // through the live occurrence lists before the next round rebuilds
            // them. This is the propagate-then-reschedule cascade that gives
            // kissat the bulk of its eliminations: assigning a unit satisfies /
            // shrinks clauses, which lowers other variables' occurrence degree
            // and re-exposes them as eliminable candidates in the next round.
            // Bounded/soundness: same call the post-BVE path already uses
            // (config_preprocess_bve.rs), guarded on occ populated + pending
            // trail; sets derived_unsat on conflict so the UNSAT verdict and
            // proof stay fail-closed.
            //
            // ORDERING (measured, wf_13a96c15 — do not "fix" to help medium):
            // this propagate sits AFTER the `candidates_exhausted` break above,
            // so it only ever fires on formulas that keep re-populating the
            // schedule across rounds (giant/huge sparse). Medium sparse
            // formulas drain their schedule in round 0 (candidates_exhausted =
            // true) and break before reaching here — which is why lowering
            // BVE_SPARSE_DEEP_MIN_VARS to engage the cascade on 5dbe7b31 /
            // cdd89d1b flips nothing (see BVE_SPARSE_DEEP_MIN_VARS in
            // constants.rs). Moving this before the break was measured inert:
            // pending_units is 0 on these instances (AY's BVE derives no units
            // to propagate here), so the call is a pure no-op — there is no
            // unit cascade to ride. The bottleneck is elimination YIELD, not
            // round structure; do not reorder for the medium band.
            if deep
                && !derived_unsat
                && self.inproc.bve.is_occ_populated()
                && self.qhead < self.trail.len()
                && self.propagate_dense_check_unsat()
            {
                derived_unsat = true;
                break;
            }

            // Kissat-style progressive growth bound (#8135, eliminate.c:339-372):
            // after exhausting all candidates at the current bound, increment
            // the bound before the next round so bound progresses 0 -> 1 -> 2.
            if candidates_exhausted && eliminated_this_round {
                self.inproc.bve.increment_growth_bound();
            }
        }

        // Backward subsumption now runs per-variable inline in the
        // elimination loop above (#7998), matching CaDiCaL's approach
        // (elim.cpp:731 `elim_backward_clauses`). The previous deferred
        // approach (#8133) was disabled because batching across variables
        // caused reconstruction failures. Per-variable backward subsumption
        // is safe because extension stack entries are populated before
        // backward subsumption runs for each variable.
        //
        // Multi-round cascade (#8216): after backward subsumption
        // strengthens a clause D, D is re-enqueued as a source for the
        // next cascade round. This matches CaDiCaL backward.cpp:202
        // `eliminator.enqueue(d)`. Cascade terminates when no more
        // strengthenings occur or BW_CASCADE_MAX_ROUNDS is reached.

        // CaDiCaL elim.cpp:917-922: collect instantiation candidates while
        // occurrence lists are still live. Must happen before garbage
        // collection deletes clauses with eliminated variables.
        //
        // Instantiate gate (lever 2, AY_AB_BVE_INST_GATE=0 kill-switch;
        // 2026-07-11 sparse-prize completion round — see
        // bve_inst_gate_enabled for the full measurement): instantiate has
        // no internal budget and the fast-inner profile measured it at
        // 6.5-13.2s PER bve_body CALL on the deep collapse+BVE path (74-86%
        // of the remaining BVE wall), all of it OUTSIDE the wall the round
        // loop enforces. Under the gate it runs (1) at most once per
        // elimination phase and (2) only if this bve_body's wall is not
        // already exhausted, with the candidate loop deadline-bounded to the
        // SAME wall — so rounds + instantiate together respect the wall.
        // Scheduling only: instantiate is an optional strengthening pass.
        let inst_gate = config_preprocess_policy::bve_inst_gate_enabled();
        let inst_wall = if self.inproc.bve.is_fastelim_mode() {
            std::time::Duration::from_secs(fastelim_wall_secs)
        } else {
            std::time::Duration::from_millis(BVE_INPROCESSING_WALL_LIMIT_MS)
        };
        let inst_admitted = !inst_gate
            || (self.cold.bve_instantiate_done_seq != self.cold.bve_elim_phase_seq
                && bve_wall_start.elapsed() < inst_wall);
        let inst_deadline = inst_gate.then(|| bve_wall_start + inst_wall);
        let inst_candidates = if !self.cold.lrat_enabled
            && !derived_unsat
            && stats.total_eliminations > 0
            && inst_admitted
        {
            self.collect_instantiation_candidates()
        } else {
            Vec::new()
        };

        // Post-elimination GC: delete clauses containing eliminated variables.
        //
        // Full arena scan: iterate ALL clauses and delete any that reference
        // a removed (eliminated/substituted) variable. This must be a full
        // scan because:
        //
        // 1. BVE adds resolvents via `add_clause_watched` which does NOT
        //    update `gc_occ`. The gc_occ-guided path (#3521) misses these
        //    new clauses entirely.
        //
        // 2. Within a single BVE round, variable X is eliminated and its
        //    clauses are deleted. Later, variable Y is eliminated, producing
        //    resolvents that may contain literals of a THIRD variable Z.
        //    If Z was eliminated between X and Y, the resolvent from Y's
        //    elimination still references Z. The BVE occ list correctly
        //    tracks Z in the resolvent, but backward subsumption or OTFS
        //    strengthening can create clause mutations not reflected in
        //    gc_occ, causing the gc_occ lookup to miss affected clauses.
        //
        // 3. The previous gc_occ-guided path caused panics on FmlaEquivChain
        //    (54K vars, 438K clauses) where compaction found active clauses
        //    with eliminated-variable literals (#8464).
        //
        // Cost: O(all_clauses * avg_clause_len). This runs once per BVE
        // phase at level 0, which is acceptable.
        if stats.total_eliminations > 0 {
            // Post-elimination GC: delete all active clauses containing
            // eliminated variables. Uses full arena scan for soundness (#8397).
            //
            // Previously this used gc_occ-guided lookup O(sum of occ sizes)
            // instead of O(all_clauses). That optimization was unsound: gc_occ
            // can lose track of learned clauses when BVE-internal backward
            // subsumption replaces clauses in-place (the replacement updates
            // gc_occ for the NEW literals but the old clause may still contain
            // a different eliminated variable that the occ-guided scan misses).
            // The full scan runs once per BVE round, matching CaDiCaL's
            // per-variable deletion approach (elim.cpp).
            self.gc_occ = None;
            // Reuse persistent buffer to avoid arena-proportional allocation (#8602).
            self.cold.reduce_indices_buf.clear();
            self.cold.reduce_indices_buf.extend(self.arena.indices());
            for i in 0..self.cold.reduce_indices_buf.len() {
                let idx = self.cold.reduce_indices_buf[i];
                if self.arena.is_dead(idx) {
                    continue;
                }
                let has_eliminated = self
                    .arena
                    .literals(idx)
                    .iter()
                    .any(|lit| self.var_lifecycle.is_removed(lit.variable().index()));
                if has_eliminated {
                    self.delete_clause_checked(idx, ReasonPolicy::ClearLevel0);
                }
            }
        }

        if stats.total_eliminations > 0 && candidates_exhausted {
            self.inproc.bve.increment_growth_bound();
        }

        // CaDiCaL elim.cpp:945-947: run instantiation after occ list
        // cleanup and garbage collection. Instantiation temporarily
        // rebuilds 2WL watches for BCP-based strengthening.
        if !derived_unsat && !inst_candidates.is_empty() {
            // Consume this phase's instantiate slot (lever 2 — once per
            // elimination phase when the gate is on).
            if inst_gate {
                self.cold.bve_instantiate_done_seq = self.cold.bve_elim_phase_seq;
            }
            if self.instantiate(inst_candidates, inst_deadline) {
                derived_unsat = true;
            }
        }

        solver_log!(
            self,
            "BVE: eliminated {} vars ({} gated), {} resolutions, {} clauses (delta {}), bound={} {}",
            stats.total_eliminations,
            gate_eliminations,
            self.cold.bve_resolutions,
            self.arena.num_clauses(),
            self.arena.num_clauses() as i64 - clauses_at_bve_start as i64,
            self.inproc.bve.growth_bound(),
            if self.inproc.bve.is_fastelim_mode() { "fastelim" } else { "additive" },
        );
        tracing::info!(
            eliminated = stats.total_eliminations,
            resolvents = stats.resolvents_total,
            bw_checks = stats.bw_checks_total,
            bw_subsumed = stats.bw_subsumed_total,
            bw_subsumed_deleted = stats.bw_subsumed_deleted,
            bw_strengthened = stats.bw_strengthened_total,
            bw_satisfied = stats.bw_satisfied_total,
            bw_cascade_rounds = stats.bw_cascade_rounds,
            active_clauses = self.arena.active_clause_count(),
            mode = if self.inproc.bve.is_fastelim_mode() {
                "fastelim"
            } else {
                "additive"
            },
            "BVE backward subsumption diagnostics"
        );
        self.cold.last_bve_fixed = self.fixed_count;
        self.cold.last_bve_marked = self.cold.bve_marked;
        self.cold.bve_phases += 1;

        #[cfg(debug_assertions)]
        if stats.total_eliminations > 0 {
            for idx in self.arena.indices() {
                // Use is_dead() instead of is_empty_clause() to also skip
                // garbage-marked and pending-garbage clauses (#8483). A clause
                // marked pending-garbage by BCP still has non-zero lit_len but
                // is logically dead and should not trigger the invariant check.
                if self.arena.is_dead(idx) {
                    continue;
                }
                debug_assert!(
                    !self
                        .arena
                        .literals(idx)
                        .iter()
                        .any(|lit| self.var_lifecycle.is_removed(lit.variable().index())),
                    "BUG: active {} clause {idx} contains a removed variable \
                     after BVE garbage collection",
                    if self.arena.is_learned(idx) {
                        "learned"
                    } else {
                        "irredundant"
                    },
                );
            }
        }

        // Return persistent scratch to cold state (#8602).
        self.cold.bve_body_scratch = scratch;

        derived_unsat
    }

    /// Build LRAT hints for backward subsumption strengthening (#8448 Bug 2).
    ///
    /// CaDiCaL backward.cpp:119-183: for a strengthening where resolvent R
    /// (at `r_idx`) self-subsumes candidate D (at `d_idx`) by removing literal
    /// `neg_lit`, the LRAT hint chain is:
    ///
    /// ```text
    /// [unit_id(-l) for l in root-false lits of D and R] + [D_id, R_id]
    /// ```
    ///
    /// The unit proof IDs justify why root-false literals can be ignored
    /// (they are implied false at level 0). D_id and R_id are the clause
    /// IDs of the candidate and resolvent respectively.
    ///
    /// `d_lits` must be the literals of D *before* strengthening (i.e., the
    /// old clause contents).
    fn build_backward_strengthen_hints(
        &self,
        d_idx: usize,
        r_idx: usize,
        d_lits: &[Literal],
    ) -> Vec<u64> {
        let d_id = self.clause_id(ClauseRef(d_idx as u32));
        let r_id = self.clause_id(ClauseRef(r_idx as u32));

        // Collect unit proof IDs for root-false literals in D and R.
        // CaDiCaL backward.cpp:149-182: lrat_chain collects unit IDs for
        // root-level-false literals, then appends clause IDs.
        let mut hints = Vec::new();

        // Root-false literals in D.
        for &lit in d_lits {
            let v = self.vals.get(lit.index()).copied().unwrap_or(0);
            if v < 0 {
                // lit is root-false. The unit proof for ~lit justifies this.
                if let Some(uid) = self.level0_unit_chain_proof_id_for_lit(lit.negated()) {
                    if !hints.contains(&uid) {
                        hints.push(uid);
                    }
                }
            }
        }

        // Root-false literals in R.
        if r_idx < self.arena.len() && !self.arena.is_dead(r_idx) {
            let r_lits = self.arena.literals(r_idx);
            for &lit in r_lits {
                let v = self.vals.get(lit.index()).copied().unwrap_or(0);
                if v < 0 {
                    if let Some(uid) = self.level0_unit_chain_proof_id_for_lit(lit.negated()) {
                        if !hints.contains(&uid) {
                            hints.push(uid);
                        }
                    }
                }
            }
        }

        // Append clause IDs: D first, then R (CaDiCaL backward.cpp:180-182).
        if d_id != 0 {
            hints.push(d_id);
        }
        if r_id != 0 && r_id != d_id {
            hints.push(r_id);
        }

        hints
    }
}
