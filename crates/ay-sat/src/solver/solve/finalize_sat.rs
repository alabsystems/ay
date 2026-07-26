// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT model finalization, verification, and result shaping.
//!
//! Hosts `finalize_sat_model` (reconstruction + original-formula verification)
//! and the `declare_sat_*` / `declare_unknown_*` API methods.

use super::super::*;
use crate::solver_log::solver_log;

impl Solver {
    // debug_assert_sat_result_model REMOVED (#9200): This function read from
    // self.vals (via get_model()) which is stale when walk/ProbSAT finds SAT.
    // Walk stores its solution in phases (get_model_from_phases), not in vals.
    // The always-on finalize_sat_model verification (unit clause check, original
    // formula verification) plus the verify_external_model debug_assert provide
    // complete coverage without the vals-vs-phases confusion.

    /// Finalize SAT model: reconstruct, verify, and truncate
    ///
    /// This method centralizes SAT model finalization to ensure all SAT returns
    /// go through verification. All SAT return sites MUST use this method.
    ///
    /// # Invariants enforced
    ///
    /// 1. **Reconstruction**: Variables eliminated by BVE/sweeping are restored
    ///    to values consistent with the original formula.
    /// 2. **Verification**: always-on SAT contract validates the model satisfies
    ///    ALL clauses (including internal selector variables for incremental solving).
    /// 3. **Truncation**: Internal variables are removed; only user-visible
    ///    variables (0..user_num_vars) are returned.
    ///
    /// Returns `Err(detail)` if model verification fails after reconstruction.
    pub(in crate::solver) fn finalize_sat_model(
        &self,
        model: Vec<bool>,
    ) -> Result<Vec<bool>, String> {
        tracing::debug!(
            num_vars = self.num_vars,
            user_num_vars = self.user_num_vars,
            reconstruction_len = self.inproc.reconstruction.len(),
            original_clauses = self.cold.original_ledger.num_clauses(),
            has_scopes = !self.cold.scope_selectors.is_empty(),
            "finalize_sat_model: entry"
        );

        // BVE soundness investigation (#8397, #8482, #8485): find clauses
        // unsatisfied in the internal model to diagnose the root cause.
        // #8577: Skip when domain restriction is active — non-domain
        // variables are don't-cares and will produce false unsatisfied counts.
        #[cfg(debug_assertions)]
        if self.active_domain.is_none() {
            let mut unsatisfied_count = 0u32;
            for ci in self.arena.active_indices() {
                if self.arena.len_of(ci) < 2
                    || self.arena.is_garbage(ci)
                    || self.arena.is_pending_garbage(ci)
                {
                    continue;
                }
                let int_lits = self.arena.literals(ci);
                let satisfied_internal = int_lits.iter().any(|&ilit| {
                    let vi = ilit.variable().index();
                    if vi < model.len() {
                        let val = model[vi];
                        if ilit.is_positive() {
                            val
                        } else {
                            !val
                        }
                    } else {
                        false
                    }
                });
                if !satisfied_internal {
                    unsatisfied_count += 1;
                    if unsatisfied_count <= 3 {
                        let per_lit: Vec<String> =
                            int_lits
                                .iter()
                                .map(|&ilit| {
                                    let vi = ilit.variable().index();
                                    let model_val = if vi < model.len() {
                                        Some(model[vi])
                                    } else {
                                        None
                                    };
                                    // vals is indexed by LITERAL index, not variable index.
                                    // Positive literal of var v is at vals[2*v], negative at vals[2*v+1].
                                    let lit_val = if ilit.index() < self.vals.len() {
                                        self.vals[ilit.index()]
                                    } else {
                                        0
                                    };
                                    let pos_lit_val = if vi * 2 < self.vals.len() {
                                        self.vals[vi * 2]
                                    } else {
                                        0
                                    };
                                    let ext_var = if vi < self.cold.i2e.len() {
                                        self.cold.i2e[vi] as usize
                                    } else {
                                        999999
                                    };
                                    format!(
                                "int_v{}(pos={},model={:?},lit_val={},pos_lit_val={},ext_v{})",
                                vi, ilit.is_positive(), model_val, lit_val, pos_lit_val, ext_var,
                            )
                                })
                                .collect();
                        eprintln!(
                            "INTERNAL_UNSAT: arena[{}] lits=[{}] learned={} details=[{}]",
                            ci,
                            int_lits
                                .iter()
                                .map(|l| format!("{}", l.to_dimacs()))
                                .collect::<Vec<_>>()
                                .join(", "),
                            self.arena.is_learned(ci),
                            per_lit.join(", "),
                        );
                    }
                }
            }
            if unsatisfied_count > 0 {
                eprintln!(
                    "INTERNAL_MODEL_CHECK: {unsatisfied_count} clauses unsatisfied in internal model",
                );
            }
        }

        // Pre-reconstruction: verify internal model against clause_db.
        // Log a warning but do NOT abort early — the authoritative
        // verification against original clauses happens later in this
        // function and produces a more specific error message with
        // the failing clause index. Aborting here would short-circuit
        // the fail-closed path that callers rely on (#9148).
        // #8577: Skip when domain restriction is active — non-domain
        // variables are don't-cares and may not satisfy non-domain clauses.
        #[cfg(debug_assertions)]
        if self.active_domain.is_none() && !self.verify_clause_db_only(&model, false) {
            tracing::warn!(
                "finalize_sat_model: internal model does not satisfy clause_db \
                 before reconstruction — continuing to original-clause verification"
            );
        }

        // #5012 Family C: validate reconstruction stack before applying it.
        #[cfg(debug_assertions)]
        self.validate_reconstruction_stack();

        // #7917: Early unit-clause check. Original unit clauses must be
        // satisfied by the internal model *before* reconstruction. Unit
        // clauses cannot be affected by BVE reconstruction (they have no
        // eliminated variables to restore), so a violation here indicates
        // a core CDCL or preprocessing bug, not a reconstruction issue.
        // This check runs in O(unit_clauses) and provides a precise
        // diagnostic that distinguishes core-solver bugs from reconstruction
        // bugs.
        {
            for (ci, clause) in self.cold.original_ledger.iter_clauses().enumerate() {
                if clause.len() != 1 {
                    continue;
                }
                let lit = clause[0];
                let vi = lit.variable().index();
                // Map external variable to internal for pre-reconstruction check.
                if vi < self.cold.e2i.len() {
                    let int_var = self.cold.e2i[vi];
                    if int_var != compact::UNMAPPED {
                        let int_var = int_var as usize;
                        if int_var < model.len() {
                            let model_val = model[int_var];
                            let expected = lit.is_positive();
                            if model_val != expected {
                                let detail =
                                    format!(
                                    "BUG: original unit clause {} (ext_var{}, pos={}) violated \
                                     by internal model BEFORE reconstruction — core solver or \
                                     preprocessing bug, not reconstruction. int_var={}, \
                                     model_val={}, clause_index={}",
                                    lit.to_dimacs(), vi, expected, int_var, model_val, ci,
                                );
                                tracing::error!(detail = detail.as_str(), "unit clause violation");
                                return Err(detail);
                            }
                        }
                    }
                }
            }
        }

        // Under active scopes, skip reconstruction. Reconstruction entries from
        // base-formula preprocessing (GBCE/BVE) may flip variables that violate
        // scoped constraints. The model already satisfies all non-deleted clauses
        // (verified above). After pop(), the no-assumptions path re-applies
        // reconstruction correctly for the base formula.
        if self.cold.scope_selectors.is_empty() {
            // Build external model from internal assignments via e2i (#5250).
            // Reference: CaDiCaL extend.cpp:134-144.
            //
            // CRITICAL (#8078): Read from the `model` parameter, NOT from
            // `self.vals`. The model parameter is the authoritative internal
            // assignment. When walk/ProbSAT finds SAT, the solution is stored
            // in phases (get_model_from_phases), and self.vals may not reflect
            // the walk result. Building ext_model from self.vals in that case
            // produces incorrect values, causing original-formula verification
            // to fail and the solver to return Unknown instead of SAT.
            let ext_num_vars = self.cold.e2i.len();
            let mut ext_model = vec![false; ext_num_vars];
            for (ext_var, val) in ext_model.iter_mut().enumerate() {
                let int_var = self.cold.e2i[ext_var];
                if int_var == compact::UNMAPPED {
                    // Variable was eliminated and compacted away. Use the
                    // level-0 value saved during compaction. CaDiCaL preserves
                    // eliminated variables' vals across compaction (extend.cpp:140
                    // reads `internal->val(ilit)` even for eliminated variables).
                    // AY's compaction truncates vals, so we read from the saved
                    // external-space copy instead. (#8179)
                    if ext_var < self.cold.eliminated_ext_vals.len() {
                        *val = self.cold.eliminated_ext_vals[ext_var];
                    }
                    continue;
                }
                let int_var = int_var as usize;
                if int_var < model.len() {
                    // Read from the model parameter — the authoritative internal
                    // assignment passed by the caller. This works for both
                    // get_model() (vals-based) and get_model_from_phases()
                    // (walk-based) call paths.
                    *val = model[int_var];
                }
            }

            // (#8356) Pre-reconstruction diagnostic: verify that the external
            // model satisfies all active clause-DB clauses mapped to external
            // space. If any fail, the external model construction is wrong
            // (not the reconstruction algorithm). This check catches bugs in
            // e2i/i2e mapping and eliminated_ext_vals initialization.
            // #8577: Skip when domain restriction is active — non-domain
            // clauses are not guaranteed to be satisfied.
            #[cfg(debug_assertions)]
            if self.active_domain.is_none() {
                let mut ext_clause_fails = 0u32;
                for idx in self.arena.active_indices() {
                    // Garbage-kept husks (mark_garbage_keep_data) are deleted
                    // from the live formula but still pass active_indices();
                    // reporting them here is a red herring (diagnostic
                    // accuracy only — this block gates nothing; the real
                    // model gate is the original-ledger check below).
                    if self.arena.is_garbage_any(idx) {
                        continue;
                    }
                    let int_lits = self.arena.literals(idx);
                    let satisfied = int_lits.iter().any(|&ilit| {
                        let int_var = ilit.variable().index();
                        if int_var >= self.cold.i2e.len() {
                            return false;
                        }
                        let ext_var = self.cold.i2e[int_var] as usize;
                        if ext_var >= ext_model.len() {
                            return false;
                        }
                        let ext_val = ext_model[ext_var];
                        if ilit.is_positive() {
                            ext_val
                        } else {
                            !ext_val
                        }
                    });
                    if !satisfied && ext_clause_fails < 5 {
                        let ext_lits: Vec<i32> = int_lits
                            .iter()
                            .map(|&ilit| {
                                let int_var = ilit.variable().index();
                                let ext_var = if int_var < self.cold.i2e.len() {
                                    self.cold.i2e[int_var] as usize
                                } else {
                                    999999
                                };

                                (ext_var as i32 + 1) * if ilit.is_positive() { 1 } else { -1 }
                            })
                            .collect();
                        let ext_vals: Vec<bool> = int_lits
                            .iter()
                            .map(|&ilit| {
                                let int_var = ilit.variable().index();
                                let ext_var = if int_var < self.cold.i2e.len() {
                                    self.cold.i2e[int_var] as usize
                                } else {
                                    0
                                };
                                if ext_var < ext_model.len() {
                                    ext_model[ext_var]
                                } else {
                                    false
                                }
                            })
                            .collect();
                        // Watch diagnostic for unsatisfied clauses (#8485).
                        // vals is indexed by LITERAL index (2*var + polarity),
                        // not by variable index. Use ilit.index() to read the
                        // correct entry.
                        let int_vals: Vec<i8> = int_lits
                            .iter()
                            .map(|&ilit| {
                                if ilit.index() < self.vals.len() {
                                    self.vals[ilit.index()]
                                } else {
                                    0
                                }
                            })
                            .collect();
                        let clause_len = self.arena.len_of(idx);
                        let (has_w0, has_w1, w0_dimacs, w1_dimacs) = if clause_len >= 2 {
                            let (w0, w1) = self.arena.watched_literals(idx);
                            let cref = ClauseRef(idx as u32);
                            let hw0 = (0..self.watches.get_watches(w0).len())
                                .any(|i| self.watches.get_watches(w0).clause_ref(i) == cref);
                            let hw1 = (0..self.watches.get_watches(w1).len())
                                .any(|i| self.watches.get_watches(w1).clause_ref(i) == cref);
                            (hw0, hw1, w0.to_dimacs(), w1.to_dimacs())
                        } else {
                            (false, false, 0i32, 0i32)
                        };
                        let any_var_removed = int_lits
                            .iter()
                            .any(|&ilit| self.var_lifecycle.is_removed(ilit.variable().index()));
                        eprintln!(
                            "PRE_RECON_CLAUSEDB_FAIL: arena[{idx}] ext_lits={ext_lits:?} \
                             ext_vals={ext_vals:?} int_vals={int_vals:?} learned={} \
                             watch0={w0_dimacs}(ok={has_w0}) watch1={w1_dimacs}(ok={has_w1}) \
                             any_var_removed={any_var_removed}",
                            self.arena.is_learned(idx),
                        );
                        ext_clause_fails += 1;
                    }
                }
                if ext_clause_fails > 0 {
                    eprintln!(
                        "PRE_RECON_CLAUSEDB_FAIL: {ext_clause_fails} clause-DB clauses \
                         unsatisfied in external model before reconstruction"
                    );
                }
            }

            let ext_model_before = ext_model.clone();

            // Apply reconstruction (external index space, #5250).
            let reconstruction = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                self.inproc.reconstruction.reconstruct(&mut ext_model);
            }));
            if let Err(payload) = reconstruction {
                let detail = if let Some(s) = payload.downcast_ref::<&str>() {
                    (*s).to_owned()
                } else if let Some(s) = payload.downcast_ref::<String>() {
                    s.clone()
                } else {
                    "non-string panic payload".to_owned()
                };
                return Err(format!("reconstruction panic: {detail}"));
            }

            // Log reconstruction impact for diagnostics (#7917).
            let vars_changed = ext_model
                .iter()
                .zip(ext_model_before.iter())
                .filter(|(a, b)| a != b)
                .count();
            tracing::debug!(
                vars_changed,
                ext_num_vars,
                reconstruction_len = self.inproc.reconstruction.len(),
                "finalize_sat_model: reconstruction complete"
            );

            // #3477: Verify sweep equivalences hold in the reconstructed model.
            // After reconstruction, every variable merged by sweep/congruence must
            // have a truth value consistent with its representative. A violation
            // here indicates a bug in reconstruct_sweep() or in the equivalence
            // detection that produced the lit_map.
            #[cfg(debug_assertions)]
            if let Some((step_idx, var_idx, expected, actual)) = self
                .inproc
                .reconstruction
                .verify_sweep_consistency(&ext_model)
            {
                debug_assert!(
                    false,
                    "BUG [#3477]: sweep equivalence violated after reconstruction: \
                     step={step_idx}, var={var_idx}, expected={expected}, actual={actual}"
                );
            }

            // Repair pass REMOVED (#6892): The greedy repair pass introduced in
            // #5522 would iterate original clauses and flip eliminated variables
            // to satisfy unsatisfied clauses. This caused oscillation — flipping
            // a variable for one clause would break a clause that reconstruction
            // had correctly satisfied. On crn_11_99_u (UNSAT), reconstruction
            // correctly set var287=true via its witness entry, but the repair
            // pass flipped it back to false for an earlier clause containing
            // ¬287, creating an infinite oscillation that never converges.
            //
            // CaDiCaL does NOT have a repair pass (extend.cpp:121-204) — it
            // trusts reconstruction to produce a correct model extension. If
            // reconstruction alone cannot satisfy all original clauses, that
            // indicates either:
            //   (a) the reconstruction stack is missing entries (a BVE bug), or
            //   (b) the formula is actually UNSAT.
            // In case (a), the proper fix is in the BVE/reconstruction code,
            // not a greedy repair. In case (b), returning Unknown is correct.

            // Verify against original-formula ledger (#4999: always-on).
            // Original clauses are in external index space (#5250).
            //
            // CaDiCaL's External::check_assignment (external.cpp:704-749)
            // checks ALL original clauses after reconstruction — no skip.
            // AY does the same: reconstruction has already run. Any clause
            // still unsatisfied is a genuine reconstruction bug → Unknown.
            //
            // When push/pop was used (#5077, #5522): skip scoped clauses,
            // because they may contain scope-selector literals that are
            // no longer asserted after pop().
            let fail_idx = self.cold.original_ledger.iter_clauses().position(|clause| {
                // Skip clauses containing scope selector variables.
                if self.cold.has_ever_scoped {
                    let has_scope = clause.iter().any(|lit| {
                        let vi = lit.variable().index();
                        vi < self.cold.was_scope_selector.len() && self.cold.was_scope_selector[vi]
                    });
                    if has_scope {
                        return false;
                    }
                }
                // #8577: Domain-restricted verification. When active_domain is set
                // (IC3/PDR domain-restricted BCP), non-domain variables are don't-cares
                // and may have incorrect values in the model. Domain-restricted BCP
                // at level >0 only propagates domain variables, so:
                // - Clauses with ANY non-domain literal may be unsatisfied because the
                //   non-domain literal wasn't propagated even though a domain literal
                //   unit-propagated it in full BCP.
                // - Only clauses where ALL variables are in the domain can be reliably
                //   checked: the solver decided/propagated all of them.
                //
                // This matches the IC3-specific bypass in solve/ic3.rs:297 which
                // returns the model directly without finalize_sat_model verification,
                // and the scoped-path domain-aware verification at line 621.
                if let Some(ref domain) = self.active_domain {
                    let has_non_domain_var = clause.iter().any(|lit| {
                        let vi = lit.variable().index();
                        if vi < self.cold.e2i.len() {
                            let int_var = self.cold.e2i[vi];
                            if int_var != compact::UNMAPPED {
                                let iv = int_var as usize;
                                iv >= domain.len() || !domain[iv]
                            } else {
                                true // Unmapped = non-domain
                            }
                        } else {
                            true // Out-of-range = non-domain
                        }
                    });
                    if has_non_domain_var {
                        return false; // Has non-domain var; cannot verify reliably.
                    }
                }
                !clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    vi < ext_model.len() && (ext_model[vi] == lit.is_positive())
                })
            });
            if let Some(fi) = fail_idx {
                let clause = self.cold.original_ledger.clause(fi);
                let clause_dimacs: Vec<i32> = clause
                    .iter()
                    .map(|&lit| {
                        let v = lit.variable().0 as i32 + 1;
                        if lit.is_positive() {
                            v
                        } else {
                            -v
                        }
                    })
                    .collect();
                let lit_details: Vec<String> = clause
                    .iter()
                    .map(|&lit| {
                        let vi = lit.variable().index();
                        let model_val = if vi < ext_model.len() {
                            Some(ext_model[vi])
                        } else {
                            None
                        };
                        let before_val = if vi < ext_model_before.len() {
                            Some(ext_model_before[vi])
                        } else {
                            None
                        };
                        format!(
                            "ext_var{}=before:{:?}->after:{:?}(pos={})",
                            vi,
                            before_val,
                            model_val,
                            lit.is_positive()
                        )
                    })
                    .collect();
                let was_sat_before = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    vi < ext_model_before.len() && (ext_model_before[vi] == lit.is_positive())
                });
                let changed_vars: Vec<usize> = (0..ext_model.len().max(ext_model_before.len()))
                    .filter(|&vi| {
                        let a = ext_model_before.get(vi).copied().unwrap_or(false);
                        let b = ext_model.get(vi).copied().unwrap_or(false);
                        a != b
                    })
                    .collect();
                // Replay reconstruction to find which step(s) flipped the
                // variables involved in the failing clause. This replaces
                // the debug-only iter_steps approach with a replay that works
                // in release builds (#8485).
                let recon_entries: Vec<String> = {
                    // Find which variable was satisfied before but broken after
                    let broken_vars: Vec<usize> = clause
                        .iter()
                        .filter_map(|&lit| {
                            let vi = lit.variable().index();
                            let was_sat = vi < ext_model_before.len()
                                && (ext_model_before[vi] == lit.is_positive());
                            let now_sat =
                                vi < ext_model.len() && (ext_model[vi] == lit.is_positive());
                            if was_sat && !now_sat {
                                Some(vi)
                            } else {
                                None
                            }
                        })
                        .collect();
                    // Also list ALL reconstruction entries whose witness involves
                    // the broken variable (both polarities).
                    let mut entries = Vec::new();
                    let steps = self.inproc.reconstruction.steps_ref();
                    // First: enumerate all entries with broken var as witness
                    for (si, step) in steps.iter().enumerate() {
                        if let crate::reconstruct::ReconstructionStep::Witness(wc) = step {
                            let has_broken_witness = wc
                                .witness
                                .iter()
                                .any(|w| broken_vars.contains(&w.variable().index()));
                            if has_broken_witness {
                                let w: Vec<i32> =
                                    wc.witness.iter().map(|l| l.to_dimacs()).collect();
                                let c: Vec<i32> = wc.clause.iter().map(|l| l.to_dimacs()).collect();
                                entries.push(format!("  stack[{si}]: witness={w:?} clause={c:?}"));
                            }
                        }
                    }
                    // Second: replay reconstruction to find the flip step
                    let mut replay = ext_model_before;
                    for (rev_idx, step) in steps.iter().rev().enumerate() {
                        let fwd_idx = steps.len() - 1 - rev_idx;
                        if let crate::reconstruct::ReconstructionStep::Witness(wc) = step {
                            let pre: Vec<(usize, bool)> = broken_vars
                                .iter()
                                .filter(|&&vi| vi < replay.len())
                                .map(|&vi| (vi, replay[vi]))
                                .collect();
                            crate::reconstruct::reconstruct_witness_pub(
                                &mut replay,
                                &wc.witness,
                                &wc.clause,
                            );
                            for (vi, old_val) in &pre {
                                if *vi < replay.len() && replay[*vi] != *old_val {
                                    let w: Vec<i32> =
                                        wc.witness.iter().map(|l| l.to_dimacs()).collect();
                                    let c: Vec<i32> =
                                        wc.clause.iter().map(|l| l.to_dimacs()).collect();
                                    entries.push(format!(
                                        "  FLIP at stack[{fwd_idx}]: witness={w:?} clause={c:?} FLIPPED ext_var{vi} {old_val}->{}", replay[*vi]
                                    ));
                                }
                            }
                        } else if let crate::reconstruct::ReconstructionStep::Sweep {
                            num_vars,
                            lit_map,
                        } = step
                        {
                            let pre: Vec<(usize, bool)> = broken_vars
                                .iter()
                                .filter(|&&vi| vi < replay.len())
                                .map(|&vi| (vi, replay[vi]))
                                .collect();
                            crate::reconstruct::reconstruct_sweep_pub(
                                &mut replay,
                                *num_vars,
                                lit_map,
                            );
                            for (vi, old_val) in &pre {
                                if *vi < replay.len() && replay[*vi] != *old_val {
                                    entries.push(format!(
                                        "  FLIP at stack[{fwd_idx}]: SWEEP FLIPPED ext_var{vi} {old_val}->{}", replay[*vi]
                                    ));
                                }
                            }
                        }
                    }
                    entries
                };
                let detail = format!(
                    "BUG: original clause {}/{} unsatisfied, reconstruction_len={}, num_original={}, \
                     clause_dimacs={:?}, lit_details=[{}], root_satisfied_saved={}, \
                     was_sat_before_recon={}, changed_vars_count={}, changed_vars={:?}, \
                     recon_entries_involving_clause=[{}]",
                    fi,
                    self.cold.original_ledger.num_clauses(),
                    self.inproc.reconstruction.len(),
                    self.num_original_clauses,
                    clause_dimacs,
                    lit_details.join(", "),
                    self.cold.root_satisfied_saved.len(),
                    was_sat_before,
                    changed_vars.len(),
                    &changed_vars[..changed_vars.len().min(30)],
                    recon_entries.join("\n"),
                );
                tracing::error!(
                    detail = detail.as_str(),
                    "original formula verification failed"
                );
                eprintln!("FINALIZE_SAT_FAIL: {detail}");

                return Err(detail);
            }

            // Verify root-satisfied clauses (external space, debug only).
            // #8577: Skip when domain restriction is active — root-satisfied
            // clauses involving non-domain variables may appear unsatisfied.
            #[cfg(debug_assertions)]
            if self.active_domain.is_none() {
                for (ri, clause) in self.cold.root_satisfied_saved.iter().enumerate() {
                    let satisfied = clause.iter().any(|&lit| {
                        let vi = lit.variable().index();
                        vi < ext_model.len() && (ext_model[vi] == lit.is_positive())
                    });
                    assert!(
                        satisfied,
                        "BUG: root-satisfied clause {} unsatisfied in post-reconstruction \
                         external model! num_ext_vars={}, recon_steps={}",
                        ri,
                        ext_num_vars,
                        self.inproc.reconstruction.len(),
                    );
                }
            }

            // #8819 (verification gap #1): Always-on clause_db re-verification in
            // release builds. The loop above already verifies against the
            // original formula ledger (authoritative); this belt-and-suspenders
            // check catches bugs where the mutable arena diverges from the
            // ledger after reconstruction. On failure we return Err so the
            // caller downgrades to Unknown rather than reporting unsound SAT.
            if self.active_domain.is_none() {
                let mut internal_model = vec![false; self.num_vars];
                let mut missing_var: Option<(usize, usize)> = None;
                for (int_var, val) in internal_model.iter_mut().enumerate() {
                    let ext_var = self.cold.i2e[int_var] as usize;
                    if ext_var >= ext_model.len() {
                        missing_var = Some((int_var, ext_var));
                        break;
                    }
                    *val = ext_model[ext_var];
                }
                if let Some((int_var, ext_var)) = missing_var {
                    let detail = format!(
                        "BUG [#8819]: reconstructed SAT model missing external var {ext_var} \
                         for internal var {int_var}; ext_model.len()={}",
                        ext_model.len(),
                    );
                    tracing::error!(detail = detail.as_str(), "i2e mapping violation");
                    return Err(detail);
                }
                if let Some(violation) = self.first_model_violation(&internal_model, false) {
                    let detail = format!(
                        "BUG [#8819]: reconstructed SAT model does not satisfy clause_db: {violation:?}"
                    );
                    tracing::error!(detail = detail.as_str(), "clause_db verification failed");
                    return Err(detail);
                }
            }

            // Truncate external model to user-visible variables.
            // User variables are the first user_num_vars external variables.
            let mut result = ext_model;
            result.truncate(self.user_num_vars);

            return Ok(result);
        }

        // Under scope: verify non-deleted clause_db with domain awareness (#8473).
        // When active_domain is set, clauses with non-domain variables are
        // trivially satisfied (don't-cares). Without domain-aware verification,
        // domain-restricted SAT results falsely fail model checks because
        // non-domain variables default to false in the model.
        //
        // Reconstruction entries may reference clauses incompatible with scoped
        // constraints, so skip_inprocessing is false (no reconstruction in scope path).
        let verification_result = if let Some(ref domain) = self.active_domain {
            self.first_model_violation_domain_aware(&model, domain)
        } else {
            self.first_model_violation(&model, false)
        };

        // Scoped path: verify internal model against clause_db and truncate.
        // No reconstruction applied (entries may conflict with scoped constraints).
        // #8819 (Gap 1): this verification is the authoritative scoped-path
        // soundness gate — always run in release.
        if let Some(violation) = verification_result {
            let detail = match &violation {
                preprocess::ModelViolation::ClauseDb {
                    clause_index,
                    clause_dimacs,
                } => {
                    format!("clause_db[{clause_index}] unsatisfied; clause={clause_dimacs:?}")
                }
            };
            return Err(detail);
        }
        let mut result = model;
        // #8819 (verification gap #1): Belt-and-suspenders re-verification runs
        // in release builds. The check above already returned Err on violation,
        // but we repeat the check to catch TOCTOU-style bugs where
        // `result`/`model` could have been mutated between the two checks (it
        // hasn't been, but this guards against future edits).
        let post_violation = if let Some(ref domain) = self.active_domain {
            self.first_model_violation_domain_aware(&result, domain)
        } else {
            self.first_model_violation(&result, false)
        };
        if let Some(violation) = post_violation {
            let detail = format!(
                "BUG [#8819]: scoped SAT model does not satisfy clause_db on re-verification: \
                 {violation:?}"
            );
            tracing::error!(detail = detail.as_str(), "scoped re-verification failed");
            return Err(detail);
        }
        result.truncate(self.user_num_vars);
        Ok(result)
    }

    #[inline]
    pub(in crate::solver) fn declare_sat_from_model(&mut self, model: Vec<bool>) -> SatResult {
        let model = match self.finalize_sat_model(model) {
            Ok(model) => model,
            Err(detail) => {
                tracing::error!(
                    detail = detail.as_str(),
                    "sat model verification failed after reconstruction"
                );
                // #8754: Poison the solver so subsequent UNSAT results
                // from this solve call are downgraded to Unknown. The
                // model/arena/ledger disagreement indicates a corruption
                // bug; any later CDCL-derived UNSAT is built on clauses
                // that may be inconsistent with the original formula.
                self.cold.finalize_sat_fail_count =
                    self.cold.finalize_sat_fail_count.saturating_add(1);
                self.cold.last_unknown_detail = Some(detail);
                return self.declare_unknown_with_reason(SatUnknownReason::InvalidSatModel);
            }
        };
        // #7912 + #8819 (verification gap #1): verify the finalized external model
        // against all original clauses. finalize_sat_model already runs an
        // always-on original-formula check, but this re-verification on the
        // truncated (user-visible) model catches bugs in truncation/scope
        // handling. Runs in release builds — on failure we downgrade to
        // Unknown rather than return an unsound SAT.
        // NOTE: debug_assert_sat_result_model was removed here because it reads
        // from self.vals (get_model()) which is stale when walk/ProbSAT finds SAT.
        // The walk path stores its solution in phases (get_model_from_phases),
        // not in vals. The finalize_sat_model + verify_external_model checks
        // provide complete verification coverage.
        if !self.verify_external_model(&model) {
            let detail = "BUG [#8819]: Invalid SAT model — finalized model does not satisfy \
                          original clauses on release-mode re-verification"
                .to_owned();
            tracing::error!(detail = detail.as_str(), "final SAT re-verification failed");
            self.cold.finalize_sat_fail_count = self.cold.finalize_sat_fail_count.saturating_add(1);
            self.cold.last_unknown_detail = Some(detail);
            return self.declare_unknown_with_reason(SatUnknownReason::InvalidSatModel);
        }
        solver_log!(
            self,
            "SAT: {} conflicts, {} decisions, model size {}",
            self.num_conflicts,
            self.num_decisions,
            model.len()
        );
        tracing::info!(
            num_conflicts = self.num_conflicts,
            num_decisions = self.num_decisions,
            model_size = model.len(),
            "solve: sat"
        );
        self.emit_diagnostic_sat_summary(model.len());
        SatResult::Sat(model)
    }

    #[inline]
    pub(in crate::solver) fn declare_sat_from_current_assignment(&mut self) -> SatResult {
        self.declare_sat_from_model(self.get_model())
    }

    #[inline]
    pub(in crate::solver) fn declare_unknown_with_reason(
        &mut self,
        reason: SatUnknownReason,
    ) -> SatResult {
        if ay_core::debug_channel_active(ay_core::DebugChannel::Unknown) {
            let detail_str = self.cold.last_unknown_detail.as_deref().unwrap_or("(none)");
            eprintln!(
                "DECLARE_UNKNOWN: reason={}, conflicts={}, decisions={}, propagations={}, detail={}",
                reason.diagnostic_label(),
                self.num_conflicts,
                self.num_decisions,
                self.num_propagations,
                detail_str,
            );
        }
        self.cold.last_unknown_reason = Some(reason);
        self.emit_diagnostic_unknown_summary(reason.diagnostic_label());
        SatResult::Unknown
    }

    #[inline]
    pub(in crate::solver) fn declare_assume_sat_from_model(
        &mut self,
        model: Vec<bool>,
    ) -> AssumeResult {
        let model = match self.finalize_sat_model(model) {
            Ok(model) => model,
            Err(detail) => {
                tracing::error!(
                    detail = detail.as_str(),
                    "assumption SAT model verification failed after reconstruction"
                );
                // #8754: Poison the solver so subsequent UNSAT results
                // from this solve call are downgraded to Unknown.
                self.cold.finalize_sat_fail_count =
                    self.cold.finalize_sat_fail_count.saturating_add(1);
                self.cold.last_unknown_detail = Some(detail);
                return self.declare_assume_unknown_with_reason(SatUnknownReason::InvalidSatModel);
            }
        };
        // #7912 + #8819 (verification gap #1): verify the finalized external model
        // against all original clauses. Runs in release builds.
        // Domain-restricted SAT (#8473): skip external verification when active
        // domain is set because the model only satisfies domain-restricted
        // clauses. Non-domain variables are don't-cares and may have incorrect
        // values in the model. The domain-aware verification in finalize_sat_model
        // is the authoritative check for domain-restricted results.
        // NOTE: debug_assert_sat_result_model removed — reads stale self.vals
        // after walk/ProbSAT. See comment in declare_sat_from_model.
        if self.active_domain.is_none() && !self.verify_external_model(&model) {
            let detail = "BUG [#8819]: Invalid SAT model — assumption-path model does not \
                          satisfy original clauses on release-mode re-verification"
                .to_owned();
            tracing::error!(
                detail = detail.as_str(),
                "assumption SAT re-verification failed"
            );
            self.cold.finalize_sat_fail_count = self.cold.finalize_sat_fail_count.saturating_add(1);
            self.cold.last_unknown_detail = Some(detail);
            return self.declare_assume_unknown_with_reason(SatUnknownReason::InvalidSatModel);
        }
        self.emit_diagnostic_sat_summary(model.len());
        AssumeResult::Sat(model)
    }

    #[inline]
    pub(in crate::solver) fn declare_assume_unknown_with_reason(
        &mut self,
        reason: SatUnknownReason,
    ) -> AssumeResult {
        self.cold.last_unknown_reason = Some(reason);
        self.emit_diagnostic_unknown_summary(reason.diagnostic_label());
        AssumeResult::Unknown
    }

    #[inline]
    pub(in crate::solver) fn declare_assume_sat_from_current_assignment(&mut self) -> AssumeResult {
        // #relevancy-lazy-routing: identical to `get_model()` unless the
        // relevancy brancher is enabled, in which case don't-care variables
        // (left unassigned by the frontier-empty SAT signal) complete from
        // their saved phase instead of `false` — see
        // `relevancy_completed_model` for the rationale and soundness note.
        self.declare_assume_sat_from_model(self.relevancy_completed_model())
    }

    pub(in crate::solver) fn finalize_assumption_api_result(
        &self,
        result: AssumeResult,
    ) -> AssumeResult {
        match result {
            AssumeResult::Sat(mut sat_model) => {
                // #7912: verify the full model BEFORE truncation, so clauses
                // containing internal variables beyond user_num_vars are checked
                // correctly. (Other call sites verify before truncation too.)
                // #8577: Skip when domain restriction is active — non-domain
                // variables are don't-cares and may not satisfy all clauses.
                debug_assert!(
                    self.active_domain.is_some() || self.verify_external_model(&sat_model),
                    "BUG: Invalid SAT model in finalize_assumption_api_result"
                );
                sat_model.truncate(self.user_num_vars);
                AssumeResult::Sat(sat_model)
            }
            AssumeResult::Unsat(core, cert) => {
                AssumeResult::Unsat(self.filter_scope_selectors_from_core(core), cert)
            }
            AssumeResult::Unknown => AssumeResult::Unknown,
        }
    }

    pub(in crate::solver) fn filter_scope_selectors_from_core(
        &self,
        core: Vec<Literal>,
    ) -> Vec<Literal> {
        core.into_iter()
            .filter(|lit| {
                let idx = lit.variable().index();
                idx >= self.cold.scope_selector_set.len() || !self.cold.scope_selector_set[idx]
            })
            .collect()
    }
}
