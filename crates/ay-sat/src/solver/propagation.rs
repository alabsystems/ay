// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core CDCL propagation and decision helpers.
//!
//! Contains literal value queries, assignment/enqueue, VSIDS/VMTF decision
//! selection with random injection, 2-watched literal initialization, and
//! the hot BCP loop with deferred watch buffer swap and in-place compaction.
//!
//! BCP is unified into a single const-generic `propagate_bcp::<MODE>()`
//! function (#5037). The compiler monomorphizes three variants at compile
//! time, and `if MODE == ...` branches on the const parameter are eliminated
//! as dead code, producing identical machine code to the hand-specialized
//! versions.

// BCP replacement scan loops use `for k in pos..len` where k is needed both
// to index `clause_lits[k]` and to call `swap_literals(clause_idx, _, k)`.
// The clippy suggestion `.iter().enumerate().take().skip()` adds iterator
// overhead in the hottest loop of the solver.
#![allow(clippy::needless_range_loop)]

use super::*;
use crate::solver_log::solver_log;

/// BCP mode constants for the unified `propagate_bcp::<MODE>()` function.
///
/// These are used as const-generic parameters. The compiler eliminates
/// dead branches at monomorphization time, so mode checks are zero-cost.
pub(super) mod bcp_mode {
    pub(crate) const SEARCH: u8 = 0;
    pub(crate) const PROBE: u8 = 1;
    pub(crate) const VIVIFY: u8 = 2;
}

impl Solver {
    #[inline]
    pub(super) fn lit_value(&self, lit: Literal) -> Option<bool> {
        match ay_prefetch::val_at(&self.vals, lit.index()) {
            0 => None,
            v => Some(v > 0),
        }
    }

    /// Branch-free literal value: 1 (true), -1 (false), 0 (unassigned).
    ///
    /// Uses unchecked access in release builds (via `val_at`) to match
    /// CaDiCaL's raw pointer `vals[lit]` pattern. The invariant that
    /// `lit.index() < vals.len()` is maintained by construction (vals is
    /// sized `2 * num_vars`, every literal satisfies `index() < 2 * num_vars`).
    #[inline]
    pub(super) fn lit_val(&self, lit: Literal) -> i8 {
        ay_prefetch::val_at(&self.vals, lit.index())
    }

    /// Check if a variable is assigned using the branch-free vals[] array.
    /// vals[] is the sole source of truth for assignment state (#3758 Phase 3).
    #[inline]
    pub(super) fn var_is_assigned(&self, var_idx: usize) -> bool {
        // vals[positive_literal(var)] is 0 iff unassigned, nonzero iff assigned.
        ay_prefetch::val_at(&self.vals, var_idx * 2) != 0
    }

    /// Get variable assignment from vals[] as Option<bool>.
    /// vals[] is the sole source of truth for assignment state (#3758 Phase 3).
    #[inline]
    pub(super) fn var_value_from_vals(&self, var_idx: usize) -> Option<bool> {
        match ay_prefetch::val_at(&self.vals, var_idx * 2) {
            0 => None,
            v => Some(v > 0),
        }
    }

    /// Compute the assignment level for a propagated literal (ChrBT).
    ///
    /// CaDiCaL propagate.cpp:25-56: the assignment level is the maximum level
    /// among the *other* literals in the reason clause. This can be lower than
    /// `decision_level` when chronological backtracking has left out-of-order
    /// literals on the trail.
    ///
    /// Unassigned literals must be ignored here. Chronological backtracking
    /// intentionally leaves stale `var_data.level` metadata on variables after
    /// unassigning them, and inprocessing can add fresh clauses at level 0
    /// before those stale levels are scrubbed. Reading raw levels for
    /// unassigned reason literals can therefore manufacture an assignment level
    /// above the current `decision_level`, tripping root-level enqueue during
    /// preprocessing.
    ///
    /// Returns `decision_level` for decisions (no reason clause) or when ChrBT
    /// is disabled.
    ///
    /// Uses `bcp_literal()` (unchecked in release) instead of `arena.literals()`
    /// (which creates a bounds-checked bytemuck slice) to match the BCP loop's
    /// raw access pattern (#7998). Also uses `val_at()` (unchecked) instead of
    /// `lit_val()` for the same reason.
    #[inline(always)]
    fn assignment_level(&self, lit: Literal, reason: ClauseRef) -> u32 {
        let decision_level = self.decision_level;
        // Fast path: at decision level 0, all assigned literals are at
        // level 0, so the max over reason literals is trivially 0.
        // Skips the arena fetch + clause scan entirely.
        if decision_level == 0 {
            return 0;
        }
        let clause_idx = reason.0 as usize;
        let len = self.arena.len_of(clause_idx);
        // Fast path: binary clauses (most common in BCP).
        // Position of propagated literal is not fixed; check both.
        if len == 2 {
            let lit0 = self.arena.bcp_literal(clause_idx, 0);
            let lit1 = self.arena.bcp_literal(clause_idx, 1);
            let other = if lit0 == lit { lit1 } else { lit0 };
            return self.assignment_level_binary(other);
        }
        // General path: scan all non-self literals using bcp_literal
        // (unchecked release access). Uses val_at (i8, unchecked) instead
        // of lit_value (Option<bool>) to avoid enum construction + pattern
        // matching per literal. The invariant is: only falsified reason
        // literals (val < 0) contribute to the assignment level.
        // CaDiCaL propagate.cpp:49 uses `val(other)`.
        let mut level = 0u32;
        for k in 0..len {
            let other = self.arena.bcp_literal(clause_idx, k);
            if other == lit {
                continue;
            }
            if ay_prefetch::val_at(&self.vals, other.index()) >= 0 {
                continue;
            }
            let other_level = self.var_data[other.variable().index()].level;
            if other_level >= decision_level {
                // Early exit: can't exceed decision_level, and we found
                // a literal at or above it. CaDiCaL propagate.cpp:51-52.
                return decision_level;
            }
            if other_level > level {
                level = other_level;
            }
        }
        level
    }

    /// Binary clause assignment level: avoids arena access entirely.
    ///
    /// When the caller already knows the other literal (e.g. from the watch
    /// entry blocker in BCP, or from the binary clause fast path in
    /// `assignment_level`), this skips the arena fetch + length check +
    /// literal comparison. CaDiCaL propagate.cpp:25-35.
    #[inline(always)]
    fn assignment_level_binary(&self, other: Literal) -> u32 {
        if self.lit_val(other) < 0 {
            self.var_data[other.variable().index()]
                .level
                .min(self.decision_level)
        } else {
            0
        }
    }

    /// REQUIRES: variable is unassigned (assignment[var] == None)
    /// ENSURES: variable assigned at its actual assignment level (which may be
    ///          below `decision_level` under chronological backtracking),
    ///          literal appended to trail, vals[] updated for both polarities
    #[inline]
    pub(super) fn enqueue(&mut self, lit: Literal, reason: Option<ClauseRef>) {
        let var = lit.variable();
        let reason_clause = reason;
        // Soundness-triage tripwire (AY_AB_TRIAGE_VAR=<dimacs var>): report
        // every assignment of that variable with level + pass attribution.
        {
            use std::sync::OnceLock;
            static TVAR: OnceLock<Option<usize>> = OnceLock::new();
            let t = TVAR.get_or_init(|| {
                std::env::var("AY_AB_TRIAGE_VAR")
                    .ok()
                    .and_then(|s| s.trim().parse::<usize>().ok())
            });
            if let Some(tv) = t {
                if var.index() + 1 == *tv {
                    let rinfo = match reason {
                        Some(r) => {
                            let lits: Vec<String> = self
                                .arena
                                .literals(r.0 as usize)
                                .iter()
                                .map(|l| l.index().to_string())
                                .collect();
                            format!(
                                "ref={} cid={} learned={} lits=[{}]",
                                r.0,
                                self.cold.clause_ids.get(r.0 as usize).copied().unwrap_or(0),
                                self.arena.is_learned(r.0 as usize),
                                lits.join(" ")
                            )
                        }
                        None => "NONE".to_string(),
                    };
                    eprintln!(
                        "TRIAGE_ASSIGN: lit_idx={} level={} pass={:?} reason {}",
                        lit.index(),
                        self.decision_level,
                        self.cold.diagnostic_pass,
                        rinfo,
                    );
                }
            }
        }
        // Safety net (#8359, #8382): skip stale literals with var_index >= num_vars.
        // This catches JIT/compaction producing out-of-bounds variable indices.
        // Tracked via stats.stale_enqueue_skips; zero is expected when correct.
        if var.index() >= self.num_vars {
            self.stats.stale_enqueue_skips += 1;
            tracing::warn!(
                "stale literal in enqueue: var {} >= num_vars {} (lit={:?})",
                var.index(),
                self.num_vars,
                lit
            );
            return;
        }
        // CaDiCaL propagate.cpp:140: assignment count overflow guard.
        // Ensures we never assign more variables than exist.
        debug_assert!(
            self.trail.len() < self.num_vars,
            "BUG: enqueue would exceed num_vars ({}) — trail already has {} entries",
            self.num_vars,
            self.trail.len(),
        );
        debug_assert!(
            !self.var_is_assigned(var.index()),
            "BUG: enqueue of already-assigned variable {} (lit {:?})",
            var.index(),
            lit
        );
        // CaDiCaL propagate.cpp:110: eliminated variables only via decision/external
        debug_assert!(
            !self.var_lifecycle.is_removed(var.index()) || reason.is_none(),
            "BUG: propagating eliminated variable {} with reason clause",
            var.index(),
        );
        // CaDiCaL propagate.cpp:151: save phase on every search assignment.
        // Keeps phases fresh between backtracks, especially during trail reuse.
        if !self.suppress_phase_saving {
            self.phase[var.index()] = lit.sign_i8();
        }
        // CaDiCaL propagate.cpp:130-140: with ChrBT enabled, compute the true
        // assignment level from the reason clause. This allows propagated
        // literals to have level < decision_level, enabling chronological
        // backtracking to keep more of the trail (#6998).
        // Computed before the var_data borrow to avoid &self / &mut conflict.
        let (assigned_level, assigned_reason) = if self.chrono_enabled {
            if let Some(reason) = reason_clause {
                let al = self.assignment_level(lit, reason);
                if al == 0 {
                    // CaDiCaL propagate.cpp:134-135: if assignment level is 0,
                    // the literal is a root-level unit. Mark as fixed so
                    // collect_level0_garbage fires correctly.
                    //
                    // Keep the reason clause (unlike CaDiCaL which clears it).
                    // AY uses lazy proof materialization: materialize_level0_unit_proofs()
                    // needs the reason clause to build LRAT proof chains for
                    // level-0 units discovered during ChrBT propagation (#6998).
                    if !self.var_lifecycle.is_inactive(var.index()) {
                        self.fixed_count += 1;
                        self.var_lifecycle.mark_fixed(var.index());
                        self.l0_gc_dirty[var.index()] = true;
                    }
                    (0, reason.0)
                } else {
                    (al, reason.0)
                }
            } else {
                // Decision literal — always at decision_level.
                (self.decision_level, NO_REASON)
            }
        } else {
            // ChrBT disabled: always use decision_level (original behavior).
            (
                self.decision_level,
                reason_clause.map_or(NO_REASON, |r| r.0),
            )
        };
        // vals[] is the sole source of truth for assignment state (#3758 Phase 3).
        ay_prefetch::val_set(&mut self.vals, lit.index(), 1);
        ay_prefetch::val_set(&mut self.vals, lit.negated().index(), -1);
        debug_assert!(
            assigned_level <= self.decision_level,
            "BUG: assignment_level {} exceeds decision_level {} for {:?}",
            assigned_level,
            self.decision_level,
            lit
        );
        // Kissat inlineassign.h pattern: write entire VarData as one struct store
        // instead of 4 separate field writes + read-modify-write on flags byte (#8042).
        // Preserve the `seen` flag bit (conflict analysis marks persist across
        // backtrack/re-assign cycles until analyze_conflict calls clear()).
        // Binary reason flag is always clear here; callers that need it set use
        // the dedicated enqueue_bcp_binary path instead.
        let preserved_flags = self.var_data[var.index()].flags & VarData::FLAG_SEEN_PUB;
        self.var_data[var.index()] = VarData {
            level: assigned_level,
            trail_pos: self.trail.len() as u32,
            reason: assigned_reason,
            flags: preserved_flags,
            _pad: [0; 3],
        };
        // Note: mark_reason_clause() is NOT called here (#8569). BCP reason
        // marking is deferred: backtrack already invalidates all reason marks
        // (line ~264 in backtrack.rs), so incremental marks written during BCP
        // are always discarded before any consumer reads them. Consumers
        // (reduction, inprocessing) call ensure_reason_clause_marks_current()
        // which rebuilds marks from the trail in O(trail_len). This saves one
        // cache-line write per propagation on the BCP hot path.
        //
        // Invalidate marks when a clause reason is set, so consumers know to
        // rebuild. BCP dispatch functions also set this, but enqueue() can be
        // called directly by tests and non-BCP paths (search_assign_driving,
        // external propagation). Single bool write — not in the hot BCP loop.
        if assigned_reason != NO_REASON {
            self.reason_marks_invalidated = true;
        }
        self.trail.push(lit);
        solver_log!(
            self,
            "assign {} at level {} (dl={}) reason {:?}",
            lit.to_dimacs(),
            assigned_level,
            self.decision_level,
            reason_clause
        );
        // Propagation events are omitted from the decision trace because BCP is
        // deterministic: given the same decisions and clause database state,
        // propagations are identical. Omitting them keeps traces compact
        // (~50 bytes/conflict vs ~300 bytes with propagations), satisfying the
        // <200MB criterion for 1M-conflict runs.
        // CaDiCaL propagate.cpp:148-149: post-assignment polarity check
        debug_assert_eq!(
            self.vals[lit.index()],
            1,
            "BUG: val[lit] != 1 after enqueue of {lit:?}"
        );
        debug_assert_eq!(
            self.vals[lit.negated().index()],
            -1,
            "BUG: val[¬lit] != -1 after enqueue of {lit:?}"
        );
        // CaDiCaL propagate.cpp:141: trail length mirrors assignment count.
        // Sampled every 1024 enqueues: the O(num_vars) scan is too expensive to
        // run on every propagation (caused 50x debug slowdown on schup-l2s, #4967).
        // After #3758 Phase 3, vals[] is the sole source of truth. Count assigned
        // variables by scanning vals[] (positive literal positions only).
        #[cfg(debug_assertions)]
        if self.trail.len() & 0x3ff == 0 {
            let assigned_count = (0..self.num_vars)
                .filter(|&v| self.vals[v * 2] != 0)
                .count();
            debug_assert_eq!(
                assigned_count,
                self.trail.len(),
                "BUG: assigned variable count != trail.len() after enqueue of {lit:?}",
            );
        }
        // CaDiCaL propagate.cpp:160-166: prefetch watch list for -lit.
        // BCP will scan this list on the next propagation step. Issue a
        // non-blocking L2 prefetch to hide main-memory latency (~60-80 cycles)
        // behind the current propagation work.
        self.watches.prefetch_first(lit.negated());
    }

    /// Lightweight enqueue for BCP propagation assignments (Kissat fastassign.h).
    ///
    /// Skips work that is unnecessary during propagation:
    /// - `suppress_phase_saving` check (always false during search BCP)
    /// - Periodic debug-mode trail/vals consistency scan
    /// - `solver_log!` macro (only useful in PROBE mode; PROBE still uses `enqueue`)
    ///
    /// Per-assignment overhead minimized (#8042):
    /// - VarData written as a single 16-byte struct store (Kissat inlineassign.h
    ///   pattern `*a = b`) instead of 4 separate field writes + read-modify-write
    ///   on flags byte. This replaces set_binary_reason(false) with flags=0 directly,
    ///   since both seen and binary_reason are always 0 at assignment time.
    /// - `decision_level` hoisted to local variable to avoid repeated field load.
    /// - ChrBT state passed as a const generic (#shave5): the BCP hot loops
    ///   already dispatch on a hoisted `chrono` local, so the two
    ///   `self.chrono_enabled` field reloads per assignment (which LLVM
    ///   cannot hoist across the loop's raw-pointer stores) fold away at
    ///   monomorphization time. `CHRONO` must equal `self.chrono_enabled`.
    ///
    /// REQUIRES: variable is unassigned, reason is always present (propagation),
    ///           `CHRONO == self.chrono_enabled`
    /// ENSURES: same post-conditions as `enqueue` for propagation assignments
    #[inline(always)]
    pub(super) fn enqueue_bcp<const CHRONO: bool>(&mut self, lit: Literal, reason: ClauseRef) {
        let var = lit.variable();
        let dl = self.decision_level;
        debug_assert_eq!(
            self.chrono_enabled, CHRONO,
            "BUG: enqueue_bcp::<{CHRONO}> called with chrono_enabled={}",
            self.chrono_enabled,
        );
        debug_assert!(
            var.index() < self.num_vars,
            "BUG: enqueue_bcp variable index {} >= num_vars {} (lit={lit:?}) — \
             stale literal after compaction or arena GC? (#8359)",
            var.index(),
            self.num_vars,
        );
        // Safety net (#8359, #8382, #8448): stale literal guard. Now debug-only
        // (#8465): the branch cost (~1 cmp+branch per propagation) is measurable
        // in the BCP hot path. The debug_assert above catches the same condition
        // during development. BVE soundness bugs (#8397) should be fixed at source.
        #[cfg(debug_assertions)]
        if var.index() >= self.num_vars {
            self.stats.stale_enqueue_skips += 1;
            tracing::warn!(
                "stale literal in enqueue_bcp: var {} >= num_vars {} (lit={:?})",
                var.index(),
                self.num_vars,
                lit
            );
            return;
        }
        debug_assert!(
            self.trail.len() < self.num_vars,
            "BUG: enqueue_bcp would exceed num_vars ({}) — trail already has {} entries",
            self.num_vars,
            self.trail.len(),
        );
        debug_assert!(
            !self.var_is_assigned(var.index()),
            "BUG: enqueue_bcp of already-assigned variable {} (lit {:?})",
            var.index(),
            lit
        );
        // Phase saving: always active during search BCP (suppress_phase_saving=false).
        self.phase[var.index()] = lit.sign_i8();
        // ChrBT assignment level computation.
        // `dl` hoisted above to avoid repeated `self.decision_level` field loads.
        // Level-0 fast path: at decision level 0, assignment level is trivially 0
        // regardless of ChrBT state. Skip the clause scan in assignment_level()
        // and go directly to the fixed-variable bookkeeping.
        let (assigned_level, assigned_reason) = if dl == 0 {
            if CHRONO && !self.var_lifecycle.is_inactive(var.index()) {
                self.fixed_count += 1;
                self.var_lifecycle.mark_fixed(var.index());
                self.l0_gc_dirty[var.index()] = true;
            }
            (0, reason.0)
        } else if CHRONO {
            let al = self.assignment_level(lit, reason);
            if al == 0 {
                if !self.var_lifecycle.is_inactive(var.index()) {
                    self.fixed_count += 1;
                    self.var_lifecycle.mark_fixed(var.index());
                    self.l0_gc_dirty[var.index()] = true;
                }
                (0, reason.0)
            } else {
                (al, reason.0)
            }
        } else {
            (dl, reason.0)
        };
        // vals[] update.
        ay_prefetch::val_set(&mut self.vals, lit.index(), 1);
        ay_prefetch::val_set(&mut self.vals, lit.negated().index(), -1);
        debug_assert!(
            assigned_level <= dl,
            "BUG: assignment_level {assigned_level} exceeds decision_level {dl} for {lit:?}"
        );
        // Kissat inlineassign.h pattern: write entire VarData as one struct store
        // instead of 4 separate field writes + read-modify-write on flags.
        // Preserve the `seen` flag bit (conflict analysis marks persist across
        // backtrack/re-assign cycles until the next analyze_conflict calls clear()).
        // Clear binary_reason since this is a non-binary propagation.
        // Debug-only reason validation (#8465): this check does
        // arena.literals() (bounds-checked bytemuck slice) + .contains()
        // on EVERY long-clause propagation. On large instances (50K+ vars),
        // this adds ~25% overhead to the BCP hot path. Critical for catching
        // bugs during development but must not run in release builds.
        debug_assert!(
            self.arena.literals(assigned_reason as usize).contains(&lit),
            "BUG(enqueue_bcp): reason clause at offset {} does not contain propagated \
             literal {:?} (dimacs={}) at time of propagation. clause_len={}, \
             dl={}, trail_len={}, num_conflicts={}",
            assigned_reason,
            lit,
            lit.to_dimacs(),
            self.arena.len_of(assigned_reason as usize),
            dl,
            self.trail.len(),
            self.num_conflicts,
        );
        let preserved_flags = self.var_data[var.index()].flags & VarData::FLAG_SEEN_PUB;
        self.var_data[var.index()] = VarData {
            level: assigned_level,
            trail_pos: self.trail.len() as u32,
            reason: assigned_reason,
            flags: preserved_flags,
            _pad: [0; 3],
        };
        // Reason marking deferred (#8569): see enqueue() comment.
        self.trail.push(lit);
        // Prefetch watch list for next propagation step.
        self.watches.prefetch_first(lit.negated());
    }

    /// Enqueue a binary-clause BCP propagation with the binary_reason flag set.
    ///
    /// Identical to `enqueue_bcp` but writes VarData with `FLAG_BINARY_REASON`
    /// already set, eliminating the extra read-modify-write that the BCP caller
    /// would otherwise need after calling `enqueue_bcp` (#8042).
    ///
    /// REQUIRES: variable is unassigned, reason is a binary clause
    /// ENSURES: same post-conditions as `enqueue_bcp` + binary_reason flag set
    #[inline(always)]
    pub(super) fn enqueue_bcp_binary(&mut self, lit: Literal, reason: ClauseRef) {
        let var = lit.variable();
        let dl = self.decision_level;
        debug_assert!(
            var.index() < self.num_vars,
            "BUG: enqueue_bcp_binary variable index {} >= num_vars {} (lit={lit:?}) — \
             stale literal after compaction or arena GC? (#8359)",
            var.index(),
            self.num_vars,
        );
        // Safety net (#8359, #8382, #8448): stale literal guard. Debug-only
        // (#8465): same rationale as enqueue_bcp.
        #[cfg(debug_assertions)]
        if var.index() >= self.num_vars {
            self.stats.stale_enqueue_skips += 1;
            tracing::warn!(
                "stale literal in enqueue_bcp_binary: var {} >= num_vars {} (lit={:?})",
                var.index(),
                self.num_vars,
                lit
            );
            return;
        }
        debug_assert!(
            self.trail.len() < self.num_vars,
            "BUG: enqueue_bcp_binary would exceed num_vars ({}) — trail already has {} entries",
            self.num_vars,
            self.trail.len(),
        );
        debug_assert!(
            !self.var_is_assigned(var.index()),
            "BUG: enqueue_bcp_binary of already-assigned variable {} (lit {:?})",
            var.index(),
            lit
        );
        // Phase saving: always active during search BCP.
        self.phase[var.index()] = lit.sign_i8();
        // ChrBT assignment level computation.
        // Level-0 fast path: at decision level 0, assignment level is trivially 0.
        // Binary ChrBT fast path (#8465): use assignment_level_binary directly
        // since we know the clause is binary. The original code called
        // assignment_level() which reads arena.len_of() + arena.literal()x2
        // to discover it's binary. The caller already has this info from the
        // watch entry.
        let (assigned_level, assigned_reason) = if dl == 0 {
            if self.chrono_enabled && !self.var_lifecycle.is_inactive(var.index()) {
                self.fixed_count += 1;
                self.var_lifecycle.mark_fixed(var.index());
                self.l0_gc_dirty[var.index()] = true;
            }
            (0, reason.0)
        } else if self.chrono_enabled {
            // Binary clause: the other literal in the reason clause is the
            // one that is NOT `lit`. We need to find it. Since this is a
            // binary clause, there are exactly 2 literals: lit and one other.
            // Use assignment_level which has a binary fast path.
            let al = self.assignment_level(lit, reason);
            if al == 0 {
                if !self.var_lifecycle.is_inactive(var.index()) {
                    self.fixed_count += 1;
                    self.var_lifecycle.mark_fixed(var.index());
                    self.l0_gc_dirty[var.index()] = true;
                }
                (0, reason.0)
            } else {
                (al, reason.0)
            }
        } else {
            (dl, reason.0)
        };
        // vals[] update.
        ay_prefetch::val_set(&mut self.vals, lit.index(), 1);
        ay_prefetch::val_set(&mut self.vals, lit.negated().index(), -1);
        debug_assert!(
            assigned_level <= dl,
            "BUG: assignment_level {assigned_level} exceeds decision_level {dl} for {lit:?}"
        );
        // Single struct store with FLAG_BINARY_REASON already set.
        // Preserve seen flag (conflict analysis marks persist across re-assign).
        let preserved_flags = (self.var_data[var.index()].flags & VarData::FLAG_SEEN_PUB)
            | VarData::FLAG_BINARY_REASON_PUB;
        self.var_data[var.index()] = VarData {
            level: assigned_level,
            trail_pos: self.trail.len() as u32,
            reason: assigned_reason,
            flags: preserved_flags,
            _pad: [0; 3],
        };
        // Reason marking deferred (#8569): see enqueue() comment.
        self.trail.push(lit);
        // Prefetch watch list for next propagation step.
        self.watches.prefetch_first(lit.negated());
    }

    /// Binary enqueue with known other literal for ChrBT (#8465).
    ///
    /// Like `enqueue_bcp_binary` but takes the other literal directly,
    /// skipping the arena access in `assignment_level()`. The BCP inner loop
    /// already knows the other literal from the watch entry (false_lit for
    /// binary clauses). This saves an `arena.len_of()` + two `arena.literal()`
    /// reads per binary propagation when ChrBT is enabled.
    ///
    /// REQUIRES: variable is unassigned, reason is a binary clause,
    ///           `other` is the other literal in the binary clause (not `lit`),
    ///           `self.chrono_enabled == true` (every caller dispatches on a
    ///           hoisted `chrono` local and uses the nochrono variant
    ///           otherwise, so the field reloads are dropped here — #shave5)
    #[inline(always)]
    pub(super) fn enqueue_bcp_binary_with_other(
        &mut self,
        lit: Literal,
        reason: ClauseRef,
        other: Literal,
    ) {
        let var = lit.variable();
        let dl = self.decision_level;
        debug_assert!(
            var.index() < self.num_vars,
            "BUG: enqueue_bcp_binary_with_other var {} >= num_vars {}",
            var.index(),
            self.num_vars,
        );
        debug_assert!(
            self.chrono_enabled,
            "BUG: enqueue_bcp_binary_with_other called with chrono_enabled=false"
        );
        // Phase saving.
        self.phase[var.index()] = lit.sign_i8();
        // ChrBT assignment level: use the known other literal directly.
        let (assigned_level, assigned_reason) = if dl == 0 {
            if !self.var_lifecycle.is_inactive(var.index()) {
                self.fixed_count += 1;
                self.var_lifecycle.mark_fixed(var.index());
                self.l0_gc_dirty[var.index()] = true;
            }
            (0, reason.0)
        } else {
            let al = self.assignment_level_binary(other);
            if al == 0 {
                if !self.var_lifecycle.is_inactive(var.index()) {
                    self.fixed_count += 1;
                    self.var_lifecycle.mark_fixed(var.index());
                    self.l0_gc_dirty[var.index()] = true;
                }
                (0, reason.0)
            } else {
                (al, reason.0)
            }
        };
        // vals[] update.
        ay_prefetch::val_set(&mut self.vals, lit.index(), 1);
        ay_prefetch::val_set(&mut self.vals, lit.negated().index(), -1);
        // VarData struct store with binary reason flag.
        let preserved_flags = (self.var_data[var.index()].flags & VarData::FLAG_SEEN_PUB)
            | VarData::FLAG_BINARY_REASON_PUB;
        self.var_data[var.index()] = VarData {
            level: assigned_level,
            trail_pos: self.trail.len() as u32,
            reason: assigned_reason,
            flags: preserved_flags,
            _pad: [0; 3],
        };
        // Reason marking deferred (#8569): see enqueue() comment.
        self.trail.push(lit);
        self.watches.prefetch_first(lit.negated());
    }

    // batch_enqueue_from_jit removed (#8517): BCP JIT staging trail gone.

    /// Stripped-down enqueue for BCP when ChrBT is disabled (#8465).
    ///
    /// Eliminates the ChrBT assignment_level() clause scan (O(clause_len)),
    /// the var_lifecycle.is_inactive() check, mark_fixed(), and l0_gc_dirty
    /// writes. These are ~30% of enqueue_bcp's per-call overhead on the BCP
    /// hot path when ChrBT is off.
    ///
    /// REQUIRES: chrono_enabled == false, variable is unassigned
    /// ENSURES: same post-conditions as enqueue_bcp with chrono_enabled=false
    #[inline(always)]
    pub(super) fn enqueue_bcp_nochrono(&mut self, lit: Literal, reason: ClauseRef) {
        let var = lit.variable();
        let dl = self.decision_level;
        debug_assert!(
            var.index() < self.num_vars,
            "BUG: enqueue_bcp_nochrono variable index {} >= num_vars {} (lit={lit:?})",
            var.index(),
            self.num_vars,
        );
        debug_assert!(
            !self.chrono_enabled,
            "BUG: enqueue_bcp_nochrono called with chrono_enabled=true"
        );
        // Phase saving.
        self.phase[var.index()] = lit.sign_i8();
        // No ChrBT: assignment level is always decision_level.
        let assigned_level = dl;
        let assigned_reason = reason.0;
        // vals[] update.
        ay_prefetch::val_set(&mut self.vals, lit.index(), 1);
        ay_prefetch::val_set(&mut self.vals, lit.negated().index(), -1);
        // VarData struct store (Kissat inlineassign.h pattern).
        let preserved_flags = self.var_data[var.index()].flags & VarData::FLAG_SEEN_PUB;
        self.var_data[var.index()] = VarData {
            level: assigned_level,
            trail_pos: self.trail.len() as u32,
            reason: assigned_reason,
            flags: preserved_flags,
            _pad: [0; 3],
        };
        // Reason marking deferred (#8569): see enqueue() comment.
        self.trail.push(lit);
        self.watches.prefetch_first(lit.negated());
    }

    /// Ensure `trail.capacity() >= num_vars` so the unsafe BCP loop may use
    /// the unchecked trail push (`assign_bcp_unchecked`, #shave7). Safe code
    /// (Vec::reserve); one predictable branch per propagate call, a no-op
    /// after the first call unless `num_vars` grew.
    #[inline]
    pub(super) fn reserve_trail_for_bcp(&mut self) {
        if self.trail.capacity() < self.num_vars {
            let len = self.trail.len();
            self.trail.reserve(self.num_vars - len);
        }
    }

    /// Stripped-down binary enqueue for BCP when ChrBT is disabled (#8465).
    ///
    /// Same as enqueue_bcp_nochrono but sets FLAG_BINARY_REASON.
    ///
    /// REQUIRES: chrono_enabled == false, variable is unassigned
    #[inline(always)]
    pub(super) fn enqueue_bcp_binary_nochrono(&mut self, lit: Literal, reason: ClauseRef) {
        let var = lit.variable();
        let dl = self.decision_level;
        debug_assert!(
            var.index() < self.num_vars,
            "BUG: enqueue_bcp_binary_nochrono variable index {} >= num_vars {} (lit={lit:?})",
            var.index(),
            self.num_vars,
        );
        debug_assert!(
            !self.chrono_enabled,
            "BUG: enqueue_bcp_binary_nochrono called with chrono_enabled=true"
        );
        // Phase saving.
        self.phase[var.index()] = lit.sign_i8();
        // No ChrBT: assignment level is always decision_level.
        let assigned_level = dl;
        let assigned_reason = reason.0;
        // vals[] update.
        ay_prefetch::val_set(&mut self.vals, lit.index(), 1);
        ay_prefetch::val_set(&mut self.vals, lit.negated().index(), -1);
        // VarData struct store with FLAG_BINARY_REASON pre-set.
        let preserved_flags = (self.var_data[var.index()].flags & VarData::FLAG_SEEN_PUB)
            | VarData::FLAG_BINARY_REASON_PUB;
        self.var_data[var.index()] = VarData {
            level: assigned_level,
            trail_pos: self.trail.len() as u32,
            reason: assigned_reason,
            flags: preserved_flags,
            _pad: [0; 3],
        };
        // Reason marking deferred (#8569): see enqueue() comment.
        self.trail.push(lit);
        self.watches.prefetch_first(lit.negated());
    }

    /// IC3-optimized long-clause enqueue (#8569 Gap 2).
    ///
    /// Maximally stripped for IC3 short queries. Compared to enqueue_bcp_nochrono:
    /// - No phase saving (IC3 uses forced phases via set_phase; BCP writes wasted)
    /// - No watch prefetch (IC3 working set fits in L1; prefetch is overhead)
    ///
    /// REQUIRES: ic3_mode, chrono_enabled == false, variable is unassigned
    /// ENSURES: same assignment semantics as enqueue_bcp_nochrono
    #[inline(always)]
    pub(super) fn enqueue_bcp_ic3(&mut self, lit: Literal, reason: ClauseRef) {
        let var = lit.variable();
        let dl = self.decision_level;
        debug_assert!(
            var.index() < self.num_vars,
            "BUG: enqueue_bcp_ic3 variable index {} >= num_vars {} (lit={lit:?})",
            var.index(),
            self.num_vars,
        );
        debug_assert!(
            self.cold.ic3_mode,
            "BUG: enqueue_bcp_ic3 called without ic3_mode"
        );
        // No phase saving: IC3 uses forced phases (set_phase), so BCP phase
        // writes are wasted. GipSAT doesn't save phases either.
        // No ChrBT: assignment level is always decision_level.
        let assigned_level = dl;
        let assigned_reason = reason.0;
        // vals[] update.
        ay_prefetch::val_set(&mut self.vals, lit.index(), 1);
        ay_prefetch::val_set(&mut self.vals, lit.negated().index(), -1);
        // VarData struct store (Kissat inlineassign.h pattern).
        let preserved_flags = self.var_data[var.index()].flags & VarData::FLAG_SEEN_PUB;
        self.var_data[var.index()] = VarData {
            level: assigned_level,
            trail_pos: self.trail.len() as u32,
            reason: assigned_reason,
            flags: preserved_flags,
            _pad: [0; 3],
        };
        // Reason marking deferred (#8569): see enqueue() comment.
        self.trail.push(lit);
        // No watch prefetch: IC3 working set fits in L1 cache.
    }

    /// IC3-optimized binary-clause enqueue (#8569 Gap 2).
    ///
    /// Maximally stripped for IC3 short queries. Compared to enqueue_bcp_binary_nochrono:
    /// - No phase saving (IC3 uses forced phases via set_phase)
    /// - No watch prefetch (IC3 working set fits in L1)
    ///
    /// REQUIRES: ic3_mode, chrono_enabled == false, variable is unassigned
    /// ENSURES: same assignment semantics as enqueue_bcp_binary_nochrono
    #[inline(always)]
    pub(super) fn enqueue_bcp_binary_ic3(&mut self, lit: Literal, reason: ClauseRef) {
        let var = lit.variable();
        let dl = self.decision_level;
        debug_assert!(
            var.index() < self.num_vars,
            "BUG: enqueue_bcp_binary_ic3 variable index {} >= num_vars {} (lit={lit:?})",
            var.index(),
            self.num_vars,
        );
        debug_assert!(
            self.cold.ic3_mode,
            "BUG: enqueue_bcp_binary_ic3 called without ic3_mode"
        );
        // No phase saving: IC3 uses forced phases (set_phase).
        // No ChrBT: assignment level is always decision_level.
        let assigned_level = dl;
        let assigned_reason = reason.0;
        // vals[] update.
        ay_prefetch::val_set(&mut self.vals, lit.index(), 1);
        ay_prefetch::val_set(&mut self.vals, lit.negated().index(), -1);
        // VarData struct store with FLAG_BINARY_REASON pre-set.
        let preserved_flags = (self.var_data[var.index()].flags & VarData::FLAG_SEEN_PUB)
            | VarData::FLAG_BINARY_REASON_PUB;
        self.var_data[var.index()] = VarData {
            level: assigned_level,
            trail_pos: self.trail.len() as u32,
            reason: assigned_reason,
            flags: preserved_flags,
            _pad: [0; 3],
        };
        // Reason marking deferred (#8569): see enqueue() comment.
        self.trail.push(lit);
        // No watch prefetch: IC3 working set fits in L1 cache.
    }

    /// Stripped-down binary-reason enqueue for BCP when ChrBT is disabled (#8465).
    ///
    /// Same as enqueue_binary_reason but skips ChrBT assignment level
    /// computation. Still does jump reason chain shortening.
    ///
    /// REQUIRES: chrono_enabled == false, SEARCH mode, decision_level > 0
    #[inline(always)]
    pub(super) fn enqueue_binary_reason_nochrono(&mut self, lit: Literal, mut reason_lit: Literal) {
        let var = lit.variable();
        let dl = self.decision_level;
        debug_assert!(
            var.index() < self.num_vars,
            "BUG: enqueue_binary_reason_nochrono variable index {} >= num_vars {} (lit={lit:?})",
            var.index(),
            self.num_vars,
        );
        debug_assert!(
            !self.chrono_enabled,
            "BUG: enqueue_binary_reason_nochrono called with chrono_enabled=true"
        );
        debug_assert!(dl > 0, "BUG: enqueue_binary_reason_nochrono at level 0");
        // Jump reason chain shortening (Kissat fastassign.h:12-19).
        let other_var = reason_lit.variable().index();
        if other_var < self.num_vars {
            let other_vd = self.var_data[other_var];
            if other_vd.is_binary_reason() {
                reason_lit = Literal(binary_reason_lit(other_vd.reason));
                self.stats.jumped_reasons += 1;
            }
        }
        // Phase saving.
        self.phase[var.index()] = lit.sign_i8();
        // No ChrBT: assignment level is always decision_level.
        let assigned_level = dl;
        // vals[] update.
        ay_prefetch::val_set(&mut self.vals, lit.index(), 1);
        ay_prefetch::val_set(&mut self.vals, lit.negated().index(), -1);
        // VarData struct store with binary reason flag.
        let preserved_flags = (self.var_data[var.index()].flags & VarData::FLAG_SEEN_PUB)
            | VarData::FLAG_BINARY_REASON_PUB;
        self.var_data[var.index()] = VarData {
            level: assigned_level,
            trail_pos: self.trail.len() as u32,
            reason: make_binary_reason(reason_lit.0),
            flags: preserved_flags,
            _pad: [0; 3],
        };
        // Binary literal reason — not a clause reason, no mark needed.
        self.trail.push(lit);
        self.watches.prefetch_first(lit.negated());
    }

    /// Enqueue a binary propagation with a literal reason (#8034).
    ///
    /// Kissat fastassign.h:12-19: stores a tagged literal in `VarData.reason`
    /// instead of a `ClauseRef`. The reason literal is the OTHER (false)
    /// literal from the binary clause. Jump reasons: if the reason literal's
    /// own reason is also binary, store the transitive reason to shorten
    /// reason chains (reducing arena dereferences during conflict analysis).
    ///
    /// REQUIRES: variable is unassigned, SEARCH mode, decision_level > 0, LRAT disabled
    /// ENSURES: variable assigned with binary literal reason
    #[inline(always)]
    pub(super) fn enqueue_binary_reason(&mut self, lit: Literal, mut reason_lit: Literal) {
        let var = lit.variable();
        let dl = self.decision_level;
        debug_assert!(
            var.index() < self.num_vars,
            "BUG: enqueue_binary_reason variable index {} >= num_vars {} (lit={lit:?}) — \
             stale literal after compaction or arena GC? (#8359)",
            var.index(),
            self.num_vars,
        );
        // Safety net (#8359, #8382): skip stale literals after compaction.
        // Debug-only in release builds (#8465): the bounds check adds a branch
        // per propagation. The invariant is maintained by construction.
        #[cfg(debug_assertions)]
        if var.index() >= self.num_vars {
            self.stats.stale_enqueue_skips += 1;
            tracing::warn!(
                "stale literal in enqueue_binary_reason: var {} >= num_vars {} (lit={:?})",
                var.index(),
                self.num_vars,
                lit
            );
            return;
        }
        debug_assert!(
            self.trail.len() < self.num_vars,
            "BUG: enqueue_binary_reason would exceed num_vars ({}) -- trail already has {} entries",
            self.num_vars,
            self.trail.len(),
        );
        debug_assert!(
            !self.var_is_assigned(var.index()),
            "BUG: enqueue_binary_reason of already-assigned variable {} (lit {:?})",
            var.index(),
            lit
        );
        debug_assert!(dl > 0, "BUG: enqueue_binary_reason at level 0");
        // Jump reason: if the reason literal's own reason is also binary,
        // follow the chain one step. This shortens reason chains, reducing
        // arena dereferences during conflict analysis. Kissat fastassign.h:12-19.
        let other_var = reason_lit.variable().index();
        // Safety net (#8382): stale reason literal after compaction.
        if other_var >= self.num_vars {
            self.stats.stale_enqueue_skips += 1;
            tracing::warn!(
                "stale reason literal in enqueue_binary_reason: reason_var {} >= num_vars {}",
                other_var,
                self.num_vars
            );
            return;
        }
        let other_vd = self.var_data[other_var];
        if other_vd.is_binary_reason() {
            reason_lit = Literal(binary_reason_lit(other_vd.reason));
            self.stats.jumped_reasons += 1;
        }
        // Phase saving: always active during search BCP.
        self.phase[var.index()] = lit.sign_i8();
        // ChrBT assignment level: for binary reasons, the assignment level
        // is the reason literal's level (single other literal in the clause).
        let assigned_level = if self.chrono_enabled {
            let reason_level = self.var_data[reason_lit.variable().index()].level;
            if self.lit_val(reason_lit) < 0 {
                reason_level.min(dl)
            } else {
                0
            }
        } else {
            dl
        };
        if assigned_level == 0 && !self.var_lifecycle.is_inactive(var.index()) {
            self.fixed_count += 1;
            self.var_lifecycle.mark_fixed(var.index());
            self.l0_gc_dirty[var.index()] = true;
        }
        // vals[] update.
        ay_prefetch::val_set(&mut self.vals, lit.index(), 1);
        ay_prefetch::val_set(&mut self.vals, lit.negated().index(), -1);
        debug_assert!(
            assigned_level <= dl,
            "BUG: assignment_level {assigned_level} exceeds decision_level {dl} for {lit:?}"
        );
        // Single struct store with binary reason flag pre-set (#8042).
        // Preserve seen flag (conflict analysis marks persist across re-assign).
        let preserved_flags = (self.var_data[var.index()].flags & VarData::FLAG_SEEN_PUB)
            | VarData::FLAG_BINARY_REASON_PUB;
        self.var_data[var.index()] = VarData {
            level: assigned_level,
            trail_pos: self.trail.len() as u32,
            reason: make_binary_reason(reason_lit.0),
            flags: preserved_flags,
            _pad: [0; 3],
        };
        // Binary literal reason — not a clause reason, no mark needed (#8100).
        self.trail.push(lit);
        // Prefetch watch list for next propagation step.
        self.watches.prefetch_first(lit.negated());
    }

    /// Make a decision (assign without reason, start new decision level)
    ///
    /// REQUIRES: variable not eliminated, variable unassigned
    /// ENSURES: decision_level incremented, trail_lim extended, literal enqueued with no reason
    #[inline]
    pub(super) fn decide(&mut self, lit: Literal) {
        // CaDiCaL propagate.cpp:188: all propagations complete before deciding
        debug_assert_eq!(
            self.qhead,
            self.trail.len(),
            "BUG: deciding {lit:?} with pending propagations (qhead={}, trail={})",
            self.qhead,
            self.trail.len(),
        );
        // O(1) check — must be assert!() because deciding on an eliminated
        // variable silently corrupts the search (stale watch lists, wrong model).
        assert!(
            !self.var_lifecycle.is_removed(lit.variable().index()),
            "BUG: decided removed variable {}",
            lit.variable().index()
        );
        self.decision_level += 1;
        // trail_lim monotonicity: each decision level's trail start must be >=
        // the previous level's start. Violation indicates a backtracking bug
        // that corrupted the trail/trail_lim correspondence (#4172).
        debug_assert!(
            self.trail_lim.is_empty()
                || *self.trail_lim.last().expect("invariant: non-empty") <= self.trail.len(),
            "BUG: trail_lim monotonicity violated: last={}, trail.len()={}",
            self.trail_lim.last().copied().unwrap_or(0),
            self.trail.len()
        );
        self.trail_lim.push(self.trail.len());
        self.num_decisions += 1;
        self.stats.record_decision_level(self.decision_level);
        if self.stable_mode {
            self.stats.stable_decisions += 1;
        } else {
            self.stats.focused_decisions += 1;
        }
        self.trace_decide(lit);
        self.enqueue(lit, None);
        solver_log!(
            self,
            "decide {} level {}",
            self.fmt_lit(lit),
            self.decision_level
        );
    }

    /// Pick the next decision variable, selecting between VSIDS (stable mode)
    /// and VMTF (focused mode). Checks for random decision injection first.
    /// Eliminated variables (BVE) are never returned.
    ///
    /// When a domain restriction is active (#8430), decisions are restricted
    /// to domain variables only. This is the core mechanism for IC3/PDR
    /// query acceleration: the solver only decides on cube-relevant variables,
    /// letting BCP handle the rest via propagation.
    #[inline]
    pub(super) fn pick_next_decision_variable(&mut self) -> Option<Variable> {
        // Domain-restricted path (#8430): when active, only decide on domain vars.
        // This takes priority over random decisions and the normal heuristic.
        // GipSAT rIC3 design: domain restriction applies at decision level > 0.
        if self.active_domain.is_some() {
            // Use decision_domain (original caller-provided domain) for decision
            // filtering (#8661). active_domain is expanded to include transitively
            // connected variables for BCP correctness, but decisions must still be
            // restricted to the original domain variables. Non-domain variables in
            // the expanded domain are handled by BCP propagation, not decisions.
            // Fall back to active_domain when decision_domain is not set (backward
            // compat for non-IC3 callers that use set_domain without expansion).
            let (domain, from_decision) = if self.decision_domain.is_some() {
                (self.decision_domain.take().unwrap(), true)
            } else {
                (self.active_domain.take().unwrap(), false)
            };
            let result = self.pick_domain_restricted_decision(&domain);
            if from_decision {
                self.decision_domain = Some(domain);
            } else {
                self.active_domain = Some(domain);
            }
            return result;
        }

        // Relevancy brancher (Increment 1): hybrid Scheme-A CNF-frontier
        // restriction. Engages ONLY while the search is wandering (past a
        // conflict warm-up + high decisions/conflicts ratio — see
        // `relevancy::relevancy_should_engage`); otherwise falls through to
        // unrestricted VSIDS below. Decisions-only: BCP and the model gate are
        // untouched, so this can never cause wrong-SAT/wrong-UNSAT (design §3).
        // A `None` result is the SAT signal (empty frontier), re-verified by the
        // authoritative model gate exactly like the IC3 domain path above.
        if self.relevancy_should_engage() {
            return self.pick_relevancy_frontier_decision();
        }

        #[cfg(debug_assertions)]
        if self.cold.ic3_mode {
            return self.pick_next_decision_variable_non_main();
        }

        #[cfg(debug_assertions)]
        self.debug_assert_main_decision_route_ready();

        self.pick_next_decision_variable_main()
    }

    #[cfg(debug_assertions)]
    #[inline]
    fn pick_next_decision_variable_non_main(&mut self) -> Option<Variable> {
        self.pick_next_decision_variable_main()
    }

    #[inline]
    pub(super) fn pick_next_decision_variable_main(&mut self) -> Option<Variable> {
        // Z3-style per-decision random frequency: with probability random_var_freq,
        // pick a random unassigned variable. Z3 SMT default: 0.01 (1%).
        if self.cold.random_var_freq > 0.0 {
            let mut rng = Random::new(self.num_decisions.wrapping_add(self.num_conflicts));
            if rng.generate_double() < self.cold.random_var_freq {
                let num_vars = self.num_vars;
                if num_vars > 0 {
                    for _ in 0..num_vars {
                        let idx = rng.pick(num_vars);
                        if !self.var_is_assigned(idx) && !self.var_lifecycle.is_removed(idx) {
                            self.stats.random_decisions += 1;
                            return Some(Variable(idx as u32));
                        }
                    }
                }
            }
        }

        // Try random decision injection (CaDiCaL-style burst)
        if let Some(var) = self.next_random_decision() {
            return Some(var);
        }
        let result = self.pick_branch_variable_by_active_heuristic();
        // CaDiCaL decide.cpp:186 — postcondition: returned variable is unassigned
        // and not eliminated. Catches heap corruption or stale assignment state.
        if let Some(var) = result {
            debug_assert!(
                !self.var_is_assigned(var.index()),
                "BUG: pick_next_decision_variable returned assigned variable {}",
                var.index()
            );
            debug_assert!(
                !self.var_lifecycle.is_removed(var.index()),
                "BUG: pick_next_decision_variable returned removed variable {}",
                var.index()
            );
        }
        result
    }

    /// Pick a decision variable restricted to the active domain (#8430).
    ///
    /// When no unassigned domain variable remains, returns `None` — the CDCL
    /// loop will then declare SAT (all domain vars assigned, the rest are
    /// don't-cares that BCP has already resolved or left unassigned).
    ///
    /// This is separate from `pick_branch_variable_by_active_heuristic` to keep
    /// the non-domain hot path free of per-decision bitmap checks.
    ///
    /// Implementation: for heap-based heuristics (EVSIDS/CHB), pop-and-filter
    /// from the heap, reinserting non-domain variables. For VMTF, scan domain
    /// variables directly (IC3 domains are typically 5-50 vars, so a linear
    /// scan is faster than walking the full VMTF linked list).
    pub(super) fn pick_domain_restricted_decision(&mut self, domain: &[bool]) -> Option<Variable> {
        // Bucket-queue fast path (#8476): O(1) amortized variable selection
        // for small domain-restricted IC3 queries.
        if self.bucket_queue_active {
            return self.vsids.pick_branching_variable_bucket(&self.vals);
        }

        match self.active_branch_heuristic {
            BranchHeuristic::Evsids | BranchHeuristic::Chb => {
                // Pop from the VSIDS heap, skipping non-domain variables.
                // Skipped variables are collected and reinserted after.
                let mut skipped: Vec<Variable> = Vec::new();
                let result = loop {
                    match self.vsids.pick_branching_variable(&self.vals) {
                        None => break None,
                        Some(var) if self.var_lifecycle.is_removed(var.index()) => {
                            self.vsids.remove_from_heap(var);
                        }
                        Some(var) => {
                            let idx = var.index();
                            if idx < domain.len() && domain[idx] {
                                break Some(var);
                            }
                            // Non-domain variable: pop it before saving for
                            // reinsertion. pick_branching_variable is a PEEK
                            // (it only lazily pops assigned vars) — without
                            // this pop the same top variable is returned
                            // forever: a non-terminating decision loop with an
                            // unbounded `skipped` Vec (observed: 8.3 GB RSS on
                            // hash_sat_08_04 under the relevancy-hard fused
                            // arm, killed only by the process watchdog).
                            self.vsids.remove_from_heap(var);
                            skipped.push(var);
                        }
                    }
                };
                for v in skipped {
                    self.vsids.insert_into_heap(v);
                }
                result
            }
            BranchHeuristic::Vmtf => {
                // VMTF uses a linked list, not a heap. Rather than walking the
                // entire list filtering by domain, scan domain vars directly.
                // IC3 domains are small (5-50 vars) so this is O(domain_size).
                let mut best: Option<Variable> = None;
                let mut best_order = 0u64;
                for (idx, &in_domain) in domain.iter().enumerate() {
                    if !in_domain {
                        continue;
                    }
                    if self.var_is_assigned(idx) || self.var_lifecycle.is_removed(idx) {
                        continue;
                    }
                    let order = self.vsids.bump_order(Variable(idx as u32));
                    if best.is_none() || order > best_order {
                        best = Some(Variable(idx as u32));
                        best_order = order;
                    }
                }
                best
            }
        }
    }

    #[cfg(debug_assertions)]
    #[inline]
    fn debug_assert_main_decision_route_ready(&self) {
        debug_assert!(
            !self.cold.ic3_mode,
            "BUG: Main decision route entered with ic3_mode"
        );
        debug_assert!(
            self.active_domain.is_none(),
            "BUG: Main decision route entered with active_domain"
        );
        debug_assert!(
            self.decision_domain.is_none(),
            "BUG: Main decision route entered with decision_domain"
        );
        debug_assert!(
            !self.bucket_queue_active,
            "BUG: Main decision route entered with bucket_queue_active"
        );
        debug_assert!(
            !self.probing_mode,
            "BUG: Main decision route entered with probing_mode"
        );
    }

    /// Start a new random decision burst. Sets burst length and schedules
    /// the next burst using CaDiCaL's phase * ln(phase) interval growth.
    pub(crate) fn start_random_sequence(&mut self) {
        let count = self.cold.random_decision_phases + 1;
        self.cold.random_decision_phases = count;

        // Burst length: RANDEC_LENGTH * ln(count + 10)
        let length = (RANDEC_LENGTH * ((count + 10) as f64).ln()) as u64;
        self.cold.randomized_deciding = length.max(1);

        // Schedule next burst: conflicts + phases * ln(phases) * RANDEC_INT
        let phases = self.cold.random_decision_phases as f64;
        let delta = phases * phases.ln();
        self.cold.next_random_decision = self
            .num_conflicts
            .saturating_add((delta * RANDEC_INT) as u64);
    }

    /// Check if a random decision should be made. Returns a random unassigned
    /// variable if we are in a random burst, or starts one if the conflict
    /// threshold is reached. CaDiCaL only enables this in focused mode.
    fn next_random_decision(&mut self) -> Option<Variable> {
        // Only inject random decisions in focused mode (CaDiCaL: randecfocused=1, randecstable=0)
        if self.stable_mode {
            return None;
        }

        // Not yet time for random decisions
        if self.num_conflicts < self.cold.next_random_decision {
            return None;
        }

        // Start a new random burst if not already in one
        if self.cold.randomized_deciding == 0 {
            // CaDiCaL decide.cpp:80: delay random burst start if too deep.
            // `level > assumptions.size()` — with no assumptions, only level 0.
            if self.decision_level > 0 {
                return None;
            }
            self.start_random_sequence();
        }

        // Pick a random unassigned, non-eliminated variable using LCG seeded from decisions
        let num_vars = self.num_vars;
        if num_vars == 0 {
            return None;
        }
        let mut rng = Random::new(self.num_decisions);
        for _ in 0..num_vars {
            let idx = rng.pick(num_vars);
            if !self.var_is_assigned(idx) && !self.var_lifecycle.is_removed(idx) {
                self.stats.random_decisions += 1;
                return Some(Variable(idx as u32));
            }
        }
        // All sampled vars are assigned or eliminated; fall through to normal decision
        None
    }

    /// Decrement the random decision burst counter on conflict.
    /// Called from conflict analysis paths to end the burst after enough conflicts.
    #[inline]
    pub(super) fn on_conflict_random_decision(&mut self) {
        self.poll_process_memory_limit();
        if self.cold.randomized_deciding > 0 {
            self.cold.randomized_deciding -= 1;
        }
    }

    /// Initialize 2-watched literals for all clauses, or incrementally attach
    /// watches for newly-appended clauses when the arena was preserved (#8374).
    pub(super) fn initialize_watches(&mut self) {
        // Check if we can do an incremental watch attach (case b in
        // reset_search_state: arena preserved, only new originals appended).
        let incremental_boundary = self.cold.incremental_watch_boundary.take();

        // Always clear dirty-watch state — the solve is starting fresh and any
        // stale dirty bits from the previous solve's clause deletions are
        // irrelevant (#8101).
        self.dirty_watches.iter_mut().for_each(|d| *d = false);
        self.dirty_watch_list.clear();

        let start_offset = incremental_boundary.unwrap_or(0);
        // Giant-mode memory lever (`AY_AB_GIANT_MEM`, default ON — see
        // `giant_mem_levers_enabled` below): collect the watch-init offsets
        // as u32, not usize. Arena offsets fit u32 by construction (the loop
        // body builds `ClauseRef(i as u32)` from the very same value); on the
        // SC2025 giants (157M/315M clauses) the usize collect was a
        // 1.26GB/2.5GB transient landing exactly at the peak-RSS moment.
        // The kill-switch path keeps the original usize collect; iteration
        // order and the loop body are bit-identical either way.
        let (narrow_offsets, wide_offsets): (Vec<u32>, Vec<usize>) = if giant_mem_levers_enabled() {
            (
                self.arena
                    .indices_from(start_offset)
                    .map(|i| i as u32)
                    .collect(),
                Vec::new(),
            )
        } else {
            (Vec::new(), self.arena.indices_from(start_offset).collect())
        };
        for i in narrow_offsets
            .into_iter()
            .map(|i| i as usize)
            .chain(wide_offsets)
        {
            let off = i;
            let clause_ref = ClauseRef(i as u32);
            // #8496: Skip dead clauses (garbage-bit or pending-garbage).
            // arena.indices_from() yields ALL clause offsets including dead
            // ones. len_of() returns the original lit_len even for clauses
            // marked pending-garbage (PENDING_GARBAGE_BIT set, lit_len > 0).
            // Without this check, pending-garbage clauses containing
            // eliminated variables would be watched, causing stale variable
            // references during BCP or false UNSAT in release builds.
            if self.arena.is_dead(off) {
                continue;
            }
            let clause_len = self.arena.len_of(off);
            // Catch eliminated variables in active clauses during watch init.
            #[cfg(debug_assertions)]
            if clause_len >= 2 {
                for j in 0..clause_len {
                    let lit = self.arena.literal(off, j);
                    debug_assert!(
                        !self.var_lifecycle.is_removed(lit.variable().index()),
                        "BUG: initialize_watches: active clause {off} (len={clause_len}, \
                         learned={}) contains eliminated variable {} at position {j}",
                        self.arena.is_learned(off),
                        lit.variable().index(),
                    );
                }
            }
            if clause_len >= 2 {
                let lit0 = self.arena.literal(off, 0);
                let mut lit1 = self.arena.literal(off, 1);
                // Guard: if the first two literals are identical, scan for a
                // distinct literal to watch (#6506). Duplicate literals can
                // enter the arena via theory propagation or inprocessing paths
                // that skip clause normalization. The 2WL scheme requires
                // distinct watch pointers so we must find a non-duplicate pair.
                if lit0 == lit1 {
                    let mut found = false;
                    for j in 2..clause_len {
                        let candidate = self.arena.literal(off, j);
                        if candidate != lit0 {
                            // Swap candidate into position 1 in the arena
                            self.arena.swap_literals(off, 1, j);
                            lit1 = candidate;
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        // All literals are identical — clause is effectively
                        // unit. Skip watch attachment (unit handled elsewhere).
                        continue;
                    }
                }
                let mut watched = [lit0, lit1];
                let watched = self
                    .prepare_watched_literals(&mut watched, WatchOrderPolicy::Preserve)
                    .expect("initialize_watches requires clauses with len >= 2");
                self.attach_clause_watches(clause_ref, watched, clause_len == 2);
            }
        }
        // Binary-first invariant is maintained incrementally on insert.
        self.watches.debug_assert_binary_first();
    }

    /// Propagate unit clauses using 2-watched literals.
    /// Propagate and check for UNSAT: returns `true` if `has_empty_clause`
    /// is set or propagation discovers a conflict at decision level 0.
    ///
    /// When a level-0 propagation conflict is found, records the BCP resolution
    /// chain for LRAT proof generation (#4397).
    ///
    /// Used as the standard inprocessing guard after any technique that may
    /// produce unit clauses or derive empty clauses.
    #[inline]
    pub(super) fn propagate_check_unsat(&mut self) -> bool {
        if self.has_empty_clause {
            return true;
        }
        // Post-rebuild BCP timing (#8103): start timer if measurement pending.
        let post_rebuild_timer = if self.cold.post_rebuild_bcp_pending {
            Some(ay_core::time::Instant::now())
        } else {
            None
        };
        // Level-0 propagation after inprocessing: no probing_mode, no vivify
        // flags — use the lightweight search variant.
        let result = if let Some(conflict_ref) = self.search_propagate() {
            self.record_level0_conflict_chain(conflict_ref);
            true
        } else {
            false
        };
        // Capture post-rebuild BCP cache behavior measurement (#8103).
        // If rebuild_watches set the pending flag, this propagate call used the
        // freshly-built sequential watch layout. Record the timing delta.
        if let Some(timer) = post_rebuild_timer {
            let is_full = self.cold.post_rebuild_is_full;
            self.cold.post_rebuild_bcp_pending = false;
            let elapsed_ns = timer.elapsed().as_nanos() as u64;
            let props_delta = self
                .num_propagations
                .saturating_sub(self.cold.post_rebuild_props_baseline);
            // Combined counters (both paths).
            self.stats.post_rebuild_bcp_ns =
                self.stats.post_rebuild_bcp_ns.saturating_add(elapsed_ns);
            self.stats.post_rebuild_bcp_propagations = self
                .stats
                .post_rebuild_bcp_propagations
                .saturating_add(props_delta);
            // Path-specific counters (#8103): distinguish full rebuild from
            // incremental reconnect to compare cache behavior.
            if is_full {
                self.stats.post_full_rebuild_bcp_ns = self
                    .stats
                    .post_full_rebuild_bcp_ns
                    .saturating_add(elapsed_ns);
                self.stats.post_full_rebuild_bcp_propagations = self
                    .stats
                    .post_full_rebuild_bcp_propagations
                    .saturating_add(props_delta);
            } else {
                self.stats.post_incremental_reconnect_bcp_ns = self
                    .stats
                    .post_incremental_reconnect_bcp_ns
                    .saturating_add(elapsed_ns);
                self.stats.post_incremental_reconnect_bcp_propagations = self
                    .stats
                    .post_incremental_reconnect_bcp_propagations
                    .saturating_add(props_delta);
            }
        }
        result
    }

    /// Probe-specialized propagation with probe-parent tracking and HBR support.
    ///
    /// Always uses safe BCP even with `raw-pointer-bcp` enabled: HBR during PROBE
    /// can call `add_watch(false_lit, ...)` which may reallocate the watch list
    /// Vec, invalidating raw pointers. The safe version avoids this by swapping
    /// the list out first. PROBE mode is rare and not performance-critical.
    #[inline]
    pub(super) fn probe_propagate(&mut self) -> Option<ClauseRef> {
        // Invalidate reason marks before BCP (#8569): BCP enqueue functions no
        // longer call mark_reason_clause(), so marks become stale after any
        // propagation. Consumers call ensure_reason_clause_marks_current()
        // which rebuilds from the trail.
        self.reason_marks_invalidated = true;
        self.propagate_bcp::<{ bcp_mode::PROBE }>()
    }

    /// Legacy propagation entry point kept for compatibility with tests and
    /// verification harnesses.
    #[cfg(any(test, kani))]
    #[inline]
    pub(super) fn propagate(&mut self) -> Option<ClauseRef> {
        // Invalidate reason marks before BCP (#8569): see probe_propagate.
        self.reason_marks_invalidated = true;
        self.propagate_bcp::<{ bcp_mode::PROBE }>()
    }

    /// Search-specialized BCP propagation — no probing or vivification overhead.
    ///
    /// The default route uses safe deferred-buffer BCP. The experimental
    /// in-place watch scan route is SEARCH-only and must be explicitly enabled
    /// through solver config in `raw-pointer-bcp` builds.
    ///
    /// Domain-restricted dispatch (#8475): when an active domain is set and
    /// `decision_level > 0`, uses `propagate_domain_bcp` which skips clauses
    /// with non-domain watched literals. At level 0, full BCP is always used
    /// for complete unit propagation. IC3/PDR queries set the domain to a small
    /// cube (5-50 vars) in a system with thousands of variables; domain BCP
    /// skips ~25x fewer clauses by treating non-domain watchers as satisfied.
    #[inline]
    pub(super) fn search_propagate(&mut self) -> Option<ClauseRef> {
        // Invalidate reason marks before BCP (#8569): BCP enqueue functions no
        // longer call mark_reason_clause(), so marks become stale after any
        // propagation. Consumers call ensure_reason_clause_marks_current()
        // which rebuilds from the trail. Single bool write — zero hot-path cost.
        self.reason_marks_invalidated = true;
        // Domain-restricted BCP (#8475): when active domain is set and we are
        // above level 0, use domain BCP. At level 0, full BCP is required for
        // soundness (complete unit propagation). Skip JIT paths for domain BCP:
        // IC3 queries are tiny and don't benefit from JIT compilation overhead.
        if self.decision_level > 0 && self.active_domain.is_some() {
            let domain = self.active_domain.take().expect("just checked is_some");
            // IC3 domain BCP breakpoint (#8802): for small IC3 formulas, the
            // bitmap/filter overhead is larger than the clause-scan savings.
            // Keep the domain for decision filtering, but use full BCP below
            // the configured threshold.
            let result = if !self.should_use_domain_bcp_for(&domain) {
                self.search_propagate_full_bcp_with_domain()
            } else if self.cold.ic3_mode {
                // IC3-optimized BCP (#8569 Gap 2): when ic3_mode is enabled,
                // use the stripped BCP that removes tick accounting, binary
                // conflict deferral, saved position, garbage check, prefetch,
                // probe/vivify paths, and jump reasons. This is 3-10x faster
                // for the short queries (0-5 conflicts) that IC3/PDR makes.
                self.propagate_bcp_ic3(&domain)
            } else {
                self.propagate_domain_bcp(&domain)
            };
            self.active_domain = Some(domain);
            return result;
        }
        #[cfg(debug_assertions)]
        if self.cold.ic3_mode
            || self.active_domain.is_some()
            || self.decision_domain.is_some()
            || self.bucket_queue_active
            || self.probing_mode
        {
            return self.search_propagate_non_main_full();
        }
        // Legacy BCP JIT dispatch removed (#8517). Standard 2WL BCP is always used.
        //
        // Recovery (#7991): if JIT watches were detached by a prior compilation
        // that has since been invalidated, reattach them before standard BCP.

        self.search_propagate_standard()
    }

    #[inline]
    fn search_propagate_full_bcp_with_domain(&mut self) -> Option<ClauseRef> {
        self.search_propagate_full_bcp_route()
    }

    #[inline]
    fn search_propagate_full_bcp_route(&mut self) -> Option<ClauseRef> {
        #[cfg(feature = "raw-pointer-bcp")]
        if self.bcp_search_inplace_watch_scan_route_enabled() {
            self.stats.record_bcp_search_inplace_watch_scan_exercised();
            return self.propagate_bcp_unsafe_search();
        }

        self.propagate_bcp::<{ bcp_mode::SEARCH }>()
    }

    #[cfg(debug_assertions)]
    #[inline]
    fn search_propagate_non_main_full(&mut self) -> Option<ClauseRef> {
        self.search_propagate_full_bcp_route()
    }

    /// Standard 2WL BCP used by search propagation.
    #[inline]
    pub(super) fn search_propagate_standard(&mut self) -> Option<ClauseRef> {
        #[cfg(debug_assertions)]
        self.debug_assert_main_standard_route_ready();

        self.search_propagate_full_bcp_route()
    }

    #[cfg(debug_assertions)]
    #[inline]
    fn debug_assert_main_standard_route_ready(&self) {
        debug_assert!(
            !self.cold.ic3_mode,
            "BUG: Main standard propagation entered with ic3_mode"
        );
        debug_assert!(
            self.active_domain.is_none(),
            "BUG: Main standard propagation entered with active_domain"
        );
        debug_assert!(
            self.decision_domain.is_none(),
            "BUG: Main standard propagation entered with decision_domain"
        );
        debug_assert!(
            !self.bucket_queue_active,
            "BUG: Main standard propagation entered with bucket_queue_active"
        );
        debug_assert!(
            !self.probing_mode,
            "BUG: Main standard propagation entered with probing_mode"
        );
    }

    /// Vivification-specialized BCP propagation — vivify-skip check, no probing.
    ///
    /// When the `raw-pointer-bcp` feature is enabled, dispatches to the
    /// CaDiCaL-exact raw-pointer implementation for maximum throughput.
    #[inline]
    pub(super) fn vivify_propagate(&mut self) -> Option<ClauseRef> {
        // Invalidate reason marks before BCP (#8569): see search_propagate.
        self.reason_marks_invalidated = true;
        #[cfg(feature = "raw-pointer-bcp")]
        {
            self.propagate_bcp_unsafe_vivify()
        }
        #[cfg(not(feature = "raw-pointer-bcp"))]
        {
            self.propagate_bcp::<{ bcp_mode::VIVIFY }>()
        }
    }
}

/// Kill-switch `AY_AB_GIANT_MEM` (default ON; unset or `=1` enables, any
/// other explicit value disables — conservative parse matching
/// `AY_AB_SUBST_AUTO_GIANT`): giant-instance peak-RSS levers. In this crate
/// it narrows the `initialize_watches` offset collect to u32 (a 1.26GB/2.5GB
/// usize transient on the SC2025 giants); the `ay` crate reads the same env
/// var to drop the DIMACS file buffer after parse. Memory-width/lifetime
/// only — verdicts, stats, iteration order and certificates are unchanged.
/// Cached OnceLock per the #8506 no-per-call-syscall convention.
pub(crate) fn giant_mem_levers_enabled() -> bool {
    use std::sync::OnceLock;
    static GIANT_MEM: OnceLock<bool> = OnceLock::new();
    *GIANT_MEM.get_or_init(|| {
        std::env::var("AY_AB_GIANT_MEM")
            .map(|v| v == "1")
            .unwrap_or(true)
    })
}
