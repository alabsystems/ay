// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Relevancy-propagation brancher — Increment 1 (Scheme A, CNF frontier).
//!
//! See the development design notes.
//!
//! # What "relevant" means
//!
//! Under a partial assignment, a variable is **relevant** iff it occurs, still
//! unassigned, in at least one currently-UNSATISFIED clause (a clause with no
//! true literal) — the "CNF frontier". A variable in no unsatisfied clause
//! cannot change whether any clause becomes satisfied, so it is a don't-care for
//! the *current* node. When the frontier is empty every clause already has a
//! true literal, so the partial assignment (unassigned vars filled with any
//! fixed default) is a model → SAT. This scheme is exactly sound and complete
//! for pure SAT (design §2.1).
//!
//! # SOUNDNESS-INVARIANT (design §3, non-negotiable)
//!
//! Relevancy gates **decisions only**. BCP still propagates over every clause
//! and every variable; SAT is reported only through the always-on model gate
//! (`first_model_violation`). Consequences:
//!   * A wrong don't-care (frontier too small) degrades at worst to `unknown`
//!     (the model gate rejects a non-model), never wrong-SAT.
//!   * No wrong-UNSAT: the frontier never closes a branch and never narrows
//!     BCP, so every genuine implication/conflict is still derived. This is
//!     exactly what the IC3 `set_domain` machinery learned the hard way —
//!     restricting *propagation* to the raw domain caused 33/50 HWMCC
//!     false-UNSAT; restricting *decisions* only does not.
//!
//! # HYBRID trip-wire (design §5.2a)
//!
//! A *hard* decision-restriction regressed one baseline-easy instance
//! (`hash_sat_09_11`, sat→timeout) by trajectory change. So relevancy is
//! consulted ONLY while the SAT search is WANDERING: past a conflict warm-up AND
//! with a high decisions/conflicts ratio (à la the existing `wander_hand_to_vsids`
//! latch). Instances VSIDS already solves quickly (few conflicts) never engage
//! relevancy and keep their baseline trajectory. Verified: `hash_sat_09_11` is
//! **byte-identical** on/off (143 conflicts / 5273 decisions) — the trip-wire
//! keeps it out — so this brancher is 0-regression by construction on the
//! baseline-easy instances.
//!
//! # Engagement (measured reality) and the hybrid arm routing
//!
//! The design prototype (§5) collapsed the Hash reds in the **lazy** regime
//! (plain per-round SAT solves), where every decision flows through
//! `pick_next_decision_variable` and relevancy restricts it. The QF_UFLIA
//! lane's default **eager** arm starves that hook: the theory's
//! `suggest_decision` claims ~every decision, and its picks are always in an
//! unsatisfied clause (relevant), so a per-atom filter is inert. Relevancy is
//! therefore deployed via ARM ROUTING (`uflia_split_arm`, ay-dpll
//! combined/mod.rs, #relevancy-lazy-routing): the eager attempt runs with the
//! `arm_wander_abort` trip-wire; when it WANDERS, the check-sat re-runs on the
//! lazy arm with relevancy HARD (`set_relevancy_hard`), the frontier-empty SAT
//! signal, phase-based don't-care completion (`relevancy_completed_model`),
//! and the sparse theory hand-off (only SAT-assigned atoms asserted).
//! Instances the eager arm solves without wandering keep byte-identical
//! trajectories. In the eager solve itself, engaged relevancy also suppresses
//! theory-aware branching (theory_backend.rs / assumptions.rs) — env-opt-in
//! only, theory propagation untouched.
//!
//! Measured (65-file Hash + 49-file Wisa sweeps, `-t 12000`): the hybrid
//! converts `hash_sat_03_11` (timeout→sat, ~2s, 781 conflicts vs baseline sat
//! only at ~59s) plus Wisa conversions (`xs_11_16` unknown→sat, `xs_10_20`
//! unknown→unsat, both z3-verified), with every both-sat instance
//! byte-identical (`hash_sat_09_11`: 143 conflicts / 5273 decisions on/off).
//! Residual: most Hash reds stay unknown — the lazy one-lemma-per-round
//! feedback converges only on smaller instances (design Increments 3-5).

use super::*;
use std::sync::OnceLock;

/// Cached hybrid trip-wire configuration for the relevancy brancher.
#[derive(Clone, Copy)]
struct RelevancyConfig {
    /// Minimum conflicts before relevancy may engage (VSIDS-first warm-up).
    /// Must exceed the conflict count at which VSIDS solves the baseline-easy
    /// wanderers (e.g. `hash_sat_09_11` finishes at 143 conflicts). Overridable
    /// via `AY_RELEVANCY_WARMUP`.
    warmup_conflicts: u64,
    /// Minimum decisions/conflicts ratio to count as "wandering". Conflict-driven
    /// solves (low ratio → VSIDS learning is productive) are left to VSIDS.
    /// Overridable via `AY_RELEVANCY_RATIO`.
    wander_ratio: u64,
    /// Verbose: emit one line on the first engaged decision per solver.
    /// Enabled by `--sat-relevancy`.
    verbose: bool,
}
/// Relevancy warmup, in conflicts (B4: was AY_RELEVANCY_WARMUP).
const RELEVANCY_WARMUP_CONFLICTS: u64 = 200;
/// Wander ratio denominator (B4: was AY_RELEVANCY_RATIO).
const RELEVANCY_WANDER_RATIO: u64 = 5;

/// Process-cached relevancy config. Each solver run is a fresh process, so a
/// `OnceLock` read of the env is correct and keeps the decision hot path free of
/// per-decision `getenv` syscalls.
fn relevancy_config() -> RelevancyConfig {
    static CFG: OnceLock<RelevancyConfig> = OnceLock::new();
    *CFG.get_or_init(|| {
        // B4: the AY_RELEVANCY_{WARMUP,RATIO} env overrides are deleted.
        let warmup_conflicts = RELEVANCY_WARMUP_CONFLICTS;
        let wander_ratio = RELEVANCY_WANDER_RATIO;
        let verbose = ay_core::misc_cli_flags().sat_relevancy == Some(2);
        RelevancyConfig {
            warmup_conflicts,
            wander_ratio,
            verbose,
        }
    })
}

/// Cached wander-abort thresholds (see `check_wander_abort`).
#[derive(Clone, Copy)]
struct WanderAbortConfig {
    min_conflicts: u64,
    min_decisions: u64,
    min_ratio: u64,
}

fn wander_abort_config() -> WanderAbortConfig {
    static CFG: OnceLock<WanderAbortConfig> = OnceLock::new();
    fn env_u64(name: &str, default: u64) -> u64 {
        std::env::var(name)
            .ok()
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(default)
    }
    *CFG.get_or_init(|| WanderAbortConfig {
        min_conflicts: env_u64("AY_WANDER_ABORT_CONFLICTS", 300),
        min_decisions: env_u64("AY_WANDER_ABORT_DECISIONS", 20_000),
        min_ratio: env_u64("AY_WANDER_ABORT_RATIO", 8),
    })
}

impl Solver {
    /// Enable/disable the relevancy brancher for this solver.
    ///
    /// Wired by the QF_UFLIA split-loop lane (env-gated). Off by default; the
    /// hybrid trip-wire still governs whether it actually engages per decision.
    pub fn set_relevancy_branching(&mut self, enabled: bool) {
        self.relevancy_branching = enabled;
    }

    /// Number of decisions taken under relevancy restriction (observability).
    #[inline]
    pub fn relevancy_decisions(&self) -> u64 {
        self.relevancy_decisions
    }

    /// Explicit tri-state env override for relevancy branching.
    ///
    /// `--sat-relevancy` => `Some(false)` (kill switch, beats any caller default);
    /// `--sat-relevancy 1|2` => `Some(true)` (`2` also enables the engage
    /// marker); `--sat-relevancy 0` => `Some(false)`; unset => `None` (caller
    /// decides the default). B36: was the --sat-relevancy tri-state env.
    pub fn relevancy_env_override() -> Option<bool> {
        match ay_core::misc_cli_flags().sat_relevancy {
            Some(0) => Some(false),
            Some(_) => Some(true),
            None => None,
        }
    }

    /// Whether the split-loop lanes should enable the relevancy brancher when
    /// the caller supplies no default (Increment 1 semantics: OFF unless
    /// `--sat-relevancy 1|2`).
    pub fn relevancy_env_enabled() -> bool {
        Self::relevancy_env_override().unwrap_or(false)
    }

    /// Set relevancy HARD mode: engage the frontier restriction on EVERY
    /// decision, skipping the warm-up / wander-ratio trip-wire. Used by the
    /// UFLIA hybrid's lazy fallback (the eager first attempt already served
    /// the baseline-easy instances, so the prototype-faithful hard
    /// restriction is safe there).
    pub fn set_relevancy_hard(&mut self, hard: bool) {
        self.relevancy_hard = hard;
    }

    /// Whether the relevancy brancher should be consulted for the NEXT decision.
    ///
    /// The hybrid trip-wire (design §5.2a): engage only while the search is
    /// WANDERING — past a conflict warm-up and with a high decisions/conflicts
    /// ratio. VSIDS gets first crack; instances it solves quickly never engage.
    /// In HARD mode (`set_relevancy_hard`) the trip-wire is skipped entirely.
    #[inline]
    pub(super) fn relevancy_should_engage(&self) -> bool {
        if !self.relevancy_branching {
            return false;
        }
        if self.relevancy_hard {
            return true;
        }
        let cfg = relevancy_config();
        let conflicts = self.num_conflicts;
        if conflicts < cfg.warmup_conflicts {
            // VSIDS-first warm-up: the baseline-easy wanderers finish here.
            return false;
        }
        // Wandering = many decisions per conflict. `checked_div` guards
        // conflicts == 0 (unreachable here since conflicts >= warmup >= 1, but
        // stay defensive: treat "infinite" ratio as wandering).
        self.num_decisions
            .checked_div(conflicts)
            .is_none_or(|ratio| ratio >= cfg.wander_ratio)
    }

    /// Arm (or disarm) the wander-abort trip-wire for the NEXT solve attempt.
    ///
    /// Hybrid arm routing (UFLIA): the eager DPLL(T) attempt runs with this
    /// armed; when the search WANDERS (see `should_wander_abort`) the CDCL
    /// loops return Unknown and set the sticky `wander_abort_tripped` signal,
    /// which the executor reads to re-route the check-sat to the lazy arm with
    /// relevancy. Arming snapshots the conflict/decision baselines (counters
    /// accumulate across rounds on the persistent solver) and clears the
    /// sticky trip signal. Soundness-neutral: an aborted solve is `unknown`.
    pub fn arm_wander_abort(&mut self, armed: bool) {
        self.wander_abort_armed = armed;
        if armed {
            self.wander_abort_tripped = false;
            self.wander_abort_base_conflicts = self.num_conflicts;
            self.wander_abort_base_decisions = self.num_decisions;
        }
    }

    /// Whether an armed solve aborted on wander (sticky until re-armed).
    #[inline]
    pub fn wander_abort_tripped(&self) -> bool {
        self.wander_abort_tripped
    }

    /// Wander-abort trip check, called from the CDCL decision checkpoints
    /// (every 1000 decisions). Returns `true` — after setting the sticky
    /// signal — when the armed attempt has wandered past the thresholds:
    /// conflict delta >= `AY_WANDER_ABORT_CONFLICTS` (default 300), decision
    /// delta >= `AY_WANDER_ABORT_DECISIONS` (default 20000), and
    /// decisions/conflicts ratio >= `AY_WANDER_ABORT_RATIO` (default 8).
    /// Defaults chosen so the eager baseline-easy Hash instances (e.g.
    /// `hash_sat_09_11`: 143 conflicts / 5273 decisions total) can never trip.
    #[inline]
    pub(super) fn check_wander_abort(&mut self) -> bool {
        if !self.wander_abort_armed {
            return false;
        }
        // Saturating: per-solve counter restarts (preprocess_reset) can leave
        // the arm-time baselines above the live counters; a stale baseline
        // must degrade to "no trip yet", never panic/wrap.
        let dc = self
            .num_conflicts
            .saturating_sub(self.wander_abort_base_conflicts);
        let dd = self
            .num_decisions
            .saturating_sub(self.wander_abort_base_decisions);
        let cfg = wander_abort_config();
        if dc < cfg.min_conflicts || dd < cfg.min_decisions {
            return false;
        }
        if dd.checked_div(dc).is_none_or(|r| r >= cfg.min_ratio) {
            self.wander_abort_tripped = true;
            return true;
        }
        false
    }

    /// Model completion for relevancy-restricted SAT (#relevancy-lazy-routing).
    ///
    /// The frontier-empty SAT signal leaves don't-care variables UNASSIGNED.
    /// `get_model` completes them with `false`, which in the SMT split loop
    /// asserts a spurious NEGATIVE polarity for every don't-care theory atom
    /// (e.g. hundreds of disequalities the formula never required), swamping
    /// the lazy theory check with irrelevant obligations (measured:
    /// `hash_sat_03_11` diverged through 40k+ one-lemma refinement rounds).
    /// Completing from the SAVED PHASE instead keeps each don't-care at its
    /// last (theory-hinted) polarity — the split loop seeds phases from the
    /// previous round's LP-consistent theory model — so don't-cares stay
    /// theory-cheap.
    ///
    /// Soundness: identical status to `get_model` — the completion only fills
    /// genuine don't-cares (when the frontier is empty every clause already
    /// has a true ASSIGNED literal), and the always-on model gate re-verifies
    /// the completed model clause-by-clause either way; a bad completion can
    /// only degrade to `unknown`.
    pub(super) fn relevancy_completed_model(&self) -> Vec<bool> {
        if !self.relevancy_branching {
            return self.get_model();
        }
        (0..self.num_vars)
            .map(|v| match ay_prefetch::val_at(&self.vals, v * 2) {
                0 => self.phase[v] > 0,
                val => val > 0,
            })
            .collect()
    }

    /// Pick the next decision restricted to the relevancy frontier (Scheme A).
    ///
    /// Recomputes the CNF frontier and defers to the existing
    /// `pick_domain_restricted_decision`. Returns `None` when the frontier is
    /// empty — the partial assignment satisfies every live clause, i.e. it is a
    /// model (re-verified by the always-on model gate before SAT is reported).
    ///
    /// Returning `None` here is the SAT signal, exactly as the IC3 domain path
    /// (`pick_domain_restricted_decision` returning `None`) is.
    pub(super) fn pick_relevancy_frontier_decision(&mut self) -> Option<Variable> {
        // Take the scratch buffer out so the frontier fill and the domain-picker
        // can both borrow `self` without aliasing a `self` field.
        let mut buf = std::mem::take(&mut self.relevancy_buf);
        let any_relevant = self.fill_relevancy_frontier(&mut buf);
        let result = if any_relevant {
            self.pick_domain_restricted_decision(&buf)
        } else {
            // Empty frontier ⇒ every live clause has a true literal ⇒ SAT.
            None
        };
        self.relevancy_buf = buf;

        if result.is_some() {
            let first = self.relevancy_decisions == 0;
            self.relevancy_decisions += 1;
            if first && relevancy_config().verbose {
                // One-line engage marker (--sat-relevancy) for observability.
                ay_core::safe_eprintln!(
                    "[relevancy] engaged: conflicts={} decisions={} num_vars={}",
                    self.num_conflicts,
                    self.num_decisions,
                    self.num_vars
                );
            }
        }
        result
    }

    /// Fill `buf` (sized `num_vars`) with the current CNF relevancy frontier.
    ///
    /// Returns `true` iff at least one variable is relevant. Mirrors the
    /// authoritative model-gate clause walk (`live_indices`) so the empty-frontier
    /// SAT signal aligns with `first_model_violation`, minimising spurious
    /// `unknown`. A clause with a true literal is satisfied and contributes
    /// nothing; otherwise every UNASSIGNED, non-removed literal's variable is
    /// relevant. (At a decision point BCP has reached fixpoint, so every
    /// unsatisfied clause has ≥1 unassigned literal — design §2.1.)
    ///
    /// `buf` is passed by `&mut` (a caller-owned local, never a `self` field) so
    /// the clause walk can hold `&self` without a borrow conflict.
    fn fill_relevancy_frontier(&self, buf: &mut Vec<bool>) -> bool {
        buf.clear();
        buf.resize(self.num_vars, false);
        let lifecycle_len = self.var_lifecycle.len();
        let mut any = false;
        for idx in self.arena.live_indices() {
            let lits = self.arena.literals(idx);
            // Satisfied clause: contributes nothing to the frontier.
            if lits.iter().any(|&lit| self.lit_val(lit) > 0) {
                continue;
            }
            for &lit in lits {
                if self.lit_val(lit) != 0 {
                    continue; // assigned-false literal: not a decision candidate.
                }
                let vi = lit.variable().index();
                if vi >= buf.len() || buf[vi] {
                    continue;
                }
                // Exclude inprocessing-removed variables: they are never returned
                // by `pick_domain_restricted_decision`, so keeping the frontier's
                // "any" flag consistent with what the picker can actually return
                // avoids a spurious empty-frontier / non-empty-frontier mismatch.
                if vi < lifecycle_len && self.var_lifecycle.is_removed(vi) {
                    continue;
                }
                buf[vi] = true;
                any = true;
            }
        }
        any
    }
}
