// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::clause::ActionId;

/// A lemma blocking states at some frame level
#[derive(Debug, Clone)]
pub(crate) struct Lemma {
    /// Predicate this lemma is about
    pub(crate) predicate: PredicateId,
    /// The invariant formula (states that satisfy this predicate's constraint).
    /// Despite the old comment saying "blocking formula", this is actually the invariant:
    /// - Created via `NOT(generalized)` at lemma construction
    /// - cumulative_frame_constraint returns AND of these formulas
    /// - The blocking formula is NOT(formula)
    pub(crate) formula: ChcExpr,
    /// Cached structural hash of `formula` for fast deduplication (#1037).
    pub(crate) formula_hash: u64,
    /// Frame level where this lemma was learned
    pub(crate) level: usize,
    /// If true, this lemma was verified algebraically and should bypass SMT checks
    /// in `is_self_inductive_blocking`. Used for sum invariants discovered via
    /// `is_sum_preserved_by_transitions` with algebraic verification. (#955)
    pub(crate) algebraically_verified: bool,
    /// Optional TLA+ action that generated the CTI this lemma blocks (#8215).
    ///
    /// When set, this lemma was learned from a counterexample-to-induction (CTI)
    /// produced by a specific TLA+ action's transition clause. Per-action lemmas
    /// enable TLA2's CDEMC to track which actions are "easy" vs "hard" to prove.
    pub(crate) action_id: Option<ActionId>,
    /// Number of times this lemma has contributed to blocking a POB.
    /// Used by usage-based GC: lemmas that have never participated in blocking
    /// (usage_count == 0) are candidates for garbage collection when the frame
    /// exceeds the soft lemma limit. (#8601)
    pub(crate) usage_count: u32,
    /// Origin tag: this lemma was admitted under RELATIVE induction only.
    ///
    /// Set for lemma hints on predicates with NO self-loop clause (multi-BB
    /// loop heads, where the loop closes through other relations). Such hints
    /// pass `is_inductive_blocking` at their level and `is_entry_inductive`
    /// (incoming-edge preservation with predecessor context), but
    /// `is_self_inductive_blocking` rejects them vacuously (#8578 guard:
    /// there is no self-loop clause to prove preservation on).
    ///
    /// Lemmas carrying this tag must NEVER count toward strict
    /// verification-skip decisions (`individually_inductive`, #5877): the
    /// strict per-lemma recomputation already excludes them via the #8578
    /// anti-vacuous guard, and this tag additionally short-circuits those
    /// paths explicitly so the exclusion survives future refactors.
    pub(crate) relative_induction_only: bool,
    /// Origin tag: this lemma's self-inductiveness was only established
    /// CONDITIONED on the optimistic entry-domain over-approximation
    /// (`is_self_inductive_blocking_with_entry_domain`, #4751 L4 / cand4).
    ///
    /// At target level 1 the entry context degenerates to the init-only
    /// must-summary, so such a lemma can be true for the sampled prefix while
    /// being globally non-inductive (bouncy's `(<= a0 0)`). The lemma is still
    /// a VALID frame lemma (frames over-approximate per-level reachability),
    /// but candidate-repair uses this tag to identify the likely poison when a
    /// direct-safety GLOBAL claim built from frame[1] fails strict validation
    /// without a usable concrete counterexample.
    pub(crate) optimistic_entry: bool,
}

impl Lemma {
    pub(crate) fn new(predicate: PredicateId, formula: ChcExpr, level: usize) -> Self {
        let formula_hash = formula.structural_hash();

        let lemma = Self {
            predicate,
            formula,
            formula_hash,
            level,
            algebraically_verified: false,
            action_id: None,
            usage_count: 0,
            relative_induction_only: false,
            optimistic_entry: false,
        };

        // Postcondition: cached hash is consistent with formula (#4757).
        debug_assert_eq!(
            lemma.formula_hash,
            lemma.formula.structural_hash(),
            "BUG: Lemma hash mismatch immediately after construction"
        );
        lemma
    }

    pub(crate) fn with_algebraically_verified(mut self, value: bool) -> Self {
        self.algebraically_verified = value;
        self
    }

    /// Tag this lemma as admitted under relative (entry) induction only:
    /// its predicate has no self-loop clause, so per-relation self-inductiveness
    /// was never proven. Tagged lemmas are excluded from strict
    /// verification-skip paths (`individually_inductive`, #5877).
    pub(crate) fn with_relative_induction_only(mut self, value: bool) -> Self {
        self.relative_induction_only = value;
        self
    }

    /// Tag this lemma as admitted through the OPTIMISTIC entry-domain
    /// conditioned self-inductiveness oracle (#4751 L4 / cand4 hardening).
    /// Candidate repair drops tagged conjuncts first when a direct-safety
    /// global claim fails strict validation without a concrete counterexample.
    pub(crate) fn with_optimistic_entry(mut self, value: bool) -> Self {
        self.optimistic_entry = value;
        self
    }

    /// Tag this lemma with the TLA+ action that produced the CTI it blocks.
    pub(crate) fn with_action(mut self, action_id: ActionId) -> Self {
        self.action_id = Some(action_id);
        self
    }

    /// Record that this lemma contributed to blocking a POB.
    /// Used by usage-based GC to distinguish active from dead lemmas. (#8601)
    pub(crate) fn mark_used(&mut self) {
        self.usage_count = self.usage_count.saturating_add(1);
    }
}
