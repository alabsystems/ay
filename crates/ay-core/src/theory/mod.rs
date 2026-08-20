// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Theory solver trait for AY
//!
//! All theory solvers implement this trait to integrate with the DPLL(T) framework.

use crate::term::{TermId, TermStore};

mod soundness;
mod types;

#[cfg(kani)]
mod kani_proofs;

pub use soundness::assert_conflict_soundness;
pub use types::{
    BoundRefinementRequest, DiscoveredDisequality, DiscoveredEquality, DisequalitySplitRequest,
    EqualityPropagationResult, ExpressionSplitRequest, ModelEqualityRequest,
    NativeTheoryPropagationBackend, NativeTheoryPropagationProfile, SplitRequest, StringLemma,
    StringLemmaKind, TheoryConflict, TheoryLemma, TheoryLit, TheoryPropagation, TheoryResult,
};

/// Trait for theory solvers.
///
/// # Push/Pop Contract
///
/// Every `TheorySolver` must support incremental scope management via
/// [`push`](Self::push) and [`pop`](Self::pop). The fundamental invariant:
///
/// > After `push(); <mutations>; pop();`, the solver MUST produce the same
/// > `check()` and `propagate()` results as if the mutations never happened.
///
/// This is the behavioral equivalence property -- the solver is logically
/// indistinguishable from a fresh solver that received only the surviving
/// (non-popped) assertions. Violations of this contract are soundness bugs:
/// they cause the DPLL(T) framework to report incorrect SAT/UNSAT results.
///
/// See [`push`](Self::push) for the detailed contract specification.
///
/// # Conformance Testing
///
/// All implementations are tested by `crates/ay-dpll/tests/theory_push_pop_contract.rs`
/// which exercises: assert-in-scope, check-sat-in-scope, pop, check-sat-after-pop
/// for every theory. See issue #3664 for history.
pub trait TheorySolver {
    /// Register a theory atom that may appear during solving.
    ///
    /// Called once per atom before solving begins. Allows the theory to
    /// pre-parse and index atoms for bound propagation. The theory can
    /// later use this index to determine which unasserted atoms are implied
    /// by current bounds, enabling same-variable chain propagation.
    ///
    /// Reference: Z3's `internalize_atom` in `theory_lra.cpp`.
    ///
    /// The default implementation does nothing (suitable for theories
    /// that don't implement bound propagation).
    fn register_atom(&mut self, _atom: TermId) {}

    /// Inform the theory of the set of terms that currently have a SAT
    /// variable, keyed by term id (`term_to_var` maps every Boolean atom the
    /// DPLL solver can assign to its variable). A pure-EUF solver uses this to
    /// restrict negative-congruence propagation to equalities that are actually
    /// SAT atoms: when EUF has no sibling theory, a propagation on an equality
    /// with no SAT variable is inert (the DPLL layer has no variable to receive
    /// it and drops it), so scanning those equalities is pure wasted work.
    ///
    /// SCOPE (soundness): only sound where the filtered propagation index feeds
    /// the SAT boundary alone. A combiner may install it only after proving that
    /// its cross-theory interface does not consume this index. The current
    /// callers are standalone EUF and the array-free UF+LIA combiner; array
    /// combiners deliberately keep the full index because their interface uses
    /// non-SAT-atom index disequalities.
    ///
    /// Passing a superset of the assignable atoms is always safe within that
    /// scope — the callee only ever *removes* provably-inert candidates. Called
    /// once per (re)created theory instance, BEFORE the first `propagate()`.
    /// The default implementation does nothing. (#euf-atom-filter)
    fn set_sat_atom_terms(&mut self, _term_to_var: &crate::kani_compat::DetHashMap<TermId, u32>) {}

    /// Assert a literal to the theory solver.
    fn assert_literal(&mut self, literal: TermId, value: bool);

    /// Attempt to retract a previously asserted literal.
    ///
    /// Returns `true` if the retraction was successful, `false` if the theory
    /// solver does not support selective retraction. When `false` is returned,
    /// the caller must fall back to full pop+push+re-assert.
    ///
    /// This is a building block for delta-based incremental sync (#2138).
    /// Currently no theory solvers implement selective retraction because
    /// LRA/LIA use LIFO trail-based bounds and EUF uses trail-based
    /// union-find, neither of which support out-of-order undo. The method
    /// is provided as a trait extension point for future solvers that may
    /// use indexed or hash-based assertion stores.
    fn retract_literal(&mut self, _literal: TermId, _value: bool) -> bool {
        false
    }

    /// Check consistency of current assignment.
    fn check(&mut self) -> TheoryResult;

    /// Drain ADDITIONAL pending string lemmas queued behind a
    /// `TheoryResult::NeedStringLemma` (strings NF-engine closure 3,
    /// `--str-nf`).
    ///
    /// When a string theory discovers several independent lemma requests in
    /// one check round (multiple buffered NF splits, multiple blocked
    /// extended-function reductions), it returns the first via
    /// `NeedStringLemma` and queues the rest. The executor drains this queue
    /// immediately after receiving the primary lemma and lowers the whole
    /// batch in ONE solver iteration instead of one CEGAR round-trip per
    /// lemma (skolem webs reduce in 1-2 rounds instead of ~10).
    ///
    /// The default returns an empty vector (no batching) — correct for every
    /// non-string theory and for string solvers with the closure disabled.
    fn take_pending_string_lemmas(&mut self) -> Vec<StringLemma> {
        Vec::new()
    }

    /// Cheap consistency check suitable for BCP-time eager callbacks.
    ///
    /// Called by the eager extension during SAT search instead of `check`.
    /// The result must be sound: any conflict or propagation returned here
    /// must be valid. However, this method may be weaker than `check()` —
    /// it is allowed to return `Sat` even when `check()` would find a
    /// conflict that requires expensive cross-theory reasoning.
    ///
    /// The default delegates to `check`, which is correct for standalone
    /// theories. Combined solvers override this to skip the Nelson-Oppen
    /// fixpoint, interface bridges, and cross-sort propagation.
    fn check_during_propagate(&mut self) -> TheoryResult {
        self.check()
    }

    /// Whether the eager path must run one full `check` after the SAT
    /// solver reaches a candidate model.
    ///
    /// When `check_during_propagate` is weaker than `check`, this must
    /// return `true` so the eager path performs one final full consistency
    /// check before accepting a SAT result.
    ///
    /// The default is `false`, which is correct for theories where
    /// `check_during_propagate` already delegates to `check`.
    fn needs_final_check_after_sat(&self) -> bool {
        false
    }

    /// Hint that the solver is in the SEARCH phase of an eager DPLL(T) solve
    /// (inline checks during CDCL) vs a FINAL/post-SAT check. Theories whose
    /// `needs_final_check_after_sat()` is `true` may defer their most
    /// expensive completeness passes (e.g. full Diophantine elimination)
    /// while in search: skipping a conflict-detection pass mid-search only
    /// delays the conflict to the post-SAT full check, never accepts a wrong
    /// SAT (#5462 deferral precedent). Default: ignored.
    fn set_search_phase(&mut self, _in_search: bool) {}

    /// Get propagated literals.
    fn propagate(&mut self) -> Vec<TheoryPropagation>;

    /// Check if the theory has pending propagations queued from assert_literal().
    ///
    /// Used by the BCP atom batching logic to bypass batching when the theory
    /// has eager same-variable propagations ready. Without this, batching delays
    /// `theory.propagate()` calls, starving the SAT solver of LP-derived bound
    /// propagations (#8422).
    ///
    /// Reference: OpenSMT `LASolver::getSimpleDeductions()` — same-variable
    /// bound chain propagations are queued during `assertBound()` and should
    /// be returned to the SAT solver immediately.
    fn has_pending_propagations(&self) -> bool {
        false
    }

    /// Check if the theory has pending analysis work that would produce
    /// propagations if `propagate()` were called now.
    ///
    /// Unlike `has_pending_propagations()` which checks for already-queued
    /// propagation results, this checks whether the theory has deferred work
    /// (e.g., touched simplex rows) that would produce new propagations.
    /// Used by the BCP batching logic to reduce batch sizes when the theory
    /// has work that should not be deferred too long (#8422).
    fn has_pending_analysis(&self) -> bool {
        false
    }

    /// Drain any pending propagations that were queued during assert_literal()
    /// without running the full propagation pipeline.
    ///
    /// This is used by the BCP batching logic (#8422) to deliver eager
    /// same-variable chain propagations to the SAT solver during batch
    /// deferral. The method should be lightweight -- it must NOT run simplex,
    /// implied bounds, or interval propagation.
    ///
    /// Returns propagations that have fully materialized reasons (Direct
    /// bounds only). Propagations with deferred reasons (ImpliedRow, Interval)
    /// are left in the pending buffer for the full `propagate()` call.
    fn drain_pending_propagations(&mut self) -> Vec<TheoryPropagation> {
        Vec::new()
    }

    /// Drain disequality split requests that were buffered by the most recent
    /// `check()` call but not returned via `NeedDisequalitySplit` (#8762).
    ///
    /// When `check()` finds N violated single-variable disequalities during a
    /// single scan, it returns the first as `NeedDisequalitySplit(first)` and
    /// buffers the remaining N-1 requests internally. Without draining, those
    /// requests are discarded on the next `check()` call — the DPLL loop then
    /// enforces only one split per SAT restart, costing N full SAT solves for
    /// N disequalities (observed pathology: 40x-300x slower than Z3 on
    /// puzzle-style QF_LIA benchmarks with `(distinct ...)` clauses).
    ///
    /// Default returns empty (theories without batched-disequality support are
    /// unaffected). Theories that buffer extras must override to return them
    /// so the DPLL split loop can encode all pending disequalities in a single
    /// round.
    fn drain_pending_diseq_splits(&mut self) -> Vec<DisequalitySplitRequest> {
        Vec::new()
    }

    /// Notify the theory that a permanent theory lemma clause has been added.
    ///
    /// This lets theories suppress rediscovery of the same lemma after SAT
    /// state is rebuilt and the clause is replayed from executor-owned state.
    /// The default implementation is a no-op.
    fn note_applied_theory_lemma(&mut self, _clause: &[TheoryLit]) {}

    /// Push a new incremental scope.
    ///
    /// Saves a boundary marker so that all semantic effects occurring after
    /// this call can be undone by the matching [`pop`](Self::pop).
    ///
    /// # Contract
    ///
    /// ## Behavioral equivalence (the key invariant)
    ///
    /// After `push(); <mutations>; pop();`, the solver's observable behavior
    /// (`check()`, `propagate()`, `propagate_equalities()`) MUST be identical
    /// to the pre-`push` state. "Identical" means: given the same sequence of
    /// future `assert_literal` / `check` / `propagate` calls, the solver
    /// produces the same results as if the pushed scope never existed.
    ///
    /// ## Must restore on pop
    ///
    /// These are **scope-local** effects that MUST be fully undone:
    ///
    /// - **Asserted literals**: logically retracted. Assertion vectors are
    ///   truncated to the push-point mark, or a trail is replayed.
    /// - **Assertion replay semantics**: replaying surviving trail literals
    ///   after backtrack must be idempotent (no duplicate semantic effects).
    ///   The `asserted` set must match only the surviving assertions.
    /// - **Union-find / equivalence classes**: must reflect only the surviving
    ///   assertions. Implementations use either an undo trail (EUF, arrays,
    ///   strings) or full snapshot restore (DT with path compression).
    /// - **Variable bounds** (LRA/LIA): bounds tightened by popped assertions
    ///   are restored to their pre-push values via a bound trail.
    /// - **Per-atom state**: entries added in the popped scope are removed;
    ///   entries overwritten are restored to their pre-scope values. Examples:
    ///   tester results (DT), constructor registrations (DT), asserted atom
    ///   dedup sets (LRA).
    ///
    /// ## Must clear on pop
    ///
    /// These are **derived** state that becomes stale after pop and MUST be
    /// cleared (they will be re-derived on the next `check()` / `propagate()`):
    ///
    /// - **Nelson-Oppen propagated equality pair sets**: stale pairs prevent
    ///   conflict detection in alternate search branches. (#3686, #3736)
    /// - **Pending propagation buffers**: stale propagations from the popped
    ///   scope must not leak into future `propagate()` calls.
    /// - **Pending conflict state**: `trivial_conflict` (LRA) and similar
    ///   fields must be cleared.
    /// - **Pending injectivity equalities** (DT): derived from popped merges.
    /// - **External equality/disequality facts** (arrays): re-derived each
    ///   check cycle.
    ///
    /// ## May persist across pop
    ///
    /// These are **globally valid** artifacts that do not depend on the
    /// assertion set and MAY be retained for performance:
    ///
    /// - Globally valid learned lemmas (e.g., BV/FP bit-blasting CNF clauses
    ///   managed by the SAT solver, not the theory solver).
    /// - Structural caches that depend on term shapes, not assertion state
    ///   (e.g., datatype definitions, tester maps, term-to-bits mappings).
    /// - LIA Diophantine analysis results (when invalidation is tracked via
    ///   equality keys).
    ///
    /// ## Nesting
    ///
    /// Scopes nest: `push(); push(); pop(); pop();` must restore to the state
    /// before the first `push()`. Each `pop()` undoes exactly one level. The
    /// scope depth after N pushes and M pops is `N - M` (for `M <= N`).
    /// Calling `pop()` with no matching `push()` is a no-op (implementations
    /// return early when the scope stack is empty).
    ///
    /// ## Implementation guidance
    ///
    /// The standard pattern is trail-based: `push()` records the current trail
    /// length; `pop()` replays the trail backwards to that length. For data
    /// structures with path compression (e.g., union-find in DT), snapshot
    /// the entire structure on `push()` and restore on `pop()`.
    ///
    /// Implementations SHOULD include `debug_assert!` checks to detect
    /// scope-mark / trail-length mismatches early.
    fn push(&mut self);

    /// Pop to the previous scope, undoing all scope-local effects.
    ///
    /// After this call, the solver's observable behavior MUST be identical
    /// to the state at the time of the matching [`push`](Self::push). All
    /// assertions, equivalence class merges, bound changes, and per-atom
    /// state from the popped scope are undone. Derived state (pending
    /// propagations, equality pairs, conflict flags) is cleared.
    ///
    /// If no matching `push()` exists (scope stack is empty), this is a
    /// no-op.
    ///
    /// See [`push`](Self::push) for the full restoration contract.
    fn pop(&mut self);

    /// Reset the solver completely, clearing all state.
    fn reset(&mut self);

    /// Soft reset: clear assertions but preserve learned state.
    ///
    /// This is called between SAT model iterations in DPLL(T). Unlike `reset()`,
    /// this preserves learned information (e.g., HNF cuts in LIA) that remains
    /// valid across different SAT assignments.
    ///
    /// Default implementation calls `reset()`. Theory solvers with learned state
    /// should override this to preserve that state.
    fn soft_reset(&mut self) {
        self.reset();
    }

    /// Warm soft reset: clear assertions but preserve both learned state AND
    /// solver internal values (e.g., simplex basis and variable assignments).
    ///
    /// This is called between iterations in persistent-theory pipelines where
    /// the theory solver is created once and reused across SAT model iterations.
    /// Unlike `soft_reset()`, which may clear internal solver state like variable
    /// values, `soft_reset_warm()` preserves the solver's working state so that
    /// subsequent `check()` calls can warm-start from the previous solution.
    ///
    /// For arithmetic theories (LRA/LIA), this preserves:
    /// - Simplex variable values (warm-start: only violated bounds need re-pivoting)
    /// - Tableau structure (rows, basic/non-basic assignment)
    /// - Learned cuts and Diophantine analysis results
    ///
    /// Default implementation calls `soft_reset()`. Theory solvers with
    /// warm-startable internal state should override this.
    fn soft_reset_warm(&mut self) {
        self.soft_reset();
    }

    /// #lra-inc-engine S3 (warm theory): hint that this check-sat reuses a theory
    /// solver persisted across check-sats (vs a fresh one). Lets the theory bound
    /// work that a STALE warm cache would otherwise blow up — for LRA, the
    /// implied-bounds recursive cascade, which on a region shift re-derives
    /// through the accumulated cache and explodes. Default no-op; sound (advisory).
    fn set_warm_reuse_hint(&mut self, _reused: bool) {}

    /// Whether `UnsatWithFarkas` conflicts carry a semantic Farkas certificate.
    ///
    /// Some theories use the optional Farkas coefficients purely as an interpolation
    /// annotation (e.g., integer-feasibility reasoning in LIA) and do not produce a
    /// real-arithmetic Farkas lemma certificate. Those solvers should return `false`
    /// so that debug verification can skip strict semantic checking.
    fn supports_farkas_semantic_check(&self) -> bool {
        false
    }

    /// Whether this theory's `Unsat` conflicts are derivable by EUF congruence
    /// closure alone.
    ///
    /// When `true`, debug verification will re-derive each `Unsat` conflict
    /// using a fresh `EufSolver`, catching semantic bugs that structural checks
    /// miss (e.g., claiming two terms are congruent when they are not).
    ///
    /// Only pure EUF solvers should return `true`. Combined solvers (AUFLIA,
    /// etc.) should leave the default `false` because their conflicts may
    /// involve arithmetic or other non-EUF reasoning.
    fn supports_euf_semantic_check(&self) -> bool {
        false
    }

    /// Propagate equalities for Nelson-Oppen theory combination.
    ///
    /// Called by the theory combinator to collect equalities that this theory
    /// has discovered. For example:
    /// - LIA discovers `x = y` when both are bounded to the same value
    /// - EUF discovers `f(a) = f(b)` by congruence when `a = b`
    ///
    /// The default implementation returns no equalities (suitable for theories
    /// that don't discover implicit equalities).
    fn propagate_equalities(&mut self) -> EqualityPropagationResult {
        EqualityPropagationResult::default()
    }

    /// Assert a shared equality from another theory (Nelson-Oppen).
    ///
    /// Called when another theory discovers that `lhs = rhs`. The theory should
    /// incorporate this equality into its reasoning. For example, EUF would
    /// merge the equivalence classes of `lhs` and `rhs`.
    ///
    /// The default implementation does nothing (suitable for theories that
    /// don't benefit from shared equalities).
    fn assert_shared_equality(&mut self, _lhs: TermId, _rhs: TermId, _reason: &[TheoryLit]) {}

    /// Assert a shared disequality from another theory (Nelson-Oppen).
    ///
    /// Called when another theory knows that `lhs != rhs`. For arithmetic
    /// solvers, this adds a disequality constraint that is checked against the
    /// model after simplex: if the model satisfies `lhs = rhs`, a split or
    /// conflict is generated.
    ///
    /// Without this, negated UF-equalities like `(not (= (g x) 5))` are
    /// invisible to the arithmetic solver, causing incompleteness when LIA/LRA
    /// bounds force `g(x) = 5` but the solver doesn't know about the
    /// disequality (#5228).
    ///
    /// The default implementation does nothing (suitable for theories that
    /// don't benefit from shared disequalities, or convex theories where
    /// equality propagation alone is complete).
    fn assert_shared_disequality(&mut self, _lhs: TermId, _rhs: TermId, _reason: &[TheoryLit]) {}

    /// Pre-register a theory atom before it is asserted.
    ///
    /// Called during DPLL(T) setup for every theory-relevant atom identified
    /// by Tseitin encoding. This allows the theory solver to parse and cache
    /// the atom structure eagerly, enabling `propagate()` to evaluate
    /// unasserted atoms from the very first check cycle.
    ///
    /// The default implementation does nothing. Theory solvers that benefit
    /// from early atom parsing (e.g., LRA interval propagation) should
    /// override this.
    fn internalize_atom(&mut self, term: TermId) {
        self.register_atom(term);
    }

    /// Drain any pending bound-refinement requests discovered during the last check.
    ///
    /// The default implementation returns no requests. Arithmetic solvers use this
    /// to ask the executor to create new bound atoms that were implied by the
    /// simplex/tableau state but absent from the current Boolean abstraction.
    fn take_bound_refinements(&mut self) -> Vec<BoundRefinementRequest> {
        Vec::new()
    }

    /// Collect per-theory runtime statistics.
    ///
    /// Returns key-value pairs where keys are theory-prefixed stat names
    /// (e.g., `"lra_checks"`, `"lia_conflicts"`) and values are counts.
    /// These are included in `(get-info :all-statistics)` output via
    /// `Statistics::extra`.
    ///
    /// The default implementation returns an empty list.
    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        Vec::new()
    }

    /// Export native theory-bound propagation metadata for DPLL dispatch.
    ///
    /// This hook is a fail-closed contract: the default is unsupported, and a
    /// non-default profile only describes what a theory has prepared. The DPLL
    /// layer must still apply its own control plane and reject partial or
    /// unsupported profiles before any native dispatch is allowed.
    fn native_theory_propagation_profile(&self) -> NativeTheoryPropagationProfile {
        NativeTheoryPropagationProfile::unsupported()
    }

    /// Suggest a polarity for a theory atom based on the current theory model.
    ///
    /// Called by the SAT solver after VSIDS picks a decision variable that
    /// is a theory atom. Returns `Some(true)` for positive polarity,
    /// `Some(false)` for negative, or `None` to use the SAT solver's default.
    ///
    /// For LRA: evaluates the atom's linear expression in the current simplex
    /// model and suggests the polarity consistent with the LP solution. This
    /// guides the SAT solver toward theory-consistent assignments, reducing
    /// the number of conflicts and restarts.
    ///
    /// Reference: Z3 `theory_lra::get_phase()`, `arith_solver::get_phase()`
    fn suggest_phase(&self, _atom: TermId) -> Option<bool> {
        None
    }

    /// Generation counter for the theory's phase-hint suggestions.
    ///
    /// The SAT solver bulk-seeds phase hints (`seed_phase_hints`) after EVERY
    /// BCP/theory-propagation quiescence — many times per decision cycle. On
    /// LRA/induction benchmarks this full O(atoms) scan + `suggest_phase` query
    /// per atom is the dominant in-solver cost, yet the theory's phase
    /// suggestions only change when its underlying model (phase-hint cache)
    /// changes — which is far rarer than the seed frequency.
    ///
    /// A theory that returns `Some(epoch)` here promises: *the value
    /// `suggest_phase(atom)` returns for every atom is unchanged as long as this
    /// counter is unchanged*. The extension caches the last epoch it seeded at
    /// and skips the entire re-seed when the epoch is unchanged, turning
    /// O(decision_cycles * atoms) seeding into O(model_changes * atoms).
    ///
    /// Returning `None` (the default) disables the optimization: the extension
    /// always re-seeds. Theories whose `suggest_phase` is constant `None`
    /// (e.g. EUF) gain nothing and need not override this.
    ///
    /// Correctness note: phase hints are a heuristic; they bias branch order and
    /// can never cause a wrong sat/unsat. Even an over-eager epoch (one that
    /// fails to advance on a model change) only degrades the heuristic, but
    /// implementations should still advance it on every model change so the
    /// seeded hints track the model, which is the whole point of seeding.
    fn phase_hint_epoch(&self) -> Option<u64> {
        None
    }

    /// Whether this theory supports theory-aware branching (#4919).
    ///
    /// When `true`, the DPLL extension's `suggest_decision` method will force
    /// all theory atoms to be decided before Tseitin encoding variables. This
    /// gives the theory solver maximum information for bound propagation.
    ///
    /// Only arithmetic theories (LRA, LIA, LIRA, NRA, NIA) should return `true`.
    /// Other theories (Seq, String, EUF, etc.) may have incomplete axiom
    /// generation that can cause false SAT when the search order changes (#6236).
    ///
    /// Reference: Z3 `smt_case_split_queue.cpp:1170-1209`
    fn supports_theory_aware_branching(&self) -> bool {
        false
    }

    /// Whether the DPLL extension should hand variable selection to VSIDS
    /// (instead of intensifying theory-aware branching) when the search is
    /// "wandering" — many decisions per conflict (#euf-search-quality).
    ///
    /// The default (`false`) keeps the historical #9505 response: when
    /// decisions/conflicts exceeds the wander threshold, the extension decides
    /// theory atoms on EVERY decision. That is right for arithmetic
    /// (BMC/induction formulas where the LP model should steer), but for EUF
    /// it is catastrophic: round-robin merge-everything decisions produce
    /// 10-100x more conflicts than Z3 on NEQ/QG-classification instances.
    ///
    /// A theory returning `true` opts into the opposite response: once the
    /// wander threshold trips, the extension stops steering entirely for the
    /// rest of the solve — no forced theory decisions, no bulk phase-hint
    /// seeding; VSIDS + phase saving drive the search and only
    /// `suggest_phase_implied` polarity hints remain.
    ///
    /// Purely heuristic: only decision order/polarity change, never the
    /// sat/unsat verdict.
    fn wander_hand_to_vsids(&self) -> bool {
        false
    }

    /// Polarity hint for an atom whose truth value is IMPLIED by the current
    /// theory state (e.g. an equality atom whose sides the e-graph already
    /// merged), or `None` when the theory has no implied preference.
    ///
    /// Unlike `suggest_phase`, this must return `Some` ONLY for atoms where
    /// the suggested polarity is currently forced by the theory — deciding
    /// the opposite polarity would immediately produce a theory conflict.
    /// Used by the DPLL extension in the wander-latched VSIDS mode (see
    /// `wander_hand_to_vsids`) where general phase steering is disabled but
    /// implied polarities are still free wins.
    fn suggest_phase_implied(&self, _atom: TermId) -> Option<bool> {
        None
    }

    /// Suggest a specific theory atom to decide, with its preferred phase.
    ///
    /// Called by the DPLL extension before the activity-based theory atom scan.
    /// Returns `Some((atom, phase))` if the theory has a high-priority atom
    /// to decide (e.g., a blocked or fixed variable from feasible-set analysis),
    /// or `None` to fall through to the default activity-based selection.
    ///
    /// This is used by the clauseSMT arithmetic propagation branching technique
    /// (#8445) to prioritize atoms whose feasible sets are empty (blocked) or
    /// singleton (fixed), as these variables have the most constrained search
    /// space and should be decided first.
    ///
    /// Reference: "Improving NLSAT for NRA" (Wang, ASE 2025), Technique 2.
    fn suggest_decision_atom(&self) -> Option<(TermId, bool)> {
        None
    }

    /// Sort atom_index by bound value after all atoms are registered.
    /// Enables O(log n) nearest-neighbor lookup for bound axiom generation.
    /// Reference: Z3 `flush_bound_axioms` sorted merge.
    fn sort_atom_index(&mut self) {}

    /// Generate bound ordering axiom term pairs.
    /// Each tuple `(t1, p1, t2, p2)` represents the binary clause `(t1^p1 ∨ t2^p2)`.
    /// Called after `register_atom()` and `sort_atom_index()`.
    /// Reference: Z3 `mk_bound_axioms` / `mk_bound_axiom`.
    fn generate_bound_axiom_terms(&self) -> Vec<(TermId, bool, TermId, bool)> {
        Vec::new()
    }

    /// Generate bound ordering axioms for a single newly-registered atom against
    /// all existing atoms on the same variable. Called after `register_atom()` for
    /// atoms created during search (bound refinement). This is AY's equivalent of
    /// Z3's `flush_bound_axioms` incremental axiom generation.
    /// Reference: Z3 `arith_axioms.cpp:470-526`, `theory_lra.cpp:2882-2937`.
    fn generate_incremental_bound_axioms(
        &self,
        _atom: TermId,
    ) -> Vec<(TermId, bool, TermId, bool)> {
        Vec::new()
    }

    /// Drain bound ordering axioms that became newly available since the last
    /// flush.
    ///
    /// The default implementation preserves the existing batch behavior:
    /// sort the atom index and regenerate the full axiom set. Persistent
    /// theories can override this to emit axioms only for newly registered
    /// atoms and skip repeated full-set regeneration across split-loop rounds.
    fn take_pending_bound_axiom_terms(&mut self) -> Vec<(TermId, bool, TermId, bool)> {
        self.sort_atom_index();
        self.generate_bound_axiom_terms()
    }

    /// Export a structural snapshot for faster reconstruction (#6590).
    ///
    /// Called before dropping a theory instance to save expensive parsing and
    /// indexing work. The snapshot is opaque to the caller and is only consumed
    /// by [`import_structural_snapshot`](Self::import_structural_snapshot) on a
    /// fresh instance of the same theory type.
    ///
    /// For LRA: exports the atom cache (parsed atom info) so that subsequent
    /// `register_atom` calls hit the cache instead of re-parsing the term DAG.
    ///
    /// The default implementation returns `None` (no snapshot support).
    fn export_structural_snapshot(&self) -> Option<Box<dyn std::any::Any>> {
        None
    }

    /// Move-based snapshot export: takes structural fields out of the solver (#6590).
    ///
    /// Like [`export_structural_snapshot`](Self::export_structural_snapshot) but moves
    /// data instead of cloning. The solver is left in a partially empty state and
    /// should only be dropped (not used) after this call.
    ///
    /// This avoids 20+ HashMap/Vec clones per split-loop iteration. Callers must
    /// ensure `collect_statistics()` and any other reads happen BEFORE this call.
    ///
    /// The default implementation delegates to `export_structural_snapshot` (clone).
    fn take_structural_snapshot(&mut self) -> Option<Box<dyn std::any::Any>> {
        self.export_structural_snapshot()
    }

    /// Reconstruct a theory directly from a structural snapshot when possible.
    ///
    /// This is an optional fast path for theories whose snapshot already
    /// contains everything needed to build a fresh solver instance. Callers
    /// fall back to `new()` + [`import_structural_snapshot`](Self::import_structural_snapshot)
    /// when the theory does not override this hook or rejects the snapshot.
    fn restore_from_structural_snapshot(
        _terms: &TermStore,
        snapshot: Box<dyn std::any::Any>,
    ) -> Result<Self, Box<dyn std::any::Any>>
    where
        Self: Sized,
    {
        Err(snapshot)
    }

    /// Import a structural snapshot from a previous theory instance (#6590).
    ///
    /// Called immediately after construction and before `register_atom`. Allows
    /// the theory to skip expensive re-parsing of atoms that were already parsed
    /// in a previous iteration.
    ///
    /// The `snapshot` must have been produced by `export_structural_snapshot` on
    /// the same theory type. Implementations should downcast and silently ignore
    /// type mismatches.
    fn import_structural_snapshot(&mut self, _snapshot: Box<dyn std::any::Any>) {}

    /// Return the number of atoms currently registered in the theory.
    ///
    /// Used for structural snapshot heuristics and incremental warm-start
    /// diagnostics. The default returns `0`.
    fn registered_atom_count(&self) -> usize {
        0
    }

    /// Optionally reconstruct the full reason literals for a lazy propagation.
    ///
    /// The eager SAT extension uses this when a theory returns compact
    /// `reason_data` instead of eagerly materializing a full reason vector.
    /// The default returns `None`, meaning the propagation already carried
    /// its explicit reason literals.
    ///
    /// Changed from `Vec<TermId>` to `Vec<TheoryLit>` (#8467) to preserve
    /// reason polarity. LRA bounds can have `term=false` reasons (e.g.,
    /// negated equalities), so the polarity must be carried through.
    fn explain_propagation(&mut self, _lit: TermId, _reason_data: u64) -> Option<Vec<TheoryLit>> {
        None
    }

    /// Notify the theory that a lazy propagation was rejected upstream.
    ///
    /// This lets the theory drop any cached state associated with the
    /// rejected `(lit, reason_data)` pair. The default is a no-op.
    fn mark_propagation_rejected(&mut self, _lit: TermId, _reason_data: u64) {}

    /// Declare whether the CONSUMER of `propagate()` supports the lazy
    /// justification protocol (#8467): `TheoryPropagation::reason_data` +
    /// [`explain_propagation`](Self::explain_propagation) +
    /// [`mark_propagation_rejected`](Self::mark_propagation_rejected).
    ///
    /// The eager SAT extension (`ay-dpll` `TheoryExtension`) calls this with
    /// `true` at construction. Consumers that convert every propagation's
    /// `reason` field directly into a clause (e.g. the legacy `DpllT`
    /// `check_theory` loop) never call it, so theories that gate lazy
    /// emission on this flag keep emitting fully materialized reasons there
    /// — a lazy (empty-`reason`) propagation handed to a non-lazy consumer
    /// would be skipped as structurally invalid, losing guidance.
    ///
    /// Combined solvers must forward this to their sub-solvers. The default
    /// is a no-op (theory emits eager reasons regardless — always sound).
    fn set_lazy_propagation_supported(&mut self, _supported: bool) {}

    /// Notify the theory that a particular atom participated in a conflict.
    ///
    /// The default is a no-op. Theories with conflict-local caching may use
    /// this hook to bias future explanation or refinement work.
    fn note_conflict_atom(&mut self, _atom: TermId) {}
}
