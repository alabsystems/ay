// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental solving state management.
//!
//! This module provides state management for incremental SMT solving:
//! - `IncrementalBvState`: Persistent state for BV theory with rebuild-on-pop reuse
//! - `IncrementalTheoryState`: Persistent state for other theories (EUF/LRA/LIA)
//!
//! All incremental subsystems implement [`IncrementalSubsystem`], which
//! provides the push/pop/reset interface used by `Executor::execute()`.
//! Adding a new subsystem requires:
//! 1. Implementing `IncrementalSubsystem` for the type
//! 2. Adding the field to the `for_each_incremental_subsystem!` macro in `executor.rs`
//!
//! Key design invariant (the development design notes):
//! - Definitional clauses (Tseitin definitions) are added GLOBALLY
//! - Only assertion activation (unit clause on root literal) is scoped
//! - This ensures cached term→var mappings remain valid after pop

mod authority_reset;
#[cfg(test)]
mod tests;

/// Trait for subsystems that participate in incremental push/pop/reset scoping.
///
/// Every field in `Executor` that maintains scope state must implement this
/// trait. The executor dispatches push/pop/reset to all registered subsystems
/// via the `for_each_incremental_subsystem!` macro.
pub(crate) trait IncrementalSubsystem {
    /// Save current state for later restoration by `pop`.
    fn push(&mut self);

    /// Restore state to before the matching `push`.
    /// Returns `true` if a scope was popped, `false` on underflow (no matching push).
    fn pop(&mut self) -> bool;

    /// Reset all state to initial conditions.
    fn reset(&mut self);
}

mod bv_state;
pub(crate) use bv_state::IncrementalBvState;

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, TermData, TermId, TermStore, TseitinState};
use ay_sat::Solver as SatSolver;

use crate::executor_types::Statistics;

/// Persistent state for incremental theory solving (QF_UF, QF_LRA, QF_LIA, etc.)
///
/// This maintains:
/// - Tseitin variable mappings for consistent term-to-var mappings across check-sat calls
/// - A persistent SAT solver that retains learned clauses
/// - Set of encoded assertions to avoid re-encoding terms with cached vars
/// - Scope depth tracking with pending push support
///
/// Key design invariant (the development design notes):
/// - Definitional clauses (Tseitin definitions) are added GLOBALLY via add_clause_global()
/// - Only assertion activation (unit clause on root literal) is scoped via add_clause()
/// - This ensures cached term→var mappings remain valid after pop: their definitions
///   are always active, only the assertions that use them are scoped.
#[derive(Clone, Default)]
pub(crate) struct LiaDerivedAssertionMetadata {
    /// Shallowest scope where this derived assertion must remain active.
    pub(crate) activation_depth: usize,
    /// Source assertion sets that justify keeping the derived assertion active.
    pub(crate) source_sets: Vec<Vec<TermId>>,
}

/// Maximum number of theory lemmas before the older half is trimmed (#8623).
/// This bounds memory growth in long-running incremental sessions (e.g., PDR
/// blocking queries) where theory lemmas accumulate across many check-sat calls.
const MAX_THEORY_LEMMAS: usize = 50_000;

pub(crate) struct IncrementalTheoryState {
    /// Persistent SAT solver that retains learned clauses
    pub(crate) persistent_sat: Option<SatSolver>,
    /// #warm-theory (SMT-COMP incremental QF_LRA): type-erased carrier for a
    /// theory solver persisted ACROSS check-sats, so its warm tableau/basis and
    /// derived-bound overlay survive instead of being rebuilt from scratch every
    /// check (the measured ~85%-of-cost wall on hybrid_networks). Default `None`;
    /// only populated when the warm-theory lane is enabled (gated default-OFF).
    /// Type-erased because the persistent-theory pipeline is generic over the
    /// theory type; the consumer downcasts to its concrete solver. NOTE: a
    /// persisted LRA solver holds a raw `terms_ptr` that dangles across check-sats
    /// and MUST be refreshed via `set_terms` before reuse.
    /// `+ Send` keeps `IncrementalTheoryState: Send` (required by the test harness
    /// and the parallel track); `LraSolver` is `unsafe impl Send` (lib.rs:1128).
    pub(crate) persist_theory: Option<Box<dyn std::any::Any + Send>>,
    /// Persistent SAT solver for incremental LIA solving.
    ///
    /// LIA uses a branch-and-bound loop that adds temporary split constraints.
    /// We keep a dedicated solver here so we can retain learned clauses across
    /// check-sat calls without interfering with other incremental theory modes.
    pub(crate) lia_persistent_sat: Option<SatSolver>,
    /// Map of assertions that have been encoded (globally) in this session to root literals.
    /// Used to avoid re-encoding terms whose definitions are already in the solver and to
    /// re-add scoped activation clauses after pop.
    pub(crate) encoded_assertions: HashMap<TermId, i32>,
    /// Scope depth where each assertion's activation clause was last added.
    ///
    /// An activation added at depth `d` remains valid for all deeper scopes `>= d`.
    /// After pop, only assertions with activation depth greater than the new
    /// scope depth must be re-activated.
    pub(crate) assertion_activation_scope: HashMap<TermId, usize>,
    /// Saved Tseitin state for consistent term-to-var mappings across calls.
    /// Used by `persistent_sat` pipelines.
    pub(crate) tseitin_state: TseitinState,
    /// Per-solver Tseitin encoding state for `lia_persistent_sat` (#6853).
    ///
    /// The LIA solver uses a separate SAT solver (`lia_persistent_sat`) with
    /// its own variable space. Sharing a Tseitin state between two solvers
    /// causes variable index collisions: a Tseitin variable cached from
    /// encoding for one solver can coincide with a scope selector allocated
    /// by `push()` in the other solver. Separate Tseitin states eliminate
    /// this cross-solver pollution entirely.
    pub(crate) lia_tseitin_state: TseitinState,
    /// Encoded assertion roots for `lia_persistent_sat` (#6853).
    pub(crate) lia_encoded_assertions: HashMap<TermId, i32>,
    /// Activation scope depths for `lia_persistent_sat` (#6853).
    pub(crate) lia_assertion_activation_scope: HashMap<TermId, usize>,
    /// Clausification proof ledger aligned with SAT original-clause insertion order.
    ///
    /// This mirrors every original clause added to the persistent SAT solver:
    /// definitional clauses carry their Tseitin proof annotation, while root
    /// activations and re-activations append `None`.
    pub(crate) clausification_proofs: Vec<Option<ay_core::ClausificationProof>>,
    /// Theory-lemma proof ledger aligned with SAT original-clause insertion order.
    ///
    /// When a persistent original SAT clause comes from `NeedLemmas`, this
    /// stores the theory-proof annotation SatProofManager should emit for that
    /// same original clause index.
    pub(crate) original_clause_theory_proofs: Vec<Option<ay_core::TheoryLemmaProof>>,
    /// Permanent theory lemmas replayed into each fresh theory rebuild.
    ///
    /// The no-split incremental pipeline recreates the theory solver on every
    /// SAT round, so clauses learned via `NeedLemmas` must be replayed here to
    /// preserve `note_applied_theory_lemma` metadata across rounds and across
    /// incremental `check-sat` calls.
    ///
    /// Each entry is paired with the scope depth at which it was learned.
    /// On pop, only lemmas from the popped scope are removed; lemmas from
    /// lower scopes are retained to avoid expensive re-derivation (#8157).
    pub(crate) theory_lemmas: Vec<(ay_core::TheoryLemma, usize)>,
    /// O(1) membership test for persistent theory-lemma replay.
    pub(crate) theory_lemma_keys: HashSet<Vec<ay_core::TheoryLit>>,
    /// Saved proof-ledger lengths per scope for truncation on pop (#8572).
    ///
    /// Each push records `(clausification_proofs.len(),
    /// original_clause_theory_proofs.len())`.  Pop truncates back to the
    /// saved lengths, keeping these ledgers aligned with the SAT solver's
    /// `OriginalLedger` which also truncates on `pop_scope()` (#8472).
    pub(crate) proof_scope_starts: Vec<(usize, usize)>,
    /// Current scope depth (0 = global, 1+ = in push scope)
    pub(crate) scope_depth: usize,
    /// Pending push count: increments on SMT push before solver exists.
    /// Applied when solver is created via apply_pending_pushes().
    pub(crate) pending_push: usize,
    /// Derived LIA assertions for the active preprocessed assertion set.
    pub(crate) lia_derived_assertions: HashMap<TermId, LiaDerivedAssertionMetadata>,
    /// Theory atoms registered for theory communication
    pub(crate) theory_atoms: Vec<TermId>,
    /// Assertions that existed before incremental mode was first enabled.
    ///
    /// Incremental mode is toggled by `push`, but the first incremental solve
    /// may happen inside that pushed scope. These pre-existing assertions are
    /// semantically global and must keep global activation clauses.
    pub(crate) pre_push_assertions: HashSet<TermId>,
    /// Whether assertion activation clauses may need to be re-added.
    ///
    /// This is set on `pop()` because scoped activation clauses are disabled when
    /// a scope is popped. It avoids re-adding duplicate activation units on every
    /// `check-sat` while still restoring activations after scope drops.
    pub(crate) needs_activation_reassert: bool,
    /// Cumulative theory conflicts across incremental check-sat calls (#662).
    pub(crate) theory_conflicts: u64,
    /// Cumulative theory propagations across incremental check-sat calls (#662).
    pub(crate) theory_propagations: u64,
    /// Cumulative DPLL(T) round trips across incremental check-sat calls (#4802).
    /// Mirrors the DpllT `timings.round_trips` counter for the incremental path.
    pub(crate) round_trips: u64,
    /// Cumulative SAT solve time (seconds). Tracked per solve call (#5175).
    pub(crate) sat_solve_secs: f64,
    /// Cumulative theory sync time (seconds). Tracked per solve call (#5175).
    pub(crate) theory_sync_secs: f64,
    /// Cumulative theory check time (seconds). Tracked per solve call (#5175).
    pub(crate) theory_check_secs: f64,
    /// SAT warm state extracted before clearing a persistent solver (#3762).
    ///
    /// When the SLIA pipeline clears `lia_persistent_sat` between effort passes
    /// or pivot candidates, it stores learned clauses, VSIDS activities, and
    /// phase hints here. The next solver creation imports this state to avoid
    /// cold-start overhead.
    pub(crate) sat_warm_state: Option<crate::SatWarmState>,
    /// Scratch var-to-term map reused across incremental check-sat calls (#8573).
    pub(crate) scratch_var_to_term: HashMap<u32, TermId>,
    /// Per-Executor bound-axiom cache (Fix 3 Layer A, #8857).
    ///
    /// Bound-axiom generation registers every active theory atom into a
    /// fresh theory solver, sorts the atom index, generates all-pairs
    /// ordering axioms, and (eager arm / proof mode) validates each pair
    /// with an LRA solver. The result is a pure function of the active atom
    /// set: generation runs on a fresh solver with no assertions, so the
    /// parse results and pair set are deterministic for a given TermStore.
    /// Ordinary incremental operation is append-only; the isolated DT
    /// speculative lane is disabled for incremental sessions and cannot mutate
    /// this persistent cache's term universe.
    ///
    /// This cache keys the generated (and possibly validated) pairs on a
    /// hash of the sorted atom-set TermIds. On a hit, the pipeline arms
    /// replay the cached pairs directly into the SAT solver, skipping
    /// axiom-theory construction, generation, and per-pair validation.
    /// The "Bound axiom injection diagnostic (#8452)" tracing line therefore
    /// fires once per distinct atom set instead of once per check.
    ///
    /// Invalidation: key mismatch regenerates. Survives push/pop (bound
    /// axioms are tautologies — valid in any scope). Cleared on reset().
    pub(crate) bound_axiom_cache: Option<BoundAxiomCache>,
    /// Incremental high-water-mark cache for the Bool-UF-arg scan in
    /// `collect_active_theory_atoms` (perf #N: O(N^2) incremental path).
    ///
    /// The Bool-UF-arg portion of that scan is a pure function of the
    /// monotonically-growing incremental-session `TermStore` (NOT of the
    /// active assertion set),
    /// so it can be made incremental: scan only terms appended since the
    /// last check-sat and union the discovered Bool args into the persisted
    /// set. See [`BoolUfArgCache`].
    pub(crate) bool_uf_arg_cache: BoolUfArgCache,
}

/// Incremental cache for the Bool-UF-arg scan in
/// `collect_active_theory_atoms`.
///
/// The scan walks every term in the global `TermStore` looking for Bool-sorted
/// arguments to (non-logical) UF applications, which must be registered as
/// theory atoms so their truth values reach the EUF solver (#4610). That scan
/// is O(`terms.len()`) and was re-run from scratch on every check-sat, making
/// the incremental pipeline O(N^2) in the number of check-sats.
///
/// Incremental sessions use an append-only `TermStore`: the only truncating
/// lane is gated off before incremental solving and runs with isolated state.
/// The set of Bool-UF-args is therefore monotonic within this cache's lifetime.
/// This cache persists the discovered set and a high-water-mark of the last
/// scanned `terms.len()`; each check-sat scans only the newly-appended terms
/// `[hwm..terms.len())` and unions any new Bool args into `bool_args`. The
/// merged result is byte-for-byte identical to the from-scratch scan.
#[derive(Clone, Default)]
pub(crate) struct BoolUfArgCache {
    /// Number of terms (`terms.len()`) scanned so far. Only terms with index
    /// `>= hwm` are examined on the next scan.
    pub(crate) hwm: usize,
    /// All Bool-UF-arg TermIds discovered so far across every check-sat.
    pub(crate) bool_args: HashSet<TermId>,
}

impl BoolUfArgCache {
    /// Incrementally scan `terms` for Bool-sorted arguments of (non-logical)
    /// UF applications, updating the persisted set and high-water-mark, then
    /// merge all discovered Bool args into `out`.
    ///
    /// This produces exactly the same additions to `out` as the equivalent
    /// full scan `for idx in 0..terms.len()` (the union semantics and the
    /// logical-symbol skip list are preserved verbatim).
    fn collect_into(&mut self, terms: &TermStore, out: &mut HashSet<TermId>) {
        // Defensive guard: an incremental-session TermStore should never
        // shrink below a prior high-water-mark. If a caller ever reuses this
        // cache with a fresh/smaller TermStore (which would make cached TermIds
        // meaningless), fall back to a full re-scan to stay sound rather than
        // trusting stale state.
        if terms.len() < self.hwm {
            self.hwm = 0;
            self.bool_args.clear();
        }
        for idx in self.hwm..terms.len() {
            let term_id = TermId::new(idx as u32);
            if let TermData::App(ay_core::term::Symbol::Named(name), args) = terms.get(term_id) {
                match name.as_str() {
                    "and" | "or" | "xor" | "=>" | "not" | "=" | "distinct" | "ite" => continue,
                    _ => {}
                }
                if args.is_empty() {
                    continue;
                }
                for &arg in args {
                    if terms.sort(arg) == &Sort::Bool {
                        self.bool_args.insert(arg);
                    }
                }
            }
        }
        self.hwm = terms.len();
        out.extend(self.bool_args.iter().copied());
    }
}

/// Cached bound-axiom generation results for one active-atom set (#8857).
pub(crate) struct BoundAxiomCache {
    /// Hash of the sorted active-atom TermId indices.
    pub(crate) atom_set_key: u64,
    /// Number of atoms hashed (cheap collision guard).
    pub(crate) atom_count: usize,
    /// Generated axiom pairs `(t1, p1, t2, p2)`, each encoding the binary
    /// tautology clause `t1^p1 ∨ t2^p2`.
    pub(crate) pairs: Vec<(TermId, bool, TermId, bool)>,
    /// Per-pair Farkas annotations, aligned with `pairs`.
    pub(crate) farkas: Vec<Option<ay_core::FarkasAnnotation>>,
    /// Whether the pairs went through per-pair tautology validation
    /// (#6242/#6564, the `TheoryExtension` construction path). The eager arm
    /// only replays validated entries; the lazy/assume/eager-persistent
    /// injection macro never validates, so it accepts either.
    pub(crate) validated: bool,
    /// Whether per-pair Farkas certificates were captured. Proof-enabled
    /// replays require this; non-proof replays accept either.
    pub(crate) proof_validated: bool,
}

/// Compute the bound-axiom cache key: hash of the sorted TermId indices of
/// the active atom set (#8857).
pub(crate) fn bound_axiom_atom_set_key<I>(atoms: I) -> u64
where
    I: IntoIterator<Item = TermId>,
{
    use std::hash::Hasher;
    let mut ids: Vec<u32> = atoms.into_iter().map(|t| t.index() as u32).collect();
    ids.sort_unstable();
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    hasher.write_usize(ids.len());
    for id in &ids {
        hasher.write_u32(*id);
    }
    hasher.finish()
}

impl IncrementalTheoryState {
    pub(crate) fn new() -> Self {
        Self {
            persistent_sat: None,
            persist_theory: None,
            lia_persistent_sat: None,
            encoded_assertions: HashMap::default(),
            assertion_activation_scope: HashMap::default(),
            tseitin_state: TseitinState::new(),
            lia_tseitin_state: TseitinState::new(),
            lia_encoded_assertions: HashMap::default(),
            lia_assertion_activation_scope: HashMap::default(),
            clausification_proofs: Vec::new(),
            original_clause_theory_proofs: Vec::new(),
            theory_lemmas: Vec::new(),
            theory_lemma_keys: HashSet::default(),
            proof_scope_starts: Vec::new(),
            scope_depth: 0,
            pending_push: 0,
            lia_derived_assertions: HashMap::default(),
            theory_atoms: Vec::new(),
            pre_push_assertions: HashSet::default(),
            needs_activation_reassert: false,
            theory_conflicts: 0,
            theory_propagations: 0,
            round_trips: 0,
            sat_solve_secs: 0.0,
            theory_sync_secs: 0.0,
            theory_check_secs: 0.0,
            sat_warm_state: None,
            scratch_var_to_term: HashMap::default(),
            bound_axiom_cache: None,
            bool_uf_arg_cache: BoolUfArgCache::default(),
        }
    }

    /// Sync tseitin_state.next_var to account for ALL SAT solver allocations.
    ///
    /// CRITICAL: Use total_num_vars() not user_num_vars() to include scope selectors.
    /// Scope selectors are allocated by push() and occupy variable indices that
    /// Tseitin encoding must avoid. (#1447)
    #[cfg(test)]
    pub(crate) fn sync_tseitin_next_var(&mut self) {
        let mut next_var = self.tseitin_state.next_var.max(1);

        if let Some(ref sat) = self.persistent_sat {
            let sat_num_vars =
                u32::try_from(sat.total_num_vars()).expect("SAT solver num_vars does not fit u32");
            next_var = next_var.max(sat_num_vars + 1);
        }
        if let Some(ref sat) = self.lia_persistent_sat {
            let sat_num_vars =
                u32::try_from(sat.total_num_vars()).expect("SAT solver num_vars does not fit u32");
            next_var = next_var.max(sat_num_vars + 1);
        }

        self.tseitin_state.next_var = self.tseitin_state.next_var.max(next_var);
    }

    /// Drop encoded assertions that are no longer active in the SMT context.
    ///
    /// Definitional clauses remain global; only activation clauses are scoped.
    /// After pop, a previously encoded assertion may need to be re-activated when
    /// asserted again, so stale encoded entries must be removed.
    pub(crate) fn retain_encoded_assertions(&mut self, active_assertions: &[TermId]) {
        fn is_still_active(
            term: &TermId,
            active: &HashSet<TermId>,
            derived: &HashMap<TermId, LiaDerivedAssertionMetadata>,
        ) -> bool {
            active.contains(term)
                || derived.get(term).is_some_and(|meta| {
                    meta.source_sets
                        .iter()
                        .any(|sources| sources.iter().all(|source| active.contains(source)))
                })
        }

        if self.encoded_assertions.is_empty() && self.lia_encoded_assertions.is_empty() {
            return;
        }
        let active: HashSet<TermId> = active_assertions.iter().copied().collect();
        self.encoded_assertions
            .retain(|term, _| is_still_active(term, &active, &self.lia_derived_assertions));
        self.assertion_activation_scope
            .retain(|term, _| is_still_active(term, &active, &self.lia_derived_assertions));
        // #6853: Per-solver LIA encoding fields
        self.lia_encoded_assertions
            .retain(|term, _| is_still_active(term, &active, &self.lia_derived_assertions));
        self.lia_assertion_activation_scope
            .retain(|term, _| is_still_active(term, &active, &self.lia_derived_assertions));
        // Note: we do NOT prune lia_derived_assertions here. Its lifecycle is
        // managed by replace_lia_derived_assertions() which clears and
        // repopulates every check-sat. Pruning here would remove metadata for
        // new-but-not-yet-encoded assertions, causing desired_activation_depth()
        // to fall through to the wrong depth and produce permanent global
        // activation clauses that conflict with later scoped assertions (#6853).

        // Note: we do NOT drop the persistent SAT solver here. The SAT solver's
        // push/pop mechanism already deactivated the scoped activation clauses for
        // popped assertions. Global definition clauses remain but are harmless since
        // their root variables are not activated. The scope filter on the array axiom
        // generators (#6726) prevents phantom axioms from dead terms.
    }

    /// Apply any pending pushes to the SAT solver.
    /// Called after solver is created to sync scope state.
    pub(crate) fn apply_pending_pushes(&mut self) {
        if let Some(ref mut sat) = self.persistent_sat {
            for _ in 0..self.pending_push {
                sat.push();
            }
            self.pending_push = 0;
        }
    }

    /// Replace the currently active LIA-derived assertion metadata.
    pub(crate) fn replace_lia_derived_assertions<I>(&mut self, entries: I)
    where
        I: IntoIterator<Item = (TermId, usize, Vec<TermId>)>,
    {
        self.lia_derived_assertions.clear();
        for (term, activation_depth, mut sources) in entries {
            sources.sort_by_key(|source| source.index());
            sources.dedup();

            let meta = self.lia_derived_assertions.entry(term).or_insert_with(|| {
                LiaDerivedAssertionMetadata {
                    activation_depth,
                    source_sets: Vec::new(),
                }
            });
            meta.activation_depth = meta.activation_depth.min(activation_depth);
            if !meta.source_sets.contains(&sources) {
                meta.source_sets.push(sources);
            }
        }
    }

    /// Compute the activation depth for an assertion root clause.
    pub(crate) fn desired_activation_depth(
        &self,
        assertion: TermId,
        active_assertion_depths: &HashMap<TermId, usize>,
    ) -> usize {
        if let Some(meta) = self.lia_derived_assertions.get(&assertion) {
            return meta.activation_depth.min(self.scope_depth);
        }
        active_assertion_depths
            .get(&assertion)
            .copied()
            .or_else(|| self.pre_push_assertions.contains(&assertion).then_some(0))
            .unwrap_or(self.scope_depth)
            .min(self.scope_depth)
    }
}

impl IncrementalSubsystem for IncrementalTheoryState {
    fn push(&mut self) {
        self.scope_depth += 1;
        // Save proof-ledger lengths for truncation on pop (#8572).
        self.proof_scope_starts.push((
            self.clausification_proofs.len(),
            self.original_clause_theory_proofs.len(),
        ));
        // #6853 fix: Each solver has its own Tseitin state. Advance
        // each state's next_var past the scope selector allocated by push()
        // so future Tseitin encoding avoids it.
        if let Some(ref mut sat) = self.persistent_sat {
            sat.push();
            let sat_total = u32::try_from(sat.total_num_vars()).expect("SAT solver vars fit u32");
            self.tseitin_state.next_var = self.tseitin_state.next_var.max(sat_total + 1);
        } else {
            self.pending_push += 1;
        }
        if let Some(ref mut sat) = self.lia_persistent_sat {
            sat.push();
            let sat_total = u32::try_from(sat.total_num_vars()).expect("SAT solver vars fit u32");
            self.lia_tseitin_state.next_var = self.lia_tseitin_state.next_var.max(sat_total + 1);
        }
    }

    fn pop(&mut self) -> bool {
        if self.scope_depth > 0 {
            self.scope_depth -= 1;
            if let Some(ref mut sat) = self.persistent_sat {
                let _ = sat.pop();
            } else if self.pending_push > 0 {
                self.pending_push -= 1;
            }
            if let Some(ref mut sat) = self.lia_persistent_sat {
                let _ = sat.pop();
            }
            // Trim proof annotation ledgers to the size at scope entry (#8572).
            // This keeps them aligned with the SAT solver's OriginalLedger which
            // also truncates on pop_scope() (#8472). The proof builder in
            // pipeline_setup_macros resizes short vectors with None entries, so
            // any global clause annotations lost here degrade gracefully.
            if let Some((cp_len, tp_len)) = self.proof_scope_starts.pop() {
                self.clausification_proofs.truncate(cp_len);
                self.original_clause_theory_proofs.truncate(tp_len);
            }
            // Scope-aware theory lemma retention (#8157): only remove lemmas
            // learned at the popped scope depth. Lemmas from lower scopes are
            // still valid and retaining them avoids expensive re-derivation on
            // workloads with frequent push/pop (PDR blocking queries, model-checker-consumer).
            //
            // We compare against `self.scope_depth` which has already been
            // decremented above.  Lemmas with depth > scope_depth came from
            // the popped (or deeper) scope and must be discarded.
            let new_depth = self.scope_depth;
            self.theory_lemmas.retain(|(_, depth)| *depth <= new_depth);
            // Clear the dedup key set entirely. The SAT solver's pop already
            // removed the scoped clauses for ALL lemmas (including retained
            // lower-scope ones). The theory_lemma_keys set must be empty so
            // that re-derived lemmas pass the dedup check and get re-added as
            // SAT clauses on the next NeedLemmas cycle. The retained entries
            // in theory_lemmas still serve their purpose: note_applied_theory_lemma
            // replay tells the theory solver what was previously learned.
            self.theory_lemma_keys.clear();
            // Trim theory_lemmas if they exceed the size cap (#8623).
            // Keep the newer half to bound memory growth in long sessions.
            if self.theory_lemmas.len() > MAX_THEORY_LEMMAS {
                let keep_from = self.theory_lemmas.len() / 2;
                self.theory_lemmas.drain(..keep_from);
                // theory_lemma_keys was already cleared above, so no need
                // to rebuild it — it will be populated on the next
                // NeedLemmas cycle when lemmas are re-derived.
            }
            // #8572: Both proof ledgers are now trimmed on pop above,
            // matching the SAT solver's OriginalLedger truncation (#8472).
            // The prior #8154 comment predated ledger truncation and is no
            // longer applicable. The proof builder resizes short vectors
            // with None entries, so global clause annotations lost by
            // truncation degrade gracefully.
            // Invalidate activation scope entries for assertions whose scoped
            // activation clauses were disabled by this pop. Only activations at
            // depth <= scope_depth survive (scope 0 activations are global and
            // always survive; deeper activations are scoped to their push level).
            // Without this, the re-activation check incorrectly skips assertions
            // that were first encoded at a deeper scope (#2822).
            self.assertion_activation_scope
                .retain(|_, depth| *depth <= self.scope_depth);
            // #6853: LIA per-solver activation scopes
            self.lia_assertion_activation_scope
                .retain(|_, depth| *depth <= self.scope_depth);
            // Popping any scope can disable activation clauses that were first added
            // in that popped frame. Re-assert on the next check-sat to restore them.
            self.needs_activation_reassert = true;
            true
        } else {
            false
        }
    }

    fn reset(&mut self) {
        self.persistent_sat = None;
        // #warm-theory soundness: a discarded SAT state must never leave a stale
        // warm theory behind (its overlay/basis would be inconsistent with a
        // rebuilt SAT). Never env-gated — this is a soundness invariant.
        self.persist_theory = None;
        self.lia_persistent_sat = None;
        self.encoded_assertions.clear();
        self.assertion_activation_scope.clear();
        self.tseitin_state = TseitinState::new();
        self.lia_encoded_assertions.clear();
        self.lia_assertion_activation_scope.clear();
        self.lia_tseitin_state = TseitinState::new();
        self.clausification_proofs.clear();
        self.original_clause_theory_proofs.clear();
        self.theory_lemmas.clear();
        self.theory_lemma_keys.clear();
        self.proof_scope_starts.clear();
        self.scope_depth = 0;
        self.pending_push = 0;
        self.lia_derived_assertions.clear();
        self.theory_atoms.clear();
        self.pre_push_assertions.clear();
        self.needs_activation_reassert = false;
        self.theory_conflicts = 0;
        self.theory_propagations = 0;
        self.round_trips = 0;
        self.sat_solve_secs = 0.0;
        self.theory_sync_secs = 0.0;
        self.theory_check_secs = 0.0;
        self.bound_axiom_cache = None;
        self.bool_uf_arg_cache = BoolUfArgCache::default();
    }
}

/// Collect all theory atoms reachable from a set of assertion terms.
///
/// This performs a DFS traversal of each assertion term and collects all sub-terms
/// that are theory atoms (comparisons, equalities, etc.). Used by incremental solving
/// to determine which CNF variables should be synced to the theory solver - only atoms
/// that appear under active assertions should be synced (#338).
///
/// Production callers (the pipeline macros) go through
/// [`collect_active_theory_atoms_cached`] directly; this uncached wrapper is
/// the reference implementation the cache tests compare against.
#[cfg(test)]
pub(crate) fn collect_active_theory_atoms(
    terms: &TermStore,
    assertions: &[TermId],
) -> HashSet<TermId> {
    collect_active_theory_atoms_cached(terms, assertions, None)
}

/// Collect theory atoms reachable (via DFS) from `assertions`, WITHOUT the
/// global Bool-UF-arg scan over the whole `TermStore`.
///
/// This is the assertion-bounded half of `collect_active_theory_atoms`. It is
/// used for per-assumption sub-collections where the (TermStore-global)
/// Bool-UF-arg set has already been added by a sibling call: that set is a pure
/// function of the TermStore, so it is identical regardless of which assertion
/// list is passed, and re-running the O(`terms.len()`) global scan once per
/// assumption is pure waste.
pub(crate) fn collect_reachable_theory_atoms(
    terms: &TermStore,
    assertions: &[TermId],
) -> HashSet<TermId> {
    let mut active_atoms = HashSet::default();
    let mut seen = HashSet::default();
    let mut stack = Vec::new();

    for &term in assertions {
        if seen.insert(term) {
            stack.push(term);
        }
    }

    while let Some(term) = stack.pop() {
        // Check if this term is a theory atom
        if crate::is_theory_atom(terms, term) {
            active_atoms.insert(term);
        }
        // Continue traversing into children
        for child in terms.children(term) {
            if seen.insert(child) {
                stack.push(child);
            }
        }
    }

    active_atoms
}

/// Like `collect_active_theory_atoms`, but reuses a persistent
/// [`BoolUfArgCache`] for the global Bool-UF-arg scan.
///
/// The assertion-reachable theory-atom traversal is bounded by the active
/// assertion set and stays full each call. The Bool-UF-arg scan over the whole
/// `TermStore` is the dominant O(`terms.len()`) cost on the incremental path;
/// when `cache` is `Some`, only terms appended since the last call are scanned,
/// collapsing the per-check-sat cost from O(global terms) to O(new terms) and
/// the whole incremental session from O(N^2) to ~O(N) check-sats.
///
/// CORRECTNESS: with a cache the result is byte-for-byte identical to the
/// `cache: None` full scan, because the Bool-UF-arg set is a pure, monotonic
/// function of the append-only `TermStore` (see [`BoolUfArgCache`]).
pub(crate) fn collect_active_theory_atoms_cached(
    terms: &TermStore,
    assertions: &[TermId],
    cache: Option<&mut BoolUfArgCache>,
) -> HashSet<TermId> {
    let mut active_atoms = collect_reachable_theory_atoms(terms, assertions);

    // Bool-sorted terms that appear as arguments to UF applications must be
    // theory atoms so their truth values reach the EUF solver. Without this,
    // congruence closure cannot propagate through Bool-valued UF arguments
    // (e.g., Concat(y, n) vs Concat(z, n) where y,z are Bool). (#4610)
    // This mirrors the same scan in DpllT::from_tseitin_impl (lib.rs:899-928).
    //
    // This scan is a pure function of the (append-only) TermStore, so when a
    // persistent cache is supplied it runs incrementally over only the terms
    // appended since the last check-sat; otherwise it runs over all terms.
    match cache {
        Some(cache) => cache.collect_into(terms, &mut active_atoms),
        None => {
            for idx in 0..terms.len() {
                let term_id = TermId::new(idx as u32);
                if let TermData::App(ay_core::term::Symbol::Named(name), args) = terms.get(term_id)
                {
                    match name.as_str() {
                        "and" | "or" | "xor" | "=>" | "not" | "=" | "distinct" | "ite" => continue,
                        _ => {}
                    }
                    if args.is_empty() {
                        continue;
                    }
                    for &arg in args {
                        if terms.sort(arg) == &Sort::Bool {
                            active_atoms.insert(arg);
                        }
                    }
                }
            }
        }
    }

    active_atoms
}

/// Theory-side statistics from one incremental round, taken from
/// [`IncrementalTheoryState`] by value so callers can read these fields while a
/// disjoint `&mut` borrow of the same state (e.g. its SAT solver) is live.
#[derive(Debug, Clone, Copy)]
pub(crate) struct IncrementalTheoryStats {
    pub theory_conflicts: u64,
    pub theory_propagations: u64,
    pub round_trips: u64,
    pub sat_solve_secs: f64,
    pub theory_sync_secs: f64,
    pub theory_check_secs: f64,
}

/// Collect theory-level statistics from one incremental round into `stats` (#4705).
///
/// De-macro'd from the former `collect_theory_stats!` so the collection logic is
/// an ordinary, unit-testable function instead of an inlined `macro_rules!`.
/// Takes the round's counters by value (via [`IncrementalTheoryStats`]) rather
/// than `&IncrementalTheoryState`, so call sites that hold a disjoint `&mut`
/// borrow of the state (its SAT solver) still compile. The macro now delegates
/// here, surviving only to capture the private `Executor::last_statistics` field.
pub(crate) fn collect_theory_stats_incremental(stats: &mut Statistics, ts: IncrementalTheoryStats) {
    stats.theory_conflicts = ts.theory_conflicts;
    stats.theory_propagations = ts.theory_propagations;
    // Pre-clamping check: log when theory counters exceed SAT counters (#4706).
    #[cfg(debug_assertions)]
    {
        let sat_conflicts = stats.conflicts;
        let sat_propagations = stats.propagations;
        if ts.theory_conflicts > sat_conflicts {
            tracing::debug!(
                target: "ay::dpll",
                theory_conflicts = ts.theory_conflicts,
                sat_conflicts,
                gap = ts.theory_conflicts - sat_conflicts,
                "incremental: theory conflicts exceed SAT conflicts (clamping will normalize)"
            );
        }
        if ts.theory_propagations > sat_propagations {
            tracing::debug!(
                target: "ay::dpll",
                theory_propagations = ts.theory_propagations,
                sat_propagations,
                gap = ts.theory_propagations - sat_propagations,
                "incremental: theory propagations exceed SAT propagations (clamping will normalize)"
            );
        }
    }
    // Theory conflicts/propagations may exceed raw SAT counters. Clamp SAT
    // counters to preserve Statistics subset invariants (#4758).
    stats.conflicts = stats.conflicts.max(ts.theory_conflicts);
    stats.propagations = stats.propagations.max(ts.theory_propagations);
    // Mirror round_trips so incremental paths expose the same stat as DpllT (#4802).
    stats.set_int("dpll.round_trips", ts.round_trips);
    // Export timing keys so :all-statistics includes them on incremental paths (#5175).
    stats.set_float("time.dpll.sat_solve", ts.sat_solve_secs);
    stats.set_float("time.dpll.theory_sync", ts.theory_sync_secs);
    stats.set_float("time.dpll.theory_check", ts.theory_check_secs);
    // #8165: drain thread-local theory observability counters.
    let obs = crate::combined_solvers::theory_stats::drain_stats();
    stats.set_int("smt.no_rounds", obs.no_rounds);
    stats.set_int("smt.unknown_returns", obs.unknown_returns);
    stats.set_int("smt.diseq_propagations", obs.diseq_propagations);
    stats.set_int("smt.conflicts.lia", obs.conflicts_lia);
    stats.set_int("smt.conflicts.lra", obs.conflicts_lra);
    stats.set_int("smt.conflicts.euf", obs.conflicts_euf);
    stats.set_int("smt.conflicts.arrays", obs.conflicts_arrays);
    stats.set_int("smt.checks.lia", obs.checks_lia);
    stats.set_int("smt.checks.lra", obs.checks_lra);
    stats.set_int("smt.checks.euf", obs.checks_euf);
    stats.set_int("smt.checks.arrays", obs.checks_arrays);
    stats.set_int("smt.props.lia", obs.props_lia);
    stats.set_int("smt.props.lra", obs.props_lra);
    stats.set_int("smt.props.euf", obs.props_euf);
    stats.set_int("smt.partial_clauses", obs.partial_clauses);
    stats.set_int("smt.replay_covered_by_calls", obs.replay_covered_by_calls);
    stats.debug_assert_consistency();
}
