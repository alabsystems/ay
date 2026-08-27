// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental BV solving state with persistent SAT reuse.
//!
//! Extracted from `mod.rs` for code health (#5970).

// #8529: Use deterministic hash maps in all builds.
use ay_bv::{BvBits, DelayedBvOp};
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{TermId, TseitinState};
use ay_sat::Solver as SatSolver;

use super::IncrementalSubsystem;

/// Persistent state for incremental BV solving with persistent SAT reuse.
///
/// Maintains:
/// - Cached term-to-bits mappings for BV terms
/// - A persistent SAT solver reused across repeated check-sat calls
/// - Tseitin state for consistent variable mappings
/// - Scope tracking with pending push support
///
/// Key design invariant:
/// - Definitional clauses are added GLOBALLY via add_clause_global()
/// - Only assertion activation (unit clause on root literal) is scoped
/// - This ensures cached term→var and term→bits mappings remain valid after pop
pub(crate) struct IncrementalBvState {
    /// Cached term-to-bits mappings from BvSolver
    pub(crate) term_to_bits: HashMap<TermId, BvBits>,
    /// Next BV variable to allocate (1-indexed for DIMACS compatibility)
    pub(crate) next_bv_var: u32,
    /// Current scope depth (0 = global, 1+ = in push scope)
    pub(crate) scope_depth: usize,
    /// Number of pending push operations to apply when solver is created
    pub(crate) pending_pushes: usize,

    // Persistent SAT fields
    /// Persistent SAT solver reused until a pop/reset forces a rebuild.
    pub(crate) persistent_sat: Option<SatSolver>,
    /// Persistent Tseitin state for consistent variable mappings
    pub(crate) tseitin_state: TseitinState,
    /// Map from encoded assertions to their Tseitin root literals (#1452).
    /// Used to re-add activation clauses after pop - definitional clauses are global
    /// but activation clauses are scoped.
    pub(crate) encoded_assertions: HashMap<TermId, i32>,
    /// Shallowest scope where each assertion already has a live activation unit.
    ///
    /// An activation clause added at depth `d` remains active for deeper scopes
    /// until a pop below `d`. Track that depth so repeated check-sat calls do
    /// not keep appending duplicate unit clauses.
    pub(crate) assertion_activation_scope: HashMap<TermId, usize>,
    /// Number of SAT variables allocated (Tseitin + BV vars)
    pub(crate) sat_num_vars: usize,
    /// Stable BV variable offset (#1453). Set once when first BV clauses are encoded.
    /// Must remain stable across push/pop for correct model extraction.
    pub(crate) bv_var_offset: Option<i32>,
    /// Ordered pairs of BV equality predicates whose congruence clauses are already global.
    ///
    /// The incremental BV path reuses one SAT solver across repeated check-sat calls.
    /// Track emitted equality-congruence pairs so the same binary clauses are not
    /// appended again when no relevant assertions changed.
    pub(crate) emitted_bv_eq_congruence_pairs: HashSet<(TermId, TermId)>,
    /// Cache of BvSolver's predicate_to_var mapping (#1454).
    /// Maps BV predicate terms (equalities, comparisons) to their bitblasted CNF variables.
    /// Must be cached because re-bitblasting allocates NEW BV variables.
    pub(crate) predicate_to_var: HashMap<TermId, i32>,
    /// Cache of BvSolver's bool_to_var mapping.
    ///
    /// Maps Bool terms that appear *inside* BV terms (e.g., BV `ite` conditions) to
    /// their bitblasted CNF literals. This must be cached because re-bitblasting
    /// allocates NEW BV variables, and previously-added BV circuit clauses must
    /// continue to reference the same variable for the same term.
    pub(crate) bool_to_var: HashMap<TermId, i32>,
    /// Bool terms already linked between Tseitin vars and BV literals.
    ///
    /// This includes BV predicates and Bool terms that appear inside BV terms.
    /// We add equivalences (tseitin_var ↔ bv_lit) globally, so repeated check-sat
    /// calls must not re-add them once the current SAT encoding already contains
    /// the corresponding clauses.
    pub(crate) linked_equivalence_terms: HashSet<TermId>,
    /// Bool terms that are conditions for BV-sorted ITE expressions.
    ///
    /// Historical: #1696 originally restricted linking to only ITE conditions.
    /// Since #5457, ALL Bool atoms (including DT testers) are linked via Tseitin
    /// equivalences in `link_all_bool_atoms()`. This field is still populated
    /// but is no longer the exclusive gating set for linking decisions.
    pub(crate) bv_ite_conditions: HashSet<TermId>,
    /// Delayed BV operations from previous scopes (#7015).
    ///
    /// When a scope returns UNSAT before the delayed circuit is built (e.g., OR-chain
    /// proactive clauses suffice to prove UNSAT), the circuit is never added. On the
    /// next check-sat, the fresh BvSolver won't create delayed ops for cached terms
    /// (get_bits returns immediately). Without this persistence, the result bits remain
    /// unconstrained by any circuit, leading to spurious SAT models.
    pub(crate) delayed_ops: Vec<DelayedBvOp>,
}

impl IncrementalBvState {
    pub(crate) fn new() -> Self {
        Self {
            term_to_bits: HashMap::default(),
            next_bv_var: 1,
            scope_depth: 0,
            pending_pushes: 0,
            persistent_sat: None,
            tseitin_state: TseitinState::new(),
            encoded_assertions: HashMap::default(),
            assertion_activation_scope: HashMap::default(),
            sat_num_vars: 0,
            bv_var_offset: None,
            emitted_bv_eq_congruence_pairs: HashSet::default(),
            predicate_to_var: HashMap::default(),
            bool_to_var: HashMap::default(),
            linked_equivalence_terms: HashSet::default(),
            bv_ite_conditions: HashSet::default(),
            delayed_ops: Vec::new(),
        }
    }

    /// Sync Tseitin next_var to account for total SAT solver variables.
    /// This prevents Tseitin variables from overlapping with scope selectors
    /// and with BV variables (which occupy SAT positions bv_var + bv_var_offset).
    pub(crate) fn sync_tseitin_next_var(&mut self) {
        if let Some(ref sat) = self.persistent_sat {
            // Use total_num_vars() which includes scope selector variables
            let sat_total = sat.total_num_vars() as u32;
            // Tseitin uses 1-indexed variables
            self.tseitin_state.next_var = self.tseitin_state.next_var.max(sat_total + 1);
        }
        // Tseitin vars must also be beyond the BV + offset range (#7015).
        // BV vars occupy SAT positions [bv_var + offset], so the highest BV SAT
        // position is (next_bv_var - 1) + offset. Tseitin vars must start after that.
        if let Some(offset) = self.bv_var_offset {
            let max_bv_sat_pos = (self.next_bv_var as i32 - 1) + offset;
            if max_bv_sat_pos >= 0 {
                self.tseitin_state.next_var =
                    self.tseitin_state.next_var.max(max_bv_sat_pos as u32 + 1);
            }
        }
    }

    /// Sync next_bv_var to account for Tseitin and scope selector allocations.
    /// This prevents BV variables from overlapping with Tseitin or selector vars.
    pub(crate) fn sync_next_bv_var(&mut self) {
        // BV vars should not overlap with Tseitin vars
        self.next_bv_var = self.next_bv_var.max(self.tseitin_state.next_var);
        if let Some(ref sat) = self.persistent_sat {
            // Account for total vars (includes scope selectors)
            let sat_total = sat.total_num_vars() as u32;
            self.next_bv_var = self.next_bv_var.max(sat_total + 1);
        }
    }

    /// Drop the persistent SAT solver and all BV/Tseitin caches, but preserve
    /// frontend scope depth so the next check-sat can rebuild the solver stack.
    ///
    /// This is the FULL teardown, reserved for `reset()` (`(reset)` /
    /// `(reset-assertions)`), where the assertion set itself is discarded and
    /// no cached encoding can be reused.
    ///
    /// It is deliberately NOT the `pop()` path — see `pop()` for why a scope
    /// retraction needs no teardown at all.
    pub(crate) fn reset_sat_encoding_for_rebuild(&mut self) {
        self.term_to_bits.clear();
        self.next_bv_var = 1;
        self.pending_pushes = self.scope_depth;
        self.persistent_sat = None;
        self.tseitin_state = TseitinState::new();
        self.encoded_assertions.clear();
        self.assertion_activation_scope.clear();
        self.sat_num_vars = 0;
        self.bv_var_offset = None;
        self.emitted_bv_eq_congruence_pairs.clear();
        self.predicate_to_var.clear();
        self.bool_to_var.clear();
        self.linked_equivalence_terms.clear();
        self.bv_ite_conditions.clear();
        self.delayed_ops.clear();
    }
}

impl IncrementalSubsystem for IncrementalBvState {
    fn push(&mut self) {
        self.scope_depth += 1;
        // Track pending pushes to apply when SAT solver is created
        if self.persistent_sat.is_none() {
            self.pending_pushes += 1;
        } else if let Some(ref mut sat) = self.persistent_sat {
            sat.push();
        }
    }

    /// Retract one assertion scope WITHOUT destroying any encoding.
    ///
    /// SAFE BY CONSTRUCTION, not by teardown. Every clause this subsystem
    /// installs is in exactly one of two classes:
    ///
    /// 1. **Scope-independent, installed globally.** Tseitin definitions, BV
    ///    circuit clauses, Tseitin↔BV equivalence links, array axioms, EUF and
    ///    non-BV congruence axioms, BV equality congruence, and delayed-op
    ///    circuits all go in through `add_clause_global` /
    ///    `add_offset_clauses_global` (see `bv_incremental.rs`). Each either
    ///    defines a fresh variable in terms of existing ones — a definitional
    ///    extension, which removes no model of the user's formula — or is a
    ///    theory tautology. Neither can over-constrain a later scope.
    ///    `add_clause_global` also routes them through
    ///    `OriginalLedger::push_clause_global`, which replays them past
    ///    `pop_scope` truncation, so they survive a SAT-level pop in the ledger
    ///    as well as in the arena.
    ///
    ///    The mechanical check behind "scope-independent": exactly ONE global
    ///    generator on this path reads the assertion set at all
    ///    (`build_bv_eq_congruence_batch`, which takes `&self.ctx.assertions`;
    ///    every other generator is handed `&[]`), and its output is guarded by
    ///    the hypothesis literal so it is a tautology too. That guard is #7892's
    ///    actual root cause — see `bv_encoding::generate_bv_eq_congruence_clauses`
    ///    and the barrier
    ///    `bv_eq_congruence_clauses_are_guarded_by_the_hypothesis`. Without it,
    ///    an equality asserted inside a push leaked its conclusion past the
    ///    matching pop: a false UNSAT.
    ///
    /// 2. **Assertion activation, a unit on the Tseitin root, installed
    ///    scoped.** At depth 0 that is a permanent unit; at depth d>0
    ///    `Solver::add_clause` appends the scope selector, making it
    ///    `[root, +selector_d]`, and the scope is entered by ASSUMING
    ///    `¬selector_d` (`compose_scope_assumptions`). That is an activation
    ///    literal in AY's idiom. `Solver::pop` asserts `+selector_d`
    ///    permanently and garbage-collects the guarded clauses, retracting the
    ///    activation exactly. Learned clauses are resolvents of installed
    ///    clauses only — assumptions are decisions, never premises — so they
    ///    are implied by the global formula and survive legitimately.
    ///
    /// Nothing scoped is ever a permanent constraint, so a pop cannot leave an
    /// over-constraining clause behind, so there is nothing to reset. The
    /// expensive state — the bit-blast cache (`term_to_bits`), the Tseitin
    /// variable mapping, the CNF already emitted, and the SAT solver with its
    /// learned clauses — is kept for the whole session.
    ///
    /// Provenance: this is the invariant Bitwuzla 0.8.0 relies on, studied from
    /// its source (`src/solving_context.cpp` `pop`;
    /// `src/solver/bv/bv_bitblast_solver.h`, where only the assertion and
    /// assumption vectors are backtrackable while the bitblaster cache, CNF
    /// encoder and SAT solver are plain members; and
    /// `src/solver/solver_engine.cpp`'s `top_level = level == 0` split that
    /// decides assertion-vs-assumption). Bitwuzla is MIT; the algorithm was
    /// studied and reimplemented on AY's existing scope-selector machinery. No
    /// code was copied.
    ///
    /// The one thing that DOES have to be retracted is the bookkeeping that
    /// records where an assertion's activation unit lives: units installed
    /// deeper than the new frontend depth were just satisfied by `Solver::pop`,
    /// so they must be re-added on the next check-sat (#2822, the same
    /// invariant `IncrementalTheoryState::pop` maintains).
    ///
    /// Pinned by `incremental_bv_state_pop_keeps_the_bitblast_and_the_solver`
    /// and `incremental_bv_state_pop_unwinds_one_sat_scope_and_keeps_every_cache`.
    fn pop(&mut self) -> bool {
        if self.scope_depth > 0 {
            self.scope_depth -= 1;
            if let Some(ref mut sat) = self.persistent_sat {
                let _ = sat.pop();
            } else if self.pending_pushes > 0 {
                self.pending_pushes -= 1;
            }
            self.assertion_activation_scope
                .retain(|_, depth| *depth <= self.scope_depth);
            true
        } else {
            false
        }
    }

    fn reset(&mut self) {
        self.scope_depth = 0;
        self.reset_sat_encoding_for_rebuild();
    }
}
