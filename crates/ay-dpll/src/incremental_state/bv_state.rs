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
    /// Soundness-first fallback for incremental BV-family logics (#7892):
    /// learned clauses or cached encodings from earlier check-sat calls can
    /// over-constrain later push/pop scopes and cause false UNSAT.
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

    fn pop(&mut self) -> bool {
        if self.scope_depth > 0 {
            self.scope_depth -= 1;
            // A pop invalidates any learned clauses and scoped activations
            // derived beneath the new frontend depth. Rebuild from the
            // surviving assertions on the next check-sat instead of carrying
            // stale SAT state forward.
            self.reset_sat_encoding_for_rebuild();
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
