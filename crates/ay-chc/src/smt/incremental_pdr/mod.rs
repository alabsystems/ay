// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental SAT context for PDR blocking queries (#6358).
//!
//! PDR's blocking loop issues hundreds of SMT queries per benchmark, each sharing
//! the same transition relation and frame lemmas but differing only in the proof
//! obligation. Previously, every query called `smt.reset() + check_sat()`, destroying
//! all solver state (learned clauses, VSIDS scores, Tseitin encodings).
//!
//! This context keeps a persistent SAT solver across queries. The transition relation
//! is encoded once as permanent background clauses. Frame lemmas use activation
//! literals for level-scoped toggling (Z3 Spacer pattern). Per-query assertions
//! (proof obligations) use SAT assumptions.
//!
//! Each `IncrementalPdrContext` owns its own `SmtContext` (`own_smt`) so that
//! TermIds in the persistent Tseitin state are never invalidated by the caller's
//! `smt.reset()` (which destroys the `TermStore`). This fixes the stale-TermId
//! crash discovered in testing.
//!
//! Reference: Z3 Spacer `spacer_prop_solver.cpp:129-137` (activation literal pattern).

mod solve;
mod theory;

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
mod tests;

use super::context::SmtContext;
use crate::ChcExpr;
#[cfg(test)]
use ay_core::TermId;

/// Per-predicate incremental SMT context for PDR blocking queries.
///
/// Background (transition relation, frame lemmas) is encoded once. Per-query
/// assertions use SAT assumptions. Frame lemmas use activation literals for
/// level-scoped toggling without push/pop.
///
/// # Activation literal pattern (Z3 Spacer)
///
/// A lemma at level k is asserted as `(lemma_clause OR act_k)`. The lemma is
/// active only when `NOT act_k` is assumed. This allows free level switching
/// without destroying solver state.
///
/// # Own SmtContext
///
/// Each context owns a private `SmtContext` so that TermIds stored in the
/// Tseitin state remain valid across the caller's `smt.reset()` calls.
pub(crate) struct IncrementalPdrContext {
    /// Persistent SAT solver — learned clauses carry across queries.
    pub(super) sat: ay_sat::Solver,
    /// Number of CNF variables allocated.
    pub(super) num_vars: u32,
    /// Saved Tseitin state for encoding reuse across queries.
    pub(super) tseitin_state: Option<ay_core::TseitinState>,
    /// Whether the background has been finalized.
    pub(super) finalized: bool,
    /// Sticky flag: conversion budget exceeded during background encoding.
    pub(super) background_conversion_budget_exceeded: bool,
    /// Activation literal SAT variables, one per level.
    pub(super) level_act_vars: Vec<u32>,
    /// Query-family activation variables for guarded background segments.
    ///
    /// Each variable gates a reusable background segment: the segment is encoded
    /// as `(formula OR act_var)` and is active when `NOT act_var` is assumed.
    /// This generalizes the level activation pattern to arbitrary query-family
    /// backgrounds (clause selection, fact selection, etc.).
    ///
    /// Allocated by `alloc_query_activation()`, read by `PredicatePropSolver`.
    /// Reference: Z3 Spacer `prop_solver` uses the same pattern for clause
    /// activation within a per-predicate solver.
    pub(super) query_act_vars: Vec<u32>,
    /// Lemma expressions tracked per level for corruption detection.
    pub(super) lemma_exprs: Vec<Vec<ChcExpr>>,
    /// Private SmtContext — TermIds here are never invalidated by caller resets.
    pub(super) own_smt: SmtContext,
}

/// Free function to create a Tseitin encoder from saved state.
///
/// Takes individual fields rather than `&mut self` to avoid borrow conflicts:
/// the Tseitin borrows `own_smt.terms` immutably, while other `self` fields
/// (e.g., `sat`, `num_vars`) need mutable access concurrently.
///
/// `num_vars` is the current variable count — ensures the Tseitin encoder
/// allocates variables past any activation literals already allocated.
pub(super) fn take_tseitin<'a>(
    tseitin_state: &mut Option<ay_core::TseitinState>,
    terms: &'a ay_core::TermStore,
    num_vars: u32,
) -> ay_core::Tseitin<'a> {
    if let Some(mut state) = tseitin_state.take() {
        // Ensure next_var is past any activation literals created since the
        // state was last saved. Without this, new Tseitin variables could
        // collide with activation variables allocated between save and restore.
        if state.next_var <= num_vars {
            state.next_var = num_vars + 1;
        }
        ay_core::Tseitin::from_state(terms, state)
    } else {
        // Create a fresh Tseitin encoder that starts past activation variables.
        let state = ay_core::TseitinState {
            term_to_var: std::collections::BTreeMap::new(),
            var_to_term: std::collections::BTreeMap::new(),
            next_var: num_vars + 1,
            encoded: std::collections::BTreeMap::new(),
        };
        ay_core::Tseitin::from_state(terms, state)
    }
}

impl IncrementalPdrContext {
    /// Create a new incremental PDR context.
    pub(crate) fn new() -> Self {
        let mut sat = ay_sat::Solver::new(0);
        // Disable preprocessing for incremental PDR solving. The SAT solver's
        // preprocessing (BVE, subsumption, decompose, etc.) can eliminate
        // variables and clauses that are needed for activation-literal-based
        // incremental queries. Freezing assumption variables before each query
        // is insufficient because the clauses themselves may be removed.
        //
        // Also mark the solver as incremental because this SAT instance is
        // persistent and reused across many PDR queries. Incremental mode
        // disables destructive inprocessing (BVE, BCE, conditioning, sweep,
        // congruence, factorize, decompose) that would modify the clause
        // database in ways unsafe for reuse, while allowing non-destructive
        // inprocessing (vivification, subsumption, probe, backbone, transred,
        // htr, reorder) to fire normally and benefit from amortization.
        sat.set_preprocess_enabled(false);
        sat.set_incremental_mode();
        Self {
            sat,
            num_vars: 0,
            tseitin_state: None,
            finalized: false,
            background_conversion_budget_exceeded: false,
            level_act_vars: Vec::new(),
            query_act_vars: Vec::new(),
            lemma_exprs: Vec::new(),
            own_smt: SmtContext::new(),
        }
    }

    /// Assert a background formula (transition relation) as permanent clauses.
    ///
    /// Must be called before `finalize_background()`. The formula is preprocessed,
    /// converted to a TermId via the owned SmtContext, and encoded via Tseitin
    /// into permanent SAT clauses.
    ///
    /// Used by tests for standalone IncrementalPdrContext queries. Production code
    /// uses `PredicatePropSolver` which calls `assert_background_guarded()` instead.
    #[cfg(test)]
    pub(crate) fn assert_background(&mut self, expr: &ChcExpr) {
        debug_assert!(!self.finalized, "cannot assert background after finalize");
        if self.background_conversion_budget_exceeded {
            return;
        }

        let namespace = format!("bg{}", self.lemma_exprs.len());
        let normalized = SmtContext::preprocess_incremental_assumption(expr, &namespace);

        self.own_smt.reset_conversion_budget();
        let term = self.own_smt.convert_expr(&normalized);
        if self.own_smt.conversion_budget_exceeded() {
            self.background_conversion_budget_exceeded = true;
            return;
        }

        self.encode_and_assert_permanent(term);
    }

    /// Finalize background encoding. After this, queries can be issued.
    pub(crate) fn finalize_background(&mut self) {
        self.finalized = true;
    }

    /// Ensure activation literals exist up to the given level.
    pub(super) fn ensure_level(&mut self, level: usize) {
        while self.level_act_vars.len() <= level {
            self.num_vars += 1;
            let act_var = self.num_vars;
            self.sat.ensure_num_vars(self.num_vars as usize);
            self.level_act_vars.push(act_var);
            self.lemma_exprs.push(Vec::new());
        }
    }

    /// Assert a lemma at a specific frame level, guarded by activation literal.
    ///
    /// Encodes `(lemma_cnf OR act_k)` as permanent clauses. The lemma is active
    /// only when `NOT act_k` is assumed during a query at level >= k.
    pub(crate) fn assert_lemma_at_level(&mut self, lemma: &ChcExpr, level: usize) {
        if self.background_conversion_budget_exceeded {
            return;
        }

        self.ensure_level(level);
        let act_var = self.level_act_vars[level];

        let namespace = format!("lem{level}_{}", self.lemma_exprs[level].len());
        let normalized = SmtContext::preprocess_incremental_assumption(lemma, &namespace);

        self.own_smt.reset_conversion_budget();
        let term = self.own_smt.convert_expr(&normalized);
        if self.own_smt.conversion_budget_exceeded() {
            return;
        }

        let mut tseitin = take_tseitin(&mut self.tseitin_state, &self.own_smt.terms, self.num_vars);
        let encoded = tseitin.encode_assertion(term);
        self.sat.ensure_num_vars(tseitin.num_vars() as usize);

        // Add definitional clauses as global (they are tautologies).
        for clause in &encoded.def_clauses {
            let lits: Vec<ay_sat::Literal> = clause
                .0
                .iter()
                .map(|&lit| ay_sat::Literal::from_dimacs(lit))
                .collect();
            self.sat.add_clause_global(lits);
        }

        // Assert `(root OR act_k)` as a permanent clause.
        let root_lit = ay_sat::Literal::from_dimacs(encoded.root_lit);
        let act_lit = ay_sat::Literal::positive(ay_sat::Variable::new(act_var - 1));
        self.sat.add_clause_global(vec![root_lit, act_lit]);

        self.num_vars = tseitin.num_vars();
        self.tseitin_state = Some(tseitin.into_state());
        self.lemma_exprs[level].push(lemma.clone());
    }

    // --- Query-family activation (#6358) ---

    /// Allocate a new query-family activation variable.
    ///
    /// Returns the SAT variable number (1-based) that can be used with
    /// `assert_background_guarded()`. The caller uses `NOT act_var` as an
    /// assumption to activate the guarded segment, or `act_var` to deactivate it.
    ///
    /// This generalizes the level activation pattern: level activations gate
    /// frame lemmas by PDR level, query activations gate reusable background
    /// segments by query family (clause, fact, init-match, etc.).
    pub(crate) fn alloc_query_activation(&mut self) -> u32 {
        self.num_vars += 1;
        let act_var = self.num_vars;
        self.sat.ensure_num_vars(self.num_vars as usize);
        self.query_act_vars.push(act_var);
        act_var
    }

    /// Assert a background formula guarded by a query activation variable.
    ///
    /// Encodes `(formula_cnf OR act_var)` as permanent clauses. The formula
    /// is active only when `NOT act_var` is assumed during a query.
    ///
    /// This is the same pattern as `assert_lemma_at_level()` but generalized:
    /// level activations scope by frame level, query activations scope by
    /// arbitrary background segment (clause body, fact constraint, etc.).
    ///
    /// Must be called after `finalize_background()` — guarded segments extend
    /// the permanent background, they do not replace it.
    pub(crate) fn assert_background_guarded(&mut self, expr: &ChcExpr, act_var: u32) {
        if self.background_conversion_budget_exceeded {
            return;
        }

        let namespace = format!("qbg{act_var}_{}", self.query_act_vars.len());
        let normalized = SmtContext::preprocess_incremental_assumption(expr, &namespace);

        self.own_smt.reset_conversion_budget();
        let term = self.own_smt.convert_expr(&normalized);
        if self.own_smt.conversion_budget_exceeded() {
            return;
        }

        let mut tseitin = take_tseitin(&mut self.tseitin_state, &self.own_smt.terms, self.num_vars);
        let encoded = tseitin.encode_assertion(term);
        self.sat.ensure_num_vars(tseitin.num_vars() as usize);

        // Add definitional clauses as global (they are tautologies).
        for clause in &encoded.def_clauses {
            let lits: Vec<ay_sat::Literal> = clause
                .0
                .iter()
                .map(|&lit| ay_sat::Literal::from_dimacs(lit))
                .collect();
            self.sat.add_clause_global(lits);
        }

        // Assert `(root OR act_var)` — the formula is active when NOT act_var is assumed.
        let root_lit = ay_sat::Literal::from_dimacs(encoded.root_lit);
        let act_lit = ay_sat::Literal::positive(ay_sat::Variable::new(act_var - 1));
        self.sat.add_clause_global(vec![root_lit, act_lit]);

        self.num_vars = tseitin.num_vars();
        self.tseitin_state = Some(tseitin.into_state());
    }

    // --- Tseitin helpers ---

    /// Encode a term as permanent clauses (no activation literal).
    #[cfg(test)]
    fn encode_and_assert_permanent(&mut self, term: TermId) {
        let mut tseitin = take_tseitin(&mut self.tseitin_state, &self.own_smt.terms, self.num_vars);
        let _root = tseitin.encode_and_assert(term);
        let new_clauses = tseitin.take_new_clauses();
        self.sat.ensure_num_vars(tseitin.num_vars() as usize);

        for clause in &new_clauses {
            let lits: Vec<ay_sat::Literal> = clause
                .0
                .iter()
                .map(|&lit| ay_sat::Literal::from_dimacs(lit))
                .collect();
            self.sat.add_clause_global(lits);
        }

        self.num_vars = tseitin.num_vars();
        self.tseitin_state = Some(tseitin.into_state());
    }

    /// Collect all active lemma expressions at a given level (for model validation).
    /// Used by tests for corruption-detection cross-checks.
    #[cfg(test)]
    pub(super) fn all_active_lemma_exprs(&self, level: usize) -> impl Iterator<Item = &ChcExpr> {
        self.lemma_exprs
            .iter()
            .enumerate()
            .filter_map(move |(k, exprs)| if k >= level { Some(exprs.iter()) } else { None })
            .flatten()
    }
}
