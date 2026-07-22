// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Reach-fact solver for fast must-reachability intersection checks.
//!
//! This implements "Option B+" from the development design notes:
//! a disjunction-based approach with tag variables that returns matching reach fact IDs.
//!
//! The key insight is that checking if a state intersects ANY cached reach_fact
//! can be reduced to a single satisfiability query: `state ∧ (rf1 ∨ ... ∨ rfn)`.
//!
//! By including per-entry tag variables in the query (`(fact_i ∧ tag_i)`), we can
//! extract from the SAT model which specific reach fact matched, enabling
//! immediate witness construction without clause iteration.
//!
//! ## Limitations vs Z3 Spacer (Option A)
//!
//! Z3 uses tag chains with incremental push/pop for O(1) amortized queries.
//! This implementation uses the shared SMT context with reset, which means:
//! - No incremental solving: learned clauses lost after each reset
//! - Formula re-encoding on each query
//!
//! The disjunction is cached to avoid re-building, but each query still requires
//! a full SAT solve. This is sufficient for correctness and provides speedup
//! over iterating all clauses, but leaves room for future optimization.

use super::reach_fact::ReachFactId;
use crate::expr::ChcVar;
use crate::smt::{SmtContext, SmtResult, SmtValue};
use crate::{ChcExpr, ChcOp, ChcSort, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;

/// Cap per-predicate reach-fact cache in `ReachSolver`.
const MAX_REACH_ENTRIES_PER_PREDICATE: usize = 20_000;
/// Cap on number of predicates tracked in `ReachSolverStore`.
const MAX_REACH_SOLVER_PREDICATES: usize = 2_048;

/// A reach-fact entry with tag variable for identification in SAT models.
///
/// When the reach solver builds a disjunction query `(fact0 ∧ tag0) ∨ (fact1 ∧ tag1) ∨ ...`,
/// and the query is SAT, the model will have at least one tag set to true, allowing
/// us to identify which reach fact matched.
#[derive(Debug, Clone)]
struct ReachEntry {
    /// Optional ReachFactId for entries with complete premise chains.
    /// `None` = "filter-only" entry (helps negative filtering but can't produce witness).
    id: Option<ReachFactId>,
    /// The formula describing the reachable state over canonical variables.
    fact: ChcExpr,
    /// Fresh Boolean variable used to identify this entry in a SAT model.
    tag: ChcVar,
}

/// Per-predicate reach fact solver for fast intersection checks.
///
/// Maintains a collection of reach facts (concrete reachable states) and
/// provides fast intersection queries to check if a given state intersects
/// any cached reach fact. Supports both:
/// - `is_reachable`: Boolean-only check (negative filter)
/// - `find_match`: Returns the matching `ReachFactId` and model for witness construction
#[derive(Debug)]
pub(crate) struct ReachSolver {
    /// Reach-fact entries with tag variables for identification
    entries: Vec<ReachEntry>,
    /// Counter for generating unique tag variable names
    tag_counter: u64,
    /// Precomputed reach-fact disjunction: `fact0 ∨ fact1 ∨ ...`
    /// Invalidated when new entries are added.
    /// Used by `is_reachable` for fast Boolean check (tags not needed).
    cached_fact_disjunction: Option<ChcExpr>,
    /// Precomputed tagged disjunction for backed entries only:
    /// `(fact_i ∧ tag_i) ∨ ...` for entries where `id.is_some()`.
    ///
    /// Used by `find_match` to ensure SAT implies some backed tag is `true`,
    /// avoiding missed matches when an identical filter-only entry exists.
    ///
    /// Invalidated only when backed entries are added (filter-only adds don't affect it).
    cached_backed_tagged_disjunction: Option<ChcExpr>,
    /// Precomputed untagged disjunction for backed entries only.
    /// Used by `is_reachable_backed` to check intersection with proven-reachable
    /// states only, excluding heuristic filter-only entries.
    cached_backed_disjunction: Option<ChcExpr>,
}

impl Default for ReachSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl ReachSolver {
    /// Create a new reach solver.
    pub(crate) fn new() -> Self {
        Self {
            entries: Vec::new(),
            tag_counter: 0,
            cached_fact_disjunction: None,
            cached_backed_tagged_disjunction: None,
            cached_backed_disjunction: None,
        }
    }

    /// Generate a fresh tag variable name.
    fn fresh_tag(&mut self) -> ChcVar {
        let name = format!("__rf_tag_{}", self.tag_counter);
        self.tag_counter += 1;
        ChcVar::new(name, ChcSort::Bool)
    }

    /// Add a reach fact without a backing ReachFactId (filter-only).
    ///
    /// The fact should be a formula over the predicate's canonical variables
    /// describing a concrete reachable state. Filter-only entries contribute
    /// to `is_reachable` checks but never return from `find_match`.
    pub(crate) fn add(&mut self, fact: ChcExpr) {
        self.add_internal(None, fact);
    }

    /// Add a reach fact backed by a ReachFactId (matchable).
    ///
    /// Entries added with this method can be returned from `find_match` for
    /// immediate witness construction without clause iteration.
    pub(crate) fn add_backed(&mut self, id: ReachFactId, fact: ChcExpr) {
        self.add_internal(Some(id), fact);
    }

    fn evict_one_entry(&mut self) {
        let victim_idx = self
            .entries
            .iter()
            .position(|entry| entry.id.is_none())
            .unwrap_or(0);
        let was_backed = self.entries[victim_idx].id.is_some();
        self.entries.remove(victim_idx);
        self.cached_fact_disjunction = None;
        self.cached_backed_tagged_disjunction = None;
        if was_backed {
            self.cached_backed_disjunction = None;
        }
    }

    /// Internal implementation for adding entries.
    fn add_internal(&mut self, id: Option<ReachFactId>, fact: ChcExpr) {
        self.add_internal_with_cap(id, fact, MAX_REACH_ENTRIES_PER_PREDICATE);
    }

    /// Internal implementation for adding entries with an explicit cap.
    fn add_internal_with_cap(&mut self, id: Option<ReachFactId>, fact: ChcExpr, cap: usize) {
        debug_assert!(cap > 0, "reach-solver entry cap must be > 0");
        if matches!(&fact, ChcExpr::Bool(false)) {
            return;
        }
        if self.entries.len() >= cap {
            self.evict_one_entry();
        }
        let is_backed = id.is_some();
        let tag = self.fresh_tag();
        self.entries.push(ReachEntry { id, fact, tag });
        // Invalidate cached disjunctions.
        self.cached_fact_disjunction = None;
        if is_backed {
            self.cached_backed_tagged_disjunction = None;
            self.cached_backed_disjunction = None;
        }
    }

    /// Check if state intersects any cached reach fact.
    ///
    /// Returns true if `state ∧ (rf1 ∨ rf2 ∨ ... ∨ rfn)` is satisfiable,
    /// i.e., the state has non-empty intersection with at least one reach fact.
    pub(crate) fn is_reachable(&mut self, smt: &mut SmtContext, state: &ChcExpr) -> bool {
        if self.entries.is_empty() {
            return false;
        }

        // Build or reuse cached disjunction (untagged for efficiency)
        let disjunction = self.get_fact_disjunction();

        // Query: state ∧ disjunction
        let query = ChcExpr::and(state.clone(), disjunction);

        smt.reset();
        // SOUNDNESS NOTE (#2659): Unknown → false is conservative. This is a positive
        // short-circuit cache — returning false just means we fall through to the full
        // clause-level check in check_must_reachability(), which will find the CEX if
        // it exists. No counterexamples are permanently lost.
        matches!(smt.check_sat(&query), SmtResult::Sat(_))
    }

    /// Check if state intersects any **backed** (proven-reachable) reach fact.
    ///
    /// Unlike `is_reachable`, this excludes filter-only entries (heuristic
    /// loop-closure enrichments) that may over-approximate reachable states.
    /// Use this for entry-inductiveness checks where spurious reach-fact
    /// intersection would incorrectly reject valid invariants.
    pub(crate) fn is_reachable_backed(&mut self, smt: &mut SmtContext, state: &ChcExpr) -> bool {
        if !self.entries.iter().any(|e| e.id.is_some()) {
            return false;
        }

        let disjunction = self.get_backed_disjunction();
        if matches!(disjunction, ChcExpr::Bool(false)) {
            return false;
        }

        let query = ChcExpr::and(state.clone(), disjunction);
        smt.reset();
        matches!(smt.check_sat(&query), SmtResult::Sat(_))
    }

    /// Find a matching backed reach fact that intersects the given state.
    ///
    /// Returns `Some((ReachFactId, model))` if `state` intersects a backed reach fact,
    /// where `model` is the SAT model from the intersection query.
    ///
    /// Only returns entries that have a `ReachFactId` (added via `add_backed`).
    /// Filter-only entries (added via `add`) are ignored for matching.
    pub(crate) fn find_match(
        &mut self,
        smt: &mut SmtContext,
        state: &ChcExpr,
    ) -> Option<(ReachFactId, FxHashMap<String, SmtValue>)> {
        if self.entries.is_empty() {
            return None;
        }

        if let Some(result) = self.find_match_via_point_facts(state) {
            return result;
        }

        // Build or reuse cached tagged disjunction of backed entries only.
        let disjunction = self.get_backed_tagged_disjunction();
        if matches!(disjunction, ChcExpr::Bool(false)) {
            return None;
        }

        // Query: state ∧ disjunction
        let query = ChcExpr::and(state.clone(), disjunction);

        smt.reset();
        match smt.check_sat(&query) {
            SmtResult::Sat(model) => {
                // Find which tag is true AND whose fact is actually satisfied.
                //
                // SOUNDNESS FIX: In the tagged disjunction `(fact_0 ∧ tag_0) ∨ (fact_1 ∧ tag_1)`,
                // the SAT solver can set "don't-care" tags to true for disjuncts whose facts
                // are NOT satisfied. For example, if fact_1 is the actual match, the solver
                // might still set tag_0 = true because tag_0 is unconstrained when fact_0 is
                // false. We must verify each entry's fact against the model to avoid returning
                // the wrong reach fact.
                for entry in &self.entries {
                    // Only return entries with a backing ReachFactId
                    if let Some(rf_id) = entry.id {
                        let tag_name = &entry.tag.name;
                        if matches!(model.get(tag_name), Some(SmtValue::Bool(true))) {
                            // Verify that this entry's fact is actually satisfied by the model.
                            // Don't-care tags can be true even when their fact is false.
                            if matches!(
                                crate::expr::evaluate_expr(&entry.fact, &model),
                                Some(SmtValue::Bool(true))
                            ) {
                                return Some((rf_id, model));
                            }
                        }
                    }
                }
                // SAT but no backed entry matched (unexpected model / missing tag values).
                None
            }
            _ => None,
        }
    }

    fn find_match_via_point_facts(
        &self,
        state: &ChcExpr,
    ) -> Option<Option<(ReachFactId, FxHashMap<String, SmtValue>)>> {
        let mut saw_backed = false;

        for entry in self.entries.iter().filter(|entry| entry.id.is_some()) {
            saw_backed = true;
            let Some(rf_id) = entry.id else {
                continue;
            };
            let mut model = FxHashMap::default();
            if !Self::collect_int_point_fact_model(&entry.fact, &mut model) {
                return None;
            }

            match crate::expr::evaluate_expr(state, &model) {
                Some(SmtValue::Bool(true)) => {
                    model.insert(entry.tag.name.clone(), SmtValue::Bool(true));
                    return Some(Some((rf_id, model)));
                }
                Some(SmtValue::Bool(false)) => {}
                _ => return None,
            }
        }

        saw_backed.then_some(None)
    }

    fn collect_int_point_fact_model(
        fact: &ChcExpr,
        model: &mut FxHashMap<String, SmtValue>,
    ) -> bool {
        match fact {
            ChcExpr::Bool(true) => true,
            ChcExpr::Op(ChcOp::And, args) => args
                .iter()
                .all(|arg| Self::collect_int_point_fact_model(arg, model)),
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                Self::collect_var_int_binding(args[0].as_ref(), args[1].as_ref(), model)
                    || Self::collect_var_int_binding(args[1].as_ref(), args[0].as_ref(), model)
            }
            _ => false,
        }
    }

    fn collect_var_int_binding(
        lhs: &ChcExpr,
        rhs: &ChcExpr,
        model: &mut FxHashMap<String, SmtValue>,
    ) -> bool {
        let (ChcExpr::Var(var), ChcExpr::Int(value)) = (lhs, rhs) else {
            return false;
        };
        if !matches!(&var.sort, ChcSort::Int) {
            return false;
        }

        match model.get(&var.name) {
            Some(SmtValue::Int(existing)) => *existing == *value,
            Some(_) => false,
            None => {
                model.insert(var.name.clone(), SmtValue::Int(*value));
                true
            }
        }
    }

    /// Get (or build) the reach-fact disjunction: `fact0 ∨ fact1 ∨ ...`
    ///
    /// Used by `is_reachable` for fast Boolean check. Tags are not included
    /// since we only care about satisfiability, not which fact matched.
    fn get_fact_disjunction(&mut self) -> ChcExpr {
        if let Some(ref disj) = self.cached_fact_disjunction {
            return disj.clone();
        }

        let facts: Vec<ChcExpr> = self
            .entries
            .iter()
            .map(|entry| entry.fact.clone())
            .collect();

        let disjunction = ChcExpr::or_vec(facts);

        self.cached_fact_disjunction = Some(disjunction.clone());
        disjunction
    }

    /// Get (or build) the untagged disjunction for backed entries only.
    ///
    /// Used by `is_reachable_backed` to check intersection with proven-reachable
    /// states only, excluding heuristic filter-only entries that may
    /// over-approximate reachable states and cause spurious invariant rejection.
    fn get_backed_disjunction(&mut self) -> ChcExpr {
        if let Some(ref disj) = self.cached_backed_disjunction {
            return disj.clone();
        }

        let facts: Vec<ChcExpr> = self
            .entries
            .iter()
            .filter(|entry| entry.id.is_some())
            .map(|entry| entry.fact.clone())
            .collect();

        let disjunction = ChcExpr::or_vec(facts);

        self.cached_backed_disjunction = Some(disjunction.clone());
        disjunction
    }

    /// Get (or build) the tagged disjunction for backed entries only:
    /// `(fact_i ∧ tag_i) ∨ ...` for entries where `id.is_some()`.
    ///
    /// This encoding ensures at least one `(fact_i ∧ tag_i)` disjunct is true.
    ///
    /// IMPORTANT: The SAT solver may set "don't-care" tags to true for disjuncts
    /// whose facts are not satisfied by the model. The caller (`find_match`) must
    /// verify each entry's fact against the model to identify the correct match.
    fn get_backed_tagged_disjunction(&mut self) -> ChcExpr {
        if let Some(ref disj) = self.cached_backed_tagged_disjunction {
            return disj.clone();
        }

        let tagged_facts: Vec<ChcExpr> = self
            .entries
            .iter()
            .filter(|entry| entry.id.is_some())
            .map(|entry| {
                let tag_expr = ChcExpr::var(entry.tag.clone());
                ChcExpr::and(entry.fact.clone(), tag_expr)
            })
            .collect();

        let disjunction = ChcExpr::or_vec(tagged_facts);

        self.cached_backed_tagged_disjunction = Some(disjunction.clone());
        disjunction
    }

    /// Check if any entries exist.
    fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

/// Per-predicate reach solver store.
///
/// Maps each predicate to its dedicated ReachSolver for fast must-reachability
/// intersection checks.
#[derive(Debug, Default)]
pub(crate) struct ReachSolverStore {
    solvers: FxHashMap<PredicateId, ReachSolver>,
}

impl ReachSolverStore {
    /// Create a new reach solver store.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    fn ensure_predicate_slot(&mut self, predicate: PredicateId) {
        if self.solvers.len() >= MAX_REACH_SOLVER_PREDICATES
            && !self.solvers.contains_key(&predicate)
        {
            self.solvers.clear();
        }
    }

    /// Add a reach fact for a predicate (filter-only, no backing ID).
    pub(crate) fn add(&mut self, predicate: PredicateId, fact: ChcExpr) {
        self.ensure_predicate_slot(predicate);
        self.solvers.entry(predicate).or_default().add(fact);
    }

    /// Add a reach fact backed by a ReachFactId (matchable).
    ///
    /// Entries added with this method can be returned from `find_match` for
    /// immediate witness construction without clause iteration.
    pub(crate) fn add_backed(&mut self, predicate: PredicateId, id: ReachFactId, fact: ChcExpr) {
        self.ensure_predicate_slot(predicate);
        self.solvers
            .entry(predicate)
            .or_default()
            .add_backed(id, fact);
    }

    /// Check if state intersects any cached reach fact for the predicate.
    pub(crate) fn is_reachable(
        &mut self,
        smt: &mut SmtContext,
        predicate: PredicateId,
        state: &ChcExpr,
    ) -> bool {
        self.solvers
            .get_mut(&predicate)
            .is_some_and(|solver| solver.is_reachable(smt, state))
    }

    /// Check if state intersects any **backed** reach fact for the predicate.
    ///
    /// Excludes filter-only (heuristic loop-closure) entries. Use this for
    /// entry-inductiveness checks where spurious reach-fact intersection from
    /// over-approximate heuristic entries would incorrectly reject valid invariants.
    pub(crate) fn is_reachable_backed(
        &mut self,
        smt: &mut SmtContext,
        predicate: PredicateId,
        state: &ChcExpr,
    ) -> bool {
        self.solvers
            .get_mut(&predicate)
            .is_some_and(|solver| solver.is_reachable_backed(smt, state))
    }

    /// Find a matching backed reach fact for the predicate.
    ///
    /// Returns `Some((ReachFactId, model))` if `state` intersects a backed reach fact
    /// for the given predicate, enabling immediate witness construction.
    pub(crate) fn find_match(
        &mut self,
        smt: &mut SmtContext,
        predicate: PredicateId,
        state: &ChcExpr,
    ) -> Option<(ReachFactId, FxHashMap<String, SmtValue>)> {
        self.solvers
            .get_mut(&predicate)
            .and_then(|solver| solver.find_match(smt, state))
    }

    /// Check if there are any cached reach facts for a predicate.
    ///
    /// Used to determine if the reach-fact fast path filter can be applied.
    /// When empty, we can't use reach facts to filter derivation attempts.
    pub(crate) fn has_facts(&self, predicate: PredicateId) -> bool {
        self.solvers
            .get(&predicate)
            .is_some_and(|solver| !solver.is_empty())
    }
}
