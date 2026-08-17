// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PropagateValues preprocessing pass
//!
//! Eliminates ground equalities of the form `(= EXPR CONST)` by building a
//! substitution table and rewriting all occurrences of `EXPR` to `CONST`.
//!
//! This is critical for QF_UFLIA benchmarks that define UF functions via
//! exhaustive lookup tables (e.g., `(= (Succ 0) 1)`, `(= (Sum 3 4) 7)`).
//! Without this pass, all ground UF equalities survive preprocessing and
//! become theory atoms, causing combinatorial explosion in DPLL(T).
//!
//! Two entry points with DIFFERENT contracts:
//! - [`PreprocessingPass::apply`] — the solve-pipeline pass: preserves defining
//!   equalities (EUF congruence closure needs them) and never drops formulas.
//! - [`PropagateValues::apply_goal`] — z3's `propagate-values` GOAL semantics
//!   for the tactic surface: also harvests asserted Boolean literals and
//!   `(= x c)` over variables, rewrites definers by each other (forward and
//!   backward sweeps), drops formulas that fold to `true`, and collapses a
//!   conflicting goal to `{false}`. Equivalence-preserving (see its docs).
//!
//! # Reference
//! - Z3: `reference/z3/src/ast/simplifiers/propagate_values.cpp`
//! - Design: the development design notes
//! - Issue: #5081

use super::PreprocessingPass;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};

mod fold_rebuild;
mod goal;

/// Red zone size for `stacker::maybe_grow` in propagate_values recursion (#8414).
const PROPVAL_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for propagate_values recursion.
const PROPVAL_STACK_SIZE: usize = 1024 * 1024;

/// Maximum forward+backward rounds in goal mode (`apply_goal`). Matches z3's
/// bounded fixpoint in `propagate_values.cpp`; each round either changes a
/// formula or the loop stops, and substitution targets are always constants
/// (strictly reducing), so termination never depends on this bound in practice.
const GOAL_MODE_MAX_ROUNDS: usize = 4;

/// Propagates ground equalities `(= EXPR CONST)` through assertions.
///
/// Phase 1: Scan assertions for `(= EXPR CONST)` where CONST is a concrete
/// constant and EXPR is any non-constant term (including function applications).
///
/// Phase 2: Rewrite NON-DEFINING assertions by substituting EXPR -> CONST.
/// The defining equalities themselves are preserved because EUF needs them
/// to compute congruence closure on non-ground applications like `Succ(x)`.
///
/// This is important for correctness: removing `(= (Succ 0) 1)` from the
/// formula makes `Succ` truly uninterpreted, which can change satisfiability.
pub(crate) struct PropagateValues {
    /// Substitution map: expression TermId -> constant TermId
    value_map: HashMap<TermId, TermId>,
    /// Set of defining equality assertions (TermIds) to skip during rewriting
    defining_equalities: HashSet<TermId>,
    /// Rewrite cache for the current iteration
    cache: HashMap<TermId, TermId>,
    /// Monotone [`PreprocessingPass::apply`] call counter, the provenance
    /// stamp: entries harvested in call `k` license rewrites of call `>= k`
    /// (#ppp-provenance). Never reset by [`PreprocessingPass::reset`].
    apply_calls: u32,
    /// Producer provenance: one record per in-place solve-pipeline rewrite
    /// (#ppp-provenance). Hints only — every consumer independently replays
    /// the rewrite and emits proof steps the untouched strict checker
    /// re-derives; a wrong or missing record can only DECLINE a derivation
    /// (fail-closed), never mint one.
    rewrite_records: Vec<PropagatedRewriteRecord>,
    /// Producer provenance: the asserted defining equality each `value_map`
    /// entry was harvested from, in exact first-wins harvest order.
    entry_sources: Vec<PropagatedEntrySource>,
    /// Set when either provenance vector hit [`MAX_PROPAGATION_RECORDS`]:
    /// the record set is incomplete, so the whole solve's records are
    /// withheld (fail-closed) rather than risk replaying against a
    /// truncated licensing environment.
    records_overflowed: bool,
}

/// One in-place solve-pipeline rewrite `before -> after` performed by
/// [`PreprocessingPass::apply`] at stamp `stamp` (#ppp-provenance).
#[derive(Debug, Clone)]
pub(crate) struct PropagatedRewriteRecord {
    pub(crate) before: TermId,
    pub(crate) after: TermId,
    pub(crate) stamp: u32,
}

/// Licensing origin of one `value_map` entry `expr ↦ value`, harvested from
/// the asserted defining equality `source_assertion` (spelled `(= expr value)`
/// or `(= value expr)`) at stamp `stamp` (#ppp-provenance).
#[derive(Debug, Clone)]
pub(crate) struct PropagatedEntrySource {
    pub(crate) expr: TermId,
    pub(crate) value: TermId,
    pub(crate) source_assertion: TermId,
    pub(crate) stamp: u32,
}

/// Drained provenance of one solve's `PropagateValues` fixpoint run.
#[derive(Debug, Clone, Default)]
pub(crate) struct PropagationRecords {
    pub(crate) rewrites: Vec<PropagatedRewriteRecord>,
    pub(crate) entries: Vec<PropagatedEntrySource>,
}

/// Hard cap on retained provenance records; overflow withholds ALL records
/// for the run (fail-closed decline downstream, never a partial replay).
const MAX_PROPAGATION_RECORDS: usize = 4096;

impl PropagateValues {
    pub(crate) fn new() -> Self {
        Self {
            value_map: HashMap::default(),
            defining_equalities: HashSet::default(),
            cache: HashMap::default(),
            apply_calls: 0,
            rewrite_records: Vec::new(),
            entry_sources: Vec::new(),
            records_overflowed: false,
        }
    }

    /// Drain the producer provenance accumulated by solve-pipeline `apply`
    /// calls. Returns `None` when recording overflowed (incomplete records
    /// must not license any replay) or when nothing was rewritten.
    pub(crate) fn take_propagation_records(&mut self) -> Option<PropagationRecords> {
        let rewrites = std::mem::take(&mut self.rewrite_records);
        let entries = std::mem::take(&mut self.entry_sources);
        if self.records_overflowed || rewrites.is_empty() {
            return None;
        }
        Some(PropagationRecords { rewrites, entries })
    }

    /// First-wins `expr ↦ source_assertion` index over the harvested entry
    /// provenance (#ppp-provenance, L3). Mirrors the first-wins insertion
    /// discipline of `value_map`, so for every key the index agrees with the
    /// entry that actually licenses rewrites — EXCEPT when recording
    /// overflowed or the map was seeded externally, in which case keys are
    /// missing and [`Self::collect_licensing_source_assertions`] fails closed.
    pub(crate) fn entry_source_index(&self) -> HashMap<TermId, TermId> {
        let mut index = HashMap::default();
        for entry in &self.entry_sources {
            index.entry(entry.expr).or_insert(entry.source_assertion);
        }
        index
    }

    /// Collect the defining ASSERTIONS whose harvested entries license the
    /// most recent solve-pipeline rewrite of `term` (#ppp-provenance, L3).
    ///
    /// Mirrors [`Self::rewrite`]'s traversal exactly — direct `value_map`
    /// hit, child rewrites via the still-warm `cache`, canonical
    /// `fold_rebuild`, then the post-fold map lookup — so the collected set
    /// is the set of entries that fired. MUST be called after an `apply` and
    /// before the next `reset` (the cache is the per-iteration replay
    /// medium). Returns `None` (fail-closed) when a used entry has no
    /// recorded source (harvest overflow, or an externally seeded map):
    /// callers must then DECLINE provenance augmentation entirely rather
    /// than claim an incomplete licensing set.
    ///
    /// Rebuilding through `fold_rebuild` re-interns only terms the pass
    /// already created during `apply`, so the walk allocates no new
    /// structure on the replayed path.
    pub(crate) fn collect_licensing_source_assertions(
        &self,
        terms: &mut TermStore,
        source_index: &HashMap<TermId, TermId>,
        term: TermId,
        visited: &mut HashSet<TermId>,
        out: &mut Vec<TermId>,
    ) -> Option<()> {
        stacker::maybe_grow(PROPVAL_STACK_RED_ZONE, PROPVAL_STACK_SIZE, || {
            if !visited.insert(term) {
                return Some(());
            }
            if self.value_map.contains_key(&term) {
                let source = source_index.get(&term).copied()?;
                if !out.contains(&source) {
                    out.push(source);
                }
                return Some(());
            }
            match terms.get(term).clone() {
                TermData::Const(_) | TermData::Var(_, _) => Some(()),
                TermData::App(sym, args) => {
                    for &arg in &args {
                        self.collect_licensing_source_assertions(
                            terms,
                            source_index,
                            arg,
                            visited,
                            out,
                        )?;
                    }
                    let new_args: Vec<TermId> = args
                        .iter()
                        .map(|&arg| self.cache.get(&arg).copied().unwrap_or(arg))
                        .collect();
                    if new_args != args {
                        let rebuilt = Self::fold_rebuild(terms, sym, term, new_args);
                        if self.value_map.contains_key(&rebuilt) {
                            let source = source_index.get(&rebuilt).copied()?;
                            if !out.contains(&source) {
                                out.push(source);
                            }
                        }
                    }
                    Some(())
                }
                TermData::Not(inner) => self.collect_licensing_source_assertions(
                    terms,
                    source_index,
                    inner,
                    visited,
                    out,
                ),
                TermData::Ite(cond, then_term, else_term) => {
                    self.collect_licensing_source_assertions(
                        terms,
                        source_index,
                        cond,
                        visited,
                        out,
                    )?;
                    self.collect_licensing_source_assertions(
                        terms,
                        source_index,
                        then_term,
                        visited,
                        out,
                    )?;
                    self.collect_licensing_source_assertions(
                        terms,
                        source_index,
                        else_term,
                        visited,
                        out,
                    )
                }
                // The pass passes binders through unchanged.
                TermData::Let(_, _) | TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {
                    Some(())
                }
                // Future TermData variants: fail closed.
                _ => None,
            }
        }) // stacker::maybe_grow
    }

    /// Seed the substitution map from an EXTERNALLY-supplied `key ↦ value` table
    /// (F6 ground-bridge fold), then rewrite terms with [`Self::rewrite_seeded`].
    ///
    /// The caller owns the map's soundness contract: every `key ↦ value` must be
    /// an asserted / entailed equality of the CURRENT problem (so substituting is
    /// an exact equivalence), and no key may be a variable that occurs under a
    /// surviving binder (`rewrite` passes `Forall`/`Exists`/`Let` through
    /// unchanged, so substitution is confined to ground positions — no capture).
    /// Values are typically constants, which are strictly reducing. This shares
    /// the folding dispatch (arith / BV / bv2nat / int2bv / Boolean / array), so a
    /// pin that turns a bridge argument constant collapses the whole term. Seed
    /// ONCE, then rewrite each assertion — the rewrite cache is keyed by term for
    /// the fixed map, so it is valid across every assertion of the same seed.
    pub(crate) fn seed_substitution(&mut self, subst: &HashMap<TermId, TermId>) {
        self.value_map = subst.clone();
        self.cache.clear();
    }

    /// Rewrite `term` under the map installed by [`Self::seed_substitution`].
    pub(crate) fn rewrite_seeded(&mut self, terms: &mut TermStore, term: TermId) -> TermId {
        self.rewrite(terms, term)
    }

    /// Check if a term is a concrete constant.
    fn is_constant(terms: &TermStore, term: TermId) -> bool {
        matches!(terms.get(term), TermData::Const(_))
    }

    /// Check if a term is ground (contains no free variables).
    ///
    /// Ground terms consist only of constants and function applications over
    /// other ground terms. Variables make a term non-ground.
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
    ///
    /// Visited-set deduplication: the term store is a hash-consed DAG; without
    /// it this walk enumerates every tree PATH — exponential in sharing depth
    /// (the DAG→tree pathology; a large BMC instance hung here). Skipping a
    /// revisited node as `true` is sound: `all`/`&&` short-circuit on the first
    /// `false` and every `false` terminates ALL ancestors immediately, so any
    /// node the walk continues past evaluated `true`, and that value is fixed
    /// for the (immutable, interned) term table.
    fn is_ground(terms: &TermStore, term: TermId) -> bool {
        let mut visited: HashSet<TermId> = HashSet::default();
        Self::is_ground_inner(terms, term, &mut visited)
    }

    fn is_ground_inner(terms: &TermStore, term: TermId, visited: &mut HashSet<TermId>) -> bool {
        stacker::maybe_grow(PROPVAL_STACK_RED_ZONE, PROPVAL_STACK_SIZE, || {
            if !visited.insert(term) {
                return true;
            }
            match terms.get(term) {
                TermData::Const(_) => true,
                TermData::Var(_, _) => false,
                TermData::App(_, args) => args
                    .iter()
                    .all(|&a| Self::is_ground_inner(terms, a, visited)),
                TermData::Not(inner) => Self::is_ground_inner(terms, *inner, visited),
                TermData::Ite(c, t, e) => {
                    Self::is_ground_inner(terms, *c, visited)
                        && Self::is_ground_inner(terms, *t, visited)
                        && Self::is_ground_inner(terms, *e, visited)
                }
                _ => false,
            }
        }) // stacker::maybe_grow
    }

    /// Extract a value equality from an assertion: `(= EXPR CONST)` or `(= CONST EXPR)`.
    ///
    /// Returns `Some((expr, const))` if the assertion is a top-level equality
    /// where exactly one side is a concrete constant and the other is a ground
    /// (variable-free) non-constant term.
    ///
    /// `pub(crate)`: the sealed-token consumer (#ppp-c7) independently
    /// replays each recorded harvest through this exact classifier.
    pub(crate) fn extract_value_equality(
        terms: &TermStore,
        assertion: TermId,
    ) -> Option<(TermId, TermId)> {
        match terms.get(assertion) {
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                let (lhs, rhs) = (args[0], args[1]);
                let lhs_const = Self::is_constant(terms, lhs);
                let rhs_const = Self::is_constant(terms, rhs);
                match (lhs_const, rhs_const) {
                    (false, true) if Self::is_ground(terms, lhs) => Some((lhs, rhs)),
                    (true, false) if Self::is_ground(terms, rhs) => Some((rhs, lhs)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Rewrite a term by substituting known value mappings.
    ///
    /// Bottom-up: first rewrite all children, then check if the result
    /// matches a known value in `value_map`. Uses canonical constructors
    /// (mk_eq, mk_add, etc.) when rebuilding to trigger constant folding.
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
    fn rewrite(&mut self, terms: &mut TermStore, term: TermId) -> TermId {
        stacker::maybe_grow(PROPVAL_STACK_RED_ZONE, PROPVAL_STACK_SIZE, || {
            if let Some(&cached) = self.cache.get(&term) {
                return cached;
            }

            // Check direct substitution first
            if let Some(&value) = self.value_map.get(&term) {
                self.cache.insert(term, value);
                return value;
            }

            let result = match terms.get(term).clone() {
                TermData::Const(_) | TermData::Var(_, _) => term,

                TermData::App(sym, args) => {
                    let new_args: Vec<TermId> =
                        args.iter().map(|&a| self.rewrite(terms, a)).collect();

                    if new_args == args {
                        term
                    } else {
                        let rebuilt = Self::fold_rebuild(terms, sym, term, new_args);
                        // Check if the rebuilt term is now in value_map
                        if let Some(&value) = self.value_map.get(&rebuilt) {
                            value
                        } else {
                            rebuilt
                        }
                    }
                }

                TermData::Not(inner) => {
                    let new_inner = self.rewrite(terms, inner);
                    if new_inner == inner {
                        term
                    } else {
                        terms.mk_not(new_inner)
                    }
                }

                TermData::Ite(c, t, e) => {
                    let nc = self.rewrite(terms, c);
                    let nt = self.rewrite(terms, t);
                    let ne = self.rewrite(terms, e);
                    if nc == c && nt == t && ne == e {
                        term
                    } else {
                        terms.mk_ite(nc, nt, ne)
                    }
                }

                // Let, Forall, Exists — pass through (not needed for ground value propagation)
                TermData::Let(_, _) | TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => term,
                // All current TermData variants are handled above.
                // This arm is required by #[non_exhaustive] and catches future variants.
                other => unreachable!("unhandled TermData variant in rewrite(): {other:?}"),
            };

            self.cache.insert(term, result);
            result
        }) // stacker::maybe_grow
    }
}

impl Default for PropagateValues {
    fn default() -> Self {
        Self::new()
    }
}

impl PreprocessingPass for PropagateValues {
    fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
        // #ppp-provenance stamp for this apply call: entries harvested now
        // license rewrites performed now and in later calls.
        self.apply_calls = self.apply_calls.saturating_add(1);
        let stamp = self.apply_calls;
        // Phase 1: Scan assertions for ground equalities (= EXPR CONST)
        let mut new_entries = false;
        for &assertion in assertions.iter() {
            if let Some((expr, value)) = Self::extract_value_equality(terms, assertion) {
                // Only insert if not already known (avoid overwriting)
                if !self.value_map.contains_key(&expr) {
                    self.value_map.insert(expr, value);
                    self.defining_equalities.insert(assertion);
                    if self.entry_sources.len() < MAX_PROPAGATION_RECORDS {
                        self.entry_sources.push(PropagatedEntrySource {
                            expr,
                            value,
                            source_assertion: assertion,
                            stamp,
                        });
                    } else {
                        self.records_overflowed = true;
                    }
                    new_entries = true;
                }
            }
        }

        if self.value_map.is_empty() {
            return false;
        }

        // Phase 2: Rewrite NON-DEFINING assertions by substituting EXPR -> CONST.
        // Defining equalities like (= (Succ 0) 1) are preserved unchanged because
        // EUF needs them to compute congruence closure on non-ground applications.
        // Without them, Succ becomes truly uninterpreted and the formula changes.
        let mut modified = new_entries;
        for assertion in assertions.iter_mut() {
            if self.defining_equalities.contains(assertion) {
                continue;
            }
            let new = self.rewrite(terms, *assertion);
            if new != *assertion {
                if self.rewrite_records.len() < MAX_PROPAGATION_RECORDS {
                    self.rewrite_records.push(PropagatedRewriteRecord {
                        before: *assertion,
                        after: new,
                        stamp,
                    });
                } else {
                    self.records_overflowed = true;
                }
                *assertion = new;
                modified = true;
            }
        }

        // Note: We do NOT remove tautological assertions. The defining equalities
        // must remain for EUF correctness, and any tautological rewrites in
        // non-defining assertions are harmless (Tseitin encodes them trivially).

        modified
    }

    fn reset(&mut self) {
        // Clear rewrite cache between fixed-point iterations so new
        // substitutions from other passes can be picked up.
        self.cache.clear();
        // Preserve value_map and defining_equalities across iterations —
        // accumulated ground equalities remain valid.
    }
}

#[cfg(test)]
mod tests;
