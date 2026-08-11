// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pattern compilation, trigger extraction, and term indexing for E-matching.
//!
//! Extracted from the ematching module — pure code motion, no algorithm changes.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData};
use ay_core::{TermId, TermStore};
use ay_euf::EufModel;

use super::pattern_helpers::{
    collect_patterns_from_term, synthesize_trigger_groups_with_fallback, user_pattern_to_ematch,
};
use super::EMATCH_STACK_RED_ZONE;
use super::EMATCH_STACK_SIZE;

/// Pattern for E-matching: a term structure with placeholders for bound variables.
#[derive(Clone, Debug)]
pub(super) struct EMatchPattern {
    /// The top-level symbol of the pattern
    pub(super) symbol: Symbol,
    /// Arguments: Left(var_index) for bound variables, Right(term_id) for ground subterms
    pub(super) args: Vec<EMatchArg>,
}

/// Pattern argument: bound variable, ground term, or nested pattern
#[derive(Clone, Debug)]
pub(super) enum EMatchArg {
    /// Bound variable at this index
    Var(usize),
    /// Ground subterm that must match exactly
    Ground(TermId),
    /// Nested pattern (e.g., f(x) in P(f(x)))
    Nested(Box<EMatchPattern>),
}

/// Index of ground terms by their top-level symbol.
#[derive(Clone)]
pub(super) struct TermIndex {
    pub(super) by_symbol: HashMap<String, Vec<TermId>>,
}

impl TermIndex {
    /// Build an index of ground App terms reachable from the current assertions.
    /// This indexes all reachable App terms (not just top-level) that are ground.
    ///
    /// Ground terms are those containing no bound variables. Declared constants
    /// (from `declare-const` or nullary `declare-fun`) ARE ground - only variables
    /// bound by enclosing quantifiers are non-ground.
    pub(super) fn new(terms: &TermStore, assertions: &[TermId]) -> Self {
        let mut reachable = Vec::new();
        let mut reachable_seen: HashSet<u32> = HashSet::default();
        for &assertion in assertions {
            Self::collect_reachable_term_ids(terms, assertion, &mut reachable, &mut reachable_seen);
        }
        reachable.sort_unstable_by_key(|term| term.0);

        // First pass: collect ALL Var term IDs that are bound by quantifiers.
        // A Var is bound if its NAME matches a quantifier's binding name.
        // Variables not in this set (declared constants) are free and thus ground.
        //
        // We need to track which binding names are currently in scope as we traverse.
        let mut bound_var_ids: HashSet<u32> = HashSet::default();
        let mut bound_names: HashSet<String> = HashSet::default();
        for &term_id in &reachable {
            Self::collect_bound_var_ids(terms, term_id, &mut bound_var_ids, &mut bound_names);
        }

        // Second pass: index all terms, using the collected bound var IDs.
        // The is_ground cache prevents redundant recursive traversals for shared subterms.
        let mut by_symbol: HashMap<String, Vec<TermId>> = HashMap::default();
        let mut seen: HashSet<u32> = HashSet::default();
        let mut ground_cache: HashMap<u32, bool> = HashMap::default();

        for &term_id in &reachable {
            Self::index_term(
                terms,
                term_id,
                &mut by_symbol,
                &mut seen,
                &bound_var_ids,
                &mut ground_cache,
            );
        }
        Self { by_symbol }
    }

    pub(super) fn collect_reachable_term_ids(
        terms: &TermStore,
        term_id: TermId,
        out: &mut Vec<TermId>,
        seen: &mut HashSet<u32>,
    ) {
        stacker::maybe_grow(EMATCH_STACK_RED_ZONE, EMATCH_STACK_SIZE, || {
            if !seen.insert(term_id.0) {
                return;
            }
            out.push(term_id);
            match terms.get(term_id) {
                TermData::App(_, args) => {
                    for &arg in args {
                        Self::collect_reachable_term_ids(terms, arg, out, seen);
                    }
                }
                TermData::Not(inner) => {
                    Self::collect_reachable_term_ids(terms, *inner, out, seen);
                }
                TermData::Ite(c, t, e) => {
                    Self::collect_reachable_term_ids(terms, *c, out, seen);
                    Self::collect_reachable_term_ids(terms, *t, out, seen);
                    Self::collect_reachable_term_ids(terms, *e, out, seen);
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        Self::collect_reachable_term_ids(terms, *v, out, seen);
                    }
                    Self::collect_reachable_term_ids(terms, *body, out, seen);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    Self::collect_reachable_term_ids(terms, *body, out, seen);
                }
                TermData::Const(_) | TermData::Var(_, _) => {}
                _ => {}
            }
        })
    }

    /// Collect all Var term IDs that are bound by quantifiers.
    /// `bound_names` contains the names of variables bound by enclosing quantifiers.
    /// A Var is bound only if its name matches one of these binding names.
    /// Uses push/pop on `bound_names` to avoid cloning at each quantifier level.
    pub(super) fn collect_bound_var_ids(
        terms: &TermStore,
        term_id: TermId,
        bound_var_ids: &mut HashSet<u32>,
        bound_names: &mut HashSet<String>,
    ) {
        stacker::maybe_grow(EMATCH_STACK_RED_ZONE, EMATCH_STACK_SIZE, || {
            match terms.get(term_id) {
                TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
                    // Push quantifier binding names, track which were new for pop
                    let mut added: Vec<String> = Vec::new();
                    for (name, _) in vars {
                        if bound_names.insert(name.clone()) {
                            added.push(name.clone());
                        }
                    }
                    Self::collect_bound_var_ids(terms, *body, bound_var_ids, bound_names);
                    // Pop: remove only names we added
                    for name in &added {
                        bound_names.remove(name);
                    }
                }
                TermData::Var(name, _) => {
                    // A Var is bound if its name (or the base name without suffix) is in scope.
                    // The frontend may rename "x" to "x_0" for uniqueness.
                    let base_name = name.trim_end_matches(|c: char| c == '_' || c.is_ascii_digit());
                    if bound_names.contains(name) || bound_names.contains(base_name) {
                        bound_var_ids.insert(term_id.0);
                    }
                }
                TermData::App(_, args) => {
                    for &arg in args {
                        Self::collect_bound_var_ids(terms, arg, bound_var_ids, bound_names);
                    }
                }
                TermData::Not(inner) => {
                    Self::collect_bound_var_ids(terms, *inner, bound_var_ids, bound_names);
                }
                TermData::Ite(c, t, e) => {
                    Self::collect_bound_var_ids(terms, *c, bound_var_ids, bound_names);
                    Self::collect_bound_var_ids(terms, *t, bound_var_ids, bound_names);
                    Self::collect_bound_var_ids(terms, *e, bound_var_ids, bound_names);
                }
                TermData::Let(bindings, body) => {
                    for (_, val) in bindings {
                        Self::collect_bound_var_ids(terms, *val, bound_var_ids, bound_names);
                    }
                    Self::collect_bound_var_ids(terms, *body, bound_var_ids, bound_names);
                }
                TermData::Const(_) => {}
                // Future TermData variants: skip (no bound vars to collect).
                _ => {}
            }
        })
    }

    /// Recursively index a term and all its subterms.
    ///
    /// `bound_var_ids` contains term IDs of all Var terms that appear inside
    /// quantifier bodies. These are the bound variables. Var terms not in this
    /// set (declared constants) are free and thus ground.
    pub(super) fn index_term(
        terms: &TermStore,
        term_id: TermId,
        by_symbol: &mut HashMap<String, Vec<TermId>>,
        seen: &mut HashSet<u32>,
        bound_var_ids: &HashSet<u32>,
        ground_cache: &mut HashMap<u32, bool>,
    ) {
        stacker::maybe_grow(EMATCH_STACK_RED_ZONE, EMATCH_STACK_SIZE, || {
            if seen.contains(&term_id.0) {
                return;
            }
            seen.insert(term_id.0);

            match terms.get(term_id) {
                TermData::App(sym, args) => {
                    // Index this App if it's ground (contains no bound variables)
                    let is_ground = args.iter().all(|&arg| {
                        Self::is_ground_cached(terms, arg, bound_var_ids, ground_cache)
                    });
                    if is_ground {
                        // Insert via binary-search sorted insert (LI-2) so each
                        // per-symbol Vec stays globally ascending by TermId. The
                        // full rebuild walks `reachable` in ascending id order, so
                        // for it a sorted insert is equivalent to a bare push; the
                        // incremental refresh, however, can introduce a later-round
                        // ground App with a LOWER id (constant folding, e.g.
                        // mk_add -> mk_int), and sorted insert keeps the Vec
                        // elementwise-identical to a full rebuild over the
                        // cumulative assertion set.
                        let bucket = by_symbol.entry(sym.name().to_string()).or_default();
                        if let Err(pos) = bucket.binary_search_by_key(&term_id.0, |t| t.0) {
                            bucket.insert(pos, term_id);
                        }
                    }
                    // Recurse into arguments
                    for &arg in args {
                        Self::index_term(terms, arg, by_symbol, seen, bound_var_ids, ground_cache);
                    }
                }
                TermData::Not(inner) => {
                    Self::index_term(terms, *inner, by_symbol, seen, bound_var_ids, ground_cache);
                }
                TermData::Ite(c, t, e) => {
                    Self::index_term(terms, *c, by_symbol, seen, bound_var_ids, ground_cache);
                    Self::index_term(terms, *t, by_symbol, seen, bound_var_ids, ground_cache);
                    Self::index_term(terms, *e, by_symbol, seen, bound_var_ids, ground_cache);
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        Self::index_term(terms, *v, by_symbol, seen, bound_var_ids, ground_cache);
                    }
                    Self::index_term(terms, *body, by_symbol, seen, bound_var_ids, ground_cache);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    // Bound vars already collected in first pass, just recurse
                    Self::index_term(terms, *body, by_symbol, seen, bound_var_ids, ground_cache);
                }
                TermData::Const(_) | TermData::Var(_, _) => {}
                // Future TermData variants: skip (nothing to index).
                _ => {}
            }
        })
    }

    /// Check if a term is ground (contains no bound variables), with memoization.
    ///
    /// A `Var` is ground if and only if its term ID is NOT in the `bound_var_ids` set.
    /// This means declared constants (free variables) are ground, while
    /// Var terms that appear inside quantifier bodies are not.
    ///
    /// The `cache` prevents redundant recursive traversals for shared subterms
    /// in the hash-consed term DAG.
    fn is_ground_cached(
        terms: &TermStore,
        term_id: TermId,
        bound_var_ids: &HashSet<u32>,
        cache: &mut HashMap<u32, bool>,
    ) -> bool {
        if let Some(&cached) = cache.get(&term_id.0) {
            return cached;
        }
        let result = stacker::maybe_grow(EMATCH_STACK_RED_ZONE, EMATCH_STACK_SIZE, || {
            match terms.get(term_id) {
                // A Var is ground only if it's NOT bound (not inside any quantifier body)
                TermData::Var(_, _) => !bound_var_ids.contains(&term_id.0),
                TermData::Const(_) => true,
                TermData::App(_, args) => args
                    .iter()
                    .all(|&arg| Self::is_ground_cached(terms, arg, bound_var_ids, cache)),
                TermData::Not(inner) => Self::is_ground_cached(terms, *inner, bound_var_ids, cache),
                TermData::Ite(c, t, e) => {
                    Self::is_ground_cached(terms, *c, bound_var_ids, cache)
                        && Self::is_ground_cached(terms, *t, bound_var_ids, cache)
                        && Self::is_ground_cached(terms, *e, bound_var_ids, cache)
                }
                TermData::Let(bindings, body) => {
                    bindings
                        .iter()
                        .all(|(_, v)| Self::is_ground_cached(terms, *v, bound_var_ids, cache))
                        && Self::is_ground_cached(terms, *body, bound_var_ids, cache)
                }
                // Quantified formulas are never ground terms
                TermData::Forall(..) | TermData::Exists(..) => false,
                // Future TermData variants: conservatively not ground.
                _ => false,
            }
        });
        cache.insert(term_id.0, result);
        result
    }

    pub(super) fn get_by_symbol(&self, symbol: &str) -> &[TermId] {
        self.by_symbol.get(symbol).map_or(&[], |v| v.as_slice())
    }
}

/// Lightweight equivalence classes extracted from explicit equalities in assertions.
///
/// Built from `(= a b)` atoms in the assertion set. Uses path-compressed union-find.
/// This enables E-matching to match modulo known equalities without requiring the
/// full EUF congruence closure (which is not available during quantifier preprocessing).
///
/// Fix for #3325 Gap 1: E-graph-aware matching via equality extraction.
#[derive(Clone, Debug)]
pub(crate) struct EqualityClasses {
    /// Union-find parent map. `parent[id] = parent_id`. Root if `parent[id] = id`.
    parent: HashMap<u32, u32>,
    /// Reverse index: root -> all members in the class.
    /// Built after all unions are complete.
    members: HashMap<u32, Vec<u32>>,
}

impl EqualityClasses {
    /// Build equivalence classes from explicit equalities in assertions.
    ///
    /// Walks the assertion list for top-level `(= a b)` atoms (App with symbol "=")
    /// and merges `a` and `b` into the same equivalence class.
    #[cfg(any(test, feature = "ematching-differential"))]
    pub(crate) fn from_assertions(terms: &TermStore, assertions: &[TermId]) -> Self {
        let mut classes = Self {
            parent: HashMap::default(),
            members: HashMap::default(),
        };
        for &assertion in assertions {
            classes.extract_equalities_from_term(terms, assertion);
        }
        // Build reverse index for class_members()
        classes.build_members_index();
        classes
    }

    /// Create an empty set of equivalence classes (no equalities folded yet).
    /// Used by the persistent incremental E-matching state.
    pub(super) fn new_empty() -> Self {
        Self {
            parent: HashMap::default(),
            members: HashMap::default(),
        }
    }

    /// Fold the `(= a b)` / `(and ...)` equalities of a single assertion ROOT
    /// into the (persisted) union-find, WITHOUT rebuilding the members index.
    ///
    /// The caller is responsible for calling `build_members_index()` exactly once
    /// after folding all new roots in a round. This mirrors `from_assertions`'s
    /// fold loop but applies to one root at a time so the persistent state can
    /// fold only NEW atoms (keyed by TermId, LI-7) across rounds.
    pub(super) fn fold_assertion_root(&mut self, terms: &TermStore, root: TermId) {
        self.extract_equalities_from_term(terms, root);
    }

    /// Rebuild the members reverse index (public wrapper for the persistent path).
    pub(super) fn rebuild_members(&mut self) {
        self.build_members_index();
    }

    /// Number of entries in the persisted union-find parent map.
    /// Used by the EUF-non-accumulation debug guard (LI-6): the persisted parent
    /// must be unchanged by a per-round `augment_with_euf_model` on a clone.
    #[cfg(debug_assertions)]
    pub(super) fn parent_len(&self) -> usize {
        self.parent.len()
    }

    /// Canonicalize the partition for the differential canary: for every TermId
    /// `t` present in `parent`, return the (sorted) member-set of its class. This
    /// is root-label-invariant, so it compares incremental-vs-full by partition,
    /// not by which element happens to be the union-find root.
    #[cfg(feature = "ematching-differential")]
    pub(super) fn canonical_partition(&self) -> Vec<Vec<u32>> {
        let mut classes: HashMap<u32, Vec<u32>> = HashMap::default();
        for &id in self.parent.keys() {
            let root = self.find(id);
            classes.entry(root).or_default().push(id);
        }
        let mut out: Vec<Vec<u32>> = classes
            .into_values()
            .map(|mut v| {
                v.sort_unstable();
                v
            })
            .collect();
        out.sort_unstable();
        out
    }

    /// Build the members reverse index from the parent map.
    ///
    /// Each member Vec is sorted (LI-8) so member order is a pure function of
    /// the partition (the TermId set), independent of `parent.keys()` iteration
    /// order. The underlying DetHashMap (hashbrown + FixedState) is deterministic
    /// across process runs but its key order depends on insertion/resize history,
    /// which differs between an N-round incremental accumulation and a single-pass
    /// full rebuild. Sorting makes the incremental and full builds byte-identical,
    /// which the cfg(debug_assertions) differential canary relies on, and makes
    /// first-success member matching (matching.rs) deterministic.
    fn build_members_index(&mut self) {
        self.members.clear();
        for &id in self.parent.keys() {
            let root = self.find(id);
            self.members.entry(root).or_default().push(id);
        }
        for v in self.members.values_mut() {
            v.sort_unstable();
        }
    }

    /// Check if two terms are in the same equivalence class.
    pub(super) fn in_same_class(&self, a: TermId, b: TermId) -> bool {
        if a == b {
            return true;
        }
        let root_a = self.find(a.0);
        let root_b = self.find(b.0);
        root_a == root_b && self.parent.contains_key(&a.0)
    }

    /// Find root without path compression (allows &self).
    /// The union-find is small (only explicit equalities) so O(depth) is fine.
    fn find(&self, x: u32) -> u32 {
        let mut current = x;
        loop {
            match self.parent.get(&current) {
                None => return current,
                Some(&p) if p == current => return current,
                Some(&p) => current = p,
            }
        }
    }

    /// Union two term IDs into the same equivalence class.
    fn union(&mut self, a: u32, b: u32) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra != rb {
            // Ensure both are in the map
            self.parent.entry(ra).or_insert(ra);
            self.parent.entry(rb).or_insert(rb);
            // Simple union: make rb point to ra
            self.parent.insert(rb, ra);
        } else {
            // Ensure both are in the map even if roots match
            self.parent.entry(ra).or_insert(ra);
        }
    }

    /// Extract equalities from a term recursively.
    /// Finds `(= a b)` atoms at top level and under conjunctions.
    fn extract_equalities_from_term(&mut self, terms: &TermStore, term: TermId) {
        match terms.get(term) {
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                self.union(args[0].0, args[1].0);
            }
            TermData::App(sym, args) if sym.name() == "and" => {
                for &arg in args {
                    self.extract_equalities_from_term(terms, arg);
                }
            }
            _ => {}
        }
    }

    /// Get all terms in the same equivalence class as `term`.
    /// Returns an empty slice if the term has no known equalities.
    pub(super) fn class_members(&self, term: TermId) -> &[u32] {
        let root = self.find(term.0);
        self.members.get(&root).map_or(&[], |v| v.as_slice())
    }

    /// Check if this set has any equalities at all (optimization: skip if empty).
    pub(super) fn is_empty(&self) -> bool {
        self.parent.is_empty()
    }

    /// Order-independent fingerprint of the current PARTITION, used by incremental
    /// matching to detect whether the equality classes changed between rounds.
    ///
    /// The fingerprint is the multiset of `(root, member)` canonical pairs, hashed
    /// with a commutative (XOR-of-per-pair-hash) combiner so it is independent of
    /// `parent.keys()` iteration order (the underlying DetHashMap order depends on
    /// insertion/resize history). Two `EqualityClasses` instances with the SAME
    /// partition produce the SAME fingerprint; a single union changes it. This is a
    /// pure optimization signal — it only ever gates a SKIP of redundant re-matching
    /// of OLD candidates and is double-checked by the differential canary; even a
    /// (vanishingly unlikely) hash collision merely causes a missed re-match, which
    /// is incompleteness (→ Unknown), never a false UNSAT (matching is monotone:
    /// fewer instances only weaken the conjunction). See incremental-match design.
    pub(super) fn partition_fingerprint(&self) -> u64 {
        // XOR-combine a per-element hash of (canonical_root, element). Using the
        // canonical root makes the fingerprint sensitive to any merge: when two
        // classes union, every element of the smaller class gets a new root, so its
        // contribution changes. XOR is commutative/associative so key-iteration
        // order does not matter.
        use std::hash::{Hash, Hasher};
        let mut acc: u64 = 0;
        for &id in self.parent.keys() {
            let root = self.find(id);
            let mut h = std::collections::hash_map::DefaultHasher::new();
            root.hash(&mut h);
            id.hash(&mut h);
            acc ^= h.finish();
        }
        // Fold the cardinality in so an empty vs non-empty partition with a
        // (degenerate) zero XOR still differ.
        acc ^ (self.parent.len() as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)
    }

    /// Augment equivalence classes with congruence information from an EUF model.
    ///
    /// The EUF model's `term_values` maps each term to a string element name.
    /// Terms mapping to the same element name are in the same congruence class.
    /// This brings congruence closure information into E-matching without
    /// persisting the EUF solver (Phase B1b of #3325).
    pub(super) fn augment_with_euf_model(&mut self, euf_model: &EufModel) {
        let mut by_value: HashMap<&str, Vec<u32>> = HashMap::default();
        for (term_id, value) in &euf_model.term_values {
            by_value.entry(value.as_str()).or_default().push(term_id.0);
        }
        for (_, term_ids) in &by_value {
            if term_ids.len() < 2 {
                continue;
            }
            let first = term_ids[0];
            for &other in &term_ids[1..] {
                self.union(first, other);
            }
        }
        self.build_members_index();
    }
}

/// A trigger group: one or more patterns that must ALL match with consistent bindings.
/// Single triggers have one pattern; multi-triggers have 2+ patterns.
pub(super) struct TriggerGroup {
    pub(super) patterns: Vec<EMatchPattern>,
    pub(super) var_names: Vec<String>,
}

pub(super) struct ExtractedTriggerGroups {
    pub(super) primary: Vec<TriggerGroup>,
    pub(super) fallback: Vec<TriggerGroup>,
}

#[cfg(test)]
pub(super) fn extract_patterns(terms: &TermStore, quantifier: TermId) -> Vec<TriggerGroup> {
    extract_patterns_with_fallback(terms, quantifier).primary
}

pub(super) fn extract_patterns_with_fallback(
    terms: &TermStore,
    quantifier: TermId,
) -> ExtractedTriggerGroups {
    let (vars, body, user_triggers) = match terms.get(quantifier) {
        TermData::Forall(v, b, t) => (v.clone(), *b, t),
        TermData::Exists(v, b, t) => (v.clone(), *b, t),
        _ => {
            return ExtractedTriggerGroups {
                primary: vec![],
                fallback: vec![],
            };
        }
    };

    // Build mapping from bound variable names to their indices.
    // The quantifier's vars vector contains (name, sort) pairs where the name
    // is the exact name used in the body for bound variables.
    //
    // IMPORTANT: We use the quantifier's declared names directly, not arbitrary
    // Var terms found in the body. This correctly distinguishes bound variables
    // from free variables (constants) that happen to have the same sort.
    //
    // Fix for #1891: Previously, the code matched Var terms to bindings by sort
    // only, which caused free variables (like declared constants) to be confused
    // with bound variables when they had the same sort.
    let mut actual_var_names: HashMap<String, usize> = HashMap::default();
    let mut actual_names_by_idx: Vec<String> = vec![String::new(); vars.len()];

    for (idx, (name, _sort)) in vars.iter().enumerate() {
        actual_var_names.insert(name.clone(), idx);
        actual_names_by_idx[idx] = name.clone();
    }

    // Use explicit user triggers if provided.
    // Each multi_trigger is a group of terms that must ALL match (AND semantics).
    // Multiple trigger groups are alternatives (OR semantics).
    if !user_triggers.is_empty() {
        let groups: Vec<TriggerGroup> = user_triggers
            .iter()
            .filter_map(|multi| {
                user_pattern_to_ematch(terms, multi, &actual_var_names, &actual_names_by_idx)
            })
            .collect();

        // If all user triggers were filtered out (e.g., non-App triggers, no bound vars,
        // or builtin symbols), fall back to auto-extraction from the quantifier body.
        if !groups.is_empty() {
            let fallback = auto_trigger_groups(
                terms,
                quantifier,
                body,
                vars.len(),
                &actual_var_names,
                &actual_names_by_idx,
            );
            return ExtractedTriggerGroups {
                primary: groups,
                fallback: fallback
                    .primary
                    .into_iter()
                    .chain(fallback.fallback)
                    .collect(),
            };
        }
    }

    auto_trigger_groups(
        terms,
        quantifier,
        body,
        vars.len(),
        &actual_var_names,
        &actual_names_by_idx,
    )
}

fn auto_trigger_groups(
    terms: &TermStore,
    quantifier: TermId,
    body: TermId,
    num_vars: usize,
    actual_var_names: &HashMap<String, usize>,
    actual_names_by_idx: &[String],
) -> ExtractedTriggerGroups {
    let mut patterns = Vec::new();
    collect_patterns_from_term(
        terms,
        body,
        actual_var_names,
        actual_names_by_idx,
        terms.quantifier_no_patterns(quantifier),
        &mut patterns,
    );

    let synthesized =
        synthesize_trigger_groups_with_fallback(patterns, num_vars, actual_names_by_idx);
    ExtractedTriggerGroups {
        primary: synthesized.primary,
        fallback: synthesized.fallback,
    }
}

// Pattern synthesis helpers are in pattern_helpers.rs.
