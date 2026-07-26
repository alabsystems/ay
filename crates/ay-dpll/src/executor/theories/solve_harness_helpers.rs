// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Free helper functions for assertion flattening, store-flat substitution,
//! and proof source tracking used by `solve_harness.rs`.
//!
//! Split from `solve_harness.rs` for code health (#7006, #5970).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};

use crate::preprocess::VariableSubstitution;

pub(super) fn flatten_assertions_with_sources(
    terms: &TermStore,
    assertions: &[TermId],
) -> Vec<(TermId, Vec<TermId>)> {
    let mut flattened = Vec::new();
    for &assertion in assertions {
        flatten_assertion_with_source(terms, assertion, &[assertion], &mut flattened);
    }
    flattened
}

pub(super) fn flatten_assertions_with_optional_sources(
    terms: &TermStore,
    assertions: &[TermId],
    source_sets: &[Option<Vec<Vec<TermId>>>],
) -> Vec<(TermId, Option<Vec<Vec<TermId>>>)> {
    let mut flattened = Vec::new();
    for (&assertion, maybe_sources) in assertions.iter().zip(source_sets.iter()) {
        flatten_assertion_with_optional_sources(
            terms,
            assertion,
            maybe_sources.clone(),
            &mut flattened,
        );
    }
    flattened
}

pub(super) fn flatten_assertion_with_source(
    terms: &TermStore,
    assertion: TermId,
    source_set: &[TermId],
    flattened: &mut Vec<(TermId, Vec<TermId>)>,
) {
    if let TermData::App(Symbol::Named(name), args) = terms.get(assertion) {
        if name == "and" {
            for &arg in args {
                flatten_assertion_with_source(terms, arg, source_set, flattened);
            }
            return;
        }
    }
    flattened.push((assertion, source_set.to_vec()));
}

fn flatten_assertion_with_optional_sources(
    terms: &TermStore,
    assertion: TermId,
    source_sets: Option<Vec<Vec<TermId>>>,
    flattened: &mut Vec<(TermId, Option<Vec<Vec<TermId>>>)>,
) {
    if let TermData::App(Symbol::Named(name), args) = terms.get(assertion) {
        if name == "and" {
            for &arg in args {
                flatten_assertion_with_optional_sources(terms, arg, source_sets.clone(), flattened);
            }
            return;
        }
    }
    flattened.push((assertion, source_sets));
}

/// Substitute store-flat array equalities in AUFLIA preprocessing (#6820).
///
/// Store-flat benchmarks encode array chains as:
///   `(= a_N (store a_{N-1} idx val))`
/// where each `a_N` is a named Array-sorted variable. This function finds such
/// equalities and substitutes each `a_N` with its store expression throughout
/// all assertions. This converts `(select a_N k)` into
/// `(select (store a_{N-1} idx val) k)`, which directly triggers ROW axioms
/// without needing equality-chain reasoning.
///
/// Unlike `VariableSubstitution` (which excludes Array sorts to avoid regressions
/// in other paths), this is only called in the AUFLIA/ArrayEUF preprocessing pipeline.
pub(super) fn substitute_store_flat_equalities(
    terms: &mut TermStore,
    assertions: &mut Vec<TermId>,
) {
    // Phase 1: Collect var -> store_expr substitutions from equalities.
    // First pass: count how many store equalities target each variable.
    // Variables with multiple store equalities (e.g., b = store(a,x,v) AND
    // b = store(a,y,w)) must NOT be substituted — replacing b destroys the
    // "two stores to same target" pattern that check_disjunctive_store_target_equalities
    // needs to detect UNSAT (#6885).
    let mut store_eq_count: HashMap<TermId, usize> = HashMap::default();
    for &assertion in assertions.iter() {
        if let TermData::App(ref sym, ref args) = terms.get(assertion).clone() {
            if sym.name() == "=" && args.len() == 2 {
                let (lhs, rhs) = (args[0], args[1]);
                if matches!(terms.get(lhs), TermData::Var(_, _))
                    && matches!(terms.sort(lhs), Sort::Array(_))
                    && is_store_term(terms, rhs)
                {
                    *store_eq_count.entry(lhs).or_insert(0) += 1;
                } else if matches!(terms.get(rhs), TermData::Var(_, _))
                    && matches!(terms.sort(rhs), Sort::Array(_))
                    && is_store_term(terms, lhs)
                {
                    *store_eq_count.entry(rhs).or_insert(0) += 1;
                }
            }
        }
    }

    let mut subst_map: HashMap<TermId, TermId> = HashMap::default();

    for &assertion in assertions.iter() {
        let candidate = match terms.get(assertion).clone() {
            TermData::App(ref sym, ref args) if sym.name() == "=" && args.len() == 2 => {
                let (lhs, rhs) = (args[0], args[1]);
                if matches!(terms.get(lhs), TermData::Var(_, _))
                    && matches!(terms.sort(lhs), Sort::Array(_))
                    && is_store_term(terms, rhs)
                {
                    Some((lhs, rhs))
                } else if matches!(terms.get(rhs), TermData::Var(_, _))
                    && matches!(terms.sort(rhs), Sort::Array(_))
                    && is_store_term(terms, lhs)
                {
                    Some((rhs, lhs))
                } else {
                    None
                }
            }
            _ => None,
        };

        if let Some((var, store_expr)) = candidate {
            // Skip variables that are the target of multiple store equalities.
            if store_eq_count.get(&var).copied().unwrap_or(0) > 1 {
                continue;
            }
            // Only take the first substitution for each variable. A
            // transitive occurs check below removes mutual and longer cycles
            // after the complete candidate graph is available.
            if !subst_map.contains_key(&var) {
                subst_map.insert(var, store_expr);
            }
        }
    }

    // A direct occurs check is insufficient for mutually recursive store-flat
    // definitions such as `a = store(b, ...)`, `b = store(a, ...)`. Following
    // that map in `apply_store_flat_subst` recurses forever because a cache
    // entry cannot be installed until the replacement has been expanded.
    //
    // Find every key whose transitive expansion reaches itself, then remove
    // exactly those cyclic keys. Independent acyclic definitions remain
    // available, while references to a removed key stay as ordinary variables.
    let cyclic_vars = cyclic_store_flat_substitution_vars(terms, &subst_map);
    for var in cyclic_vars {
        subst_map.remove(&var);
    }

    if subst_map.is_empty() {
        return;
    }

    // Phase 2: Apply substitutions to all assertions.
    // After substitution, defining equalities like (= a_N (store ...)) become
    // tautological (mk_eq simplifies (= X X) to true). Remove them to avoid
    // the axiom fixpoint generating spurious ROW axioms from dead terms.
    let true_term = terms.true_term();
    let mut cache: HashMap<TermId, TermId> = HashMap::default();
    let mut new_assertions = Vec::with_capacity(assertions.len());
    for &assertion in assertions.iter() {
        let substituted = apply_store_flat_subst(terms, assertion, &subst_map, &mut cache);
        if substituted != true_term {
            new_assertions.push(substituted);
        }
    }
    *assertions = new_assertions;
}

/// Substitute pure top-level array-variable aliases `(= a b)` (#auflia-alias).
///
/// `VariableSubstitution` deliberately EXCLUDES Array sorts (`new_skip_arrays`)
/// to avoid regressions, so a top-level array alias `(= a1 a0)` between two
/// Array-sorted *variables* is never collapsed. Leaving it un-substituted is a
/// soundness hazard for the combined array+LIA path: the eager array-axiom scan
/// ranges over the WHOLE term store (QF reachability scoping is off for
/// quantifier-free) and treats `select`/`store` terms built on BOTH aliased
/// variables across several distinct array (dis)equalities as simultaneously
/// active, learning a cross-assertion array relation that holds under NO actual
/// model — a spurious conflict / wrong-UNSAT (the arr_lia561 / store-distinct +
/// alias family, e.g. `(= a1 a0) ∧ (distinct a0 (store a1 2 x)) ∧ (distinct …)`).
/// Collapsing the alias to a single canonical representative removes the second
/// name, so all `select`/`store` terms refer to one array and the spurious
/// cross-name relation cannot form (verified: substituting the alias at the SMT
/// level makes AY return the correct `sat`).
///
/// SOUNDNESS / equisatisfiability: a top-level conjunct `(= a b)` forces `a` and
/// `b` to denote the SAME array in every model, so replacing every occurrence of
/// the non-canonical variable with the canonical one preserves the truth value
/// of every assertion and the full set of models (modulo renaming the eliminated
/// variable, which is recovered as a copy of the representative at model time).
/// It can never flip sat↔unsat.
///
/// SCOPE (kept narrow to avoid the regressions that motivated `new_skip_arrays`):
///  * Only TOP-LEVEL conjuncts that are *directly* `(= aVar bVar)` with BOTH
///    sides Array-sorted `Var` terms — never aliases buried inside a disjunction
///    or other connective (those do not hold unconditionally).
///  * Chains (`a=b`, `b=c`) collapse to one representative via union-find.
///
/// Returns the `(eliminated_var, representative_var)` substitution pairs so the
/// caller can record them for model recovery (`record_var_substitutions` /
/// `recorded_var_substitutions`): the deferred-postprocessing model validator
/// restores the ORIGINAL assertions, so the eliminated variable must be filled
/// in (as a copy of its representative) for the validated model to evaluate the
/// restored alias equality. With no recovery the model would lack the variable
/// and SAT would degrade to Unknown — still sound, but recovery keeps SAT.
pub(super) fn substitute_array_var_aliases(
    terms: &mut TermStore,
    assertions: &mut Vec<TermId>,
) -> Vec<(TermId, TermId)> {
    // Collect canonical-representative mapping over array-variable aliases drawn
    // ONLY from top-level conjuncts that are directly `(= aVar bVar)`.
    let mut parent: HashMap<TermId, TermId> = HashMap::default();
    fn find(parent: &mut HashMap<TermId, TermId>, x: TermId) -> TermId {
        let mut root = x;
        while let Some(&p) = parent.get(&root) {
            if p == root {
                break;
            }
            root = p;
        }
        // Path compression.
        let mut cur = x;
        while let Some(&p) = parent.get(&cur) {
            if p == root {
                break;
            }
            parent.insert(cur, root);
            cur = p;
        }
        root
    }

    let mut had_alias = false;
    // Flatten top-level `and` so conjuncts of a single `(and …)` assertion are
    // also seen (matches how store-flat reasoning treats top-level conjuncts).
    let mut top_level: Vec<TermId> = Vec::new();
    for &assertion in assertions.iter() {
        flatten_top_level_and(terms, assertion, &mut top_level);
    }
    for &conj in &top_level {
        if let TermData::App(ref sym, ref args) = terms.get(conj).clone() {
            if sym.name() == "=" && args.len() == 2 {
                let (lhs, rhs) = (args[0], args[1]);
                if lhs != rhs
                    && matches!(terms.get(lhs), TermData::Var(_, _))
                    && matches!(terms.get(rhs), TermData::Var(_, _))
                    && matches!(terms.sort(lhs), Sort::Array(_))
                    && matches!(terms.sort(rhs), Sort::Array(_))
                {
                    parent.entry(lhs).or_insert(lhs);
                    parent.entry(rhs).or_insert(rhs);
                    let rl = find(&mut parent, lhs);
                    let rr = find(&mut parent, rhs);
                    if rl != rr {
                        // Canonical representative = the smaller TermId for
                        // determinism (lower-id vars are typically declared first).
                        let (keep, drop) = if rl.0 <= rr.0 { (rl, rr) } else { (rr, rl) };
                        parent.insert(drop, keep);
                        had_alias = true;
                    }
                }
            }
        }
    }

    if !had_alias {
        return Vec::new();
    }

    // Build the substitution map: each aliased variable → its canonical root,
    // excluding the root itself.
    let keys: Vec<TermId> = parent.keys().copied().collect();
    let mut subst_map: HashMap<TermId, TermId> = HashMap::default();
    for v in keys {
        let root = find(&mut parent, v);
        if root != v {
            subst_map.insert(v, root);
        }
    }
    if subst_map.is_empty() {
        return Vec::new();
    }

    // Apply throughout all assertions. The defining alias equality `(= a b)`
    // becomes `(= root root)` → `true` (via mk_eq); drop such tautologies.
    let true_term = terms.true_term();
    let mut cache: HashMap<TermId, TermId> = HashMap::default();
    let mut new_assertions = Vec::with_capacity(assertions.len());
    for &assertion in assertions.iter() {
        let substituted = apply_store_flat_subst(terms, assertion, &subst_map, &mut cache);
        if substituted != true_term {
            new_assertions.push(substituted);
        }
    }
    *assertions = new_assertions;

    let mut pairs: Vec<(TermId, TermId)> = subst_map.into_iter().collect();
    // Deterministic ordering for stable recovery passes.
    pairs.sort_by_key(|(from, _)| from.0);
    pairs
}

/// Append the top-level conjuncts of `assertion` (flattening nested `and`s) to
/// `out`. A non-`and` assertion is pushed as-is.
fn flatten_top_level_and(terms: &TermStore, assertion: TermId, out: &mut Vec<TermId>) {
    if let TermData::App(Symbol::Named(name), args) = terms.get(assertion) {
        if name == "and" {
            let args = args.clone();
            for arg in args {
                flatten_top_level_and(terms, arg, out);
            }
            return;
        }
    }
    out.push(assertion);
}

/// Check if a term is a `store` application.
fn is_store_term(terms: &TermStore, term: TermId) -> bool {
    matches!(
        terms.get(term),
        TermData::App(Symbol::Named(name), args) if name == "store" && args.len() == 3
    )
}

/// Return substitution keys whose transitive replacements reach themselves.
fn cyclic_store_flat_substitution_vars(
    terms: &TermStore,
    subst_map: &HashMap<TermId, TermId>,
) -> HashSet<TermId> {
    let mut cyclic = HashSet::default();

    for (&target, &replacement) in subst_map {
        let mut pending = vec![replacement];
        let mut visited = HashSet::default();

        while let Some(term) = pending.pop() {
            // Check before visited suppression: a mapped path may return to
            // the target through a term already reached along another edge.
            if term == target {
                cyclic.insert(target);
                break;
            }
            if !visited.insert(term) {
                continue;
            }

            if let Some(&nested_replacement) = subst_map.get(&term) {
                pending.push(nested_replacement);
                continue;
            }

            match terms.get(term) {
                TermData::Const(_) | TermData::Var(_, _) => {}
                TermData::App(_, args) => pending.extend(args.iter().copied()),
                TermData::Not(inner) => pending.push(*inner),
                TermData::Ite(condition, then_term, else_term) => {
                    pending.push(*condition);
                    pending.push(*then_term);
                    pending.push(*else_term);
                }
                TermData::Let(bindings, body) => {
                    pending.extend(bindings.iter().map(|(_, value)| *value));
                    pending.push(*body);
                }
                TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {
                    // Match apply_store_flat_subst: quantified bodies are not
                    // rewritten by this QF-only preprocessing pass.
                }
                other => unreachable!(
                    "unhandled TermData variant in cyclic_store_flat_substitution_vars(): {other:?}"
                ),
            }
        }
    }

    cyclic
}

/// Recursively apply store-flat substitutions with caching.
fn apply_store_flat_subst(
    terms: &mut TermStore,
    term: TermId,
    subst_map: &HashMap<TermId, TermId>,
    cache: &mut HashMap<TermId, TermId>,
) -> TermId {
    if let Some(&cached) = cache.get(&term) {
        return cached;
    }

    // If this term is a variable in the substitution map, replace it
    // (and recursively substitute in the replacement).
    if let Some(&replacement) = subst_map.get(&term) {
        let result = apply_store_flat_subst(terms, replacement, subst_map, cache);
        cache.insert(term, result);
        return result;
    }

    let result = match terms.get(term).clone() {
        TermData::Const(_) | TermData::Var(_, _) => term,

        TermData::App(sym, args) => {
            let new_args: Vec<TermId> = args
                .iter()
                .map(|&a| apply_store_flat_subst(terms, a, subst_map, cache))
                .collect();
            if new_args == args {
                term
            } else {
                // Use canonical constructors for known operators.
                match sym.name() {
                    "=" if new_args.len() == 2 => terms.mk_eq_coerce(new_args[0], new_args[1]),
                    "select" if new_args.len() == 2 => terms.mk_select(new_args[0], new_args[1]),
                    "store" if new_args.len() == 3 => {
                        terms.mk_store(new_args[0], new_args[1], new_args[2])
                    }
                    _ => {
                        let sort = terms.sort(term).clone();
                        terms.mk_app(sym.clone(), new_args, sort)
                    }
                }
            }
        }

        TermData::Not(inner) => {
            let new_inner = apply_store_flat_subst(terms, inner, subst_map, cache);
            if new_inner == inner {
                term
            } else {
                terms.mk_not(new_inner)
            }
        }

        TermData::Ite(c, t, e) => {
            let new_c = apply_store_flat_subst(terms, c, subst_map, cache);
            let new_t = apply_store_flat_subst(terms, t, subst_map, cache);
            let new_e = apply_store_flat_subst(terms, e, subst_map, cache);
            if new_c == c && new_t == t && new_e == e {
                term
            } else {
                terms.mk_ite(new_c, new_t, new_e)
            }
        }

        TermData::Let(bindings, body) => {
            let new_bindings: Vec<(String, TermId)> = bindings
                .iter()
                .map(|(name, t)| {
                    (
                        name.clone(),
                        apply_store_flat_subst(terms, *t, subst_map, cache),
                    )
                })
                .collect();
            let new_body = apply_store_flat_subst(terms, body, subst_map, cache);
            let changed = new_body != body
                || new_bindings
                    .iter()
                    .zip(bindings.iter())
                    .any(|((_, a), (_, b))| a != b);
            if changed {
                terms.mk_let(new_bindings, new_body)
            } else {
                term
            }
        }

        TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {
            // Quantifiers are uncommon in QF_AUFLIA; skip substitution inside them.
            term
        }

        other => unreachable!("unhandled TermData variant in apply_store_flat_subst(): {other:?}"),
    };

    cache.insert(term, result);
    result
}

pub(super) fn push_assertion_source_set(
    assertion_sources: &mut HashMap<TermId, Vec<Vec<TermId>>>,
    assertion: TermId,
    mut source_set: Vec<TermId>,
) {
    source_set.sort_by_key(|term| term.index());
    source_set.dedup();
    let entry = assertion_sources.entry(assertion).or_default();
    if !entry.contains(&source_set) {
        entry.push(source_set);
    }
}

pub(super) fn augment_lia_source_sets_with_substitutions(
    terms: &TermStore,
    original_assertions: &[TermId],
    source_sets: &mut [Vec<TermId>],
    var_subst: &VariableSubstitution,
) {
    for (assertion, source_set) in original_assertions
        .iter()
        .copied()
        .zip(source_sets.iter_mut())
    {
        let mut extra_sources = HashSet::default();
        let mut visited_vars = HashSet::default();
        collect_lia_substitution_sources_for_term(
            terms,
            assertion,
            var_subst,
            &mut visited_vars,
            &mut extra_sources,
        );
        for source in extra_sources {
            if !source_set.contains(&source) {
                source_set.push(source);
            }
        }
    }
}

fn collect_lia_substitution_sources_for_term(
    terms: &TermStore,
    term: TermId,
    var_subst: &VariableSubstitution,
    visited_vars: &mut HashSet<TermId>,
    sources: &mut HashSet<TermId>,
) {
    match terms.get(term) {
        TermData::Const(_) => {}
        TermData::Var(_, _) => {
            if !visited_vars.insert(term) {
                return;
            }
            if let Some(&source_assertion) = var_subst.substitution_sources().get(&term) {
                sources.insert(source_assertion);
            }
            if let Some(&replacement) = var_subst.substitutions().get(&term) {
                collect_lia_substitution_sources_for_term(
                    terms,
                    replacement,
                    var_subst,
                    visited_vars,
                    sources,
                );
            }
        }
        TermData::App(_, args) => {
            for &arg in args {
                collect_lia_substitution_sources_for_term(
                    terms,
                    arg,
                    var_subst,
                    visited_vars,
                    sources,
                );
            }
        }
        TermData::Not(inner) => collect_lia_substitution_sources_for_term(
            terms,
            *inner,
            var_subst,
            visited_vars,
            sources,
        ),
        TermData::Ite(cond, then_term, else_term) => {
            collect_lia_substitution_sources_for_term(
                terms,
                *cond,
                var_subst,
                visited_vars,
                sources,
            );
            collect_lia_substitution_sources_for_term(
                terms,
                *then_term,
                var_subst,
                visited_vars,
                sources,
            );
            collect_lia_substitution_sources_for_term(
                terms,
                *else_term,
                var_subst,
                visited_vars,
                sources,
            );
        }
        TermData::Let(bindings, body) => {
            for (_, value) in bindings {
                collect_lia_substitution_sources_for_term(
                    terms,
                    *value,
                    var_subst,
                    visited_vars,
                    sources,
                );
            }
            collect_lia_substitution_sources_for_term(
                terms,
                *body,
                var_subst,
                visited_vars,
                sources,
            );
        }
        TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
            collect_lia_substitution_sources_for_term(
                terms,
                *body,
                var_subst,
                visited_vars,
                sources,
            );
            for &trigger_term in triggers.iter().flatten() {
                collect_lia_substitution_sources_for_term(
                    terms,
                    trigger_term,
                    var_subst,
                    visited_vars,
                    sources,
                );
            }
        }
        other => unreachable!(
            "unhandled TermData variant in collect_lia_substitution_sources_for_term(): {other:?}"
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    fn int(terms: &mut TermStore, value: i64) -> TermId {
        terms.mk_int(BigInt::from(value))
    }

    #[test]
    fn store_flat_mutual_cycle_is_left_unchanged() {
        let mut terms = TermStore::new();
        let array_sort = Sort::array(Sort::Int, Sort::Int);
        let a = terms.mk_var("a", array_sort.clone());
        let b = terms.mk_var("b", array_sort);
        let zero = int(&mut terms, 0);
        let one = int(&mut terms, 1);
        let ten = int(&mut terms, 10);
        let twenty = int(&mut terms, 20);
        let store_b = terms.mk_store(b, zero, ten);
        let store_a = terms.mk_store(a, one, twenty);
        let a_def = terms.mk_eq(a, store_b);
        let b_def = terms.mk_eq(b, store_a);
        let mut assertions = vec![a_def, b_def];
        let original = assertions.clone();

        substitute_store_flat_equalities(&mut terms, &mut assertions);

        assert_eq!(
            assertions, original,
            "mutually recursive store definitions must fail closed"
        );
    }

    #[test]
    fn store_flat_three_node_cycle_is_left_unchanged() {
        let mut terms = TermStore::new();
        let array_sort = Sort::array(Sort::Int, Sort::Int);
        let a = terms.mk_var("a", array_sort.clone());
        let b = terms.mk_var("b", array_sort.clone());
        let c = terms.mk_var("c", array_sort);
        let zero = int(&mut terms, 0);
        let one = int(&mut terms, 1);
        let two = int(&mut terms, 2);
        let ten = int(&mut terms, 10);
        let twenty = int(&mut terms, 20);
        let thirty = int(&mut terms, 30);
        let store_b = terms.mk_store(b, zero, ten);
        let store_c = terms.mk_store(c, one, twenty);
        let store_a = terms.mk_store(a, two, thirty);
        let a_def = terms.mk_eq(a, store_b);
        let b_def = terms.mk_eq(b, store_c);
        let c_def = terms.mk_eq(c, store_a);
        let mut assertions = vec![a_def, b_def, c_def];
        let original = assertions.clone();

        substitute_store_flat_equalities(&mut terms, &mut assertions);

        assert_eq!(
            assertions, original,
            "multi-node recursive store definitions must fail closed"
        );
    }

    #[test]
    fn store_flat_cycle_does_not_disable_independent_substitution() {
        let mut terms = TermStore::new();
        let array_sort = Sort::array(Sort::Int, Sort::Int);
        let a = terms.mk_var("a", array_sort.clone());
        let b = terms.mk_var("b", array_sort.clone());
        let d = terms.mk_var("d", array_sort.clone());
        let e = terms.mk_var("e", array_sort);
        let zero = int(&mut terms, 0);
        let one = int(&mut terms, 1);
        let three = int(&mut terms, 3);
        let ten = int(&mut terms, 10);
        let twenty = int(&mut terms, 20);
        let forty = int(&mut terms, 40);
        let store_b = terms.mk_store(b, zero, ten);
        let store_a = terms.mk_store(a, one, twenty);
        let store_e = terms.mk_store(e, three, forty);
        let a_def = terms.mk_eq(a, store_b);
        let b_def = terms.mk_eq(b, store_a);
        let d_def = terms.mk_eq(d, store_e);
        let read_d = terms.mk_select(d, three);
        let read_eq = terms.mk_eq(read_d, forty);
        let mut assertions = vec![a_def, b_def, d_def, read_eq];

        substitute_store_flat_equalities(&mut terms, &mut assertions);

        assert_eq!(
            assertions,
            vec![a_def, b_def],
            "only the cyclic component should be pruned"
        );
    }
}
