// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};

use super::{instantiate_body, TermIndex};

/// Enumerative instantiation fallback for triggerless quantifiers.
///
/// When E-matching auto-pattern extraction and CEGQI both fail (e.g., the quantifier
/// body uses only builtin operators over bound variables mixed with UF), this fallback
/// collects all ground terms of the right sort from the assertion set and instantiates
/// the quantifier body with every combination.
///
/// This is a simplified form of Z3's MBQI: instead of using the model to guide
/// instantiation, we enumerate all available ground terms. Sound because every
/// instantiation of a universally quantified formula is implied by the formula.
///
/// Reference: Z3 smt/smt_model_based_qi.cpp, CVC5 QuantifiersEngine::getTermForType
pub(crate) fn enumerative_instantiation(
    terms: &mut TermStore,
    assertions: &[TermId],
    quantifier: TermId,
    max_instantiations: usize,
) -> Vec<TermId> {
    // A no_mbqi ("E-matching only") quantifier — the Hilbert-`choose` combined
    // axiom — must never be enumeratively (synthesis) instantiated: enumeration
    // builds the cartesian product of ground terms, which reaches the always-true
    // diagonal f2(x,x) and discharges the choose existential with no genuine
    // witness (unfaithful to Verus). Fail closed instead.
    if terms.is_no_mbqi(quantifier) {
        return vec![];
    }
    let (vars, body) = match terms.get(quantifier) {
        TermData::Forall(v, b, _) => (v.clone(), *b),
        TermData::Exists(v, b, _) => (v.clone(), *b),
        _ => return vec![],
    };

    if vars.is_empty() {
        return vec![];
    }

    // Collect ground terms by sort from the assertion set.
    // A ground term is any term that is not under a quantifier binding scope
    // and has no free bound variables.
    let ground_by_sort = collect_ground_terms_by_sort(terms, assertions);

    // For each bound variable, find ground terms of the matching sort.
    let mut candidates_per_var: Vec<Vec<TermId>> = Vec::with_capacity(vars.len());
    for (_name, sort) in &vars {
        let candidates = ground_by_sort.get(sort).cloned().unwrap_or_default();
        if candidates.is_empty() {
            // No ground terms of this sort — can't instantiate this quantifier.
            return vec![];
        }
        candidates_per_var.push(candidates);
    }

    // Generate cartesian product of bindings, up to max_instantiations.
    let var_names: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();
    let mut instantiations = Vec::new();
    let mut indices: Vec<usize> = vec![0; vars.len()];

    loop {
        if instantiations.len() >= max_instantiations {
            break;
        }

        // Build binding from current indices
        let binding: Vec<TermId> = indices
            .iter()
            .enumerate()
            .map(|(var_idx, &term_idx)| candidates_per_var[var_idx][term_idx])
            .collect();

        let inst = instantiate_body(terms, body, &var_names, &binding);
        instantiations.push(inst);

        // Advance to next combination (rightmost index increments first)
        let mut carry = true;
        for i in (0..vars.len()).rev() {
            if carry {
                indices[i] += 1;
                if indices[i] < candidates_per_var[i].len() {
                    carry = false;
                } else {
                    indices[i] = 0;
                }
            }
        }
        if carry {
            break; // All combinations exhausted
        }
    }

    instantiations
}

/// Collect ground terms from assertions grouped by their sort.
///
/// Walks the assertion DAG, collecting:
/// - Constants (Int, Real, etc.)
/// - Declared variables (constants in SMT-LIB terms)
/// - Function applications that are fully ground
///
/// Skips terms under quantifier binders (those are not ground).
/// Public for MBQI (#5971).
pub(crate) fn collect_ground_terms_by_sort(
    terms: &TermStore,
    assertions: &[TermId],
) -> HashMap<Sort, Vec<TermId>> {
    let mut result: HashMap<Sort, Vec<TermId>> = HashMap::default();
    let mut visited: HashSet<TermId> = HashSet::default();
    // Collect bound var IDs (same as TermIndex) to skip non-ground terms
    let mut bound_var_ids: HashSet<u32> = HashSet::default();
    let mut bound_names: HashSet<String> = HashSet::default();
    for idx in 0..terms.len() {
        let term_id = TermId(idx as u32);
        TermIndex::collect_bound_var_ids(terms, term_id, &mut bound_var_ids, &mut bound_names);
    }

    for &assertion in assertions {
        collect_ground_terms_recursive(terms, assertion, &bound_var_ids, &mut visited, &mut result);
    }

    // Deduplicate within each sort
    for terms_vec in result.values_mut() {
        terms_vec.sort_unstable_by_key(|t| t.0);
        terms_vec.dedup();
    }

    result
}

/// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
fn collect_ground_terms_recursive(
    terms: &TermStore,
    term: TermId,
    bound_var_ids: &HashSet<u32>,
    visited: &mut HashSet<TermId>,
    result: &mut HashMap<Sort, Vec<TermId>>,
) {
    stacker::maybe_grow(
        super::EMATCH_STACK_RED_ZONE,
        super::EMATCH_STACK_SIZE,
        || {
            if !visited.insert(term) {
                return;
            }

            match terms.get(term) {
                TermData::Const(_) => {
                    let sort = terms.sort(term).clone();
                    // Only collect non-Bool constants (Bool constants are trivial)
                    if !matches!(sort, Sort::Bool) {
                        result.entry(sort).or_default().push(term);
                    }
                }
                TermData::Var(_, _)
                    // Only collect if this is a free variable (declared constant), not quantifier-bound
                    if !bound_var_ids.contains(&term.0) => {
                        let sort = terms.sort(term).clone();
                        if !matches!(sort, Sort::Bool) {
                            result.entry(sort).or_default().push(term);
                        }
                    }
                TermData::App(_, args) => {
                    // Collect this App term if it's ground (no bound vars inside)
                    let is_ground = !args
                        .iter()
                        .any(|&arg| term_contains_bound_var(terms, arg, bound_var_ids));
                    if is_ground {
                        let sort = terms.sort(term).clone();
                        if !matches!(sort, Sort::Bool) {
                            result.entry(sort).or_default().push(term);
                        }
                    }
                    // Recurse into children regardless (to find nested ground terms)
                    for &arg in args {
                        collect_ground_terms_recursive(terms, arg, bound_var_ids, visited, result);
                    }
                }
                TermData::Not(inner) => {
                    collect_ground_terms_recursive(terms, *inner, bound_var_ids, visited, result);
                }
                TermData::Ite(c, t, e) => {
                    collect_ground_terms_recursive(terms, *c, bound_var_ids, visited, result);
                    collect_ground_terms_recursive(terms, *t, bound_var_ids, visited, result);
                    collect_ground_terms_recursive(terms, *e, bound_var_ids, visited, result);
                }
                TermData::Let(bindings, body) => {
                    for (_, val) in bindings {
                        collect_ground_terms_recursive(terms, *val, bound_var_ids, visited, result);
                    }
                    collect_ground_terms_recursive(terms, *body, bound_var_ids, visited, result);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    // #3441: Descend into quantifier bodies to find free ground terms.
                    // Free variables inside quantifiers (e.g., `x` in `forall a. NOT(= a x)`)
                    // are legitimate ground terms for enumerative instantiation. The bound
                    // variable check (bound_var_ids) and the is_ground check in App handling
                    // ensure quantifier-bound variables are excluded.
                    collect_ground_terms_recursive(terms, *body, bound_var_ids, visited, result);
                }
                // Future TermData variants: skip (nothing to collect).
                _ => {}
            }
        },
    ) // stacker::maybe_grow
}

/// Check if a term contains any quantifier-bound variable.
fn term_contains_bound_var(terms: &TermStore, term: TermId, bound_var_ids: &HashSet<u32>) -> bool {
    match terms.get(term) {
        TermData::Var(_, _) => bound_var_ids.contains(&term.0),
        TermData::Const(_) => false,
        TermData::App(_, args) => args
            .iter()
            .any(|&arg| term_contains_bound_var(terms, arg, bound_var_ids)),
        TermData::Not(inner) => term_contains_bound_var(terms, *inner, bound_var_ids),
        TermData::Ite(c, t, e) => {
            term_contains_bound_var(terms, *c, bound_var_ids)
                || term_contains_bound_var(terms, *t, bound_var_ids)
                || term_contains_bound_var(terms, *e, bound_var_ids)
        }
        TermData::Let(bindings, body) => {
            bindings
                .iter()
                .any(|(_, val)| term_contains_bound_var(terms, *val, bound_var_ids))
                || term_contains_bound_var(terms, *body, bound_var_ids)
        }
        TermData::Forall(..) | TermData::Exists(..) => true, // conservative: assume bound vars inside
        // Future TermData variants: conservatively assume bound vars present.
        _ => true,
    }
}

/// #bool-ground-inst: collect the ground Bool-sorted terms that occur as an
/// ARGUMENT of an UNINTERPRETED function application anywhere in `assertions`.
///
/// These are exactly the terms the two-point Bool finite-domain expansion
/// loses contact with: an opaque Bool term `c` buried in a UF argument
/// position never becomes a SAT atom, so EUF never merges it with the
/// true/false class and `f(c)` floats free of the expanded `f(true)`/`f(false)`
/// instances (#bool-arg-congruence). The finite-domain expander instantiates
/// Bool binders at these terms IN ADDITION to `true`/`false` — an
/// equivalence-preserving augmentation (any ground Bool term denotes `true` or
/// `false`), see `skolemize::finite_domain`.
///
/// Bool literals are excluded (already covered by the base domain), as is any
/// term containing a quantifier-bound variable (same discipline as
/// [`collect_ground_terms_by_sort`]). Result is sorted/deduped for
/// determinism.
pub(crate) fn collect_bool_uf_arg_terms(terms: &TermStore, assertions: &[TermId]) -> Vec<TermId> {
    let mut bound_var_ids: HashSet<u32> = HashSet::default();
    let mut bound_names: HashSet<String> = HashSet::default();
    for idx in 0..terms.len() {
        let term_id = TermId(idx as u32);
        TermIndex::collect_bound_var_ids(terms, term_id, &mut bound_var_ids, &mut bound_names);
    }
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut out: Vec<TermId> = Vec::new();
    for &a in assertions {
        collect_bool_uf_args_recursive(terms, a, &bound_var_ids, &mut visited, &mut out);
    }
    out.sort_unstable_by_key(|t| t.0);
    out.dedup();
    out
}

/// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
fn collect_bool_uf_args_recursive(
    terms: &TermStore,
    term: TermId,
    bound_var_ids: &HashSet<u32>,
    visited: &mut HashSet<TermId>,
    out: &mut Vec<TermId>,
) {
    stacker::maybe_grow(
        super::EMATCH_STACK_RED_ZONE,
        super::EMATCH_STACK_SIZE,
        || {
            if !visited.insert(term) {
                return;
            }
            match terms.get(term) {
                TermData::App(sym, args) => {
                    let uf = !crate::features::is_builtin_symbol_name(sym.name());
                    for &arg in args {
                        if uf
                            && matches!(terms.sort(arg), Sort::Bool)
                            && !matches!(terms.get(arg), TermData::Const(_))
                            && !term_contains_bound_var(terms, arg, bound_var_ids)
                        {
                            out.push(arg);
                        }
                        collect_bool_uf_args_recursive(terms, arg, bound_var_ids, visited, out);
                    }
                }
                TermData::Not(inner) => {
                    collect_bool_uf_args_recursive(terms, *inner, bound_var_ids, visited, out);
                }
                TermData::Ite(c, t, e) => {
                    collect_bool_uf_args_recursive(terms, *c, bound_var_ids, visited, out);
                    collect_bool_uf_args_recursive(terms, *t, bound_var_ids, visited, out);
                    collect_bool_uf_args_recursive(terms, *e, bound_var_ids, visited, out);
                }
                TermData::Let(bindings, body) => {
                    for (_, val) in bindings {
                        collect_bool_uf_args_recursive(terms, *val, bound_var_ids, visited, out);
                    }
                    collect_bool_uf_args_recursive(terms, *body, bound_var_ids, visited, out);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    // Same as collect_ground_terms_recursive (#3441): a UF app
                    // under a binder can still carry a GROUND Bool argument
                    // (the bound-var check above excludes non-ground ones).
                    collect_bool_uf_args_recursive(terms, *body, bound_var_ids, visited, out);
                }
                // Const / Var leaves and future variants: nothing to collect.
                _ => {}
            }
        },
    )
}
