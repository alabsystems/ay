// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checking `alpha(phi)`: the lockstep renaming check the rung's authority
//! rests on.

use super::build::{
    app_head_class, binders_are_array_free, classify_sort, is_binary_equality,
    is_minted_function_name, sort_mentions_uninterpreted, ArrayUfAbstraction, HeadClass,
    RenamingWitness, MAX_ABSTRACTION_NODES,
};
use super::*;
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Sort, Symbol};

/// THE CHECK. Accept `abstraction` as `alpha(original)` under its own witness,
/// or reject.
///
/// This is the half of the rung that carries the soundness argument, so it
/// re-derives everything from the term store and the witness maps:
///
/// * the witness is well formed: array sorts and array-reaching declared
///   carriers map to pairwise distinct fresh uninterpreted sorts, typed
///   operations the head classifier renames at exactly that signature (array
///   operations, carrier constructors and selectors) to pairwise distinct
///   fresh symbols spelled by this rung's own mint (so none is a theory
///   operator or constructor), constants of those sorts to pairwise distinct
///   fresh constants with pairwise distinct names, and no fresh name is shared
///   across the three;
/// * no fresh identity occurs anywhere in `original` (as a node, a name, a
///   head, a binder or inside a sort), so the induced structure never needs two
///   interpretations for one name;
/// * the two root lists have the same length and every positionally paired
///   node has the same variant, arity, binders and triggers shape, with
///   `sort(abstract) == sigma(sort(original))`, array-free leaves unchanged,
///   renamed constants and heads drawn from THIS witness, and kept heads only
///   where their signature is unchanged or they are `=`/`distinct` (a binary
///   `=` the witness marks swapped pairs its two children crosswise, which is
///   the same proposition);
/// * no quantifier binds an array-sorted variable, and no renamed constant's
///   name is reused by any binder, so no variable can be captured or released;
/// * no kept sort reaches an array, declared datatype carriers included, and
///   the abstract roots contain no array term at all.
pub(super) fn is_pure_renaming(
    terms: &TermStore,
    original: &[TermId],
    abstraction: &ArrayUfAbstraction,
) -> bool {
    let witness = &abstraction.witness;
    let abstract_roots = abstraction.roots();
    if original.len() != abstract_roots.len() || original.is_empty() {
        return false;
    }
    let Some(fresh) = FreshNames::of(terms, witness) else {
        return false;
    };
    let Some(binder_names) = original_is_fresh_free(terms, original, &fresh) else {
        return false;
    };
    let lockstep = Lockstep {
        terms,
        witness,
        binder_names: &binder_names,
    };
    let mut visited: HashSet<(TermId, TermId)> = HashSet::default();
    let mut pairs: Vec<(TermId, TermId)> = original
        .iter()
        .copied()
        .zip(abstract_roots.iter().copied())
        .collect();
    while let Some((node, image)) = pairs.pop() {
        if !visited.insert((node, image)) {
            continue;
        }
        if visited.len() > MAX_ABSTRACTION_NODES || !lockstep.pair_matches(node, image, &mut pairs)
        {
            return false;
        }
    }
    // Independent of the walk: the quarantine's own feature predicates must see
    // no array-sorted term in the abstract problem, and nothing it would arm on
    // (`has_nested_arrays` also resolves declared datatype carriers).
    let features = StaticFeatures::collect(terms, abstract_roots);
    !features.has_arrays && !features.has_nested_arrays
}

/// One lockstep comparison context: the store, the witness under test, and
/// the binder names the original DAG uses.
struct Lockstep<'a> {
    terms: &'a TermStore,
    witness: &'a RenamingWitness,
    binder_names: &'a HashSet<&'a str>,
}

impl Lockstep<'_> {
    /// Compare one positionally paired `(original, image)` node and queue its
    /// children pairs. `false` rejects the whole abstraction.
    fn pair_matches(&self, node: TermId, image: TermId, pairs: &mut Vec<(TermId, TermId)>) -> bool {
        let (terms, witness) = (self.terms, self.witness);
        let original_sort = terms.sort(node);
        if witness.mapped_sort(terms, original_sort).as_ref() != Some(terms.sort(image)) {
            return false;
        }
        let renamed_sort = classify_sort(terms, original_sort).is_renamed();
        match (terms.get(node), terms.get(image)) {
            (TermData::Const(_), TermData::Const(_)) => !renamed_sort && node == image,
            (TermData::Var(name, _), TermData::Var(_, _)) => {
                let renamed_ok = renamed_sort
                    && witness.vars.get(&node) == Some(&image)
                    && !self.binder_names.contains(name.as_str());
                renamed_ok || (!renamed_sort && node == image)
            }
            (TermData::App(symbol, args), TermData::App(image_symbol, image_args)) => {
                if args.len() != image_args.len() {
                    return false;
                }
                let arg_sorts = args
                    .iter()
                    .map(|&arg| terms.sort(arg).clone())
                    .collect::<Vec<Sort>>();
                let head_ok = match app_head_class(terms, symbol, original_sort, &arg_sorts) {
                    Some(HeadClass::Kept) => symbol == image_symbol,
                    Some(HeadClass::Renamed) => {
                        let key = (symbol.clone(), original_sort.clone(), arg_sorts);
                        witness.symbols.get(&key) == Some(image_symbol)
                    }
                    None => false,
                };
                if witness.swapped.contains(&node) {
                    if !is_binary_equality(symbol, args, original_sort) {
                        return false;
                    }
                    pairs.extend([(args[0], image_args[1]), (args[1], image_args[0])]);
                } else {
                    pairs.extend(args.iter().copied().zip(image_args.iter().copied()));
                }
                head_ok
            }
            (TermData::Not(inner), TermData::Not(image_inner)) => {
                pairs.push((*inner, *image_inner));
                true
            }
            (TermData::Ite(c, t, e), TermData::Ite(image_c, image_t, image_e)) => {
                pairs.extend([(*c, *image_c), (*t, *image_t), (*e, *image_e)]);
                true
            }
            (
                TermData::Forall(vars, body, triggers),
                TermData::Forall(image_vars, image_body, image_triggers),
            )
            | (
                TermData::Exists(vars, body, triggers),
                TermData::Exists(image_vars, image_body, image_triggers),
            ) => {
                if vars != image_vars
                    || !binders_are_array_free(terms, vars)
                    || triggers.len() != image_triggers.len()
                {
                    return false;
                }
                for (group, image_group) in triggers.iter().zip(image_triggers) {
                    if group.len() != image_group.len() {
                        return false;
                    }
                    pairs.extend(group.iter().copied().zip(image_group.iter().copied()));
                }
                pairs.push((*body, *image_body));
                true
            }
            // A variant mismatch, `Let`, or a future `TermData` variant.
            _ => false,
        }
    }
}

/// The fresh names a witness introduces, validated for shape and injectivity.
struct FreshNames<'a> {
    sorts: HashSet<&'a str>,
    /// Fresh function and constant names together: the two share the symbol
    /// namespace of a printed or re-parsed problem, so one must never alias the
    /// other.
    symbols: HashSet<&'a str>,
    constant_nodes: HashSet<TermId>,
}

impl<'a> FreshNames<'a> {
    fn of(terms: &'a TermStore, witness: &'a RenamingWitness) -> Option<Self> {
        let mut sorts = HashSet::default();
        for (original, fresh) in &witness.sorts {
            let Sort::Uninterpreted(name) = fresh else {
                return None;
            };
            if !classify_sort(terms, original).is_renamed() || !sorts.insert(name.as_str()) {
                return None;
            }
        }
        let mut symbols = HashSet::default();
        for ((symbol, result, args), fresh) in &witness.symbols {
            let Symbol::Named(_) = fresh else {
                return None;
            };
            if !matches!(
                app_head_class(terms, symbol, result, args),
                Some(HeadClass::Renamed)
            ) || !is_minted_function_name(fresh.name())
                || !symbols.insert(fresh.name())
            {
                return None;
            }
        }
        let mut constant_nodes = HashSet::default();
        for (&original, &fresh) in &witness.vars {
            let (TermData::Var(_, _), TermData::Var(fresh_name, _)) =
                (terms.get(original), terms.get(fresh))
            else {
                return None;
            };
            let expected_sort = witness.sorts.get(terms.sort(original))?;
            if terms.sort(fresh) != expected_sort
                || !constant_nodes.insert(fresh)
                || !symbols.insert(fresh_name.as_str())
                || sorts.contains(fresh_name.as_str())
            {
                return None;
            }
        }
        if symbols.iter().any(|name| sorts.contains(name)) {
            return None;
        }
        Some(Self {
            sorts,
            symbols,
            constant_nodes,
        })
    }
}

/// Check that no fresh identity occurs in the ORIGINAL DAG and collect every
/// binder name it uses. `None` rejects.
fn original_is_fresh_free<'a>(
    terms: &'a TermStore,
    original: &[TermId],
    fresh: &FreshNames<'_>,
) -> Option<HashSet<&'a str>> {
    let mut binder_names = HashSet::default();
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack = original.to_vec();
    let sort_is_fresh_free =
        |sort: &Sort| sort_mentions_uninterpreted(sort, &fresh.sorts, 0) == Some(false);
    while let Some(node) = stack.pop() {
        if !seen.insert(node) {
            continue;
        }
        if seen.len() > MAX_ABSTRACTION_NODES
            || fresh.constant_nodes.contains(&node)
            || !sort_is_fresh_free(terms.sort(node))
        {
            return None;
        }
        match terms.get(node) {
            TermData::Const(_) => {}
            TermData::Var(name, _) => {
                if fresh.symbols.contains(name.as_str()) {
                    return None;
                }
            }
            TermData::App(symbol, args) => {
                if fresh.symbols.contains(symbol.name()) {
                    return None;
                }
                stack.extend(args.iter().copied());
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => stack.extend([*c, *t, *e]),
            TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                for (name, sort) in vars {
                    if fresh.symbols.contains(name.as_str()) || !sort_is_fresh_free(sort) {
                        return None;
                    }
                    binder_names.insert(name.as_str());
                }
                stack.push(*body);
                stack.extend(triggers.iter().flatten().copied());
            }
            _ => return None,
        }
    }
    Some(binder_names)
}
