// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lexical capture admission for the one global Boolean-proxy substitution.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::{TermData, TermId, TermStore};

type Names<'a> = DetHashSet<&'a str>;
type FreeNames<'a> = DetHashMap<TermId, Option<Names<'a>>>;

/// Free spellings relative to this term's OWN binders. A raw `Var` identity
/// does not discharge a surrounding name binder. Unknown syntax is not closed.
fn free_names<'a>(
    terms: &'a TermStore,
    term: TermId,
    memo: &mut FreeNames<'a>,
) -> Option<Names<'a>> {
    if let Some(known) = memo.get(&term) {
        return known.clone();
    }
    let result = stacker::maybe_grow(32 * 1024, 1024 * 1024, || {
        let mut free = Names::default();
        match terms.get(term) {
            TermData::Var(name, _) => {
                free.insert(name.as_str());
            }
            TermData::Const(_) => {}
            TermData::App(_, arguments) => {
                for &argument in arguments {
                    free.extend(free_names(terms, argument, memo)?);
                }
            }
            TermData::Not(inner) => free.extend(free_names(terms, *inner, memo)?),
            TermData::Ite(condition, yes, no) => {
                for child in [condition, yes, no] {
                    free.extend(free_names(terms, *child, memo)?);
                }
            }
            TermData::Let(bindings, body) => {
                // Simultaneous RHS values see only the OUTER scope.
                for (_, value) in bindings {
                    free.extend(free_names(terms, *value, memo)?);
                }
                let mut body_free = free_names(terms, *body, memo)?;
                body_free.retain(|name| !bindings.iter().any(|(bound, _)| bound.as_str() == *name));
                free.extend(body_free);
            }
            TermData::Forall(bindings, body, triggers)
            | TermData::Exists(bindings, body, triggers) => {
                free.extend(free_names(terms, *body, memo)?);
                for &trigger in triggers.iter().flatten() {
                    free.extend(free_names(terms, trigger, memo)?);
                }
                free.retain(|name| !bindings.iter().any(|(bound, _)| bound.as_str() == *name));
            }
            _ => return None,
        }
        Some(free)
    });
    memo.insert(term, result.clone());
    result
}

/// All retained binder spellings, including unused names and trigger-only
/// syntax. A newly inserted proxy must not acquire any of these bindings.
fn binder_names<'a>(terms: &'a TermStore, roots: &[TermId]) -> Option<Names<'a>> {
    let mut names = Names::default();
    let mut seen = DetHashSet::default();
    let mut pending = roots.to_vec();
    while let Some(term) = pending.pop() {
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::App(_, arguments) => pending.extend(arguments.iter().copied()),
            TermData::Not(inner) => pending.push(*inner),
            TermData::Ite(condition, yes, no) => pending.extend([*condition, *yes, *no]),
            TermData::Let(bindings, body) => {
                names.extend(bindings.iter().map(|(name, _)| name.as_str()));
                pending.extend(bindings.iter().map(|(_, value)| *value));
                pending.push(*body);
            }
            TermData::Forall(bindings, body, triggers)
            | TermData::Exists(bindings, body, triggers) => {
                names.extend(bindings.iter().map(|(name, _)| name.as_str()));
                pending.push(*body);
                pending.extend(triggers.iter().flatten().copied());
                pending.extend(terms.quantifier_no_patterns(term).iter().copied());
            }
            _ => return None,
        }
    }
    Some(names)
}

/// Union incoming lexical contexts, revisiting a shared term whenever that
/// union grows. The FIRST visit is scheduled even for an empty incoming set.
fn merge<'a>(
    term: TermId,
    incoming: &Names<'a>,
    contexts: &mut DetHashMap<TermId, Names<'a>>,
    queued: &mut DetHashSet<TermId>,
    pending: &mut Vec<TermId>,
) {
    let changed = if let Some(known) = contexts.get_mut(&term) {
        let before = known.len();
        known.extend(incoming.iter().copied());
        known.len() != before
    } else {
        contexts.insert(term, incoming.clone());
        true
    };
    if changed && queued.insert(term) {
        pending.push(term);
    }
}

/// Retain only targets safe at EVERY occurrence the existing global recorder
/// can replace. A safe occurrence must not hide a captured occurrence of the
/// same TermId elsewhere. This admits no new candidate under a quantifier.
///
/// The analysis borrows names only while the store is immutable. Returned
/// spellings are owned before the caller starts allocating proxy terms.
pub(super) fn retain_closed(
    terms: &TermStore,
    roots: &[TermId],
    targets: &mut DetHashSet<TermId>,
) -> Option<DetHashSet<String>> {
    let binders = binder_names(terms, roots)?;
    let mut free = FreeNames::default();
    let mut relevant = Names::default();
    // Only a candidate's free spellings can make an occurrence unsafe.
    // Unsupported closure is vetoed, never recorded as an empty free set.
    targets.retain(|&term| {
        if let Some(names) = free_names(terms, term, &mut free) {
            relevant.extend(names);
            true
        } else {
            false
        }
    });
    // Every candidate's free set is known now. Unrelated binders cannot
    // capture one, but ALL their strings still protect proxy allocation.
    if relevant.is_disjoint(&binders) {
        return Some(binders.into_iter().map(str::to_owned).collect());
    }
    let mut contexts = DetHashMap::default();
    let mut queued = DetHashSet::default();
    let mut pending = Vec::new();
    for &root in roots {
        merge(
            root,
            &Names::default(),
            &mut contexts,
            &mut queued,
            &mut pending,
        );
    }
    while let Some(term) = pending.pop() {
        queued.remove(&term);
        let active = contexts.get(&term)?.clone();
        if targets.contains(&term) {
            let safe = free
                .get(&term)
                .and_then(Option::as_ref)
                .is_some_and(|names| names.is_disjoint(&active));
            if !safe {
                targets.remove(&term);
            }
        }
        // These are EXACTLY the recursive edges substitute_terms_inner uses.
        // Triggers remain unchanged; its quantifier BODY still is rewritten.
        match terms.get(term) {
            TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::App(_, arguments) => {
                for &argument in arguments {
                    merge(argument, &active, &mut contexts, &mut queued, &mut pending);
                }
            }
            TermData::Not(inner) => {
                merge(*inner, &active, &mut contexts, &mut queued, &mut pending);
            }
            TermData::Ite(condition, yes, no) => {
                for &child in [condition, yes, no] {
                    merge(child, &active, &mut contexts, &mut queued, &mut pending);
                }
            }
            TermData::Let(bindings, body) => {
                for (_, value) in bindings {
                    merge(*value, &active, &mut contexts, &mut queued, &mut pending);
                }
                let mut body_scope = active;
                body_scope.extend(bindings.iter().filter_map(|(name, _)| {
                    let bound = name.as_str();
                    relevant.contains(bound).then_some(bound)
                }));
                merge(*body, &body_scope, &mut contexts, &mut queued, &mut pending);
            }
            TermData::Forall(bindings, body, _) | TermData::Exists(bindings, body, _) => {
                let mut body_scope = active;
                body_scope.extend(bindings.iter().filter_map(|(name, _)| {
                    let bound = name.as_str();
                    relevant.contains(bound).then_some(bound)
                }));
                merge(*body, &body_scope, &mut contexts, &mut queued, &mut pending);
            }
            _ => return None,
        }
    }
    Some(binders.into_iter().map(str::to_owned).collect())
}
