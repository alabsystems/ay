// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::DetHashSet as HashSet;

use super::*;

/// Source conjunction path, retaining each exact parent and child position.
pub(super) struct Path {
    pub(super) body: TermId,
    pub(super) edges: Vec<(TermId, u32, TermId)>,
    pub(super) target: TermId,
}

fn live(terms: &TermStore, term: TermId) -> Option<()> {
    ((term.0 as usize) < terms.len()).then_some(())
}

fn scalar(sort: &Sort) -> bool {
    matches!(sort, Sort::Bool)
        || matches!(sort, Sort::BitVec(width) if width.width > 0 && width.width <= crate::api::MAX_API_BITVECTOR_WIDTH)
}

pub(super) fn validate(
    terms: &TermStore,
    request: GuardedStoreRequest,
    progress: Progress<'_>,
) -> Option<[[TermId; 3]; 2]> {
    live(terms, request.variable)?;
    live(terms, request.cover_source)?;
    if let Some(activation) = request.activation {
        live(terms, activation)?;
        if terms.sort(activation) != &Sort::Bool {
            return None;
        }
    }
    let TermData::Var(_, _) = terms.get(request.variable) else {
        return None;
    };
    let Sort::Array(array) = terms.sort(request.variable) else {
        return None;
    };
    if !scalar(&array.index_sort)
        || !scalar(&array.element_sort)
        || terms.sort(request.cover_source) != &Sort::Bool
        || request.cases[0].guard == request.cases[1].guard
    {
        return None;
    }
    let mut stores = [[request.variable; 3]; 2];
    for (case, output) in request.cases.iter().zip(stores.iter_mut()) {
        for term in [case.guard, case.source, case.store] {
            live(terms, term)?;
        }
        if !matches!(terms.get(case.guard), TermData::Var(_, _))
            || terms.sort(case.guard) != &Sort::Bool
            || terms.sort(case.source) != &Sort::Bool
            || terms.sort(case.store) != terms.sort(request.variable)
        {
            return None;
        }
        let TermData::App(Symbol::Named(name), args) = terms.get(case.store) else {
            return None;
        };
        if name != "store" || args.len() != 3 {
            return None;
        }
        for &term in args {
            live(terms, term)?;
        }
        if terms.sort(args[0]) != terms.sort(request.variable)
            || terms.sort(args[1]) != &array.index_sort
            || terms.sort(args[2]) != &array.element_sort
        {
            return None;
        }
        output.copy_from_slice(args);
        independent(terms, case.store, request.variable, progress)?;
    }
    (stores[0][..2] == stores[1][..2]).then_some(stores)
}

fn independent(
    terms: &TermStore,
    root: TermId,
    variable: TermId,
    progress: Progress<'_>,
) -> Option<()> {
    if !progress(1, 64) {
        return None;
    }
    let mut todo = vec![root];
    let mut seen = HashSet::default();
    while let Some(term) = todo.pop() {
        if !progress(1, 64) {
            return None;
        }
        live(terms, term)?;
        if term == variable {
            return None;
        }
        if !seen.insert(term) {
            continue;
        }
        let children: &[TermId] = match terms.get(term) {
            TermData::App(_, args) => args,
            TermData::Not(child) => std::slice::from_ref(child),
            TermData::Ite(c, t, e) => {
                if !progress(3, 24) {
                    return None;
                }
                todo.extend([*c, *t, *e]);
                continue;
            }
            TermData::Const(_) | TermData::Var(_, _) => continue,
            _ => return None,
        };
        if !progress(children.len(), children.len().checked_mul(8)?) {
            return None;
        }
        todo.extend_from_slice(children);
    }
    Some(())
}

fn guarded_body(terms: &TermStore, source: TermId, guard: TermId) -> Option<TermId> {
    let TermData::App(Symbol::Named(name), args) = terms.get(source) else {
        return None;
    };
    if name != "or" || args.len() != 2 {
        return None;
    }
    for index in 0..2 {
        live(terms, args[index])?;
        live(terms, args[1 - index])?;
        if matches!(terms.get(args[index]), TermData::Not(inner) if *inner == guard)
            && terms.sort(args[index]) == &Sort::Bool
            && terms.sort(args[1 - index]) == &Sort::Bool
        {
            return Some(args[1 - index]);
        }
    }
    None
}

pub(super) fn case_path(
    terms: &TermStore,
    variable: TermId,
    case: GuardedStoreCase,
    progress: Progress<'_>,
) -> Option<Path> {
    let body = guarded_body(terms, case.source, case.guard)?;
    find(terms, body, progress, |term| {
        matches!(terms.get(term), TermData::App(Symbol::Named(name), args)
            if name == "=" && (args.as_slice() == [variable, case.store]
                || args.as_slice() == [case.store, variable]))
    })
}

pub(super) fn cover_path(
    terms: &TermStore,
    request: GuardedStoreRequest,
    progress: Progress<'_>,
) -> Option<Path> {
    let body = match request.activation {
        Some(guard) => guarded_body(terms, request.cover_source, guard)?,
        None => request.cover_source,
    };
    let [g, h] = request.cases.map(|case| case.guard);
    find(terms, body, progress, |term| {
        matches!(terms.get(term), TermData::App(Symbol::Named(name), args)
            if name == "or" && (args.as_slice() == [g, h] || args.as_slice() == [h, g]))
    })
}

fn find(
    terms: &TermStore,
    body: TermId,
    progress: Progress<'_>,
    matches: impl Fn(TermId) -> bool,
) -> Option<Path> {
    if !progress(1, 128) {
        return None;
    }
    let mut nodes: Vec<(TermId, Option<(usize, u32)>)> = vec![(body, None)];
    let mut seen = HashSet::default();
    let mut cursor = 0;
    while cursor < nodes.len() {
        let (term, _) = nodes[cursor];
        live(terms, term)?;
        if !progress(1, 64) || terms.sort(term) != &Sort::Bool {
            return None;
        }
        if !seen.insert(term) {
            cursor += 1;
            continue;
        }
        if matches(term) {
            if !progress(nodes.len(), nodes.len().checked_mul(24)?) {
                return None;
            }
            let mut edges = Vec::new();
            let mut index = cursor;
            while let Some((parent, position)) = nodes[index].1 {
                edges.push((nodes[parent].0, position, nodes[index].0));
                index = parent;
            }
            edges.reverse();
            return Some(Path {
                body,
                edges,
                target: term,
            });
        }
        if let TermData::App(Symbol::Named(name), args) = terms.get(term) {
            if name == "and" {
                if !progress(args.len(), args.len().checked_mul(64)?) {
                    return None;
                }
                for (position, &child) in args.iter().enumerate() {
                    if !seen.contains(&child) {
                        nodes.push((child, Some((cursor, u32::try_from(position).ok()?))));
                    }
                }
            }
        }
        cursor += 1;
    }
    None
}
