// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::DetHashSet as HashSet;

use super::*;

pub(super) struct Unit {
    pub(super) source: TermId,
    pub(super) activation: TermId,
    pub(super) path: shape::Path,
}

pub(super) struct Plan {
    pub(super) requests: Vec<GuardedStoreRequest>,
    pub(super) units: Vec<Unit>,
}

struct Case {
    variable: TermId,
    case: GuardedStoreCase,
    base: TermId,
    key: TermId,
}

struct Cover {
    source: TermId,
    activation: Option<TermId>,
    guards: [TermId; 2],
}

fn live(terms: &TermStore, term: TermId) -> bool {
    (term.0 as usize) < terms.len()
}

fn bool_variable(terms: &TermStore, term: TermId) -> bool {
    live(terms, term)
        && terms.sort(term) == &Sort::Bool
        && matches!(terms.get(term), TermData::Var(_, _))
}

fn scalar(sort: &Sort) -> bool {
    matches!(sort, Sort::Bool)
        || matches!(sort, Sort::BitVec(width) if width.width > 0
            && width.width <= crate::api::MAX_API_BITVECTOR_WIDTH)
}

fn scalar_array_variable(terms: &TermStore, term: TermId) -> bool {
    live(terms, term)
        && matches!(terms.get(term), TermData::Var(_, _))
        && matches!(terms.sort(term), Sort::Array(array)
            if scalar(&array.index_sort) && scalar(&array.element_sort))
}

fn cover(terms: &TermStore, term: TermId) -> Option<[TermId; 2]> {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    (name == "or"
        && args.len() == 2
        && args[0] != args[1]
        && args.iter().all(|&arg| bool_variable(terms, arg)))
    .then(|| [args[0], args[1]])
}

fn alias_variable(terms: &TermStore, term: TermId) -> bool {
    live(terms, term)
        && matches!(terms.get(term), TermData::Var(_, _))
        && (scalar(terms.sort(term)) || scalar_array_variable(terms, term))
}

fn typed_alias(terms: &TermStore, term: TermId) -> bool {
    matches!(terms.get(term), TermData::App(Symbol::Named(name), args)
        if name == "=" && args.len() == 2
            && args.iter().all(|&arg| alias_variable(terms, arg))
            && terms.sort(args[0]) == terms.sort(args[1]))
}

pub(super) fn scan(terms: &TermStore, roots: &[TermId], progress: Progress<'_>) -> Option<Plan> {
    let mut asserted = Vec::new();
    let mut activations = HashSet::default();
    for &root in roots {
        for leaf in leaves(terms, root, progress)? {
            if !progress(1, 80) {
                return None;
            }
            if bool_variable(terms, leaf.target) {
                activations.insert(leaf.target);
            }
            asserted.push(leaf.target);
        }
    }
    let mut cases = Vec::new();
    let mut covers = Vec::new();
    let mut units = Vec::new();
    for source in asserted {
        if !progress(64, 128) {
            return None;
        }
        if let Some(guards) = cover(terms, source) {
            covers.push(Cover {
                source,
                activation: None,
                guards,
            });
        }
        let TermData::App(Symbol::Named(name), args) = terms.get(source) else {
            continue;
        };
        if name != "or" || args.len() != 2 {
            continue;
        }
        for position in 0..2 {
            let negated = args[position];
            let body = args[1 - position];
            if !live(terms, negated) || !live(terms, body) {
                return None;
            }
            let TermData::Not(guard) = terms.get(negated) else {
                continue;
            };
            if !bool_variable(terms, *guard) || terms.sort(negated) != &Sort::Bool {
                continue;
            }
            collect_body(
                terms,
                source,
                *guard,
                body,
                activations.contains(guard),
                &mut cases,
                &mut covers,
                &mut units,
                progress,
            )?;
        }
    }
    Some(Plan {
        requests: join(&cases, &covers, progress)?,
        units,
    })
}

fn collect_body(
    terms: &TermStore,
    source: TermId,
    guard: TermId,
    body: TermId,
    activated: bool,
    cases: &mut Vec<Case>,
    covers: &mut Vec<Cover>,
    units: &mut Vec<Unit>,
    progress: Progress<'_>,
) -> Option<()> {
    for path in leaves(terms, body, progress)? {
        if !progress(64, 256) {
            return None;
        }
        if let Some(case) = store_case(terms, source, guard, path.target) {
            cases.push(case);
        }
        if activated {
            let guards = cover(terms, path.target);
            if let Some(guards) = guards {
                covers.push(Cover {
                    source,
                    activation: Some(guard),
                    guards,
                });
            }
            if guards.is_some() || typed_alias(terms, path.target) {
                units.push(Unit {
                    source,
                    activation: guard,
                    path,
                });
            }
        }
    }
    Some(())
}

fn store_case(terms: &TermStore, source: TermId, guard: TermId, term: TermId) -> Option<Case> {
    let TermData::App(Symbol::Named(eq), pair) = terms.get(term) else {
        return None;
    };
    if eq != "=" || pair.len() != 2 {
        return None;
    }
    for position in 0..2 {
        let variable = pair[position];
        let store = pair[1 - position];
        if !scalar_array_variable(terms, variable) || !live(terms, store) {
            continue;
        }
        let TermData::App(Symbol::Named(name), args) = terms.get(store) else {
            continue;
        };
        if name == "store" && args.len() == 3 && args.iter().all(|&arg| live(terms, arg)) {
            // Complete store typing and the occurs check remain derive's job.
            return Some(Case {
                variable,
                case: GuardedStoreCase {
                    guard,
                    source,
                    store,
                },
                base: args[0],
                key: args[1],
            });
        }
    }
    None
}

fn join(
    cases: &[Case],
    covers: &[Cover],
    progress: Progress<'_>,
) -> Option<Vec<GuardedStoreRequest>> {
    let mut requests: Vec<GuardedStoreRequest> = Vec::new();
    for cover in covers {
        for left in cases {
            if !progress(1, 0) {
                return None;
            }
            if left.case.guard != cover.guards[0] {
                continue;
            }
            for right in cases {
                if !progress(1, 0) {
                    return None;
                }
                if right.case.guard != cover.guards[1]
                    || left.variable != right.variable
                    || left.base != right.base
                    || left.key != right.key
                {
                    continue;
                }
                if !progress(requests.len(), 0) {
                    return None;
                }
                if requests
                    .iter()
                    .any(|request| request.variable == left.variable)
                {
                    continue;
                }
                if !progress(1, 256) {
                    return None;
                }
                requests.push(GuardedStoreRequest {
                    variable: left.variable,
                    cases: [left.case, right.case],
                    cover_source: cover.source,
                    activation: cover.activation,
                });
            }
        }
    }
    Some(requests)
}

/// Only AND edges are traversed: OR alternatives and quantified bodies never
/// become asserted facts. The exact parent/position chain is retained for proof.
fn leaves(terms: &TermStore, root: TermId, progress: Progress<'_>) -> Option<Vec<shape::Path>> {
    if !progress(1, 128) {
        return None;
    }
    let mut nodes: Vec<(TermId, Option<(usize, u32)>)> = vec![(root, None)];
    let mut seen = HashSet::default();
    let mut result = Vec::new();
    let mut cursor = 0;
    while cursor < nodes.len() {
        let term = nodes[cursor].0;
        if !progress(1, 64) || !live(terms, term) || terms.sort(term) != &Sort::Bool {
            return None;
        }
        if !seen.insert(term) {
            cursor += 1;
            continue;
        }
        if let TermData::App(Symbol::Named(name), args) = terms.get(term) {
            if name == "and" {
                if !progress(args.len(), args.len().checked_mul(64)?) {
                    return None;
                }
                for (position, &child) in args.iter().enumerate() {
                    nodes.push((child, Some((cursor, u32::try_from(position).ok()?))));
                }
                cursor += 1;
                continue;
            }
        }
        if !progress(nodes.len(), nodes.len().checked_mul(48)?.checked_add(128)?) {
            return None;
        }
        let mut edges = Vec::new();
        let mut index = cursor;
        while let Some((parent, position)) = nodes[index].1 {
            edges.push((nodes[parent].0, position, nodes[index].0));
            index = parent;
        }
        edges.reverse();
        result.push(shape::Path {
            body: root,
            edges,
            target: term,
        });
        cursor += 1;
    }
    Some(result)
}
