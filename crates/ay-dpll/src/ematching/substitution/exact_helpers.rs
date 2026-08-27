// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{HashSet, TermData, TermId, TermStore};

const WORK_LIMIT: usize = 100_000;

pub(super) fn nested_binder_names(
    terms: &TermStore,
    root: TermId,
    work: &mut usize,
) -> Option<HashSet<String>> {
    let mut names = HashSet::default();
    let mut seen = HashSet::default();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if *work >= WORK_LIMIT {
            return None;
        }
        *work += 1;
        match terms.get(term) {
            TermData::Forall(bindings, body, triggers)
            | TermData::Exists(bindings, body, triggers) => {
                names.extend(bindings.iter().map(|(name, _)| name.clone()));
                stack.push(*body);
                stack.extend(triggers.iter().flatten().copied());
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_branch, else_branch) => {
                stack.extend([*condition, *then_branch, *else_branch]);
            }
            TermData::Let(..) => return None,
            TermData::Var(..) | TermData::Const(..) => {}
            // An unknown future `TermData` variant could carry a binder
            // this scan would then miss. An empty result now AUTHORIZES
            // replacements spelled like a source binder, so silently
            // skipping an unrecognized node is no longer safe: fail closed.
            _ => return None,
        }
    }
    Some(names)
}

pub(super) fn replacement_avoids_nested_names(
    terms: &TermStore,
    root: TermId,
    nested_names: &HashSet<String>,
    work: &mut usize,
) -> Option<bool> {
    let mut seen = HashSet::default();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if *work >= WORK_LIMIT {
            return None;
        }
        *work += 1;
        match terms.get(term) {
            TermData::Var(name, _) if nested_names.contains(name) => return Some(false),
            TermData::Var(..) | TermData::Const(..) => {}
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_branch, else_branch) => {
                stack.extend([*condition, *then_branch, *else_branch]);
            }
            TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => {
                return Some(false);
            }
            _ => return Some(false),
        }
    }
    Some(true)
}
