// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;

pub(super) fn round(
    terms: &TermStore,
    before: &[TermId],
    after: &[TermId],
    substitution: &VariableSubstitution,
    stamp: u32,
    progress: Progress<'_>,
) -> Option<PropagationRecords> {
    if before.len() != after.len() || !progress(before.len(), 0) {
        return None;
    }
    let mut result = PropagationRecords::default();
    let mut pending = Vec::new();
    for (&before, &after) in before.iter().zip(after) {
        if before == after {
            continue;
        }
        if result.rewrites.len() == MAX_PROPAGATION_RECORDS || !progress(1, 128) {
            return None;
        }
        if !live(terms, before) || !live(terms, after) {
            return None;
        }
        result.rewrites.push(PropagatedRewriteRecord {
            before,
            after,
            stamp,
        });
        pending.push(before);
    }
    if !progress(pending.len(), 0) {
        return None;
    }
    pending.reverse();
    let mut seen = HashSet::default();
    while let Some(term) = pending.pop() {
        if !progress(1, 64) || !live(terms, term) {
            return None;
        }
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Var(_, _) => {
                let Some(&value) = substitution.substitutions().get(&term) else {
                    continue;
                };
                if result.entries.len() == MAX_PROPAGATION_RECORDS || !progress(8, 128) {
                    return None;
                }
                let &source_assertion = substitution.substitution_sources().get(&term)?;
                if !defining_equality(terms, source_assertion, term, value) {
                    return None;
                }
                result.entries.push(PropagatedEntrySource {
                    expr: term,
                    value,
                    source_assertion,
                    stamp,
                });
                pending.push(value);
            }
            TermData::Const(_) => {}
            TermData::App(_, children) => {
                if !progress(children.len(), children.len().checked_mul(8)?) {
                    return None;
                }
                pending.extend(children.iter().rev().copied());
            }
            TermData::Not(child) => {
                if !progress(1, 8) {
                    return None;
                }
                pending.push(*child);
            }
            TermData::Ite(c, t, e) => {
                if !progress(3, 24) {
                    return None;
                }
                pending.extend([*e, *t, *c]);
            }
            // Binding-aware rewriting is not mirrored here. Refuse hints
            // rather than pretend a shadowed occurrence used an outer entry.
            _ => return None,
        }
    }
    progress(0, 0).then_some(result)
}

fn live(terms: &TermStore, term: TermId) -> bool {
    (term.0 as usize) < terms.len()
}

fn defining_equality(terms: &TermStore, source: TermId, variable: TermId, value: TermId) -> bool {
    live(terms, source)
        && live(terms, value)
        && terms.sort(source) == &Sort::Bool
        && matches!(terms.get(source), TermData::App(Symbol::Named(name), args)
            if name == "=" && (args.as_slice() == [variable, value]
                || args.as_slice() == [value, variable]))
}
