// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded occurs check for authored arithmetic definitions.

use ay_core::{TermData, TermId, TermStore};

pub(super) fn contains_term_bounded(terms: &TermStore, root: TermId, needle: TermId) -> bool {
    const MAX_VISITS: usize = 4_096;

    let mut stack = vec![root];
    let mut visits = 0usize;
    while let Some(term) = stack.pop() {
        if term == needle {
            return true;
        }
        visits += 1;
        if visits > MAX_VISITS {
            return true;
        }
        let remaining = MAX_VISITS.saturating_sub(visits.saturating_add(stack.len()));
        match terms.get(term) {
            TermData::Const(_) | TermData::Var(..) => {}
            TermData::App(_, args) => {
                if args.len() > remaining {
                    return true;
                }
                stack.extend(args.iter().copied());
            }
            TermData::Let(bindings, body) => {
                let Some(child_count) = bindings.len().checked_add(1) else {
                    return true;
                };
                if child_count > remaining {
                    return true;
                }
                stack.extend(bindings.iter().map(|(_, value)| *value));
                stack.push(*body);
            }
            TermData::Not(inner)
            | TermData::Forall(_, inner, _)
            | TermData::Exists(_, inner, _) => {
                if remaining == 0 {
                    return true;
                }
                stack.push(*inner);
            }
            TermData::Ite(condition, then_term, else_term) => {
                if remaining < 3 {
                    return true;
                }
                stack.extend([*condition, *then_term, *else_term]);
            }
            _ => return true,
        }
    }
    false
}
