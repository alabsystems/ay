// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Iterative work/depth bounds for direct ground-pin replay.

use super::*;

impl Executor {
    pub(super) fn term_occurs_bounded(
        terms: &TermStore,
        needle: TermId,
        root: TermId,
        remaining: &mut usize,
    ) -> bool {
        let mut seen = ay_core::kani_compat::DetHashSet::default();
        let mut stack = vec![root];
        while let Some(term) = stack.pop() {
            let Some(next) = (*remaining).checked_sub(1) else {
                return false;
            };
            *remaining = next;
            if term == needle {
                return true;
            }
            if !seen.insert(term) {
                continue;
            }
            match terms.get(term) {
                TermData::App(_, args) => {
                    if stack
                        .len()
                        .checked_add(args.len())
                        .is_none_or(|queued| queued > *remaining)
                    {
                        return false;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => {
                    if stack.len() >= *remaining {
                        return false;
                    }
                    stack.push(*inner);
                }
                TermData::Ite(condition, then_term, else_term) => {
                    if stack
                        .len()
                        .checked_add(3)
                        .is_none_or(|queued| queued > *remaining)
                    {
                        return false;
                    }
                    stack.push(*condition);
                    stack.push(*then_term);
                    stack.push(*else_term);
                }
                TermData::Const(_) | TermData::Var(..) => {}
                _ => return false,
            }
        }
        false
    }

    pub(super) fn ground_instance_within_budget(
        terms: &TermStore,
        root: TermId,
        remaining: &mut usize,
    ) -> bool {
        let mut stack = vec![(root, 0_usize)];
        while let Some((term, depth)) = stack.pop() {
            if depth > MAX_INSTANCE_DEPTH {
                return false;
            }
            let Some(next) = (*remaining).checked_sub(1) else {
                return false;
            };
            *remaining = next;
            match terms.get(term) {
                TermData::App(_, args) => {
                    if stack
                        .len()
                        .checked_add(args.len())
                        .is_none_or(|queued| queued > *remaining)
                    {
                        return false;
                    }
                    stack.extend(args.iter().rev().copied().map(|arg| (arg, depth + 1)));
                }
                TermData::Not(inner) => {
                    if stack.len() >= *remaining {
                        return false;
                    }
                    stack.push((*inner, depth + 1));
                }
                TermData::Ite(condition, then_term, else_term) => {
                    if stack
                        .len()
                        .checked_add(3)
                        .is_none_or(|queued| queued > *remaining)
                    {
                        return false;
                    }
                    stack.push((*condition, depth + 1));
                    stack.push((*then_term, depth + 1));
                    stack.push((*else_term, depth + 1));
                }
                TermData::Const(_) | TermData::Var(..) => {}
                _ => return false,
            }
        }
        true
    }
}
