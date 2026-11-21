// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lexical binding excludes local variables; free-variable authority retains
//! exact term entries, never a name-to-sort grouping.

use super::{codec::Control, *};
use ay_core::term::TermData;
use std::collections::BTreeSet;

enum Frame {
    Visit(TermId),
    Body(TermId),
    Restore(usize),
}

pub(super) fn collect(
    executor: &Executor,
    roots: &[TermId],
    control: &mut Control<'_>,
) -> Option<Vec<NativeFreeVariableBinding>> {
    let terms = &executor.ctx.terms;
    control.charge(
        roots.len(),
        roots.len().checked_mul(std::mem::size_of::<Frame>())?,
    )?;
    let mut pending: Vec<_> = roots.iter().rev().copied().map(Frame::Visit).collect();
    let mut bound: Vec<&str> = Vec::new();
    let mut outside_seen = BTreeSet::new();
    let mut free = BTreeSet::new();
    while let Some(frame) = pending.pop() {
        control.charge(1, 0)?;
        let term = match frame {
            Frame::Restore(base) => {
                bound.truncate(base);
                continue;
            }
            Frame::Body(term) => {
                let base = bound.len();
                pending.push(Frame::Restore(base));
                match terms.get(term) {
                    TermData::Let(bindings, body) => {
                        control.charge(
                            bindings.len(),
                            bindings.len().checked_mul(std::mem::size_of::<&str>())?,
                        )?;
                        bound.extend(bindings.iter().map(|(name, _)| name.as_str()));
                        pending.push(Frame::Visit(*body));
                    }
                    TermData::Forall(vars, body, triggers)
                    | TermData::Exists(vars, body, triggers) => {
                        control.charge(
                            vars.len(),
                            vars.len().checked_mul(std::mem::size_of::<&str>())?,
                        )?;
                        bound.extend(vars.iter().map(|(name, _)| name.as_str()));
                        for trigger in triggers.iter().rev() {
                            control.charge(
                                trigger.len(),
                                trigger.len().checked_mul(std::mem::size_of::<Frame>())?,
                            )?;
                            pending.extend(trigger.iter().rev().copied().map(Frame::Visit));
                        }
                        pending.push(Frame::Visit(*body));
                    }
                    _ => return None,
                }
                continue;
            }
            Frame::Visit(term) => term,
        };
        if term.index() >= terms.len() {
            return None;
        }
        if bound.is_empty() && !outside_seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Const(_) => {}
            TermData::Var(name, _) => {
                // A real bound nullary constructor is a declaration member,
                // never a separately invented free constant. Same-spelling
                // variables with another entry retain ordinary free identity.
                if executor
                    .ctx
                    .exact_datatype_member_info(name)
                    .is_some_and(|info| {
                        info.declaration_kind() == ay_frontend::DeclarationKind::DatatypeConstructor
                            && info.arg_sorts.is_empty()
                            && info.term == Some(term)
                            && info.sort == *terms.sort(term)
                    })
                {
                    continue;
                }
                control.charge(bound.len(), 0)?;
                if !bound.iter().any(|binding| *binding == name) {
                    free.insert(term);
                }
            }
            TermData::App(_, args) => {
                control.charge(
                    args.len(),
                    args.len().checked_mul(std::mem::size_of::<Frame>())?,
                )?;
                pending.extend(args.iter().rev().copied().map(Frame::Visit));
            }
            TermData::Not(inner) => pending.push(Frame::Visit(*inner)),
            TermData::Ite(a, b, c) => {
                pending.extend([Frame::Visit(*c), Frame::Visit(*b), Frame::Visit(*a)])
            }
            TermData::Forall(..) | TermData::Exists(..) => pending.push(Frame::Body(term)),
            TermData::Let(bindings, _) => {
                // SMT-LIB lets are simultaneous: RHS occurrences retain the
                // surrounding scope; only the body sees the new bindings.
                control.charge(
                    bindings.len(),
                    bindings.len().checked_mul(std::mem::size_of::<Frame>())?,
                )?;
                pending.push(Frame::Body(term));
                pending.extend(bindings.iter().rev().map(|(_, value)| Frame::Visit(*value)));
            }
            _ => return None,
        }
        if pending.len() > MAX_SOURCE_WORK || bound.len() > MAX_SOURCE_TERMS {
            return None;
        }
    }
    control.charge(
        free.len(),
        free.len()
            .checked_mul(std::mem::size_of::<NativeFreeVariableBinding>())?,
    )?;
    free.into_iter()
        .map(|term| {
            super::codec::validate_sort(terms.sort(term), 32, true, control)?;
            Some(NativeFreeVariableBinding {
                term,
                entry: terms.entry_stamp(term)?,
                sort: terms.sort(term).clone(),
            })
        })
        .collect()
}
