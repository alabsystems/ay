// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

pub(super) fn read(
    terms: &TermStore,
    roots: &[TermId],
    owner: &CountedAdmission,
) -> Result<Source> {
    let mut state = memory::filled(terms.len(), 0_u8, owner)?;
    let mut kinds = memory::filled(terms.len(), Kind::Value, owner)?;
    let mut order = Vec::new();
    let mut stack = Vec::new();
    for &root in roots {
        owner.admit(1, 0)?;
        if root.index() >= terms.len() || terms.sort(root) != &Sort::Bool {
            return Err(Error::Invalid);
        }
        memory::push(&mut stack, (root, false), owner)?;
        while let Some((id, exit)) = stack.pop() {
            owner.admit(1, 0)?;
            if id.index() >= terms.len() {
                return Err(Error::Invalid);
            }
            if exit {
                kinds[id.index()] = typing::classify(terms, id, owner)?;
                state[id.index()] = 2;
                memory::push(&mut order, id, owner)?;
            } else if state[id.index()] != 2 {
                if state[id.index()] == 1 {
                    return Err(Error::Invalid);
                }
                state[id.index()] = 1;
                memory::push(&mut stack, (id, true), owner)?;
                match terms.get(id) {
                    TermData::App(_, args) => {
                        for &child in args.iter().rev() {
                            memory::push(&mut stack, (child, false), owner)?;
                        }
                    }
                    TermData::Not(child) => memory::push(&mut stack, (*child, false), owner)?,
                    TermData::Ite(c, t, e) => {
                        for child in [*e, *t, *c] {
                            memory::push(&mut stack, (child, false), owner)?;
                        }
                    }
                    TermData::Const(_) | TermData::Var(_, _) => {}
                    _ => return Err(Error::Unsupported),
                }
            }
        }
    }
    drop(state);
    drop(stack);
    owner.check()?;
    Ok(Source { order, kinds })
}
