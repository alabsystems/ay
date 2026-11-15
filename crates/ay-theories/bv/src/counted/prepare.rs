// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn encode(encoder: &mut CountedBvEncoder<'_>, roots: &[TermId]) -> Result<()> {
    encoder.owner.admit(1, 0)?;
    let mut pending = Vec::new();
    let mut states = HashMap::default();
    let mut order = Vec::new();
    let retained_control = Arc::clone(&encoder.solver.encoding);
    let control = &retained_control;
    if !memory::reserve(&mut pending, roots.len(), control) {
        return stopped(encoder);
    }
    encoder.owner.admit(roots.len(), 0)?;
    pending.extend(roots.iter().rev().map(|&root| (root, false)));
    while let Some((term, done)) = pending.pop() {
        encoder.owner.admit(2, 0)?;
        if encoder.prepared.contains(&term) {
            continue;
        }
        if done {
            typing::validate(encoder.solver.terms, term, &encoder.owner)?;
            if !memory::reserve(&mut order, 1, control) {
                return stopped(encoder);
            }
            order.push(term);
            states.insert(term, true);
            continue;
        }
        match states.get(&term) {
            Some(true) => continue,
            Some(false) => return Err(CountedBvError::Invalid),
            None => {}
        }
        if term.index() >= encoder.solver.terms.len() {
            return Err(CountedBvError::Invalid);
        }
        if !memory::map(&mut states, control) || !memory::reserve(&mut pending, 4, control) {
            return stopped(encoder);
        }
        states.insert(term, false);
        pending.push((term, true));
        match encoder.solver.terms.get(term) {
            TermData::App(_, args) => {
                if !memory::reserve(&mut pending, args.len(), control) {
                    return stopped(encoder);
                }
                encoder.owner.admit(args.len(), 0)?;
                pending.extend(args.iter().rev().map(|&child| (child, false)));
            }
            TermData::Not(child) => pending.push((*child, false)),
            TermData::Ite(c, t, e) => pending.extend([(*e, false), (*t, false), (*c, false)]),
            TermData::Const(_) | TermData::Var(_, _) => {}
            _ => return Err(CountedBvError::Unsupported("unaccounted term form")),
        }
    }
    drop(pending);
    drop(states);
    encoder.check()?;
    for term in order {
        encoder.owner.admit(1, 0)?;
        match encoder.solver.terms.sort(term) {
            Sort::Bool => {
                encoder.solver.bitblast_bool(term);
            }
            Sort::BitVec(_) => {
                encoder.solver.get_bits(term);
            }
            _ => return Err(CountedBvError::Unsupported("non-scalar source")),
        }
        encoder.check()?;
        if !memory::set(&mut encoder.prepared, control) {
            return stopped(encoder);
        }
        encoder.prepared.insert(term);
    }
    encoder.check()
}

fn stopped<T>(encoder: &CountedBvEncoder<'_>) -> Result<T> {
    encoder.owner.check()?;
    Err(CountedBvError::Invalid)
}
