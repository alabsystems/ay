// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Expanded traversal and borrowed byte preflight, before the native checker
/// or either formatter can copy large literals, indices, aliases, or caches.
pub(super) fn bounded_clause(printer: &AlethePrinter<'_>, clause: &[TermId]) -> Option<u64> {
    if !(3..=MAX_PINS + 2).contains(&clause.len()) {
        return None;
    }
    let terms = printer.terms;
    let mut pending: Vec<_> = clause.iter().map(|&t| (t, 0usize)).collect();
    let mut remaining = MAX_NODES;
    let mut bytes = 0u64;
    while let Some((term, depth)) = pending.pop() {
        remaining = remaining.checked_sub(1)?;
        if depth > MAX_DEPTH {
            return None;
        }
        terms.entry_stamp(term)?;
        bytes = bytes.checked_add(own_text_bound(terms.get(term))?)?;
        // Checking every channel is conservative when one shadows another.
        // No source map is cloned, and unrelated entries are never scanned.
        for text in [
            printer.skolem_overrides.borrow().get(&term),
            printer.let_bridge_renderings.borrow().get(&term),
            printer.term_overrides.and_then(|m| m.get(&term)),
            printer.format_cache.borrow().get(&term),
        ]
        .into_iter()
        .flatten()
        {
            bytes = bytes.checked_add(text.len() as u64)?;
        }
        if bytes > MAX_INPUT as u64 {
            return None;
        }
        match terms.get(term) {
            TermData::App(_, args) => {
                if args.len() > remaining {
                    return None;
                }
                pending.extend(args.iter().map(|&a| (a, depth + 1)));
            }
            TermData::Not(t) => pending.push((*t, depth + 1)),
            TermData::Ite(c, t, e) => pending.extend([*c, *t, *e].map(|a| (a, depth + 1))),
            TermData::Const(_) | TermData::Var(..) => {}
            _ => return None,
        }
    }
    if !clause.iter().all(|&t| terms.sort(t) == &Sort::Bool) {
        return None;
    }
    // A descendant's text may be copied at every enclosing depth, in both
    // canonical and effective rendering. All arithmetic is checked.
    bytes.checked_mul(2 * (MAX_DEPTH as u64 + 1))
}

fn own_text_bound(term: &TermData) -> Option<u64> {
    let payload = match term {
        TermData::Const(Constant::Bool(_)) => 5,
        TermData::Const(Constant::Int(value)) => value.bits(),
        TermData::Const(Constant::Rational(value)) => {
            value.0.numer().bits().checked_add(value.0.denom().bits())?
        }
        TermData::Const(Constant::BitVec { value, width }) => value.bits().max(u64::from(*width)),
        TermData::Const(Constant::String(value)) => (value.len() as u64).checked_mul(10)?,
        TermData::Var(name, _) => (name.len() as u64).checked_mul(2)?,
        TermData::App(symbol, args) => {
            // Constant-array rendering embeds a recursively printed sort;
            // this first bounded domain excludes that additional syntax.
            if symbol.name() == "const-array" {
                return None;
            }
            let indices = match symbol {
                Symbol::Named(_) => 0,
                Symbol::Indexed(_, indices) => (indices.len() as u64).checked_mul(11)?,
                _ => return None,
            };
            (symbol.name().len() as u64)
                .checked_mul(2)?
                .checked_add(indices)?
                .checked_add(args.len() as u64)?
        }
        TermData::Not(_) | TermData::Ite(..) => 0,
        _ => return None,
    };
    payload.checked_add(32)
}
