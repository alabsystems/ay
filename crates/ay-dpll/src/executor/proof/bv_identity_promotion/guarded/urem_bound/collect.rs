// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-DAG census only. The independent native theorem checker types the
//! complete operand DAG before a collected occurrence can authorize a proof.

use super::*;
use ay_core::kani_compat::DetHashSet;
use ay_core::TermData;

pub(super) fn occurrences(
    executor: &Executor,
    roots: &[TermId],
    control: &mut Control<'_>,
) -> Option<Vec<(TermId, TermId, u32)>> {
    let work = &executor.proof_source_work;
    control.admit(work, roots.len(), roots.len().checked_mul(4)?)?;
    let mut pending = Vec::new();
    pending.try_reserve(roots.len()).ok()?;
    pending.extend_from_slice(roots);
    let mut seen = DetHashSet::default();
    let mut out = Vec::new();
    while let Some(id) = pending.pop() {
        control.admit(work, 1, 0)?;
        if seen.contains(&id) {
            continue;
        }
        let terms = &executor.ctx.terms;
        terms.entry_stamp(id)?;
        control.admit(work, 1, 64)?;
        seen.try_reserve(1).ok()?;
        seen.insert(id);
        let inline;
        let children = match terms.get(id) {
            TermData::App(symbol, args) => {
                control.admit(work, symbol.name().len().checked_add(args.len())?, 0)?;
                if let (Symbol::Named(name), [x, d], Sort::BitVec(bits)) =
                    (symbol, args.as_slice(), terms.sort(id))
                {
                    if name == "bvurem"
                        && !executor.ctx.has_symbol_binding("bvurem")
                        && (1..=128).contains(&bits.width)
                        && terms.entry_stamp(*x).is_some()
                        && terms.entry_stamp(*d).is_some()
                        && terms.sort(*x) == terms.sort(id)
                        && terms.sort(*d) == terms.sort(id)
                    {
                        control.admit(work, 1, std::mem::size_of::<(TermId, TermId, u32)>())?;
                        out.try_reserve(1).ok()?;
                        out.push((id, *d, bits.width));
                    }
                }
                args.as_slice()
            }
            TermData::Not(arg) => std::slice::from_ref(arg),
            TermData::Ite(c, a, b) => {
                inline = [*c, *a, *b];
                &inline
            }
            TermData::Const(_) | TermData::Var(..) => &[],
            _ => return Some(Vec::new()),
        };
        control.admit(work, children.len(), children.len().checked_mul(4)?)?;
        if children.iter().any(|child| child.index() >= id.index()) {
            return control.refuse();
        }
        pending.try_reserve(children.len()).ok()?;
        pending.extend_from_slice(children);
    }
    drop(pending);
    drop(seen);
    control.admit(work, 0, 0)?;
    Some(out)
}
