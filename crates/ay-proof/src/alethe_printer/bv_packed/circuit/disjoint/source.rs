// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{Constant, TermStore};

pub(super) fn query(
    source: &TermStore,
    shape: &Shape,
    i: &str,
    j: &str,
) -> Option<(TermStore, TermId)> {
    fn copy(
        source: &TermStore,
        target: &mut TermStore,
        term: TermId,
        memo: &mut DetHashMap<TermId, TermId>,
        nodes: &mut usize,
        depth: usize,
    ) -> Option<TermId> {
        *nodes = nodes.checked_add(1)?;
        if *nodes > 2048 || depth > MAX_DEPTH {
            return None;
        }
        source.entry_stamp(term)?;
        if let Some(&known) = memo.get(&term) {
            return Some(known);
        }
        let sort = source.sort(term).clone();
        let copied = match source.get(term) {
            TermData::Var(name, _) => target.mk_var(name, sort),
            TermData::Const(Constant::Bool(value)) => target.mk_bool(*value),
            TermData::Const(Constant::BitVec { value, width }) => {
                target.mk_bitvec(value.clone(), *width)
            }
            TermData::Not(child) => {
                let child = copy(source, target, *child, memo, nodes, depth + 1)?;
                target.mk_not_raw(child)
            }
            TermData::App(symbol, args) if args.len() <= 128 => {
                let children = args
                    .iter()
                    .map(|&child| copy(source, target, child, memo, nodes, depth + 1))
                    .collect::<Option<Vec<_>>>()?;
                target.mk_app(symbol.clone(), children, sort)
            }
            _ => return None,
        };
        memo.insert(term, copied);
        Some(copied)
    }
    let mut terms = TermStore::new();
    let mut memo = DetHashMap::default();
    let mut nodes = 0;
    let mut copied = Vec::new();
    for term in shape.guards {
        copied.push(copy(source, &mut terms, term, &mut memo, &mut nodes, 0)?);
    }
    let tail = terms.mk_app(Symbol::named("and"), [copied[1], copied[2]], Sort::Bool);
    let guard = terms.mk_app(Symbol::named("and"), [copied[0], tail], Sort::Bool);
    let a = copy(
        source,
        &mut terms,
        shape.spans[0].start,
        &mut memo,
        &mut nodes,
        0,
    )?;
    let b = copy(
        source,
        &mut terms,
        shape.spans[1].start,
        &mut memo,
        &mut nodes,
        0,
    )?;
    let sort = Sort::bitvec(shape.width);
    let i = terms.mk_var(i, sort.clone());
    let j = terms.mk_var(j, sort.clone());
    let la = terms.mk_bitvec(shape.spans[0].length.into(), shape.width);
    let lb = terms.mk_bitvec(shape.spans[1].length.into(), shape.width);
    let ina = terms.mk_app(Symbol::named("bvult"), [i, la], Sort::Bool);
    let inb = terms.mk_app(Symbol::named("bvult"), [j, lb], Sort::Bool);
    let a = terms.mk_app(Symbol::named("bvadd"), [i, a], sort.clone());
    let b = terms.mk_app(Symbol::named("bvadd"), [j, b], sort);
    let eq = terms.mk_app(Symbol::named("="), [a, b], Sort::Bool);
    let query = terms.mk_app(Symbol::named("and"), [guard, ina, inb, eq], Sort::Bool);
    Some((terms, query))
}
