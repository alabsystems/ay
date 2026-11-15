// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{Constant, TermStore};

pub(super) fn query(
    printer: &AlethePrinter<'_>,
    shape: &OutsideFrameShape,
    offset: &str,
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
    for term in [shape.guard, shape.outside, shape.start, shape.observe] {
        let value = copy(printer.terms, &mut terms, term, &mut memo, &mut nodes, 0)?;
        // The independent scalar lemma must retain the source printer's exact
        // effective spelling, including any caller-provided overrides.
        if AlethePrinter::new(&terms).format_term(value) != printer.format_term(term) {
            return None;
        }
        copied.push(value);
    }
    let sort = Sort::bitvec(shape.width);
    let offset = terms.mk_var(offset, sort.clone());
    let length = terms.mk_bitvec(shape.length.into(), shape.width);
    let within = terms.mk_app(Symbol::named("bvult"), [offset, length], Sort::Bool);
    let address = terms.mk_app(Symbol::named("bvadd"), [copied[2], offset], sort);
    let equal = terms.mk_app(Symbol::named("="), [copied[3], address], Sort::Bool);
    let query = terms.mk_app(
        Symbol::named("and"),
        [copied[0], copied[1], within, equal],
        Sort::Bool,
    );
    Some((terms, query))
}
