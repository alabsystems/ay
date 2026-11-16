// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bound repeated source edges before rendering or allocating circuit terms.

use super::*;
use ay_core::Constant;

pub(super) fn preflight(printer: &AlethePrinter<'_>, root: TermId) -> Option<()> {
    fn visit(
        printer: &AlethePrinter<'_>,
        term: TermId,
        nodes: &mut usize,
        names: &mut usize,
        depth: usize,
    ) -> Option<()> {
        printer.charge(1);
        *nodes = nodes.checked_add(1)?;
        // Count repeated source edges too. A 48-byte calling frame expands
        // its store chain at every read (15,725 nodes, depth 70). This source
        // bound is separate from the unchanged proof-construction depth cap.
        if *nodes > 16_384 || depth > 96 || printer.work_budget_exhausted() {
            return None;
        }
        printer.terms.entry_stamp(term)?;
        match printer.terms.sort(term) {
            Sort::Bool => (),
            Sort::BitVec(sort) if sort.width > 0 && sort.width <= MAX_WIDTH as u32 => (),
            Sort::Array(shape) if matches!((&shape.index_sort, &shape.element_sort), (Sort::BitVec(i), Sort::BitVec(v)) if i.width > 0 && i.width <= MAX_WIDTH as u32 && v.width > 0 && v.width <= MAX_WIDTH as u32) =>
                {}
            _ => return None,
        }
        match printer.terms.get(term) {
            TermData::Var(name, _) => {
                *names = names.checked_add(name.len())?;
                printer.charge(name.len() as u64);
                (*names <= MAX_TEXT / 4 && !printer.work_budget_exhausted()).then_some(())
            }
            TermData::Const(Constant::Bool(_) | Constant::BitVec { .. }) => Some(()),
            TermData::Not(child) => visit(printer, *child, nodes, names, depth + 1),
            TermData::Ite(c, y, n) => {
                for child in [c, y, n] {
                    visit(printer, *child, nodes, names, depth + 1)?;
                }
                Some(())
            }
            TermData::App(Symbol::Named(op), args)
                if matches!(
                    op.as_str(),
                    "ite"
                        | "and"
                        | "or"
                        | "xor"
                        | "not"
                        | "="
                        | "distinct"
                        | "bvadd"
                        | "bvsub"
                        | "bvneg"
                        | "bvnot"
                        | "bvmul"
                        | "bvult"
                        | "bvule"
                        | "bvugt"
                        | "bvuge"
                        | "bvslt"
                        | "bvsle"
                        | "bvsgt"
                        | "bvsge"
                        | "select"
                        | "store"
                        | "const-array"
                        | "concat"
                        | "bvor"
                        | "bvand"
                        | "bvxor"
                        | "bvshl"
                        | "bvlshr"
                        | "bvashr"
                ) && args.len() <= 128 =>
            {
                for &child in args {
                    visit(printer, child, nodes, names, depth + 1)?;
                }
                Some(())
            }
            TermData::App(Symbol::Indexed(op, _), args)
                if matches!(op.as_str(), "extract" | "zero_extend" | "sign_extend")
                    && args.len() == 1 =>
            {
                visit(printer, args[0], nodes, names, depth + 1)
            }
            _ => None,
        }
    }
    visit(printer, root, &mut 0, &mut 0, 0)
}
