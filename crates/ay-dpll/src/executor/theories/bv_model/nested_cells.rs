// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array-valued cells: the default and the stored values of an array whose
//! element sort is itself a BV-indexed array, such as model-checker-consumer's
//! `(Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 8)))` memory.
//!
//! An [`ArrayInterpretation`] holds every cell as model text. A nested cell is
//! the SMT-LIB rendering of the inner array, `((as const <sort>) <default>)`
//! under a `store` chain, which is exactly what the model printer emits and
//! what the independent gate parses back into a structured array
//! (#gate-nested-array-encoding). The element builder had no arm for an
//! array-sorted operand, so every definition of a nested array withheld its
//! variable, e.g. `(= m ((as const ...) ((as const ...) #x2a)))`.
//!
//! An inner array's interpretation is built with the same complete-or-`None`
//! builders as an outer one and rendered as that text. A read of an array of
//! arrays stored whole copies the read cell's text, which the nested select
//! scan (`nested_reads.rs`) provides for an array some read reaches. A free
//! array of arrays without such an entry receives no default here: a default
//! could contradict a read the scan did not resolve. A read of an array of
//! arrays used as a store base, `(store (select m0 k) off v)` (the write of
//! one byte into a row of model-checker-consumer's memory), takes the cell `m0` holds at
//! `k` parsed back from its text (`executor_format/array_cell.rs`), so that
//! definition builds; without it every such definition withheld its
//! variable, and a refused one could never be checked against the reads
//! (`live_definitions.rs`).

use super::*;

impl Executor {
    /// Whether the builders can resolve cells of `sort`: BV, Bool, or a
    /// BV-indexed array of such cells.
    pub(super) fn is_buildable_cell_sort(sort: &Sort) -> bool {
        match sort {
            Sort::BitVec(_) | Sort::Bool => true,
            Sort::Array(inner) => {
                matches!(inner.index_sort, Sort::BitVec(_))
                    && Self::is_buildable_cell_sort(&inner.element_sort)
            }
            _ => false,
        }
    }

    /// The cell an array-sorted operand denotes: a read of an array of arrays
    /// is that array's stored cell; any other operand (a variable resolved
    /// like a store base, a `const-array`, a store chain) is its complete
    /// interpretation, rendered.
    pub(super) fn array_cell_value(
        terms: &TermStore,
        bv_model: &BvModel,
        term: TermId,
        array_model: &mut ArrayModel,
        memo: &mut BvEvalMemo,
    ) -> Option<String> {
        let sort = terms.sort(term);
        if !matches!(sort, Sort::Array(_)) || !Self::is_buildable_cell_sort(sort) {
            return None;
        }
        if let TermData::App(sym, args) = terms.get(term) {
            if sym.name() == "select" && args.len() == 2 {
                return Self::definition_operand_read_value(
                    terms,
                    bv_model,
                    args[0],
                    args[1],
                    array_model,
                    memo,
                );
            }
        }
        let interp = Self::resolve_substitution_target_interp(terms, bv_model, term, array_model)?;
        Self::render_array_cell(sort, &interp)
    }

    /// The interpretation of a read of an array of arrays, `(select m k)`: the
    /// cell `m` holds at `k`, parsed back from its text
    /// (`executor_format/array_cell.rs`), so a store chain whose base is such
    /// a read resolves. `None` when `m` or `k` does not resolve.
    pub(super) fn nested_read_target_interp(
        terms: &TermStore,
        bv_model: &BvModel,
        read: TermId,
        array_model: &mut ArrayModel,
    ) -> Option<ArrayInterpretation> {
        let Sort::Array(sort) = terms.sort(read) else {
            return None;
        };
        if !matches!(sort.index_sort, Sort::BitVec(_)) {
            return None;
        }
        let mut memo = BvEvalMemo::default();
        let cell = Self::array_cell_value(terms, bv_model, read, array_model, &mut memo)?;
        let (default, stores) = crate::executor_format::array_cell::array_cell_parts(&cell)?;
        Some(ArrayInterpretation {
            index_sort: Some(sort.index_sort.clone()),
            element_sort: Some(sort.element_sort.clone()),
            default: Some(default),
            stores,
        })
    }

    /// Render a complete interpretation as model text: the constant array of
    /// its default under its stores, oldest innermost.
    pub(super) fn render_array_cell(sort: &Sort, interp: &ArrayInterpretation) -> Option<String> {
        let default = interp.default.as_deref()?;
        let mut cell = format!(
            "((as const {}) {default})",
            crate::executor_format::format_sort(sort)
        );
        for (index, value) in interp.stores.iter().rev() {
            cell = format!("(store {cell} {index} {value})");
        }
        Some(cell)
    }
}
