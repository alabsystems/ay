// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact source reduction for one narrow same-array read disequality.
//!
//! Array congruence gives `i = j => select(A, i) = select(A, j)`, so the exact
//! source root `select(A, i) != select(A, j)` implies `i != j`. Replacing only
//! that root by its necessary consequence weakens the query. A checked
//! refutation of the weakened Bool/BV query therefore proves the source query.

use ay_core::{Sort, Symbol, TermData, TermId, TermStore};

use super::{BvExpr, ProofProducingLowerer};

pub(super) fn lower_same_array_read_disequalities(
    terms: &TermStore,
    roots: &[TermId],
    lowerer: &mut ProofProducingLowerer<'_>,
) -> Result<Option<Vec<BvExpr>>, String> {
    let mut lowered = Vec::new();
    if let Err(error) = lowered.try_reserve_exact(roots.len()) {
        lowerer.resource_exhausted = true;
        return Err(format!("array-congruence root allocation failed: {error}"));
    }
    let mut replaced = false;
    for &root in roots {
        if let Some((left_index, right_index)) = exact_same_array_read_disequality(terms, root) {
            let (left, left_width) = lowerer.lower_bv(left_index)?;
            let (right, right_width) = lowerer.lower_bv(right_index)?;
            if left_width != right_width {
                return Err(format!(
                    "array read indices lower to different widths ({left_width} and {right_width})"
                ));
            }
            lowered.push(BvExpr::not(BvExpr::eq(left, right)));
            replaced = true;
        } else {
            lowered.push(lowerer.lower_bool(root)?);
        }
    }
    Ok(replaced.then_some(lowered))
}

/// Recognize only `not (= (select A i) (select A j))`, where `A` is the same
/// atomic array variable and the complete signature is `Array(BV, U) × BV → U`.
/// The deliberately atomic/scalar restriction keeps malformed native DAGs and
/// recursive sort descriptors outside this source-authority boundary.
fn exact_same_array_read_disequality(terms: &TermStore, root: TermId) -> Option<(TermId, TermId)> {
    term_is_live(terms, root)?;
    if !matches!(terms.sort(root), Sort::Bool) {
        return None;
    }
    let TermData::Not(equality) = terms.get(root) else {
        return None;
    };
    term_is_live(terms, *equality)?;
    if !matches!(terms.sort(*equality), Sort::Bool) {
        return None;
    }
    let TermData::App(Symbol::Named(operator), equality_args) = terms.get(*equality) else {
        return None;
    };
    let [left_read, right_read] = equality_args.as_slice() else {
        return None;
    };
    if operator != "=" {
        return None;
    }
    let (left_array, left_index, left_width) = exact_select_parts(terms, *left_read)?;
    let (right_array, right_index, right_width) = exact_select_parts(terms, *right_read)?;
    (left_array == right_array && left_width == right_width).then_some((left_index, right_index))
}

fn exact_select_parts(terms: &TermStore, term: TermId) -> Option<(TermId, TermId, u32)> {
    term_is_live(terms, term)?;
    let TermData::App(Symbol::Named(operator), args) = terms.get(term) else {
        return None;
    };
    let [array, index] = args.as_slice() else {
        return None;
    };
    if operator != "select" {
        return None;
    }
    term_is_live(terms, *array)?;
    term_is_live(terms, *index)?;
    if !matches!(terms.get(*array), TermData::Var(..)) {
        return None;
    }
    let Sort::Array(array_sort) = terms.sort(*array) else {
        return None;
    };
    let (Sort::BitVec(array_index), Sort::BitVec(index_sort)) =
        (&array_sort.index_sort, terms.sort(*index))
    else {
        return None;
    };
    let (Sort::Uninterpreted(element), Sort::Uninterpreted(result)) =
        (&array_sort.element_sort, terms.sort(term))
    else {
        return None;
    };
    (array_index.width > 0
        && array_index.width == index_sort.width
        && element.len() <= 256
        && element == result)
        .then_some((*array, *index, array_index.width))
}

fn term_is_live(terms: &TermStore, term: TermId) -> Option<()> {
    terms.entry_stamp(term).map(|_| ())
}
