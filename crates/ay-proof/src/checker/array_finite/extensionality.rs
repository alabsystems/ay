// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact finite-carrier array-extensionality recognition.

use std::collections::BTreeSet;

use ay_core::{Sort, Symbol, TermData, TermId, TermStore};

use super::{equality_sides, select_parts, DatatypeContext, DomainPoint, FiniteCarrier};

pub(super) fn matches_finite_extensionality(
    terms: &TermStore,
    clause: &[TermId],
    datatype_context: Option<DatatypeContext<'_>>,
) -> bool {
    let [axiom] = clause else {
        return false;
    };
    let Some((outer_left, outer_right)) = equality_sides(terms, *axiom) else {
        return false;
    };
    for (array_equality, pointwise) in [(outer_left, outer_right), (outer_right, outer_left)] {
        let Some((array_a, array_b, array_sort)) = array_equality_parts(terms, array_equality)
        else {
            continue;
        };
        let Some(carrier) =
            FiniteCarrier::for_sort(terms, &array_sort.index_sort, true, datatype_context)
        else {
            continue;
        };
        let conjuncts: &[TermId] = match terms.get(pointwise) {
            TermData::App(Symbol::Named(name), arguments) if name == "and" => arguments,
            _ if carrier.cardinality() == 1 => std::slice::from_ref(&pointwise),
            _ => continue,
        };
        if conjuncts.len() != carrier.cardinality() {
            continue;
        }

        let mut points = BTreeSet::new();
        let complete = conjuncts.iter().all(|&conjunct| {
            let Some(point) = pointwise_equality_point(
                terms,
                conjunct,
                array_a,
                array_b,
                &array_sort.index_sort,
                &array_sort.element_sort,
                &carrier,
            ) else {
                return false;
            };
            points.insert(point)
        });
        if complete && carrier.is_complete(&points) {
            return true;
        }
    }
    false
}

fn array_equality_parts(
    terms: &TermStore,
    equality: TermId,
) -> Option<(TermId, TermId, ay_core::ArraySort)> {
    let (array_a, array_b) = equality_sides(terms, equality)?;
    if array_a == array_b || terms.sort(array_a) != terms.sort(array_b) {
        return None;
    }
    let Sort::Array(array_sort) = terms.sort(array_a) else {
        return None;
    };
    Some((array_a, array_b, (**array_sort).clone()))
}

fn pointwise_equality_point(
    terms: &TermStore,
    equality: TermId,
    array_a: TermId,
    array_b: TermId,
    index_sort: &Sort,
    element_sort: &Sort,
    carrier: &FiniteCarrier,
) -> Option<DomainPoint> {
    let (left, right) = equality_sides(terms, equality)?;
    let (left_array, left_index) = select_parts(terms, left)?;
    let (right_array, right_index) = select_parts(terms, right)?;
    if left_index != right_index
        || terms.sort(left) != element_sort
        || terms.sort(right) != element_sort
        || !((left_array == array_a && right_array == array_b)
            || (left_array == array_b && right_array == array_a))
    {
        return None;
    }
    carrier.point(terms, index_sort, left_index)
}
