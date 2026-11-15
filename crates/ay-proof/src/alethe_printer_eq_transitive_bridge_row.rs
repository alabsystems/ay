// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The read-over-write link of the closed-spelling chain repair.
//!
//! `mk_select` folds `(select (store a i v) i)` to `v` while the problem is
//! elaborated, so an assertion `(= (select (store a i v1) i) v2)` is the
//! internal `(= v1 v2)` printed back in the problem's spelling, and a chain AY
//! derived over `v1` prints with the read in its place:
//!
//! ```text
//! (cl (not (= v1 v2)) (= (select (store a i v1) i) v2))
//! ```
//!
//! Pinned carcara's `arrays_idx` concludes exactly `(= (select (store a i1 e1)
//! i2) e2)` when `i1`/`i2` and `e1`/`e2` parse to one term each
//! (`checker/rules/arrays.rs`, `arrays::idx`), so the missing link is one stock
//! step; a re-spelled element adds its own link and a `trans`. Only the SAME
//! index is admitted: a read at another index needs `arrays_row` and a proved
//! index disequality, which this planner never claims.

use super::{plain_application, plan_equality, Plan};
use crate::alethe_printer::surface_literal::equal_modulo_bitvec_literal_spelling;

/// `arrays_idx` from either side's same-index read over a write to the other
/// side, tried only once `cong` declined, so every link the planner already
/// proved keeps its derivation.
pub(super) fn plan_read_over_write<'a>(
    left: &'a str,
    right: &'a str,
    depth: usize,
    budget: &mut usize,
) -> Option<Plan<'a>> {
    [(left, right), (right, left)]
        .into_iter()
        .find_map(|(read, other)| {
            let element = written_element_read_back(read)?;
            let link = match plan_equality(element, other, depth + 1, budget)? {
                Plan::Same => None,
                plan => Some(Box::new(plan)),
            };
            Some(Plan::ReadOverWrite {
                read,
                element,
                other,
                link,
            })
        })
}

/// `e` of a printed `(select (store a i e) j)` whose `i` and `j` are one term
/// to carcara's parser: the exact premise-free `arrays_idx` shape.
fn written_element_read_back(read: &str) -> Option<&str> {
    let (select, read_args) = plain_application(read)?;
    let [array, read_index] = read_args.as_slice() else {
        return None;
    };
    let (store, store_args) = plain_application(array)?;
    let [_, written_index, element] = store_args.as_slice() else {
        return None;
    };
    (select == "select"
        && store == "store"
        && equal_modulo_bitvec_literal_spelling(written_index, read_index))
    .then_some(*element)
}
