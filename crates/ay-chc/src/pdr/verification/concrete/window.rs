// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The values a concrete check enumerates for each variable: the Int window
//! (centred on [-100, 100], or anchored inside a range wholly beyond it) and
//! the names whose value more than one query variable can read.

use super::ConcreteCheckRange;
use crate::{ChcSort, ChcVar};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

/// Half the width of the window an Int variable's range meets: [-100, 100].
const INT_WINDOW_RADIUS: i64 = 100;

/// How far past its first value one Int window reaches: at most 201 values.
const INT_WINDOW_SPAN: i64 = 2 * INT_WINDOW_RADIUS;

/// The centred clamp (#5539): `lo..=hi` cut to [-100, 100]. It is empty
/// whenever `lo..=hi` misses that window, although the range may hold values.
fn centred_int_window(lo: i64, hi: i64) -> (i64, i64) {
    let lo = lo.max(-INT_WINDOW_RADIUS);
    (
        lo,
        hi.min(INT_WINDOW_RADIUS)
            .min(lo.saturating_add(INT_WINDOW_SPAN)),
    )
}

/// The values `transition_check` enumerates for an Int variable whose
/// extracted bounds are `lo..=hi` (`i64::MIN` or `i64::MAX` on an unbounded
/// side): at most 201 values, every one inside `lo..=hi`.
///
/// A range that meets [-100, 100] keeps the centred clamp's intersection, value
/// for value. A range wholly above that window is checked on its lowest 201
/// values, one wholly below on its highest 201: the values nearest the window.
/// The result is empty exactly when `lo > hi`, bounds that cross, which no
/// value satisfies. Saturating arithmetic keeps the ends of `i64` in range.
pub(super) fn int_check_window(lo: i64, hi: i64) -> (i64, i64) {
    if lo > INT_WINDOW_RADIUS {
        (lo, hi.min(lo.saturating_add(INT_WINDOW_SPAN)))
    } else if hi < -INT_WINDOW_RADIUS {
        (lo.max(hi.saturating_sub(INT_WINDOW_SPAN)), hi)
    } else {
        centred_int_window(lo, hi)
    }
}

/// Each enumerated variable's range: every value of a small BitVec, and for
/// an Int at most 201 values inside the bounds `body` gives it (`-50..=50`
/// when it has none, #5539); and whether an Int range is anchored beyond ±100.
///
/// The assignment is keyed by plain name, and the evaluator's sort-aware
/// lookup (`lookup_model_value`) reads a variable's plain entry, else its
/// `name!<Sort>` entry, else the plain entry whatever it holds. So a query
/// variable of another sort reads an Int variable's value when it shares the
/// Int variable's name (`J:Bool` beside `J:Int`) or when its sort-qualified
/// name is the Int variable's name (`J:Bool` beside an Int named `J!Bool`).
/// For a Bool reader an Int value other than 0 or 1 equals neither `true` nor
/// `false`, which no Bool value does. Such an Int variable keeps the centred
/// clamp, where the old answers stand: an anchored value lies beyond ±100,
/// never 0 or 1, so the new window would add exactly those inexact
/// evaluations.
pub(super) fn check_ranges(
    vars: &[ChcVar],
    all_vars: &[ChcVar],
    bounds: &FxHashMap<String, (i64, i64)>,
) -> (Vec<ConcreteCheckRange>, bool) {
    let read_by_another = names_read_by_two_variables(all_vars);
    let mut anchored = false;
    let ranges = vars
        .iter()
        .map(|v| match &v.sort {
            ChcSort::BitVec(w) => ConcreteCheckRange::BitVec {
                name: v.name.clone(),
                width: *w,
                count: 1u128.checked_shl(*w).unwrap_or(u128::MAX),
            },
            _ => {
                let (lo, hi) = bounds
                    .get(&v.name)
                    .map(|(l, u)| (*l, *u))
                    .unwrap_or((-50, 50));
                let (lo, hi) = if read_by_another.contains(v.name.as_str()) {
                    centred_int_window(lo, hi)
                } else {
                    anchored |= lo > INT_WINDOW_RADIUS || hi < -INT_WINDOW_RADIUS;
                    int_check_window(lo, hi)
                };
                ConcreteCheckRange::Int {
                    name: v.name.clone(),
                    lo,
                    hi,
                }
            }
        })
        .collect();
    (ranges, anchored)
}

/// The assignment keys two distinct query variables can read: a variable reads
/// its plain name and, when that entry is missing or of another sort, its
/// sort-qualified name (`lookup_model_value`).
fn names_read_by_two_variables(all_vars: &[ChcVar]) -> FxHashSet<String> {
    let mut first_reader: FxHashMap<String, &ChcVar> = FxHashMap::default();
    let mut shared = FxHashSet::default();
    for v in all_vars {
        for key in [v.name.clone(), v.sort_qualified_name()] {
            match first_reader.get(&key) {
                Some(reader) if *reader != v => {
                    shared.insert(key);
                }
                Some(_) => {}
                None => {
                    first_reader.insert(key, v);
                }
            }
        }
    }
    shared
}
