// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 2 gate for #8717: bail out of algebraic invariant synthesis when
//! any transition variable has a bitvector sort.
//!
//! # Why
//!
//! The algebraic invariant synthesizer in `super` normalizes a self-looping
//! Horn clause into a polynomial recurrence (over `Int`) and derives a
//! closed form by eliminating the iteration count. This strategy is
//! correct for Int / Real arithmetic but **algorithmically wrong** for
//! bitvectors: `bvshl`, `bvor`, `bvudiv`, `bvlshr` (and friends) do not
//! admit Integer polynomial closed forms, and the synthesizer would
//! produce a degenerate expression like `x_next = x * 2^k` interpreted
//! over Integers, which is neither implied by nor consistent with BV
//! semantics modulo `2^N`.
//!
//! When that happens the downstream SMT solver either spins refuting the
//! invalid recurrence or explores an exponentially large state space.
//! Z3 issue #1634 and Z3 issue #2119 track the mixed BV+Int Horn class
//! this fix unblocks.
//!
//! This gate is the Phase 2 step from
//! the development design notes. Phase 3 will port Z3 Spacer's
//! BV MBP (`reference/z3/src/qe/qe_bv_plugin.cpp`) to handle the mixed
//! case positively.
//!
//! # What this function does NOT do
//!
//! It does NOT prove safety or unsafety of BV-bearing transitions; it
//! simply stops the algebraic synthesizer from wasting time on the wrong
//! algorithm so that the remaining portfolio engines (PDR / IC3 /
//! interpolation) can take over.

use crate::ChcSort;
use ay_core::kani_compat::DetHashMap as FxHashMap;

/// Returns `true` when any variable in `var_sorts` has a bitvector sort.
///
/// The map is the `NormalizedSelfLoop::var_sorts` populated in
/// `extract_normalized_self_loop`: every pre-state and post-state variable
/// that appeared directly in the head or body of the self-loop predicate,
/// keyed by its real declared sort. A `ChcSort::BitVec(_)` match anywhere
/// in the map means the transition relation is BV-flavored and the
/// algebraic synthesizer should not be invoked.
///
/// Note: nested sorts (e.g., `ChcSort::Array(BitVec, BitVec)`) are also
/// flagged as BV-bearing — the current synthesizer cannot reason about
/// those either.
pub(super) fn has_bv_variables(var_sorts: &FxHashMap<String, ChcSort>) -> bool {
    var_sorts.values().any(sort_contains_bv)
}

fn sort_contains_bv(sort: &ChcSort) -> bool {
    match sort {
        ChcSort::BitVec(_) => true,
        ChcSort::Array(key, value) => sort_contains_bv(key) || sort_contains_bv(value),
        // Datatype fields cannot currently be introspected from the sort alone —
        // the algebraic synthesizer bails out on Datatype transitions via the
        // extraction path, so we do not need to recurse here.
        ChcSort::Bool
        | ChcSort::Int
        | ChcSort::Real
        | ChcSort::Uninterpreted(_)
        | ChcSort::Datatype { .. } => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sorts(entries: &[(&str, ChcSort)]) -> FxHashMap<String, ChcSort> {
        let mut map = FxHashMap::default();
        for (name, sort) in entries {
            map.insert((*name).to_string(), sort.clone());
        }
        map
    }

    #[test]
    fn test_has_bv_variables_pure_int_is_false() {
        let map = sorts(&[("x", ChcSort::Int), ("i", ChcSort::Int)]);
        assert!(!has_bv_variables(&map));
    }

    #[test]
    fn test_has_bv_variables_pure_real_is_false() {
        let map = sorts(&[("x", ChcSort::Real)]);
        assert!(!has_bv_variables(&map));
    }

    #[test]
    fn test_has_bv_variables_pure_bv_is_true() {
        let map = sorts(&[("x", ChcSort::BitVec(32))]);
        assert!(has_bv_variables(&map));
    }

    #[test]
    fn test_has_bv_variables_mixed_bv_int_is_true() {
        // Z3 #1634 shape: BV state + Int counter.
        let map = sorts(&[("x", ChcSort::BitVec(32)), ("i", ChcSort::Int)]);
        assert!(has_bv_variables(&map));
    }

    #[test]
    fn test_has_bv_variables_bv_array_is_true() {
        let map = sorts(&[(
            "mem",
            ChcSort::Array(Box::new(ChcSort::BitVec(8)), Box::new(ChcSort::BitVec(8))),
        )]);
        assert!(has_bv_variables(&map));
    }

    #[test]
    fn test_has_bv_variables_int_array_is_false() {
        let map = sorts(&[(
            "mem",
            ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
        )]);
        assert!(!has_bv_variables(&map));
    }

    #[test]
    fn test_has_bv_variables_empty_is_false() {
        let map = sorts(&[]);
        assert!(!has_bv_variables(&map));
    }
}
