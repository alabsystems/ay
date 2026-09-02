// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Content-validated routing for the array-free `QF_UFBVLIA` slice.

use ay_core::kani_compat::DetHashSet;
use ay_core::{TermId, TermStore};

use crate::features::StaticFeatures;
use crate::logic_detection::LogicCategory;

/// Split only positive top-level conjunctions into their asserted leaves.
///
/// `(assert (and a b))` is semantically the same assertion window as two
/// authored roots `a` and `b`. The independence audit must use that canonical
/// shape too, especially on the direct `check-sat-assuming` path which runs
/// before the ordinary `FlattenAnd` preprocessing pass. Nested Boolean
/// structure below any other operator remains whole and therefore fail-closed
/// when it couples BV and Int.
pub(super) fn flatten_positive_top_level_conjunctions(
    terms: &TermStore,
    assertions: &[TermId],
) -> Vec<TermId> {
    let mut flattened = Vec::with_capacity(assertions.len());
    let mut stack = Vec::new();
    let mut visited_conjunctions = DetHashSet::default();
    for &assertion in assertions.iter().rev() {
        stack.push(assertion);
    }
    while let Some(term) = stack.pop() {
        match terms.get(term) {
            ay_core::term::TermData::App(symbol, args)
                if symbol.name() == "and" && args.len() >= 2 =>
            {
                if !visited_conjunctions.insert(term) {
                    continue;
                }
                for &arg in args.iter().rev() {
                    stack.push(arg);
                }
            }
            _ => flattened.push(term),
        }
    }
    flattened
}

/// Return the existing sound solver route for a declared `QF_UFBVLIA` query,
/// or `None` when its live footprint exceeds the first supported slice.
///
/// This is deliberately a closed admission predicate. The public logic name
/// is an upper bound, but it is not authority to silently erase a component
/// theory. The admitted slice contains only Bool, uninterpreted carriers/UF,
/// BitVec, and linear Int. BV/Int conversions use the existing conservative
/// bridge; independent BV and Int use the existing two-lane solver. Both
/// routes retain their normal proof and model-validation chokepoints.
pub(super) fn validated_route(
    features: &StaticFeatures,
    terms: &TermStore,
    symbol_components: Option<&[Vec<TermId>]>,
    has_datatype_term: bool,
) -> Option<LogicCategory> {
    let outside_slice = has_datatype_term
        || features.has_arrays
        || features.has_nested_arrays
        || features.has_real
        || features.has_strings
        || features.has_seq
        || features.has_seq_ops
        || features.has_set_ops
        || features.has_multiset_ops
        || features.has_map_ops
        || features.has_regex
        || features.has_fpa
        || features.has_rounding_mode
        || features.has_quantifiers
        || features.has_nonlinear_int
        || features.has_nonlinear_real
        || features.has_int_div_mod
        || features.has_is_int_real;
    if outside_slice {
        return None;
    }

    let mut route = LogicCategory::from_logic(features.infer_logic());
    // The sequential BV/AUFLIA lane is an independence procedure, not a
    // general combination engine. Audit every connected component whenever
    // both theories are live, including conversion-bearing `QfBvLia`: a
    // conversion marker must not let a direct or transitive mixed-theory UF
    // bypass this boundary. Roots joined by a shared free variable or exact
    // non-builtin symbol identity belong to one component.
    //
    // A mixed BV+Int component with no live UF is propositional coupling, not
    // independence, so route it through the conservative source-checked
    // bridge. Any UF inside such a component remains outside this first
    // combination slice. Failure to construct the partition is fail-closed.
    if matches!(route, LogicCategory::QfBvLia | LogicCategory::QfBvLiaIndep) {
        let components = symbol_components?;
        let mut bridge_required = route == LogicCategory::QfBvLia;
        for component in components {
            let component_features = StaticFeatures::collect(terms, component);
            if component_features.has_bv && component_features.has_int {
                if component_features.has_uf {
                    return None;
                }
                bridge_required = true;
            }
        }
        if bridge_required {
            route = LogicCategory::QfBvLia;
        }
    }

    matches!(
        route,
        LogicCategory::Propositional
            | LogicCategory::QfUf
            | LogicCategory::QfLia
            | LogicCategory::QfUflia
            | LogicCategory::QfBv
            | LogicCategory::QfUfbv
            | LogicCategory::QfBvLia
            | LogicCategory::QfBvLiaIndep
    )
    .then_some(route)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn selects_existing_scalar_routes() {
        let cases = [
            (
                StaticFeatures {
                    has_int: true,
                    has_int_var: true,
                    has_uf: true,
                    num_theories: 1,
                    ..StaticFeatures::default()
                },
                LogicCategory::QfUflia,
            ),
            (
                StaticFeatures {
                    has_bv: true,
                    has_uf: true,
                    num_theories: 1,
                    ..StaticFeatures::default()
                },
                LogicCategory::QfUfbv,
            ),
            (
                StaticFeatures {
                    has_int: true,
                    has_int_var: true,
                    has_bv: true,
                    has_uf: true,
                    num_theories: 2,
                    ..StaticFeatures::default()
                },
                LogicCategory::QfBvLiaIndep,
            ),
            (
                StaticFeatures {
                    has_int: true,
                    has_int_var: true,
                    has_bv: true,
                    has_uf: true,
                    has_bv_int_conversion: true,
                    num_theories: 2,
                    ..StaticFeatures::default()
                },
                LogicCategory::QfBvLia,
            ),
        ];

        for (features, expected) in cases {
            let terms = TermStore::new();
            let components = [Vec::new()];
            assert_eq!(
                validated_route(&features, &terms, Some(&components), false),
                Some(expected)
            );
        }
    }

    #[test]
    fn rejects_every_out_of_slice_feature_class() {
        let base = StaticFeatures {
            has_int: true,
            has_int_var: true,
            has_bv: true,
            has_uf: true,
            num_theories: 2,
            ..StaticFeatures::default()
        };

        let terms = TermStore::new();
        assert_eq!(validated_route(&base, &terms, None, true), None, "datatype");

        let mutations: &[(&str, fn(&mut StaticFeatures))] = &[
            ("array", |f| f.has_arrays = true),
            ("nested-array", |f| f.has_nested_arrays = true),
            ("real", |f| f.has_real = true),
            ("string", |f| f.has_strings = true),
            ("sequence", |f| f.has_seq = true),
            ("sequence-op", |f| f.has_seq_ops = true),
            ("set", |f| f.has_set_ops = true),
            ("multiset", |f| f.has_multiset_ops = true),
            ("map", |f| f.has_map_ops = true),
            ("regex", |f| f.has_regex = true),
            ("floating-point", |f| f.has_fpa = true),
            ("rounding-mode", |f| f.has_rounding_mode = true),
            ("quantifier", |f| f.has_quantifiers = true),
            ("nonlinear-int", |f| f.has_nonlinear_int = true),
            ("nonlinear-real", |f| f.has_nonlinear_real = true),
            ("int-div-mod", |f| f.has_int_div_mod = true),
            ("is-int-real", |f| f.has_is_int_real = true),
        ];
        for (name, mutate) in mutations {
            let mut features = base.clone();
            mutate(&mut features);
            assert_eq!(
                validated_route(&features, &terms, None, false),
                None,
                "{name}"
            );
        }
    }
}
