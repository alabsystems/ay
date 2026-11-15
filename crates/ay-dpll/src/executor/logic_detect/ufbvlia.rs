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
        // Int `div`/`mod` is out of slice only while a BITVECTOR is still live.
        // The combination this validator fences is BV + arithmetic, and a
        // div/mod residue is fenced because it would reach the conservative
        // BV<->LIA bridge, not because ay cannot decide it: `QF_LIA` and
        // `QF_UFLIA` — two routes this very predicate ADMITS below — decide
        // `mod`/`div` through `mod_div_elim` and publish strict proofs.
        //
        // Excluding it unconditionally made admission NON-MONOTONE in the
        // declared logic name, which is the one thing a logic name must never
        // do: a declared name is an upper bound on the symbols a script may
        // mention, so widening it can lose no verdict. Measured on the ay
        // binary at 6695757a6:
        //
        //   (set-logic QF_LIA)       (assert (= k (mod a 4))) (<= k 3) (>= k 4)  -> unsat
        //   (set-logic QF_UFBVLIA)   ... the same three assertions ...           -> unknown
        //
        // There is no bitvector anywhere in that query. The shape is not
        // exotic: `TermStore::mk_bv2nat` rewrites the masked residue
        // `bv2nat(bvand(int2bv_w(x), 2^k-1))` to `(mod x 2^k)` AT INTERNING
        // TIME, so every power-of-two-mask index obligation Trust's vcgen
        // emits (`let i = a & 3; arr[i]`) arrives here BV-free and carrying a
        // `mod` — and was answered `unknown (incomplete)` for that reason
        // alone.
        //
        // The fence stays exactly where it was for every query that still
        // carries a bitvector.
        || (features.has_int_div_mod && features.has_bv)
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

    /// #ufbvlia-modmonotone. A BV-FREE `mod`/`div` footprint is admitted and
    /// routed to the plain scalar Int lane this predicate already lists.
    ///
    /// The shape is not hypothetical: `TermStore::mk_bv2nat` rewrites
    /// `bv2nat(bvand(int2bv_w(x), 2^k-1))` to `(mod x 2^k)` at interning time,
    /// so a power-of-two-mask index query declared `QF_UFBVLIA` reaches this
    /// predicate with `has_int_div_mod` set and NO bitvector left at all.
    #[test]
    fn bv_free_int_div_mod_is_admitted_to_the_scalar_int_lane() {
        let terms = TermStore::new();
        let cases = [
            (
                StaticFeatures {
                    has_int: true,
                    has_int_var: true,
                    has_int_div_mod: true,
                    num_theories: 1,
                    ..StaticFeatures::default()
                },
                LogicCategory::QfLia,
            ),
            (
                StaticFeatures {
                    has_int: true,
                    has_int_var: true,
                    has_int_div_mod: true,
                    has_uf: true,
                    num_theories: 1,
                    ..StaticFeatures::default()
                },
                LogicCategory::QfUflia,
            ),
        ];
        for (features, expected) in cases {
            assert_eq!(
                validated_route(&features, &terms, None, false),
                Some(expected),
                "a BV-free div/mod footprint has no theory COMBINATION to fence"
            );
        }
    }

    /// The UNSAFE twin of the test above: the moment a bitvector is live the
    /// div/mod residue could reach the conservative BV<->LIA bridge, so the
    /// fence stays exactly where it was. This must keep returning `None`.
    #[test]
    fn int_div_mod_beside_a_live_bitvector_stays_fenced() {
        let terms = TermStore::new();
        let features = StaticFeatures {
            has_int: true,
            has_int_var: true,
            has_bv: true,
            has_int_div_mod: true,
            num_theories: 2,
            ..StaticFeatures::default()
        };
        assert_eq!(
            validated_route(&features, &terms, Some(&[Vec::new()]), false),
            None,
            "BV + div/mod is the combination this validator exists to fence"
        );
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
