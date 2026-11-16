// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An UNSAT proof over a datatype name spelled `||`, the empty SMT-LIB symbol,
//! exports a bundle that `re_check_bundle_strict` accepts, as its non-empty
//! twin's bundle is accepted.

use crate::api::*;

/// `(name, script with an empty name, non-empty twin)`.
const CASES: &[(&str, &str, &str)] = &[
    (
        "p11_eq_2: constructor ||",
        "(declare-datatypes ((E 0)) (((||) (b))))\n(assert (= || b))",
        "(declare-datatypes ((E 0)) (((a) (b))))\n(assert (= a b))",
    ),
    (
        "r1: selector ||",
        "(declare-datatypes ((P 0)) (((mk (|| Int)) (nil))))\n\
         (declare-const p P)\n(declare-const q P)\n\
         (assert (= p q))\n(assert (not (= (|| p) (|| q))))",
        "(declare-datatypes ((P 0)) (((mk (sx Int)) (nil))))\n\
         (declare-const p P)\n(declare-const q P)\n\
         (assert (= p q))\n(assert (not (= (sx p) (sx q))))",
    ),
    (
        "r5: datatype sort ||",
        "(declare-datatypes ((|| 0)) (((a) (b))))\n(declare-const v ||)\n\
         (assert (= v a))\n(assert (= v b))",
        "(declare-datatypes ((D 0)) (((a) (b))))\n(declare-const v D)\n\
         (assert (= v a))\n(assert (= v b))",
    ),
];

fn declares_an_empty_name(bundle: &SerializableProofBundle) -> bool {
    bundle
        .datatype_declarations
        .iter()
        .any(|(datatype, constructors)| {
            datatype.is_empty() || constructors.iter().any(String::is_empty)
        })
        || bundle
            .constructor_selectors
            .iter()
            .any(|(_, selectors)| selectors.iter().any(String::is_empty))
}

#[test]
fn empty_name_bundles_recheck_offline_like_their_twins() {
    for &(label, empty, twin) in CASES {
        for (side, script) in [("twin", twin), ("empty", empty)] {
            let mut solver = Solver::try_new(Logic::All).expect("solver");
            solver.set_produce_proofs(true);
            solver
                .parse_smtlib2(script)
                .unwrap_or_else(|error| panic!("{label} {side}: {error}"));
            assert!(solver.check_sat().is_unsat(), "{label} {side}");
            let bundle = solver
                .export_last_unsat_bundle()
                .unwrap_or_else(|| panic!("{label} {side}: no bundle"));
            assert_eq!(
                declares_an_empty_name(&bundle),
                side == "empty",
                "{label} {side}"
            );
            let checked = re_check_bundle_strict(&bundle)
                .unwrap_or_else(|error| panic!("{label} {side}: {error:?}"));
            assert!(checked.quality.is_complete(), "{label} {side}");
        }
    }
}
