// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native-proof and Alethe-surface boundaries for duplicate authored roots.

use super::*;
use ay_proof::re_check_bundle_strict;

fn duplicate_solver(source_rows: &str) -> (Solver, Vec<Term>) {
    let mut solver = Solver::new(Logic::QfUflia);
    solver.set_produce_proofs(true);
    solver
        .try_set_option(":check-proofs-strict", "true")
        .expect("enable native strict proof checking");
    let parsed = solver
        .parse_smtlib2(&format!(
            r#"
            (declare-fun f (Int) Int)
            (declare-const b Int)
            {source_rows}
            (assert (not (<= 0 (f b))))
            "#
        ))
        .expect("duplicate-root fixture parses");
    assert_eq!(parsed[0].id(), parsed[1].id());
    assert!(solver.check_sat().is_unsat());
    (solver, parsed)
}

fn assert_native_bundle_is_complete(solver: &Solver) {
    assert!(
        solver
            .last_strict_proof_quality()
            .is_some_and(|quality| quality.is_ok_and(|quality| quality.is_complete())),
        "native proof unavailable; recorded decline={:?}",
        solver.executor.last_proof_decline()
    );
    let bundle = solver
        .export_last_unsat_bundle()
        .expect("duplicate roots must retain portable native authority");
    let checked = re_check_bundle_strict(&bundle)
        .expect("duplicate-root bundle must independently recheck offline");
    assert!(checked.quality.is_complete());
    assert!(checked
        .assume_terms
        .iter()
        .all(|term| bundle.obligation_assertions.contains(term)));
}

#[test]
fn canonical_duplicate_row_authenticates_identity_alethe_surface() {
    let (solver, _) = duplicate_solver("(assert (>= (f b) 0))\n(assert (<= 0 (f b)))");
    assert_native_bundle_is_complete(&solver);
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("an exact identity row authenticates canonical Alethe text");
    assert!(matches!(
        artifact.strict_verdict,
        StrictProofVerdict::Verified(ref quality) if quality.is_complete()
    ));
    assert!(artifact
        .alethe
        .lines()
        .any(|line| line.contains("(assume ") && line.contains("(<= 0 (f b))")));
}

#[test]
fn identical_noncanonical_duplicate_rows_share_one_exact_alethe_surface() {
    let (solver, _) = duplicate_solver("(assert (>= (f b) 0))\n(assert (>= (f b) 0))");
    assert_native_bundle_is_complete(&solver);
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("identical source rows justify their common authored spelling");
    assert!(matches!(
        artifact.strict_verdict,
        StrictProofVerdict::Verified(ref quality) if quality.is_complete()
    ));
    assert!(artifact
        .alethe
        .lines()
        .any(|line| line.contains("(assume ") && line.contains("(>= (f b) 0)")));
}

/// Rows that spell one root DIFFERENTLY are each a premise of the problem,
/// and the proof assumes the root once, so the FIRST row's spelling, confined
/// to its own `assume` exactly as a common spelling is, binds as exactly as a
/// common one (pinned Carcara: `group_proofs` duplicate_authored_root). The
/// surface used to be withheld, and `--proof FILE` then lost the verdict
/// (#8821; g06, `(= x (- 2.5))` beside `(= x -2.5)`).
#[test]
fn differing_noncanonical_duplicates_bind_the_first_rows_spelling() {
    let (solver, _) = duplicate_solver("(assert (>= (f b) 0))\n(assert (<= (+ 0 0) (f b)))");
    assert_native_bundle_is_complete(&solver);
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("the first source row binds the duplicate root");
    assert!(matches!(
        artifact.strict_verdict,
        StrictProofVerdict::Verified(ref quality) if quality.is_complete()
    ));
    let assumes: Vec<&str> = artifact
        .alethe
        .lines()
        .filter(|line| line.contains("(assume "))
        .collect();
    assert!(
        assumes.iter().any(|line| line.contains("(>= (f b) 0)")),
        "{assumes:?}"
    );
    assert!(
        !assumes
            .iter()
            .any(|line| line.trim_end().ends_with(" (<= 0 (f b)))") || line.contains("(+ 0 0)")),
        "only the first row's spelling is assumed: {assumes:?}"
    );
}
