//! Integration tests for the diagnostics printed when a `rup` step fails.
//!
//! The fixture is the smallest case where reverse unit propagation legitimately
//! has nothing to work with: an at-most-one over four variables, asked for in a
//! single `rup` step, from the six pairwise at-most-one constraints.
//!
//! Asserting the negation gives `x1+x2+x3+x4 >= 2`, which has slack 2, and each
//! pairwise constraint has slack 1 under the empty assignment. Nothing is unit,
//! so propagation reaches a fixpoint immediately and the trail stays empty.
//!
//! The same constraint *is* derivable by cutting planes, which `amo4_pol.pbp`
//! does, so the fixtures also pin down that the rejection is about the rule used
//! and not about the constraint being false.

use std::process::Command;

const FORMULA: &str = "tests/fixtures/amo4_pairwise.opb";
const RUP_DERIVATION: &str = "tests/fixtures/amo4_single_rup.pbp";
const POL_DERIVATION: &str = "tests/fixtures/amo4_pol.pbp";

/// Run `veripb`, returning `(success, stdout, stderr)`.
fn run(derivation: &str, extra_args: &[&str]) -> (bool, String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_veripb"))
        .args(extra_args)
        .args(["--opb", FORMULA, derivation])
        .output()
        .expect("failed to run veripb binary");
    (
        output.status.success(),
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

#[test]
fn at_most_one_over_four_is_not_rup_derivable() {
    let (ok, _, err) = run(RUP_DERIVATION, &[]);
    assert!(!ok, "expected the single-rup derivation to be rejected");
    assert!(
        err.contains("not implied by reverse unit propagation"),
        "stderr was:\n{err}"
    );
}

#[test]
fn the_same_constraint_is_derivable_by_cutting_planes() {
    let (ok, out, err) = run(POL_DERIVATION, &[]);
    assert!(ok, "expected the pol derivation to verify; stderr:\n{err}");
    assert!(out.contains("s VERIFIED"), "stdout was:\n{out}");
}

#[test]
fn empty_propagation_trail_explains_itself() {
    let (_, out, _) = run(RUP_DERIVATION, &["--trace-failed"]);
    assert!(
        out.contains("no propagations"),
        "an empty trail should say so rather than printing a bare header; stdout was:\n{out}"
    );
    assert!(
        out.contains("pol"),
        "the empty-trail note should point at cutting planes; stdout was:\n{out}"
    );
}

#[test]
fn checking_error_is_reported_exactly_once() {
    let (_, _, err) = run(RUP_DERIVATION, &[]);
    assert_eq!(
        err.matches("Checking error at").count(),
        1,
        "the checking error should appear once, not once per layer of the error chain; \
         stderr was:\n{err}"
    );
    assert_eq!(
        err.matches("not implied by reverse unit propagation")
            .count(),
        1,
        "the underlying cause should appear once; stderr was:\n{err}"
    );
}
