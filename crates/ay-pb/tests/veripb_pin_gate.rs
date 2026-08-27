// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The checker PIN, enforced from Rust so `cargo test -p ay-pb` holds it too.
//!
//! Every other checker-backed suite in this workspace ends in "…and VeriPB
//! said VERIFIED". That sentence is only worth something if you can name the
//! checker. These tests name it:
//!
//! * the resolved checker reports the version pinned in `ci/veripb.pin`, and
//! * it REJECTS all twenty-two committed formula/proof pairs on which published
//!   VeriPB 3.0.2 returns a verdict that contradicts the truth. Twenty-two pairs
//!   cover twenty-one defects: defect 7 (normalization wrapping) has two
//!   manifestations whose wrong verdicts point in opposite directions.
//!
//! The second half is the one that matters. A checker with those bugs prints
//! `s VERIFIED UNSATISFIABLE` for satisfiable formulas in two proof lines — so
//! without this gate, every green certified-track run in the workspace could be
//! green against a checker that certifies nothing. `scripts/ci/pb_certified_gate.sh`
//! runs the identical fixtures from the identical manifest; this is the copy
//! that fires when someone runs the tests instead of the CI job.
//!
//! Checker-absent behaviour follows the workspace rule: hard failure unless
//! `AY_VERIPB_OPTIONAL` is set, in which case the skip is announced.

use ay_test_support::veripb::{self, pin};

const SUITE: &str = "veripb_pin_gate";

#[test]
fn resolved_checker_matches_the_pinned_version() {
    let Some(checker) = veripb::require_checker(SUITE) else {
        return;
    };
    if let Err(problem) = pin::check_version(&checker) {
        panic!(
            "{SUITE}: the checker in use is not the pinned one.\n{problem}\n\
             Pinned: veripb {} @ {} + {}",
            pin::version(),
            pin::commit(),
            pin::patch()
        );
    }
}

/// The behavioural half of the pin.
///
/// A version string can be shared by checkers that disagree about what is
/// true; these fixtures cannot. Each is a formula/proof pair whose verdict
/// contradicts reality on an unfixed build, so "rejected" is the only answer a
/// checker AY is willing to certify against may give.
///
/// "Rejected" means: no accepting `s ...` verdict line at any guarantee level.
/// `s VERIFIED NO CONCLUSION` counts as a rejection (nothing was concluded);
/// a parse or checking error with no `s` line counts too. Exit status is not
/// consulted — VeriPB exits 0 on `NO CONCLUSION` and has been observed printing
/// a success line while exiting 1, so neither stream alone is a gate.
#[test]
fn pinned_checker_rejects_every_known_wrong_verdict_fixture() {
    let Some(checker) = veripb::require_checker(SUITE) else {
        return;
    };

    let fixtures = pin::soundness_fixtures();
    assert_eq!(
        fixtures.len(),
        22,
        "twenty-one wrong-verdict defects are pinned across twenty-two fixtures; \
         the manifest lists {}",
        fixtures.len()
    );

    let mut accepted = Vec::new();
    for fixture in &fixtures {
        let run = veripb::run(
            &checker,
            &fixture.formula,
            &fixture.proof,
            // The fixture manifest carries the formula-format flag. One of them
            // is a DIMACS CNF, so the flag must come from the manifest and not
            // from `run`'s `--opb` default — two format flags would leave the
            // choice up to the argument parser.
            &[fixture.flag.as_str()],
        );
        if !run.is_rejected() {
            accepted.push(format!(
                "  - {}: got `{}`, but the truth is {} (an unfixed checker answers `{}` here)",
                fixture.name,
                run.verdict_or_placeholder(),
                fixture.truth,
                fixture.wrong_verdict
            ));
        }
    }

    assert!(
        accepted.is_empty(),
        "{SUITE}: the checker at {} ACCEPTED {} proof(s) that contradict the truth:\n{}\n\
         This binary cannot be used to certify AY's answers. Build the pinned checker \
         (see ci/veripb.pin and ci/veripb-soundness/README.md) instead of moving the pin \
         onto it.",
        checker.display(),
        accepted.len(),
        accepted.join("\n")
    );
}
