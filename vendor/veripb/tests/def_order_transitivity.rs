//! Regression test: a `def_order` block without a `transitivity` sub-block has
//! to be *rejected*, not crash the checker.
//!
//! The `transitivity` block is optional in the grammar, and transitivity of the
//! order is a side condition of the rule that VeriPB cannot autoprove, so
//! `OrderContext::autoprove_transitivity` has to report failure. It used to be
//! `todo!()`, which made the release binary abort (SIGABRT, exit 134, because
//! the release profile sets `panic = "abort"`) with a bare "not yet implemented"
//! and no proof-file location — indistinguishable from a checker bug for any
//! harness that separates "proof rejected" from "checker crashed".

use std::process::Command;

const FORMULA: &str = "tests/instances/incorrect/version3/def_order_without_transitivity.opb";
const DERIVATION: &str = "tests/instances/incorrect/version3/def_order_without_transitivity.pbp";

#[test]
fn def_order_without_transitivity_is_rejected_without_crashing() {
    let output = Command::new(env!("CARGO_BIN_EXE_veripb"))
        .args(["--opb", FORMULA, DERIVATION])
        .output()
        .expect("failed to run veripb binary");

    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let context = format!("--- stdout ---\n{stdout}--- stderr ---\n{stderr}");

    assert_eq!(
        output.status.code(),
        Some(1),
        "the proof should be rejected with the ordinary failure status, not by \
         aborting the process:\n{context}"
    );
    assert!(
        stderr.contains("Transitivity of the order could not be proven"),
        "the rejection should name the side condition that failed:\n{context}"
    );
    assert!(
        !stderr.contains("not yet implemented"),
        "an unimplemented autoprover must not be reported as an internal error:\n{context}"
    );
    assert!(
        !stdout.contains("s VERIFIED"),
        "a rejected proof must not print a verdict:\n{context}"
    );
}
