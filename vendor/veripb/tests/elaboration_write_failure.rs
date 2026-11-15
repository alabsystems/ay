//! Regression test: `--elaborate` must not report success when the elaborated
//! proof could not be written to disk.
//!
//! `Elaborator` wraps the output file in a `BufWriter`, which flushes when it is
//! dropped and throws any error away by design. A whole elaborated proof that
//! fits in the 8 KiB buffer therefore used to disappear without a trace: VeriPB
//! printed `s VERIFIED ...` on stdout, exited 0, and left a 0-byte kernel proof
//! behind for the next tool in the pipeline.
//!
//! The write failure is provoked with a zero file-size limit (`RLIMIT_FSIZE`),
//! which makes every write to the elaborated proof fail with `EFBIG` while
//! leaving pipes and the input files alone. `SIGXFSZ` has to be ignored so that
//! the failure surfaces as an error return instead of killing the process, and
//! an ignored disposition is what a child inherits across `exec`.

#![cfg(unix)]

use std::path::Path;
use std::process::Command;

const FORMULA: &str = "tests/fixtures/amo4_pairwise.opb";
const DERIVATION: &str = "tests/fixtures/amo4_pol.pbp";

#[test]
fn elaboration_write_failure_is_not_reported_as_success() {
    let dir = tempfile::tempdir().expect("failed to create temporary directory");
    let kernel_proof = dir.path().join("kernel.pbp");

    let output = Command::new("/bin/sh")
        .arg("-c")
        .arg(format!(
            "trap '' XFSZ; ulimit -f 0; exec {veripb} --opb {formula} {derivation} --elaborate {kernel}",
            veripb = shell_quote(env!("CARGO_BIN_EXE_veripb")),
            formula = shell_quote(FORMULA),
            derivation = shell_quote(DERIVATION),
            kernel = shell_quote(kernel_proof.to_str().unwrap()),
        ))
        .output()
        .expect("failed to run veripb binary");

    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let context = format!("--- stdout ---\n{stdout}--- stderr ---\n{stderr}");

    // The elaborated proof is what was asked for, and it is not there.
    let written = std::fs::read(&kernel_proof).unwrap_or_default();
    assert!(
        written.is_empty(),
        "the file-size limit did not take effect, so this test proves nothing"
    );

    assert!(
        !stdout.contains("s VERIFIED"),
        "veripb claimed to have verified a proof whose elaboration was lost:\n{context}"
    );
    assert_ne!(
        output.status.code(),
        Some(0),
        "veripb exited 0 although the elaborated proof could not be written:\n{context}"
    );
    assert!(
        stderr.contains("Failed to write the elaborated proof"),
        "the write failure should be reported, not swallowed:\n{context}"
    );
}

/// A successful elaboration still writes the kernel proof (i.e. the test above
/// fails for the right reason, and `finish` did not break the normal path).
#[test]
fn successful_elaboration_writes_the_kernel_proof() {
    let dir = tempfile::tempdir().expect("failed to create temporary directory");
    let kernel_proof = dir.path().join("kernel.pbp");

    let output = Command::new(env!("CARGO_BIN_EXE_veripb"))
        .args(["--opb", FORMULA, DERIVATION])
        .arg("--elaborate")
        .arg(&kernel_proof)
        .output()
        .expect("failed to run veripb binary");

    assert_eq!(output.status.code(), Some(0));
    let written = std::fs::read(&kernel_proof).expect("no kernel proof was written");
    assert!(!written.is_empty(), "the kernel proof is empty");
    assert!(Path::new(&kernel_proof).exists());
}

/// Wrap `value` in single quotes for `/bin/sh`.
fn shell_quote(value: &str) -> String {
    format!("'{}'", value.replace('\'', r"'\''"))
}
