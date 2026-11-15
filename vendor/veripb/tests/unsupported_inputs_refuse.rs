//! Inputs the checker does not support must be *refused*, never aborted.
//!
//! The release profile sets `panic = "abort"`, so a `panic!`/`unimplemented!`
//! reached from ordinary input is a process death with no verdict — the same
//! failure shape as the `wiplvl` slice fixed in `66138cf7`. These three all
//! did that, and all three were found by triaging the `indexing_slicing` /
//! `unwrap_used` / `unimplemented` findings that the four crate-level
//! `#![allow(clippy::restriction)]` attributes hide.
//!
//! Measured against `66138cf7`: the first two abort with
//! `not implemented` at `veripb-checker/src/rules/output.rs:21` and `:217`,
//! and the third with `called Option::unwrap() on a None value` at
//! `veripb-parser/src/pbp_parser/legacy_v2/parser.rs:167`. None of them was
//! ever an *accepted* proof, so turning each into a checking error changes no
//! verdict: it replaces "no verdict, exit 134" with "refused, exit 1".

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

struct Case {
    _dir: tempfile::TempDir,
    formula: PathBuf,
    proof: PathBuf,
    output_formula: Option<PathBuf>,
}

fn write_in(dir: &tempfile::TempDir, name: &str, contents: &str) -> PathBuf {
    let path = dir.path().join(name);
    let mut file = std::fs::File::create(&path).expect("failed to create temporary file");
    file.write_all(contents.as_bytes())
        .expect("failed to write test input");
    file.flush().expect("failed to flush test input");
    path
}

fn case(proof: &str, output_formula: Option<(&str, &str)>) -> Case {
    let dir = tempfile::tempdir().expect("failed to create temporary directory");
    let formula = write_in(
        &dir,
        "f.opb",
        "* #variable= 1 #constraint= 1\n1 x1 >= 0 ;\n",
    );
    let proof = write_in(&dir, "p.pbp", proof);
    let output_formula = output_formula.map(|(name, body)| write_in(&dir, name, body));
    Case {
        formula,
        proof,
        output_formula,
        _dir: dir,
    }
}

/// Run the binary and assert it refused: exit 1, and no sign of a panic on
/// stderr. `Output::status.code()` is `None` when the child dies on a signal,
/// which is what `panic = "abort"` produces, so the status alone is not
/// enough — the stderr check is what covers the dev profile, where a panic
/// unwinds to exit 101 and the binary's own hook prints `INTERNAL ERROR`.
fn assert_refused(case: &Case, what: &str) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_veripb"));
    command.arg(&case.formula).arg(&case.proof);
    if let Some(output_formula) = &case.output_formula {
        command.arg(output_formula);
    }
    let output = command.output().expect("failed to run veripb binary");
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let context = format!("--- stdout ---\n{stdout}--- stderr ---\n{stderr}");

    assert!(
        !stderr.contains("INTERNAL ERROR in VeriPB"),
        "{what}: veripb crashed instead of refusing the input:\n{context}"
    );
    assert_eq!(
        output.status.code(),
        Some(1),
        "{what}: an unsupported input must exit with the ordinary \
         checking-error status, not crash and not exit 0:\n{context}"
    );
    assert!(
        !stdout.lines().any(|line| line.starts_with("s VERIFIED")),
        "{what}: an unsupported input must not be reported as verified:\n{context}"
    );
}

#[test]
fn a_dimacs_cnf_output_formula_is_refused() {
    assert_refused(
        &case(
            "pseudo-Boolean proof version 3.0\n\
             f 1;\n\
             output EQUISATISFIABLE FILE;\n\
             conclusion NONE;\n\
             end pseudo-Boolean proof;\n",
            Some(("out.cnf", "p cnf 1 1\n1 0\n")),
        ),
        "output ... FILE against a .cnf output formula",
    );
}

#[test]
fn output_permutation_is_refused_in_both_proof_versions() {
    // Version 3 routes this through `UnimplementedRule` in the parser and has
    // always refused it; version 2 reached `output.rs`'s catch-all arm.
    assert_refused(
        &case(
            "pseudo-Boolean proof version 3.0\n\
             f 1;\n\
             output EQUISATISFIABLE PERMUTATION;\n\
             conclusion NONE;\n\
             end pseudo-Boolean proof;\n",
            None,
        ),
        "version 3 `output EQUISATISFIABLE PERMUTATION`",
    );
    assert_refused(
        &case(
            "pseudo-Boolean proof version 2.0\n\
             f 1\n\
             output EQUISATISFIABLE PERMUTATION\n\
             conclusion NONE\n\
             end pseudo-Boolean proof\n",
            None,
        ),
        "version 2 `output EQUISATISFIABLE PERMUTATION`",
    );
}

#[test]
fn a_constraint_id_that_does_not_fit_isize_is_refused() {
    assert_refused(
        &case(
            "pseudo-Boolean proof version 2.0\n\
             f 1\n\
             core id 99999999999999999999999\n\
             conclusion NONE\n\
             end pseudo-Boolean proof\n",
            None,
        ),
        "version 2 `core id` with an out-of-range constraint ID",
    );
}
