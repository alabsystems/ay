//! End-to-end regression tests for silent input truncation (bugs A and B).
//!
//! These run the compiled `veripb` binary as a subprocess so that both the
//! verdict printed on stdout *and* the exit code are checked: the original
//! bugs printed `s VERIFIED SATISFIABLE` and exited 0 for a solution that
//! falsifies the real formula, because the parsers silently discarded every
//! constraint after the first unreadable line (or after an unterminated final
//! clause).

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

/// A byte sequence that is not valid UTF-8 (a lone continuation byte).
const BAD_BYTE: &[u8] = b"\xff";

struct Case {
    _dir: tempfile::TempDir,
    formula: PathBuf,
    proof: PathBuf,
}

/// Write a formula/proof pair into a fresh temporary directory.
fn case(formula_name: &str, formula: &[u8], proof_name: &str, proof: &[u8]) -> Case {
    let dir = tempfile::tempdir().expect("failed to create temporary directory");
    let write = |name: &str, bytes: &[u8]| {
        let path = dir.path().join(name);
        let mut file = std::fs::File::create(&path).expect("failed to create temporary file");
        file.write_all(bytes).expect("failed to write test input");
        file.flush().expect("failed to flush test input");
        path
    };
    let formula = write(formula_name, formula);
    let proof = write(proof_name, proof);
    Case {
        _dir: dir,
        formula,
        proof,
    }
}

struct Run {
    stdout: String,
    stderr: String,
    code: Option<i32>,
}

fn run_veripb(case: &Case, extra_args: &[&str]) -> Run {
    let output = Command::new(env!("CARGO_BIN_EXE_veripb"))
        .args(extra_args)
        .arg(&case.formula)
        .arg(&case.proof)
        .output()
        .expect("failed to run veripb binary");
    Run {
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        code: output.status.code(),
    }
}

/// The checker must not claim to have verified anything, and must have got
/// there by refusing rather than by falling over.
///
/// The exit status is pinned to exactly 1. `assert_ne!(code, Some(0))` is not
/// enough: `Output::status.code()` is `None` when the child dies on a signal,
/// and `[profile.release]` sets `panic = "abort"`, so an abort would satisfy
/// it — and with `overflow-checks` on, an abort is the *expected* outcome of a
/// whole class of defect. The stderr check additionally covers the dev
/// profile, where a panic unwinds to exit 101 instead.
fn assert_rejected(run: &Run, what: &str) {
    assert!(
        !run.stdout.contains("VERIFIED"),
        "{what}: veripb printed a verdict for an input it could not fully read:\n\
         --- stdout ---\n{}\n--- stderr ---\n{}",
        run.stdout,
        run.stderr
    );
    assert!(
        !run.stderr.contains("INTERNAL ERROR in VeriPB"),
        "{what}: veripb crashed instead of refusing the input:\n\
         --- stdout ---\n{}\n--- stderr ---\n{}",
        run.stdout,
        run.stderr
    );
    assert_eq!(
        run.code,
        Some(1),
        "{what}: an input veripb could not fully read must be refused with the \
         ordinary checking-error status, not crash and not exit 0:\n\
         --- stdout ---\n{}\n--- stderr ---\n{}",
        run.stdout,
        run.stderr
    );
}

/// Reproducer `01-formula-truncation-utf8`: a non-UTF-8 byte in an OPB comment
/// truncated the formula, and the proof's `conclusion SAT` was then checked
/// against the surviving prefix only, yielding `s VERIFIED SATISFIABLE` (exit
/// 0) for an assignment that falsifies `+1 x2 >= 1`.
#[test]
fn opb_non_utf8_byte_does_not_yield_a_verdict() {
    let formula = [
        b"* ok\n+1 x1 >= 1 ;\n* bad ".as_slice(),
        BAD_BYTE,
        b" byte\n+1 x2 >= 1 ;\n",
    ]
    .concat();
    let proof = b"pseudo-Boolean proof version 3.0\n\
                  sol x1 ~x2;\n\
                  output NONE;\n\
                  conclusion SAT : x1 ~x2;\n\
                  end pseudo-Boolean proof;\n";
    let case = case("t.opb", &formula, "t.pbp", proof);

    let run = run_veripb(&case, &["--opb"]);
    assert_rejected(&run, "opb non-UTF-8 comment");
}

/// Reproducer `02-cnf-unterminated-clause`: the final clause `3` is not
/// terminated by `0`, so it was dropped and `~x3` was accepted as part of a
/// satisfying assignment.
#[test]
fn cnf_unterminated_final_clause_does_not_yield_a_verdict() {
    let proof = b"pseudo-Boolean proof version 3.0\n\
                  sol x1 x2 ~x3;\n\
                  output NONE;\n\
                  conclusion SAT : x1 x2 ~x3;\n\
                  end pseudo-Boolean proof;\n";
    let case = case("t.cnf", b"p cnf 3 3\n1 0\n2 0\n3", "c.pbp", proof);

    let run = run_veripb(&case, &["--cnf"]);
    assert_rejected(&run, "cnf unterminated final clause");
}

/// A CNF file truncated at a clause boundary is syntactically fine; only the
/// declared `p cnf <vars> <clauses>` count reveals the loss. The CLI runs the
/// CNF parser in strict mode so this is rejected.
#[test]
fn cnf_missing_clause_count_does_not_yield_a_verdict() {
    let proof = b"pseudo-Boolean proof version 3.0\n\
                  sol x1 x2 ~x3;\n\
                  output NONE;\n\
                  conclusion SAT : x1 x2 ~x3;\n\
                  end pseudo-Boolean proof;\n";
    let case = case("t.cnf", b"p cnf 3 3\n1 0\n2 0\n", "c.pbp", proof);

    let run = run_veripb(&case, &["--cnf"]);
    assert_rejected(&run, "cnf clause count mismatch");
}

/// A WCNF file whose last clause is not terminated by `0`.
#[test]
fn wcnf_unterminated_final_clause_does_not_yield_a_verdict() {
    // The dropped clause `~x1` contradicts the first clause `x1`, so `x1 x2`
    // is not a solution of the real formula; with the clause dropped the `sol`
    // rule is accepted and the run ends in `s VERIFIED NO CONCLUSION` (exit 0).
    // (A WCNF instance always carries an objective, so `conclusion SAT` is not
    // available here.)
    let proof = b"pseudo-Boolean proof version 3.0\n\
                  sol x1 x2;\n\
                  output NONE;\n\
                  conclusion NONE;\n\
                  end pseudo-Boolean proof;\n";
    let case = case("t.wcnf", b"h 1 0\nh 2 0\nh -1\n", "w.pbp", proof);

    let run = run_veripb(&case, &["--wcnf"]);
    assert_rejected(&run, "wcnf unterminated final clause");
}

/// The version-2 proof parser had the same `map_while(Result::ok)` bug: an
/// unreadable line silently ended proof parsing. The checker must report the
/// read failure rather than a downstream symptom of the dropped lines.
#[test]
fn v2_proof_non_utf8_byte_reports_the_read_failure() {
    let proof = [
        b"pseudo-Boolean proof version 2.0\nf 1\n* bad ".as_slice(),
        BAD_BYTE,
        b" byte\nu 1 x1 >= 1 ;\noutput NONE\nconclusion NONE\nend pseudo-Boolean proof\n",
    ]
    .concat();
    let case = case("t.opb", b"1 x1 >= 1 ;\n", "t.pbp", &proof);
    let run = run_veripb(&case, &["--opb"]);

    assert_ne!(
        run.code,
        Some(0),
        "veripb exited 0 on an unreadable proof file"
    );
    let combined = format!("{}{}", run.stdout, run.stderr);
    assert!(
        combined.contains("Failed to read"),
        "expected a read-failure diagnostic naming the unreadable line, got:\n\
         --- stdout ---\n{}\n--- stderr ---\n{}",
        run.stdout,
        run.stderr
    );
}
