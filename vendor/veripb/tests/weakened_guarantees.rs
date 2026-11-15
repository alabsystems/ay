//! End-to-end regression tests for what VeriPB reports once unchecked deletion
//! has weakened the guarantee it can give.
//!
//! Two separate defects are covered:
//!
//! 1. A hintless `conclusion SAT` was validated against `best_objective_value`
//!    (any logged solution) instead of `best_valid_objective_value` (a solution
//!    logged while checked deletion was still in effect). Since `sol` is checked
//!    against the *current* database, deleting a core constraint first made an
//!    unsatisfiable formula report `s VERIFIED SATISFIABLE` with exit code 0 and
//!    default flags.
//!
//! 2. Even where the verdict does hold, it holds under a weaker guarantee than
//!    `s VERIFIED` claims. The downgrade was only mentioned in a `log::warn!` on
//!    stderr while stdout carried an unqualified pass, so every caller that
//!    greps stdout — the documented way to consume the result — saw nothing.

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

struct Case {
    _dir: tempfile::TempDir,
    formula: PathBuf,
    proof: PathBuf,
}

fn case(formula: &str, proof: &str) -> Case {
    let dir = tempfile::tempdir().expect("failed to create temporary directory");
    let write = |name: &str, contents: &str| {
        let path = dir.path().join(name);
        let mut file = std::fs::File::create(&path).expect("failed to create temporary file");
        file.write_all(contents.as_bytes())
            .expect("failed to write test input");
        file.flush().expect("failed to flush test input");
        path
    };
    Case {
        formula: write("f.opb", formula),
        proof: write("p.pbp", proof),
        _dir: dir,
    }
}

struct Run {
    stdout: String,
    stderr: String,
    code: Option<i32>,
}

impl Run {
    fn verdict(&self) -> Option<&str> {
        self.stdout.lines().find(|line| line.starts_with("s "))
    }

    fn context(&self) -> String {
        format!(
            "--- stdout ---\n{}--- stderr ---\n{}",
            self.stdout, self.stderr
        )
    }

    /// The run refused the proof: the ordinary checking-error exit status, and
    /// no sign of a panic.
    ///
    /// Pinning the status matters more here than anywhere else in the tree.
    /// `Output::status.code()` is `None` when the child dies on a signal, and
    /// `[profile.release]` sets `panic = "abort"`, so the `assert_ne!(code,
    /// Some(0))` these tests used to carry was satisfied by a **crash** — in
    /// the profile that was deliberately given `overflow-checks` so that a
    /// whole class of wrap defect aborts instead of returning a wrong verdict.
    /// A test that scores an abort as a correct refusal would go green on a
    /// build that crashes for a completely unrelated reason. The stderr check
    /// covers the dev profile too, where a panic unwinds to exit 101.
    fn assert_refused(&self) {
        assert!(
            !self.stderr.contains("INTERNAL ERROR in VeriPB"),
            "veripb crashed instead of refusing the proof:\n{}",
            self.context()
        );
        assert_eq!(
            self.code,
            Some(1),
            "a refused proof must exit with the ordinary checking-error status, \
             not crash and not exit 0:\n{}",
            self.context()
        );
    }
}

fn run_veripb(case: &Case, extra_args: &[&str]) -> Run {
    let output = Command::new(env!("CARGO_BIN_EXE_veripb"))
        .args(extra_args)
        .arg("--opb")
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

/// At least two of `x1, x2, x3` must be true, but no two of them may be: this
/// formula is unsatisfiable.
const UNSAT_FORMULA: &str = "\
* #variable= 3 #constraint= 4
1 x1 1 x2 1 x3 >= 2 ;
1 ~x1 1 ~x2 >= 1 ;
1 ~x1 1 ~x3 >= 1 ;
1 ~x2 1 ~x3 >= 1 ;
";

/// Deleting constraint 2 (which cannot be proven) makes `x1 x2 ~x3` pass the
/// `sol` check against what is left of the formula.
const FAKE_SAT_PROOF: &str = "\
pseudo-Boolean proof version 3.0
f 4 ;
del id 2;
sol x1 x2 ~x3;
output NONE;
conclusion SAT;
end pseudo-Boolean proof;
";

/// The core wrong-verdict case: default flags, unsatisfiable formula,
/// `s VERIFIED SATISFIABLE` on stdout and exit 0.
#[test]
fn hintless_conclusion_sat_after_unchecked_deletion_is_rejected() {
    let run = run_veripb(&case(UNSAT_FORMULA, FAKE_SAT_PROOF), &[]);

    assert_eq!(
        run.verdict(),
        None,
        "veripb printed a verdict for an unsatisfiable formula:\n{}",
        run.context()
    );
    run.assert_refused();
}

/// The same holds when the user asked for unchecked deletion up front: nothing
/// then guarantees that a logged solution is a solution of the original problem.
#[test]
fn hintless_conclusion_sat_is_rejected_with_unchecked_deletion() {
    let run = run_veripb(&case(UNSAT_FORMULA, FAKE_SAT_PROOF), &["-u"]);

    assert_eq!(run.verdict(), None, "{}", run.context());
    run.assert_refused();
}

/// Control: the same attack with an explicit solution hint was already rejected,
/// because the hint is checked against the original constraints.
#[test]
fn conclusion_sat_with_a_solution_hint_is_still_checked_against_the_formula() {
    let proof = FAKE_SAT_PROOF.replace("conclusion SAT;", "conclusion SAT : x1 x2 ~x3;");
    let run = run_veripb(&case(UNSAT_FORMULA, &proof), &[]);

    assert_eq!(run.verdict(), None, "{}", run.context());
    run.assert_refused();
}

/// Control: `--force-checked-deletion` rejects the proof at the deletion.
#[test]
fn force_checked_deletion_rejects_the_deletion_itself() {
    let run = run_veripb(&case(UNSAT_FORMULA, FAKE_SAT_PROOF), &["-c"]);

    assert_eq!(run.verdict(), None, "{}", run.context());
    run.assert_refused();
}

/// A satisfiable formula whose solution is logged *before* the deletion that
/// cannot be checked. The `SAT` conclusion does hold, but the run no longer
/// checked everything it was asked to check, so it must not report a bare
/// `s VERIFIED` and must not exit 0.
#[test]
fn a_verdict_reached_after_a_silent_downgrade_is_qualified() {
    let formula = "* #variable= 2 #constraint= 2\n1 x1 >= 1 ;\n1 x2 >= 1 ;\n";
    let proof = "\
pseudo-Boolean proof version 3.0
f 2 ;
sol x1 x2;
del id 2;
output NONE;
conclusion SAT;
end pseudo-Boolean proof;
";
    let run = run_veripb(&case(formula, proof), &[]);

    assert_eq!(
        run.verdict(),
        Some("s UNDER WEAKENED GUARANTEES SATISFIABLE"),
        "the weakened guarantee has to be visible in the verdict itself:\n{}",
        run.context()
    );
    assert!(
        !run.stdout.contains("s VERIFIED"),
        "a downgraded run must not print an unqualified pass:\n{}",
        run.context()
    );
    assert_eq!(
        run.code,
        Some(2),
        "a silent downgrade must not exit 0 either:\n{}",
        run.context()
    );
}

/// Asking for the weaker guarantee with `--unchecked-deletion` is not an
/// unrequested downgrade: the verdict is still qualified, but the exit code
/// stays 0 because the run did what it was told to do.
#[test]
fn requested_unchecked_deletion_still_exits_zero() {
    let formula = "* #variable= 2 #constraint= 2\n1 x1 >= 1 ;\n1 x2 >= 1 ;\n";
    let proof = "\
pseudo-Boolean proof version 3.0
f 2 ;
sol x1 x2;
del id 2;
output NONE;
conclusion SAT : x1 x2;
end pseudo-Boolean proof;
";
    let run = run_veripb(&case(formula, proof), &["-u"]);

    assert_eq!(
        run.verdict(),
        Some("s UNDER WEAKENED GUARANTEES SATISFIABLE"),
        "{}",
        run.context()
    );
    assert_eq!(run.code, Some(0), "{}", run.context());
}

/// Unchecked deletion does not weaken a refutation — deletion only ever removes
/// constraints — so an `UNSAT` verdict must keep saying `s VERIFIED` and exit 0.
/// This is the verdict downstream tooling greps for.
#[test]
fn unsat_verdicts_are_not_qualified_by_unchecked_deletion() {
    let formula = "* #variable= 1 #constraint= 2\n1 x1 >= 1 ;\n1 ~x1 >= 1 ;\n";
    let proof = "\
pseudo-Boolean proof version 3.0
f 2 ;
pol 1 2 + ;
output NONE;
conclusion UNSAT;
end pseudo-Boolean proof;
";
    let run = run_veripb(&case(formula, proof), &["-u"]);

    assert_eq!(
        run.verdict(),
        Some("s VERIFIED UNSATISFIABLE"),
        "{}",
        run.context()
    );
    assert_eq!(run.code, Some(0), "{}", run.context());
}

/// A proof that is rejected after its `conclusion` line (here: the closing
/// `end pseudo-Boolean proof;` is missing) must not leave a verdict on stdout.
#[test]
fn no_verdict_is_printed_when_the_proof_is_rejected_after_the_conclusion() {
    let formula = "* #variable= 1 #constraint= 2\n1 x1 >= 1 ;\n1 ~x1 >= 1 ;\n";
    let proof = "\
pseudo-Boolean proof version 3.0
f 2 ;
pol 1 2 + ;
output NONE;
conclusion UNSAT;
";
    let run = run_veripb(&case(formula, proof), &[]);

    assert_eq!(
        run.verdict(),
        None,
        "an incomplete proof must not print a verdict:\n{}",
        run.context()
    );
    run.assert_refused();
}
