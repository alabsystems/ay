//! End-to-end regression tests for the verdicts that solution logging is
//! allowed to reach.
//!
//! `sol`, `soli`/`obji` and `solx` all record something about a solution, but
//! only `sol` leaves the problem alone. The other two store a constraint that is
//! satisfiability-preserving and *not* entailed, i.e. they delete solutions —
//! and each verdict that talks about solutions of the original problem has to
//! account for exactly what they deleted. Two defects came from not doing so:
//!
//! 1. `conclusion ENUMERATION_COMPLETE n` checks that `n` matches the number of
//!    solutions `solx` excluded and that the database is contradictory, but
//!    nothing checked *why* it is contradictory. An objective-improving
//!    `soli`/`obji` stores `obj <= v - 1`, which removes every assignment with
//!    objective value at least `v` without touching the counter, so a single
//!    `soli` on a genuine solution made a satisfiable formula report
//!    `s VERIFIED COMPLETE ENUMERATION OF 0 SOLUTIONS` with exit code 0 and
//!    default flags. The `ENUMERATION_PARTIAL` leg is *not* affected and stays
//!    accepted — it claims only that at least `n` projected solutions were
//!    witnessed, which no deletion can falsify.
//!
//! 2. The `conclusion BOUNDS` lower bound was compared against
//!    `best_objective_value`, the objective value of the logged
//!    *representative*. `solx` removes the whole class of assignments agreeing
//!    with that representative on the preserved variables, and when the
//!    objective mentions an unpreserved variable that class reaches below the
//!    representative's value — so a lower bound proved through the excluding
//!    constraint passed the guard and certified an optimum above the true one.
//!    The same miscalibration reached `output EQUIOPTIMAL`, whose
//!    `FOR obj < ...` qualifier named the representative's value, and
//!    `output EQUISATISFIABLE`, which tolerates no deletion at all.

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

fn case(formula: &str, proof: &str) -> Case {
    let dir = tempfile::tempdir().expect("failed to create temporary directory");
    Case {
        formula: write_in(&dir, "f.opb", formula),
        proof: write_in(&dir, "p.pbp", proof),
        output_formula: None,
        _dir: dir,
    }
}

fn case_with_output(formula: &str, proof: &str, output_formula: &str) -> Case {
    let dir = tempfile::tempdir().expect("failed to create temporary directory");
    Case {
        formula: write_in(&dir, "f.opb", formula),
        proof: write_in(&dir, "p.pbp", proof),
        output_formula: Some(write_in(&dir, "out.opb", output_formula)),
        _dir: dir,
    }
}

struct Run {
    stdout: String,
    stderr: String,
    code: Option<i32>,
}

impl Run {
    fn verdicts(&self) -> Vec<&str> {
        self.stdout
            .lines()
            .filter(|line| line.starts_with("s "))
            .collect()
    }

    fn context(&self) -> String {
        format!(
            "--- stdout ---\n{}--- stderr ---\n{}",
            self.stdout, self.stderr
        )
    }

    /// The proof was refused: nothing that looks like a pass on stdout, and the
    /// ordinary checking-error exit status.
    ///
    /// The status is pinned to exactly 1, not merely asserted non-zero, and the
    /// panic marker is checked separately. `Output::status.code()` is `None`
    /// when the child dies on a signal and `[profile.release]` sets
    /// `panic = "abort"`, so `assert_ne!(code, Some(0))` is satisfied by a
    /// **crash** — and `overflow-checks` was deliberately turned on to make an
    /// abort the expected outcome of a whole class of defect, which is exactly
    /// the surface on which a rejection test could start passing for the wrong
    /// reason. The stderr check catches the dev profile's unwind too (exit
    /// 101, which a bare `is_some()` would accept), and says what happened.
    fn assert_rejected(&self) {
        assert!(
            self.verdicts().is_empty(),
            "veripb printed a verdict for a proof it must refuse:\n{}",
            self.context()
        );
        self.assert_did_not_crash();
        assert_eq!(
            self.code,
            Some(1),
            "a refused proof must exit with the ordinary checking-error status, \
             not crash and not exit 0:\n{}",
            self.context()
        );
    }

    /// The run ended by deciding something, not by falling over. See
    /// [`Run::assert_rejected`] for why "non-zero exit" does not imply this.
    fn assert_did_not_crash(&self) {
        assert!(
            !self.stderr.contains("INTERNAL ERROR in VeriPB"),
            "veripb crashed instead of refusing the proof:\n{}",
            self.context()
        );
    }

    /// The proof was accepted with exactly these verdict lines.
    fn assert_accepted(&self, expected: &[&str]) {
        assert_eq!(
            self.verdicts(),
            expected,
            "unexpected verdict lines:\n{}",
            self.context()
        );
        assert_eq!(
            self.code,
            Some(0),
            "a valid proof must exit 0:\n{}",
            self.context()
        );
    }
}

fn run_veripb(case: &Case) -> Run {
    let mut command = Command::new(env!("CARGO_BIN_EXE_veripb"));
    command.arg("--opb").arg(&case.formula).arg(&case.proof);
    if let Some(output_formula) = &case.output_formula {
        command.arg(output_formula);
    }
    let output = command.output().expect("failed to run veripb binary");
    Run {
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        code: output.status.code(),
    }
}

/// Satisfiable, with an objective over the *preserved* variable. Solutions are
/// `(x1,x2) in {(0,1),(1,0),(1,1)}`: three solutions, two projections onto x1,
/// one optimum. Every reading of "0 solutions" is false.
const ENUM_FORMULA: &str = "\
* #variable= 2 #constraint= 1
preserved: x1 ;
min: 1 x1 ;
1 x1 1 x2 >= 1 ;
";

/// Satisfiable, objective over the *unpreserved* x2. Projections onto x1 are
/// `{0, 1}`, so there are two projected solutions.
const ENUM_FORMULA_UNPRESERVED_OBJECTIVE: &str = "\
* #variable= 2 #constraint= 1
preserved: x1 ;
min: 1 x2 ;
1 x1 1 x2 >= 1 ;
";

/// The `soli` alone makes the database contradictory, without ever incrementing
/// the excluded-solution counter.
#[test]
fn enumeration_complete_after_an_improving_solution_is_rejected() {
    let proof = "\
pseudo-Boolean proof version 3.0
f 1;
soli ~x1 x2;
output NONE;
conclusion ENUMERATION_COMPLETE 0;
end pseudo-Boolean proof;
";
    run_veripb(&case(ENUM_FORMULA, proof)).assert_rejected();
}

/// `obji` stores the same constraint without even exhibiting a solution.
#[test]
fn enumeration_complete_after_an_objective_bound_is_rejected() {
    let proof = "\
pseudo-Boolean proof version 3.0
f 1;
obji 0;
output NONE;
conclusion ENUMERATION_COMPLETE 0;
end pseudo-Boolean proof;
";
    run_veripb(&case(ENUM_FORMULA, proof)).assert_rejected();
}

/// The non-degenerate shape: one projection really is witnessed and counted, the
/// `soli` deletes the other one uncounted. Rejecting only `... 0` would miss it.
#[test]
fn an_undercounted_enumeration_is_rejected() {
    let proof = "\
pseudo-Boolean proof version 3.0
f 1;
solx x1 ~x2;
soli ~x1 x2;
pol 1 2 + 3 +;
output NONE;
conclusion ENUMERATION_COMPLETE 1;
end pseudo-Boolean proof;
";
    run_veripb(&case(ENUM_FORMULA_UNPRESERVED_OBJECTIVE, proof)).assert_rejected();
}

/// The scope line of that fix. `ENUMERATION_PARTIAL n` claims only that at least
/// `n` projected solutions were witnessed; no rule ever adds models, so the
/// `solx` below really did witness a distinct projected solution of the original
/// problem and the `soli` cannot falsify that. Guarding this leg would reject
/// sound proofs, so it is deliberately left alone.
#[test]
fn enumeration_partial_after_an_improving_solution_is_still_accepted() {
    let proof = "\
pseudo-Boolean proof version 3.0
f 1;
solx x1 ~x2;
soli ~x1 x2;
pol 1 2 + 3 +;
output NONE;
conclusion ENUMERATION_PARTIAL 1;
end pseudo-Boolean proof;
";
    run_veripb(&case(ENUM_FORMULA_UNPRESERVED_OBJECTIVE, proof))
        .assert_accepted(&["s VERIFIED PARTIAL ENUMERATION OF 1 SOLUTIONS"]);
}

/// The other half of the scope line: having an objective, and logging a solution
/// with a plain `sol`, must not trip the guard. Only the objective-improving
/// rules do.
#[test]
fn enumeration_complete_with_an_objective_and_a_plain_sol_is_still_accepted() {
    let proof = "\
pseudo-Boolean proof version 3.0
f 1;
sol x1 ~x2;
solx x1 ~x2;
solx ~x1 x2;
pol 2 3 +;
output NONE;
conclusion ENUMERATION_COMPLETE 2;
end pseudo-Boolean proof;
";
    run_veripb(&case(ENUM_FORMULA_UNPRESERVED_OBJECTIVE, proof))
        .assert_accepted(&["s VERIFIED COMPLETE ENUMERATION OF 2 SOLUTIONS"]);
}

/// `preserved: x1` with the objective on x2. Solutions are `(0,0)` with
/// objective 0, `(0,1)` and `(1,1)` with objective 100 — the optimum is 0.
const BOUNDS_FORMULA: &str = "\
* #variable= 2 #constraint= 1
preserved: x1 ;
min: 100 x2 ;
1 ~x1 1 x2 >= 1 ;
";

/// `solx ~x1 x2` deletes the whole x1=0 class, which contains the optimum, while
/// only recording the representative's value 100. The lower bound is then proved
/// straight through the excluding constraint.
#[test]
fn a_lower_bound_proved_through_an_excluded_class_is_rejected() {
    let proof = "\
pseudo-Boolean proof version 3.0
f 1;
solx ~x1 x2;
pol 1 2 +;
pol 3 100 *;
output NONE;
conclusion BOUNDS 100 100 : ~x1 x2;
end pseudo-Boolean proof;
";
    run_veripb(&case(BOUNDS_FORMULA, proof)).assert_rejected();
}

/// The same binary used to certify both `BOUNDS 100 100` and this, the true
/// optimum, for the same formula. Only one of them may survive.
#[test]
fn the_true_optimum_of_the_same_formula_is_still_accepted() {
    let proof = "\
pseudo-Boolean proof version 3.0
f 1;
output NONE;
conclusion BOUNDS 0 0 : ~x1 ~x2;
end pseudo-Boolean proof;
";
    run_veripb(&case(BOUNDS_FORMULA, proof)).assert_accepted(&["s VERIFIED BOUNDS 0 <= obj <= 0"]);
}

/// The completeness side of that fix: with the objective inside the preserved
/// set the excluded class is pinned down to the logged solution, so its minimum
/// is exactly the representative's value and an exact optimum is still
/// concluded after excluding an optimal solution.
#[test]
fn a_lower_bound_after_solx_over_a_preserved_objective_is_still_accepted() {
    let formula = "\
* #variable= 2 #constraint= 1
preserved: x1 x2 ;
min: 1 x1 1 x2 ;
1 x1 1 x2 >= 1 ;
";
    let proof = "\
pseudo-Boolean proof version 3.0
f 1;
solx x1 ~x2;
output NONE;
conclusion BOUNDS 1 1 : x1 ~x2;
end pseudo-Boolean proof;
";
    run_veripb(&case(formula, proof)).assert_accepted(&["s VERIFIED BOUNDS 1 <= obj <= 1"]);
}

/// `output EQUIOPTIMAL` stays available after `solx`, but its qualifier has to
/// name the value below which nothing was removed. It printed `FOR obj < 100`,
/// the representative's value, which is false here: restricted to `obj < 100`
/// the input still has the solution `(0,0)` while the output formula has none.
#[test]
fn the_equioptimal_qualifier_names_what_was_actually_removed() {
    let proof = "\
pseudo-Boolean proof version 3.0
f 1;
solx ~x1 x2;
output EQUIOPTIMAL FILE;
conclusion NONE;
end pseudo-Boolean proof;
";
    let output_formula = "\
* #variable= 2 #constraint= 2
min: 100 x2 ;
1 ~x1 1 x2 >= 1 ;
1 x1 >= 1 ;
";
    run_veripb(&case_with_output(BOUNDS_FORMULA, proof, output_formula)).assert_accepted(&[
        "s VERIFIED OUTPUT EQUIOPTIMAL FOR obj < 0",
        "s VERIFIED NO CONCLUSION",
    ]);
}

/// `output EQUISATISFIABLE` carries no qualifier, so it cannot survive a rule
/// that deletes solutions. Here `solx` deletes the only solution class, leaving
/// an unsatisfiable output formula for a satisfiable input.
#[test]
fn equisatisfiable_after_an_excluded_solution_is_rejected() {
    let formula = "\
* #variable= 1 #constraint= 1
preserved: x1 ;
1 x1 >= 1 ;
";
    let proof = "\
pseudo-Boolean proof version 3.0
f 1;
solx x1;
output EQUISATISFIABLE FILE;
conclusion NONE;
end pseudo-Boolean proof;
";
    let output_formula = "\
* #variable= 1 #constraint= 2
1 x1 >= 1 ;
1 ~x1 >= 1 ;
";
    run_veripb(&case_with_output(formula, proof, output_formula)).assert_rejected();
}
