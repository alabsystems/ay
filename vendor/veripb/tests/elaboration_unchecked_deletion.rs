//! What the elaborated proof says about a core deletion whose obligation the
//! run did not discharge.
//!
//! Two deletion paths write a *bare* `delc <id>;` into the elaborated proof:
//! `Elaborator::write_unchecked_deletion`, when a checked deletion was
//! attempted and failed and VeriPB fell back; and
//! `Elaborator::write_core_deletions_no_subproof`, when the check was never
//! attempted (`--unchecked-deletion`, or any point after an earlier fallback
//! already lowered the guarantee). Neither records the downgrade, and the
//! obvious worry is that it cannot: the proof format has no rule for an
//! unchecked core deletion, so there is nothing to write.
//!
//! That worry is unfounded, and this file is what makes it stay unfounded. A
//! bare `delc <id>;` is a **checked** core deletion — `delc` is `del id`
//! restricted to the core set (`proof_format_overview.md`, "(delc) Delete Core
//! Constraint"), and deletion from the core is exactly what carries the
//! obligation. So the artifact *states* the obligation the run dropped rather
//! than hiding it: whoever checks the elaborated proof has to discharge it or
//! lower its guarantee, which is what VeriPB itself does when it re-reads its
//! own output. The artifact asks for at least as much as the run established,
//! never less.
//!
//! Two properties have to hold for that to be true, and both are pinned here:
//!
//! 1. **The round trip is faithful under every deletion flag.** Verdict *and*
//!    exit code, for the input and for its elaboration, under default flags,
//!    `--unchecked-deletion` and `--force-checked-deletion`. This is the part
//!    `tests/elaboration_verdict.rs` structurally cannot see: it sweeps the
//!    corpus under default flags only and skips any run that exits non-zero,
//!    so the exit-2 downgrade and the whole `-u` axis are invisible to it.
//! 2. **A discharged deletion is distinguishable from a dropped one.** Every
//!    core deletion the elaborator *does* discharge goes out in the subproof
//!    form, `delc <id> : <witness> : subproof ... qed;`. The bare form is
//!    reserved for dropped obligations. If that ever stopped being true the
//!    artifact would become genuinely ambiguous, which is the defect this file
//!    exists to catch.

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

struct Case {
    _dir: tempfile::TempDir,
    formula: PathBuf,
    proof: PathBuf,
    elaborated: PathBuf,
}

/// A run's observable outcome: the `s ...` line (or `None` when the proof was
/// refused) together with the process exit code.
#[derive(Debug, PartialEq, Eq)]
struct Outcome {
    verdict: Option<String>,
    code: Option<i32>,
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
        elaborated: dir.path().join("elaborated.pbp"),
        _dir: dir,
    }
}

fn run(formula: &PathBuf, proof: &PathBuf, extra: &[&str]) -> (Outcome, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_veripb"))
        .args(extra)
        .arg(formula)
        .arg(proof)
        .output()
        .expect("failed to run veripb binary");
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(
        !stderr.contains("INTERNAL ERROR in VeriPB"),
        "veripb crashed:\n--- stdout ---\n{stdout}--- stderr ---\n{stderr}"
    );
    (
        Outcome {
            verdict: stdout
                .lines()
                .find(|line| line.starts_with("s "))
                .map(str::to_string),
            code: output.status.code(),
        },
        stderr,
    )
}

/// Elaborate `case` under `elaborate_flags` and return the elaborated text.
fn elaborate(case: &Case, elaborate_flags: &[&str]) -> String {
    let mut args: Vec<&str> = elaborate_flags.to_vec();
    args.push("-e");
    args.push(case.elaborated.to_str().expect("utf-8 path"));
    let (outcome, stderr) = run(&case.formula, &case.proof, &args);
    assert!(
        outcome.code == Some(0) || outcome.code == Some(2),
        "elaboration neither succeeded nor merely weakened its guarantee: {outcome:?}\n{stderr}"
    );
    std::fs::read_to_string(&case.elaborated).expect("elaboration wrote no proof")
}

/// The elaborated proof must reproduce the input's verdict *and* exit code
/// under every flag that changes how a core deletion is treated.
fn assert_round_trips(case: &Case, elaborate_flags: &[&str], what: &str) {
    elaborate(case, elaborate_flags);
    for flags in [&[][..], &["-u"][..], &["-c"][..]] {
        let (before, _) = run(&case.formula, &case.proof, flags);
        let (after, _) = run(&case.formula, &case.elaborated, flags);
        assert_eq!(
            before, after,
            "{what}: elaboration changed the claim when re-checked with {flags:?}"
        );
    }
}

/// Bare `delc <ids>;` lines, i.e. deletions written without a subproof.
fn bare_delc_lines(elaborated: &str) -> Vec<&str> {
    elaborated
        .lines()
        .map(str::trim)
        .filter(|line| {
            line.starts_with("delc ")
                && line.ends_with(';')
                && !line.contains("subproof")
                && line[5..line.len() - 1]
                    .split_whitespace()
                    .all(|token| token.parse::<usize>().is_ok())
        })
        .collect()
}

fn subproof_delc_lines(elaborated: &str) -> Vec<&str> {
    elaborated
        .lines()
        .map(str::trim)
        .filter(|line| line.starts_with("delc ") && line.contains("subproof"))
        .collect()
}

/// `1 x1 >= 1` cannot be re-derived from `1 x2 >= 1`, so deleting it from the
/// core fails its check and VeriPB falls back.
const UNPROVABLE_FORMULA: &str = "* #variable= 2 #constraint= 2\n1 x1 >= 1 ;\n1 x2 >= 1 ;\n";

/// The same formula plus `1 x1 1 x2 >= 2`, which makes deleting `1 x2 >= 1`
/// RUP — so here the check *can* be discharged, and `--unchecked-deletion` is
/// the only reason it is not.
const PROVABLE_FORMULA: &str =
    "* #variable= 2 #constraint= 3\n1 x1 >= 1 ;\n1 x2 >= 1 ;\n1 x1 1 x2 >= 2 ;\n";

/// Logging the solution before the deletion makes the conclusion depend on it,
/// which is what turns the downgrade into a visible `s UNDER WEAKENED
/// GUARANTEES` verdict and exit code 2.
const SOL_THEN_DELETE: &str = "\
pseudo-Boolean proof version 3.0
f 2 ;
sol x1 x2;
del id 1;
output NONE;
conclusion SAT;
end pseudo-Boolean proof;
";

const SOL_THEN_DELETE_V2: &str = "\
pseudo-Boolean proof version 2.0
f 2
sol x1 x2
del id 1
output NONE
conclusion SAT
end pseudo-Boolean proof
";

/// A deletion that *is* provable, so that `--unchecked-deletion` is the only
/// thing standing between the run and a discharged obligation.
const SOL_THEN_PROVABLE_DELETE: &str = "\
pseudo-Boolean proof version 3.0
f 3 ;
sol x1 x2;
del id 2;
output NONE;
conclusion SAT : x1 x2;
end pseudo-Boolean proof;
";

/// The fallback path (`write_unchecked_deletion`): the run attempted the check,
/// failed, downgraded, and exits 2. The elaborated proof re-checks to the same
/// verdict and the same exit code, because the consumer re-attempts the same
/// check and downgrades identically.
#[test]
fn a_fallback_deletion_round_trips_under_every_deletion_flag() {
    let case = case(UNPROVABLE_FORMULA, SOL_THEN_DELETE);
    // The precondition: this is the exit-2 downgrade, i.e. exactly the run
    // `tests/elaboration_verdict.rs` skips.
    let (before, _) = run(&case.formula, &case.proof, &[]);
    assert_eq!(
        before,
        Outcome {
            verdict: Some("s UNDER WEAKENED GUARANTEES SATISFIABLE".to_string()),
            code: Some(2),
        },
        "the fixture no longer exercises the unchecked-deletion fallback"
    );
    assert_round_trips(&case, &[], "fallback deletion");
}

/// The same shape in the version-2 dialect. The elaborator emits version 3 for
/// both, so this is the one place the two front ends can come apart.
#[test]
fn a_fallback_deletion_round_trips_in_the_version_2_dialect() {
    let case = case(UNPROVABLE_FORMULA, SOL_THEN_DELETE_V2);
    let (before, _) = run(&case.formula, &case.proof, &[]);
    assert_eq!(
        before.code,
        Some(2),
        "the version-2 fixture no longer exercises the fallback: {before:?}"
    );
    assert_round_trips(&case, &[], "fallback deletion (version 2)");
}

/// The requested-unchecked path (`write_core_deletions_no_subproof`): the run
/// never attempted the check. Re-checking the elaborated proof *without* `-u`
/// does attempt it and reports `s VERIFIED SATISFIABLE` — but so does
/// re-checking the input without `-u`, which is the point. The artifact
/// behaves like the proof it was elaborated from under every flag, so nothing
/// was lost in the rewrite; what differs is the flag, not the proof.
#[test]
fn a_requested_unchecked_deletion_round_trips_under_every_deletion_flag() {
    let case = case(PROVABLE_FORMULA, SOL_THEN_PROVABLE_DELETE);
    let (under_u, _) = run(&case.formula, &case.proof, &["-u"]);
    let (under_default, _) = run(&case.formula, &case.proof, &[]);
    assert_eq!(
        under_u.verdict.as_deref(),
        Some("s UNDER WEAKENED GUARANTEES SATISFIABLE"),
        "the fixture no longer skips the deletion check under -u"
    );
    assert_eq!(
        under_default.verdict.as_deref(),
        Some("s VERIFIED SATISFIABLE"),
        "the fixture's deletion is supposed to be dischargeable without -u"
    );
    assert_round_trips(&case, &["-u"], "requested unchecked deletion");
}

/// A deletion whose obligation was *dropped* is written as a bare `delc <id>;`,
/// and a deletion whose obligation was *discharged* is written with a subproof.
/// The two are distinguishable in the artifact, which is what makes a bare
/// `delc` mean "not discharged here" rather than nothing at all.
#[test]
fn a_discharged_deletion_and_a_dropped_one_are_distinguishable() {
    // Dropped: the check fails, the run falls back.
    let dropped = case(UNPROVABLE_FORMULA, SOL_THEN_DELETE);
    let text = elaborate(&dropped, &[]);
    assert_eq!(
        bare_delc_lines(&text),
        vec!["delc 1;"],
        "a dropped deletion obligation must still appear as a core deletion:\n{text}"
    );
    assert!(
        subproof_delc_lines(&text).is_empty(),
        "nothing was discharged, so nothing may claim to have been:\n{text}"
    );

    // Discharged: the same rule on a formula where the deletion is RUP.
    let discharged = case(PROVABLE_FORMULA, SOL_THEN_PROVABLE_DELETE);
    let text = elaborate(&discharged, &[]);
    assert!(
        bare_delc_lines(&text).is_empty(),
        "a discharged deletion must not be written in the form reserved for \
         dropped obligations:\n{text}"
    );
    assert_eq!(
        subproof_delc_lines(&text).len(),
        1,
        "a discharged deletion must carry its subproof:\n{text}"
    );
}

/// The downgrade cannot be recorded *in* the artifact — the format has no
/// unchecked core deletion — so the run has to say it. It says it only when
/// elaborating, because only then is there an artifact to warn about.
#[test]
fn elaborating_a_dropped_deletion_obligation_is_reported() {
    const MARKER: &str = "Elaborating a core deletion whose check was not discharged";

    let dropped = case(UNPROVABLE_FORMULA, SOL_THEN_DELETE);
    let mut args: Vec<&str> = vec!["-e"];
    let elaborated = dropped.elaborated.to_str().expect("utf-8 path").to_string();
    args.push(&elaborated);
    let (_, stderr) = run(&dropped.formula, &dropped.proof, &args);
    assert!(
        stderr.contains(MARKER),
        "the fallback wrote a `delc` the run never discharged and said nothing:\n{stderr}"
    );

    let (_, stderr) = run(&dropped.formula, &dropped.proof, &[]);
    assert!(
        !stderr.contains(MARKER),
        "a run that writes no artifact must not warn about one:\n{stderr}"
    );

    // The requested-unchecked path has no other diagnostic at all, so this is
    // the only thing that tells the user the artifact asks for more work than
    // the run did.
    let requested = case(PROVABLE_FORMULA, SOL_THEN_PROVABLE_DELETE);
    let elaborated = requested
        .elaborated
        .to_str()
        .expect("utf-8 path")
        .to_string();
    let (_, stderr) = run(
        &requested.formula,
        &requested.proof,
        &["-u", "-e", &elaborated],
    );
    assert!(
        stderr.contains(MARKER),
        "-u skipped a deletion check and the elaboration said nothing:\n{stderr}"
    );
}
