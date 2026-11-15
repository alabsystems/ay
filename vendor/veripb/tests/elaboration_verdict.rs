//! Elaborating a proof must not change what it claims.
//!
//! `-e` rewrites a proof into the restricted "kernel" fragment a simpler
//! checker can read — CakePB, in the integration harness. That artifact is what
//! a downstream consumer actually verifies, so the elaborated proof has to make
//! the *same claim* as the input: an elaboration that turned
//! `s VERIFIED UNSATISFIABLE` into `s VERIFIED SATISFIABLE`, or `BOUNDS 1 1`
//! into `BOUNDS 0 0`, would hand that consumer a different problem's answer.
//!
//! `tests/integration.rs` already elaborates every instance and re-checks the
//! result, but it asks only whether the elaborated proof is *accepted*: it calls
//! `run_veripb` with `print_verification_result: false` and passes the outcome
//! to `verify_veripb_result(_, true)`, which is satisfied by `Ok(())`. The
//! verdict line is never produced, let alone compared. So the whole suite would
//! stay green under an elaborator that preserved checkability and lost the
//! claim.
//!
//! No such divergence exists today — every accepted instance in the corpus
//! round-trips with a byte-identical verdict, which is what makes this a
//! regression test rather than a bug report. It is here because "accepted" and
//! "says the same thing" are different properties and only one of them was
//! being checked.
//!
//! Both are needed: this file does not re-check what `integration.rs` checks
//! (that the elaborated proof passes CakePB, that incorrect instances stay
//! incorrect), and `integration.rs` does not check what this file checks.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Instances the integration harness marks as not elaboratable, in either
/// comment syntax. Skipping them here rather than failing keeps this file's
/// notion of "elaboratable" the same as `tests/integration.rs`'s, so the two
/// cannot disagree about which instances are in scope.
const IGNORE_MARKERS: [&str; 4] = [
    "* INTEGRATION-TEST: ignore(elaborate)",
    "% INTEGRATION-TEST: ignore(elaborate)",
    "* INTEGRATION-TEST: ignore(both)",
    "% INTEGRATION-TEST: ignore(both)",
];

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// The formula belonging to a derivation, by the same name-matching the corpus
/// uses: `<stem>.<ext>`, or `<prefix-before-first-underscore>.<ext>`.
fn formula_for(derivation: &Path) -> Option<PathBuf> {
    let dir = derivation.parent()?;
    let stem = derivation.file_stem()?.to_str()?;
    let prefix = stem.split('_').next().unwrap_or(stem);
    for ext in ["opb", "cnf", "wcnf"] {
        for base in [stem, prefix] {
            let candidate = dir.join(format!("{base}.{ext}"));
            if candidate.is_file() {
                return Some(candidate);
            }
        }
    }
    None
}

fn verdicts(stdout: &str) -> Vec<String> {
    stdout
        .lines()
        .filter(|line| line.starts_with("s "))
        .map(str::to_string)
        .collect()
}

/// Run the checker, returning its verdict lines and exit code.
fn check(formula: &Path, derivation: &Path) -> (Vec<String>, Option<i32>) {
    let out = Command::new(env!("CARGO_BIN_EXE_veripb"))
        .arg(formula)
        .arg(derivation)
        .output()
        .expect("failed to run veripb");
    (
        verdicts(&String::from_utf8_lossy(&out.stdout)),
        out.status.code(),
    )
}

struct Outcome {
    compared: usize,
    skipped_unaccepted: usize,
    skipped_marked: usize,
    by_version: [usize; 2],
    failures: Vec<String>,
}

fn sweep(paths: &[PathBuf]) -> Outcome {
    let mut outcome = Outcome {
        compared: 0,
        skipped_unaccepted: 0,
        skipped_marked: 0,
        by_version: [0, 0],
        failures: Vec::new(),
    };
    for derivation in paths {
        let Some(formula) = formula_for(derivation) else {
            continue;
        };
        let body = std::fs::read_to_string(derivation).expect("readable derivation");
        if IGNORE_MARKERS.iter().any(|m| body.contains(m)) {
            outcome.skipped_marked += 1;
            continue;
        }

        // Only accepted proofs have a verdict to preserve. An instance under
        // `correct/` that does not verify is `integration.rs`'s problem, not
        // this file's.
        let (before, code) = check(&formula, derivation);
        if before.is_empty() || code != Some(0) {
            outcome.skipped_unaccepted += 1;
            continue;
        }

        let dir = tempfile::tempdir().expect("failed to create temporary directory");
        let elaborated = dir.path().join("elaborated.pbp");
        let status = Command::new(env!("CARGO_BIN_EXE_veripb"))
            .arg("-e")
            .arg(&elaborated)
            .arg(&formula)
            .arg(derivation)
            .output()
            .expect("failed to run veripb");
        if !status.status.success() {
            outcome.failures.push(format!(
                "{}: elaboration failed on a proof that verifies:\n{}",
                derivation.display(),
                String::from_utf8_lossy(&status.stderr)
            ));
            continue;
        }
        if !elaborated.is_file() {
            outcome.failures.push(format!(
                "{}: elaboration reported success but wrote no proof",
                derivation.display()
            ));
            continue;
        }

        let (after, after_code) = check(&formula, &elaborated);
        if after != before || after_code != Some(0) {
            outcome.failures.push(format!(
                "{}: elaboration changed the claim.\n  before: {before:?} (exit {code:?})\n   after: {after:?} (exit {after_code:?})",
                derivation.display(),
            ));
            continue;
        }

        outcome.compared += 1;
        let version = usize::from(derivation.to_string_lossy().contains("version3"));
        outcome.by_version[version] += 1;
    }
    outcome
}

/// Every accepted instance elaborates to a proof with the same verdict.
///
/// Spread over threads because it is 3 checker invocations per instance; one
/// thread takes about half a minute, eight about a second.
#[test]
fn elaboration_preserves_the_verdict() {
    let root = repo_root().join("tests/instances/correct");
    let mut paths: Vec<PathBuf> = ["version2", "version3"]
        .iter()
        .flat_map(|version| {
            std::fs::read_dir(root.join(version))
                .unwrap_or_else(|e| panic!("cannot list {}: {e}", root.join(version).display()))
                .flatten()
                .map(|entry| entry.path())
                .filter(|path| path.extension().is_some_and(|e| e == "pbp"))
        })
        .collect();
    paths.sort();
    assert!(
        paths.len() > 200,
        "found only {} correct instances; the corpus walk has gone stale and a \
         sweep over nothing would pass",
        paths.len()
    );

    let threads = std::thread::available_parallelism()
        .map(std::num::NonZeroUsize::get)
        .unwrap_or(4)
        .min(8);
    let chunk = paths.len().div_ceil(threads);
    let outcomes: Vec<Outcome> = std::thread::scope(|scope| {
        let handles: Vec<_> = paths
            .chunks(chunk)
            .map(|slice| scope.spawn(move || sweep(slice)))
            .collect();
        handles
            .into_iter()
            .map(|handle| handle.join().expect("sweep thread panicked"))
            .collect()
    });

    let failures: Vec<&String> = outcomes.iter().flat_map(|o| o.failures.iter()).collect();
    assert!(
        failures.is_empty(),
        "elaboration changed what {} proof(s) claim:\n\n{}",
        failures.len(),
        failures
            .iter()
            .map(|f| f.as_str())
            .collect::<Vec<_>>()
            .join("\n\n")
    );

    let compared: usize = outcomes.iter().map(|o| o.compared).sum();
    let marked: usize = outcomes.iter().map(|o| o.skipped_marked).sum();
    let unaccepted: usize = outcomes.iter().map(|o| o.skipped_unaccepted).sum();
    let v2: usize = outcomes.iter().map(|o| o.by_version[0]).sum();
    let v3: usize = outcomes.iter().map(|o| o.by_version[1]).sum();

    // Floors, so that a sweep which quietly stopped finding instances — or
    // stopped covering a dialect — fails instead of passing on an empty set.
    // Both dialects matter: several recent wrong verdicts were reachable in
    // version 2 only, and the elaborator emits version 3 for both.
    assert!(
        compared > 200,
        "only {compared} instance(s) were compared ({marked} marked \
         non-elaboratable, {unaccepted} did not verify); this test is no longer \
         measuring the corpus"
    );
    assert!(
        v2 > 50 && v3 > 100,
        "dialect coverage collapsed: {v2} version-2 and {v3} version-3 instances \
         compared"
    );
    assert!(
        marked < 30,
        "{marked} instances are marked non-elaboratable, far more than the \
         handful this test was written against -- if elaboration has been \
         switched off for a whole class, that is worth saying out loud rather \
         than skipping"
    );
}
