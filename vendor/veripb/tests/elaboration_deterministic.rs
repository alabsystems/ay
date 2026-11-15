//! Elaborating the same proof twice must produce the same bytes.
//!
//! The elaborated proof is the artifact a downstream consumer verifies, so it
//! ought to be a *function* of the input. It was not: `rup_php65` elaborated to
//! a different file on every run — six distinct hashes over three runs of each
//! of two binaries — differing only in permutations of the recorded RUP hints,
//! every one of which re-checked to the same verdict.
//!
//! Two independent causes, both an iteration over a hash container whose order
//! is not a function of the input:
//!
//! 1. `general_pb_watcher` and `cardinality_watcher` held their watch sets in
//!    `ahash::{HashMap, HashSet}::new()`. `ahash`'s default `RandomState` seeds
//!    itself from runtime randomness once per process, so the watch list handed
//!    to the propagator came out in a different order each run. That decides
//!    propagation order, hence the trail, hence the hints. Fixed by seeding
//!    those containers deterministically; their keys are `Lit` *values*, so a
//!    fixed seed is enough.
//! 2. `Database::add_non_obvious_proofgoals` iterated a `HashSet` keyed by
//!    `ByAddress`, i.e. by allocator address, which varies run to run under
//!    ASLR whatever the seed. That decides the order `red`/`dom`/`delc`
//!    proofgoals are generated in. Fixed by iterating in constraint-id order.
//!    (This one is not what `rup_php65` hit — that proof has no `red`, `dom` or
//!    `delc` at all — but it is the same defect and would surface on any proof
//!    that does.)
//!
//! Neither was a wrong verdict, and this test does not pretend otherwise: every
//! artifact produced under either order re-checked to the same verdict. The
//! reason to care is twofold. A consumer who receives an elaborated proof
//! cannot reproduce it, so it cannot be hash-pinned or diffed. And — the reason
//! this belongs in an audit rather than a backlog — a checker whose behaviour
//! varies run to run cannot be *tested* reliably: a defect that appears under
//! one propagation order and not another is flaky rather than absent, and the
//! randomized differential tests in this tree (`obligation_differential`,
//! `dialect_differential`) would have met such a defect only by luck.
//!
//! This runs the shipped binary rather than the library, because the
//! randomness was per *process*: two elaborations inside one test process would
//! share a seed and agree even with the bug present.

use std::path::{Path, PathBuf};
use std::process::Command;

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// The formula belonging to a derivation, by the corpus's naming.
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

/// Elaborate `derivation` into a fresh directory and return the bytes written.
fn elaborate(formula: &Path, derivation: &Path) -> Option<Vec<u8>> {
    let dir = tempfile::tempdir().expect("failed to create temporary directory");
    let out = dir.path().join("elaborated.pbp");
    let status = Command::new(env!("CARGO_BIN_EXE_veripb"))
        .arg("-e")
        .arg(&out)
        .arg(formula)
        .arg(derivation)
        .output()
        .expect("failed to run veripb");
    if !status.status.success() || !out.is_file() {
        return None;
    }
    Some(std::fs::read(&out).expect("elaborated proof is readable"))
}

/// Every corpus proof that elaborates does so byte-identically, twice running.
///
/// Two separate processes, because the randomness was per process.
#[test]
fn elaboration_is_a_function_of_its_input() {
    let root = repo_root().join("tests/instances/correct");
    let mut derivations: Vec<PathBuf> = ["version2", "version3"]
        .iter()
        .flat_map(|version| {
            std::fs::read_dir(root.join(version))
                .unwrap_or_else(|e| panic!("cannot list {}: {e}", root.join(version).display()))
                .flatten()
                .map(|entry| entry.path())
                .filter(|path| path.extension().is_some_and(|e| e == "pbp"))
        })
        .collect();
    derivations.sort();
    assert!(
        derivations.len() > 200,
        "found only {} correct instances; the corpus walk has gone stale",
        derivations.len()
    );

    let threads = std::thread::available_parallelism()
        .map(std::num::NonZeroUsize::get)
        .unwrap_or(4)
        .min(8);
    let chunk = derivations.len().div_ceil(threads);
    let results: Vec<(usize, Vec<String>)> = std::thread::scope(|scope| {
        let handles: Vec<_> = derivations
            .chunks(chunk)
            .map(|slice| {
                scope.spawn(move || {
                    let mut compared = 0usize;
                    let mut differing = Vec::new();
                    for derivation in slice {
                        let Some(formula) = formula_for(derivation) else {
                            continue;
                        };
                        let Some(first) = elaborate(&formula, derivation) else {
                            continue;
                        };
                        let Some(second) = elaborate(&formula, derivation) else {
                            continue;
                        };
                        compared += 1;
                        if first != second {
                            differing.push(format!(
                                "{}: two elaborations differ ({} vs {} bytes)",
                                derivation.display(),
                                first.len(),
                                second.len()
                            ));
                        }
                    }
                    (compared, differing)
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|handle| handle.join().expect("sweep thread panicked"))
            .collect()
    });

    let differing: Vec<&String> = results.iter().flat_map(|(_, d)| d.iter()).collect();
    assert!(
        differing.is_empty(),
        "elaboration is not a function of its input for {} proof(s):\n  {}\n\n\
         Look for an iteration over a hash container whose order is not a function \
         of the input — a randomly seeded `ahash` state, or a set keyed by \
         `ByAddress`. See this file's header for the two that were already found.",
        differing.len(),
        differing
            .iter()
            .map(|d| d.as_str())
            .collect::<Vec<_>>()
            .join("\n  ")
    );

    let compared: usize = results.iter().map(|(c, _)| c).sum();
    assert!(
        compared > 200,
        "only {compared} proof(s) were elaborated twice; this test is no longer \
         measuring the corpus"
    );
}
