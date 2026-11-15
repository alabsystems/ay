// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! On/off agreement gate for LNH finite-model symmetry breaking
//! (`ay-dpll` `executor/lnh_symmetry.rs`).
//!
//! The pass was switched off on main by faece014b1 after it published WRONG
//! `unsat` in both postures: over "domains" that were not interchangeable
//! constants (compound terms, datatype constructors, a popped scope's
//! or-node: `l01`..`l06`, `pre07`, `pre11`, `pre13`), and through symmetry
//! clauses that outlived their check on the persistent incremental lanes
//! (2026-10-02 audit `k00`..`k11`, `M3*`, `M8b`, `L*`, `leakin_*`). That
//! commit asked for this gate before the pass returns.
//!
//! Every fixture is run through the CLI in the default posture, in
//! `--z3-mode` and under `--self-check` (a checked certificate demanded),
//! each with the pass on and off (`--dpll-no-euf-lnh`). The first line of
//! each fixture records z3 5.1.0's answers. The gate holds:
//!
//! 1. no definite answer contradicts z3, in any of the six runs;
//! 2. on and off never give opposite definite answers to the same check;
//! 3. in every posture the pass never loses a verdict: every check the run
//!    with the pass off decides, the run with it on decides too.
//!
//! The `r5_*` fixtures are the 2026-10-09 audit and verification repros, all
//! lost verdicts: a demanded certificate (`php5_produce_proofs`, and
//! `php7_6` under `--self-check`), a declined pass that still interned terms
//! (`lv5*`, `a4_lv5`, `a4_lv6`), datatype-sorted domains (`lv2c`, `lv3`),
//! an uninterpreted-sort application over a substituted argument (`a4_lv9*`,
//! `a4_lv10`), quantified problems (`a4_lv2`, `a4_lv7`), and checks after a
//! check that carried the clauses or after nested re-solves (`lv1*`, `lv2`,
//! `lv2b`, `lv4`, `m2`).
//!
//! `php7_6_symmetric_unsat` is the shape the pass exists for (it fires and
//! answers `unsat`); `V1_ufbv_lnh_unknown` was a single-check QF_UFBV `sat`
//! the pass turned into `unknown` (a Bool UF application over an argument
//! that preprocessing substituted away had no congruence fallback);
//! `crash_lra_opt_minimize_ite_k3` panicked in the LRA optimizer with or
//! without the pass.

use ntest::timeout;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use crate::spawn::OutputTimeout;

const CHILD_TIMEOUT: Duration = Duration::from_secs(90);

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/group_soundness/fixtures/lnh_on_off")
}

fn verdicts(stdout: &str) -> Vec<String> {
    stdout
        .lines()
        .map(str::trim)
        .filter(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .map(str::to_string)
        .collect()
}

/// z3 5.1.0's answers, from the fixture's first line `; z3 5.1.0: sat sat`.
fn expected(src: &str) -> Vec<String> {
    let first = src.lines().next().unwrap_or_default();
    let answers = first
        .strip_prefix("; z3 5.1.0:")
        .unwrap_or_else(|| panic!("fixture must start with `; z3 5.1.0: ...`: {first}"));
    answers.split_whitespace().map(str::to_string).collect()
}

/// Run `ay` on a private copy (the default posture writes proof files next to
/// its input).
fn run(work: &Path, name: &str, src: &str, args: &[&str]) -> Vec<String> {
    let file = work.join(name);
    std::fs::write(&file, src).expect("write fixture copy");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(args)
        .arg("-T:30")
        .arg(&file)
        .output_timeout(CHILD_TIMEOUT)
        .unwrap_or_else(|err| panic!("run ay {args:?} on {name}: {err}"));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !stderr.contains("panicked"),
        "{name} {args:?}: ay panicked:\n{stderr}"
    );
    verdicts(&String::from_utf8_lossy(&output.stdout))
}

#[test]
#[timeout(1_800_000)]
fn lnh_on_and_off_agree_with_z3_and_each_other() {
    let mut fixtures: Vec<PathBuf> = std::fs::read_dir(fixture_dir())
        .expect("fixture dir")
        .map(|entry| entry.expect("dir entry").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "smt2"))
        .collect();
    fixtures.sort();
    assert!(fixtures.len() >= 50, "fixtures missing: {fixtures:?}");
    let work = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<String> = Vec::new();
    for path in &fixtures {
        let name = path
            .file_name()
            .expect("name")
            .to_string_lossy()
            .to_string();
        let src = std::fs::read_to_string(path).expect("read fixture");
        let want = expected(&src);
        for posture in [&[][..], &["--z3-mode"][..], &["--self-check"][..]] {
            let on = run(work.path(), &name, &src, posture);
            let off_args: Vec<&str> = posture
                .iter()
                .copied()
                .chain(["--dpll-no-euf-lnh"])
                .collect();
            let off = run(work.path(), &name, &src, &off_args);
            for (label, got) in [("on", &on), ("off", &off)] {
                if got.len() != want.len() {
                    failures.push(format!(
                        "{name} {posture:?} LNH {label}: one verdict per check expected, got {got:?}"
                    ));
                }
                for (index, (got, want)) in got.iter().zip(&want).enumerate() {
                    if got != want && got != "unknown" {
                        failures.push(format!(
                            "{name} {posture:?} LNH {label}, check {index}: z3 says {want}, got {got} (all: {got_all:?})",
                            got_all = if label == "on" { &on } else { &off }
                        ));
                    }
                }
            }
            for (index, (a, b)) in on.iter().zip(&off).enumerate() {
                if a != b && a != "unknown" && b != "unknown" {
                    failures.push(format!(
                        "{name} {posture:?}, check {index}: LNH on says {a}, off says {b}"
                    ));
                }
                if a == "unknown" && b != "unknown" {
                    failures.push(format!(
                        "{name} {posture:?}, check {index}: LNH on lost the verdict `{b}` (on: {on:?}, off: {off:?})"
                    ));
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "LNH on/off gate:\n{}",
        failures.join("\n")
    );
}
