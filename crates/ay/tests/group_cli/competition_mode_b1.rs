// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Competition-mode switch plumbing, CLI surface (#proof-capability B1).
//!
//! `AY_COMPETITION=1` is the generic harness env signal: it must enter
//! competition mode exactly like `--competition` (suppressing the default
//! proof-certificate emission), while an explicit `--proof FILE` still WINS
//! (documented precedence, never a clap conflict).

use ntest::timeout;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct CleanupGuard(PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn temp_path(extension: &str) -> (PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_competition_mode_b1_{}_{}.{}",
        std::process::id(),
        file_id,
        extension
    ));
    (path.clone(), CleanupGuard(path))
}

fn write_temp(contents: &str, extension: &str) -> (PathBuf, CleanupGuard) {
    let (path, cleanup) = temp_path(extension);
    std::fs::write(&path, contents).expect("write temp input");
    (path, cleanup)
}

/// Trivially unsatisfiable QF_UF instance.
const TRIVIAL_UNSAT_SMT: &str = "(set-logic QF_UF)\n\
(declare-const p Bool)\n\
(assert p)\n\
(assert (not p))\n\
(check-sat)\n";

/// The PLAIN default (`ay FILE.smt2`, no flag at all) is batteries-on: the
/// proof tracker is armed, the certificate is minted and strict-checked, and
/// the sibling `.alethe` sidecar is written and announced. This is the
/// baseline `--z3-mode` (and the env signal, and `--no-proof`) must suppress.
///
/// Owner decision, 2026-09-06: "I want batteries on by default and a flag for
/// z3 exact behavior" — the certificate is the product, so a flagless run
/// produces one. A one-day experiment with the opposite default is what these
/// pins now guard against.
#[test]
#[timeout(120_000)]
fn default_run_emits_sibling_alethe_artifact() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_UNSAT_SMT, "smt2");
    let alethe = PathBuf::from(format!("{}.alethe", input.display()));
    let _alethe_cleanup = CleanupGuard(alethe.clone());

    let output = Command::new(ay_path)
        .arg("--stats-full")
        .arg(&input)
        .output()
        .expect("spawn ay");
    assert_certified_proof_posture(&output, &alethe, "plain default");
}

/// `--rigor standard` names the same rung the plain default already sits on,
/// so it must be indistinguishable from it.
#[test]
#[timeout(120_000)]
fn rigor_standard_matches_the_plain_default() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_UNSAT_SMT, "smt2");
    let alethe = PathBuf::from(format!("{}.alethe", input.display()));
    let _alethe_cleanup = CleanupGuard(alethe.clone());

    let output = Command::new(ay_path)
        .args(["--rigor", "standard", "--stats-full"])
        .arg(&input)
        .output()
        .expect("spawn ay");
    assert_certified_proof_posture(&output, &alethe, "--rigor standard");
}

/// `--z3-mode` is the documented flag for z3-exact behaviour, and
/// `--no-proof` / `--rigor fast` reach the same proof posture: the tracker,
/// the certificate mint, the nested corroboration re-solves and the sidecar
/// are all shed. They used to leave the tracker armed with an unbudgeted
/// meter (slower than the certified default they claimed to opt out of).
#[test]
#[timeout(120_000)]
fn no_proof_and_z3_mode_shed_the_proof_cycle_like_rigor_fast() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    for flag in ["--z3-mode", "--no-proof", "--rigor=fast"] {
        let (input, _c) = write_temp(TRIVIAL_UNSAT_SMT, "smt2");
        let alethe = PathBuf::from(format!("{}.alethe", input.display()));
        let _alethe_cleanup = CleanupGuard(alethe.clone());

        let output = Command::new(ay_path)
            .arg(flag)
            .arg("--stats-full")
            .arg(&input)
            .output()
            .expect("spawn ay");
        assert_shed_proof_posture(&output, &alethe, flag);
    }
}

/// The batteries-on proof posture, as `--stats-full` reports it: `unsat`
/// published with a certificate behind it — the tracker recorded steps, the
/// mint ran and was strict-checked — and the sidecar announced and written.
/// The exact inverse of [`assert_shed_proof_posture`].
fn assert_certified_proof_posture(output: &std::process::Output, alethe: &PathBuf, label: &str) {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stdout.lines().any(|line| line.trim() == "unsat"),
        "{label} run must publish unsat, got stdout={stdout} stderr={stderr}"
    );
    assert!(
        alethe.exists(),
        "{label} run must emit the sibling .alethe certificate: stderr={stderr}"
    );
    assert!(
        stderr
            .lines()
            .any(|line| line.starts_with("c writing Alethe proof to ")),
        "{label} run must announce the sidecar: {stderr}"
    );
    assert!(
        stderr
            .lines()
            .any(|line| line.contains("c ay.proof.certificate ")
                && line.contains("ay_self_checkable=yes")),
        "{label} run must mint a certificate its own acceptance gate takes: {stderr}"
    );
    let combined = format!("{stdout}\n{stderr}");
    // NOT `:cert.proof_steps_recorded`: a query decided by propagation alone
    // records zero steps and still mints a real certificate.
    for key in [":cert.mints", ":proof.strict_check_invocations"] {
        let value = stat_value(&combined, key);
        let parsed: u64 = value
            .as_deref()
            .and_then(|v| v.parse().ok())
            .unwrap_or_else(|| panic!("{label}: no numeric {key} in stats: {combined}"));
        assert!(
            parsed > 0,
            "{label} run must do real certificate work ({key} = {parsed}): {combined}"
        );
    }
    assert_eq!(
        stat_value(&combined, ":cert.raw_admissions").as_deref(),
        Some("0"),
        "{label} run must not publish UNSAT through the raw admission lane: {combined}"
    );
    assert_ne!(
        stat_value(&combined, ":unsat_admission").as_deref(),
        Some("\"competition-raw\""),
        "{label} run must not be labelled competition-raw: {combined}"
    );
}

/// One `--stats-full` counter, by its `:key value` line.
fn stat_value(combined: &str, key: &str) -> Option<String> {
    combined.lines().find_map(|line| {
        let trimmed = line.trim();
        trimmed
            .strip_prefix(key)
            .filter(|rest| rest.starts_with(' '))
            .map(|rest| rest.trim().to_string())
    })
}

/// The shed proof posture, as `--stats-full` reports it: `unsat` published
/// through the raw admission lane, every proof-cycle meter at zero (nothing
/// recorded, minted, re-solved, or strict-checked), no sidecar announced or
/// written.
fn assert_shed_proof_posture(output: &std::process::Output, alethe: &PathBuf, label: &str) {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stdout.lines().any(|line| line.trim() == "unsat"),
        "{label} run must publish unsat, got stdout={stdout} stderr={stderr}"
    );
    assert!(
        !alethe.exists(),
        "{label} run must not write a sidecar next to the input"
    );
    assert!(
        !stderr.contains("c writing Alethe proof to "),
        "{label} run must not announce a sidecar: {stderr}"
    );
    let combined = format!("{stdout}\n{stderr}");
    let stat = |key: &str| stat_value(&combined, key);
    for key in [
        ":cert.proof_steps_recorded",
        ":cert.decisions_proof_tracked",
        ":cert.mints",
        ":cert.mint_nanos",
        ":cert.nested_corroboration_solves",
        ":cert.nested_corroboration_nanos",
        ":proof.strict_check_invocations",
    ] {
        assert_eq!(
            stat(key).as_deref(),
            Some("0"),
            "{label} run must record no proof/certificate work ({key}): {combined}"
        );
    }
    assert_eq!(
        stat(":cert.raw_admissions").as_deref(),
        Some("1"),
        "{label} run publishes UNSAT through the raw admission lane: {combined}"
    );
    assert_eq!(
        stat(":unsat_admission").as_deref(),
        Some("\"competition-raw\""),
        "{label}: the raw admission class must be labelled: {combined}"
    );
}

/// A QF_LRA optimization script: `(maximize ...)` drives
/// `optimize_one_objective` -> `check_sat_assuming_with_publication` ->
/// `solve_with_assumptions_for_theory`, the lane whose bookkeeping-budget
/// setter was unguarded.
const LRA_MAXIMIZE_SMT: &str = "(set-logic QF_LRA)\n\
(declare-const x Real)\n\
(assert (<= (* 2 x) 10))\n\
(assert (>= x 0))\n\
(maximize x)\n\
(check-sat)\n\
(get-objectives)\n";

/// The shed posture must never ABORT. An executor can carry a best-effort
/// proof-reconstruction budget while `begin_public_solve` has shed the
/// tracker; the `DpllT` built for the optimization lane then owns no clause
/// trace, and ay-sat's `LiveTraceForBudget` lifecycle check refuses a
/// bookkeeping budget without one. The setter in `run_dpll_with_models!` was
/// the one site that called it unconditionally, so a plain `ay opt.smt2`
/// (and `--rigor fast`, and `--no-proof`) killed the process with
/// "BUG: a proof bookkeeping budget requires one live synthesized clause
/// trace" instead of answering. Every posture must answer, and identically.
#[test]
#[timeout(120_000)]
fn lra_optimization_answers_in_every_posture() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(LRA_MAXIMIZE_SMT, "smt2");
    let alethe = PathBuf::from(format!("{}.alethe", input.display()));
    let _alethe_cleanup = CleanupGuard(alethe);

    for flags in [
        &[][..],
        &["--rigor", "fast"][..],
        &["--no-proof"][..],
        &["--z3-mode"][..],
        &["--rigor", "standard"][..],
    ] {
        let output = Command::new(ay_path)
            .args(["-T:20", "--quiet"])
            .args(flags)
            .arg(&input)
            .output()
            .expect("spawn ay");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let label = format!("{flags:?}");
        assert!(
            !stderr.contains("panicked at"),
            "{label}: the solver aborted instead of answering: {stderr}"
        );
        assert!(
            stdout.lines().any(|line| line.trim() == "sat"),
            "{label}: expected sat: stdout={stdout} stderr={stderr}"
        );
        assert!(
            stdout.contains("(objectives"),
            "{label}: expected the objective block: stdout={stdout} stderr={stderr}"
        );
        assert_eq!(
            output.status.code(),
            Some(0),
            "{label}: exit code: stdout={stdout} stderr={stderr}"
        );
    }
}

#[path = "competition_mode_b1/memout_fixtures.rs"]
mod memout_fixtures;
use memout_fixtures::{memory_hungry_cnf, memory_hungry_smt, MEMORY_HUNGRY_CNF_MIN_BYTES};

/// The memory-budget verdict follows the INPUT FORMAT, not the posture: an
/// SMT-LIB memout is `unknown` + `(:reason-unknown "memout")` (exit 124) at
/// every rung. `--rigor fast` / `--competition` used to answer it in DIMACS
/// grammar (`c memout` / `s UNKNOWN`, exit 0), which no SMT-LIB consumer can
/// parse — and the fast rung's proof posture is now the plain default.
#[test]
#[timeout(120_000)]
fn smt_memout_prints_smtlib_grammar_at_every_posture() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(&memory_hungry_smt(), "smt2");
    let alethe = PathBuf::from(format!("{}.alethe", input.display()));
    let _alethe_cleanup = CleanupGuard(alethe.clone());

    for flags in [
        &[][..],
        &["--rigor", "fast"][..],
        &["--competition"][..],
        &["--rigor", "standard"][..],
    ] {
        let output = Command::new(ay_path)
            .args(["--quiet", "--memory", "64", "-T:20"])
            .args(flags)
            .arg(&input)
            .env_remove("AY_INTERNAL_SATCOMP_WRAPPER")
            .env_remove("AY_COMPETITION")
            .env_remove("AY_SAT_COMPETITION_PROFILE")
            .env_remove("AY_SAT_PROFILE_ID")
            .output()
            .expect("spawn ay");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let label = format!("{flags:?}");
        // The property that must hold on EVERY outcome: SMT-LIB input never
        // gets the DIMACS grammar.
        assert!(
            !stdout.lines().any(|line| line.trim() == "s UNKNOWN")
                && !stdout.contains("c memout")
                && !stderr.contains("c memout"),
            "{label}: SMT-LIB input answered in DIMACS grammar: stdout={stdout} stderr={stderr}"
        );
        // And the memout itself, in SMT-LIB grammar.
        assert_eq!(
            stdout.trim(),
            "unknown",
            "{label}: expected the memout verdict: stdout={stdout} stderr={stderr}"
        );
        assert!(
            stderr.contains("(:reason-unknown \"memout\")"),
            "{label}: expected the SMT-LIB memout reason: stderr={stderr}"
        );
        assert_eq!(
            output.status.code(),
            Some(124),
            "{label}: an SMT-LIB memout keeps the resource-exhaustion exit code: stdout={stdout} stderr={stderr}"
        );
    }
}

/// DIMACS input keeps its own grammar: `c memout` / `s UNKNOWN` at every
/// posture (as its timeout path already prints), exit 0 under `--rigor fast`
/// and 124 for a plain run.
///
/// The memout must be forced, not raced. This test used to run the 2-clause
/// contradiction `1`, `-1`, whose counted heap stays under 1 MiB, so the
/// allocator ceiling never fired and only the memory watchdog's first poll
/// (RSS over the budget) could end the run. When the scheduler held that
/// thread back, the solve answered first, correctly, `s UNSATISFIABLE`: 12 of
/// 40 `--rigor fast` runs under CPU contention on 2026-10-07, 9 of 40 on a
/// build of the commit that added this test. [`memory_hungry_cnf`]'s input
/// buffer alone is over the budget, so no verdict can precede the memout.
#[test]
#[timeout(120_000)]
fn dimacs_memout_prints_sat_competition_grammar_at_every_posture() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let cnf = memory_hungry_cnf();
    assert!(
        cnf.len() > MEMORY_HUNGRY_CNF_MIN_BYTES,
        "the memout fixture must dwarf the 1 MiB budget, or the run races the watchdog: {} bytes",
        cnf.len()
    );
    for (flags, expected_exit) in [(&[][..], 124), (&["--rigor", "fast"][..], 0)] {
        let (input, _c) = write_temp(&cnf, "cnf");
        let drat = PathBuf::from(format!("{}.drat", input.display()));
        let _drat_cleanup = CleanupGuard(drat);
        // The allocator's hard ceiling refuses the buffer the input is read
        // into, on the reading thread, before any clause is parsed.
        let output = Command::new(ay_path)
            .args(["--quiet", "--memory", "1", "-T:20"])
            .args(flags)
            .arg(&input)
            .env_remove("AY_INTERNAL_SATCOMP_WRAPPER")
            .env_remove("AY_COMPETITION")
            .env_remove("AY_SAT_COMPETITION_PROFILE")
            .env_remove("AY_SAT_PROFILE_ID")
            .output()
            .expect("spawn ay");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let label = format!("{flags:?}");
        assert!(
            !stdout.lines().any(|line| line.trim().starts_with("s ") && line.trim() != "s UNKNOWN"),
            "{label}: a decisive verdict preceded the memout, so the budget did not end the run: stdout={stdout} stderr={stderr}"
        );
        assert!(
            stdout.lines().any(|line| line.trim() == "s UNKNOWN")
                && stdout.lines().any(|line| line.trim() == "c memout"),
            "{label}: DIMACS memout must print `c memout` / `s UNKNOWN`: stdout={stdout} stderr={stderr}"
        );
        assert!(
            !stdout.lines().any(|line| line.trim() == "unknown")
                && !stderr.contains("(:reason-unknown \"memout\")"),
            "{label}: DIMACS memout must not use the SMT-LIB grammar: stdout={stdout} stderr={stderr}"
        );
        assert_eq!(
            output.status.code(),
            Some(expected_exit),
            "{label}: DIMACS memout exit code: stdout={stdout} stderr={stderr}"
        );
    }
}

/// `AY_COMPETITION=1` (no flag at all) enters competition mode: the default
/// proof-certificate emission is suppressed. The verdict remains sound and
/// fail-closed — in v1 (pre-B3 raw admission) an UNSAT may degrade to
/// `unknown`; it must never publish anything else.
#[test]
#[timeout(120_000)]
fn ay_competition_env_suppresses_default_proof_artifact() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_UNSAT_SMT, "smt2");
    let alethe = PathBuf::from(format!("{}.alethe", input.display()));
    let _alethe_cleanup = CleanupGuard(alethe.clone());

    let output = Command::new(ay_path)
        .env("AY_COMPETITION", "1")
        .arg(&input)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let verdict = stdout
        .lines()
        .map(str::trim)
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .unwrap_or_default()
        .to_string();
    assert!(
        verdict == "unsat" || verdict == "unknown",
        "competition-mode UNSAT must stay fail-closed (unsat or unknown), \
         got stdout={stdout} stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        !alethe.exists(),
        "AY_COMPETITION=1 must suppress the default .alethe emission"
    );
}

/// Documented precedence: an explicit `--proof FILE` WINS over competition
/// mode — even with the env signal set, the run restores the certified lane,
/// publishes `unsat`, and writes the requested proof.
#[test]
#[timeout(120_000)]
fn explicit_proof_flag_wins_over_competition_env() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_UNSAT_SMT, "smt2");
    let (proof, _proof_cleanup) = temp_path("alethe");

    let output = Command::new(ay_path)
        .env("AY_COMPETITION", "1")
        .arg("--proof")
        .arg(&proof)
        .arg(&input)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.lines().any(|line| line.trim() == "unsat"),
        "--proof must win over AY_COMPETITION=1 and publish certified unsat, \
         got stdout={stdout} stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let proof_len = std::fs::metadata(&proof).map(|m| m.len()).unwrap_or(0);
    assert!(
        proof_len > 0,
        "--proof must still write the requested certificate under \
         AY_COMPETITION=1"
    );
}
