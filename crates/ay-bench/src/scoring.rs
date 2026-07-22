// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Competition-standard scoring for SAT, SMT, and CHC.
//!
//! Implements the exact scoring methods used by:
//! - **SAT Competition**: PAR-2 ([satcompetition.github.io/2024/](https://satcompetition.github.io/2024/))
//! - **SMT-COMP**: lexicographic `<e,n,w,c>` ([smt-comp.github.io/2024/rules.pdf](https://smt-comp.github.io/2024/rules.pdf))
//! - **CHC-COMP**: solved count + CPU tiebreak ([chc-comp.github.io](https://chc-comp.github.io))

use crate::error::{BenchError, Result, WithContext};
use serde::{Deserialize, Serialize};
use std::path::PathBuf;

// ===================================================================
// Competition constants
// ===================================================================

/// SAT Competition 2024 main track: 5000s wall-clock, 128 GB RAM.
pub const SAT_COMP_TIMEOUT_SEC: f64 = 5000.0;
/// SMT-COMP 2024 single-query track: 1200s (20 min), ~30 GB RAM, 4 cores.
pub const SMT_COMP_TIMEOUT_SEC: f64 = 1200.0;
/// CHC-COMP 2022 competition run: 1800s (30 min), 64 GB RAM.
pub const CHC_COMP_TIMEOUT_SEC: f64 = 1800.0;
/// HWMCC 2024/2025 standard timeout: 3600s (1 hour), single-threaded.
pub const HWMCC_TIMEOUT_SEC: f64 = 3600.0;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Competition {
    SatComp,
    SmtComp,
    ChcComp,
    HwmccComp,
}

impl Competition {
    pub fn standard_timeout(&self) -> f64 {
        match self {
            Competition::SatComp => SAT_COMP_TIMEOUT_SEC,
            Competition::SmtComp => SMT_COMP_TIMEOUT_SEC,
            Competition::ChcComp => CHC_COMP_TIMEOUT_SEC,
            Competition::HwmccComp => HWMCC_TIMEOUT_SEC,
        }
    }

    pub fn name(&self) -> &'static str {
        match self {
            Competition::SatComp => "SAT-COMP",
            Competition::SmtComp => "SMT-COMP",
            Competition::ChcComp => "CHC-COMP",
            Competition::HwmccComp => "HWMCC",
        }
    }
}

// ===================================================================
// Shared types for reading results JSON
// ===================================================================

/// Generic benchmark result item from results.json.
#[derive(Debug, Deserialize)]
pub struct ResultItem {
    /// Benchmark name or file path
    #[serde(alias = "name")]
    pub file: Option<String>,
    /// Expected verdict (sat/unsat/SAT/UNSAT)
    pub expected: Option<String>,
    /// AY actual result
    #[serde(alias = "ay_actual", alias = "ay_result", alias = "actual")]
    pub result: Option<String>,
    /// Wall-clock time in seconds
    #[serde(
        alias = "ay_elapsed_sec",
        alias = "ay_time_sec",
        alias = "elapsed_sec",
        alias = "wall_time_sec"
    )]
    pub time_sec: Option<f64>,
    /// CPU time in seconds (optional; falls back to wall time)
    pub cpu_time_sec: Option<f64>,
    /// Exit code (deserialized for schema fidelity; not used in scoring).
    #[allow(dead_code)] // serde: deserialized from JSON but not read in code
    #[serde(alias = "ay_exit_code")]
    pub exit_code: Option<i32>,
    /// Correctness flag (deserialized for schema fidelity; not used in scoring).
    #[allow(dead_code)] // serde: deserialized from JSON but not read in code
    pub correct: Option<bool>,
}

/// Top-level results JSON structure.
#[derive(Debug, Deserialize)]
pub struct ResultsFile {
    pub items: Option<Vec<ResultItem>>,
    pub benchmarks: Option<Vec<ResultItem>>,
    #[allow(dead_code)] // serde: deserialized from JSON but not read in code
    pub metrics: Option<serde_json::Value>,
    #[allow(dead_code)] // serde: deserialized from JSON but not read in code
    pub settings: Option<serde_json::Value>,
}

impl ResultsFile {
    pub fn load(path: &std::path::Path) -> Result<Self> {
        let text = std::fs::read_to_string(path)
            .with_bench_context(|| format!("reading {}", path.display()))?;
        serde_json::from_str(&text)
            .with_bench_context(|| format!("parsing JSON from {}", path.display()))
    }

    pub fn items(&self) -> &[ResultItem] {
        self.items
            .as_deref()
            .or(self.benchmarks.as_deref())
            .unwrap_or(&[])
    }
}

fn name_of(item: &ResultItem) -> &str {
    item.file.as_deref().unwrap_or("<unknown>")
}

fn actual_of(item: &ResultItem) -> &str {
    item.result.as_deref().unwrap_or("error")
}

fn wall_time_of(item: &ResultItem) -> f64 {
    item.time_sec.unwrap_or(0.0)
}

fn cpu_time_of(item: &ResultItem) -> f64 {
    item.cpu_time_sec.unwrap_or_else(|| wall_time_of(item))
}

fn is_definitive(s: &str) -> bool {
    let lower = s.to_ascii_lowercase();
    lower == "sat" || lower == "unsat"
}

fn is_sat(s: &str) -> bool {
    s.eq_ignore_ascii_case("sat")
}

fn verdicts_match(expected: &str, actual: &str) -> bool {
    expected.eq_ignore_ascii_case(actual)
}

// ===================================================================
// SAT Competition: PAR-2
// ===================================================================
//
// Source: satcompetition.github.io/2024/tracks.html
//
// "Solvers in all tracks will be ranked based on the PAR-2 score,
// which is the sum of the runtime plus twice the timeout for unsolved
// instances."
//
// Wrong answer = disqualification (binary, not a score penalty).

#[derive(Debug, Serialize)]
pub struct SatScore {
    pub par2_total: f64,
    pub par2_avg: f64,
    pub solved: u32,
    pub solved_sat: u32,
    pub solved_unsat: u32,
    pub unsolved: u32,
    pub wrong: u32,
    pub disqualified: bool,
    pub total: u32,
    pub timeout_sec: f64,
    pub wrong_answers: Vec<WrongAnswer>,
}

#[derive(Debug, Serialize)]
pub struct WrongAnswer {
    pub name: String,
    pub expected: String,
    pub actual: String,
}

pub fn score_sat(items: &[ResultItem], timeout_sec: f64) -> SatScore {
    let mut par2_total = 0.0;
    let mut solved = 0u32;
    let mut solved_sat = 0u32;
    let mut solved_unsat = 0u32;
    let mut unsolved = 0u32;
    let mut wrong = 0u32;
    let mut wrong_answers = Vec::new();

    for item in items {
        let actual = actual_of(item);
        let definitive = is_definitive(actual);
        let is_wrong = definitive
            && item
                .expected
                .as_deref()
                .is_some_and(|exp| !verdicts_match(exp, actual));

        if is_wrong {
            wrong += 1;
            wrong_answers.push(WrongAnswer {
                name: name_of(item).to_string(),
                expected: item.expected.clone().unwrap_or_default(),
                actual: actual.to_string(),
            });
            par2_total += 2.0 * timeout_sec;
            unsolved += 1;
        } else if definitive {
            par2_total += wall_time_of(item);
            solved += 1;
            if is_sat(actual) {
                solved_sat += 1;
            } else {
                solved_unsat += 1;
            }
        } else {
            par2_total += 2.0 * timeout_sec;
            unsolved += 1;
        }
    }

    let total = items.len() as u32;
    SatScore {
        par2_total: round3(par2_total),
        par2_avg: if total > 0 {
            round3(par2_total / total as f64)
        } else {
            0.0
        },
        solved,
        solved_sat,
        solved_unsat,
        unsolved,
        wrong,
        disqualified: wrong > 0,
        total,
        timeout_sec,
        wrong_answers,
    }
}

// ===================================================================
// SMT-COMP: lexicographic <e, n, w, c>
// ===================================================================
//
// Source: SMT-COMP 2024 Rules §7 (Bobot, Bromberger, Jonas)
//
// Per-benchmark: <e, n, w, c>
//   e = error count (0 or 1)
//   n = correctly solved (0 or 1)
//   w = wall-clock time if correct, else 0
//   c = CPU time if correct, else 0
//
// Division ranking (lexicographic on sums):
//   1. Fewer total errors
//   2. More total solved
//   3. Less total wall-clock time
//   4. Less total CPU time
//
// Sequential score: if cpu_time > timeout, result is discarded.

#[derive(Debug, Serialize)]
pub struct SmtScore {
    pub division: String,
    pub errors: u32,
    pub solved: u32,
    pub wall_time: f64,
    pub cpu_time: f64,
    pub total: u32,
    pub solved_sat: u32,
    pub solved_unsat: u32,
    pub timeout_count: u32,
    pub sound: bool,
    pub wrong_answers: Vec<WrongAnswer>,
}

pub fn score_smt(items: &[ResultItem], timeout_sec: f64, division: &str) -> SmtScore {
    let mut errors = 0u32;
    let mut solved = 0u32;
    let mut solved_sat = 0u32;
    let mut solved_unsat = 0u32;
    let mut timeout_count = 0u32;
    let mut wall_time = 0.0f64;
    let mut cpu_time = 0.0f64;
    let mut wrong_answers = Vec::new();

    for item in items {
        let actual = actual_of(item);
        let definitive = is_definitive(actual);
        let is_wrong = definitive
            && item
                .expected
                .as_deref()
                .is_some_and(|exp| !verdicts_match(exp, actual));

        if is_wrong {
            errors += 1;
            wrong_answers.push(WrongAnswer {
                name: name_of(item).to_string(),
                expected: item.expected.clone().unwrap_or_default(),
                actual: actual.to_string(),
            });
            continue;
        }

        if !definitive {
            if actual.eq_ignore_ascii_case("timeout") {
                timeout_count += 1;
            }
            continue;
        }

        // Sequential score: discard if CPU exceeds timeout
        let cpu = cpu_time_of(item);
        if cpu > timeout_sec {
            continue;
        }

        solved += 1;
        wall_time += wall_time_of(item);
        cpu_time += cpu;
        if is_sat(actual) {
            solved_sat += 1;
        } else {
            solved_unsat += 1;
        }
    }

    SmtScore {
        division: division.to_string(),
        errors,
        solved,
        wall_time: round3(wall_time),
        cpu_time: round3(cpu_time),
        total: items.len() as u32,
        solved_sat,
        solved_unsat,
        timeout_count,
        sound: errors == 0,
        wrong_answers,
    }
}

/// Lexicographic comparison per SMT-COMP rules.
/// Returns `Less` if `a` is better, `Greater` if `b` is better, `Equal` if tied.
pub fn compare_smt(a: &SmtScore, b: &SmtScore) -> std::cmp::Ordering {
    a.errors
        .cmp(&b.errors)
        .then(b.solved.cmp(&a.solved))
        .then(a.wall_time.total_cmp(&b.wall_time))
        .then(a.cpu_time.total_cmp(&b.cpu_time))
}

// ===================================================================
// CHC-COMP: solved count + CPU tiebreak
// ===================================================================
//
// Source: CHC-COMP 2022 report (De Angelis, Hari Govind V K)
//         doi:10.4204/EPTCS.373.5
//
// Primary: number of correctly solved benchmarks (sat + unsat)
// Tiebreaker: total CPU time of solved instances (lower is better)

#[derive(Debug, Serialize)]
pub struct ChcScore {
    pub track: String,
    pub solved: u32,
    pub solved_sat: u32,
    pub solved_unsat: u32,
    pub cpu_time: f64,
    pub unsolved: u32,
    pub wrong: u32,
    pub total: u32,
    pub timeout_sec: f64,
    pub wrong_answers: Vec<WrongAnswer>,
}

pub fn score_chc(items: &[ResultItem], timeout_sec: f64, track: &str) -> ChcScore {
    let mut solved = 0u32;
    let mut solved_sat = 0u32;
    let mut solved_unsat = 0u32;
    let mut unsolved = 0u32;
    let mut wrong = 0u32;
    let mut cpu_time = 0.0f64;
    let mut wrong_answers = Vec::new();

    for item in items {
        let actual = actual_of(item);
        let definitive = is_definitive(actual);
        let is_wrong = definitive
            && item
                .expected
                .as_deref()
                .is_some_and(|exp| !verdicts_match(exp, actual));

        if is_wrong {
            wrong += 1;
            wrong_answers.push(WrongAnswer {
                name: name_of(item).to_string(),
                expected: item.expected.clone().unwrap_or_default(),
                actual: actual.to_string(),
            });
            unsolved += 1;
        } else if definitive {
            solved += 1;
            cpu_time += cpu_time_of(item);
            if is_sat(actual) {
                solved_sat += 1;
            } else {
                solved_unsat += 1;
            }
        } else {
            unsolved += 1;
        }
    }

    ChcScore {
        track: track.to_string(),
        solved,
        solved_sat,
        solved_unsat,
        cpu_time: round3(cpu_time),
        unsolved,
        wrong,
        total: items.len() as u32,
        timeout_sec,
        wrong_answers,
    }
}

/// CHC-COMP comparison: more solved wins, then lower CPU.
pub fn compare_chc(a: &ChcScore, b: &ChcScore) -> std::cmp::Ordering {
    b.solved
        .cmp(&a.solved)
        .then(a.cpu_time.total_cmp(&b.cpu_time))
}

// ===================================================================
// HWMCC: solved count + CPU tiebreak
// ===================================================================
//
// Source: HWMCC 2020 report (Biere, Froleyks, Preiner, Tentrup)
//         doi:10.29007/fxl7
//
// Primary: number of correctly solved benchmarks (sat + unsat)
// Tiebreaker: total CPU time of solved instances (lower is better)
// Timeout: 3600s (1 hour), single-threaded

#[derive(Debug, Serialize)]
pub struct HwmccScore {
    pub track: String,
    pub solved: u32,
    pub solved_sat: u32,
    pub solved_unsat: u32,
    pub cpu_time: f64,
    pub unsolved: u32,
    pub wrong: u32,
    pub total: u32,
    pub timeout_sec: f64,
    pub wrong_answers: Vec<WrongAnswer>,
}

pub fn score_hwmcc(items: &[ResultItem], timeout_sec: f64, track: &str) -> HwmccScore {
    let mut solved = 0u32;
    let mut solved_sat = 0u32;
    let mut solved_unsat = 0u32;
    let mut unsolved = 0u32;
    let mut wrong = 0u32;
    let mut cpu_time = 0.0f64;
    let mut wrong_answers = Vec::new();

    for item in items {
        let actual = actual_of(item);
        let definitive = is_definitive(actual);
        let is_wrong = definitive
            && item
                .expected
                .as_deref()
                .is_some_and(|exp| !verdicts_match(exp, actual));

        if is_wrong {
            wrong += 1;
            wrong_answers.push(WrongAnswer {
                name: name_of(item).to_string(),
                expected: item.expected.clone().unwrap_or_default(),
                actual: actual.to_string(),
            });
            unsolved += 1;
        } else if definitive {
            solved += 1;
            cpu_time += cpu_time_of(item);
            if is_sat(actual) {
                solved_sat += 1;
            } else {
                solved_unsat += 1;
            }
        } else {
            unsolved += 1;
        }
    }

    HwmccScore {
        track: track.to_string(),
        solved,
        solved_sat,
        solved_unsat,
        cpu_time: round3(cpu_time),
        unsolved,
        wrong,
        total: items.len() as u32,
        timeout_sec,
        wrong_answers,
    }
}

/// HWMCC comparison: more solved wins, then lower CPU.
pub fn compare_hwmcc(a: &HwmccScore, b: &HwmccScore) -> std::cmp::Ordering {
    b.solved
        .cmp(&a.solved)
        .then(a.cpu_time.total_cmp(&b.cpu_time))
}

// ===================================================================
// Display formatting
// ===================================================================

impl std::fmt::Display for SatScore {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let dq = if self.disqualified {
            " DISQUALIFIED"
        } else {
            ""
        };
        write!(
            f,
            "SAT-COMP PAR-2: {:.1} ({}/{} solved, {} sat + {} unsat, {} wrong){}",
            self.par2_total,
            self.solved,
            self.total,
            self.solved_sat,
            self.solved_unsat,
            self.wrong,
            dq,
        )
    }
}

impl std::fmt::Display for SmtScore {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let sound = if self.sound { "" } else { " UNSOUND" };
        write!(
            f,
            "SMT-COMP {}: {}/{} solved ({} sat + {} unsat), {} errors, {:.1}s wall / {:.1}s cpu{}",
            self.division,
            self.solved,
            self.total,
            self.solved_sat,
            self.solved_unsat,
            self.errors,
            self.wall_time,
            self.cpu_time,
            sound,
        )
    }
}

impl std::fmt::Display for ChcScore {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "CHC-COMP {}: {}/{} solved ({} sat + {} unsat), {:.1}s cpu, {} wrong",
            self.track,
            self.solved,
            self.total,
            self.solved_sat,
            self.solved_unsat,
            self.cpu_time,
            self.wrong,
        )
    }
}

impl std::fmt::Display for HwmccScore {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "HWMCC {}: {}/{} solved ({} sat + {} unsat), {:.1}s cpu, {} wrong",
            self.track,
            self.solved,
            self.total,
            self.solved_sat,
            self.solved_unsat,
            self.cpu_time,
            self.wrong,
        )
    }
}

// ===================================================================
// CLI entry points
// ===================================================================

pub struct ScoreArgs {
    pub results_file: PathBuf,
    pub method: Competition,
    pub timeout: Option<f64>,
    pub division: Option<String>,
    pub track: Option<String>,
    pub standard: bool,
    pub json: bool,
}

pub fn cmd_score(args: ScoreArgs) -> Result<()> {
    let data = ResultsFile::load(&args.results_file)?;
    let items = data.items();

    // Validate --standard flag: timeout must match competition standard
    let standard_timeout = match args.method {
        Competition::SatComp => SAT_COMP_TIMEOUT_SEC,
        Competition::SmtComp => SMT_COMP_TIMEOUT_SEC,
        Competition::ChcComp => CHC_COMP_TIMEOUT_SEC,
        Competition::HwmccComp => HWMCC_TIMEOUT_SEC,
    };
    if args.standard {
        let t = args.timeout.unwrap_or(standard_timeout);
        if (t - standard_timeout).abs() > 0.1 {
            return Err(BenchError::InvalidArgs {
                reason: format!(
                    "--standard requires competition timeout ({standard_timeout:.0}s), got {t:.0}s"
                ),
            });
        }
    }

    let mode = if args.standard { "standard" } else { "dev" };

    if items.is_empty() {
        eprintln!("warning: 0 benchmarks in results file");
    }

    match args.method {
        Competition::SatComp => {
            let t = args.timeout.unwrap_or(SAT_COMP_TIMEOUT_SEC);
            let score = score_sat(items, t);
            println!("[{mode}, T={t:.0}s] {score}");
            if args.json {
                println!("{}", serde_json::to_string_pretty(&score)?);
            }
            if score.disqualified {
                return Err(BenchError::ScoringFailed {
                    reason: format!("disqualified: {} wrong answer(s)", score.wrong),
                });
            }
        }
        Competition::SmtComp => {
            let t = args.timeout.unwrap_or(SMT_COMP_TIMEOUT_SEC);
            let div = args.division.as_deref().unwrap_or("unknown");
            let score = score_smt(items, t, div);
            println!("[{mode}, T={t:.0}s] {score}");
            if args.json {
                println!("{}", serde_json::to_string_pretty(&score)?);
            }
            if !score.sound {
                return Err(BenchError::ScoringFailed {
                    reason: format!("unsound: {} error(s)", score.errors),
                });
            }
        }
        Competition::ChcComp => {
            let t = args.timeout.unwrap_or(CHC_COMP_TIMEOUT_SEC);
            let track = args.track.as_deref().unwrap_or("unknown");
            let score = score_chc(items, t, track);
            println!("[{mode}, T={t:.0}s] {score}");
            if args.json {
                println!("{}", serde_json::to_string_pretty(&score)?);
            }
            if score.wrong > 0 {
                return Err(BenchError::ScoringFailed {
                    reason: format!("{} wrong answer(s)", score.wrong),
                });
            }
        }
        Competition::HwmccComp => {
            let t = args.timeout.unwrap_or(HWMCC_TIMEOUT_SEC);
            let track = args.track.as_deref().unwrap_or("unknown");
            let score = score_hwmcc(items, t, track);
            println!("[{mode}, T={t:.0}s] {score}");
            if args.json {
                println!("{}", serde_json::to_string_pretty(&score)?);
            }
            if score.wrong > 0 {
                return Err(BenchError::ScoringFailed {
                    reason: format!("{} wrong answer(s)", score.wrong),
                });
            }
        }
    }

    Ok(())
}

pub fn print_standards() {
    println!(
        "\
Competition Scoring Standards
======================================================================

SAT Competition (satcompetition.github.io/2024/)
  Metric:    PAR-2 — Penalized Average Runtime, factor 2 (lower is better)
  Formula:   sum(wall_time if solved correctly, 2 * timeout if unsolved)
  Timeout:   {SAT_COMP_TIMEOUT_SEC:.0}s (main track), sequential, single core
  Memory:    128 GB
  Wrong:     Disqualification (binary — one wrong answer disqualifies)
  Proofs:    UNSAT requires DRAT/LRAT proof, SAT requires model
  Instances: 300–600 per track
  Exit:      10 = SAT, 20 = UNSAT (IPASIR convention)

SMT-COMP (smt-comp.github.io/2024/)
  Metric:    Lexicographic <errors, solved, wall-clock, cpu-time>
  Ranking:   Fewer errors > more solved > less wall-clock > less CPU
  Timeout:   {SMT_COMP_TIMEOUT_SEC:.0}s (single-query, 20 min), 4 cores
  Memory:    ~30 GB
  Sequential: if CPU time > timeout, result is discarded
  Wrong:     Error count dominates ranking (lexicographically worst)
  Variants:  24-second score, SAT-only score, UNSAT-only score
  Instances: 300+ per division (logic)

CHC-COMP (chc-comp.github.io)
  Metric:    Solved count (higher is better)
  Tiebreak:  CPU time of solved instances (lower is better)
  Timeout:   {CHC_COMP_TIMEOUT_SEC:.0}s (30 min), CPU and wall-clock
  Memory:    64 GB
  Wrong:     Investigated by organizers, solver may resubmit fix
  Instances: Varies by track (LIA-Lin, LIA-Nonlin, etc.)

HWMCC (hwmcc.github.io)
  Metric:    Solved count (higher is better)
  Tiebreak:  Total CPU time of solved instances (lower is better)
  Timeout:   {HWMCC_TIMEOUT_SEC:.0}s (1 hour), single-threaded
  Memory:    128 GB
  Format:    BTOR2 (word-level), AIGER 1.9 (bit-level)
  Wrong:     Investigated by organizers
  Tracks:    word-level BV, word-level array, bit-level safety, bit-level liveness
  Instances: 200-400 per track

References:
  SAT Competition 2024 rules: satcompetition.github.io/2024/tracks.html
  SMT-COMP 2024 rules:        smt-comp.github.io/2024/rules.pdf
  CHC-COMP 2022 report:        doi:10.4204/EPTCS.373.5
  HWMCC 2020 report:           doi:10.29007/fxl7
"
    );
}

fn round3(x: f64) -> f64 {
    (x * 1000.0).round() / 1000.0
}

// ===================================================================
// Tests
// ===================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn item(expected: Option<&str>, actual: &str, time: f64) -> ResultItem {
        ResultItem {
            file: Some("test.smt2".into()),
            expected: expected.map(String::from),
            result: Some(actual.into()),
            time_sec: Some(time),
            cpu_time_sec: Some(time),
            exit_code: None,
            correct: None,
        }
    }

    // --- SAT PAR-2 ---

    #[test]
    fn sat_all_solved() {
        let items = vec![
            item(Some("SAT"), "SAT", 1.0),
            item(Some("UNSAT"), "UNSAT", 2.0),
            item(Some("SAT"), "SAT", 3.0),
        ];
        let s = score_sat(&items, 300.0);
        assert_eq!(s.par2_total, 6.0);
        assert_eq!(s.solved, 3);
        assert_eq!(s.solved_sat, 2);
        assert_eq!(s.solved_unsat, 1);
        assert!(!s.disqualified);
    }

    #[test]
    fn sat_timeout_penalty() {
        let items = vec![
            item(Some("SAT"), "SAT", 1.0),
            item(Some("UNSAT"), "TIMEOUT", 300.0),
        ];
        let s = score_sat(&items, 300.0);
        assert_eq!(s.par2_total, 601.0);
        assert_eq!(s.unsolved, 1);
    }

    #[test]
    fn sat_wrong_disqualifies() {
        let items = vec![
            item(Some("SAT"), "UNSAT", 2.0), // wrong
        ];
        let s = score_sat(&items, 300.0);
        assert_eq!(s.wrong, 1);
        assert!(s.disqualified);
    }

    #[test]
    fn sat_no_expected_accepts() {
        let items = vec![item(None, "SAT", 5.0)];
        let s = score_sat(&items, 300.0);
        assert_eq!(s.solved, 1);
        assert_eq!(s.wrong, 0);
    }

    #[test]
    fn sat_competition_timeout() {
        let items = vec![item(Some("SAT"), "TIMEOUT", 5000.0)];
        let s = score_sat(&items, 5000.0);
        assert_eq!(s.par2_total, 10000.0);
    }

    // --- SMT-COMP ---

    #[test]
    fn smt_correct_result() {
        let items = vec![item(Some("sat"), "sat", 1.5)];
        let s = score_smt(&items, 1200.0, "QF_LIA");
        assert_eq!(s.errors, 0);
        assert_eq!(s.solved, 1);
        assert!((s.wall_time - 1.5).abs() < 0.01);
        assert!(s.sound);
    }

    #[test]
    fn smt_wrong_result() {
        let items = vec![item(Some("sat"), "unsat", 1.5)];
        let s = score_smt(&items, 1200.0, "QF_LIA");
        assert_eq!(s.errors, 1);
        assert_eq!(s.solved, 0);
        assert!(!s.sound);
    }

    #[test]
    fn smt_cpu_exceeds_timeout_discards() {
        let i = ResultItem {
            file: Some("test.smt2".into()),
            expected: Some("sat".into()),
            result: Some("sat".into()),
            time_sec: Some(500.0),
            cpu_time_sec: Some(1300.0), // exceeds 1200s
            exit_code: None,
            correct: None,
        };
        let s = score_smt(&[i], 1200.0, "QF_LIA");
        assert_eq!(s.solved, 0); // discarded
    }

    #[test]
    fn smt_errors_dominate() {
        let a_items = vec![item(Some("sat"), "sat", 1.0)]; // 0 errors, 1 solved
        let b_items = vec![item(Some("sat"), "unsat", 0.5)]; // 1 error
        let a = score_smt(&a_items, 1200.0, "QF_LIA");
        let b = score_smt(&b_items, 1200.0, "QF_LIA");
        assert!(compare_smt(&a, &b).is_lt(), "fewer errors should win");
    }

    // --- CHC-COMP ---

    #[test]
    fn chc_all_solved() {
        let items = vec![
            item(Some("sat"), "sat", 1.0),
            item(Some("unsat"), "unsat", 2.0),
        ];
        let s = score_chc(&items, 1800.0, "LIA-Lin");
        assert_eq!(s.solved, 2);
        assert_eq!(s.cpu_time, 3.0);
        assert_eq!(s.wrong, 0);
    }

    #[test]
    fn chc_unsolved_no_penalty() {
        let items = vec![
            item(Some("sat"), "sat", 1.0),
            item(Some("unsat"), "timeout", 1800.0),
        ];
        let s = score_chc(&items, 1800.0, "LIA-Lin");
        assert_eq!(s.solved, 1);
        assert_eq!(s.unsolved, 1);
        assert_eq!(s.cpu_time, 1.0); // only the solved instance
    }

    #[test]
    fn chc_more_solved_wins() {
        let a_items = vec![
            item(Some("sat"), "sat", 5.0),
            item(Some("unsat"), "unsat", 5.0),
        ];
        let b_items = vec![
            item(Some("sat"), "sat", 1.0),
            item(Some("unsat"), "timeout", 1800.0),
        ];
        let a = score_chc(&a_items, 1800.0, "LIA-Lin");
        let b = score_chc(&b_items, 1800.0, "LIA-Lin");
        assert!(compare_chc(&a, &b).is_lt(), "more solved should win");
    }

    #[test]
    fn chc_tiebreak_by_cpu() {
        let a_items = vec![item(Some("sat"), "sat", 10.0)];
        let b_items = vec![item(Some("sat"), "sat", 1.0)];
        let a = score_chc(&a_items, 1800.0, "LIA-Lin");
        let b = score_chc(&b_items, 1800.0, "LIA-Lin");
        assert_eq!(a.solved, b.solved);
        assert!(compare_chc(&a, &b).is_gt(), "lower CPU should win");
    }

    // --- HWMCC ---

    #[test]
    fn hwmcc_all_solved() {
        let items = vec![
            item(Some("sat"), "sat", 1.0),
            item(Some("unsat"), "unsat", 2.0),
        ];
        let s = score_hwmcc(&items, 3600.0, "wordlevel-bv");
        assert_eq!(s.solved, 2);
        assert_eq!(s.solved_sat, 1);
        assert_eq!(s.solved_unsat, 1);
        assert_eq!(s.cpu_time, 3.0);
        assert_eq!(s.wrong, 0);
    }

    #[test]
    fn hwmcc_unsolved_no_penalty() {
        let items = vec![
            item(Some("sat"), "sat", 1.0),
            item(Some("unsat"), "timeout", 3600.0),
        ];
        let s = score_hwmcc(&items, 3600.0, "wordlevel-bv");
        assert_eq!(s.solved, 1);
        assert_eq!(s.unsolved, 1);
        assert_eq!(s.cpu_time, 1.0);
    }

    #[test]
    fn hwmcc_wrong_answer() {
        let items = vec![item(Some("sat"), "unsat", 1.0)];
        let s = score_hwmcc(&items, 3600.0, "wordlevel-bv");
        assert_eq!(s.wrong, 1);
        assert_eq!(s.solved, 0);
        assert_eq!(s.unsolved, 1);
    }

    #[test]
    fn hwmcc_more_solved_wins() {
        let a_items = vec![
            item(Some("sat"), "sat", 5.0),
            item(Some("unsat"), "unsat", 5.0),
        ];
        let b_items = vec![
            item(Some("sat"), "sat", 1.0),
            item(Some("unsat"), "timeout", 3600.0),
        ];
        let a = score_hwmcc(&a_items, 3600.0, "wordlevel-bv");
        let b = score_hwmcc(&b_items, 3600.0, "wordlevel-bv");
        assert!(compare_hwmcc(&a, &b).is_lt(), "more solved should win");
    }
}
