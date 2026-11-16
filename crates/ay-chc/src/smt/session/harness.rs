// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Differential harness core for the `HornSmt` session (design §8 Rung 1,
//! §10.1; owner WP-4 / D).
//!
//! Three drivers share this file so the in-crate tests
//! (`session/tests/{pushpop_fuzz,diff_lra,replay}.rs`), the integration test
//! `tests/group_soundness/session_pushpop_vs_z3.rs` (through
//! `crate::testing::session_harness`) and the CLI-less board runs use ONE
//! generator, ONE z3 driver and ONE verdict comparison:
//!
//! * [`run_pushpop_fuzz`] — random Bool/QF_LRA push/pop scripts (≤ 12 vars,
//!   ≤ 40 assertions, ≤ 6 nested scopes, ≤ 30 checks) through the session's
//!   API path (`assert_persistent` / `push` / `pop` / `check_assuming`, i.e.
//!   logical scopes over activation literals) vs a from-scratch legacy
//!   `SmtContext::check_sat` of the active conjunction vs z3 on the same
//!   script.
//! * [`run_diff_lra`] — random linear conjunctions over 3–8 Real vars
//!   (bounds, sums, ITEs under Bool guards, strict/non-strict mixes,
//!   disequalities) through the PRODUCTION router path (a `Search`-lane
//!   context under `ScopedSessionMode::set(2)`, warm across a batch of 200
//!   interleaved queries drawn from a shared conjunct pool so the shim's
//!   reuse / kill / revive paths run) vs legacy vs z3.
//! * [`run_replay`] — a dumped corpus (`--chc-session-dump` / microbenchmark
//!   layout: `q_*.smt2` + `index.tsv`) in corpus order through the same warm
//!   router path vs a fresh legacy context per query vs z3 vs the verdict the
//!   original run recorded.
//!
//! Verdict agreement is mandatory whenever two sides are decided; `Unknown`
//! on either side is "no evidence" and counted. A session `Unsat` against a
//! `Sat` from legacy or z3 on a query with Real variables is additionally
//! counted as `real_false_unsat` (design §7.3 (i)).
//!
//! z3 is optional: [`Z3::find`] takes the workspace's one z3 oracle,
//! `ay_sys::z3_oracle` (`Z3_PATH`, else the first z3 on `PATH` that proves it
//! is z3, reached by path past reroute stubs); a run without z3 reports
//! `z3_available = false` and compares session vs legacy only, and a run with
//! one names it in `z3_oracle`.

use std::fmt::Write as _;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Arc;
use std::time::Duration;

use ay_core::time::Instant;

use super::{HornCheck, HornSmt, SessionConfig, SessionStats, UnknownReason};
use crate::smt::lane::ScopedSessionMode;
use crate::smt::types::{Partition, SmtResult};
use crate::smt::SmtContext;
use crate::{ChcExpr, ChcOp, ChcParser, ChcSort, ChcVar, InvariantModel};

// ---------------------------------------------------------------------------
// RNG (SplitMix64; no dependency, stable across platforms)
// ---------------------------------------------------------------------------

pub(crate) struct Rng(u64);

impl Rng {
    pub(crate) fn new(seed: u64) -> Self {
        Self(
            seed.wrapping_mul(0x9E37_79B9_7F4A_7C15)
                .wrapping_add(0xD1B5_4A32_D192_ED03),
        )
    }

    pub(crate) fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Uniform in `0..n` (`n > 0`).
    pub(crate) fn below(&mut self, n: u64) -> u64 {
        debug_assert!(n > 0);
        self.next_u64() % n
    }

    /// Uniform in `lo..=hi`.
    pub(crate) fn range(&mut self, lo: i64, hi: i64) -> i64 {
        debug_assert!(lo <= hi);
        lo + self.below((hi - lo + 1) as u64) as i64
    }

    /// `true` with probability `num / den`.
    pub(crate) fn chance(&mut self, num: u64, den: u64) -> bool {
        self.below(den) < num
    }

    pub(crate) fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len() as u64) as usize]
    }
}

// ---------------------------------------------------------------------------
// Generators
// ---------------------------------------------------------------------------

/// A Bool/Real vocabulary with sort-unique names.
#[derive(Clone)]
pub(crate) struct Vocab {
    pub(crate) reals: Vec<ChcVar>,
    pub(crate) bools: Vec<ChcVar>,
}

impl Vocab {
    pub(crate) fn new(n_reals: usize, n_bools: usize) -> Self {
        Self {
            reals: (0..n_reals)
                .map(|i| ChcVar::new(format!("x{i}"), ChcSort::Real))
                .collect(),
            bools: (0..n_bools)
                .map(|i| ChcVar::new(format!("b{i}"), ChcSort::Bool))
                .collect(),
        }
    }

    fn declarations(&self) -> String {
        let mut s = String::new();
        for v in &self.reals {
            let _ = writeln!(s, "(declare-const {} Real)", v.name);
        }
        for v in &self.bools {
            let _ = writeln!(s, "(declare-const {} Bool)", v.name);
        }
        s
    }

    fn real(&self, rng: &mut Rng) -> ChcExpr {
        ChcExpr::var(rng.pick(&self.reals).clone())
    }

    fn bool_var(&self, rng: &mut Rng) -> Option<ChcExpr> {
        if self.bools.is_empty() {
            None
        } else {
            Some(ChcExpr::var(rng.pick(&self.bools).clone()))
        }
    }
}

/// A small rational or integer constant; integer constants exercise the
/// converter's Int/Real constant fold (WP-3's eligibility rule).
fn constant(rng: &mut Rng) -> ChcExpr {
    match rng.below(6) {
        0 => ChcExpr::Int(rng.range(-6, 6) as i128),
        1 => ChcExpr::Real(rng.range(-9, 9), rng.range(2, 4)),
        _ => ChcExpr::Real(rng.range(-8, 8), 1),
    }
}

/// A non-zero coefficient.
fn coefficient(rng: &mut Rng) -> ChcExpr {
    let n = loop {
        let n = rng.range(-3, 3);
        if n != 0 {
            break n;
        }
    };
    if rng.chance(1, 4) {
        ChcExpr::Real(n, rng.range(2, 3))
    } else {
        ChcExpr::Real(n, 1)
    }
}

/// `x`, `c*x`, `x + y`, `c*x - y`, `ite(b, x, y)`.
fn linear_term(rng: &mut Rng, v: &Vocab, allow_ite: bool) -> ChcExpr {
    match rng.below(6) {
        0 | 1 => v.real(rng),
        2 => ChcExpr::mul(coefficient(rng), v.real(rng)),
        3 => ChcExpr::add(v.real(rng), v.real(rng)),
        4 => ChcExpr::sub(ChcExpr::mul(coefficient(rng), v.real(rng)), v.real(rng)),
        _ => match (allow_ite, v.bool_var(rng)) {
            (true, Some(b)) => ChcExpr::ite(b, v.real(rng), v.real(rng)),
            _ => ChcExpr::add(v.real(rng), constant(rng)),
        },
    }
}

fn compare(rng: &mut Rng, lhs: ChcExpr, rhs: ChcExpr) -> ChcExpr {
    compare_kind(rng.below(7), lhs, rhs)
}

fn compare_kind(kind: u64, lhs: ChcExpr, rhs: ChcExpr) -> ChcExpr {
    match kind {
        0 => ChcExpr::le(lhs, rhs),
        1 => ChcExpr::ge(lhs, rhs),
        2 => ChcExpr::lt(lhs, rhs),
        3 => ChcExpr::gt(lhs, rhs),
        4 => ChcExpr::eq(lhs, rhs),
        5 => ChcExpr::ne(lhs, rhs),
        _ => ChcExpr::le(lhs, rhs),
    }
}

/// One theory atom or a Bool literal.
fn atom(rng: &mut Rng, v: &Vocab) -> ChcExpr {
    let kind = rng.below(7);
    match rng.below(10) {
        0..=2 => {
            let (l, r) = (v.real(rng), constant(rng));
            compare_kind(kind, l, r)
        }
        3 | 4 => {
            let (l, r) = (linear_term(rng, v, true), constant(rng));
            compare_kind(kind, l, r)
        }
        5 => {
            let (l, r) = (v.real(rng), v.real(rng));
            compare_kind(kind, l, r)
        }
        6 => {
            let (l, r) = (linear_term(rng, v, false), linear_term(rng, v, false));
            compare_kind(kind, l, r)
        }
        7 => {
            let (l, r) = (v.real(rng), v.real(rng));
            ChcExpr::ne(l, r)
        }
        _ => match v.bool_var(rng) {
            Some(b) if rng.chance(1, 2) => ChcExpr::not(b),
            Some(b) => b,
            None => {
                let (l, r) = (v.real(rng), constant(rng));
                compare_kind(kind, l, r)
            }
        },
    }
}

/// A Bool/LRA conjunct with a little propositional structure.
pub(crate) fn gen_conjunct(rng: &mut Rng, v: &Vocab) -> ChcExpr {
    match rng.below(12) {
        0..=5 => atom(rng, v),
        6 => ChcExpr::not(atom(rng, v)),
        7 | 8 => ChcExpr::or_vec((0..rng.range(2, 3)).map(|_| atom(rng, v)).collect()),
        9 => match v.bool_var(rng) {
            Some(b) => ChcExpr::implies(b, atom(rng, v)),
            None => atom(rng, v),
        },
        10 => match v.bool_var(rng) {
            Some(b) => ChcExpr::Op(ChcOp::Iff, vec![Arc::new(b), Arc::new(atom(rng, v))]),
            None => ChcExpr::or(atom(rng, v), atom(rng, v)),
        },
        _ => ChcExpr::or(ChcExpr::and(atom(rng, v), atom(rng, v)), atom(rng, v)),
    }
}

/// One step of a push/pop script.
#[derive(Clone, Debug)]
pub(crate) enum Step {
    Push,
    Pop,
    Assert(Arc<ChcExpr>),
    Check,
}

pub(crate) struct PushPopScript {
    pub(crate) vocab: Vocab,
    pub(crate) steps: Vec<Step>,
}

/// Design §8 bounds: ≤ 12 vars, ≤ 40 assertions, ≤ 6 nested scopes, ≤ 30 checks.
pub(crate) fn gen_pushpop_script(rng: &mut Rng) -> PushPopScript {
    let n_reals = rng.range(2, 8) as usize;
    let n_bools = rng.range(0, (12 - n_reals as i64).min(4)) as usize;
    let vocab = Vocab::new(n_reals, n_bools);
    let max_asserts = rng.range(4, 40);
    let max_checks = rng.range(2, 30);
    let mut steps = Vec::new();
    let (mut asserts, mut checks, mut depth) = (0i64, 0i64, 0i64);
    while asserts < max_asserts || checks < max_checks {
        match rng.below(10) {
            0 | 1 if depth < 6 => {
                steps.push(Step::Push);
                depth += 1;
            }
            2 if depth > 0 => {
                steps.push(Step::Pop);
                depth -= 1;
            }
            3..=6 if asserts < max_asserts => {
                steps.push(Step::Assert(Arc::new(gen_conjunct(rng, &vocab))));
                asserts += 1;
            }
            _ if checks < max_checks => {
                steps.push(Step::Check);
                checks += 1;
            }
            _ => {
                if asserts < max_asserts {
                    steps.push(Step::Assert(Arc::new(gen_conjunct(rng, &vocab))));
                    asserts += 1;
                } else {
                    steps.push(Step::Check);
                    checks += 1;
                }
            }
        }
    }
    PushPopScript { vocab, steps }
}

impl PushPopScript {
    /// The SMT-LIB text z3 runs (one answer line per `Check`).
    pub(crate) fn smt2(&self, per_check_timeout_ms: u64) -> String {
        let mut s = String::new();
        s.push_str("(set-logic QF_LRA)\n");
        let _ = writeln!(s, "(set-option :timeout {per_check_timeout_ms})");
        s.push_str(&self.vocab.declarations());
        for step in &self.steps {
            match step {
                Step::Push => s.push_str("(push 1)\n"),
                Step::Pop => s.push_str("(pop 1)\n"),
                Step::Assert(e) => {
                    let _ = writeln!(s, "(assert {})", InvariantModel::expr_to_smtlib(e));
                }
                Step::Check => s.push_str("(check-sat)\n"),
            }
        }
        s
    }
}

// ---------------------------------------------------------------------------
// Verdicts, z3, reports
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

impl Verdict {
    pub(crate) fn of_smt(r: &SmtResult) -> Self {
        match r {
            SmtResult::Sat(_) => Self::Sat,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                Self::Unsat
            }
            SmtResult::Unknown => Self::Unknown,
        }
    }

    pub(crate) fn of_horn(r: &HornCheck) -> Self {
        match r {
            HornCheck::Sat(_) => Self::Sat,
            HornCheck::Unsat { .. } => Self::Unsat,
            HornCheck::Unknown(_) => Self::Unknown,
        }
    }

    fn parse(line: &str) -> Option<Self> {
        match line.trim() {
            "sat" => Some(Self::Sat),
            "unsat" => Some(Self::Unsat),
            "unknown" | "timeout" => Some(Self::Unknown),
            _ => None,
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Unsat => "unsat",
            Self::Unknown => "unknown",
        }
    }
}

/// An external z3, identity-checked and reached by its absolute path.
pub struct Z3 {
    path: PathBuf,
    identity: String,
}

impl Z3 {
    /// The workspace's z3 oracle (`ay_sys::z3_oracle`), or `None` when no
    /// program resolves that proves it is z3.
    ///
    /// An explicit choice that is wrong (`Z3_PATH` set to something that is
    /// not z3) is not "z3 absent": it is recorded in `errors`, so a run the
    /// caller asked to compare against z3 fails instead of quietly dropping
    /// its z3 leg.
    pub fn find(errors: &mut Vec<String>) -> Option<Self> {
        match ay_sys::z3_oracle::z3_oracle() {
            Ok(oracle) => Some(Self {
                path: oracle.path().to_path_buf(),
                identity: oracle.identity(),
            }),
            Err(unavailable) => {
                if unavailable.is_misconfigured() {
                    errors.push(format!("z3 oracle misconfigured: {unavailable}"));
                }
                None
            }
        }
    }

    /// Which z3 this is: banner, path, and how it was found.
    pub fn identity(&self) -> &str {
        &self.identity
    }

    /// Run z3 on `script` (stdin, then EOF) and collect its output; `None`
    /// when it cannot be spawned, fed or reaped.
    ///
    /// A z3 that stops reading early (a crash, its `-T:` limit) leaves the
    /// verdicts it printed: a short answer, not a failure of this driver, and
    /// never a SIGPIPE. A `unix_hardened` build runs with SIGPIPE at its
    /// default (terminate) disposition, so the script goes through
    /// `ChildPipeWriter`, which turns the dead reader into an `EPIPE` this
    /// ignores.
    fn run_script(&self, script: &str, total_timeout_secs: u64) -> Option<std::process::Output> {
        let mut child = Command::new(&self.path)
            .arg("-in")
            .arg(format!("-T:{total_timeout_secs}"))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .ok()?;
        match ay_sys::child_pipe::ChildPipeWriter::take_from(&mut child) {
            // The writer drops (EOF) once the script is written.
            Ok(mut stdin) => {
                let _ = stdin.write_all(script.as_bytes());
            }
            Err(_) => {
                let _ = child.kill();
                let _ = child.wait();
                return None;
            }
        }
        child.wait_with_output().ok()
    }

    /// Run `script` on stdin; returns every `sat`/`unsat`/`unknown` line in
    /// order (a process-level timeout or crash yields an empty/short list).
    pub(crate) fn run(&self, script: &str, total_timeout_secs: u64) -> Vec<Verdict> {
        let Some(out) = self.run_script(script, total_timeout_secs) else {
            return Vec::new();
        };
        let stdout = String::from_utf8_lossy(&out.stdout);
        stdout.lines().filter_map(Verdict::parse).collect()
    }

    /// Run a script whose queries are separated by `(echo "@q <i>")` markers
    /// and `(reset)`; returns one verdict per marker (Unknown when a query
    /// printed nothing, e.g. after a crash or the process timeout).
    pub(crate) fn run_marked(
        &self,
        script: &str,
        n: usize,
        total_timeout_secs: u64,
    ) -> Vec<Verdict> {
        let Some(out) = self.run_script(script, total_timeout_secs) else {
            return vec![Verdict::Unknown; n];
        };
        let stdout = String::from_utf8_lossy(&out.stdout);
        let mut verdicts = vec![Verdict::Unknown; n];
        let mut current: Option<usize> = None;
        for line in stdout.lines() {
            let line = line.trim();
            if let Some(rest) = line.strip_prefix("@q ") {
                current = rest.parse::<usize>().ok().filter(|i| *i < n);
            } else if let (Some(i), Some(v)) = (current, Verdict::parse(line)) {
                verdicts[i] = v;
            }
        }
        verdicts
    }
}

/// Outcome of one differential run.
#[derive(Debug, Default, Clone)]
pub struct DiffReport {
    pub scripts: u64,
    pub checks: u64,
    /// Both sides decided and equal (counted once per decided pair).
    pub agreements: u64,
    /// Human-readable descriptions of every disagreement (empty = pass).
    pub disagreements: Vec<String>,
    pub session_sat: u64,
    pub session_unsat: u64,
    pub session_unknown: u64,
    pub legacy_unknown: u64,
    pub z3_unknown: u64,
    /// Session `Unsat` vs a `Sat` from legacy or z3 on a query with Real vars.
    pub real_false_unsat: u64,
    pub z3_available: bool,
    /// [`Z3::identity`] of the z3 consulted; empty when none was.
    pub z3_oracle: String,
    /// Harness-level failures (assert rejected, parse failure, ...).
    pub errors: Vec<String>,
    /// Per-query session wall (µs): median / p99 / max.
    pub session_us_median: u64,
    pub session_us_p99: u64,
    pub session_us_max: u64,
    pub legacy_us_median: u64,
    /// Final stats line of the LAST session used (board columns).
    pub session_stats: String,
    /// Session `Unknown` classes.
    pub unknown_budget: u64,
    pub unknown_unsupported: u64,
    pub unknown_theory_incomplete: u64,
    pub unknown_poisoned: u64,
    pub strict_demotions: u64,
    pub reentries: u64,
    pub ext_full_reset_hits: u64,
    /// Session queries that ran past their budget, and the overrun
    /// (elapsed - budget) distribution over them, µs.
    pub overruns: u64,
    pub overrun_p99_us: u64,
    pub overrun_max_us: u64,
    /// Lock-L2 counter delta over the run (must be 0).
    pub constructions_in_verification: u64,
}

impl DiffReport {
    pub fn passed(&self) -> bool {
        self.disagreements.is_empty() && self.errors.is_empty() && self.real_false_unsat == 0
    }

    pub fn summary(&self) -> String {
        format!(
            "scripts={} checks={} agreements={} disagreements={} real_false_unsat={} \
             session[sat/unsat/unknown]={}/{}/{} legacy_unknown={} z3_unknown={} z3={} \
             errors={} session_us[med/p99/max]={}/{}/{} legacy_us_med={} \
             unknown[budget/unsupported/theory_incomplete/poisoned]={}/{}/{}/{} \
             strict_demotions={} reentries={} ext_full_reset_hits={} \
             overruns={} overrun_us[p99/max]={}/{} constructions_in_verification={} \
             z3_oracle={}",
            self.scripts,
            self.checks,
            self.agreements,
            self.disagreements.len(),
            self.real_false_unsat,
            self.session_sat,
            self.session_unsat,
            self.session_unknown,
            self.legacy_unknown,
            self.z3_unknown,
            self.z3_available,
            self.errors.len(),
            self.session_us_median,
            self.session_us_p99,
            self.session_us_max,
            self.legacy_us_median,
            self.unknown_budget,
            self.unknown_unsupported,
            self.unknown_theory_incomplete,
            self.unknown_poisoned,
            self.strict_demotions,
            self.reentries,
            self.ext_full_reset_hits,
            self.overruns,
            self.overrun_p99_us,
            self.overrun_max_us,
            self.constructions_in_verification,
            if self.z3_oracle.is_empty() {
                "none"
            } else {
                &self.z3_oracle
            },
        )
    }

    /// Record which z3 (if any) this run consults.
    fn record_z3(&mut self, z3: Option<&Z3>) {
        self.z3_available = z3.is_some();
        self.z3_oracle = z3.map(|z3| z3.identity().to_string()).unwrap_or_default();
    }

    /// Record the session-side overrun distribution from per-query walls.
    fn fold_overruns(&mut self, session_us: &[u64], budget: Duration) {
        let b = u64::try_from(budget.as_micros()).unwrap_or(u64::MAX);
        let mut over: Vec<u64> = session_us
            .iter()
            .filter(|&&t| t > b)
            .map(|&t| t - b)
            .collect();
        over.sort_unstable();
        self.overruns = over.len() as u64;
        self.overrun_p99_us = percentile(&over, 0.99);
        self.overrun_max_us = over.last().copied().unwrap_or(0);
    }

    fn fold_stats(&mut self, s: &SessionStats) {
        self.unknown_budget += s.unknown_budget;
        self.unknown_unsupported += s.unknown_unsupported;
        self.unknown_theory_incomplete += s.unknown_theory_incomplete;
        self.unknown_poisoned += s.unknown_poisoned;
        self.strict_demotions += s.strict_demotions;
        self.reentries += s.reentries;
        self.ext_full_reset_hits += s.ext_full_reset_hits;
        self.session_stats = format!("{s:?}");
    }
}

fn percentile(sorted: &[u64], q: f64) -> u64 {
    if sorted.is_empty() {
        return 0;
    }
    let idx = ((q * sorted.len() as f64).ceil() as usize).clamp(1, sorted.len()) - 1;
    sorted[idx]
}

fn has_real_vars(e: &ChcExpr) -> bool {
    e.vars().iter().any(|v| v.sort == ChcSort::Real)
}

/// Compare one check across the three sides; records agreements /
/// disagreements / the Real false-UNSAT counter.
fn compare_verdicts(
    report: &mut DiffReport,
    label: &str,
    expr: &ChcExpr,
    session: Verdict,
    legacy: Verdict,
    z3: Option<Verdict>,
) {
    report.checks += 1;
    match session {
        Verdict::Sat => report.session_sat += 1,
        Verdict::Unsat => report.session_unsat += 1,
        Verdict::Unknown => report.session_unknown += 1,
    }
    if legacy == Verdict::Unknown {
        report.legacy_unknown += 1;
    }
    if z3 == Some(Verdict::Unknown) {
        report.z3_unknown += 1;
    }
    let mut decided_pairs = 0u64;
    let mut disagree = |a: &str, va: Verdict, b: &str, vb: Verdict, report: &mut DiffReport| {
        if va != Verdict::Unknown && vb != Verdict::Unknown {
            decided_pairs += 1;
            if va != vb {
                let text = crate::smt::session::dump::script_for(expr, false);
                report.disagreements.push(format!(
                    "{label}: {a}={} {b}={}\n{text}",
                    va.as_str(),
                    vb.as_str()
                ));
                return true;
            }
        }
        false
    };
    let mut any = false;
    any |= disagree("session", session, "legacy", legacy, report);
    if let Some(z) = z3 {
        any |= disagree("session", session, "z3", z, report);
        any |= disagree("legacy", legacy, "z3", z, report);
    }
    if !any && decided_pairs > 0 {
        report.agreements += 1;
    }
    if session == Verdict::Unsat
        && (legacy == Verdict::Sat || z3 == Some(Verdict::Sat))
        && has_real_vars(expr)
    {
        report.real_false_unsat += 1;
    }
}

// ---------------------------------------------------------------------------
// Driver 1: push/pop scripts through the API path
// ---------------------------------------------------------------------------

/// Per-check budget for the session and legacy sides.
const CHECK_BUDGET: Duration = Duration::from_secs(2);

/// Run one script: returns `(session, legacy, active expr)` per check.
pub(crate) fn run_pushpop_script(
    script: &PushPopScript,
    report: &mut DiffReport,
    session_us: &mut Vec<u64>,
    legacy_us: &mut Vec<u64>,
) -> (Vec<(Verdict, Verdict, ChcExpr)>, SessionStats) {
    let mut session = HornSmt::new(SessionConfig::new(), None);
    // Scope stack of (id, expr) — the active set is the union.
    let mut scopes: Vec<Vec<(super::AssertId, Arc<ChcExpr>)>> = vec![Vec::new()];
    let mut out = Vec::new();
    for step in &script.steps {
        match step {
            Step::Push => {
                session.push();
                scopes.push(Vec::new());
            }
            Step::Pop => {
                if scopes.len() > 1 {
                    assert!(session.pop(), "session pop with an open scope");
                    scopes.pop();
                }
            }
            Step::Assert(e) => match session.assert_persistent(e, Partition::AB) {
                Ok(id) => scopes.last_mut().expect("scope").push((id, Arc::clone(e))),
                Err(UnknownReason::Unsupported(kind)) => {
                    report.errors.push(format!(
                        "assert rejected as unsupported ({kind:?}): {}",
                        InvariantModel::expr_to_smtlib(e)
                    ));
                }
                Err(other) => {
                    report.errors.push(format!(
                        "assert failed ({other:?}): {}",
                        InvariantModel::expr_to_smtlib(e)
                    ));
                }
            },
            Step::Check => {
                let mut ids: Vec<super::AssertId> =
                    scopes.iter().flatten().map(|(id, _)| *id).collect();
                ids.sort_unstable();
                ids.dedup();
                let exprs: Vec<ChcExpr> = scopes
                    .iter()
                    .flatten()
                    .map(|(_, e)| (**e).clone())
                    .collect();
                let conj = ChcExpr::and_all(exprs);
                // Each check is an independent solve: a fresh no-progress
                // breaker per side, or one tripped breaker (thread-global)
                // turns every later check on this thread into Unknown.
                let t0 = Instant::now();
                let s = {
                    let _fresh = crate::smt::ScopedNoProgressBreaker::new();
                    Verdict::of_horn(&session.check_assuming(&ids, &[], Some(CHECK_BUDGET)))
                };
                session_us.push(t0.elapsed().as_micros() as u64);
                let t1 = Instant::now();
                let l = {
                    let _fresh = crate::smt::ScopedNoProgressBreaker::new();
                    Verdict::of_smt(&SmtContext::new().check_sat_with_timeout(&conj, CHECK_BUDGET))
                };
                legacy_us.push(t1.elapsed().as_micros() as u64);
                out.push((s, l, conj));
            }
        }
    }
    let stats = session.stats().clone();
    (out, stats)
}

/// Design §8: `n_scripts` seeded random push/pop scripts (500 in CI;
/// `AY_FUZZ_N` for more), each vs legacy and (when available) vs z3.
pub fn run_pushpop_fuzz(seed: u64, n_scripts: u64, use_z3: bool) -> DiffReport {
    let civ_before = crate::smt::lane::constructions_in_verification();
    let mut report = DiffReport::default();
    let z3 = if use_z3 {
        Z3::find(&mut report.errors)
    } else {
        None
    };
    report.record_z3(z3.as_ref());
    let mut rng = Rng::new(seed);
    let mut session_us = Vec::new();
    let mut legacy_us = Vec::new();
    for i in 0..n_scripts {
        let script = gen_pushpop_script(&mut rng);
        report.scripts += 1;
        let (results, stats) =
            run_pushpop_script(&script, &mut report, &mut session_us, &mut legacy_us);
        report.fold_stats(&stats);
        let z3_verdicts = z3.as_ref().map(|z| z.run(&script.smt2(5_000), 60));
        if let Some(zv) = &z3_verdicts {
            if zv.len() != results.len() {
                report.errors.push(format!(
                    "script {i}: z3 answered {} checks, expected {}",
                    zv.len(),
                    results.len()
                ));
            }
        }
        for (k, (s, l, expr)) in results.iter().enumerate() {
            let z = z3_verdicts.as_ref().and_then(|zv| zv.get(k).copied());
            compare_verdicts(
                &mut report,
                &format!("pushpop seed={seed} script={i} check={k}"),
                expr,
                *s,
                *l,
                z,
            );
        }
    }
    session_us.sort_unstable();
    legacy_us.sort_unstable();
    report.session_us_median = percentile(&session_us, 0.5);
    report.session_us_p99 = percentile(&session_us, 0.99);
    report.session_us_max = session_us.last().copied().unwrap_or(0);
    report.legacy_us_median = percentile(&legacy_us, 0.5);
    report.fold_overruns(&session_us, CHECK_BUDGET);
    report.constructions_in_verification =
        crate::smt::lane::constructions_in_verification() - civ_before;
    report
}

// ---------------------------------------------------------------------------
// Driver 2: random conjunctions through the production router path
// ---------------------------------------------------------------------------

/// One query = a conjunction drawn from a batch pool (reuse) plus fresh
/// conjuncts (delta), 200 queries per warm session.
pub fn run_diff_lra(seed: u64, n_queries: u64, use_z3: bool) -> DiffReport {
    const BATCH: u64 = 200;
    let civ_before = crate::smt::lane::constructions_in_verification();
    let mut report = DiffReport::default();
    let z3 = if use_z3 {
        Z3::find(&mut report.errors)
    } else {
        None
    };
    report.record_z3(z3.as_ref());
    let mut rng = Rng::new(seed ^ 0xD1FF_1A2A);
    let mut session_us = Vec::new();
    let mut legacy_us = Vec::new();
    let mut done = 0u64;
    let mut batch_no = 0u64;
    while done < n_queries {
        let n = BATCH.min(n_queries - done);
        let vocab = Vocab::new(rng.range(3, 8) as usize, rng.range(1, 4) as usize);
        // Shared pool: transition-like conjuncts every query may reuse.
        let pool: Vec<Arc<ChcExpr>> = (0..rng.range(12, 30))
            .map(|_| Arc::new(gen_conjunct(&mut rng, &vocab)))
            .collect();
        let _mode = ScopedSessionMode::set(2);
        let mut ctx = SmtContext::new_search();
        let mut queries: Vec<ChcExpr> = Vec::with_capacity(n as usize);
        for _ in 0..n {
            let n_pool = rng.range(2, 8) as usize;
            let n_fresh = rng.range(0, 4) as usize;
            let mut parts: Vec<ChcExpr> = Vec::new();
            for _ in 0..n_pool {
                parts.push((**rng.pick(&pool)).clone());
            }
            for _ in 0..n_fresh {
                parts.push(gen_conjunct(&mut rng, &vocab));
            }
            queries.push(ChcExpr::and_all(parts));
        }
        let mut sides: Vec<(Verdict, Verdict)> = Vec::with_capacity(n as usize);
        for q in &queries {
            let t0 = Instant::now();
            let s = {
                let _fresh = crate::smt::ScopedNoProgressBreaker::new();
                Verdict::of_smt(&ctx.check_sat_with_timeout(q, CHECK_BUDGET))
            };
            session_us.push(t0.elapsed().as_micros() as u64);
            let t1 = Instant::now();
            let l = {
                let _fresh = crate::smt::ScopedNoProgressBreaker::new();
                Verdict::of_smt(&SmtContext::new().check_sat_with_timeout(q, CHECK_BUDGET))
            };
            legacy_us.push(t1.elapsed().as_micros() as u64);
            sides.push((s, l));
        }
        if let Some(stats) = ctx.session_stats() {
            report.fold_stats(stats);
        } else {
            report.errors.push(format!(
                "batch {batch_no}: no session was created on the Search context"
            ));
        }
        let z3_verdicts = z3.as_ref().map(|z| {
            let mut script = String::new();
            script.push_str("(set-logic QF_LRA)\n(set-option :timeout 5000)\n");
            script.push_str(&vocab.declarations());
            for q in &queries {
                script.push_str("(push 1)\n");
                for c in q.conjuncts() {
                    let _ = writeln!(script, "(assert {})", InvariantModel::expr_to_smtlib(c));
                }
                script.push_str("(check-sat)\n(pop 1)\n");
            }
            let v = z.run(&script, 120);
            if v.len() != queries.len() {
                report.errors.push(format!(
                    "batch {batch_no}: z3 answered {} queries, expected {}",
                    v.len(),
                    queries.len()
                ));
            }
            v
        });
        for (k, q) in queries.iter().enumerate() {
            let (s, l) = sides[k];
            let z = z3_verdicts.as_ref().and_then(|v| v.get(k).copied());
            compare_verdicts(
                &mut report,
                &format!("diff_lra seed={seed} batch={batch_no} query={k}"),
                q,
                s,
                l,
                z,
            );
        }
        report.scripts += 1;
        done += n;
        batch_no += 1;
    }
    session_us.sort_unstable();
    legacy_us.sort_unstable();
    report.session_us_median = percentile(&session_us, 0.5);
    report.session_us_p99 = percentile(&session_us, 0.99);
    report.session_us_max = session_us.last().copied().unwrap_or(0);
    report.legacy_us_median = percentile(&legacy_us, 0.5);
    report.fold_overruns(&session_us, CHECK_BUDGET);
    report.constructions_in_verification =
        crate::smt::lane::constructions_in_verification() - civ_before;
    report
}

// ---------------------------------------------------------------------------
// Driver 3: replay of a dumped corpus
// ---------------------------------------------------------------------------

/// One dumped query.
pub(crate) struct CorpusQuery {
    pub(crate) file: String,
    pub(crate) text: String,
    pub(crate) expr: ChcExpr,
    /// Verdict the original run recorded in `index.tsv`, if the index has it.
    pub(crate) recorded: Option<Verdict>,
}

/// The assertions of a plain `declare-const`/`assert` script, recovered from
/// `ChcParser` (a predicate-free `(assert C)` becomes the clause
/// `¬C ⇒ false`; `ChcExpr::not` is an involution on that shape, so `¬(¬C)`
/// is `C` again — an `(assert (=> A B))` comes back as `¬(A ∧ ¬B)`, the same
/// formula in a different shape).
pub(crate) fn parse_script_assertions(text: &str) -> Result<ChcExpr, String> {
    let problem = ChcParser::parse(text).map_err(|e| format!("parse: {e}"))?;
    let mut parts = Vec::new();
    for clause in problem.clauses() {
        if !clause.body.predicates.is_empty() {
            return Err("script mentions a predicate".to_owned());
        }
        if let Some(c) = &clause.body.constraint {
            parts.push(ChcExpr::not(c.clone()));
        }
    }
    Ok(ChcExpr::and_all(parts))
}

/// Read `<dir>/q_*.smt2` in name order plus the recorded verdicts of
/// `<dir>/index.tsv` (microbenchmark layout: `seq thread lane result ...`;
/// session layout: `seq thread lane_result ...`).
pub(crate) fn load_corpus(dir: &Path) -> Result<Vec<CorpusQuery>, String> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir)
        .map_err(|e| format!("{}: {e}", dir.display()))?
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| {
            p.extension().is_some_and(|x| x == "smt2")
                && p.file_name()
                    .and_then(|n| n.to_str())
                    .is_some_and(|n| n.starts_with("q_"))
        })
        .collect();
    files.sort();
    // seq -> recorded verdict
    let mut recorded: std::collections::HashMap<u64, Verdict> = std::collections::HashMap::new();
    if let Ok(index) = std::fs::read_to_string(dir.join("index.tsv")) {
        for line in index.lines() {
            let cols: Vec<&str> = line.split('\t').collect();
            let Some(seq) = cols.first().and_then(|s| s.parse::<u64>().ok()) else {
                continue;
            };
            // microbenchmark: seq thread lane result ; session: seq thread lane_result
            let v = cols
                .get(3)
                .and_then(|s| Verdict::parse(s))
                .or_else(|| cols.get(2).and_then(|s| Verdict::parse(s)));
            if let Some(v) = v {
                recorded.insert(seq, v);
            }
        }
    }
    let mut out = Vec::with_capacity(files.len());
    for path in files {
        let text =
            std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        let file = path
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or_default()
            .to_owned();
        let seq = file
            .trim_start_matches("q_")
            .split('_')
            .next()
            .and_then(|s| s.parse::<u64>().ok());
        let expr = parse_script_assertions(&text).map_err(|e| format!("{file}: {e}"))?;
        out.push(CorpusQuery {
            recorded: seq.and_then(|s| recorded.get(&s).copied()),
            file,
            text,
            expr,
        });
    }
    Ok(out)
}

/// Replay report = the diff report plus the recorded-verdict agreement.
#[derive(Debug, Default, Clone)]
pub struct ReplayReport {
    pub diff: DiffReport,
    pub queries: u64,
    /// Session vs the verdict the original run recorded (both decided).
    pub recorded_agreements: u64,
    pub recorded_disagreements: Vec<String>,
    pub z3_us_total: u64,
    /// `(file, session, legacy, z3)` per query, corpus order.
    pub per_query: Vec<(String, Verdict, Verdict, Option<Verdict>)>,
}

impl ReplayReport {
    pub fn passed(&self) -> bool {
        self.diff.passed() && self.recorded_disagreements.is_empty()
    }

    pub fn summary(&self) -> String {
        format!(
            "queries={} recorded_agreements={} recorded_disagreements={} {}",
            self.queries,
            self.recorded_agreements,
            self.recorded_disagreements.len(),
            self.diff.summary()
        )
    }
}

/// Replay `dir` (corpus order) through one warm Search-lane context vs a
/// fresh legacy context per query vs z3 (one process, `(reset)` between
/// queries) vs the recorded verdicts. `limit` caps the number of queries
/// (0 = all).
pub fn run_replay(dir: &Path, use_z3: bool, limit: usize) -> Result<ReplayReport, String> {
    let civ_before = crate::smt::lane::constructions_in_verification();
    let mut corpus = load_corpus(dir)?;
    if limit > 0 && corpus.len() > limit {
        corpus.truncate(limit);
    }
    let mut report = ReplayReport::default();
    let z3 = if use_z3 {
        Z3::find(&mut report.diff.errors)
    } else {
        None
    };
    report.diff.record_z3(z3.as_ref());
    let mut session_us = Vec::with_capacity(corpus.len());
    let mut legacy_us = Vec::with_capacity(corpus.len());
    let _mode = ScopedSessionMode::set(2);
    let mut ctx = SmtContext::new_search();
    let mut sides: Vec<(Verdict, Verdict)> = Vec::with_capacity(corpus.len());
    for q in &corpus {
        let t0 = Instant::now();
        let s = {
            let _fresh = crate::smt::ScopedNoProgressBreaker::new();
            Verdict::of_smt(&ctx.check_sat_with_timeout(&q.expr, CHECK_BUDGET))
        };
        session_us.push(t0.elapsed().as_micros() as u64);
        let t1 = Instant::now();
        let l = {
            let _fresh = crate::smt::ScopedNoProgressBreaker::new();
            Verdict::of_smt(&SmtContext::new().check_sat_with_timeout(&q.expr, CHECK_BUDGET))
        };
        legacy_us.push(t1.elapsed().as_micros() as u64);
        sides.push((s, l));
    }
    if let Some(stats) = ctx.session_stats() {
        report.diff.fold_stats(stats);
    } else if !corpus.is_empty() {
        report
            .diff
            .errors
            .push("no session was created on the Search context".to_owned());
    }
    let z3_verdicts = z3.as_ref().map(|z| {
        let mut script = String::new();
        for (i, q) in corpus.iter().enumerate() {
            let _ = writeln!(script, "(echo \"@q {i}\")");
            script.push_str("(set-option :timeout 10000)\n");
            for line in q.text.lines() {
                if line.trim_start().starts_with("(get-model)") {
                    continue;
                }
                script.push_str(line);
                script.push('\n');
            }
            script.push_str("(reset)\n");
        }
        let t = Instant::now();
        let v = z.run_marked(&script, corpus.len(), 3_600);
        report.z3_us_total = t.elapsed().as_micros() as u64;
        v
    });
    for (k, q) in corpus.iter().enumerate() {
        let (s, l) = sides[k];
        let z = z3_verdicts.as_ref().and_then(|v| v.get(k).copied());
        report.per_query.push((q.file.clone(), s, l, z));
        compare_verdicts(
            &mut report.diff,
            &format!("replay {} {}", dir.display(), q.file),
            &q.expr,
            s,
            l,
            z,
        );
        if let Some(r) = q.recorded {
            if s != Verdict::Unknown && r != Verdict::Unknown {
                if s == r {
                    report.recorded_agreements += 1;
                } else {
                    report.recorded_disagreements.push(format!(
                        "{}: session={} recorded={}",
                        q.file,
                        s.as_str(),
                        r.as_str()
                    ));
                }
            }
        }
    }
    report.queries = corpus.len() as u64;
    report.diff.scripts = 1;
    session_us.sort_unstable();
    legacy_us.sort_unstable();
    report.diff.session_us_median = percentile(&session_us, 0.5);
    report.diff.session_us_p99 = percentile(&session_us, 0.99);
    report.diff.session_us_max = session_us.last().copied().unwrap_or(0);
    report.diff.legacy_us_median = percentile(&legacy_us, 0.5);
    report.diff.fold_overruns(&session_us, CHECK_BUDGET);
    report.diff.constructions_in_verification =
        crate::smt::lane::constructions_in_verification() - civ_before;
    Ok(report)
}

// ---------------------------------------------------------------------------
// Driver 4: push/pop SMT-LIB scripts from files (the false-UNSAT repros)
// ---------------------------------------------------------------------------

/// Split SMT-LIB text into top-level forms (comments and `|..|`/`".."`
/// respected).
fn top_level_forms(text: &str) -> Vec<String> {
    let mut forms = Vec::new();
    let mut depth = 0i32;
    let mut cur = String::new();
    let mut in_str = false;
    let mut in_sym = false;
    let mut chars = text.chars();
    while let Some(c) = chars.next() {
        if in_str {
            cur.push(c);
            if c == '"' {
                in_str = false;
            }
            continue;
        }
        if in_sym {
            cur.push(c);
            if c == '|' {
                in_sym = false;
            }
            continue;
        }
        match c {
            ';' => {
                for d in chars.by_ref() {
                    if d == '\n' {
                        break;
                    }
                }
            }
            '"' => {
                in_str = true;
                cur.push(c);
            }
            '|' => {
                in_sym = true;
                cur.push(c);
            }
            '(' => {
                depth += 1;
                cur.push(c);
            }
            ')' => {
                depth -= 1;
                cur.push(c);
                if depth == 0 {
                    forms.push(cur.trim().to_owned());
                    cur.clear();
                }
            }
            _ => {
                if depth > 0 {
                    cur.push(c);
                }
            }
        }
    }
    forms
}

fn form_head(form: &str) -> &str {
    form.trim_start_matches('(')
        .split(|c: char| c.is_whitespace() || c == ')')
        .next()
        .unwrap_or("")
}

/// A push/pop script read from a file: declarations plus steps whose
/// assertions were parsed through `ChcParser` (one script per assertion).
pub(crate) fn parse_pushpop_file(text: &str) -> Result<(String, Vec<Step>), String> {
    let mut decls = String::new();
    let mut steps = Vec::new();
    for form in top_level_forms(text) {
        match form_head(&form) {
            "declare-const" | "declare-fun" => {
                decls.push_str(&form);
                decls.push('\n');
            }
            "push" | "pop" => {
                let n: usize = form
                    .trim_end_matches(')')
                    .split_whitespace()
                    .nth(1)
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(1);
                for _ in 0..n {
                    steps.push(if form_head(&form) == "push" {
                        Step::Push
                    } else {
                        Step::Pop
                    });
                }
            }
            "assert" => {
                let script = format!("(set-logic QF_LRA)\n{decls}{form}\n");
                let e = parse_script_assertions(&script)?;
                steps.push(Step::Assert(Arc::new(e)));
            }
            "check-sat" => steps.push(Step::Check),
            _ => {}
        }
    }
    Ok((decls, steps))
}

/// Replay every `*.smt2` push/pop script under `dir` through the session's
/// API path vs legacy vs z3 (the whole script, one z3 process per file).
pub fn run_pushpop_files(dir: &Path, use_z3: bool) -> Result<DiffReport, String> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir)
        .map_err(|e| format!("{}: {e}", dir.display()))?
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "smt2"))
        .collect();
    files.sort();
    let mut report = DiffReport::default();
    let z3 = if use_z3 {
        Z3::find(&mut report.errors)
    } else {
        None
    };
    report.record_z3(z3.as_ref());
    let mut session_us = Vec::new();
    let mut legacy_us = Vec::new();
    for path in files {
        let text =
            std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        let name = path
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or_default()
            .to_owned();
        let (_decls, steps) = parse_pushpop_file(&text).map_err(|e| format!("{name}: {e}"))?;
        let script = PushPopScript {
            vocab: Vocab::new(0, 0),
            steps,
        };
        report.scripts += 1;
        let (results, stats) =
            run_pushpop_script(&script, &mut report, &mut session_us, &mut legacy_us);
        report.fold_stats(&stats);
        let z3_verdicts = z3.as_ref().map(|z| {
            // z3 runs the ORIGINAL file text.
            let v = z.run(&text, 120);
            if v.len() != results.len() {
                report.errors.push(format!(
                    "{name}: z3 answered {} checks, expected {}",
                    v.len(),
                    results.len()
                ));
            }
            v
        });
        for (k, (s, l, expr)) in results.iter().enumerate() {
            let z = z3_verdicts.as_ref().and_then(|zv| zv.get(k).copied());
            compare_verdicts(
                &mut report,
                &format!("pushpop-file {name} check={k}"),
                expr,
                *s,
                *l,
                z,
            );
        }
    }
    session_us.sort_unstable();
    legacy_us.sort_unstable();
    report.session_us_median = percentile(&session_us, 0.5);
    report.session_us_p99 = percentile(&session_us, 0.99);
    report.session_us_max = session_us.last().copied().unwrap_or(0);
    report.legacy_us_median = percentile(&legacy_us, 0.5);
    Ok(report)
}

#[cfg(all(test, unix))]
mod child_pipe_tests;
