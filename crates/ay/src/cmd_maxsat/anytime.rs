// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Anytime reporting for `ay maxsat solve`: what AY prints when it stops
//! holding a model it has not proven optimal.
//!
//! The MaxSAT Evaluation credits a non-optimal model only under
//! `s SATISFIABLE` (MSE 2022+ output rules); `s UNKNOWN` with a `v` line scores
//! nothing. But `s SATISFIABLE` is a claim the evaluation grades: a model that
//! falsifies a hard clause, or whose cost differs from the last `o` line, is a
//! wrong answer, and the anytime tracks disqualify on a wrong answer. So the
//! model is re-checked against the instance on disk before it is claimed
//! (every hard clause satisfied, cost equal to the reported `o`), within a
//! bounded time, and withheld (`s UNKNOWN`) whenever that check fails or
//! cannot finish.
//!
//! The evaluation stops anytime runs with SIGTERM, and AY can overrun its own
//! deadline (an engine phase that does not poll, a multi-GB instance still
//! being read). Both end the same way: a stop request is a flag the solve
//! polls, and a watchdog thread answers in the solver's place
//! [`STOP_GRACE`] later from the model of the last `o` line. Exactly one `s`
//! line is printed, by whichever side wins [`Reporter::claim`], and the
//! process exits 0.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

/// What re-checking an incumbent against the instance found.
#[derive(Debug, PartialEq, Eq)]
pub(super) enum IncumbentAudit {
    /// Every hard clause is satisfied and the model costs exactly the
    /// reported amount: the model may be claimed as `s SATISFIABLE`.
    Clean,
    /// The model is not what it claims to be (a hard clause is falsified or
    /// the cost differs). A soundness alarm: never report it.
    Alarm(String),
    /// The check did not finish (out of time, or the file could not be read
    /// again). Fail closed: the model is withheld.
    Incomplete(String),
}

/// How long the incumbent audit may run once AY has decided to stop.
///
/// The audit is one streaming pass over the instance, cheaper than the parse
/// that built the solver, so twice the parse time is ample; the floor covers
/// small files on a busy machine, and the cap keeps a multi-GB instance from
/// spending the evaluator's SIGTERM-to-SIGKILL grace on a check that would be
/// killed anyway (that run reports `s UNKNOWN`, which it did before this
/// audit existed).
pub(super) fn audit_budget(parse_elapsed: Duration) -> Duration {
    const FLOOR: Duration = Duration::from_secs(2);
    const CAP: Duration = Duration::from_secs(10);
    parse_elapsed.saturating_mul(2).clamp(FLOOR, CAP)
}

/// How often (in clauses) the audit looks at the clock.
const CLOCK_STRIDE: u64 = 1024;

/// Re-check `model` (indexed by DIMACS variable, index 0 unused) against the
/// WCNF at `path`: every hard clause satisfied and the soft cost equal to
/// `reported_cost`. Stops with [`IncumbentAudit::Incomplete`] at `stop_at`.
pub(super) fn audit_incumbent(
    path: &Path,
    model: &[bool],
    reported_cost: u64,
    stop_at: Option<Instant>,
) -> IncumbentAudit {
    let val = |lit: i32| -> bool {
        let assigned = model
            .get(lit.unsigned_abs() as usize)
            .copied()
            .unwrap_or(false);
        if lit > 0 {
            assigned
        } else {
            !assigned
        }
    };
    let mut violated_hard: Option<Vec<i32>> = None;
    let mut n_hard: u64 = 0;
    let mut seen: u64 = 0;
    let mut computed: u64 = 0;
    let mut overflow = false;
    let res = super::stream_wcnf_file(path, &mut |weight, lits| {
        seen += 1;
        if seen.is_multiple_of(CLOCK_STRIDE) && stop_at.is_some_and(|t| Instant::now() >= t) {
            anyhow::bail!("out of time after {seen} clauses");
        }
        let satisfied = lits.iter().any(|&l| val(l));
        match weight {
            None => {
                n_hard += 1;
                if violated_hard.is_none() && !satisfied {
                    violated_hard = Some(lits.to_vec());
                }
            }
            Some(w) => {
                if !satisfied {
                    match computed.checked_add(w) {
                        Some(c) => computed = c,
                        None => overflow = true,
                    }
                }
            }
        }
        Ok(())
    });
    if let Err(err) = res {
        return IncumbentAudit::Incomplete(format!("{err:#}"));
    }
    if let Some(c) = violated_hard {
        let head: Vec<i32> = c.iter().take(8).copied().collect();
        return IncumbentAudit::Alarm(format!(
            "HARD_VIOLATED: the incumbent falsifies a hard clause {head:?} (of {n_hard} hards)"
        ));
    }
    if overflow || computed != reported_cost {
        return IncumbentAudit::Alarm(format!(
            "COST_MISMATCH: reported o {reported_cost} but the incumbent costs {}",
            if overflow {
                "more than u64::MAX".to_string()
            } else {
                computed.to_string()
            }
        ));
    }
    IncumbentAudit::Clean
}

/// The MSE `v` line: `v ` followed by one `0`/`1` per variable 1..=num_vars.
pub(super) fn assignment_line(num_vars: usize, model: &[bool]) -> String {
    let mut line = String::with_capacity(num_vars + 2);
    line.push_str("v ");
    for var in 1..=num_vars {
        line.push(if model.get(var).copied().unwrap_or(false) {
            '1'
        } else {
            '0'
        });
    }
    line
}

/// Write the final answer for a stop without an optimality proof.
///
/// `incumbent` is the best model with its cost and the result of auditing it.
/// Exactly one `s` line is written. A clean incumbent is reported as
/// `s SATISFIABLE` preceded by its `o` line (unless `last_printed` already
/// says it) and followed by its `v` line; anything else is `s UNKNOWN`.
pub(super) fn write_unproven_answer(
    out: &mut dyn Write,
    num_vars: usize,
    incumbent: Option<(u64, &[bool], &IncumbentAudit)>,
    last_printed: Option<u64>,
) -> std::io::Result<()> {
    match incumbent {
        Some((cost, model, IncumbentAudit::Clean)) => {
            if last_printed != Some(cost) {
                writeln!(out, "o {cost}")?;
            }
            writeln!(out, "s SATISFIABLE")?;
            writeln!(out, "{}", assignment_line(num_vars, model))?;
        }
        Some((_, _, IncumbentAudit::Alarm(reason))) => {
            eprintln!("c SOUNDNESS-ALARM[incumbent/{reason}]");
            eprintln!(
                "c SOUNDNESS-ALARM: refusing to report the incumbent; answering UNKNOWN. \
                 An unsolved instance costs one solve, a wrong answer is disqualifying."
            );
            writeln!(out, "s UNKNOWN")?;
        }
        Some((_, _, IncumbentAudit::Incomplete(why))) => {
            eprintln!("c anytime: incumbent audit did not finish ({why}); withholding it");
            writeln!(out, "s UNKNOWN")?;
        }
        None => writeln!(out, "s UNKNOWN")?,
    }
    out.flush()
}

/// Grace between a stop request (SIGTERM/SIGINT) or AY's own deadline and the
/// watchdog answering in the solver's place. The cooperative path (the engine
/// polls the same stop flag) normally answers well within it.
pub(super) const STOP_GRACE: Duration = Duration::from_secs(1);

/// The single owner of `ay maxsat solve`'s answer lines.
///
/// Every `o` line goes through [`Reporter::improved`], and whoever prints the
/// `s` line — the main thread when the solve returns, or the watchdog when it
/// does not — must first win [`Reporter::claim`]. After a claim no `o` line is
/// printed, so stdout carries exactly one `s` line, after every `o` line.
pub(super) struct Reporter {
    state: Mutex<ReporterState>,
}

#[derive(Default)]
struct ReporterState {
    answered: bool,
    last_printed: Option<u64>,
    /// The model of the last `o` line printed.
    best: Option<(u64, Vec<bool>)>,
    num_vars: usize,
    audit_budget: Duration,
}

/// What the winner of [`Reporter::claim`] answers from.
pub(super) struct Claim {
    pub(super) last_printed: Option<u64>,
    pub(super) best: Option<(u64, Vec<bool>)>,
    pub(super) num_vars: usize,
    pub(super) audit_budget: Duration,
}

impl Reporter {
    pub(super) fn new() -> Self {
        Self {
            state: Mutex::new(ReporterState {
                audit_budget: audit_budget(Duration::ZERO),
                ..ReporterState::default()
            }),
        }
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, ReporterState> {
        // A panic while holding the lock leaves plain data behind; the answer
        // must still be printable.
        self.state.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// Record the instance size (for the `v` line) and the audit budget once
    /// the instance has been read.
    pub(super) fn set_instance(&self, num_vars: usize, audit_budget: Duration) {
        let mut s = self.lock();
        s.num_vars = num_vars;
        s.audit_budget = audit_budget;
    }

    /// The engine found a better model: print its `o` line and keep the model,
    /// unless the answer has already been claimed.
    pub(super) fn improved(&self, out: &mut dyn Write, cost: u64, model: &[bool]) {
        let mut s = self.lock();
        if s.answered || s.last_printed.is_some_and(|c| c <= cost) {
            return;
        }
        if writeln!(out, "o {cost}")
            .and_then(|()| out.flush())
            .is_err()
        {
            return;
        }
        s.last_printed = Some(cost);
        match &mut s.best {
            Some((c, m)) => {
                *c = cost;
                m.clear();
                m.extend_from_slice(model);
            }
            None => s.best = Some((cost, model.to_vec())),
        }
    }

    /// Take the right to print the `s` line. `None` when it is already taken.
    pub(super) fn claim(&self) -> Option<Claim> {
        let mut s = self.lock();
        if s.answered {
            return None;
        }
        s.answered = true;
        Some(Claim {
            last_printed: s.last_printed,
            best: s.best.take(),
            num_vars: s.num_vars,
            audit_budget: s.audit_budget,
        })
    }

    fn answered(&self) -> bool {
        self.lock().answered
    }
}

/// The thread that lost [`Reporter::claim`] waits here for the winner to end
/// the process.
pub(super) fn wait_for_the_answer() -> ! {
    loop {
        std::thread::park();
    }
}

/// SIGTERM and SIGINT as a flag the solve polls (the MaxSAT Evaluation stops
/// anytime runs with SIGTERM). Installing it takes SIGTERM over from the
/// process default, which killed the run with no `s` or `v` line.
pub(super) fn install_stop_request() -> anyhow::Result<Arc<AtomicBool>> {
    let flag = Arc::new(AtomicBool::new(false));
    #[cfg(unix)]
    {
        use anyhow::Context as _;
        for signal in [signal_hook::consts::SIGTERM, signal_hook::consts::SIGINT] {
            signal_hook::flag::register(signal, Arc::clone(&flag))
                .context("failed to register a stop-signal flag")?;
        }
        ay_sys::early_sigterm::hand_over_sigterm();
    }
    Ok(flag)
}

/// When the watchdog must answer in the solver's place: [`STOP_GRACE`] after
/// the first stop request it saw, or after the deadline, whichever is first.
fn watchdog_due(stop_seen: Option<Instant>, deadline: Option<Instant>) -> Option<Instant> {
    let a = stop_seen.map(|t| t + STOP_GRACE);
    let b = deadline.and_then(|d| d.checked_add(STOP_GRACE));
    match (a, b) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (a, b) => a.or(b),
    }
}

/// Wait until the watchdog is due, then try to claim the answer. `None`
/// when the main thread claimed it first.
fn watch(reporter: &Reporter, stop: &AtomicBool, deadline: Option<Instant>) -> Option<Claim> {
    let mut stop_seen: Option<Instant> = None;
    loop {
        if reporter.answered() {
            return None;
        }
        let now = Instant::now();
        if stop_seen.is_none() && stop.load(Ordering::Acquire) {
            stop_seen = Some(now);
        }
        if watchdog_due(stop_seen, deadline).is_some_and(|due| now >= due) {
            return reporter.claim();
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

/// Print the answer for `claim`: the audited model of the last `o` line under
/// `s SATISFIABLE`, else `s UNKNOWN`.
pub(super) fn answer_from_claim(
    out: &mut dyn Write,
    file: &Path,
    claim: &Claim,
) -> std::io::Result<()> {
    let audit = claim.best.as_ref().map(|(cost, model)| {
        audit_incumbent(
            file,
            model,
            *cost,
            Some(Instant::now() + claim.audit_budget),
        )
    });
    let incumbent = match (&claim.best, &audit) {
        (Some((cost, model)), Some(audit)) => Some((*cost, model.as_slice(), audit)),
        _ => None,
    };
    write_unproven_answer(out, claim.num_vars, incumbent, claim.last_printed)
}

/// Start the thread that answers when the solver does not: a stop request
/// the engine has not honoured within [`STOP_GRACE`], or an overrun of AY's
/// own deadline (including while the instance is still being read). It
/// prints the model of the last `o` line (audited) or `s UNKNOWN`, then ends
/// the process with status 0.
pub(super) fn spawn_watchdog(
    reporter: Arc<Reporter>,
    stop: Arc<AtomicBool>,
    deadline: Option<Instant>,
    file: PathBuf,
) -> anyhow::Result<()> {
    std::thread::Builder::new()
        .name("maxsat-answer".into())
        .spawn(move || {
            let Some(claim) = watch(&reporter, &stop, deadline) else {
                return;
            };
            eprintln!(
                "c anytime: the solve did not return in time; answering from the last o line"
            );
            let _ = answer_from_claim(&mut std::io::stdout().lock(), &file, &claim);
            std::process::exit(0);
        })
        .map(|_| ())
        .map_err(|e| anyhow::anyhow!("failed to start the answer watchdog: {e}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    struct Scratch(PathBuf);

    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn wcnf(label: &str, text: &str) -> (Scratch, PathBuf) {
        let dir = std::env::temp_dir().join(format!(
            "ay-maxsat-anytime-{label}-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        std::fs::create_dir_all(&dir).expect("mkdir");
        let path = dir.join("in.wcnf");
        std::fs::write(&path, text).expect("write");
        (Scratch(dir), path)
    }

    // h (1 v 2), h (-1 v -2), soft 3:(1), soft 5:(2)
    const SMALL: &str = "h 1 2 0\nh -1 -2 0\n3 1 0\n5 2 0\n";

    fn render(num_vars: usize, inc: Option<(u64, &[bool], &IncumbentAudit)>) -> String {
        let mut out = Vec::new();
        write_unproven_answer(&mut out, num_vars, inc, None).expect("write");
        String::from_utf8(out).expect("utf8")
    }

    #[test]
    fn clean_incumbent_is_reported_satisfiable_with_its_cost_and_model() {
        let (_s, path) = wcnf("clean", SMALL);
        // x1 = 0, x2 = 1: soft (1) is falsified, cost 3.
        let model = [false, false, true];
        let audit = audit_incumbent(&path, &model, 3, None);
        assert_eq!(audit, IncumbentAudit::Clean);
        let text = render(2, Some((3, &model, &audit)));
        assert_eq!(text, "o 3\ns SATISFIABLE\nv 01\n");
        assert_eq!(text.lines().filter(|l| l.starts_with("s ")).count(), 1);
    }

    #[test]
    fn o_line_is_not_repeated_when_already_printed() {
        let model = [false, false, true];
        let audit = IncumbentAudit::Clean;
        let mut out = Vec::new();
        write_unproven_answer(&mut out, 2, Some((3, &model, &audit)), Some(3)).expect("write");
        assert_eq!(String::from_utf8(out).unwrap(), "s SATISFIABLE\nv 01\n");
    }

    #[test]
    fn hard_violation_is_an_alarm_and_withholds_the_model() {
        let (_s, path) = wcnf("hard", SMALL);
        // x1 = x2 = 1 falsifies h (-1 v -2) and costs 0.
        let model = [false, true, true];
        let audit = audit_incumbent(&path, &model, 0, None);
        assert!(matches!(audit, IncumbentAudit::Alarm(ref r) if r.starts_with("HARD_VIOLATED")));
        assert_eq!(render(2, Some((0, &model, &audit))), "s UNKNOWN\n");
    }

    #[test]
    fn cost_mismatch_is_an_alarm() {
        let (_s, path) = wcnf("cost", SMALL);
        let model = [false, false, true];
        let audit = audit_incumbent(&path, &model, 5, None);
        assert!(matches!(audit, IncumbentAudit::Alarm(ref r) if r.starts_with("COST_MISMATCH")));
        assert_eq!(render(2, Some((5, &model, &audit))), "s UNKNOWN\n");
    }

    #[test]
    fn audit_out_of_time_is_incomplete_and_withholds_the_model() {
        let mut text = String::new();
        for v in 1..=5000 {
            text.push_str(&format!("h {v} -{v} 0\n"));
        }
        let (_s, path) = wcnf("time", &text);
        let model = vec![false; 5001];
        let past = Instant::now();
        let audit = audit_incumbent(&path, &model, 0, Some(past));
        assert!(matches!(audit, IncumbentAudit::Incomplete(_)), "{audit:?}");
        assert_eq!(render(5000, Some((0, &model, &audit))), "s UNKNOWN\n");
        // The same file audits clean with no stop time.
        assert_eq!(
            audit_incumbent(&path, &model, 0, None),
            IncumbentAudit::Clean
        );
    }

    #[test]
    fn missing_file_is_incomplete_not_restricted_subset() {
        let audit = audit_incumbent(Path::new("/nonexistent/ay-anytime.wcnf"), &[false], 0, None);
        assert!(matches!(audit, IncumbentAudit::Incomplete(_)));
    }

    #[test]
    fn no_incumbent_is_unknown() {
        assert_eq!(render(3, None), "s UNKNOWN\n");
    }

    #[test]
    fn audit_budget_is_bounded() {
        assert_eq!(audit_budget(Duration::ZERO), Duration::from_secs(2));
        assert_eq!(audit_budget(Duration::from_secs(3)), Duration::from_secs(6));
        assert_eq!(
            audit_budget(Duration::from_secs(600)),
            Duration::from_secs(10)
        );
    }
    #[test]
    fn reporter_prints_each_improvement_once_and_nothing_after_the_claim() {
        let r = Reporter::new();
        r.set_instance(2, Duration::from_secs(2));
        let mut out = Vec::new();
        r.improved(&mut out, 8, &[false, true, true]);
        r.improved(&mut out, 3, &[false, false, true]);
        r.improved(&mut out, 3, &[false, false, true]);
        let claim = r.claim().expect("first claim wins");
        assert!(r.claim().is_none(), "the answer is claimed once");
        r.improved(&mut out, 1, &[false, true, false]);
        assert_eq!(String::from_utf8(out).unwrap(), "o 8\no 3\n");
        assert_eq!(claim.last_printed, Some(3));
        assert_eq!(claim.best, Some((3, vec![false, false, true])));
        assert_eq!(claim.num_vars, 2);
    }

    #[test]
    fn watchdog_answer_is_the_audited_model_of_the_last_o_line() {
        let (_s, path) = wcnf("watchdog", SMALL);
        let r = Reporter::new();
        r.set_instance(2, Duration::from_secs(2));
        let mut out = Vec::new();
        r.improved(&mut out, 3, &[false, false, true]);
        let claim = r.claim().expect("claim");
        answer_from_claim(&mut out, &path, &claim).expect("write");
        assert_eq!(
            String::from_utf8(out).unwrap(),
            "o 3\ns SATISFIABLE\nv 01\n"
        );
    }

    #[test]
    fn watchdog_withholds_a_model_that_fails_the_audit() {
        let (_s, path) = wcnf("watchdog-bad", SMALL);
        let r = Reporter::new();
        r.set_instance(2, Duration::from_secs(2));
        let mut out = Vec::new();
        // Falsifies the hard clause (-1 v -2).
        r.improved(&mut out, 0, &[false, true, true]);
        let claim = r.claim().expect("claim");
        answer_from_claim(&mut out, &path, &claim).expect("write");
        assert_eq!(String::from_utf8(out).unwrap(), "o 0\ns UNKNOWN\n");
    }

    #[test]
    fn watchdog_with_no_incumbent_answers_unknown() {
        let r = Reporter::new();
        let claim = r.claim().expect("claim");
        let mut out = Vec::new();
        answer_from_claim(&mut out, Path::new("/nonexistent"), &claim).expect("write");
        assert_eq!(String::from_utf8(out).unwrap(), "s UNKNOWN\n");
    }

    #[test]
    fn watchdog_fires_after_a_deadline_overrun() {
        let r = Reporter::new();
        let stop = AtomicBool::new(false);
        let past = Instant::now() - STOP_GRACE;
        assert!(watch(&r, &stop, Some(past)).is_some());
        assert!(r.claim().is_none(), "the watchdog holds the answer");
    }

    #[test]
    fn watchdog_fires_a_grace_after_a_stop_request() {
        let r = Reporter::new();
        let stop = AtomicBool::new(true);
        let started = Instant::now();
        assert!(watch(&r, &stop, None).is_some());
        assert!(started.elapsed() >= STOP_GRACE);
    }

    #[test]
    fn watchdog_stands_down_when_the_solver_answered() {
        let r = Reporter::new();
        let _main = r.claim().expect("main thread answers");
        let stop = AtomicBool::new(true);
        assert!(watch(&r, &stop, Some(Instant::now() - STOP_GRACE)).is_none());
    }

    #[test]
    fn watchdog_due_takes_the_earlier_trigger() {
        let t = Instant::now();
        let later = t + Duration::from_secs(5);
        assert_eq!(watchdog_due(None, None), None);
        assert_eq!(watchdog_due(Some(t), None), Some(t + STOP_GRACE));
        assert_eq!(watchdog_due(None, Some(later)), Some(later + STOP_GRACE));
        assert_eq!(watchdog_due(Some(t), Some(later)), Some(t + STOP_GRACE));
    }
}
