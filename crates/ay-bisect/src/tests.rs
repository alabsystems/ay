// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use std::sync::Mutex;

/// Mock runner: the "fix" requires a specific set of `--no-*` flags to be
/// present in the CLI arg list. When they are present, returns `pass`.
/// When absent (or partially present), returns `fail`.
struct MockRunner {
    required: Vec<&'static str>,
    pass: SolveResult,
    fail: SolveResult,
    calls: Mutex<Vec<Vec<String>>>,
}

impl MockRunner {
    fn new(required: Vec<&'static str>, pass: SolveResult, fail: SolveResult) -> Self {
        Self {
            required,
            pass,
            fail,
            calls: Mutex::new(Vec::new()),
        }
    }

    fn call_count(&self) -> usize {
        self.calls.lock().expect("mutex poisoned").len()
    }
}

impl TrialRunner for MockRunner {
    fn run(&self, flags: &[&str]) -> Result<SolveResult> {
        self.calls
            .lock()
            .expect("mutex poisoned")
            .push(flags.iter().map(|s| (*s).to_string()).collect());
        let all = self.required.iter().all(|r| flags.contains(r));
        Ok(if all { self.pass } else { self.fail })
    }
}

struct ConcurrencyRunner {
    active: AtomicUsize,
    max_active: AtomicUsize,
}

impl TrialRunner for ConcurrencyRunner {
    fn run(&self, flags: &[&str]) -> Result<SolveResult> {
        let active = self.active.fetch_add(1, Ordering::SeqCst) + 1;
        self.max_active.fetch_max(active, Ordering::SeqCst);
        std::thread::sleep(Duration::from_millis(5));
        self.active.fetch_sub(1, Ordering::SeqCst);
        // Requiring every flag makes the minimizer exercise all parallel
        // probe sites rather than short-circuiting at the baseline.
        Ok(if flags.len() == FLAGS.len() {
            SolveResult::Sat
        } else {
            SolveResult::Unsat
        })
    }
}

#[test]
fn test_baseline_already_correct_returns_empty_set() {
    // Mock requires NO flags: baseline (empty args) already returns Sat,
    // matching the expected Sat — bisect should short-circuit.
    let runner = MockRunner::new(vec![], SolveResult::Sat, SolveResult::Unsat);
    let cfg = BisectConfig::new(PathBuf::from("/nonexistent-ignored.smt2"), Expected::Sat);
    let result = bisect_with_runner(&runner, &cfg).expect("bisect succeeds");

    assert!(result.baseline_already_correct);
    assert!(!result.outside_flag_set);
    assert!(result.minimal_flags.is_empty());
    assert!(result.subsystems.is_empty());
    // Exactly one trial (the baseline probe).
    assert_eq!(result.trials, 1);
    assert_eq!(runner.call_count(), 1);
}

#[test]
fn test_single_flag_minimal_set() {
    // Mock requires `--no-bve` to be present in args for a Sat verdict.
    // All other flags are irrelevant. Expected Sat. Bisect must return
    // exactly `["--no-bve"]`.
    let runner = MockRunner::new(vec!["--no-bve"], SolveResult::Sat, SolveResult::Unsat);
    let cfg = BisectConfig::new(PathBuf::from("/nonexistent-ignored.smt2"), Expected::Sat);
    let result = bisect_with_runner(&runner, &cfg).expect("bisect succeeds");

    assert!(!result.baseline_already_correct);
    assert!(!result.outside_flag_set);
    assert_eq!(
        result.minimal_flags,
        vec!["--no-bve".to_string()],
        "expected minimal set to be exactly [--no-bve], got {:?}",
        result.minimal_flags
    );
    assert_eq!(result.subsystems, vec!["sat".to_string()]);
    assert!(
        result.trials >= 2,
        "should have run baseline + probe + search"
    );
}

#[test]
fn test_outside_flag_set_detected() {
    // Mock requires a flag that is NOT in FLAGS — bisect can never fix
    // the bug with our flag universe.
    let runner = MockRunner::new(
        vec!["--no-does-not-exist"],
        SolveResult::Sat,
        SolveResult::Unsat,
    );
    let cfg = BisectConfig::new(PathBuf::from("/nonexistent-ignored.smt2"), Expected::Sat);
    let result = bisect_with_runner(&runner, &cfg).expect("bisect succeeds");

    assert!(!result.baseline_already_correct);
    assert!(result.outside_flag_set);
    assert!(result.minimal_flags.is_empty());
    // We should have run baseline + all-flags probe only.
    assert_eq!(result.trials, 2);
}

#[test]
fn test_pair_of_flags_minimal_set() {
    let runner = MockRunner::new(
        vec!["--no-vivify", "--no-bound-axioms"],
        SolveResult::Unsat,
        SolveResult::Sat,
    );
    let cfg = BisectConfig::new(PathBuf::from("/x.smt2"), Expected::Unsat);
    let result = bisect_with_runner(&runner, &cfg).expect("bisect");
    let set: std::collections::HashSet<_> = result.minimal_flags.iter().cloned().collect();
    assert!(
        set.contains("--no-vivify"),
        "got {:?}",
        result.minimal_flags
    );
    assert!(
        set.contains("--no-bound-axioms"),
        "got {:?}",
        result.minimal_flags
    );
    assert_eq!(result.minimal_flags.len(), 2);
    // Must span both subsystems.
    let ss: std::collections::HashSet<_> = result.subsystems.iter().cloned().collect();
    assert!(ss.contains("sat"));
    assert!(ss.contains("theory"));
}

#[test]
fn test_file_not_found() {
    let cfg = BisectConfig::new(
        PathBuf::from("/definitely/does/not/exist/bug.smt2"),
        Expected::Sat,
    );
    match bisect(&cfg) {
        Err(BisectError::FileNotFound { .. }) => {}
        other => panic!("expected FileNotFound, got {other:?}"),
    }
}

#[test]
fn test_config_builder_defaults() {
    let cfg = BisectConfig::new(PathBuf::from("x.smt2"), Expected::Sat);
    assert_eq!(cfg.timeout, Duration::from_secs(30));
    assert_eq!(cfg.jobs, 4);
    assert!(cfg.ay_binary.is_none());
}

#[test]
fn test_config_builder_chaining() {
    let cfg = BisectConfig::new(PathBuf::from("x.smt2"), Expected::Unsat)
        .with_timeout(Duration::from_mins(1))
        .with_jobs(8)
        .with_verbose(true);
    assert_eq!(cfg.timeout, Duration::from_mins(1));
    assert_eq!(cfg.jobs, 8);
    assert!(cfg.verbose);
}

#[test]
fn custom_runner_uses_private_pool_with_exact_job_limit() {
    // A pre-existing global pool was the regression: build_global() then
    // failed silently, so cfg.jobs did not govern child concurrency.
    let _ = rayon::ThreadPoolBuilder::new()
        .num_threads(4)
        .build_global();
    let runner = ConcurrencyRunner {
        active: AtomicUsize::new(0),
        max_active: AtomicUsize::new(0),
    };
    let cfg = BisectConfig::new(PathBuf::from("ignored.smt2"), Expected::Sat).with_jobs(1);
    let result = bisect_with_runner(&runner, &cfg).expect("bisect");
    assert!(!result.baseline_already_correct);
    assert_eq!(runner.max_active.load(Ordering::SeqCst), 1);
}

#[test]
fn test_extract_build_field() {
    let text = "mock-ay-build\nbuild.version=0.0.0\nbuild.stamp=mock-ay-build";
    assert_eq!(
        extract_build_field(text, "build.version").as_deref(),
        Some("0.0.0")
    );
    assert_eq!(
        extract_build_field(text, "build.stamp").as_deref(),
        Some("mock-ay-build")
    );
    assert!(extract_build_field(text, "build.commit").is_none());
}

#[test]
fn test_write_report_uses_recorded_binary_identity() {
    let cfg = BisectConfig::new(PathBuf::from("bug.smt2"), Expected::Sat);
    let result = BisectResult {
        minimal_flags: vec!["--no-bve".to_string()],
        subsystems: vec!["sat".to_string()],
        trials: 3,
        wall_ms: 42,
        baseline_already_correct: false,
        outside_flag_set: false,
        ay_binary: "/tmp/mock-ay".to_string(),
        ay_build_summary: Some("mock-ay-build".to_string()),
        resource_plan: Some(ResourcePlan {
            requested_jobs: 4,
            jobs: 3,
            memlimit_mb_per_child: 2048,
            nbcore_per_child: 2,
            headroom_mb: 16000,
            planner: "scripts/_oom_guard.py".to_string(),
        }),
    };

    let mut out = Vec::new();
    result.write_report(&mut out, &cfg).expect("write report");
    let text = String::from_utf8(out).expect("utf8");

    assert!(text.contains("ay binary: /tmp/mock-ay"), "got:\n{text}");
    assert!(text.contains("ay build:  mock-ay-build"), "got:\n{text}");
    assert!(
        text.contains("Repro command:\n  /tmp/mock-ay --memory 2048 --no-bve bug.smt2"),
        "got:\n{text}"
    );
    assert!(text.contains("resources: jobs=3 (requested 4)"));
}
