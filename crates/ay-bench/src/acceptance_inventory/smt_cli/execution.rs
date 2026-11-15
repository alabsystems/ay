// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::selection::invalid;
use super::snapshot::{hash, remaining};
use super::types::{DefaultObservation, SmtCliTerminal};
use super::{SmtCliArgs, SmtCliBlocker as Blocker, SmtCliCase, SmtCliRecord, SmtCliReport};
use crate::environment::PinnedSolver;
use crate::resource::{BoundedPipeCapture, PlannedResources};
use crate::Result;
use std::collections::BTreeMap;
use std::fs;
use std::path::Path;
use std::process::Stdio;
use std::time::{Duration, Instant};

const TREE_MIB: usize = 4096;
const DEFAULT_PROBE: &[u8] = b"(set-logic QF_UF)\n(assert true)\n(check-sat)\n";
const SOLVER_PATH: &str = "/usr/bin:/bin";
const SOLVER_LOCALE: &str = "C";
const SOLVER_TIMEZONE: &str = "UTC";
const SOLVER_CORES: &str = "1";

/// Run selected source-bound SMT profiles. This is in-tree self-check evidence,
/// never an independent certificate, tuple check, performance comparison or ask
/// closure. The single original owner begins before planning and source reads.
/// Existing process stop/cleanup and filesystem calls remain cooperative opaque
/// intervals; a late completion is refused, not claimed to meet a hard latency.
pub fn run_smt_cli(args: SmtCliArgs) -> Result<SmtCliReport> {
    let duration =
        crate::resource::checked_benchmark_timeout(args.timeout_sec, "SMT acceptance owner")?;
    let started = Instant::now();
    let deadline = started
        .checked_add(duration)
        .ok_or_else(|| invalid("SMT owner overflow"))?;
    // Exclusive destination: neither stale output nor another run is evidence.
    fs::create_dir(&args.out_dir)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&args.out_dir, fs::Permissions::from_mode(0o700))?;
    }
    let mut result = run_owned(&args, started, deadline);
    if result.is_ok() {
        if let Err(error) = remaining(deadline) {
            fs::remove_file(args.out_dir.join("report.json"))?;
            result = Err(error);
        }
    }
    if let Err(error) = &result {
        // Failure-only cleanup publication grants no additional solver work or
        // accepted result. Preserve it even when the original owner expired.
        let detail: String = error.to_string().chars().take(2048).collect();
        let failure = serde_json::json!({"schema":"ay.model-checker-consumer-smt-cli-failure/v1",
            "blocker": if Instant::now() >= deadline { Blocker::Deadline } else { Blocker::UnfinishedRoute },
            "detail":detail,"promotable_for_ask_closure":false});
        let file = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(args.out_dir.join("failure.json"))?;
        serde_json::to_writer(&file, &failure)?;
        file.sync_all()?;
    }
    result
}

fn run_owned(args: &SmtCliArgs, started: Instant, deadline: Instant) -> Result<SmtCliReport> {
    let (inventory, selection_sha256, cases) = super::selection::load(&args.selection)?;
    remaining(deadline)?;
    let mut resources =
        PlannedResources::plan(&crate::runner::repo_root_public(), 1, "SMT acceptance")?;
    if resources.plan.jobs != 1 || resources.plan.memlimit_mb_per_child < TREE_MIB {
        return Err(invalid("cannot admit serial4GiB process-tree profile"));
    }
    resources.apply_per_child_caps(Some(TREE_MIB), Some(1))?;
    remaining(deadline)?;
    let solver =
        PinnedSolver::capture_before(&args.ay, &resources, "SMT acceptance version", deadline)?;
    let mut records = Vec::new();
    for (index, case) in cases.into_iter().enumerate() {
        remaining(deadline)?;
        let case_deadline = Instant::now()
            .checked_add(Duration::from_millis(case.timeout_ms))
            .ok_or_else(|| invalid("SMT case deadline overflow"))?
            .min(deadline);
        let directory = args.out_dir.join(format!("case-{index}"));
        fs::create_dir(&directory)?;
        let mut record = run_case(
            case,
            &directory,
            &solver,
            &resources,
            started,
            case_deadline,
        )?;
        publish_record(&directory, &mut record, case_deadline)?;
        records.push(record);
        remaining(deadline)?;
    }
    solver.verify_source_before(deadline)?;
    let binary = serde_json::to_value(solver.provenance())?;
    let resource_record = serde_json::to_value(&resources.plan)?;
    drop(solver);
    drop(resources);
    remaining(deadline)?;
    let report = SmtCliReport {
        schema: "ay.model-checker-consumer-smt-cli-run/v1",
        selection_sha256,
        owner_budget_ns: u64::try_from(deadline.duration_since(started).as_nanos())
            .map_err(|_| invalid("owner duration overflow"))?,
        observed_tree_peak_bytes: None,
        inventory_sha256: inventory.sha256.clone(),
        plan: inventory.plan(),
        binary,
        resources: resource_record,
        records,
        blockers: vec![
            Blocker::IncompleteRequiredRoutes,
            Blocker::ConsumerTupleUnqualified,
            Blocker::IndependentReplayNotRun,
            Blocker::PerformanceComparisonNotRun,
            Blocker::OriginalSourceRevisionUnqualified,
            Blocker::TreePeakUnavailable,
        ],
        promotable_for_ask_closure: false,
    };
    super::snapshot::write_json(&args.out_dir.join("report.json"), &report, deadline)?;
    Ok(report)
}

fn run_case(
    case: SmtCliCase,
    directory: &Path,
    solver: &PinnedSolver,
    resources: &PlannedResources,
    run_started: Instant,
    deadline: Instant,
) -> Result<SmtCliRecord> {
    let start = Instant::now();
    let binary = serde_json::to_value(solver.provenance())?;
    let deadline_from_run_start_ns = u64::try_from(deadline.duration_since(run_started).as_nanos())
        .map_err(|_| invalid("case duration overflow"))?;
    let execution_envelope = crate::resource::effective_execution_envelope(
        &resources.plan,
        crate::resource::ENFORCEMENT_RSS_WATCHDOG_V1,
        remaining(deadline)?.as_secs_f64(),
    )?;
    let input = directory.join("input.smt2");
    super::snapshot::copy(&case.path, &input, &case.sha256, case.size_bytes, deadline)?;
    let environment = fixed_environment();
    let default_observation =
        observe_default(&case, directory, solver, resources, &environment, deadline)?;
    if let Some(observation) = &default_observation {
        if !observation.blockers.is_empty() {
            let blockers = observation.blockers.clone();
            return Ok(SmtCliRecord {
                case,
                binary,
                terminal: None,
                argv: Vec::new(),
                environment,
                observed_status: "not-run".to_owned(),
                in_tree_self_check_passed: false,
                independent_replay_passed: false,
                observed_solver_memory_bytes: None,
                default_observation,
                tree_memory_bytes: TREE_MIB as u64 * 1024 * 1024,
                execution_envelope,
                elapsed_ns: u64::try_from(start.elapsed().as_nanos())
                    .map_err(|_| invalid("elapsed time overflow"))?,
                deadline_from_run_start_ns,
                stdout_sha256: hash(b""),
                stderr_sha256: hash(b""),
                blockers,
                promotable_for_ask_closure: false,
            });
        }
    }
    let argv = argv(&case, &input, remaining(deadline)?);
    let mut output = execute(
        solver.execution_path(),
        &argv,
        &environment,
        resources,
        deadline,
    )?;
    retain_output(directory, "solve", &output)?;
    output.note_deadline(deadline);
    let mut assessment = super::assess::assess(
        &case,
        solver.provenance(),
        &output.stdout,
        &output.stderr,
        output.terminal.exit_code,
        output.terminal.timed_out || output.terminal.original_deadline_expired,
        output.terminal.memory_limit_exceeded,
        default_observation
            .as_ref()
            .and_then(|value| value.solver_memory_bytes),
    );
    output.refuse_incomplete(&mut assessment);
    let elapsed_ns =
        u64::try_from(start.elapsed().as_nanos()).map_err(|_| invalid("elapsed time overflow"))?;
    Ok(SmtCliRecord {
        case,
        binary,
        terminal: Some(output.terminal),
        argv: full_argv(solver.execution_path(), &argv),
        environment,
        observed_status: assessment.status,
        in_tree_self_check_passed: assessment.checked,
        independent_replay_passed: false,
        observed_solver_memory_bytes: assessment.memory,
        default_observation,
        tree_memory_bytes: TREE_MIB as u64 * 1024 * 1024,
        execution_envelope,
        elapsed_ns,
        deadline_from_run_start_ns,
        stdout_sha256: hash(output.stdout.as_bytes()),
        stderr_sha256: hash(output.stderr.as_bytes()),
        blockers: assessment.blockers,
        promotable_for_ask_closure: false,
    })
}

fn observe_default(
    case: &SmtCliCase,
    directory: &Path,
    solver: &PinnedSolver,
    resources: &PlannedResources,
    environment: &BTreeMap<String, String>,
    deadline: Instant,
) -> Result<Option<DefaultObservation>> {
    Ok(if case.variant.explicit_mib().is_none() {
        let path = directory.join("default-probe.smt2");
        super::snapshot::write_bytes(&path, DEFAULT_PROBE, deadline)?;
        let probe_case = SmtCliCase {
            expected: super::super::CliStatus::Sat,
            ..case.clone()
        };
        let argv = argv(&probe_case, &path, remaining(deadline)?);
        let mut output = execute(
            solver.execution_path(),
            &argv,
            environment,
            resources,
            deadline,
        )?;
        retain_output(directory, "default", &output)?;
        output.note_deadline(deadline);
        let mut tentative = super::assess::assess(
            &probe_case,
            solver.provenance(),
            &output.stdout,
            &output.stderr,
            output.terminal.exit_code,
            output.terminal.timed_out || output.terminal.original_deadline_expired,
            output.terminal.memory_limit_exceeded,
            None,
        );
        output.refuse_incomplete(&mut tentative);
        // The observation has no prior value to match. Preserve a failed
        // profile without launching its original case or calling it a pass.
        let mut blockers: Vec<_> = tentative
            .blockers
            .into_iter()
            .filter(|blocker| *blocker != Blocker::DefaultMemoryUnavailable)
            .collect();
        let memory = tentative.memory;
        default_envelope(memory, &mut blockers);
        Some(DefaultObservation {
            argv: full_argv(solver.execution_path(), &argv),
            input_sha256: hash(DEFAULT_PROBE),
            input_size_bytes: DEFAULT_PROBE.len() as u64,
            solver_memory_bytes: memory,
            terminal: output.terminal,
            blockers,
            stdout_sha256: hash(output.stdout.as_bytes()),
            stderr_sha256: hash(output.stderr.as_bytes()),
        })
    } else {
        None
    })
}

pub(super) fn argv(case: &SmtCliCase, path: &Path, remaining: Duration) -> Vec<String> {
    let mut argv = vec![
        "--self-check".to_owned(),
        "--stats-json".to_owned(),
        format!("-t:{}", remaining.as_millis().max(1)),
    ];
    if let Some(mib) = case.variant.explicit_mib() {
        argv.extend(["--memory".to_owned(), mib.to_string()]);
    }
    argv.push(path.display().to_string());
    argv
}
fn full_argv(binary: &Path, args: &[String]) -> Vec<String> {
    std::iter::once(binary.display().to_string())
        .chain(args.iter().cloned())
        .collect()
}
fn fixed_environment() -> BTreeMap<String, String> {
    BTreeMap::from([
        ("PATH".into(), SOLVER_PATH.into()),
        ("LC_ALL".into(), SOLVER_LOCALE.into()),
        ("TZ".into(), SOLVER_TIMEZONE.into()),
        ("NBCORE".into(), SOLVER_CORES.into()),
    ])
}
pub(super) struct Output {
    pub(super) stdout: String,
    pub(super) stderr: String,
    pub(super) terminal: SmtCliTerminal,
}
impl Output {
    fn note_deadline(&mut self, deadline: Instant) {
        self.terminal.original_deadline_expired |= Instant::now() >= deadline;
    }
    pub(super) fn refuse_incomplete(&self, assessment: &mut super::assess::Assessment) {
        if !self.terminal.stdout_complete || !self.terminal.stderr_complete {
            assessment.blockers.push(Blocker::OutputIncomplete);
        }
        if !self.terminal.errors.is_empty() {
            assessment.blockers.push(Blocker::ChildFailure);
        }
        assessment.checked = assessment.blockers.is_empty();
    }
}
pub(super) fn default_envelope(memory: Option<u64>, blockers: &mut Vec<Blocker>) {
    match memory {
        None => blockers.push(Blocker::DefaultMemoryUnavailable),
        Some(n) if n > TREE_MIB as u64 * 1024 * 1024 => {
            blockers.push(Blocker::DefaultMemoryExceedsTreeEnvelope)
        }
        Some(_) => {}
    }
}
fn execute(
    binary: &Path,
    argv: &[String],
    environment: &BTreeMap<String, String>,
    resources: &PlannedResources,
    deadline: Instant,
) -> Result<Output> {
    remaining(deadline)?;
    if environment != &fixed_environment() {
        return Err(invalid(
            "solver environment differs from the recorded fixed profile",
        ));
    }
    // A finite file-size ceiling covers default proof emission next to the
    // private input. Excess output/artifact production is a failed invocation.
    let mut command = resources.external_command_with_file_limit(binary, 64 * 1024 * 1024);
    command
        .args(argv)
        .env_clear()
        .env("PATH", SOLVER_PATH)
        .env("LC_ALL", SOLVER_LOCALE)
        .env("TZ", SOLVER_TIMEZONE)
        .env("NBCORE", SOLVER_CORES)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    remaining(deadline)?;
    let mut child = resources.spawn_owned_child(&mut command, "SMT acceptance")?;
    let stdout = child
        .take_stdout()
        .map(BoundedPipeCapture::start)
        .transpose();
    let stderr = child
        .take_stderr()
        .map(BoundedPipeCapture::start)
        .transpose();
    let waited = if !matches!(&stdout, Ok(Some(_))) || !matches!(&stderr, Ok(Some(_))) {
        match child.cancel() {
            Ok(()) => Err(invalid(
                "native capture setup failed; original child cancelled",
            )),
            Err(error) => Err(error),
        }
    } else {
        match remaining(deadline) {
            Ok(duration) => child.wait(duration),
            Err(_) => child.deadline(),
        }
    };
    // Finish both readers even when waiting or one capture fails. Preserve
    // bounded prefixes and exact uncertainty after the original deadline.
    let stdout = finish_capture(stdout, "stdout");
    let stderr = finish_capture(stderr, "stderr");
    let mut errors = Vec::new();
    for error in [stdout.error, stderr.error].into_iter().flatten() {
        errors.push(error);
    }
    let (exit_code, timed_out, memory_limit_exceeded) = match waited {
        Ok(outcome) => (
            outcome.status.and_then(|s| s.code()),
            outcome.timed_out,
            outcome.memout,
        ),
        Err(error) => {
            errors.push(error.to_string().chars().take(2048).collect());
            (None, false, false)
        }
    };
    Ok(Output {
        stdout: stdout.text,
        stderr: stderr.text,
        terminal: SmtCliTerminal {
            exit_code,
            timed_out,
            memory_limit_exceeded,
            original_deadline_expired: Instant::now() >= deadline,
            stdout_complete: !stdout.incomplete,
            stderr_complete: !stderr.incomplete,
            errors,
        },
    })
}
fn finish_capture(
    capture: std::io::Result<Option<BoundedPipeCapture>>,
    stream: &str,
) -> crate::resource::PipeCaptureEvidence {
    match capture {
        Ok(Some(capture)) => capture.finish_evidence(),
        result => crate::resource::PipeCaptureEvidence {
            text: String::new(),
            incomplete: true,
            error: Some(match result {
                Err(error) => format!("cannot start {stream} capture: {error}"),
                _ => format!("missing {stream} pipe"),
            }),
        },
    }
}
pub(super) fn retain_output(directory: &Path, prefix: &str, output: &Output) -> Result<()> {
    super::snapshot::write_terminal_bytes(
        &directory.join(format!("{prefix}.stdout")),
        output.stdout.as_bytes(),
    )?;
    super::snapshot::write_terminal_bytes(
        &directory.join(format!("{prefix}.stderr")),
        output.stderr.as_bytes(),
    )
}
pub(super) fn publish_record(
    directory: &Path,
    record: &mut SmtCliRecord,
    deadline: Instant,
) -> Result<()> {
    let path = directory.join("record.json");
    demote_late(record, deadline);
    if record.in_tree_self_check_passed {
        let result = super::snapshot::write_json(&path, record, deadline);
        if let Err(error) = result {
            if Instant::now() < deadline {
                return Err(error);
            }
            demote_late(record, deadline);
        } else if Instant::now() >= deadline {
            fs::remove_file(&path)?;
            demote_late(record, deadline);
        } else {
            return Ok(());
        }
    }
    // The fixed bounded record is terminal failure evidence. No accepted bit
    // or solver work is permitted by this post-deadline cleanup path.
    super::snapshot::write_failure_json(&path, record)
}
fn demote_late(record: &mut SmtCliRecord, deadline: Instant) {
    if Instant::now() >= deadline {
        record.in_tree_self_check_passed = false;
        if !record.blockers.contains(&Blocker::Deadline) {
            record.blockers.push(Blocker::Deadline);
        }
        if let Some(terminal) = &mut record.terminal {
            terminal.original_deadline_expired = true;
        }
    }
}
