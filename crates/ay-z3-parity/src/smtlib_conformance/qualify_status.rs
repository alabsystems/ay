// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Read-only inspection of the existing qualification-run/v2 journals.
//! Recorded outcomes are diagnostics, never replacement validator evidence.

use super::*;
use std::io::Read as _;

const SCHEMA: &str = "ay-z3-qualification-status/v2";
// These are the existing qualification summary's stage and byte bounds.
const MAX_JOURNALS: usize = 100;
const MAX_JOURNAL_BYTES: u64 = 1024 * 1024;
const MAX_INSPECTION_BYTES: u64 = 4 * 1024 * 1024;

#[derive(Debug, Serialize)]
struct StatusReport {
    schema: &'static str,
    directory: PathBuf,
    mode: &'static str,
    notes: Vec<String>,
    recorded_summary: Option<RecordedSummary>,
    summary_error: Option<String>,
    journal_errors: Vec<JournalError>,
    action: Option<Action>,
    stages: Vec<StageObservation>,
}

#[derive(Debug, Serialize)]
struct RecordedSummary {
    campaign_id: String,
    passed_stages: usize,
    total_stages: usize,
    completed_registered_qualification: bool,
    missing_product_acceptance: Vec<String>,
}

#[derive(Debug, Serialize)]
struct StageObservation {
    id: String,
    state: &'static str,
    reason: String,
    journal: Option<PathBuf>,
    evidence: Option<PathBuf>,
    action: Option<Action>,
}

#[derive(Debug, Serialize)]
struct JournalError {
    journal: PathBuf,
    stage_id: Option<String>,
    state: &'static str,
    reason: String,
}

#[derive(Debug, Serialize)]
struct Action {
    description: &'static str,
    argv: Vec<String>,
}

fn action(description: &'static str, command: &str, operands: &[String]) -> Action {
    let mut argv = vec![
        "ay-z3-parity".into(),
        "smtlib-conformance".into(),
        command.into(),
    ];
    argv.extend_from_slice(operands);
    Action { description, argv }
}

fn local_locations(base: &Path, path: &Path) -> Vec<PathBuf> {
    let relative = if path.is_absolute() {
        let Ok(relative) = path.strip_prefix(base) else {
            return Vec::new();
        };
        relative
    } else {
        path
    };
    let Some(text) = relative.to_str() else {
        return Vec::new();
    };
    if validate_relative_path(text, "qualification status location").is_err() {
        return Vec::new();
    }
    if path.is_absolute() {
        return vec![base.join(relative)];
    }
    // Main's original writer also records launch-relative operands such as
    // `out/receipt.json`. Only consider lexical anchors whose complete result
    // remains inside this run; never probe an ancestor or an external file.
    base.ancestors()
        .map(|parent| parent.join(relative))
        .filter(|candidate| candidate.starts_with(base))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn recorded_file(base: &Path, path: &Path) -> Option<PathBuf> {
    let mut files = BTreeSet::new();
    for location in local_locations(base, path) {
        let relative = location.strip_prefix(base).ok()?.to_str()?;
        if let Ok(path) = resolve_relative_evidence_path(base, relative) {
            files.insert(path);
        }
    }
    if files.len() == 1 {
        files.into_iter().next()
    } else {
        None
    }
}

fn local_location(base: &Path, path: &Path) -> Option<PathBuf> {
    let relative = if path.is_absolute() {
        path.strip_prefix(base).ok()?
    } else {
        path
    };
    validate_relative_path(relative.to_str()?, "qualification status location").ok()?;
    Some(base.join(relative))
}

fn local_file(base: &Path, path: &Path) -> Option<PathBuf> {
    let location = local_location(base, path)?;
    resolve_relative_evidence_path(base, location.strip_prefix(base).ok()?.to_str()?).ok()
}

fn exists(path: &Path) -> Result<bool, String> {
    match fs::symlink_metadata(path) {
        Ok(_) => Ok(true),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(format!("inspect {}: {error}", path.display())),
    }
}

fn bounded_reason(mut reason: String) -> String {
    if reason.len() > 2048 {
        let mut end = 2000;
        while !reason.is_char_boundary(end) {
            end -= 1;
        }
        reason.truncate(end);
        reason.push_str("… [truncated]");
    }
    reason
}

fn stage_reason(stage: Option<&Stage>) -> (&'static str, String) {
    let Some(stage) = stage else {
        return (
            "not-recorded",
            "No stage journal was published at inspection time".into(),
        );
    };
    let (state, reason) = match (stage.status.as_str(), stage.exit_code, &stage.error) {
        ("passed", Some(0), None) => ("recorded-passed", "Journal records exit code 0".into()),
        ("failed", _, Some(error)) => ("recorded-failed", error.clone()),
        ("failed", Some(code), None) if code != 0 => (
            "recorded-failed",
            format!(
                "Journal records exit code {code}. See the stage report or receipt for details"
            ),
        ),
        ("blocked", _, Some(error)) => ("recorded-blocked", error.clone()),
        _ => (
            "inconsistent-journal",
            format!("Journal has inconsistent status {:?}", stage.status),
        ),
    };
    (state, bounded_reason(reason))
}

fn expected_ids() -> Result<Vec<String>, String> {
    let mut ids = [
        "provision",
        "current-release-inventory",
        "current-behavior",
        "stock-python",
        "stock-cpp",
        "stock-c",
        "provision-official-corpus",
        "provision-checker",
    ]
    .map(str::to_owned)
    .to_vec();
    ids.extend(validator_ids()?);
    ids.extend(["current-abi", "performance-domination", "completion-check"].map(str::to_owned));
    Ok(ids)
}

fn validator_ids() -> Result<Vec<String>, String> {
    let options = parse(&["unused".into(), "--plan".into()])?;
    Ok(validators(&options)
        .into_iter()
        .map(|(owner, dimension, _)| {
            dimension.map_or_else(
                || owner.to_owned(),
                |dimension| format!("{owner}:{dimension}"),
            )
        })
        .collect())
}

fn report_owner(id: &str) -> Option<(&'static str, &'static str)> {
    match id {
        "current-release-inventory" => {
            Some(("current-release-inventory.json", "current-release-check"))
        }
        "current-abi" => Some(("current-abi.json", "abi-gaps")),
        "current-behavior" => Some(("current-behavior.json", "current-behavior-check")),
        "stock-python" => Some(("stock-python/stock-python.json", "stock-python-check")),
        "stock-cpp" => Some(("stock-cpp.json", "stock-cpp-check")),
        "stock-c" => Some(("stock-c.json", "stock-c-check")),
        "performance-domination" => Some(("performance/domination.json", "dominate-check")),
        "completion-check" => Some(("completion-check.json", "check")),
        _ => None,
    }
}

/// This header peek selects a diagnostic command only. The checkpoint owner
/// will authenticate its entire sampled prefix, profile, and corpus manifest.
fn checkpoint_action(base: &Path) -> Result<Option<Action>, String> {
    use std::io::BufRead as _;
    let Some(checkpoint) = local_file(
        base,
        Path::new("official-corpus-results.evidence/records.jsonl"),
    ) else {
        return Ok(None);
    };
    let Some(corpus) = local_file(base, Path::new("official-corpus.json")) else {
        return Ok(None);
    };
    let mut options = fs::OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
    }
    let file = options
        .open(&checkpoint)
        .map_err(|error| format!("open checkpoint header: {error}"))?;
    if !file
        .metadata()
        .map_err(|error| error.to_string())?
        .is_file()
    {
        return Err("checkpoint header is not a regular file".into());
    }
    let mut line = Vec::new();
    std::io::BufReader::new(file.take(64 * 1024 + 1))
        .read_until(b'\n', &mut line)
        .map_err(|error| format!("read checkpoint header: {error}"))?;
    if line.len() > 64 * 1024 || !line.ends_with(b"\n") {
        return Err("checkpoint header is incomplete or exceeds its 64 KiB bound".into());
    }
    let header: Value = serde_json::from_slice(&line)
        .map_err(|error| format!("invalid checkpoint header: {error}"))?;
    if header.get("schema").and_then(Value::as_str) != Some("ay-official-corpus-record-stream/v2")
        || !header.get("producer").is_some_and(Value::is_object)
    {
        return Err("Checkpoint inspection requires producer-bound v2 records; unbound v1 records require ordinary receipt replay".into());
    }
    Ok(Some(action(
        "Inspect the recorded official corpus checkpoint prefix",
        "official-corpus-gaps",
        &[
            "--checkpoint".into(),
            path_text(&checkpoint)?,
            "--corpus-manifest".into(),
            path_text(&corpus)?,
        ],
    )))
}

fn receipt_location_matches(base: &Path, stage: &Stage) -> bool {
    let mut expected = stage
        .command
        .windows(2)
        .filter(|pair| pair[0] == "--receipt");
    let Some(expected_path) = expected.next() else {
        return false;
    };
    if expected.next().is_some() {
        return false;
    }
    let expected = recorded_file(base, Path::new(&expected_path[1]));
    let recorded = stage
        .receipt
        .as_deref()
        .and_then(|path| recorded_file(base, Path::new(path)));
    expected.is_some() && expected == recorded
}

#[derive(Clone, Copy)]
enum EvidenceOwner {
    Receipt,
    ReportOrJournal,
}

fn observe_stage(
    base: &Path,
    id: String,
    recorded: Option<(PathBuf, Stage)>,
    evidence_owner: EvidenceOwner,
) -> StageObservation {
    let receipt_required = matches!(evidence_owner, EvidenceOwner::Receipt);
    let stage = recorded.as_ref().map(|(_, stage)| stage);
    let (mut state, mut reason) = stage_reason(stage);
    let owner = report_owner(&id);
    let required = owner
        .map(|(file, _)| PathBuf::from(file))
        .or_else(|| stage?.receipt.as_ref().map(PathBuf::from));
    let present = required.as_deref().and_then(|path| {
        if owner.is_some() {
            local_file(base, path)
        } else {
            recorded_file(base, path)
        }
    });
    let evidence = present.clone().or_else(|| {
        required
            .as_deref()
            .and_then(|path| local_location(base, path))
    });
    let attached = stage
        .and_then(|stage| stage.attached_manifest.as_deref())
        .and_then(|path| recorded_file(base, Path::new(path)));
    let receipt_matches = stage.is_some_and(|stage| receipt_location_matches(base, stage));
    let manifest = stage
        .and_then(|stage| stage.command.first())
        .and_then(|path| recorded_file(base, Path::new(path)));
    let corpus = local_file(base, Path::new("official-corpus.json"));
    if state == "recorded-passed"
        && ((required.is_some() && present.is_none())
            || (receipt_required && (present.is_none() || attached.is_none() || !receipt_matches))
            || (matches!(id.as_str(), "completion-check" | "performance-domination")
                && manifest.is_none())
            || (id == "performance-domination" && corpus.is_none()))
    {
        state = "missing-evidence";
        reason = "Journal records a pass, but its required local report, receipt, or attached manifest is unavailable or differs from its recorded operand".into();
    }
    let replay = if matches!(state, "inconsistent-journal" | "missing-evidence") {
        None
    } else if let (Some((_, command)), Some(path)) = (owner, present.as_ref()) {
        if matches!(id.as_str(), "completion-check" | "performance-domination") {
            // These owners need the manifest as well as the report. Never
            // guess an absent operand or execute a recorded command vector.
            manifest.and_then(|manifest| {
                let operands = if id == "completion-check" {
                    vec![path_text(&manifest).ok()?, "--require-complete".into()]
                } else {
                    let corpus = corpus?;
                    vec![
                        path_text(&manifest).ok()?,
                        "--corpus-manifest".into(),
                        path_text(&corpus).ok()?,
                        "--receipt".into(),
                        path_text(path).ok()?,
                    ]
                };
                Some(action(
                    "Replay this stage's recorded evidence",
                    command,
                    &operands,
                ))
            })
        } else if id == "current-abi" {
            path_text(path)
                .ok()
                .map(|path| action("Inspect the recorded ABI gaps", command, &[path]))
        } else {
            path_text(path)
                .ok()
                .map(|path| action("Replay this stage's recorded evidence", command, &[path]))
        }
    } else if receipt_required && receipt_matches && present.is_some() {
        attached.and_then(|path| path_text(&path).ok()).map(|path| {
            action(
                "Inspect the attached contract with the existing validator owner",
                "check",
                &[path],
            )
        })
    } else {
        None
    };
    StageObservation {
        id,
        state,
        reason,
        journal: recorded.map(|(path, _)| path),
        evidence,
        action: replay,
    }
}

fn inspect(base: &Path) -> Result<StatusReport, String> {
    let mut records = BTreeMap::new();
    let mut ambiguous = BTreeSet::new();
    let mut errors = Vec::new();
    let mut remaining = MAX_INSPECTION_BYTES;
    for index in 0..MAX_JOURNALS {
        let path = base.join(format!("stage-{index:03}.json"));
        match exists(&path) {
            Ok(false) => continue,
            Ok(true) => {}
            Err(reason) => {
                errors.push(JournalError {
                    journal: path,
                    stage_id: None,
                    state: "unreadable-journal",
                    reason: bounded_reason(reason),
                });
                continue;
            }
        }
        let observed: Result<Stage, String> = (|| {
            let size = fs::symlink_metadata(&path)
                .map_err(|error| error.to_string())?
                .len();
            if size > remaining.min(MAX_JOURNAL_BYTES) {
                return Err(
                    "Journal exceeds its fixed per-file or aggregate inspection byte bound".into(),
                );
            }
            remaining -= size;
            let (_, stage) = read_hashed_json::<Stage>(&path, size, "qualification stage journal")?;
            Ok(stage)
        })();
        let stage = match observed {
            Ok(stage) => stage,
            Err(reason) => {
                errors.push(JournalError {
                    journal: path,
                    stage_id: None,
                    state: "invalid-journal",
                    reason: bounded_reason(reason),
                });
                continue;
            }
        };
        if ambiguous.contains(&stage.id) || records.contains_key(&stage.id) {
            if let Some((prior, _)) = records.remove(&stage.id) {
                errors.push(JournalError {
                    journal: prior,
                    stage_id: Some(stage.id.clone()),
                    state: "ambiguous-journal",
                    reason: "Multiple journals record this stage; none was selected".into(),
                });
            }
            ambiguous.insert(stage.id.clone());
            errors.push(JournalError {
                journal: path,
                stage_id: Some(stage.id),
                state: "ambiguous-journal",
                reason: "Multiple journals record this stage; none was selected".into(),
            });
        } else {
            records.insert(stage.id.clone(), (path, stage));
        }
    }
    let summary_path = base.join("qualification.json");
    let summary = if exists(&summary_path)? {
        Some((|| {
            let (_, summary) = read_hashed_json::<Summary>(
                &summary_path,
                MAX_INSPECTION_BYTES,
                "qualification summary",
            )?;
            validate_summary_claims(&summary)?;
            if recorded_file(base, &summary.manifest).is_none() {
                return Err("qualification summary's local manifest is unavailable".into());
            }
            let mut paths = BTreeSet::new();
            for evidence in &summary.evidence {
                validate_sha256(&evidence.sha256, "qualification evidence digest")?;
                validate_relative_path(&evidence.path, "qualification evidence path")?;
                if !paths.insert(&evidence.path)
                    || local_file(base, Path::new(&evidence.path)).is_none()
                {
                    return Err(format!(
                        "qualification summary has duplicate or unavailable evidence {:?}",
                        evidence.path
                    ));
                }
            }
            for (index, stage) in summary.stages.iter().enumerate() {
                if !records.get(&stage.id).is_some_and(|(path, recorded)| {
                    path == &base.join(format!("stage-{index:03}.json")) && recorded == stage
                }) {
                    return Err(format!(
                        "qualification summary differs from journal for {}",
                        stage.id
                    ));
                }
            }
            Ok(summary)
        })())
    } else {
        None
    };
    let (recorded_summary, summary_error) = match summary {
        Some(Ok(summary)) => (
            Some(RecordedSummary {
                campaign_id: summary.campaign_id,
                passed_stages: summary.passed_stages,
                total_stages: summary.stages.len(),
                completed_registered_qualification: summary.completed_registered_qualification,
                missing_product_acceptance: summary.missing_product_acceptance,
            }),
            None,
        ),
        Some(Err(error)) => (None, Some(error)),
        None => (None, None),
    };
    let mut ids = expected_ids()?;
    let extra_ids = records
        .keys()
        .chain(ambiguous.iter())
        .filter(|id| !ids.contains(id))
        .cloned()
        .collect::<BTreeSet<_>>();
    ids.extend(extra_ids);
    let receipt_stages = validator_ids()?.into_iter().collect::<BTreeSet<_>>();
    let mut stages = Vec::new();
    for id in ids {
        let observed = if ambiguous.contains(&id) {
            StageObservation {
                id,
                state: "ambiguous-journal",
                reason: "Multiple journals record this stage; none was selected".into(),
                journal: None,
                evidence: None,
                action: None,
            }
        } else {
            observe_stage(
                base,
                id.clone(),
                records.remove(&id),
                if receipt_stages.contains(&id) {
                    EvidenceOwner::Receipt
                } else {
                    EvidenceOwner::ReportOrJournal
                },
            )
        };
        if matches!(observed.state, "missing-evidence" | "inconsistent-journal") {
            errors.push(JournalError {
                journal: observed
                    .journal
                    .clone()
                    .unwrap_or_else(|| base.to_path_buf()),
                stage_id: Some(observed.id.clone()),
                state: observed.state,
                reason: observed.reason.clone(),
            });
        }
        stages.push(observed);
    }
    let mut notes = vec!["Recorded passes have not been replayed. Inspection never establishes qualification or product compatibility.".into()];
    if let Some(corpus) = stages
        .iter_mut()
        .find(|stage| stage.id == "official-corpus")
    {
        if !matches!(
            corpus.state,
            "ambiguous-journal" | "inconsistent-journal" | "missing-evidence"
        ) {
            match checkpoint_action(base) {
                Ok(Some(action)) => corpus.action = Some(action),
                Ok(None) => {}
                Err(error) => notes.push(error),
            }
        }
    }
    let action = if recorded_summary.is_some() && summary_error.is_none() && errors.is_empty() {
        Some(action(
            "Replay the recorded campaign using its recorded evaluator",
            "qualify-check",
            &[path_text(&summary_path)?],
        ))
    } else {
        None
    };
    Ok(StatusReport {
        schema: SCHEMA,
        directory: base.to_path_buf(),
        mode: "journal inspection only",
        notes,
        recorded_summary,
        summary_error,
        journal_errors: errors,
        action,
        stages,
    })
}

fn inspection_exit(report: &StatusReport) -> i32 {
    i32::from(report.summary_error.is_some() || !report.journal_errors.is_empty())
}

#[derive(Clone, Copy)]
enum View<'a> {
    All,
    Stage(&'a str),
    Gaps,
}

fn filtered(mut report: StatusReport, view: View<'_>) -> Result<(StatusReport, i32), String> {
    let exit = inspection_exit(&report);
    if let View::Stage(id) = view {
        report.stages.retain(|stage| stage.id == id);
        if report.stages.is_empty() {
            return Err(format!("qualification status has no stage {id:?}"));
        }
    }
    if matches!(view, View::Gaps) {
        report
            .stages
            .retain(|stage| stage.state != "recorded-passed");
    }
    Ok((report, exit))
}

pub(super) fn run(args: &[String]) -> Result<i32, String> {
    if args == ["--help"] || args == ["-h"] {
        println!("Usage: ay-z3-parity qualify-status DIR [--stage ID | --gaps] [--json]");
        return Ok(0);
    }
    let mut directory = None;
    let mut stage = None;
    let mut gaps = false;
    let mut json = false;
    let mut words = args.iter();
    while let Some(word) = words.next() {
        match word.as_str() {
            "--stage" if stage.is_none() => {
                stage = Some(words.next().ok_or("--stage needs an id")?)
            }
            "--gaps" => gaps = true,
            "--json" => json = true,
            flag if flag.starts_with('-') => return Err(format!("unknown status flag {flag:?}")),
            dir if directory.is_none() => directory = Some(dir),
            _ => return Err("qualify-status takes one directory".into()),
        }
    }
    if gaps && stage.is_some() {
        return Err("--gaps and --stage cannot be combined".into());
    }
    let base = fs::canonicalize(directory.ok_or("qualify-status needs a qualification directory")?)
        .map_err(|error| error.to_string())?;
    if !base.is_dir() {
        return Err("qualification status requires a directory".into());
    }
    let view = match (stage, gaps) {
        (Some(stage), _) => View::Stage(stage),
        (None, true) => View::Gaps,
        (None, false) => View::All,
    };
    let (report, exit) = filtered(inspect(&base)?, view)?;
    if json {
        print_utf8(&pretty_json(&report)?)?;
    } else {
        println!(
            "Qualification journal inspection for {:?}",
            report.directory
        );
        if let Some(summary) = &report.recorded_summary {
            println!(
                "Recorded campaign {:?}. Stages passed {}/{}. Registered qualification {}.",
                summary.campaign_id,
                summary.passed_stages,
                summary.total_stages,
                if summary.completed_registered_qualification {
                    "passed"
                } else {
                    "incomplete"
                }
            );
            for category in &summary.missing_product_acceptance {
                println!("  Missing product acceptance {category:?}");
            }
        }
        if let Some(error) = &report.summary_error {
            println!("Qualification summary error {error:?}");
        }
        for error in &report.journal_errors {
            println!(
                "Journal inspection error {:?} {}. {:?}",
                error.journal, error.state, error.reason
            );
        }
        for stage in &report.stages {
            println!(
                "{} {}. {:?}",
                stage.id.escape_debug(),
                stage.state,
                stage.reason
            );
            if let Some(path) = &stage.journal {
                println!("  journal {path:?}");
            }
            if let Some(path) = &stage.evidence {
                println!("  evidence location {path:?}");
            }
            if let Some(action) = &stage.action {
                println!("  {}. argv {:?}", action.description, action.argv);
            }
        }
        if let Some(action) = &report.action {
            println!("{}. argv {:?}", action.description, action.argv);
        }
        for note in &report.notes {
            println!("Diagnostic note {note:?}");
        }
        println!("Journal inspection ran no validator. Evidence replay uses qualify-check.");
    }
    Ok(exit)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn base(directory: &tempfile::TempDir) -> PathBuf {
        fs::canonicalize(directory.path()).unwrap()
    }

    fn recorded(base: &Path, index: usize, id: &str, result: Result<i32, String>) {
        let mut stage = stage(id.into(), Vec::new());
        result_stage(&mut stage, result);
        journal(base, index, &stage).unwrap();
    }

    fn row<'a>(report: &'a StatusReport, id: &str) -> &'a StageObservation {
        report.stages.iter().find(|stage| stage.id == id).unwrap()
    }

    #[test]
    fn gaps_keep_real_refusals_and_omit_only_recorded_passes() {
        let temporary = tempfile::tempdir().unwrap();
        let base = base(&temporary);
        recorded(&base, 0, "current-abi", Ok(0));
        fs::write(base.join("current-abi.json"), b"recorded report").unwrap();
        recorded(&base, 1, "stock-c", Ok(1));
        fs::write(base.join("stock-c.json"), b"recorded report").unwrap();
        recorded(
            &base,
            2,
            "provision-checker",
            Err("pinned checker is unavailable".into()),
        );

        let normal = inspect(&base).unwrap();
        assert_eq!(row(&normal, "current-abi").state, "recorded-passed");
        assert_eq!(row(&normal, "stock-c").state, "recorded-failed");
        assert!(row(&normal, "stock-c").action.is_some());
        assert_eq!(
            row(&normal, "provision-checker").reason,
            "pinned checker is unavailable"
        );
        let (gaps, exit) = filtered(normal, View::Gaps).unwrap();
        assert_eq!(
            exit, 0,
            "an honestly recorded failure is a valid inspection"
        );
        assert!(!gaps.stages.iter().any(|stage| stage.id == "current-abi"));
        assert!(gaps.stages.iter().any(|stage| stage.id == "stock-c"));
        assert_eq!(
            fs::read_dir(&base).unwrap().count(),
            5,
            "inspection publishes nothing"
        );
    }

    #[test]
    fn missing_pass_evidence_stays_a_refusal_after_stage_or_gap_filtering() {
        let temporary = tempfile::tempdir().unwrap();
        let base = base(&temporary);
        recorded(&base, 0, "current-abi", Ok(0));
        recorded(&base, 1, "official-corpus", Ok(0));
        let report = inspect(&base).unwrap();
        for id in ["current-abi", "official-corpus"] {
            assert_eq!(row(&report, id).state, "missing-evidence");
            assert!(row(&report, id).action.is_none());
        }
        let (filtered, exit) = filtered(report, View::Stage("stock-c")).unwrap();
        assert_eq!(exit, 1);
        assert_eq!(filtered.journal_errors.len(), 2);
        let (gaps, exit) = super::filtered(inspect(&base).unwrap(), View::Gaps).unwrap();
        assert_eq!(exit, 1);
        assert_eq!(row(&gaps, "current-abi").state, "missing-evidence");
    }

    #[test]
    fn report_presence_cannot_replace_missing_completion_or_performance_inputs() {
        let temporary = tempfile::tempdir().unwrap();
        let base = base(&temporary);
        fs::write(base.join("completion-check.json"), b"recorded report").unwrap();
        fs::create_dir(base.join("performance")).unwrap();
        fs::write(base.join("performance/domination.json"), b"recorded report").unwrap();
        for (index, id) in ["completion-check", "performance-domination"]
            .into_iter()
            .enumerate()
        {
            let mut stage = stage(
                id.into(),
                vec![path_text(&base.join("missing-manifest.json")).unwrap()],
            );
            result_stage(&mut stage, Ok(0));
            journal(&base, index, &stage).unwrap();
        }
        let (gaps, exit) = filtered(inspect(&base).unwrap(), View::Gaps).unwrap();
        assert_eq!(exit, 1);
        for id in ["completion-check", "performance-domination"] {
            assert_eq!(row(&gaps, id).state, "missing-evidence");
            assert!(row(&gaps, id).action.is_none());
        }
    }

    #[test]
    fn duplicate_or_inconsistent_journals_cannot_select_a_passing_record() {
        let temporary = tempfile::tempdir().unwrap();
        let base = base(&temporary);
        recorded(&base, 0, "stock-c", Ok(0));
        recorded(&base, 1, "stock-c", Ok(1));
        let mut inconsistent = stage("current-abi".into(), Vec::new());
        inconsistent.status = "passed".into();
        inconsistent.exit_code = Some(1);
        journal(&base, 2, &inconsistent).unwrap();

        let report = inspect(&base).unwrap();
        assert_eq!(row(&report, "stock-c").state, "ambiguous-journal");
        assert_eq!(row(&report, "current-abi").state, "inconsistent-journal");
        assert!(row(&report, "stock-c").action.is_none());
        assert_eq!(inspection_exit(&report), 1);
    }

    #[test]
    fn an_attachment_action_requires_the_receipt_recorded_by_the_actual_stage() {
        let temporary = tempfile::tempdir().unwrap();
        let base = base(&temporary);
        for name in ["receipt.json", "other.json", "attached.json"] {
            fs::write(base.join(name), b"retained evidence").unwrap();
        }
        let mut passed = stage(
            "official-corpus".into(),
            vec![
                "official-corpus".into(),
                "manifest.json".into(),
                "--receipt".into(),
                path_text(&base.join("receipt.json")).unwrap(),
            ],
        );
        result_stage(&mut passed, Ok(0));
        passed.receipt = Some(path_text(&base.join("receipt.json")).unwrap());
        passed.attached_manifest = Some(path_text(&base.join("attached.json")).unwrap());
        let observed = observe_stage(
            &base,
            passed.id.clone(),
            Some((base.join("stage-000.json"), passed.clone())),
            EvidenceOwner::Receipt,
        );
        assert_eq!(observed.state, "recorded-passed");
        assert!(observed.action.is_some());
        passed.receipt = Some(path_text(&base.join("other.json")).unwrap());
        let mismatch = observe_stage(
            &base,
            passed.id.clone(),
            Some((base.join("stage-000.json"), passed)),
            EvidenceOwner::Receipt,
        );
        assert_eq!(mismatch.state, "missing-evidence");
        assert!(mismatch.action.is_none());
    }

    #[test]
    fn launch_relative_operands_resolve_only_to_unique_files_inside_the_run() {
        let temporary = tempfile::tempdir().unwrap();
        let base = base(&temporary).join("run");
        fs::create_dir(&base).unwrap();
        for name in ["receipt.json", "attached.json"] {
            fs::write(base.join(name), b"retained evidence").unwrap();
        }
        let mut passed = stage(
            "official-corpus".into(),
            vec![
                "official-corpus".into(),
                "run/manifest.json".into(),
                "--receipt".into(),
                "run/receipt.json".into(),
            ],
        );
        result_stage(&mut passed, Ok(0));
        passed.receipt = Some("run/receipt.json".into());
        passed.attached_manifest = Some("run/attached.json".into());
        let observe = || {
            observe_stage(
                &base,
                passed.id.clone(),
                Some((base.join("stage-000.json"), passed.clone())),
                EvidenceOwner::Receipt,
            )
        };
        assert_eq!(observe().state, "recorded-passed");
        assert!(observe().action.is_some());
        // EvidenceRef paths, unlike historical command operands, are always
        // relative to the run itself and cannot acquire an ancestral anchor.
        assert!(local_file(&base, Path::new("run/receipt.json")).is_none());
        assert!(recorded_file(&base, Path::new("../receipt.json")).is_none());

        fs::create_dir(base.join("run")).unwrap();
        fs::write(base.join("run/receipt.json"), b"ambiguous second receipt").unwrap();
        assert!(recorded_file(&base, Path::new("run/receipt.json")).is_none());
        assert_eq!(observe().state, "missing-evidence");
        assert!(observe().action.is_none());
    }

    #[test]
    fn malformed_and_oversized_journals_do_not_hide_later_real_refusals() {
        let temporary = tempfile::tempdir().unwrap();
        let base = base(&temporary);
        fs::write(base.join("stage-000.json"), b"{malformed").unwrap();
        let large = fs::File::create(base.join("stage-001.json")).unwrap();
        large.set_len(MAX_JOURNAL_BYTES + 1).unwrap();
        recorded(&base, 2, "stock-c", Err("real later refusal".into()));
        fs::write(base.join("qualification.json"), b"{malformed summary").unwrap();

        let report = inspect(&base).unwrap();
        assert_eq!(report.journal_errors.len(), 2);
        assert!(report.summary_error.is_some());
        assert_eq!(row(&report, "stock-c").reason, "real later refusal");
        assert!(report.action.is_none());
        assert_eq!(inspection_exit(&report), 1);
    }

    #[test]
    fn existing_v2_summary_must_match_its_real_journals_and_local_artifacts() {
        let temporary = tempfile::tempdir().unwrap();
        let base = base(&temporary);
        let mut stages = Vec::new();
        for (index, id) in expected_ids().unwrap().into_iter().enumerate() {
            let mut stage = stage(id, Vec::new());
            result_stage(&mut stage, Err("recorded dependency refusal".into()));
            journal(&base, index, &stage).unwrap();
            stages.push(stage);
        }
        let manifest = base.join("manifest-000.json");
        fs::write(&manifest, b"retained manifest").unwrap();
        let summary = Summary {
            schema: SUMMARY_SCHEMA.into(),
            profile_id: PROFILE_ID.into(),
            campaign_id: "fixture-status".into(),
            manifest: manifest.clone(),
            evaluator_sha256: "0".repeat(64),
            evidence: vec![EvidenceRef {
                path: "manifest-000.json".into(),
                sha256: sha256_bytes(b"retained manifest"),
            }],
            passed_stages: 0,
            completed_registered_qualification: false,
            universal_equivalence_proven: false,
            full_product_ready: false,
            missing_product_acceptance: vec!["unclosed semantic contracts".into()],
            claim: "Recorded observations only".into(),
            stages,
        };
        validate_summary_claims(&summary).unwrap();
        fs::write(
            base.join("qualification.json"),
            pretty_json(&summary).unwrap(),
        )
        .unwrap();

        let report = inspect(&base).unwrap();
        assert_eq!(inspection_exit(&report), 0);
        assert_eq!(report.recorded_summary.unwrap().passed_stages, 0);
        assert!(report.action.is_some());
        fs::remove_file(&manifest).unwrap();
        let missing = inspect(&base).unwrap();
        assert_eq!(inspection_exit(&missing), 1);
        assert!(missing.action.is_none());
        assert!(missing
            .summary_error
            .unwrap()
            .contains("manifest is unavailable"));

        fs::write(&manifest, b"retained manifest").unwrap();
        let mut changed = summary.stages[0].clone();
        changed.error = Some("different journal refusal".into());
        fs::write(base.join("stage-000.json"), pretty_json(&changed).unwrap()).unwrap();
        let changed = inspect(&base).unwrap();
        assert_eq!(inspection_exit(&changed), 1);
        assert!(changed
            .summary_error
            .unwrap()
            .contains("differs from journal"));
    }

    #[test]
    fn checkpoint_actions_require_local_operands_and_a_producer_bound_header() {
        let temporary = tempfile::tempdir().unwrap();
        let base = base(&temporary);
        fs::create_dir(base.join("official-corpus-results.evidence")).unwrap();
        let records = base.join("official-corpus-results.evidence/records.jsonl");
        fs::write(
            &records,
            b"{\"schema\":\"ay-official-corpus-record-stream/v2\",\"producer\":{}}\n",
        )
        .unwrap();
        assert!(checkpoint_action(&base).unwrap().is_none());
        fs::write(
            base.join("official-corpus.json"),
            b"retained corpus manifest",
        )
        .unwrap();
        let report = inspect(&base).unwrap();
        let action = row(&report, "official-corpus").action.as_ref().unwrap();
        assert!(action.argv.iter().any(|word| Path::new(word) == records));
        assert_eq!(inspection_exit(&report), 0);
        // Selecting an inspection command does not validate the header, manifest,
        // or row bytes. The real checkpoint owner remains responsible for that.
        fs::write(
            &records,
            b"{\"schema\":\"ay-official-corpus-record-stream/v1\"}\n",
        )
        .unwrap();
        let old = inspect(&base).unwrap();
        assert!(row(&old, "official-corpus").action.is_none());
        assert!(old
            .notes
            .iter()
            .any(|note| note.contains("producer-bound v2")));
        fs::remove_file(&records).unwrap();
        assert!(checkpoint_action(&base).unwrap().is_none());
    }

    #[cfg(unix)]
    #[test]
    fn symlinked_journals_and_external_receipts_never_supply_replay_operands() {
        let temporary = tempfile::tempdir().unwrap();
        let base = base(&temporary);
        let outside = tempfile::tempdir().unwrap();
        let external = outside.path().join("evidence.json");
        fs::write(&external, b"external evidence").unwrap();
        std::os::unix::fs::symlink(&external, base.join("stage-000.json")).unwrap();
        let mut passed = stage("official-corpus".into(), Vec::new());
        result_stage(&mut passed, Ok(0));
        passed.receipt = Some(path_text(&external).unwrap());
        passed.attached_manifest = Some(path_text(&external).unwrap());
        journal(&base, 1, &passed).unwrap();

        let report = inspect(&base).unwrap();
        assert_eq!(inspection_exit(&report), 1);
        assert_eq!(row(&report, "official-corpus").state, "missing-evidence");
        assert!(row(&report, "official-corpus").action.is_none());
        assert!(local_file(&base, &external).is_none());
        assert!(local_file(&base, Path::new("../evidence.json")).is_none());
    }
}
