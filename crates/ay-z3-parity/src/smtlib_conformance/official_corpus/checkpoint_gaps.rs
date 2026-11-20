// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Read a stable, complete-row prefix of the official corpus checkpoint.

use super::*;
use crate::smtlib_conformance::worklist::Worklist;

const CHECKPOINT_SCHEMA: &str = "ay-official-corpus-checkpoint-gaps/v1";
const CHECKPOINT_WORKLIST_SCHEMA: &str = "ay-official-corpus-checkpoint-gap-worklist/v1";
const CHECKPOINT_MODE: &str = "recorded checkpoint observation without evidence replay";

pub(in crate::smtlib_conformance) fn gaps(args: &[String]) -> Result<i32, String> {
    if args == ["--help"] || args == ["-h"] {
        println!(
            "Usage: ay-z3-parity official-corpus-gaps --checkpoint RECORDS.jsonl --corpus-manifest CORPUS.json [--worklist NEW_JSONL]\nInspect a stable prefix of a producer-bound v2 corpus checkpoint without replaying its evidence."
        );
        return Ok(0);
    }
    let (records, corpus, worklist) = parse_args(args)?;
    let report = inspect_checkpoint(&records, &corpus, worklist.as_deref())?;
    print_utf8(&pretty_json(&report)?)?;
    Ok(0)
}

fn parse_args(args: &[String]) -> Result<(PathBuf, PathBuf, Option<PathBuf>), String> {
    let mut records = None;
    let mut corpus = None;
    let mut worklist = None;
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        let target = match arg.as_str() {
            "--checkpoint" => &mut records,
            "--corpus-manifest" => &mut corpus,
            "--worklist" => &mut worklist,
            _ => return Err(format!("unknown official-corpus-gaps option {arg:?}")),
        };
        let path = args
            .next()
            .filter(|value| !value.is_empty() && !value.starts_with('-'))
            .ok_or_else(|| format!("{arg} needs a path"))?;
        if target.replace(PathBuf::from(path)).is_some() {
            return Err(format!("official-corpus-gaps takes one {arg} path"));
        }
    }
    Ok((
        records.ok_or("official-corpus-gaps needs --checkpoint")?,
        corpus.ok_or("official-corpus-gaps needs --corpus-manifest")?,
        worklist,
    ))
}

#[derive(Default, Serialize)]
struct GapCounts {
    failed_files: usize,
    files_with_only_execution_failures: usize,
    failed_queries: usize,
    queries_with_unaccepted_evidence: usize,
    shared_unknown_queries: usize,
    ay_files_with_missing_verdicts: usize,
    ay_files_with_extra_verdicts: usize,
    z3_files_with_missing_verdicts: usize,
    z3_files_with_extra_verdicts: usize,
}

#[derive(Serialize)]
struct CheckpointReport {
    schema: &'static str,
    mode: &'static str,
    header: records::Header,
    snapshot: records::CheckpointSnapshot,
    files_expected: usize,
    queries_expected: usize,
    recorded_counts: CorpusRunCounts,
    gaps: GapCounts,
    worklist: Option<PathBuf>,
}

fn inspect_checkpoint(
    checkpoint: &Path,
    input: &Path,
    worklist_path: Option<&Path>,
) -> Result<CheckpointReport, String> {
    let initial_manifest = fs::symlink_metadata(input)
        .map_err(|error| format!("inspect official corpus manifest: {error}"))?;
    let (input_sha256, manifest) =
        read_hashed_json(input, MAX_CORPUS_MANIFEST_BYTES, "official corpus manifest")?;
    validate_manifest_for_use(&manifest, ManifestUse::Checkpoint)?;
    let mut gaps = GapCounts::default();
    let mut counts = CorpusRunCounts::default();
    let mut worklist = worklist_path
        .map(|path| {
            Worklist::stage(
                path,
                &serde_json::json!({
                    "kind": "header",
                    "schema": CHECKPOINT_WORKLIST_SCHEMA,
                    "mode": CHECKPOINT_MODE,
                    "corpus_manifest_sha256": input_sha256,
                }),
            )
        })
        .transpose()?;
    let (header, snapshot) = records::inspect_checkpoint(
        checkpoint,
        |header| header.require_checkpoint_population(&manifest, &input_sha256),
        |header, index, row| {
            let file = manifest
                .files
                .get(index)
                .ok_or("checkpoint record exceeds corpus population")?;
            require_file_result_identity(row, file)?;
            if row.input_size != Some(file.size) {
                return Err(format!(
                    "official corpus input size drift for {:?}",
                    file.path
                ));
            }
            require_recorded_classification(row, file)?;
            require_recorded_evidence_shape(header, row)?;
            accumulate_run_counts(&mut counts, row)?;
            observe_gaps(index, row, &mut gaps, worklist.as_mut())
        },
    )?;
    let current_manifest = fs::symlink_metadata(input)
        .map_err(|error| format!("inspect official corpus manifest: {error}"))?;
    if !same_observed_regular_file(&initial_manifest, &current_manifest) {
        return Err("corpus manifest changed during checkpoint inspection".into());
    }
    if let Some(worklist) = worklist {
        let rows = worklist.rows();
        check_worklist_population(rows, &gaps)?;
        worklist.publish(&serde_json::json!({
            "kind": "summary",
            "rows": rows,
            "header": &header,
            "snapshot": &snapshot,
            "recorded_counts": &counts,
            "gaps": &gaps,
        }))?;
    }
    Ok(CheckpointReport {
        schema: CHECKPOINT_SCHEMA,
        mode: CHECKPOINT_MODE,
        header,
        snapshot,
        files_expected: manifest.files.len(),
        queries_expected: manifest.query_count,
        recorded_counts: counts,
        gaps,
        worklist: worklist_path.map(Path::to_owned),
    })
}

fn require_recorded_evidence_shape(header: &records::Header, file: &FileRun) -> Result<(), String> {
    for query in &file.queries {
        let evidence = &query.evidence;
        let complete = match evidence.status {
            EvidenceStatus::AcceptedSat => {
                query.ay == Some(CorpusVerdict::Sat)
                    && !evidence.has_proof_evidence()
                    && evidence.sat.as_ref().is_some_and(|model| {
                        model
                            .records_accepted_model(&query.prefix_sha256, header.reference_sha256())
                    })
            }
            EvidenceStatus::AcceptedUnsat => {
                query.ay == Some(CorpusVerdict::Unsat)
                    && header.has_pinned_checker()
                    && evidence.sat.is_none()
                    && evidence
                        .problem
                        .as_ref()
                        .is_some_and(|problem| problem.sha256 == query.prefix_sha256)
                    && evidence.proof.is_some()
                    && evidence.producer.as_ref().is_some_and(|producer| {
                        producer.process.is_complete()
                            && producer.process.verdicts == [CorpusVerdict::Unsat]
                    })
                    && evidence.checker.as_ref().is_some_and(|checker| {
                        checker.process.is_complete()
                            && checker.stdout == "valid\n"
                            && checker.stderr.is_empty()
                    })
            }
            _ => true,
        };
        if !complete {
            return Err(format!(
                "checkpoint lacks the recorded evidence required for {:?} query {}",
                file.path, query.ordinal
            ));
        }
    }
    Ok(())
}

fn check_worklist_population(rows: usize, counts: &GapCounts) -> Result<(), String> {
    if rows != counts.failed_files + counts.failed_queries {
        return Err("official corpus gap worklist has an incomplete row count".into());
    }
    Ok(())
}

fn observe_gaps(
    index: usize,
    file: &FileRun,
    counts: &mut GapCounts,
    mut worklist: Option<&mut Worklist>,
) -> Result<(), String> {
    counts.ay_files_with_missing_verdicts += usize::from(file.ay.verdicts.len() < file.query_count);
    counts.ay_files_with_extra_verdicts += usize::from(file.ay.verdicts.len() > file.query_count);
    counts.z3_files_with_missing_verdicts += usize::from(file.z3.verdicts.len() < file.query_count);
    counts.z3_files_with_extra_verdicts += usize::from(file.z3.verdicts.len() > file.query_count);

    let query_gaps = file
        .queries
        .iter()
        .filter(|query| is_query_gap(query))
        .count();
    let input = Input {
        file_ordinal: index + 1,
        path: &file.path,
        input_sha256: &file.input_sha256,
        input_size: file
            .input_size
            .ok_or("checkpoint record has no input size")?,
    };
    if file.outcome != FileOutcome::Pass {
        let execution_only = query_gaps == 0;
        counts.failed_files += 1;
        counts.files_with_only_execution_failures += usize::from(execution_only);
        if let Some(worklist) = worklist.as_deref_mut() {
            worklist.append(&WorkItem::File {
                input,
                outcome: file.outcome,
                expected_query_count: file.query_count,
                failed_queries: query_gaps,
                execution_only,
                ay: &file.ay,
                z3: &file.z3,
            })?;
        }
    }
    counts.failed_queries += query_gaps;
    for query in &file.queries {
        counts.shared_unknown_queries += usize::from(
            query.ay == Some(CorpusVerdict::Unknown) && query.z3 == Some(CorpusVerdict::Unknown),
        );
        let evidence_accepted = query.evidence.satisfies(query.ay);
        counts.queries_with_unaccepted_evidence += usize::from(!evidence_accepted);
        if let Some(worklist) = worklist
            .as_deref_mut()
            .filter(|_| query.outcome != QueryOutcome::Pass || !evidence_accepted)
        {
            worklist.append(&WorkItem::Query {
                input,
                ordinal: query.ordinal,
                command: &query.command,
                prefix_sha256: &query.prefix_sha256,
                outcome: query.outcome,
                ay: query.ay,
                z3: query.z3,
                evidence_status: query.evidence.status,
                evidence_reason: &query.evidence.reason,
            })?;
        }
    }
    Ok(())
}

fn is_query_gap(query: &QueryRun) -> bool {
    query.outcome != QueryOutcome::Pass || !query.evidence.satisfies(query.ay)
}

#[derive(Clone, Copy, Serialize)]
struct Input<'a> {
    file_ordinal: usize,
    path: &'a str,
    input_sha256: &'a str,
    input_size: u64,
}

#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
enum WorkItem<'a> {
    File {
        #[serde(flatten)]
        input: Input<'a>,
        outcome: FileOutcome,
        expected_query_count: usize,
        failed_queries: usize,
        execution_only: bool,
        ay: &'a ProcessRun,
        z3: &'a ProcessRun,
    },
    Query {
        #[serde(flatten)]
        input: Input<'a>,
        ordinal: usize,
        command: &'a str,
        prefix_sha256: &'a str,
        outcome: QueryOutcome,
        ay: Option<CorpusVerdict>,
        z3: Option<CorpusVerdict>,
        evidence_status: EvidenceStatus,
        evidence_reason: &'a str,
    },
}

#[cfg(test)]
mod tests {
    use super::*;

    fn process(verdicts: &[CorpusVerdict]) -> ProcessRun {
        let mut run = ProcessRun::unavailable(String::new());
        run.harness_error = None;
        run.exit_code = Some(0);
        run.stdin_complete = true;
        run.verdicts = verdicts.to_vec();
        run
    }

    fn file(path: &str, ay: &[CorpusVerdict], z3: &[CorpusVerdict]) -> FileRun {
        let source = b"(check-sat)";
        let digest = sha256_bytes(source);
        let mut row = classify_file(
            &CorpusFile {
                path: format!("QF_UF/{path}.smt2"),
                size: source.len() as u64,
                sha256: digest.clone(),
                queries: vec![CorpusQuery {
                    ordinal: 1,
                    command: "check-sat".into(),
                    byte_start: 0,
                    byte_end: source.len() as u64,
                    command_sha256: digest.clone(),
                    prefix_sha256: digest,
                }],
                echoes: None,
            },
            process(ay),
            process(z3),
        );
        row.input_size = Some(source.len() as u64);
        row
    }

    #[test]
    fn worklist_keeps_execution_only_rows_and_every_query_gap() {
        use CorpusVerdict::{Sat, Unknown, Unsat};
        let directory = tempfile::tempdir().unwrap();
        let worklist = directory.path().join("gaps.jsonl");
        let extra = file("extra", &[Unknown, Sat], &[Unknown]);
        let missing = file("missing", &[Sat], &[]);
        let mut uncertified = file("uncertified", &[Unsat], &[Unsat]);
        uncertified.queries[0].evidence.reason = "rejected proof evidence".repeat(300);
        let unknown = file("unknown", &[Unknown], &[Unknown]);
        let expected_reason = uncertified.queries[0].evidence.reason.clone();
        let rows = [extra, missing, uncertified, unknown];
        let mut gaps = GapCounts::default();
        let mut staged = Worklist::stage(
            &worklist,
            &serde_json::json!({"schema": CHECKPOINT_WORKLIST_SCHEMA}),
        )
        .unwrap();
        for (index, row) in rows.iter().enumerate() {
            observe_gaps(index, row, &mut gaps, Some(&mut staged)).unwrap();
        }
        assert!(!worklist.exists());
        let summary = serde_json::to_string(&gaps).unwrap();
        assert!(summary.len() < expected_reason.len());
        assert_eq!(gaps.failed_files, 3);
        assert_eq!(gaps.failed_queries, 2);
        assert_eq!(gaps.files_with_only_execution_failures, 1);
        assert_eq!(gaps.ay_files_with_extra_verdicts, 1);
        assert_eq!(gaps.z3_files_with_missing_verdicts, 1);
        assert_eq!(gaps.shared_unknown_queries, 2);
        assert_eq!(gaps.queries_with_unaccepted_evidence, 2);
        let count = staged.rows();
        check_worklist_population(count, &gaps).unwrap();
        staged
            .publish(&serde_json::json!({"kind": "summary", "rows": count}))
            .unwrap();

        let text = fs::read_to_string(&worklist).unwrap();
        let exported: Vec<serde_json::Value> = text
            .lines()
            .map(|row| serde_json::from_str(row).unwrap())
            .collect();
        assert_eq!(exported.len(), 7);
        assert_eq!(exported[0]["schema"], CHECKPOINT_WORKLIST_SCHEMA);
        assert_eq!(exported[1]["kind"], "file");
        assert_eq!(exported[1]["execution_only"], true);
        assert_eq!(
            exported[1]["ay"]["verdicts"],
            serde_json::json!(["unknown", "sat"])
        );
        assert_eq!(exported[3]["kind"], "query");
        assert_eq!(exported[3]["input_sha256"], rows[1].input_sha256);
        assert_eq!(
            exported[3]["prefix_sha256"],
            rows[1].queries[0].prefix_sha256
        );
        assert_eq!(exported[3]["ordinal"], 1);
        assert_eq!(exported[3]["outcome"], "missing");
        assert_eq!(exported[3]["ay"], "sat");
        assert!(exported[3]["z3"].is_null());
        assert_eq!(exported[5]["evidence_status"], "unavailable");
        assert_eq!(exported[5]["evidence_reason"], expected_reason);
        assert_eq!(exported[6]["rows"], 5);
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            assert_eq!(
                fs::metadata(&worklist).unwrap().permissions().mode() & 0o777,
                0o600
            );
        }
    }
}
