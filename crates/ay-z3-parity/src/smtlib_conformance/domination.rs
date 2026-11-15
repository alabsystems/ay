// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Repeated, population-bound performance qualification. Scoreboard's ordinary
//! zero exit means no detected contradiction, not replacement or domination.
use super::*;
use sha2::Digest as _;
mod measurements;
#[cfg(test)]
use measurements::assess;
use measurements::{execution_conditions, Campaign, ParsedRun};
use official_corpus::PerformanceFile;

const RECEIPT_SCHEMA: &str = "ay-z3-measured-domination/v2";
const RECEIPT_SCOPE: &str = "complete pinned official corpus; FFI eval timings; same host, one sequential job; median per-file measurements; proof validation measured separately";
const MAX_SCOREBOARD_BYTES: u64 = 2 * 1024 * 1024 * 1024;

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct ScoreboardArtifact {
    repeat: usize,
    file: String,
    sha256: String,
    exit_code: i32,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Receipt {
    schema: String,
    profile: String,
    campaign: String,
    contract_sha256: String,
    corpus_manifest_sha256: String,
    ay_executable_sha256: String,
    ay_library_sha256: String,
    z3_library_sha256: String,
    repetitions: usize,
    timeout_seconds: u64,
    universal_equivalence_proven: bool,
    scope: String,
    execution_conditions: Value,
    assessment: Assessment,
    scoreboards: Vec<ScoreboardArtifact>,
}

const HELP: &str = "smtlib-conformance dominate <manifest> --corpus-manifest FILE --directory DIR [--timeout SECONDS] [--repetitions ODD]\nRuns the complete authenticated official corpus, sequentially, at least three times.\nNo checkpoint reuse, sampling, or division filtering. Uses median per-file time\nand RSS, requires no capability losses and no slower timed file or aggregate.\nThis is measured performance on this host and corpus, not universal superiority.\n";

/// Recompute an assessment from the exact retained observations, without
/// rerunning the solvers. This authenticates input identities and consistency;
/// independent timing reproduction still requires a fresh measurement run.
pub(super) fn check(args: &[String]) -> Result<i32, String> {
    if args
        .iter()
        .any(|arg| matches!(arg.as_str(), "--help" | "-h"))
    {
        println!(
            "smtlib-conformance dominate-check <manifest> --corpus-manifest FILE --receipt FILE\nAuthenticates binaries, corpus and retained scoreboards; recomputes every\nrepeat and the median assessment without rerunning solvers. This validates\nretained evidence consistency. It does not independently authenticate claimed\ntiming observations: reproduce those with a fresh dominate run."
        );
        return Ok(0);
    }
    let mut manifest = None;
    let mut corpus = None;
    let mut receipt = None;
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--corpus-manifest" => {
                corpus = Some(PathBuf::from(
                    args.next().ok_or("--corpus-manifest needs a path")?,
                ))
            }
            "--receipt" => {
                receipt = Some(PathBuf::from(args.next().ok_or("--receipt needs a path")?))
            }
            value if value.starts_with('-') => {
                return Err(format!("unknown dominate-check option {value}"));
            }
            value => {
                if manifest.replace(PathBuf::from(value)).is_some() {
                    return Err("dominate-check takes one contract".to_string());
                }
            }
        }
    }
    let loaded = load_contract(&manifest.ok_or("dominate-check needs a contract")?)?;
    validate_contract(&loaded.contract, &loaded.base, ValidationMode::Structural)?;
    let corpus = corpus.ok_or("dominate-check needs --corpus-manifest")?;
    let receipt_path = receipt.ok_or("dominate-check needs --receipt")?;
    let receipt: Receipt = serde_json::from_slice(&read_bounded_bytes(
        &receipt_path,
        8 * 1024 * 1024,
        "domination receipt",
        true,
    )?)
    .map_err(|error| format!("invalid domination receipt: {error}"))?;
    let executable = loaded
        .contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("missing AY executable")?;
    let library = loaded
        .contract
        .subject
        .ay_shared_library
        .as_ref()
        .ok_or("missing AY library")?;
    let reference = &loaded.contract.profile.z3_overlay.reference_shared_library;
    verify_artifact(executable, &loaded.base, "AY executable")?;
    verify_artifact(library, &loaded.base, "AY library")?;
    verify_reference_artifact(&reference.path, &reference.sha256, "Z3 library")?;
    let (_, population, corpus_sha) = official_corpus::performance_population(&corpus)?;
    let expected = ReplayBinding {
        profile: &loaded.contract.profile.id,
        campaign: &loaded.contract.campaign_id,
        contract_sha256: &loaded.sha256,
        corpus_sha256: &corpus_sha,
        cli_sha256: &executable.sha256,
        ay_sha256: &library.sha256,
        z3_sha256: &reference.sha256,
    };
    let directory = receipt_path
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    let assessment = replay(&receipt, directory, &population, &expected)?;
    verify_artifact(executable, &loaded.base, "AY executable")?;
    verify_artifact(library, &loaded.base, "AY library")?;
    verify_reference_artifact(&reference.path, &reference.sha256, "Z3 library")?;
    if sha256_file(&corpus, "corpus manifest")? != corpus_sha {
        return Err("corpus manifest changed during domination replay".to_string());
    }
    println!(
        "domination_consistency=PASS measured_domination={} independent_timing_reproduction=false",
        assessment.passed
    );
    Ok(i32::from(!assessment.passed))
}

struct ReplayBinding<'a> {
    profile: &'a str,
    campaign: &'a str,
    contract_sha256: &'a str,
    corpus_sha256: &'a str,
    cli_sha256: &'a str,
    ay_sha256: &'a str,
    z3_sha256: &'a str,
}

fn replay(
    receipt: &Receipt,
    directory: &Path,
    population: &[PerformanceFile],
    binding: &ReplayBinding<'_>,
) -> Result<Assessment, String> {
    if receipt.schema != RECEIPT_SCHEMA
        || receipt.scope != RECEIPT_SCOPE
        || receipt.universal_equivalence_proven
        || receipt.profile != binding.profile
        || receipt.campaign != binding.campaign
        || receipt.contract_sha256 != binding.contract_sha256
        || receipt.corpus_manifest_sha256 != binding.corpus_sha256
        || receipt.ay_executable_sha256 != binding.cli_sha256
        || receipt.ay_library_sha256 != binding.ay_sha256
        || receipt.z3_library_sha256 != binding.z3_sha256
    {
        return Err("domination receipt scope or authenticated identity mismatch".to_string());
    }
    if !(3..=31).contains(&receipt.repetitions)
        || receipt.repetitions % 2 == 0
        || receipt.scoreboards.len() != receipt.repetitions
        || !(1..=3600).contains(&receipt.timeout_seconds)
    {
        return Err("invalid domination repetition count or timeout".to_string());
    }
    let mut campaign = Campaign::new(population)?;
    for (repeat, artifact) in receipt.scoreboards.iter().enumerate() {
        if artifact.repeat != repeat || artifact.file != format!("scoreboard-{repeat}.json") {
            return Err(
                "domination scoreboards were omitted, duplicated, or reordered".to_string(),
            );
        }
        validate_sha256(&artifact.sha256, "scoreboard digest")?;
        let path = resolve_relative_evidence_path(directory, &artifact.file)?;
        let report = read_scoreboard(&path, &artifact.sha256)?;
        if report.timeout_secs != receipt.timeout_seconds
            || execution_conditions(&report)? != receipt.execution_conditions
        {
            return Err(
                "scoreboard timeout or execution conditions differ from receipt".to_string(),
            );
        }
        campaign.record(
            artifact.exit_code,
            report,
            binding.cli_sha256,
            binding.ay_sha256,
            binding.z3_sha256,
        )?;
    }
    let actual = campaign.finish()?;
    if actual != receipt.assessment {
        return Err("claimed domination assessment differs from retained measurements".to_string());
    }
    Ok(actual)
}

fn read_scoreboard(path: &Path, expected_sha256: &str) -> Result<ParsedRun, String> {
    let (digest, parsed) = read_written_scoreboard(path)?;
    if digest != expected_sha256 {
        return Err("retained scoreboard digest or size mismatch".to_string());
    }
    Ok(parsed)
}

/// Hash the exact byte stream consumed by the parser, retaining only the
/// measured fields rather than an additional multi-gigabyte JSON tree. A new
/// producer has no prior digest to authenticate: derive its identity from this
/// same stream instead of reading the entire file once before parsing it.
/// Retained replay compares this identity with its receipt, and the producer
/// still rehashes every retained scoreboard before completing the campaign.
fn read_written_scoreboard(path: &Path) -> Result<(String, ParsedRun), String> {
    struct HashedReader<R> {
        inner: R,
        digest: Sha256,
        bytes: u64,
    }
    impl<R: std::io::Read> std::io::Read for HashedReader<R> {
        fn read(&mut self, output: &mut [u8]) -> std::io::Result<usize> {
            let read = self.inner.read(output)?;
            self.bytes = self
                .bytes
                .checked_add(read as u64)
                .ok_or_else(|| std::io::Error::other("scoreboard byte count overflow"))?;
            if self.bytes > MAX_SCOREBOARD_BYTES {
                return Err(std::io::Error::other("scoreboard exceeds its byte bound"));
            }
            self.digest.update(&output[..read]);
            Ok(read)
        }
    }
    let metadata = fs::symlink_metadata(path).map_err(|error| error.to_string())?;
    if !metadata.file_type().is_file() || metadata.len() > MAX_SCOREBOARD_BYTES {
        return Err("scoreboard must be a bounded non-symlink regular file".to_string());
    }
    let file = fs::File::open(path).map_err(|error| error.to_string())?;
    // serde_json's Read adapter requests individual bytes. Buffer outside the
    // hashing layer so SHA-256 consumes file chunks rather than one update
    // per JSON byte. A successful parse also consumes trailing whitespace
    // through EOF, preserving the complete retained-file identity.
    let mut reader = std::io::BufReader::new(HashedReader {
        inner: file,
        digest: Sha256::new(),
        bytes: 0,
    });
    let parsed = serde_json::from_reader(&mut reader)
        .map_err(|error| format!("invalid scoreboard: {error}"))?;
    let reader = reader.into_inner();
    if reader.bytes != metadata.len() {
        return Err("retained scoreboard digest or size mismatch".to_string());
    }
    Ok((format!("{:x}", reader.digest.finalize()), parsed))
}

pub(super) fn run(args: &[String]) -> Result<i32, String> {
    if args.iter().any(|a| a == "--help" || a == "-h") {
        print!("{HELP}");
        return Ok(0);
    }
    let mut manifest = None;
    let mut corpus = None;
    let mut directory = None;
    let mut timeout = 10u64;
    let mut repetitions = 3usize;
    let mut index = 0;
    while index < args.len() {
        let arg = &args[index];
        match arg.as_str() {
            "--corpus-manifest" | "--directory" | "--timeout" | "--repetitions" => {
                index += 1;
                let value = args
                    .get(index)
                    .ok_or_else(|| format!("{arg} needs a value"))?;
                match arg.as_str() {
                    "--corpus-manifest" => corpus = Some(PathBuf::from(value)),
                    "--directory" => directory = Some(PathBuf::from(value)),
                    "--timeout" => timeout = value.parse().map_err(|_| "invalid timeout")?,
                    _ => repetitions = value.parse().map_err(|_| "invalid repetitions")?,
                }
            }
            value if value.starts_with('-') => {
                return Err(format!("unknown dominate option {value}"));
            }
            value => {
                if manifest.replace(PathBuf::from(value)).is_some() {
                    return Err("dominate takes one contract".to_string());
                }
            }
        }
        index += 1;
    }
    if !(1..=3600).contains(&timeout) || !(3..=31).contains(&repetitions) || repetitions % 2 == 0 {
        return Err("timeout must be 1..3600; repetitions must be odd and 3..31".to_string());
    }
    let loaded = load_contract(&manifest.ok_or("dominate needs a contract")?)?;
    validate_contract(&loaded.contract, &loaded.base, ValidationMode::Structural)?;
    let corpus = corpus.ok_or("dominate needs --corpus-manifest")?;
    let directory = directory.ok_or("dominate needs --directory")?;
    let executable = loaded
        .contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("missing AY executable")?;
    let library = loaded
        .contract
        .subject
        .ay_shared_library
        .as_ref()
        .ok_or("missing AY library")?;
    verify_artifact(executable, &loaded.base, "AY executable")?;
    verify_artifact(library, &loaded.base, "AY library")?;
    let target = &loaded.contract.profile.z3_overlay;
    verify_reference_artifact(
        &target.reference_shared_library.path,
        &target.reference_shared_library.sha256,
        "Z3 library",
    )?;
    let (root, population, corpus_sha) = official_corpus::performance_population(&corpus)?;
    fs::create_dir(&directory)
        .map_err(|error| format!("create fresh performance directory: {error}"))?;
    let mut campaign = Campaign::new(&population)?;
    let mut scoreboards = Vec::new();
    let mut conditions = None;
    for repeat in 0..repetitions {
        let output = directory.join(format!("scoreboard-{repeat}.json"));
        eprintln!(
            "performance repeat {}/{}: {} complete files",
            repeat + 1,
            repetitions,
            population.len()
        );
        let code = crate::scoreboard::run(&crate::scoreboard::ScoreboardConfig {
            ay: artifact_path(&loaded.base, &library.path),
            ay_cli: Some(artifact_path(&loaded.base, &executable.path)),
            z3: reference_artifact_path(&target.reference_shared_library.path)?,
            root: root.clone(),
            timeout_secs: timeout,
            jobs: 1,
            json_out: output.clone(),
            baseline: None,
            divisions: None,
            checkpoint: Some(directory.join(format!("scoreboard-{repeat}.checkpoint.jsonl"))),
            resume: false,
            sample: None,
            seed: 0,
            progress: Some(directory.join("progress.json")),
        });
        // Even a failed run is evidence. Missing output remains an explicit error.
        let (digest, report) = read_written_scoreboard(&output)?;
        if report.timeout_secs != timeout {
            return Err("scoreboard did not use the requested timeout".to_string());
        }
        if conditions.is_none() {
            conditions = Some(execution_conditions(&report)?);
        }
        campaign.record(
            code,
            report,
            &executable.sha256,
            &library.sha256,
            &target.reference_shared_library.sha256,
        )?;
        scoreboards.push(ScoreboardArtifact {
            repeat,
            file: format!("scoreboard-{repeat}.json"),
            sha256: digest,
            exit_code: code,
        });
    }
    // The exact manifest digest already binds every derived path and query
    // count. Reauthenticate that original manifest and its complete live
    // materialization without allocating a second parent-side population.
    provision::authenticate_corpus_manifest(&corpus, &corpus_sha, None)?;
    verify_artifact(executable, &loaded.base, "AY executable")?;
    verify_artifact(library, &loaded.base, "AY library")?;
    verify_reference_artifact(
        &target.reference_shared_library.path,
        &target.reference_shared_library.sha256,
        "Z3 library",
    )?;
    let assessment = campaign.finish()?;
    for artifact in &scoreboards {
        if sha256_file(&directory.join(&artifact.file), "scoreboard")? != artifact.sha256 {
            return Err("scoreboard changed during qualification".to_string());
        }
    }
    let path = directory.join("domination.json");
    let receipt = Receipt {
        schema: RECEIPT_SCHEMA.to_string(),
        profile: loaded.contract.profile.id.clone(),
        campaign: loaded.contract.campaign_id.clone(),
        contract_sha256: loaded.sha256,
        corpus_manifest_sha256: corpus_sha,
        ay_executable_sha256: executable.sha256.clone(),
        ay_library_sha256: library.sha256.clone(),
        z3_library_sha256: target.reference_shared_library.sha256.clone(),
        repetitions,
        timeout_seconds: timeout,
        universal_equivalence_proven: false,
        scope: RECEIPT_SCOPE.to_string(),
        execution_conditions: conditions.ok_or("performance produced no run conditions")?,
        assessment,
        scoreboards,
    };
    atomic_write_new(&path, &pretty_json(&receipt)?)?;
    println!(
        "domination_receipt={} measured_domination={}",
        path.display(),
        receipt.assessment.passed
    );
    Ok(i32::from(!receipt.assessment.passed))
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq)]
#[serde(deny_unknown_fields)]
struct Assessment {
    passed: bool,
    files: usize,
    timed_files: usize,
    slower_files: usize,
    greater_memory_files: usize,
    capability_losses: usize,
    execution_or_validation_failures: usize,
    median_total_ay_ms: f64,
    median_total_z3_ms: f64,
}

fn number(value: &Value, key: &str) -> Result<f64, String> {
    value
        .get(key)
        .and_then(Value::as_f64)
        .filter(|n| n.is_finite() && *n >= 0.0)
        .ok_or_else(|| format!("missing or invalid {key}"))
}

fn median(values: &mut [f64]) -> f64 {
    values.sort_by(f64::total_cmp);
    values[values.len() / 2]
}

fn verdicts(text: &str) -> Option<Vec<&str>> {
    let values: Vec<_> = text.split(',').collect();
    values
        .iter()
        .all(|v| matches!(*v, "sat" | "unsat" | "unknown"))
        .then_some(values)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn performance_file(path: &str, query_count: usize) -> PerformanceFile {
        PerformanceFile {
            path: path.to_string(),
            query_count,
        }
    }
    fn report(ay: &str, z3: &str, millis: f64) -> Value {
        json!({"kind":"ay-z3-scoreboard", "format_version":3, "timeout_secs":10, "host":{"machine":"fixture"}, "resource":{"effective_jobs":1,"memlimit_mb_per_child":512,"nbcore_per_child":1,"solver_timeout_secs":10,"hard_timeout_secs":12,"external_ffi":{"enforcement":ENFORCEMENT_RSS_WATCHDOG_V1}}, "ay_lib":{"sha256":"a"}, "z3_lib":{"sha256":"z"}, "ay_cli_identity":{"sha256":"c"}, "sampling":{"mode":"all"}, "divisions_filter":null, "pass":true, "self_certification_available":true, "files":[{"file":"f", "ay":{"outcome":ay,"decided":verdicts(ay).is_some_and(|v|v.iter().all(|v|*v!="unknown")),"wall_ms":millis,"peak_rss_bytes":6000000}, "z3":{"outcome":z3,"decided":verdicts(z3).is_some_and(|v|v.iter().all(|v|*v!="unknown")),"wall_ms":20.0,"peak_rss_bytes":6000000}, "self_certified":true, "declared_conflict":false,"verdict_shape_mismatch":false}]})
    }
    fn assessment(value: Value) -> Assessment {
        assessment_with_queries(value, 1)
    }
    fn assessment_with_queries(value: Value, query_count: usize) -> Assessment {
        assess(
            &vec![(0, value); 3],
            &[performance_file("f", query_count)],
            "c",
            "a",
            "z",
        )
        .unwrap()
    }
    #[test]
    fn no_contradictions_does_not_mean_domination() {
        assert!(!assessment(report("unknown", "sat", 1.0)).passed);
        assert!(!assessment(report("sat", "sat", 21.0)).passed);
        assert!(!assessment(report("unknown", "unknown", 1.0)).passed);
        assert!(assessment(report("sat", "sat", 10.0)).passed);
    }
    #[test]
    fn missing_rows_foreign_binaries_and_timeouts_cannot_pass() {
        for (field, value) in [
            ("files", json!([])),
            ("ay_lib", json!({"sha256":"foreign"})),
        ] {
            let mut r = report("sat", "sat", 10.0);
            r[field] = value;
            assert!(assess(&vec![(0, r); 3], &[performance_file("f", 1)], "c", "a", "z").is_err());
        }
        assert!(!assessment(report("timeout", "unknown", 10.0)).passed);
    }
    #[test]
    fn isolated_fast_repeat_cannot_hide_median_regression() {
        let reports = vec![
            (0, report("sat", "sat", 1.0)),
            (0, report("sat", "sat", 30.0)),
            (0, report("sat", "sat", 31.0)),
        ];
        assert!(
            !assess(&reports, &[performance_file("f", 1)], "c", "a", "z")
                .unwrap()
                .passed
        );
    }

    #[test]
    fn multiple_queries_are_compared_positionally() {
        assert!(assessment_with_queries(report("sat,unsat", "sat,unsat", 10.0), 2).passed);
        assert!(!assessment_with_queries(report("sat,unsat", "unsat,sat", 10.0), 2).passed);
        assert!(!assessment_with_queries(report("sat,", "sat,unsat", 10.0), 2).passed);
        assert!(!assessment_with_queries(report("unknown,sat", "sat,unknown", 10.0), 2).passed);
    }

    #[test]
    fn matching_extra_and_missing_query_vectors_never_count_as_domination() {
        for (expected, outcome) in [(1, "sat,sat"), (2, "sat"), (2, "sat,unsat,unknown")] {
            let result = assessment_with_queries(report(outcome, outcome, 1.0), expected);
            assert!(!result.passed);
            assert!(result.execution_or_validation_failures > 0);
            assert_eq!(result.timed_files, 0);
        }
        assert!(assessment_with_queries(report("sat,unsat", "sat,unsat", 1.0), 2).passed);
    }

    #[test]
    fn query_counts_are_bound_per_file_not_just_to_the_total() {
        let mut run = report("sat,sat", "sat,sat", 1.0);
        let mut first = run["files"][0].clone();
        first["file"] = json!("a");
        let mut second = report("sat", "sat", 1.0)["files"][0].clone();
        second["file"] = json!("b");
        run["files"] = json!([first, second]);
        let population = [performance_file("a", 1), performance_file("b", 2)];
        let result = assess(&vec![(0, run); 3], &population, "c", "a", "z").unwrap();
        assert!(!result.passed);
        assert!(result.execution_or_validation_failures > 0);
        assert_eq!(result.timed_files, 0);
        assert!(Campaign::new(&[performance_file("a", 0)]).is_err());
    }

    #[test]
    fn changing_execution_envelope_invalidates_repetition_evidence() {
        let good = report("sat", "sat", 10.0);
        let mut changed = good.clone();
        changed["resource"]["memlimit_mb_per_child"] = json!(1024);
        assert!(assess(
            &[(0, good.clone()), (0, changed), (0, good)],
            &[performance_file("f", 1)],
            "c",
            "a",
            "z"
        )
        .is_err());
    }

    #[test]
    fn row_order_is_irrelevant_but_duplicate_identity_cannot_replace_a_missing_file() {
        let mut first = report("sat", "sat", 10.0);
        let mut a = first["files"][0].clone();
        a["file"] = json!("a");
        let mut b = a.clone();
        b["file"] = json!("b");
        first["files"] = json!([a.clone(), b.clone()]);
        let mut reversed = first.clone();
        reversed["files"] = json!([b, a.clone()]);
        let population = vec![performance_file("a", 1), performance_file("b", 1)];
        assert!(
            assess(
                &[(0, first.clone()), (0, reversed), (0, first.clone())],
                &population,
                "c",
                "a",
                "z"
            )
            .unwrap()
            .passed
        );
        first["files"] = json!([a.clone(), a]);
        assert!(assess(&vec![(0, first); 3], &population, "c", "a", "z").is_err());
    }

    #[test]
    fn missing_memory_and_false_decision_flags_do_not_count_as_evidence() {
        let mut missing = report("sat", "sat", 10.0);
        missing["files"][0]["ay"]["peak_rss_bytes"] = Value::Null;
        assert!(!assessment(missing).passed);
        let mut false_flag = report("sat", "sat", 10.0);
        false_flag["files"][0]["ay"]["decided"] = json!(false);
        assert!(!assessment(false_flag).passed);
    }

    const CLI: &str = "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";
    const AY: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    const Z3: &str = "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd";
    const CONTRACT: &str = "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee";
    const CORPUS: &str = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";

    fn binding() -> ReplayBinding<'static> {
        ReplayBinding {
            profile: "fixture",
            campaign: "fixture-campaign",
            contract_sha256: CONTRACT,
            corpus_sha256: CORPUS,
            cli_sha256: CLI,
            ay_sha256: AY,
            z3_sha256: Z3,
        }
    }

    fn persisted_receipt(directory: &Path) -> Receipt {
        let mut run = report("sat", "sat", 10.0);
        run["ay_lib"]["sha256"] = json!(AY);
        run["z3_lib"]["sha256"] = json!(Z3);
        run["ay_cli_identity"]["sha256"] = json!(CLI);
        let population = vec![performance_file("f", 1)];
        let mut campaign = Campaign::new(&population).unwrap();
        let conditions =
            execution_conditions(&serde_json::from_value(run.clone()).unwrap()).unwrap();
        let mut scoreboards = Vec::new();
        for repeat in 0..3 {
            let bytes = serde_json::to_vec(&run).unwrap();
            let file = format!("scoreboard-{repeat}.json");
            fs::write(directory.join(&file), &bytes).unwrap();
            scoreboards.push(ScoreboardArtifact {
                repeat,
                file,
                sha256: sha256_bytes(&bytes),
                exit_code: 0,
            });
            campaign
                .record(0, serde_json::from_value(run.clone()).unwrap(), CLI, AY, Z3)
                .unwrap();
        }
        Receipt {
            schema: RECEIPT_SCHEMA.to_string(),
            profile: "fixture".to_string(),
            campaign: "fixture-campaign".to_string(),
            contract_sha256: CONTRACT.to_string(),
            corpus_manifest_sha256: CORPUS.to_string(),
            ay_executable_sha256: CLI.to_string(),
            ay_library_sha256: AY.to_string(),
            z3_library_sha256: Z3.to_string(),
            repetitions: 3,
            timeout_seconds: 10,
            universal_equivalence_proven: false,
            scope: RECEIPT_SCOPE.to_string(),
            execution_conditions: conditions,
            assessment: campaign.finish().unwrap(),
            scoreboards,
        }
    }

    #[test]
    fn replay_recomputes_assessment_and_actual_scoreboard_exit_codes() {
        let directory = tempfile::tempdir().unwrap();
        let mut receipt = persisted_receipt(directory.path());
        let population = vec![performance_file("f", 1)];
        assert!(
            replay(&receipt, directory.path(), &population, &binding())
                .unwrap()
                .passed
        );
        receipt.assessment.slower_files = 1;
        assert!(replay(&receipt, directory.path(), &population, &binding()).is_err());
        receipt.assessment.slower_files = 0;
        receipt.scoreboards[1].exit_code = 1;
        assert!(replay(&receipt, directory.path(), &population, &binding()).is_err());
    }

    #[test]
    fn rehashed_matching_extra_verdicts_cannot_preserve_a_passing_receipt() {
        let directory = tempfile::tempdir().unwrap();
        let mut receipt = persisted_receipt(directory.path());
        for scoreboard in &mut receipt.scoreboards {
            let path = directory.path().join(&scoreboard.file);
            let mut run: Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
            run["files"][0]["ay"]["outcome"] = json!("sat,sat");
            run["files"][0]["z3"]["outcome"] = json!("sat,sat");
            let bytes = serde_json::to_vec(&run).unwrap();
            fs::write(path, &bytes).unwrap();
            scoreboard.sha256 = sha256_bytes(&bytes);
        }
        assert!(receipt.assessment.passed);
        assert!(replay(
            &receipt,
            directory.path(),
            &[performance_file("f", 1)],
            &binding()
        )
        .is_err());
    }

    #[test]
    fn replay_refuses_changed_missing_and_reordered_scoreboards() {
        let directory = tempfile::tempdir().unwrap();
        let mut receipt = persisted_receipt(directory.path());
        let population = vec![performance_file("f", 1)];
        receipt.scoreboards.swap(0, 1);
        assert!(replay(&receipt, directory.path(), &population, &binding()).is_err());
        receipt.scoreboards.swap(0, 1);
        let path = directory.path().join("scoreboard-0.json");
        let mut changed: Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        changed["files"][0]["ay"]["wall_ms"] = json!(1000.0);
        fs::write(&path, serde_json::to_vec(&changed).unwrap()).unwrap();
        assert!(replay(&receipt, directory.path(), &population, &binding()).is_err());
        fs::remove_file(path).unwrap();
        assert!(replay(&receipt, directory.path(), &population, &binding()).is_err());
    }

    #[test]
    fn written_scoreboard_stream_preserves_exact_bytes_and_existing_bound() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("scoreboard.json");
        let mut bytes = serde_json::to_vec(&report("sat", "sat", 10.0)).unwrap();
        bytes.extend(std::iter::repeat_n(b' ', 24 * 1024));
        fs::write(&path, &bytes).unwrap();
        let (digest, parsed) = read_written_scoreboard(&path).unwrap();
        assert_eq!(digest, sha256_bytes(&bytes));
        assert_eq!(parsed.timeout_secs, 10);
        assert_eq!(
            read_scoreboard(&path, &digest).unwrap().timeout_secs,
            parsed.timeout_secs
        );
        assert!(read_scoreboard(&path, &"0".repeat(64)).is_err());
        *bytes.last_mut().unwrap() = b'\n';
        fs::write(&path, &bytes).unwrap();
        // Same JSON value, different complete byte stream: the prior digest
        // must not authenticate the later parse.
        assert!(read_scoreboard(&path, &digest).is_err());
        let (changed_digest, _) = read_written_scoreboard(&path).unwrap();
        assert_ne!(digest, changed_digest);
        bytes.extend_from_slice(b"{}");
        fs::write(&path, &bytes).unwrap();
        assert!(read_written_scoreboard(&path).is_err());
        fs::File::create(&path)
            .unwrap()
            .set_len(MAX_SCOREBOARD_BYTES + 1)
            .unwrap();
        assert!(read_written_scoreboard(&path).is_err());
    }

    #[test]
    fn replay_rejects_rehashed_foreign_resources_and_identity() {
        let directory = tempfile::tempdir().unwrap();
        let mut receipt = persisted_receipt(directory.path());
        let population = vec![performance_file("f", 1)];
        receipt.campaign = "different-campaign".to_string();
        assert!(replay(&receipt, directory.path(), &population, &binding()).is_err());
        receipt.campaign = "fixture-campaign".to_string();
        let path = directory.path().join("scoreboard-0.json");
        let mut changed: Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        changed["resource"]["memlimit_mb_per_child"] = json!(1024);
        let bytes = serde_json::to_vec(&changed).unwrap();
        fs::write(path, &bytes).unwrap();
        receipt.scoreboards[0].sha256 = sha256_bytes(&bytes);
        assert!(replay(&receipt, directory.path(), &population, &binding()).is_err());
    }

    #[test]
    fn receipt_schema_rejects_extra_fields_and_unrecorded_exits() {
        let directory = tempfile::tempdir().unwrap();
        let receipt = persisted_receipt(directory.path());
        let mut value = serde_json::to_value(&receipt).unwrap();
        value["trust_me_passed"] = json!(true);
        assert!(serde_json::from_value::<Receipt>(value).is_err());
        let mut value = serde_json::to_value(receipt).unwrap();
        value["scoreboards"][0]
            .as_object_mut()
            .unwrap()
            .remove("exit_code");
        assert!(serde_json::from_value::<Receipt>(value).is_err());
    }

    #[test]
    fn impossible_resource_envelopes_cannot_be_consistent_evidence() {
        for (field, value) in [
            ("memlimit_mb_per_child", 0),
            ("nbcore_per_child", 0),
            ("solver_timeout_secs", 9),
            ("hard_timeout_secs", 9),
        ] {
            let mut run = report("sat", "sat", 10.0);
            run["resource"][field] = json!(value);
            assert!(assess(
                &vec![(0, run); 3],
                &[performance_file("f", 1)],
                "c",
                "a",
                "z"
            )
            .is_err());
        }
    }
}
