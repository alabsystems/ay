// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT-COMP mirror manifest generation and completeness validation.
//!
//! This module is intentionally about benchmark metadata only. It does not run
//! solvers and it does not infer SAT/UNSAT from filenames.

use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::io::Write as _;
use std::path::{Path, PathBuf};

use crate::error::{BenchError, Result, WithContext};

const REPORT_SCHEMA: &str = "ay.sat-mirror-manifest-report/v1";
const DETAILS_SCHEMA: &str = "ay.sat-mirror-manifest-details/v1";
const DEFAULT_MIRROR_DIRNAME: &str = "win-all-software-proof-competitions";

/// Arguments for `ay bench sat-mirror-manifest`.
#[derive(Debug, Clone)]
pub struct SatMirrorManifestArgs {
    /// SAT-COMP mirror root. Defaults to `$SATCOMP_OFFICIAL_MIRROR` or
    /// `$HOME/win-all-software-proof-competitions`.
    pub mirror_root: Option<PathBuf>,
    /// Competition year under `benchmarks/sat/<year>`.
    pub year: String,
    /// Optional explicit compressed benchmark directory.
    pub benchmarks_dir: Option<PathBuf>,
    /// Optional explicit two-column expected-result labels CSV.
    pub labels_csv: Option<PathBuf>,
    /// Optional CSV of official-unknown hashes.
    ///
    /// These rows are allowed to materialize as `unknown` without using the
    /// broad inventory-only `allow_unknown` escape hatch.
    pub official_unknowns_csv: Option<PathBuf>,
    /// Optional official metadata CSV with `hash filename family author`.
    pub metadata_csv: Option<PathBuf>,
    /// Required compressed benchmark count.
    pub expected_count: usize,
    /// Write a SAT delta / matrix-compatible CSV manifest here on success.
    pub out_csv: Option<PathBuf>,
    /// Write a JSON details manifest here on success.
    pub out_json: Option<PathBuf>,
    /// Always write a structured report here, including fail-closed failures.
    pub report_json: Option<PathBuf>,
    /// Permit unknown or missing labels to be materialized as `unknown`.
    ///
    /// This is for inventory/debugging only. Score-bearing manifest generation
    /// should leave this false.
    pub allow_unknown: bool,
}

#[derive(Debug, Clone)]
struct BenchmarkFile {
    hash: String,
    filename: String,
    path: PathBuf,
    size_bytes: u64,
}

#[derive(Debug, Clone)]
struct MetadataRow {
    filename: String,
    family: String,
    author: String,
}

#[derive(Debug, Clone, Serialize)]
struct ManifestRow {
    local_path: String,
    result: String,
    family: String,
    category: String,
    track: String,
    hash: String,
    filename: String,
    size_bytes: u64,
}

#[derive(Debug, Clone, Serialize)]
pub struct MissingLabelRow {
    pub hash: String,
    pub filename: String,
    pub local_path: String,
    pub family: String,
    pub author: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct SatMirrorManifestReport {
    pub schema: &'static str,
    pub status: String,
    pub year: String,
    pub mirror_root: String,
    pub benchmarks_dir: String,
    pub labels_csv: String,
    pub official_unknowns_csv: Option<String>,
    pub metadata_csv: Option<String>,
    pub expected_count: usize,
    pub benchmark_files: usize,
    pub label_rows: usize,
    pub sat_labels: usize,
    pub unsat_labels: usize,
    pub unknown_labels: usize,
    pub manifest_rows: usize,
    pub missing_label_count: usize,
    pub materialized_unknown_label_count: usize,
    pub unresolved_missing_label_count: usize,
    pub stale_label_count: usize,
    pub duplicate_label_count: usize,
    pub ambiguous_file_count: usize,
    pub bad_label_count: usize,
    pub metadata_missing_count: usize,
    pub metadata_filename_mismatch_count: usize,
    pub allow_unknown: bool,
    pub errors: Vec<String>,
    pub missing_labels: Vec<MissingLabelRow>,
    pub stale_labels: Vec<String>,
    pub duplicate_labels: Vec<String>,
    pub ambiguous_files: Vec<String>,
    pub bad_labels: Vec<String>,
    pub metadata_missing: Vec<String>,
    pub metadata_filename_mismatches: Vec<String>,
    pub out_csv: Option<String>,
    pub out_json: Option<String>,
}

#[derive(Debug, Serialize)]
struct DetailsManifest<'a> {
    schema: &'static str,
    source_report_schema: &'static str,
    year: &'a str,
    mirror_root: &'a str,
    labels_csv: &'a str,
    official_unknowns_csv: Option<&'a str>,
    metadata_csv: Option<&'a str>,
    expected_count: usize,
    count: usize,
    rows: &'a [ManifestRow],
}

/// Generate or validate a SAT-COMP mirror manifest.
///
/// On blocked input this still writes `report_json`, when requested, before
/// returning an error. The returned error text is concise; the report contains
/// the exact missing rows.
pub fn cmd_sat_mirror_manifest(args: SatMirrorManifestArgs) -> Result<()> {
    let outcome = build_manifest(&args)?;

    if let Some(report_path) = &args.report_json {
        write_json(report_path, &outcome.report)?;
    }

    if !outcome.report.errors.is_empty() {
        print_report_summary(&outcome.report);
        return Err(BenchError::InvalidArgs {
            reason: format!(
                "SAT-COMP {} mirror manifest is incomplete: {}",
                outcome.report.year,
                outcome.report.errors.join("; ")
            ),
        });
    }

    if let Some(out_csv) = &args.out_csv {
        write_csv(out_csv, &outcome.rows)?;
    }
    if let Some(out_json) = &args.out_json {
        write_details_json(out_json, &outcome.report, &outcome.rows)?;
    }

    print_report_summary(&outcome.report);
    Ok(())
}

struct ManifestOutcome {
    report: SatMirrorManifestReport,
    rows: Vec<ManifestRow>,
}

fn build_manifest(args: &SatMirrorManifestArgs) -> Result<ManifestOutcome> {
    let mirror_root = resolve_mirror_root(args.mirror_root.as_deref())?;
    let benchmarks_dir = args.benchmarks_dir.clone().unwrap_or_else(|| {
        mirror_root
            .join("benchmarks")
            .join("sat")
            .join(&args.year)
            .join("benchmarks")
    });
    let labels_csv = args.labels_csv.clone().unwrap_or_else(|| {
        mirror_root
            .join("benchmarks")
            .join("sat")
            .join(&args.year)
            .join("labels.csv")
    });

    let files = load_benchmark_files(&benchmarks_dir)?;
    let (labels, label_stats) = load_labels(&labels_csv)?;
    let official_unknowns = match &args.official_unknowns_csv {
        Some(path) => load_official_unknowns(path)?,
        None => BTreeSet::new(),
    };
    let metadata = match &args.metadata_csv {
        Some(path) => load_metadata(path)?,
        None => BTreeMap::new(),
    };

    let mut by_hash: BTreeMap<String, Vec<BenchmarkFile>> = BTreeMap::new();
    for file in files {
        by_hash.entry(file.hash.clone()).or_default().push(file);
    }

    let mut rows = Vec::new();
    let mut errors = Vec::new();
    let mut missing_labels = Vec::new();
    let mut materialized_unknown_label_count = 0usize;
    let mut stale_labels = Vec::new();
    let duplicate_labels = label_stats.duplicates.clone();
    let mut ambiguous_files = Vec::new();
    let mut bad_labels = label_stats.bad_labels.clone();
    let mut metadata_missing = Vec::new();
    let mut metadata_filename_mismatches = Vec::new();

    if by_hash.len() != args.expected_count {
        errors.push(format!(
            "expected {} compressed benchmark hashes, found {}",
            args.expected_count,
            by_hash.len()
        ));
    }

    for (hash, matches) in &by_hash {
        if matches.len() != 1 {
            ambiguous_files.push(hash.clone());
            continue;
        }
        let file = &matches[0];
        let meta = metadata.get(hash);
        if args.metadata_csv.is_some() && meta.is_none() {
            metadata_missing.push(hash.clone());
        }
        if let Some(meta) = meta {
            let local_expected = format!("{hash}-{}", meta.filename);
            if file.filename != meta.filename
                && file.path.file_name().and_then(|s| s.to_str()) != Some(local_expected.as_str())
            {
                metadata_filename_mismatches.push(format!(
                    "{} local={} metadata={}",
                    hash,
                    file.path
                        .file_name()
                        .and_then(|s| s.to_str())
                        .unwrap_or("<non-utf8>"),
                    meta.filename
                ));
            }
        }

        let Some(result) = labels.get(hash) else {
            let missing = missing_label_row(file, meta);
            missing_labels.push(missing);
            if args.allow_unknown || official_unknowns.contains(hash) {
                materialized_unknown_label_count += 1;
                rows.push(manifest_row(file, meta, "unknown", &args.year));
            }
            continue;
        };

        if result == "unknown" && !(args.allow_unknown || official_unknowns.contains(hash)) {
            bad_labels.push(format!(
                "{hash}: unknown result is not score-bearing definitive"
            ));
        }
        rows.push(manifest_row(file, meta, result, &args.year));
    }

    let file_hashes: BTreeSet<&str> = by_hash.keys().map(String::as_str).collect();
    for hash in labels.keys() {
        if !file_hashes.contains(hash.as_str()) {
            stale_labels.push(hash.clone());
        }
    }

    let unresolved_missing_label_count = missing_labels
        .len()
        .saturating_sub(materialized_unknown_label_count);
    if unresolved_missing_label_count != 0 && !args.allow_unknown {
        errors.push(format!(
            "{unresolved_missing_label_count} benchmark files have no expected-result label or official-unknown row"
        ));
    }
    if !stale_labels.is_empty() {
        errors.push(format!(
            "{} label rows do not match any benchmark file",
            stale_labels.len()
        ));
    }
    if !duplicate_labels.is_empty() {
        errors.push(format!("{} duplicate label hashes", duplicate_labels.len()));
    }
    if !ambiguous_files.is_empty() {
        errors.push(format!(
            "{} ambiguous benchmark hashes",
            ambiguous_files.len()
        ));
    }
    if !bad_labels.is_empty() {
        errors.push(format!(
            "{} invalid or non-definitive label rows",
            bad_labels.len()
        ));
    }
    if !metadata_missing.is_empty() {
        errors.push(format!(
            "{} benchmark hashes missing metadata rows",
            metadata_missing.len()
        ));
    }
    if !metadata_filename_mismatches.is_empty() {
        errors.push(format!(
            "{} benchmark filenames differ from metadata",
            metadata_filename_mismatches.len()
        ));
    }

    rows.sort_by(|left, right| left.hash.cmp(&right.hash));

    let status = if errors.is_empty() { "ok" } else { "blocked" }.to_string();
    let report = SatMirrorManifestReport {
        schema: REPORT_SCHEMA,
        status,
        year: args.year.clone(),
        mirror_root: display_path(&mirror_root),
        benchmarks_dir: display_path(&benchmarks_dir),
        labels_csv: display_path(&labels_csv),
        official_unknowns_csv: args
            .official_unknowns_csv
            .as_ref()
            .map(|path| display_path(path)),
        metadata_csv: args.metadata_csv.as_ref().map(|path| display_path(path)),
        expected_count: args.expected_count,
        benchmark_files: by_hash.len(),
        label_rows: label_stats.total_rows,
        sat_labels: label_stats.sat,
        unsat_labels: label_stats.unsat,
        unknown_labels: label_stats.unknown,
        manifest_rows: rows.len(),
        missing_label_count: missing_labels.len(),
        materialized_unknown_label_count,
        unresolved_missing_label_count,
        stale_label_count: stale_labels.len(),
        duplicate_label_count: duplicate_labels.len(),
        ambiguous_file_count: ambiguous_files.len(),
        bad_label_count: bad_labels.len(),
        metadata_missing_count: metadata_missing.len(),
        metadata_filename_mismatch_count: metadata_filename_mismatches.len(),
        allow_unknown: args.allow_unknown,
        errors,
        missing_labels,
        stale_labels,
        duplicate_labels,
        ambiguous_files,
        bad_labels,
        metadata_missing,
        metadata_filename_mismatches,
        out_csv: args.out_csv.as_ref().map(|path| display_path(path)),
        out_json: args.out_json.as_ref().map(|path| display_path(path)),
    };

    Ok(ManifestOutcome { report, rows })
}

fn resolve_mirror_root(explicit: Option<&Path>) -> Result<PathBuf> {
    if let Some(path) = explicit {
        return Ok(path.to_path_buf());
    }
    if let Ok(path) = env::var("SATCOMP_OFFICIAL_MIRROR") {
        if !path.trim().is_empty() {
            return Ok(PathBuf::from(path));
        }
    }
    let home = env::var("HOME").map_err(|_| BenchError::InvalidArgs {
        reason: "HOME is not set and --mirror-root was not provided".to_string(),
    })?;
    Ok(PathBuf::from(home).join(DEFAULT_MIRROR_DIRNAME))
}

fn load_benchmark_files(benchmarks_dir: &Path) -> Result<Vec<BenchmarkFile>> {
    if !benchmarks_dir.is_dir() {
        return Err(BenchError::BenchmarksDirMissing {
            path: benchmarks_dir.to_path_buf(),
        });
    }

    let mut files = Vec::new();
    for entry in fs::read_dir(benchmarks_dir)
        .with_bench_context(|| format!("reading {}", benchmarks_dir.display()))?
    {
        let entry = entry?;
        let path = entry.path();
        if !path.is_file() {
            continue;
        }
        let Some(name) = path.file_name().and_then(|s| s.to_str()) else {
            continue;
        };
        if !name.ends_with(".cnf.xz") {
            continue;
        }
        let Some((hash, filename)) = name.split_once('-') else {
            continue;
        };
        files.push(BenchmarkFile {
            hash: hash.to_string(),
            filename: filename.to_string(),
            size_bytes: path.metadata()?.len(),
            path,
        });
    }
    files.sort_by(|left, right| left.hash.cmp(&right.hash));
    Ok(files)
}

struct LabelStats {
    total_rows: usize,
    sat: usize,
    unsat: usize,
    unknown: usize,
    duplicates: Vec<String>,
    bad_labels: Vec<String>,
}

fn load_labels(path: &Path) -> Result<(BTreeMap<String, String>, LabelStats)> {
    let text = fs::read_to_string(path)
        .with_bench_context(|| format!("reading labels {}", path.display()))?;
    let mut labels = BTreeMap::new();
    let mut total_rows = 0;
    let mut sat = 0;
    let mut unsat = 0;
    let mut unknown = 0;
    let mut duplicates = Vec::new();
    let mut bad_labels = Vec::new();

    for (line_index, raw) in text.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let fields: Vec<&str> = line.split(',').map(str::trim).collect();
        if line_index == 0
            && fields.len() >= 2
            && fields[0].eq_ignore_ascii_case("hash")
            && fields[1].eq_ignore_ascii_case("result")
        {
            continue;
        }
        total_rows += 1;
        if fields.len() < 2 || fields[0].is_empty() {
            bad_labels.push(format!("line {}: malformed label row", line_index + 1));
            continue;
        }
        let hash = fields[0].to_string();
        let result = normalize_result(fields[1]);
        match result.as_str() {
            "sat" => sat += 1,
            "unsat" => unsat += 1,
            "unknown" => unknown += 1,
            _ => {
                bad_labels.push(format!(
                    "line {} hash {}: result must be sat, unsat, or unknown, got {:?}",
                    line_index + 1,
                    hash,
                    fields[1]
                ));
                continue;
            }
        }
        if labels.insert(hash.clone(), result).is_some() {
            duplicates.push(hash);
        }
    }

    Ok((
        labels,
        LabelStats {
            total_rows,
            sat,
            unsat,
            unknown,
            duplicates,
            bad_labels,
        },
    ))
}

fn load_official_unknowns(path: &Path) -> Result<BTreeSet<String>> {
    let (labels, stats) = load_labels(path)?;
    if !stats.bad_labels.is_empty() {
        return Err(BenchError::InvalidArgs {
            reason: format!(
                "official unknown labels {} contain malformed rows: {}",
                path.display(),
                stats.bad_labels.join("; ")
            ),
        });
    }
    let non_unknown: Vec<String> = labels
        .iter()
        .filter_map(|(hash, result)| {
            if result == "unknown" {
                None
            } else {
                Some(format!("{hash}:{result}"))
            }
        })
        .collect();
    if !non_unknown.is_empty() {
        return Err(BenchError::InvalidArgs {
            reason: format!(
                "official unknown labels {} must contain only unknown rows: {}",
                path.display(),
                non_unknown.join(", ")
            ),
        });
    }
    Ok(labels.into_keys().collect())
}

fn load_metadata(path: &Path) -> Result<BTreeMap<String, MetadataRow>> {
    let text = fs::read_to_string(path)
        .with_bench_context(|| format!("reading metadata {}", path.display()))?;
    let mut rows = BTreeMap::new();
    for (line_index, raw) in text.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let fields: Vec<&str> = line.split_whitespace().collect();
        if line_index == 0
            && fields.len() >= 4
            && fields[0].eq_ignore_ascii_case("hash")
            && fields[1].eq_ignore_ascii_case("filename")
        {
            continue;
        }
        if fields.len() < 4 {
            return Err(BenchError::InvalidArgs {
                reason: format!(
                    "metadata {} line {} must have hash filename family author",
                    path.display(),
                    line_index + 1
                ),
            });
        }
        rows.insert(
            fields[0].to_string(),
            MetadataRow {
                filename: fields[1].to_string(),
                family: fields[2].to_string(),
                author: fields[3].to_string(),
            },
        );
    }
    Ok(rows)
}

fn normalize_result(value: &str) -> String {
    match value.trim().to_ascii_lowercase().as_str() {
        "sat" | "satisfiable" => "sat".to_string(),
        "unsat" | "unsatisfiable" => "unsat".to_string(),
        "unknown" => "unknown".to_string(),
        other => other.to_string(),
    }
}

fn manifest_row(
    file: &BenchmarkFile,
    metadata: Option<&MetadataRow>,
    result: &str,
    year: &str,
) -> ManifestRow {
    ManifestRow {
        local_path: file.path.to_string_lossy().into_owned(),
        result: result.to_string(),
        family: metadata
            .map(|row| row.family.clone())
            .unwrap_or_else(|| "unknown".to_string()),
        category: format!("satcomp{year}-main-mirror"),
        track: format!("main_{year}"),
        hash: file.hash.clone(),
        filename: file.filename.clone(),
        size_bytes: file.size_bytes,
    }
}

fn missing_label_row(file: &BenchmarkFile, metadata: Option<&MetadataRow>) -> MissingLabelRow {
    MissingLabelRow {
        hash: file.hash.clone(),
        filename: file.filename.clone(),
        local_path: file.path.to_string_lossy().into_owned(),
        family: metadata
            .map(|row| row.family.clone())
            .unwrap_or_else(|| "unknown".to_string()),
        author: metadata
            .map(|row| row.author.clone())
            .unwrap_or_else(|| "unknown".to_string()),
    }
}

fn write_csv(path: &Path, rows: &[ManifestRow]) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    let mut file = fs::File::create(path)?;
    writeln!(
        file,
        "local_path,result,family,category,track,hash,filename,size_bytes"
    )?;
    for row in rows {
        writeln!(
            file,
            "{},{},{},{},{},{},{},{}",
            csv_escape(&row.local_path),
            csv_escape(&row.result),
            csv_escape(&row.family),
            csv_escape(&row.category),
            csv_escape(&row.track),
            csv_escape(&row.hash),
            csv_escape(&row.filename),
            row.size_bytes
        )?;
    }
    Ok(())
}

fn write_details_json(
    path: &Path,
    report: &SatMirrorManifestReport,
    rows: &[ManifestRow],
) -> Result<()> {
    let payload = DetailsManifest {
        schema: DETAILS_SCHEMA,
        source_report_schema: REPORT_SCHEMA,
        year: &report.year,
        mirror_root: &report.mirror_root,
        labels_csv: &report.labels_csv,
        official_unknowns_csv: report.official_unknowns_csv.as_deref(),
        metadata_csv: report.metadata_csv.as_deref(),
        expected_count: report.expected_count,
        count: rows.len(),
        rows,
    };
    write_json(path, &payload)
}

fn write_json<T: Serialize>(path: &Path, payload: &T) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(path, serde_json::to_string_pretty(payload)? + "\n")?;
    Ok(())
}

fn csv_escape(value: &str) -> String {
    if value.contains([',', '"', '\n', '\r']) {
        format!("\"{}\"", value.replace('"', "\"\""))
    } else {
        value.to_string()
    }
}

fn display_path(path: &Path) -> String {
    path.to_string_lossy().into_owned()
}

fn print_report_summary(report: &SatMirrorManifestReport) {
    println!(
        "sat-mirror-manifest status={} year={} benchmarks={} labels={} sat={} unsat={} unknown={} missing={} materialized_unknown={} unresolved_missing={} stale={} duplicates={}",
        report.status,
        report.year,
        report.benchmark_files,
        report.label_rows,
        report.sat_labels,
        report.unsat_labels,
        report.unknown_labels,
        report.missing_label_count,
        report.materialized_unknown_label_count,
        report.unresolved_missing_label_count,
        report.stale_label_count,
        report.duplicate_label_count,
    );
    for missing in report.missing_labels.iter().take(20) {
        println!(
            "missing-label hash={} filename={} family={} author={}",
            missing.hash, missing.filename, missing.family, missing.author
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn write(path: &Path, text: &str) {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(path, text).unwrap();
    }

    fn fixture_root() -> tempfile::TempDir {
        tempfile::tempdir().unwrap()
    }

    #[test]
    fn complete_labels_generate_manifest() {
        let tmp = fixture_root();
        let mirror = tmp.path();
        let bench_dir = mirror.join("benchmarks/sat/2024/benchmarks");
        write(
            &bench_dir.join("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa-alpha.cnf.xz"),
            "a",
        );
        write(
            &bench_dir.join("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb-beta.cnf.xz"),
            "b",
        );
        write(
            &mirror.join("benchmarks/sat/2024/labels.csv"),
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,sat\nbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb,unsat\n",
        );
        let meta = tmp.path().join("meta.csv");
        write(
            &meta,
            "hash filename family author\naaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa alpha.cnf.xz alpha-family alice\nbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb beta.cnf.xz beta-family bob\n",
        );

        let out_csv = tmp.path().join("out/manifest.csv");
        let out_json = tmp.path().join("out/manifest.json");
        let report = tmp.path().join("out/report.json");
        cmd_sat_mirror_manifest(SatMirrorManifestArgs {
            mirror_root: Some(mirror.to_path_buf()),
            year: "2024".to_string(),
            benchmarks_dir: None,
            labels_csv: None,
            official_unknowns_csv: None,
            metadata_csv: Some(meta),
            expected_count: 2,
            out_csv: Some(out_csv.clone()),
            out_json: Some(out_json.clone()),
            report_json: Some(report.clone()),
            allow_unknown: false,
        })
        .unwrap();

        let csv = fs::read_to_string(out_csv).unwrap();
        assert!(csv.contains("alpha-family"));
        assert!(csv.contains("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"));
        let details: serde_json::Value =
            serde_json::from_str(&fs::read_to_string(out_json).unwrap()).unwrap();
        assert_eq!(details["count"], 2);
        let report: serde_json::Value =
            serde_json::from_str(&fs::read_to_string(report).unwrap()).unwrap();
        assert_eq!(report["status"], "ok");
        assert_eq!(report["missing_label_count"], 0);
    }

    #[test]
    fn missing_labels_block_by_default() {
        let tmp = fixture_root();
        let mirror = tmp.path();
        let bench_dir = mirror.join("benchmarks/sat/2024/benchmarks");
        write(
            &bench_dir.join("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa-alpha.cnf.xz"),
            "a",
        );
        write(
            &bench_dir.join("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb-beta.cnf.xz"),
            "b",
        );
        write(
            &mirror.join("benchmarks/sat/2024/labels.csv"),
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,sat\n",
        );

        let report = tmp.path().join("report.json");
        let err = cmd_sat_mirror_manifest(SatMirrorManifestArgs {
            mirror_root: Some(mirror.to_path_buf()),
            year: "2024".to_string(),
            benchmarks_dir: None,
            labels_csv: None,
            official_unknowns_csv: None,
            metadata_csv: None,
            expected_count: 2,
            out_csv: None,
            out_json: None,
            report_json: Some(report.clone()),
            allow_unknown: false,
        })
        .unwrap_err();

        assert!(err.to_string().contains("mirror manifest is incomplete"));
        let report: serde_json::Value =
            serde_json::from_str(&fs::read_to_string(report).unwrap()).unwrap();
        assert_eq!(report["status"], "blocked");
        assert_eq!(report["missing_label_count"], 1);
        assert_eq!(
            report["missing_labels"][0]["hash"],
            "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
        );
    }

    #[test]
    fn allow_unknown_materializes_missing_label_as_inventory_only() {
        let tmp = fixture_root();
        let mirror = tmp.path();
        let bench_dir = mirror.join("benchmarks/sat/2024/benchmarks");
        write(
            &bench_dir.join("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa-alpha.cnf.xz"),
            "a",
        );
        write(
            &bench_dir.join("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb-beta.cnf.xz"),
            "b",
        );
        write(
            &mirror.join("benchmarks/sat/2024/labels.csv"),
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,sat\n",
        );

        let out_csv = tmp.path().join("manifest.csv");
        cmd_sat_mirror_manifest(SatMirrorManifestArgs {
            mirror_root: Some(mirror.to_path_buf()),
            year: "2024".to_string(),
            benchmarks_dir: None,
            labels_csv: None,
            official_unknowns_csv: None,
            metadata_csv: None,
            expected_count: 2,
            out_csv: Some(out_csv.clone()),
            out_json: None,
            report_json: None,
            allow_unknown: true,
        })
        .unwrap();

        let csv = fs::read_to_string(out_csv).unwrap();
        assert!(csv.contains("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb-beta.cnf.xz,unknown"));
    }

    #[test]
    fn official_unknowns_materialize_only_audited_missing_labels() {
        let tmp = fixture_root();
        let mirror = tmp.path();
        let bench_dir = mirror.join("benchmarks/sat/2024/benchmarks");
        write(
            &bench_dir.join("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa-alpha.cnf.xz"),
            "a",
        );
        write(
            &bench_dir.join("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb-beta.cnf.xz"),
            "b",
        );
        write(
            &mirror.join("benchmarks/sat/2024/labels.csv"),
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,sat\n",
        );
        let official_unknowns = tmp.path().join("official-unknowns.csv");
        write(
            &official_unknowns,
            "hash,result\nbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb,unknown\n",
        );

        let out_csv = tmp.path().join("manifest.csv");
        let report = tmp.path().join("report.json");
        cmd_sat_mirror_manifest(SatMirrorManifestArgs {
            mirror_root: Some(mirror.to_path_buf()),
            year: "2024".to_string(),
            benchmarks_dir: None,
            labels_csv: None,
            official_unknowns_csv: Some(official_unknowns),
            metadata_csv: None,
            expected_count: 2,
            out_csv: Some(out_csv.clone()),
            out_json: None,
            report_json: Some(report.clone()),
            allow_unknown: false,
        })
        .unwrap();

        let csv = fs::read_to_string(out_csv).unwrap();
        assert!(csv.contains("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb-beta.cnf.xz,unknown"));
        let report: serde_json::Value =
            serde_json::from_str(&fs::read_to_string(report).unwrap()).unwrap();
        assert_eq!(report["status"], "ok");
        assert_eq!(report["missing_label_count"], 1);
        assert_eq!(report["materialized_unknown_label_count"], 1);
        assert_eq!(report["unresolved_missing_label_count"], 0);
    }
}
