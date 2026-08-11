// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expand a sparse official-field seed into an exact-coverage campaign bundle.
//!
//! This is deliberately an example binary rather than production library API:
//! it is a repository-maintenance tool used to produce reviewable JSON
//! artifacts. The generated documents are validated against their exact bytes
//! before either output is installed.

use std::collections::{BTreeMap, HashSet};
use std::env;
use std::ffi::OsString;
use std::fmt;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};

use ay_bench::campaign::{
    load_and_validate_campaign, AyScoreReport, AyScoreRow, CampaignIdentity, CatalogTrack,
    ContinuousCatalog, OfficialFieldReport, OfficialLeaderboard, ScoreDisposition,
    CAMPAIGN_SCHEMA_VERSION,
};
use serde::Deserialize;
use sha2::{Digest, Sha256};
use tempfile::{Builder, NamedTempFile};

const USAGE: &str = "\
Usage:
  seed_continuous_campaign \\
    --catalog <catalog.toml> \\
    --seed <official-seed.json> \\
    --official-output <official-field.json> \\
    --ay-output <ay-score-report.json> \\
    --generated-at <timestamp> [--force]
";

type Result<T> = std::result::Result<T, ToolError>;

#[derive(Debug)]
struct ToolError(String);

impl ToolError {
    fn new(message: impl Into<String>) -> Self {
        Self(message.into())
    }
}

impl fmt::Display for ToolError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for ToolError {}

#[derive(Debug)]
struct Args {
    catalog: PathBuf,
    seed: PathBuf,
    official_output: PathBuf,
    ay_output: PathBuf,
    generated_at: String,
    force: bool,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct OfficialSeed {
    schema_version: u32,
    leaderboards: Vec<OfficialLeaderboard>,
}

#[derive(Clone, Copy, Debug)]
enum CatalogStatusRule {
    Final,
    PartialRequired,
    Exact(ScoreDisposition),
}

fn main() {
    match parse_args(env::args_os().skip(1)).and_then(run) {
        Ok(()) => {}
        Err(error) if error.0 == USAGE => {
            print!("{USAGE}");
        }
        Err(error) => {
            eprintln!("seed_continuous_campaign: {error}");
            eprintln!("{USAGE}");
            std::process::exit(2);
        }
    }
}

#[allow(
    clippy::unnecessary_debug_formatting,
    reason = "Debug preserves the bytes of a non-Unicode command-line argument"
)]
fn parse_args(arguments: impl IntoIterator<Item = OsString>) -> Result<Args> {
    let mut catalog = None;
    let mut seed = None;
    let mut official_output = None;
    let mut ay_output = None;
    let mut generated_at = None;
    let mut force = false;
    let mut arguments = arguments.into_iter();

    while let Some(flag) = arguments.next() {
        match flag.to_str() {
            Some("--catalog") => set_once_path(
                &mut catalog,
                "--catalog",
                next_value(&mut arguments, "--catalog")?,
            )?,
            Some("--seed") => {
                set_once_path(&mut seed, "--seed", next_value(&mut arguments, "--seed")?)?
            }
            Some("--official-output") => set_once_path(
                &mut official_output,
                "--official-output",
                next_value(&mut arguments, "--official-output")?,
            )?,
            Some("--ay-output") => set_once_path(
                &mut ay_output,
                "--ay-output",
                next_value(&mut arguments, "--ay-output")?,
            )?,
            Some("--generated-at") => {
                let value = next_value(&mut arguments, "--generated-at")?;
                let value = value.into_string().map_err(|_| {
                    ToolError::new("--generated-at must contain valid Unicode text")
                })?;
                set_once(&mut generated_at, "--generated-at", value)?;
            }
            Some("--force") if !force => force = true,
            Some("--force") => return Err(ToolError::new("--force was provided more than once")),
            Some("--help" | "-h") => return Err(ToolError::new(USAGE)),
            Some(flag) => return Err(ToolError::new(format!("unknown argument {flag}"))),
            None => {
                return Err(ToolError::new(format!(
                    "argument is not valid Unicode: {flag:?}"
                )))
            }
        }
    }

    let args = Args {
        catalog: required(catalog, "--catalog")?,
        seed: required(seed, "--seed")?,
        official_output: required(official_output, "--official-output")?,
        ay_output: required(ay_output, "--ay-output")?,
        generated_at: required(generated_at, "--generated-at")?,
        force,
    };
    ensure_distinct_paths(&args)?;
    Ok(args)
}

fn next_value(
    arguments: &mut impl Iterator<Item = OsString>,
    flag: &'static str,
) -> Result<OsString> {
    arguments
        .next()
        .ok_or_else(|| ToolError::new(format!("{flag} requires a value")))
}

fn set_once_path(target: &mut Option<PathBuf>, flag: &'static str, value: OsString) -> Result<()> {
    set_once(target, flag, PathBuf::from(value))
}

fn set_once<T>(target: &mut Option<T>, flag: &'static str, value: T) -> Result<()> {
    if target.replace(value).is_some() {
        return Err(ToolError::new(format!(
            "{flag} was provided more than once"
        )));
    }
    Ok(())
}

fn required<T>(value: Option<T>, flag: &'static str) -> Result<T> {
    value.ok_or_else(|| ToolError::new(format!("missing required argument {flag}")))
}

fn ensure_distinct_paths(args: &Args) -> Result<()> {
    let paths = [
        ("--catalog", &args.catalog),
        ("--seed", &args.seed),
        ("--official-output", &args.official_output),
        ("--ay-output", &args.ay_output),
    ];
    for (index, (left_name, left_path)) in paths.iter().enumerate() {
        for (right_name, right_path) in paths.iter().skip(index + 1) {
            if left_path == right_path {
                return Err(ToolError::new(format!(
                    "{left_name} and {right_name} must name different paths"
                )));
            }
        }
    }
    Ok(())
}

fn run(args: Args) -> Result<()> {
    reject_existing_outputs(&args)?;

    let catalog_bytes = read_bytes(&args.catalog, "catalog")?;
    let catalog_text = std::str::from_utf8(&catalog_bytes)
        .map_err(|error| ToolError::new(format!("catalog is not UTF-8: {error}")))?;
    let catalog: ContinuousCatalog = toml::from_str(catalog_text)
        .map_err(|error| ToolError::new(format!("failed to parse catalog: {error}")))?;

    let seed_bytes = read_bytes(&args.seed, "seed")?;
    let seed: OfficialSeed = serde_json::from_slice(&seed_bytes)
        .map_err(|error| ToolError::new(format!("failed to parse seed: {error}")))?;

    let catalog_identity = identity_for_exact_bytes(&args.catalog, &catalog_bytes)?;
    let official =
        expand_official_field(&catalog, seed, &args.generated_at, catalog_identity.clone())?;
    let official_bytes = json_with_newline(&official, "official field")?;
    let official_identity = identity_for_exact_bytes(&args.official_output, &official_bytes)?;
    let ay_report = build_ay_report(
        &catalog,
        &official,
        &args.generated_at,
        catalog_identity,
        official_identity,
    )?;
    let ay_bytes = json_with_newline(&ay_report, "AY score report")?;

    let official_temp = write_same_directory_temp(&args.official_output, &official_bytes)?;
    let ay_temp = write_same_directory_temp(&args.ay_output, &ay_bytes)?;
    load_and_validate_campaign(&args.catalog, official_temp.path(), ay_temp.path())
        .map_err(|error| ToolError::new(format!("generated bundle did not validate: {error}")))?;

    install_validated_bundle(
        official_temp,
        &args.official_output,
        ay_temp,
        &args.ay_output,
        args.force,
    )?;

    println!(
        "wrote {} official leaderboards to {} and {} AY rows to {}",
        official.leaderboards.len(),
        args.official_output.display(),
        ay_report.rows.len(),
        args.ay_output.display()
    );
    Ok(())
}

fn reject_existing_outputs(args: &Args) -> Result<()> {
    if args.force {
        return Ok(());
    }
    for (label, path) in [
        ("official field", &args.official_output),
        ("AY score report", &args.ay_output),
    ] {
        if path.exists() {
            return Err(ToolError::new(format!(
                "{label} output {} already exists; pass --force to replace it",
                path.display()
            )));
        }
    }
    Ok(())
}

fn read_bytes(path: &Path, label: &str) -> Result<Vec<u8>> {
    fs::read(path).map_err(|error| {
        ToolError::new(format!(
            "failed to read {label} {}: {error}",
            path.display()
        ))
    })
}

fn identity_for_exact_bytes(path: &Path, bytes: &[u8]) -> Result<CampaignIdentity> {
    let id = path.to_str().filter(|id| !id.is_empty()).ok_or_else(|| {
        ToolError::new(format!("path is not nonempty Unicode: {}", path.display()))
    })?;
    Ok(CampaignIdentity {
        id: id.to_owned(),
        sha256: Some(sha256_hex(bytes)),
    })
}

fn sha256_hex(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn expand_official_field(
    catalog: &ContinuousCatalog,
    seed: OfficialSeed,
    generated_at: &str,
    catalog_identity: CampaignIdentity,
) -> Result<OfficialFieldReport> {
    if catalog.schema_version != CAMPAIGN_SCHEMA_VERSION {
        return Err(ToolError::new(format!(
            "catalog has schema_version={}; expected {}",
            catalog.schema_version, CAMPAIGN_SCHEMA_VERSION
        )));
    }
    if seed.schema_version != CAMPAIGN_SCHEMA_VERSION {
        return Err(ToolError::new(format!(
            "seed has schema_version={}; expected {}",
            seed.schema_version, CAMPAIGN_SCHEMA_VERSION
        )));
    }

    let mut catalog_ids = HashSet::new();
    for track in &catalog.tracks {
        if !catalog_ids.insert(track.id.as_str()) {
            return Err(ToolError::new(format!(
                "catalog contains duplicate track id {:?}",
                track.id
            )));
        }
    }

    let mut overrides = BTreeMap::new();
    for leaderboard in seed.leaderboards {
        if !catalog_ids.contains(leaderboard.track_id.as_str()) {
            return Err(ToolError::new(format!(
                "seed contains unknown track id {:?}",
                leaderboard.track_id
            )));
        }
        let track_id = leaderboard.track_id.clone();
        if overrides.insert(track_id.clone(), leaderboard).is_some() {
            return Err(ToolError::new(format!(
                "seed contains duplicate track id {track_id:?}"
            )));
        }
    }

    let mut leaderboards = Vec::with_capacity(catalog.tracks.len());
    for track in &catalog.tracks {
        let rule = catalog_status_rule(track)?;
        let leaderboard = match overrides.remove(&track.id) {
            Some(leaderboard) => {
                ensure_override_compatible(track, rule, &leaderboard)?;
                leaderboard
            }
            None => default_leaderboard(track, rule)?,
        };
        leaderboards.push(leaderboard);
    }

    Ok(OfficialFieldReport {
        schema_version: CAMPAIGN_SCHEMA_VERSION,
        generated_at: generated_at.to_owned(),
        catalog: catalog_identity,
        leaderboards,
    })
}

fn catalog_status_rule(track: &CatalogTrack) -> Result<CatalogStatusRule> {
    let rule = match track.status.as_str() {
        "final" => CatalogStatusRule::Final,
        "final-field-partial" | "provisional-field-partial" => CatalogStatusRule::PartialRequired,
        "final-field-unpublished" => CatalogStatusRule::Exact(ScoreDisposition::Pending),
        "cancelled" => CatalogStatusRule::Exact(ScoreDisposition::Cancelled),
        "not-held" | "omitted" => CatalogStatusRule::Exact(ScoreDisposition::NotHeld),
        "demo-no-separate-award"
        | "experimental-no-ranking"
        | "experimental-one-submission-no-published-ranking"
        | "final-unranked"
        | "no-medal-no-entrants" => CatalogStatusRule::Exact(ScoreDisposition::NotRanked),
        "conditional-pending-results"
        | "conditional-unconfirmed"
        | "event-held-public-artifacts-pending"
        | "event-ran-artifacts-pending"
        | "event-running-results-pending"
        | "experimental-pending-results-aggregate-placeholder"
        | "experimental-results-unpublished"
        | "final-aggregate-placeholder"
        | "full-run-window-complete-results-pending"
        | "pending-results"
        | "pending-results-aggregate-placeholder"
        | "planned-separate-event"
        | "provisional-primary-branch-results-public"
        | "results-certified-report-pending"
        | "scheduled"
        | "scheduled-results-pending"
        | "scheduled-unranked" => CatalogStatusRule::Exact(ScoreDisposition::Pending),
        status => {
            return Err(ToolError::new(format!(
                "catalog track {:?} has unsupported status {status:?}",
                track.id
            )))
        }
    };
    Ok(rule)
}

fn ensure_override_compatible(
    track: &CatalogTrack,
    rule: CatalogStatusRule,
    leaderboard: &OfficialLeaderboard,
) -> Result<()> {
    let compatible = match rule {
        CatalogStatusRule::Final => matches!(
            leaderboard.disposition,
            ScoreDisposition::Scored
                | ScoreDisposition::Partial
                | ScoreDisposition::Unmaterialized
                | ScoreDisposition::PendingNormalization
        ),
        CatalogStatusRule::PartialRequired => leaderboard.disposition == ScoreDisposition::Partial,
        CatalogStatusRule::Exact(expected) => leaderboard.disposition == expected,
    };
    if compatible {
        Ok(())
    } else {
        Err(ToolError::new(format!(
            "seed track {:?} has incompatible disposition {}; catalog status is {:?}",
            track.id, leaderboard.disposition, track.status
        )))
    }
}

fn default_leaderboard(
    track: &CatalogTrack,
    rule: CatalogStatusRule,
) -> Result<OfficialLeaderboard> {
    let (disposition, evidence) = match rule {
        CatalogStatusRule::Final => (ScoreDisposition::PendingNormalization, Vec::new()),
        CatalogStatusRule::PartialRequired => {
            return Err(ToolError::new(format!(
                "catalog track {:?} has status final-field-partial but no partial seed override",
                track.id
            )))
        }
        CatalogStatusRule::Exact(disposition) => (disposition, Vec::new()),
    };
    Ok(OfficialLeaderboard {
        track_id: track.id.clone(),
        disposition,
        competitors: Vec::new(),
        denominator: None,
        evidence,
    })
}

fn build_ay_report(
    catalog: &ContinuousCatalog,
    official: &OfficialFieldReport,
    generated_at: &str,
    catalog_identity: CampaignIdentity,
    official_identity: CampaignIdentity,
) -> Result<AyScoreReport> {
    let official_by_id: BTreeMap<_, _> = official
        .leaderboards
        .iter()
        .map(|leaderboard| (leaderboard.track_id.as_str(), leaderboard))
        .collect();
    let mut rows = Vec::with_capacity(catalog.tracks.len());
    for track in &catalog.tracks {
        let official = official_by_id.get(track.id.as_str()).ok_or_else(|| {
            ToolError::new(format!(
                "internal error: official field is missing catalog track {:?}",
                track.id
            ))
        })?;
        let disposition = ay_disposition(track, official.disposition)?;
        rows.push(AyScoreRow {
            track_id: track.id.clone(),
            disposition,
            score: None,
            solves: None,
            rank: None,
            win: None,
            candidate: None,
            corpus: None,
            scorer: None,
            checker: None,
            envelope: None,
            evidence: Vec::new(),
        });
    }
    Ok(AyScoreReport {
        schema_version: CAMPAIGN_SCHEMA_VERSION,
        generated_at: generated_at.to_owned(),
        catalog: catalog_identity,
        official_field: official_identity,
        rows,
    })
}

fn ay_disposition(
    track: &CatalogTrack,
    official_disposition: ScoreDisposition,
) -> Result<ScoreDisposition> {
    if !matches!(
        official_disposition,
        ScoreDisposition::Scored
            | ScoreDisposition::Partial
            | ScoreDisposition::Unmaterialized
            | ScoreDisposition::PendingNormalization
    ) {
        return Ok(official_disposition);
    }
    match track.ay_adapter_status.as_str() {
        "ready" | "partial" => Ok(ScoreDisposition::Pending),
        "unsupported" | "not-applicable" => Ok(ScoreDisposition::Unsupported),
        status => Err(ToolError::new(format!(
            "catalog track {:?} has unsupported AY adapter status {status:?}",
            track.id
        ))),
    }
}

fn json_with_newline<T: serde::Serialize>(value: &T, label: &str) -> Result<Vec<u8>> {
    let mut bytes = serde_json::to_vec_pretty(value)
        .map_err(|error| ToolError::new(format!("failed to serialize {label}: {error}")))?;
    bytes.push(b'\n');
    Ok(bytes)
}

fn write_same_directory_temp(output: &Path, bytes: &[u8]) -> Result<NamedTempFile> {
    let parent = output.parent().unwrap_or_else(|| Path::new("."));
    fs::create_dir_all(parent).map_err(|error| {
        ToolError::new(format!(
            "failed to create output directory {}: {error}",
            parent.display()
        ))
    })?;
    let mut temporary = Builder::new()
        .prefix(".seed-continuous-campaign-")
        .tempfile_in(parent)
        .map_err(|error| {
            ToolError::new(format!(
                "failed to create temporary file in {}: {error}",
                parent.display()
            ))
        })?;
    temporary.write_all(bytes).map_err(|error| {
        ToolError::new(format!(
            "failed to write temporary file {}: {error}",
            temporary.path().display()
        ))
    })?;
    temporary.as_file().sync_all().map_err(|error| {
        ToolError::new(format!(
            "failed to sync temporary file {}: {error}",
            temporary.path().display()
        ))
    })?;
    Ok(temporary)
}

fn install_temp(temporary: NamedTempFile, output: &Path, force: bool, label: &str) -> Result<()> {
    let result = if force {
        temporary.persist(output)
    } else {
        temporary.persist_noclobber(output)
    };
    result.map(|_| ()).map_err(|error| {
        ToolError::new(format!(
            "failed to atomically install {label} {}: {}",
            output.display(),
            error.error
        ))
    })
}

/// Install the already cross-validated packet pair. The two paths cannot be
/// replaced atomically as one filesystem operation, so prepare a same-directory
/// rollback copy of the official packet before changing it. If the AY install
/// fails, restore the exact old official bytes (or remove the newly created
/// official file) before returning the error.
fn install_validated_bundle(
    official_temp: NamedTempFile,
    official_output: &Path,
    ay_temp: NamedTempFile,
    ay_output: &Path,
    force: bool,
) -> Result<()> {
    let official_rollback = if force {
        prepare_rollback(official_output)?
    } else {
        None
    };
    install_temp(official_temp, official_output, force, "official field")?;
    if let Err(install_error) = install_temp(ay_temp, ay_output, force, "AY score report") {
        let had_previous_official = official_rollback.is_some();
        let rollback = rollback_official(official_output, official_rollback, force);
        return match rollback {
            Ok(()) => Err(ToolError::new(format!(
                "{install_error}; {}",
                if had_previous_official {
                    "restored the previous official packet"
                } else {
                    "removed the partially installed official packet"
                }
            ))),
            Err(rollback_error) => Err(ToolError::new(format!(
                "{install_error}; additionally failed to roll back {}: {rollback_error}",
                official_output.display()
            ))),
        };
    }
    Ok(())
}

fn prepare_rollback(output: &Path) -> Result<Option<NamedTempFile>> {
    let metadata = match fs::symlink_metadata(output) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(error) => {
            return Err(ToolError::new(format!(
                "failed to inspect existing output {}: {error}",
                output.display()
            )))
        }
    };
    if !metadata.file_type().is_file() {
        return Err(ToolError::new(format!(
            "refusing to replace non-regular output {}",
            output.display()
        )));
    }
    let bytes = fs::read(output).map_err(|error| {
        ToolError::new(format!(
            "failed to read existing output {} for rollback: {error}",
            output.display()
        ))
    })?;
    let rollback = write_same_directory_temp(output, &bytes)?;
    rollback
        .as_file()
        .set_permissions(metadata.permissions())
        .map_err(|error| {
            ToolError::new(format!(
                "failed to preserve permissions for rollback of {}: {error}",
                output.display()
            ))
        })?;
    Ok(Some(rollback))
}

fn rollback_official(output: &Path, rollback: Option<NamedTempFile>, force: bool) -> Result<()> {
    if let Some(rollback) = rollback {
        return install_temp(rollback, output, true, "official-field rollback");
    }
    if force || output.exists() {
        match fs::remove_file(output) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                return Err(ToolError::new(format!(
                    "failed to remove partially installed official field {}: {error}",
                    output.display()
                )))
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_bench::campaign::{validate_campaign, OfficialCompetitor};
    use serde_json::json;

    fn identity(id: &str) -> CampaignIdentity {
        CampaignIdentity {
            id: id.to_owned(),
            sha256: Some("a".repeat(64)),
        }
    }

    fn track(id: &str, status: &str, adapter: &str) -> CatalogTrack {
        CatalogTrack {
            id: id.to_owned(),
            status: status.to_owned(),
            readiness: "test".to_owned(),
            official_score_kind: "test-score".to_owned(),
            official_score_direction: "maximize".to_owned(),
            ay_adapter_status: adapter.to_owned(),
        }
    }

    fn partial_leaderboard(track_id: &str) -> OfficialLeaderboard {
        OfficialLeaderboard {
            track_id: track_id.to_owned(),
            disposition: ScoreDisposition::Partial,
            competitors: vec![OfficialCompetitor {
                rank: 1,
                name: "Published winner".to_owned(),
                eligible: true,
                winner: true,
                tied: false,
                score: json!({"primary": 1}),
                metrics: json!({"solved": 1}),
            }],
            denominator: None,
            evidence: vec![identity("official-source")],
        }
    }

    fn seed(leaderboards: Vec<OfficialLeaderboard>) -> OfficialSeed {
        OfficialSeed {
            schema_version: CAMPAIGN_SCHEMA_VERSION,
            leaderboards,
        }
    }

    #[test]
    fn sparse_seed_expands_every_catalog_status_and_ay_adapter() {
        let catalog = ContinuousCatalog {
            schema_version: CAMPAIGN_SCHEMA_VERSION,
            scope: "bounded-test-inventory".to_owned(),
            tracks: vec![
                track("comp-2025-final-ready", "final", "ready"),
                track("comp-2025-partial", "final-field-partial", "partial"),
                track("comp-2026-unpublished", "final-field-unpublished", "ready"),
                track("comp-2025-cancelled", "cancelled", "unsupported"),
                track("comp-2025-omitted", "omitted", "not-applicable"),
                track(
                    "comp-2025-unranked",
                    "experimental-no-ranking",
                    "unsupported",
                ),
                track("comp-2025-final-unsupported", "final", "unsupported"),
            ],
        };
        let catalog_identity = identity("catalog");
        let official = expand_official_field(
            &catalog,
            seed(vec![partial_leaderboard("comp-2025-partial")]),
            "2026-07-23T12:00:00Z",
            catalog_identity.clone(),
        )
        .expect("expand sparse seed");
        let official_bytes = json_with_newline(&official, "official field").expect("serialize");
        let ay = build_ay_report(
            &catalog,
            &official,
            "2026-07-23T12:00:00Z",
            catalog_identity,
            CampaignIdentity {
                id: "official.json".to_owned(),
                sha256: Some(sha256_hex(&official_bytes)),
            },
        )
        .expect("build AY report");

        assert_eq!(official.leaderboards.len(), catalog.tracks.len());
        assert_eq!(ay.rows.len(), catalog.tracks.len());
        assert_eq!(
            official.leaderboards[0].disposition,
            ScoreDisposition::PendingNormalization
        );
        assert!(official.leaderboards[0].evidence.is_empty());
        assert_eq!(
            official.leaderboards[1].disposition,
            ScoreDisposition::Partial
        );
        assert_eq!(
            official.leaderboards[2].disposition,
            ScoreDisposition::Pending
        );
        assert_eq!(
            official.leaderboards[3].disposition,
            ScoreDisposition::Cancelled
        );
        assert_eq!(
            official.leaderboards[4].disposition,
            ScoreDisposition::NotHeld
        );
        assert_eq!(
            official.leaderboards[5].disposition,
            ScoreDisposition::NotRanked
        );
        assert_eq!(ay.rows[0].disposition, ScoreDisposition::Pending);
        assert_eq!(ay.rows[1].disposition, ScoreDisposition::Pending);
        assert_eq!(ay.rows[6].disposition, ScoreDisposition::Unsupported);
        validate_campaign(&catalog, &official, &ay).expect("expanded campaign validates");
    }

    #[test]
    fn partial_catalog_row_requires_a_partial_seed_override() {
        let catalog = ContinuousCatalog {
            schema_version: CAMPAIGN_SCHEMA_VERSION,
            scope: "bounded-test-inventory".to_owned(),
            tracks: vec![track("comp-2025-partial", "final-field-partial", "ready")],
        };
        let error = expand_official_field(
            &catalog,
            seed(Vec::new()),
            "2026-07-23T12:00:00Z",
            identity("catalog"),
        )
        .expect_err("missing partial override must fail");
        assert!(error.to_string().contains("no partial seed override"));
    }

    #[test]
    fn duplicate_unknown_and_incompatible_seed_rows_fail_closed() {
        let catalog = ContinuousCatalog {
            schema_version: CAMPAIGN_SCHEMA_VERSION,
            scope: "bounded-test-inventory".to_owned(),
            tracks: vec![track("comp-2025-cancelled", "cancelled", "unsupported")],
        };
        let cancelled = OfficialLeaderboard {
            track_id: "comp-2025-cancelled".to_owned(),
            disposition: ScoreDisposition::Cancelled,
            competitors: Vec::new(),
            denominator: None,
            evidence: Vec::new(),
        };
        let duplicate_error = expand_official_field(
            &catalog,
            seed(vec![cancelled.clone(), cancelled]),
            "2026-07-23T12:00:00Z",
            identity("catalog"),
        )
        .expect_err("duplicate must fail");
        assert!(duplicate_error.to_string().contains("duplicate track id"));

        let unknown_error = expand_official_field(
            &catalog,
            seed(vec![partial_leaderboard("comp-2025-unknown")]),
            "2026-07-23T12:00:00Z",
            identity("catalog"),
        )
        .expect_err("unknown must fail");
        assert!(unknown_error.to_string().contains("unknown track id"));

        let incompatible_error = expand_official_field(
            &catalog,
            seed(vec![partial_leaderboard("comp-2025-cancelled")]),
            "2026-07-23T12:00:00Z",
            identity("catalog"),
        )
        .expect_err("incompatible must fail");
        assert!(incompatible_error
            .to_string()
            .contains("incompatible disposition"));
    }

    #[test]
    fn end_to_end_write_hashes_newline_bytes_and_refuses_overwrite() {
        let directory = tempfile::tempdir().expect("temporary directory");
        let catalog_path = directory.path().join("catalog.toml");
        let seed_path = directory.path().join("seed.json");
        let official_path = directory.path().join("official.json");
        let ay_path = directory.path().join("ay.json");
        let catalog = ContinuousCatalog {
            schema_version: CAMPAIGN_SCHEMA_VERSION,
            scope: "bounded-test-inventory".to_owned(),
            tracks: vec![track("comp-2025-final", "final", "ready")],
        };
        fs::write(
            &catalog_path,
            toml::to_string(&catalog).expect("serialize catalog"),
        )
        .expect("write catalog");
        fs::write(
            &seed_path,
            serde_json::to_vec(&json!({
                "schema_version": CAMPAIGN_SCHEMA_VERSION,
                "leaderboards": []
            }))
            .expect("serialize seed"),
        )
        .expect("write seed");

        let args = Args {
            catalog: catalog_path.clone(),
            seed: seed_path,
            official_output: official_path.clone(),
            ay_output: ay_path.clone(),
            generated_at: "2026-07-23T12:00:00Z".to_owned(),
            force: false,
        };
        run(args).expect("generate bundle");
        assert!(
            fs::read(&official_path)
                .expect("read official output")
                .ends_with(b"\n"),
            "official identity must cover the emitted trailing newline"
        );
        assert!(
            fs::read(&ay_path).expect("read AY output").ends_with(b"\n"),
            "AY output must end with a newline"
        );
        load_and_validate_campaign(&catalog_path, &official_path, &ay_path)
            .expect("installed bundle validates against exact bytes");

        let overwrite_error = run(Args {
            catalog: catalog_path,
            seed: directory.path().join("seed.json"),
            official_output: official_path,
            ay_output: ay_path,
            generated_at: "2026-07-23T12:00:01Z".to_owned(),
            force: false,
        })
        .expect_err("existing outputs require --force");
        assert!(overwrite_error.to_string().contains("already exists"));
    }

    #[test]
    fn bundle_install_rolls_back_official_when_second_install_fails() {
        for (force, previous) in [(false, None), (true, Some(b"old official".as_slice()))] {
            let directory = tempfile::tempdir().expect("temporary directory");
            let official_path = directory.path().join("official.json");
            let ay_path = directory.path().join("ay.json");
            if let Some(previous) = previous {
                fs::write(&official_path, previous).expect("write previous official");
            }
            fs::create_dir(&ay_path).expect("AY destination failure injection");
            let official_temp =
                write_same_directory_temp(&official_path, b"new official").expect("official temp");
            let ay_temp = write_same_directory_temp(&ay_path, b"new ay").expect("AY temp");

            let error =
                install_validated_bundle(official_temp, &official_path, ay_temp, &ay_path, force)
                    .expect_err("second install must fail");
            assert!(
                error.to_string().contains(if previous.is_some() {
                    "restored"
                } else {
                    "removed"
                }),
                "unexpected rollback diagnostic: {error}"
            );
            match previous {
                Some(previous) => assert_eq!(
                    fs::read(&official_path).expect("restored official"),
                    previous
                ),
                None => assert!(
                    !official_path.exists(),
                    "new official must be removed on rollback"
                ),
            }
        }
    }
}
