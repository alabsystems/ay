// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `ay corpus` — manage benchmark corpora from multiple sources.
//!
//! Each entry in `benchmarks/corpora.toml` describes one corpus with a
//! `source` discriminator. Supported sources:
//!   - `release` (default): tarball uploaded as a GitHub release asset on
//!     the manifest's `repo`/`release_tag`. SHA256-pinned. Two-way:
//!     supports `upload`.
//!   - `http`: archive fetched from a fixed URL. Optionally size/SHA256-pinned;
//!     every declared pin is enforced before publication.
//!     `archive` controls extraction: `tar` (default), `zip`, or `none`.
//!     `wrap_archive = true` owns every archive root as one directory at
//!     `extract_to`, for archives that do not have one matching root.
//!   - `git`: shallow fetch from a URL. Optional `commit` pin; pinned entries
//!     verify an exact, clean checkout rather than accepting any nonempty tree.
//!   - `gbd`: per-file fetch from the Global Benchmark Database, driven by a
//!     `manifest` CSV with `hash` and `local_path` columns. Each row's content
//!     is GET from `https://benchmark-database.de/file/<hash>` and written to
//!     `<local_path>` (typically `…cnf.xz`). Campaign rows also require exact
//!     `size_bytes` and `sha256` response pins and remain compressed; legacy
//!     unpinned test manifests still materialize the decompressed sibling.
//!   - `uri-list`: fetch every HTTPS artifact named by a pinned, locally
//!     managed list into `extract_to`. Campaign lists enforce exact response
//!     sizes and SHA-256 values; compressed CNFs stay compressed so the runner
//!     consumes the verified bytes rather than an unpinned sibling.
//!
//! Verbs include `list`, `plan`, `download`, `verify`, `campaign-audit`,
//! `upload` (release only), and `prune`.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::{BufReader, Read};
use std::path::{Component, Path, PathBuf};
use std::process::{Child, Command as ProcCommand, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

use anyhow::{anyhow, bail, Context, Result};
use clap::{Args, Subcommand};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const DEFAULT_MANIFEST: &str = "benchmarks/corpora.toml";
const DEFAULT_CAMPAIGN_ASSETS: &str = "benchmarks/competition-assets-2025-2026.toml";
const DEFAULT_CAMPAIGN_CATALOG: &str = "benchmarks/continuous-2025-2026.toml";
const CORPUS_PLAN_CAPACITY_NOTE: &str = "Known byte totals are lower bounds: unknown-size \
assets, extracted contents, decompressed materializations, and transactional staging are not \
included. A plan without a capacity warning is not a guarantee that the acquisition will fit.";

#[derive(Subcommand)]
pub(crate) enum CorpusCommand {
    /// Print the corpus table with local status.
    List(ListArgs),
    /// Plan corpus acquisition without network access or filesystem changes.
    Plan(PlanArgs),
    /// Download one or more corpora.
    Download(DownloadArgs),
    /// Verify integrity, provenance, and materialized corpus contents.
    Verify(VerifyArgs),
    /// Audit exact catalog-to-asset coverage and reproducibility pins.
    CampaignAudit(CampaignAuditArgs),
    /// Repack a local directory and upload it as a release asset.
    Upload(UploadArgs),
    /// Remove locally-extracted corpora (and any cached archive).
    Prune(PruneArgs),
    /// Check that every entry's upstream URL (or release asset) still resolves.
    CheckUrls(CheckUrlsArgs),
    /// Refresh the vendored CHC `*_000.smt2` test fixtures from upstream.
    Fixtures(FixturesArgs),
    /// Build and install an external tool used by the test suite
    ///
    /// DEPRECATED alias for `ay tool install`; reads the same registry
    /// (reference/tools.toml). Kept for existing invocations.
    InstallTool(InstallToolArgs),
}

#[derive(Args)]
pub(crate) struct ManifestArgs {
    /// Path to the corpus manifest TOML file.
    #[arg(long, default_value = DEFAULT_MANIFEST)]
    manifest: PathBuf,
}

#[derive(Args)]
pub(crate) struct ListArgs {
    #[command(flatten)]
    manifest: ManifestArgs,
    /// Show only assets assigned to one of these manifest groups.
    #[arg(long = "group", value_name = "GROUP")]
    groups: Vec<String>,
}

#[derive(Args)]
pub(crate) struct PlanArgs {
    #[command(flatten)]
    manifest: ManifestArgs,
    /// Plan every corpus in the manifest.
    #[arg(long)]
    all: bool,
    /// Plan every asset assigned to one of these manifest groups.
    ///
    /// Mutually exclusive with `--all` and explicit corpus names.
    #[arg(long = "group", value_name = "GROUP")]
    groups: Vec<String>,
    /// Emit the complete plan as JSON.
    #[arg(long)]
    json: bool,
    /// Corpus names. Required unless `--all` or `--group` is set.
    names: Vec<String>,
}

#[derive(Args)]
pub(crate) struct DownloadArgs {
    #[command(flatten)]
    manifest: ManifestArgs,
    /// Download every corpus in the manifest.
    #[arg(long)]
    all: bool,
    /// Download every asset assigned to one of these manifest groups.
    ///
    /// Mutually exclusive with `--all` and explicit corpus names.
    #[arg(long = "group", value_name = "GROUP")]
    groups: Vec<String>,
    /// Re-download even if the local copy looks correct.
    #[arg(long)]
    force: bool,
    /// Corpus names. Required unless `--all` or `--group` is set.
    names: Vec<String>,
}

#[derive(Args)]
pub(crate) struct VerifyArgs {
    #[command(flatten)]
    manifest: ManifestArgs,
    /// Verify every corpus in the manifest, including dependency closure.
    #[arg(long)]
    all: bool,
    /// Verify every asset assigned to one of these manifest groups, including dependency closure.
    ///
    /// Mutually exclusive with `--all` and explicit corpus names.
    #[arg(long = "group", value_name = "GROUP")]
    groups: Vec<String>,
    /// Corpus names to verify, including dependency closure.
    ///
    /// Required unless `--all` or `--group` is set.
    names: Vec<String>,
}

#[derive(Args)]
pub(crate) struct CampaignAuditArgs {
    /// Campaign asset coverage manifest.
    #[arg(long, default_value = DEFAULT_CAMPAIGN_ASSETS)]
    assets: PathBuf,
    /// Official competition/track catalog.
    #[arg(long, default_value = DEFAULT_CAMPAIGN_CATALOG)]
    catalog: PathBuf,
    #[command(flatten)]
    manifest: ManifestArgs,
    /// Also fail unless every referenced locally obtainable asset is installed.
    #[arg(long)]
    require_installed: bool,
    /// Emit the audit summary as JSON.
    #[arg(long)]
    json: bool,
}

#[derive(Args)]
pub(crate) struct UploadArgs {
    #[command(flatten)]
    manifest: ManifestArgs,
    /// Name of the (release-source) corpus to upload.
    name: String,
    /// Directory whose contents become the tarball. Defaults to `extract_to`.
    #[arg(long)]
    from: Option<PathBuf>,
    /// Release tag to upload under. Defaults to the manifest's `release_tag`.
    #[arg(long)]
    release_tag: Option<String>,
    /// Overwrite an existing asset of the same name on the release.
    #[arg(long)]
    clobber: bool,
}

#[derive(Args)]
pub(crate) struct CheckUrlsArgs {
    #[command(flatten)]
    manifest: ManifestArgs,
    /// Check every asset assigned to one of these manifest groups.
    ///
    /// Mutually exclusive with explicit corpus names.
    #[arg(long = "group", value_name = "GROUP")]
    groups: Vec<String>,
    /// Only check entries with these names. Default: all entries.
    names: Vec<String>,
}

#[derive(Args)]
pub(crate) struct PruneArgs {
    #[command(flatten)]
    manifest: ManifestArgs,
    #[arg(long)]
    all: bool,
    /// Also delete the cached archive (for release/http sources).
    #[arg(long)]
    archive: bool,
    names: Vec<String>,
}

#[derive(Args)]
pub(crate) struct FixturesArgs {
    /// Directory holding the vendored `*_000.smt2` fixtures.
    #[arg(long, default_value = CHC_FIXTURE_DEST)]
    dest: PathBuf,
}

#[derive(Args)]
pub(crate) struct InstallToolArgs {
    /// Tool to build and install: `drat-trim` (DRAT proof checker, into
    /// ~/.local/bin) or `cadical` (CaDiCaL SAT solver, the reference oracle for
    /// the SAT cross-validation tests, built into reference/cadical/build).
    name: String,
    /// Rebuild and reinstall even if a working binary is already present.
    #[arg(long)]
    force: bool,
}

#[derive(Debug, Serialize, Deserialize)]
struct Manifest {
    schema_version: u32,
    repo: String,
    release_tag: String,
    #[serde(default, rename = "corpus")]
    corpora: Vec<Corpus>,
}

#[derive(Debug, Deserialize)]
struct CampaignAssetManifest {
    schema_version: u32,
    catalog: String,
    corpora_manifest: String,
    profiles_manifest: String,
    scope: String,
    #[serde(default)]
    event: Vec<CampaignAssetEvent>,
}

#[derive(Debug, Deserialize)]
struct CampaignAssetEvent {
    id: String,
    competition: String,
    edition: u32,
    #[serde(default)]
    track_ids: Vec<String>,
    corpus_status: String,
    #[serde(default)]
    corpora: Vec<String>,
    #[serde(default)]
    competitor_corpora: Vec<String>,
    official_machine_status: String,
    local_run_support: String,
    competitor_replay_status: String,
    subset_policy: String,
    reason: String,
}

#[derive(Debug, Deserialize)]
struct CampaignCatalog {
    #[serde(default, rename = "track")]
    tracks: Vec<CampaignCatalogTrack>,
}

#[derive(Debug, Deserialize)]
struct CampaignCatalogTrack {
    id: String,
    competition: String,
    edition: u32,
}

#[derive(Debug, Deserialize)]
struct CampaignRunProfiles {
    schema_version: u32,
    #[serde(default)]
    profile: Vec<CampaignRunProfile>,
    #[serde(default)]
    subset: Vec<CampaignSubsetProfile>,
}

#[derive(Debug, Deserialize)]
struct CampaignRunProfile {
    id: String,
    run_class: String,
    oom_guard_required: bool,
    score_comparable: bool,
    #[serde(default)]
    requires_exact_hardware: bool,
}

#[derive(Debug, Deserialize)]
struct CampaignSubsetProfile {
    id: String,
    kind: String,
    scoring: String,
}

#[derive(Debug, Serialize)]
struct CampaignAuditSummary {
    catalog_tracks: usize,
    catalog_events: usize,
    asset_events: usize,
    referenced_assets: usize,
    referenced_competitor_assets: usize,
    locally_verified_assets: usize,
    locally_missing_or_stale_assets: usize,
    locally_verified_competitor_assets: usize,
    locally_missing_or_stale_competitor_assets: usize,
    run_profiles: usize,
    subset_profiles: usize,
    status_counts: BTreeMap<String, usize>,
    local_run_support_counts: BTreeMap<String, usize>,
    competitor_replay_status_counts: BTreeMap<String, usize>,
    scope: String,
}

#[derive(Debug, Serialize)]
struct CorpusPlanSummary {
    schema_version: u32,
    selected_assets: usize,
    dependency_assets: usize,
    closure_assets: usize,
    installed_assets: usize,
    missing_or_stale_assets: usize,
    network_fetch_assets: usize,
    known_transfer_bytes: u64,
    known_remaining_transfer_bytes: u64,
    unknown_size_sources: BTreeMap<String, usize>,
    unknown_remaining_size_sources: BTreeMap<String, usize>,
    required_tools: Vec<CorpusPlanToolRequirement>,
    missing_tool_requirements: usize,
    filesystem_path: String,
    available_filesystem_bytes: Option<u64>,
    capacity_warning: Option<String>,
    capacity_note: String,
    assets: Vec<CorpusPlanAsset>,
}

#[derive(Debug, Serialize)]
struct CorpusPlanAsset {
    name: String,
    source: String,
    groups: Vec<String>,
    dependencies: Vec<String>,
    selected: bool,
    installed: bool,
    network_fetch_required: bool,
    known_transfer_bytes: u64,
    transfer_size_complete: bool,
    known_remaining_transfer_bytes: u64,
    remaining_transfer_size_complete: bool,
    local_layout: CorpusPlanLocalLayout,
    acquisition: CorpusPlanAcquisition,
    pins: CorpusPlanPins,
    manifest: Option<CorpusPlanManifest>,
}

#[derive(Debug, Serialize)]
struct CorpusPlanLocalLayout {
    destination: CorpusPlanPath,
    cache: Option<CorpusPlanPath>,
    materialization: CorpusPlanMaterialization,
}

#[derive(Debug, Serialize)]
struct CorpusPlanPath {
    declared: String,
    resolved: String,
}

#[derive(Debug, Serialize)]
struct CorpusPlanMaterialization {
    kind: String,
    declared: String,
    resolved: String,
    archive_format: Option<String>,
    archive_layout: Option<String>,
    archive_symlink_policy: Option<String>,
}

#[derive(Debug, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
enum CorpusPlanAcquisition {
    Release {
        repository: String,
        release_tag: String,
        asset: String,
    },
    Http {
        url: String,
        url_redacted: bool,
    },
    Git {
        url: String,
        url_redacted: bool,
        depth: u32,
        requires_git_lfs: bool,
        allowed_unmapped_gitlinks: Vec<String>,
    },
    Gbd {
        file_endpoint: String,
    },
    UriList,
}

#[derive(Debug, Serialize)]
struct CorpusPlanPins {
    sha256: Option<String>,
    size_bytes: Option<u64>,
    git_commit: Option<String>,
}

#[derive(Debug, Serialize)]
struct CorpusPlanManifest {
    kind: String,
    format: String,
    path: CorpusPlanPath,
    sha256: String,
    size_bytes: u64,
    row_count: usize,
    rows: Vec<CorpusPlanManifestRow>,
}

#[derive(Debug, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
enum CorpusPlanManifestRow {
    GbdObject {
        upstream_object_id: String,
        url: String,
        url_redacted: bool,
        size_bytes: Option<u64>,
        sha256: Option<String>,
        download: CorpusPlanPath,
        materialized: Option<CorpusPlanPath>,
    },
    Uri {
        id: String,
        url: String,
        url_redacted: bool,
        size_bytes: Option<u64>,
        sha256: Option<String>,
        download: CorpusPlanPath,
    },
}

#[derive(Debug, Serialize)]
struct CorpusPlanToolRequirement {
    id: String,
    purpose: String,
    alternatives: Vec<String>,
    available: Vec<String>,
    satisfied: bool,
    required_by: Vec<String>,
}

#[derive(Debug)]
struct ToolRequirementAccumulator {
    purpose: &'static str,
    alternatives: BTreeSet<&'static str>,
    required_by: BTreeSet<String>,
}

#[derive(Debug, Clone, Copy, Default)]
struct TransferEstimate {
    known_bytes: u64,
    has_unknown: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct Corpus {
    name: String,
    /// Named acquisition sets, for example `competition-2025-2026`.
    ///
    /// Groups make a complete campaign portable without making
    /// `download --all` the only way to select a coherent asset set.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    groups: Vec<String>,
    /// Other corpus assets that must be installed first.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    depends_on: Vec<String>,
    #[serde(default, skip_serializing_if = "Source::is_default")]
    source: Source,
    extract_to: String,
    // release: required asset filename + sha256, optional size
    #[serde(skip_serializing_if = "Option::is_none")]
    asset: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    sha256: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    size_bytes: Option<u64>,
    // http/git: source URL
    #[serde(skip_serializing_if = "Option::is_none")]
    url: Option<String>,
    /// Stable local archive filename for HTTP endpoints whose URL basename is
    /// generic (for example Zenodo's trailing `/content` endpoint).
    #[serde(skip_serializing_if = "Option::is_none")]
    cache_name: Option<String>,
    // http: archive format
    #[serde(default, skip_serializing_if = "Archive::is_default")]
    archive: Archive,
    // HTTP archives: extract all archive roots into a directory owned as one
    // unit at `extract_to`, rather than expecting one archive root to have that
    // basename. Release upload/download always uses the matching-root layout.
    #[serde(default, skip_serializing_if = "is_false")]
    wrap_archive: bool,
    /// Rewrite a pinned archive's absolute symlink only when its target has
    /// exactly one suffix match among the archive's own members. Relative
    /// in-tree links are preserved; ambiguous, missing, or escaping targets
    /// remain fatal.
    #[serde(default, skip_serializing_if = "is_false")]
    normalize_absolute_archive_symlinks: bool,
    // git: shallow depth (default 1) and optional commit pin
    #[serde(skip_serializing_if = "Option::is_none")]
    depth: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    commit: Option<String>,
    /// The pinned Git tree contains actual Git LFS pointer blobs.
    ///
    /// `.gitattributes` declarations alone do not set this: ordinary Git
    /// blobs may retain historical `filter=lfs` attributes.
    #[serde(default, skip_serializing_if = "is_false")]
    requires_git_lfs: bool,
    /// Pinned mode-160000 entries intentionally lacking `.gitmodules`
    /// mappings. The verifier requires exact equality with the checkout's
    /// unmapped gitlinks; these paths are never initialized or recursed into.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    allowed_unmapped_gitlinks: Vec<String>,
    // gbd: path to the CSV manifest with `hash` and `local_path` columns.
    #[serde(skip_serializing_if = "Option::is_none")]
    manifest: Option<String>,
    // uri-list: row naming and manifest semantics.
    #[serde(default, skip_serializing_if = "UriListFormat::is_default")]
    uri_list_format: UriListFormat,
    /// Filesystem anchor assigned by `Manifest::load`; never serialized.
    #[serde(skip)]
    base_dir: PathBuf,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "lowercase")]
enum Source {
    #[default]
    Release,
    Http,
    Git,
    Gbd,
    #[serde(rename = "uri-list")]
    UriList,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "kebab-case")]
enum UriListFormat {
    #[default]
    GbdCnf,
    RawJson,
}

impl UriListFormat {
    fn is_default(&self) -> bool {
        *self == Self::GbdCnf
    }

    fn label(&self) -> &'static str {
        match self {
            UriListFormat::GbdCnf => "gbd-cnf",
            UriListFormat::RawJson => "raw-json",
        }
    }
}

impl Source {
    fn is_default(&self) -> bool {
        *self == Source::Release
    }

    fn label(&self) -> &'static str {
        match self {
            Source::Release => "release",
            Source::Http => "http",
            Source::Git => "git",
            Source::Gbd => "gbd",
            Source::UriList => "uri-list",
        }
    }
}

/// Base URL of the Global Benchmark Database file endpoint. Each row's
/// content is fetched from `<GBD_FILE_BASE>/<hash>`.
const GBD_FILE_BASE: &str = "https://benchmark-database.de/file";

// --- `ay corpus fixtures`: refresh the vendored CHC `*_000.smt2` fixtures. ---

/// Upstream repo holding the CHC-COMP 2025 `extra-small-lia` benchmarks.
const CHC_FIXTURE_REPO: &str = "chc-comp/chc-comp25-benchmarks";
/// Subdirectory within that repo holding the fixture sources.
const CHC_FIXTURE_SUBDIR: &str = "extra-small-lia";
/// Repo-relative directory holding the vendored `*_000.smt2` fixtures.
const CHC_FIXTURE_DEST: &str = "benchmarks/chc-comp/2025/extra-small-lia";
/// Pinned commit of `CHC_FIXTURE_REPO` the fixtures are fetched from. Pinning
/// to a commit (rather than the default branch, as the old shell script did)
/// makes refreshes reproducible.
const CHC_FIXTURE_COMMIT: &str = "ddd279cab0717db6effe69baad451a8eb04ffd86";

/// Fixtures that are AY-specific and have no upstream counterpart. They are
/// never fetched and their vendored copies are never overwritten or deleted.
const CHC_AY_SPECIFIC_FIXTURES: &[&str] =
    &["accumulator_unsafe_000.smt2", "two_phase_unsafe_000.smt2"];

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "lowercase")]
enum Archive {
    #[default]
    Tar,
    Zip,
    None,
}

impl Archive {
    fn is_default(&self) -> bool {
        *self == Archive::Tar
    }

    fn label(&self) -> &'static str {
        match self {
            Archive::Tar => "tar",
            Archive::Zip => "zip",
            Archive::None => "none",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExtractionLayout {
    /// The archive already contains the directory named by `extract_to`.
    ArchiveRootInParent,
    /// Every archive root belongs inside the directory at `extract_to`.
    WrappedDirectory,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ArchiveSymlinkPolicy {
    RejectAbsolute,
    NormalizeUniqueInArchive,
}

fn is_false(value: &bool) -> bool {
    !*value
}

fn is_canonical_sha256(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

fn validate_manifest_relative_path(value: &str, label: &str) -> Result<()> {
    let path = Path::new(value);
    let bytes = value.as_bytes();
    if value.is_empty()
        || value != value.trim()
        || path.is_absolute()
        || value.contains('\\')
        || value.chars().any(char::is_control)
        || (bytes.len() >= 2 && bytes[0].is_ascii_alphabetic() && bytes[1] == b':')
    {
        bail!("{label} is not a normalized repository-relative path: {value:?}");
    }
    let components = value.split('/').collect::<Vec<_>>();
    if components
        .iter()
        .any(|component| component.is_empty() || matches!(*component, "." | ".."))
        || path
            .components()
            .any(|component| !matches!(component, Component::Normal(_)))
    {
        bail!("{label} is not a normalized repository-relative path: {value:?}");
    }
    Ok(())
}

/// Resolve a repository-relative manifest from either the caller's directory
/// tree or the running binary's checkout. This keeps the documented
/// `target/release/ay corpus ...` workflow usable from outside the repository
/// without changing how explicit absolute paths behave.
fn resolve_repo_file(path: &Path) -> PathBuf {
    if path.is_absolute() || path.exists() {
        return path.to_path_buf();
    }
    let mut starts = Vec::new();
    if let Ok(cwd) = std::env::current_dir() {
        starts.push(cwd);
    }
    if let Ok(executable) = std::env::current_exe() {
        if let Some(parent) = executable.parent() {
            starts.push(parent.to_path_buf());
        }
    }
    for start in starts {
        for ancestor in start.ancestors() {
            let candidate = ancestor.join(path);
            if candidate.exists() {
                return candidate;
            }
        }
    }
    path.to_path_buf()
}

impl Manifest {
    fn load(path: &Path) -> Result<Self> {
        let resolved_path = resolve_repo_file(path);
        let body = fs::read_to_string(&resolved_path)
            .with_context(|| format!("read manifest {}", resolved_path.display()))?;
        let mut manifest: Manifest = toml::from_str(&body)
            .with_context(|| format!("parse manifest {}", resolved_path.display()))?;
        if manifest.schema_version < 1 || manifest.schema_version > 2 {
            bail!(
                "manifest {}: unsupported schema_version {} (expected 1 or 2)",
                resolved_path.display(),
                manifest.schema_version
            );
        }
        let absolute = if resolved_path.is_absolute() {
            resolved_path.clone()
        } else {
            std::env::current_dir()
                .context("resolve current directory")?
                .join(&resolved_path)
        };
        let parent = absolute.parent().ok_or_else(|| {
            anyhow!(
                "manifest {} has no parent directory",
                resolved_path.display()
            )
        })?;
        let base_dir = if parent.file_name().is_some_and(|name| name == "benchmarks") {
            parent.parent().unwrap_or(parent)
        } else {
            parent
        }
        .to_path_buf();
        for corpus in &mut manifest.corpora {
            corpus.base_dir = base_dir.clone();
        }
        let mut seen = BTreeSet::new();
        for c in &manifest.corpora {
            if !seen.insert(c.name.clone()) {
                bail!(
                    "manifest {}: duplicate corpus name {}",
                    resolved_path.display(),
                    c.name
                );
            }
            c.validate()
                .with_context(|| format!("corpus {} in {}", c.name, resolved_path.display()))?;
        }
        let all = manifest.corpora.iter().collect::<Vec<_>>();
        manifest
            .dependency_order(&all)
            .with_context(|| format!("validate dependencies in {}", resolved_path.display()))?;
        Ok(manifest)
    }

    fn save(&self, path: &Path) -> Result<()> {
        let body = toml::to_string_pretty(self).context("serialize manifest")?;
        fs::write(path, body).with_context(|| format!("write manifest {}", path.display()))?;
        Ok(())
    }

    fn find(&self, name: &str) -> Result<&Corpus> {
        self.corpora
            .iter()
            .find(|c| c.name == name)
            .ok_or_else(|| anyhow!("corpus {name} not found in manifest"))
    }

    fn find_mut(&mut self, name: &str) -> Result<&mut Corpus> {
        self.corpora
            .iter_mut()
            .find(|c| c.name == name)
            .ok_or_else(|| anyhow!("corpus {name} not found in manifest"))
    }

    fn select<'a>(
        &'a self,
        names: &[String],
        all: bool,
        groups: &[String],
    ) -> Result<Vec<&'a Corpus>> {
        if all {
            if !names.is_empty() || !groups.is_empty() {
                bail!("--all is mutually exclusive with --group and explicit corpus names");
            }
            return Ok(self.corpora.iter().collect());
        }
        if !groups.is_empty() {
            if !names.is_empty() {
                bail!("--group is mutually exclusive with explicit corpus names");
            }
            let requested = groups.iter().map(String::as_str).collect::<BTreeSet<_>>();
            let unknown = requested
                .iter()
                .filter(|group| {
                    !self
                        .corpora
                        .iter()
                        .any(|corpus| corpus.groups.iter().any(|value| value.as_str() == **group))
                })
                .map(|group| (*group).to_string())
                .collect::<Vec<_>>();
            if !unknown.is_empty() {
                bail!("unknown corpus group(s): {}", unknown.join(", "));
            }
            return Ok(self
                .corpora
                .iter()
                .filter(|corpus| {
                    corpus
                        .groups
                        .iter()
                        .any(|group| requested.contains(group.as_str()))
                })
                .collect());
        }
        if names.is_empty() {
            bail!("specify at least one corpus name, pass --group, or pass --all");
        }
        names.iter().map(|n| self.find(n)).collect()
    }

    fn dependency_order<'a>(&'a self, targets: &[&'a Corpus]) -> Result<Vec<&'a Corpus>> {
        fn visit<'a>(
            manifest: &'a Manifest,
            corpus: &'a Corpus,
            visiting: &mut BTreeSet<String>,
            visited: &mut BTreeSet<String>,
            ordered: &mut Vec<&'a Corpus>,
        ) -> Result<()> {
            if visited.contains(&corpus.name) {
                return Ok(());
            }
            if !visiting.insert(corpus.name.clone()) {
                bail!("corpus dependency cycle includes {}", corpus.name);
            }
            let mut unique = BTreeSet::new();
            for dependency in &corpus.depends_on {
                if dependency == &corpus.name {
                    bail!("corpus {} depends on itself", corpus.name);
                }
                if !unique.insert(dependency) {
                    bail!("corpus {} repeats dependency {}", corpus.name, dependency);
                }
                let dependency_corpus = manifest
                    .find(dependency)
                    .with_context(|| format!("corpus {} depends on {}", corpus.name, dependency))?;
                visit(manifest, dependency_corpus, visiting, visited, ordered)?;
            }
            visiting.remove(&corpus.name);
            visited.insert(corpus.name.clone());
            ordered.push(corpus);
            Ok(())
        }

        let mut visiting = BTreeSet::new();
        let mut visited = BTreeSet::new();
        let mut ordered = Vec::new();
        for corpus in targets {
            visit(self, corpus, &mut visiting, &mut visited, &mut ordered)?;
        }
        Ok(ordered)
    }
}

impl Corpus {
    fn resolve_path(&self, path: &str) -> PathBuf {
        let path = Path::new(path);
        if path.is_absolute() || self.base_dir.as_os_str().is_empty() {
            path.to_path_buf()
        } else {
            self.base_dir.join(path)
        }
    }

    fn extract_path(&self) -> PathBuf {
        self.resolve_path(&self.extract_to)
    }

    fn extraction_layout(&self) -> ExtractionLayout {
        if self.wrap_archive {
            ExtractionLayout::WrappedDirectory
        } else {
            ExtractionLayout::ArchiveRootInParent
        }
    }

    fn archive_symlink_policy(&self) -> ArchiveSymlinkPolicy {
        if self.normalize_absolute_archive_symlinks {
            ArchiveSymlinkPolicy::NormalizeUniqueInArchive
        } else {
            ArchiveSymlinkPolicy::RejectAbsolute
        }
    }

    fn validate(&self) -> Result<()> {
        if self.requires_git_lfs && self.source != Source::Git {
            bail!("`requires_git_lfs` is only valid for source=git");
        }
        if !self.allowed_unmapped_gitlinks.is_empty() && self.source != Source::Git {
            bail!("`allowed_unmapped_gitlinks` is only valid for source=git");
        }
        let mut allowed_unmapped_gitlinks = BTreeSet::new();
        for path in &self.allowed_unmapped_gitlinks {
            let relative = Path::new(path);
            if relative.as_os_str().is_empty()
                || relative.is_absolute()
                || relative
                    .components()
                    .any(|component| !matches!(component, Component::Normal(_)))
            {
                bail!("unsafe allowed unmapped gitlink path {path:?}");
            }
            if !allowed_unmapped_gitlinks.insert(path) {
                bail!("duplicate allowed unmapped gitlink path {path:?}");
            }
        }
        let mut groups = BTreeSet::new();
        for group in &self.groups {
            let valid = !group.is_empty()
                && !group.starts_with('-')
                && !group.ends_with('-')
                && group
                    .chars()
                    .all(|ch| ch.is_ascii_lowercase() || ch.is_ascii_digit() || ch == '-');
            if !valid {
                bail!("group must be non-empty kebab-case [a-z0-9-]: {group:?}");
            }
            if !groups.insert(group) {
                bail!("duplicate group {group:?}");
            }
        }
        match self.source {
            Source::Release => {
                if !self.uri_list_format.is_default() {
                    bail!("source=release does not use `uri_list_format`");
                }
                if self.asset.is_none() {
                    bail!("source=release requires `asset`");
                }
                if self.sha256.is_none() {
                    bail!("source=release requires `sha256`");
                }
            }
            Source::Http => {
                if !self.uri_list_format.is_default() {
                    bail!("source=http does not use `uri_list_format`");
                }
                if self.url.is_none() {
                    bail!("source=http requires `url`");
                }
                if let Some(cache_name) = &self.cache_name {
                    let path = Path::new(cache_name);
                    if path.components().count() != 1
                        || cache_name.is_empty()
                        || cache_name == "."
                        || cache_name == ".."
                    {
                        bail!("`cache_name` must be one non-empty filename component");
                    }
                }
            }
            Source::Git => {
                if !self.uri_list_format.is_default() {
                    bail!("source=git does not use `uri_list_format`");
                }
                if self.url.is_none() {
                    bail!("source=git requires `url`");
                }
                if self.cache_name.is_some() {
                    bail!("source=git does not use `cache_name`");
                }
                if self.archive != Archive::Tar {
                    bail!("source=git does not use `archive`");
                }
            }
            Source::Gbd => {
                if !self.uri_list_format.is_default() {
                    bail!("source=gbd does not use `uri_list_format`");
                }
                if self.manifest.is_none() {
                    bail!("source=gbd requires `manifest` (CSV with hash,local_path columns)");
                }
                if self.cache_name.is_some() {
                    bail!("source=gbd does not use `cache_name`");
                }
                if self.archive != Archive::Tar {
                    bail!("source=gbd does not use `archive`");
                }
            }
            Source::UriList => {
                if self.manifest.is_none() {
                    bail!("source=uri-list requires `manifest` (one HTTPS URL per line)");
                }
                if self.url.is_some()
                    || self.asset.is_some()
                    || self.cache_name.is_some()
                    || self.sha256.is_some()
                    || self.size_bytes.is_some()
                {
                    bail!(
                        "source=uri-list stores pins on its separate manifest asset, not on the fetched set"
                    );
                }
                if self.archive != Archive::Tar {
                    bail!("source=uri-list does not use `archive`");
                }
            }
        }
        if self.wrap_archive {
            match (self.source, self.archive) {
                (Source::Http, Archive::Tar | Archive::Zip) => {}
                (Source::Release | Source::Http, Archive::None) => {
                    bail!("`wrap_archive` requires an extracted archive, not archive=\"none\"");
                }
                (Source::Release, _) => {
                    bail!(
                        "`wrap_archive` is not valid for source=release because release upload \
                         archives already contain the `extract_to` root"
                    );
                }
                (Source::Git | Source::Gbd | Source::UriList, _) => {
                    bail!("`wrap_archive` is only valid for HTTP archive sources");
                }
            }
        }
        if self.normalize_absolute_archive_symlinks {
            match (self.source, self.archive) {
                (Source::Release | Source::Http, Archive::Tar | Archive::Zip) => {}
                _ => {
                    bail!(
                        "`normalize_absolute_archive_symlinks` requires an extracted HTTP or release archive"
                    );
                }
            }
        }
        Ok(())
    }

    /// Path to the cached archive (release, http) or `None` for sources
    /// that produce a directory directly (git). For `archive = "none"`
    /// the cache path is the same as `extract_to` — the file IS the result.
    fn cache_path(&self) -> Option<PathBuf> {
        match (self.source, self.archive) {
            (Source::Release, _) => {
                let extract = self.extract_path();
                let parent = extract.parent().unwrap_or_else(|| Path::new("."));
                Some(parent.join(self.asset.as_ref()?))
            }
            (Source::Http, Archive::None) => Some(self.extract_path()),
            (Source::Http, _) => {
                let extract = self.extract_path();
                let parent = extract.parent().unwrap_or_else(|| Path::new("."));
                let basename = match self.cache_name.as_deref() {
                    Some(value) => value,
                    None => self
                        .url
                        .as_deref()?
                        .rsplit('/')
                        .next()
                        .filter(|s| !s.is_empty())?,
                };
                Some(parent.join(basename))
            }
            // git clones a directory; gbd writes per-row files: neither has a
            // single cached archive.
            (Source::Git, _) | (Source::Gbd, _) | (Source::UriList, _) => None,
        }
    }

    fn local_status(&self) -> String {
        // gbd: report how many of the manifest's local_paths are present.
        if self.source == Source::Gbd {
            return match self.gbd_rows() {
                Ok(rows) if rows.is_empty() => "empty-manifest".to_string(),
                Ok(rows) => {
                    let present = rows.iter().filter(|r| r.is_present()).count();
                    let total = rows.len();
                    if present == total {
                        format!("downloaded ({present}/{total})")
                    } else if present == 0 {
                        format!("missing (0/{total})")
                    } else {
                        format!("partial ({present}/{total})")
                    }
                }
                Err(_) => "no-manifest".to_string(),
            };
        }
        if self.source == Source::UriList {
            return match self.uri_rows() {
                Ok(rows) => {
                    let present = rows.iter().filter(|row| row.is_present(self)).count();
                    let total = rows.len();
                    if present == total {
                        format!("downloaded ({present}/{total})")
                    } else if present == 0 {
                        format!("missing (0/{total})")
                    } else {
                        format!("partial ({present}/{total})")
                    }
                }
                Err(_) => "no-manifest".to_string(),
            };
        }
        if self.source == Source::Git {
            let extract = self.extract_path();
            if !extract.exists() {
                return "missing".to_string();
            }
            return match verify_git_checkout(self) {
                Ok(()) if self.commit.is_some() => "cloned (pin verified)".to_string(),
                Ok(()) => "cloned (unpinned)".to_string(),
                Err(_) => "stale".to_string(),
            };
        }
        let cache = self.cache_path();
        let cache_status = cache.as_deref().map(|path| {
            if path_is_present(path).unwrap_or(false) {
                match validate_file_pins(path, self.sha256.as_deref(), self.size_bytes) {
                    Ok(()) => CacheStatus::Valid,
                    Err(_) => CacheStatus::Stale,
                }
            } else {
                CacheStatus::Missing
            }
        });

        // Archive::None: the file at cache_path IS the result.
        if self.archive == Archive::None {
            return match cache_status {
                Some(CacheStatus::Valid) => "downloaded".to_string(),
                Some(CacheStatus::Stale) => "stale".to_string(),
                Some(CacheStatus::Missing) | None => "missing".to_string(),
            };
        }
        let extract = self.extract_path();
        if path_is_present(&extract).unwrap_or(false) {
            return match cache_status {
                Some(CacheStatus::Stale) => "stale".to_string(),
                Some(CacheStatus::Missing)
                    if self.sha256.is_some() || self.size_bytes.is_some() =>
                {
                    "unverified".to_string()
                }
                Some(CacheStatus::Valid) | Some(CacheStatus::Missing) | None => {
                    "extracted".to_string()
                }
            };
        }
        match cache_status {
            Some(CacheStatus::Valid) => "downloaded".to_string(),
            Some(CacheStatus::Stale) => "stale".to_string(),
            Some(CacheStatus::Missing) | None => "missing".to_string(),
        }
    }

    fn cache_is_valid(&self, cache: &Path) -> bool {
        if !path_is_present(cache).unwrap_or(false) {
            return false;
        }
        if self.sha256.is_none() && self.size_bytes.is_none() {
            return true;
        }
        validate_file_pins(cache, self.sha256.as_deref(), self.size_bytes).is_ok()
    }

    fn has_file_pins(&self) -> bool {
        self.sha256.is_some() || self.size_bytes.is_some()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CacheStatus {
    Missing,
    Valid,
    Stale,
}

impl Corpus {
    /// Parse the gbd CSV manifest into rows. Errors if the entry has no
    /// `manifest` field or the file cannot be read/parsed.
    fn gbd_rows(&self) -> Result<Vec<GbdRow>> {
        let manifest = self
            .manifest
            .as_deref()
            .ok_or_else(|| anyhow!("source=gbd requires `manifest`"))?;
        let mut rows = parse_gbd_manifest(&self.resolve_path(manifest))?;
        let destination = self.extract_path();
        let mut owned_paths = BTreeSet::new();
        for row in &mut rows {
            let resolved = self.resolve_path(&row.local_path);
            if resolved == destination || !resolved.starts_with(&destination) {
                bail!(
                    "GBD local_path {:?} escapes corpus destination {}",
                    row.local_path,
                    destination.display()
                );
            }
            row.local_path = resolved.to_string_lossy().to_string();
            let raw = row.raw_path();
            validate_existing_gbd_path(&destination, &raw)?;
            if !owned_paths.insert(raw.clone()) {
                bail!(
                    "GBD manifest repeats local benchmark path {}",
                    raw.display()
                );
            }
            let materialized = row.decompressed_path();
            if materialized == destination || !materialized.starts_with(&destination) {
                bail!(
                    "GBD decompressed sibling {} escapes corpus destination {}",
                    materialized.display(),
                    destination.display()
                );
            }
            if materialized != raw {
                validate_existing_gbd_path(&destination, &materialized)?;
                if !owned_paths.insert(materialized.clone()) {
                    bail!(
                        "GBD manifest materialized path {} collides with another row",
                        materialized.display()
                    );
                }
            }
        }
        Ok(rows)
    }

    fn uri_rows(&self) -> Result<Vec<UriRow>> {
        let manifest = self
            .manifest
            .as_deref()
            .ok_or_else(|| anyhow!("source=uri-list requires `manifest`"))?;
        parse_uri_list(&self.resolve_path(manifest), self.uri_list_format)
    }
}

fn validate_existing_gbd_path(destination: &Path, artifact: &Path) -> Result<()> {
    let parent = artifact
        .parent()
        .ok_or_else(|| anyhow!("GBD artifact {} has no parent", artifact.display()))?;
    let relative_parent = parent.strip_prefix(destination).with_context(|| {
        format!(
            "GBD artifact {} escapes corpus destination {}",
            artifact.display(),
            destination.display()
        )
    })?;
    let mut current = destination.to_path_buf();
    for component in std::iter::once(None).chain(
        relative_parent
            .components()
            .map(|component| Some(component.as_os_str())),
    ) {
        if let Some(component) = component {
            current.push(component);
        }
        let metadata = match fs::symlink_metadata(&current) {
            Ok(metadata) => metadata,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
            Err(error) => {
                return Err(error)
                    .with_context(|| format!("inspect GBD path ancestor {}", current.display()));
            }
        };
        if metadata.file_type().is_symlink() || !metadata.file_type().is_dir() {
            bail!(
                "GBD path ancestor {} must be a real directory, never a symlink",
                current.display()
            );
        }
    }

    match fs::symlink_metadata(artifact) {
        Ok(metadata) if metadata.file_type().is_symlink() || !metadata.file_type().is_file() => {
            bail!(
                "existing GBD artifact {} must be a regular non-symlink file",
                artifact.display()
            );
        }
        Ok(_) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => {
            Err(error).with_context(|| format!("inspect GBD artifact {}", artifact.display()))
        }
    }
}

/// One row of a gbd manifest CSV: a content `hash` and the repo-relative
/// `local_path` of the downloaded (xz) artifact.
#[derive(Debug, Clone)]
struct GbdRow {
    hash: String,
    local_path: String,
    expected_size: Option<u64>,
    expected_sha256: Option<String>,
}

#[derive(Debug, Clone)]
struct UriRow {
    url: String,
    id: String,
    expected_size: Option<u64>,
    expected_sha256: Option<String>,
}

impl UriRow {
    fn downloaded_path(&self, corpus: &Corpus) -> PathBuf {
        let extension = match corpus.uri_list_format {
            UriListFormat::GbdCnf => "cnf.xz",
            UriListFormat::RawJson => "json",
        };
        corpus
            .extract_path()
            .join(format!("{}.{}", self.id, extension))
    }

    fn materialized_path(&self, corpus: &Corpus) -> Option<PathBuf> {
        match corpus.uri_list_format {
            UriListFormat::GbdCnf => Some(corpus.extract_path().join(format!("{}.cnf", self.id))),
            UriListFormat::RawJson => None,
        }
    }

    fn is_present(&self, corpus: &Corpus) -> bool {
        self.downloaded_path(corpus).exists()
            || self
                .materialized_path(corpus)
                .is_some_and(|path| path.exists())
    }

    fn verify(&self, corpus: &Corpus) -> Result<()> {
        let downloaded = self.downloaded_path(corpus);
        if downloaded.exists() {
            return validate_file_pins(
                &downloaded,
                self.expected_sha256.as_deref(),
                self.expected_size,
            );
        }
        if self
            .materialized_path(corpus)
            .is_some_and(|path| path.exists())
            && self.expected_sha256.is_none()
            && self.expected_size.is_none()
        {
            return Ok(());
        }
        bail!("missing {}", downloaded.display())
    }

    fn owned_paths(&self, corpus: &Corpus) -> Vec<PathBuf> {
        let mut paths = vec![self.downloaded_path(corpus)];
        if let Some(path) = self.materialized_path(corpus) {
            paths.push(path);
        }
        paths
    }
}

impl GbdRow {
    /// The raw downloaded artifact path (typically `…cnf.xz`).
    fn raw_path(&self) -> PathBuf {
        PathBuf::from(&self.local_path)
    }

    /// The decompressed sibling, i.e. `local_path` with a trailing `.xz`
    /// stripped. Tests read this `.cnf`; if `local_path` has no `.xz` suffix
    /// it is the same as `raw_path`.
    fn decompressed_path(&self) -> PathBuf {
        match self.local_path.strip_suffix(".xz") {
            Some(stem) => PathBuf::from(stem),
            None => PathBuf::from(&self.local_path),
        }
    }

    fn has_complete_pins(&self) -> bool {
        self.expected_size.is_some_and(|size| size > 0)
            && self
                .expected_sha256
                .as_deref()
                .is_some_and(is_canonical_sha256)
    }

    /// A pinned row is present only when its exact raw response verifies.
    /// Legacy unpinned manifests may still be satisfied by a decompressed
    /// sibling because several small test corpora predate response pinning.
    fn is_present(&self) -> bool {
        self.verify().is_ok()
    }

    fn verify(&self) -> Result<()> {
        let raw = self.raw_path();
        if self.expected_size.is_some() || self.expected_sha256.is_some() {
            if !raw.exists() {
                bail!("missing pinned GBD response {}", raw.display());
            }
            return validate_file_pins(&raw, self.expected_sha256.as_deref(), self.expected_size);
        }
        if raw.exists() || self.decompressed_path().exists() {
            return Ok(());
        }
        bail!("missing GBD row {}", raw.display())
    }
}

/// Parse a GBD manifest CSV. `hash` and `local_path` are mandatory;
/// `size_bytes` and `sha256` provide exact response pins when present.
/// Remaining columns are provenance and are ignored here. Fields may be
/// double-quoted (for example, a `category` column can embed commas).
fn parse_gbd_manifest(path: &Path) -> Result<Vec<GbdRow>> {
    let body = fs::read_to_string(path)
        .with_context(|| format!("read gbd manifest {}", path.display()))?;
    let mut lines = body.lines();
    let header = lines
        .next()
        .ok_or_else(|| anyhow!("gbd manifest {} is empty", path.display()))?;
    let cols = split_csv_line(header);
    let hash_idx = cols
        .iter()
        .position(|c| c == "hash")
        .ok_or_else(|| anyhow!("gbd manifest {} has no `hash` column", path.display()))?;
    let path_idx = cols
        .iter()
        .position(|c| c == "local_path")
        .ok_or_else(|| anyhow!("gbd manifest {} has no `local_path` column", path.display()))?;
    let size_idx = cols.iter().position(|c| c == "size_bytes");
    let sha256_idx = cols.iter().position(|c| c == "sha256");
    let mut rows = Vec::new();
    for (row_index, line) in lines.enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let fields = split_csv_line(line);
        let hash = fields
            .get(hash_idx)
            .cloned()
            .ok_or_else(|| anyhow!("gbd manifest {}: row missing hash", path.display()))?;
        let local_path = fields
            .get(path_idx)
            .cloned()
            .ok_or_else(|| anyhow!("gbd manifest {}: row missing local_path", path.display()))?;
        if hash.is_empty() {
            bail!(
                "gbd manifest {} row {} has an empty hash",
                path.display(),
                row_index + 2
            );
        }
        validate_manifest_relative_path(
            &local_path,
            &format!(
                "gbd manifest {} row {} local_path",
                path.display(),
                row_index + 2
            ),
        )?;
        let expected_size = size_idx
            .and_then(|index| fields.get(index))
            .filter(|value| !value.is_empty())
            .map(|value| {
                value.parse::<u64>().with_context(|| {
                    format!(
                        "gbd manifest {} row {} has invalid size_bytes",
                        path.display(),
                        row_index + 2
                    )
                })
            })
            .transpose()?;
        let expected_sha256 = sha256_idx
            .and_then(|index| fields.get(index))
            .filter(|value| !value.is_empty())
            .cloned();
        match (expected_size, expected_sha256.as_deref()) {
            (None, None) => {}
            (Some(size), Some(sha256)) if size > 0 && is_canonical_sha256(sha256) => {}
            _ => {
                bail!(
                    "gbd manifest {} row {} pins must include a positive size_bytes and canonical lowercase SHA-256",
                    path.display(),
                    row_index + 2
                );
            }
        }
        rows.push(GbdRow {
            hash,
            local_path,
            expected_size,
            expected_sha256,
        });
    }
    Ok(rows)
}

fn parse_uri_list(path: &Path, format: UriListFormat) -> Result<Vec<UriRow>> {
    let body =
        fs::read_to_string(path).with_context(|| format!("read URI list {}", path.display()))?;
    let mut seen = BTreeSet::new();
    let mut rows = Vec::new();
    for (index, line) in body.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let fields = line.split('\t').collect::<Vec<_>>();
        if fields.len() != 1 && fields.len() != 3 {
            bail!(
                "URI list {} line {} must contain URL or URL<TAB>bytes<TAB>SHA-256",
                path.display(),
                index + 1
            );
        }
        let url = fields[0];
        if !url.starts_with("https://") {
            bail!(
                "URI list {} line {} is not HTTPS: {url:?}",
                path.display(),
                index + 1
            );
        }
        let path_segments = url
            .split(['?', '#'])
            .next()
            .unwrap_or(url)
            .split('/')
            .filter(|value| !value.is_empty())
            .collect::<Vec<_>>();
        let id = match format {
            UriListFormat::GbdCnf => path_segments
                .last()
                .copied()
                .unwrap_or_default()
                .to_string(),
            UriListFormat::RawJson => path_segments
                .iter()
                .rev()
                .take(2)
                .rev()
                .copied()
                .collect::<Vec<_>>()
                .join("-"),
        };
        if id.is_empty()
            || !id
                .chars()
                .all(|ch| ch.is_ascii_alphanumeric() || ch == '-' || ch == '_')
        {
            return Err(anyhow!(
                "URI list {} line {} has no safe artifact id",
                path.display(),
                index + 1
            ));
        }
        let (expected_size, expected_sha256) = if fields.len() == 3 {
            let size = fields[1].parse::<u64>().map_err(|error| {
                anyhow!(
                    "URI list {} line {} has invalid byte size: {error}",
                    path.display(),
                    index + 1
                )
            })?;
            let sha256 = fields[2];
            if size == 0 || !is_canonical_sha256(sha256) {
                bail!(
                    "URI list {} line {} pins must include a positive byte size and canonical lowercase SHA-256",
                    path.display(),
                    index + 1
                );
            }
            (Some(size), Some(sha256.to_string()))
        } else {
            (None, None)
        };
        if !seen.insert(id.clone()) {
            bail!("URI list {} repeats artifact id {id:?}", path.display());
        }
        rows.push(UriRow {
            url: url.to_string(),
            id,
            expected_size,
            expected_sha256,
        });
    }
    if rows.is_empty() {
        bail!("URI list {} has no artifact URLs", path.display());
    }
    Ok(rows)
}

/// Minimal RFC4180-ish CSV line splitter: handles double-quoted fields with
/// embedded commas and `""` escapes. Sufficient for the gbd manifests we own.
fn split_csv_line(line: &str) -> Vec<String> {
    let mut fields = Vec::new();
    let mut cur = String::new();
    let mut in_quotes = false;
    let mut chars = line.chars().peekable();
    while let Some(ch) = chars.next() {
        if in_quotes {
            if ch == '"' {
                if chars.peek() == Some(&'"') {
                    cur.push('"');
                    chars.next();
                } else {
                    in_quotes = false;
                }
            } else {
                cur.push(ch);
            }
        } else if ch == '"' {
            in_quotes = true;
        } else if ch == ',' {
            fields.push(std::mem::take(&mut cur));
        } else {
            cur.push(ch);
        }
    }
    fields.push(cur);
    fields
}

pub(crate) fn run(cmd: CorpusCommand) -> Result<i32> {
    match cmd {
        CorpusCommand::List(args) => run_list(args),
        CorpusCommand::Plan(args) => run_plan(args),
        CorpusCommand::Download(args) => run_download(args),
        CorpusCommand::Verify(args) => run_verify(args),
        CorpusCommand::CampaignAudit(args) => run_campaign_audit(args),
        CorpusCommand::Upload(args) => run_upload(args),
        CorpusCommand::Prune(args) => run_prune(args),
        CorpusCommand::CheckUrls(args) => run_check_urls(args),
        CorpusCommand::Fixtures(args) => run_fixtures(args),
        CorpusCommand::InstallTool(args) => run_install_tool(args),
    }
}

fn run_plan(args: PlanArgs) -> Result<i32> {
    let manifest_path = resolve_repo_file(&args.manifest.manifest);
    let manifest = Manifest::load(&manifest_path)?;
    let selected = manifest.select(&args.names, args.all, &args.groups)?;
    let targets = manifest.dependency_order(&selected)?;
    let filesystem_path = targets
        .first()
        .map(|corpus| corpus.base_dir.clone())
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or_else(|| {
            manifest_path
                .parent()
                .unwrap_or_else(|| Path::new("."))
                .to_path_buf()
        });
    let plan = build_corpus_plan(&manifest, &selected, &targets, &filesystem_path)?;
    if args.json {
        serde_json::to_writer_pretty(std::io::stdout().lock(), &plan)
            .context("serialize corpus acquisition plan")?;
        println!();
    } else {
        print_corpus_plan(&plan);
    }
    Ok(0)
}

fn build_corpus_plan(
    manifest: &Manifest,
    selected: &[&Corpus],
    targets: &[&Corpus],
    filesystem_path: &Path,
) -> Result<CorpusPlanSummary> {
    let selected_names = selected
        .iter()
        .map(|corpus| corpus.name.as_str())
        .collect::<BTreeSet<_>>();
    let mut installed_assets = 0usize;
    let mut missing_or_stale_assets = 0usize;
    let mut network_fetch_assets = 0usize;
    let mut known_transfer_bytes = 0u64;
    let mut known_remaining_transfer_bytes = 0u64;
    let mut unknown_size_sources = BTreeMap::new();
    let mut unknown_remaining_size_sources = BTreeMap::new();
    let mut assets = Vec::with_capacity(targets.len());

    for corpus in targets {
        let (installed, network_fetch_required) = corpus_plan_local_state(corpus)
            .with_context(|| format!("inspect local corpus {}", corpus.name))?;
        let transfer = corpus_transfer_estimate(corpus)
            .with_context(|| format!("estimate transfer for {}", corpus.name))?;
        let remaining = corpus_remaining_transfer_estimate(corpus, network_fetch_required)
            .with_context(|| format!("estimate remaining transfer for {}", corpus.name))?;
        checked_add_bytes(
            &mut known_transfer_bytes,
            transfer.known_bytes,
            "known transfer total",
        )?;
        checked_add_bytes(
            &mut known_remaining_transfer_bytes,
            remaining.known_bytes,
            "known remaining transfer total",
        )?;

        if installed {
            installed_assets += 1;
        } else {
            missing_or_stale_assets += 1;
        }
        if network_fetch_required {
            network_fetch_assets += 1;
        }
        if transfer.has_unknown {
            *unknown_size_sources
                .entry(corpus.source.label().to_string())
                .or_insert(0) += 1;
        }
        if remaining.has_unknown {
            *unknown_remaining_size_sources
                .entry(corpus.source.label().to_string())
                .or_insert(0) += 1;
        }
        let (local_layout, acquisition, pins, source_manifest) =
            corpus_plan_provenance(manifest, corpus)
                .with_context(|| format!("describe acquisition provenance for {}", corpus.name))?;

        assets.push(CorpusPlanAsset {
            name: corpus.name.clone(),
            source: corpus.source.label().to_string(),
            groups: corpus.groups.clone(),
            dependencies: corpus.depends_on.clone(),
            selected: selected_names.contains(corpus.name.as_str()),
            installed,
            network_fetch_required,
            known_transfer_bytes: transfer.known_bytes,
            transfer_size_complete: !transfer.has_unknown,
            known_remaining_transfer_bytes: remaining.known_bytes,
            remaining_transfer_size_complete: !remaining.has_unknown,
            local_layout,
            acquisition,
            pins,
            manifest: source_manifest,
        });
    }

    let required_tools = corpus_plan_tool_requirements(targets);
    let missing_tool_requirements = required_tools
        .iter()
        .filter(|requirement| !requirement.satisfied)
        .count();
    let available_filesystem_bytes = available_filesystem_bytes(filesystem_path)?;
    let capacity_warning = available_filesystem_bytes
        .filter(|available| known_remaining_transfer_bytes > *available)
        .map(|available| {
            format!(
                "known remaining transfer {} exceeds the {} available on the planned \
                 filesystem; this lower bound excludes unknown-size downloads, extraction, \
                 decompression, and staging",
                human_bytes(known_remaining_transfer_bytes),
                human_bytes(available),
            )
        });

    Ok(CorpusPlanSummary {
        schema_version: 2,
        selected_assets: selected_names.len(),
        dependency_assets: targets.len().saturating_sub(selected_names.len()),
        closure_assets: targets.len(),
        installed_assets,
        missing_or_stale_assets,
        network_fetch_assets,
        known_transfer_bytes,
        known_remaining_transfer_bytes,
        unknown_size_sources,
        unknown_remaining_size_sources,
        required_tools,
        missing_tool_requirements,
        filesystem_path: filesystem_path.display().to_string(),
        available_filesystem_bytes,
        capacity_warning,
        capacity_note: CORPUS_PLAN_CAPACITY_NOTE.to_string(),
        assets,
    })
}

fn corpus_plan_provenance(
    manifest: &Manifest,
    corpus: &Corpus,
) -> Result<(
    CorpusPlanLocalLayout,
    CorpusPlanAcquisition,
    CorpusPlanPins,
    Option<CorpusPlanManifest>,
)> {
    let destination = CorpusPlanPath {
        declared: corpus.extract_to.clone(),
        resolved: corpus.extract_path().display().to_string(),
    };
    let cache = match (corpus_plan_declared_cache_path(corpus), corpus.cache_path()) {
        (Some(declared), Some(resolved)) => Some(CorpusPlanPath {
            declared: declared.display().to_string(),
            resolved: resolved.display().to_string(),
        }),
        (None, None) => None,
        _ => bail!("cache path declaration and resolution disagree"),
    };
    let (materialization_kind, archive_format, archive_layout) = match corpus.source {
        Source::Release | Source::Http if corpus.archive != Archive::None => {
            let layout = match corpus.extraction_layout() {
                ExtractionLayout::ArchiveRootInParent => "archive-root-in-parent",
                ExtractionLayout::WrappedDirectory => "wrapped-directory",
            };
            (
                "archive-extraction",
                Some(corpus.archive.label().to_string()),
                Some(layout.to_string()),
            )
        }
        Source::Release | Source::Http => (
            "direct-file",
            Some(corpus.archive.label().to_string()),
            None,
        ),
        Source::Git => ("git-checkout", None, None),
        Source::Gbd => ("gbd-row-files", None, None),
        Source::UriList => ("uri-list-row-files", None, None),
    };
    let archive_symlink_policy = archive_layout.as_ref().map(|_| {
        match corpus.archive_symlink_policy() {
            ArchiveSymlinkPolicy::RejectAbsolute => "reject-escaping-links",
            ArchiveSymlinkPolicy::NormalizeUniqueInArchive => {
                "normalize-unique-in-archive-absolute-targets"
            }
        }
        .to_string()
    });
    let local_layout = CorpusPlanLocalLayout {
        materialization: CorpusPlanMaterialization {
            kind: materialization_kind.to_string(),
            declared: destination.declared.clone(),
            resolved: destination.resolved.clone(),
            archive_format,
            archive_layout,
            archive_symlink_policy,
        },
        destination,
        cache,
    };

    let acquisition = match corpus.source {
        Source::Release => CorpusPlanAcquisition::Release {
            repository: manifest.repo.clone(),
            release_tag: manifest.release_tag.clone(),
            asset: corpus
                .asset
                .clone()
                .ok_or_else(|| anyhow!("release source has no asset"))?,
        },
        Source::Http => {
            let (url, url_redacted) = corpus_plan_public_url(
                corpus
                    .url
                    .as_deref()
                    .ok_or_else(|| anyhow!("HTTP source has no URL"))?,
            );
            CorpusPlanAcquisition::Http { url, url_redacted }
        }
        Source::Git => {
            let (url, url_redacted) = corpus_plan_public_url(
                corpus
                    .url
                    .as_deref()
                    .ok_or_else(|| anyhow!("Git source has no URL"))?,
            );
            CorpusPlanAcquisition::Git {
                url,
                url_redacted,
                depth: corpus.depth.unwrap_or(1),
                requires_git_lfs: corpus.requires_git_lfs,
                allowed_unmapped_gitlinks: corpus.allowed_unmapped_gitlinks.clone(),
            }
        }
        Source::Gbd => CorpusPlanAcquisition::Gbd {
            file_endpoint: format!("{GBD_FILE_BASE}/{{upstream_object_id}}"),
        },
        Source::UriList => CorpusPlanAcquisition::UriList,
    };
    let pins = CorpusPlanPins {
        sha256: corpus.sha256.clone(),
        size_bytes: corpus.size_bytes,
        git_commit: corpus.commit.clone(),
    };
    let source_manifest = corpus_plan_source_manifest(corpus)?;
    Ok((local_layout, acquisition, pins, source_manifest))
}

fn corpus_plan_declared_cache_path(corpus: &Corpus) -> Option<PathBuf> {
    let destination = Path::new(&corpus.extract_to);
    match (corpus.source, corpus.archive) {
        (Source::Release, _) => Some(
            destination
                .parent()
                .unwrap_or_else(|| Path::new("."))
                .join(corpus.asset.as_ref()?),
        ),
        (Source::Http, Archive::None) => Some(destination.to_path_buf()),
        (Source::Http, _) => {
            let basename = match corpus.cache_name.as_deref() {
                Some(value) => value,
                None => corpus
                    .url
                    .as_deref()?
                    .rsplit('/')
                    .next()
                    .filter(|value| !value.is_empty())?,
            };
            Some(
                destination
                    .parent()
                    .unwrap_or_else(|| Path::new("."))
                    .join(basename),
            )
        }
        (Source::Git | Source::Gbd | Source::UriList, _) => None,
    }
}

fn corpus_plan_source_manifest(corpus: &Corpus) -> Result<Option<CorpusPlanManifest>> {
    let Some(declared_manifest) = corpus.manifest.as_deref() else {
        return Ok(None);
    };
    let resolved_manifest = corpus.resolve_path(declared_manifest);
    let metadata = fs::metadata(&resolved_manifest)
        .with_context(|| format!("stat source manifest {}", resolved_manifest.display()))?;
    let path = CorpusPlanPath {
        declared: declared_manifest.to_string(),
        resolved: resolved_manifest.display().to_string(),
    };
    let sha256 = local_sha256(&resolved_manifest)
        .with_context(|| format!("hash source manifest {}", resolved_manifest.display()))?;

    let (kind, format, rows) = match corpus.source {
        Source::Gbd => {
            let rows = parse_gbd_manifest(&resolved_manifest)?
                .into_iter()
                .map(|row| {
                    let declared_download = PathBuf::from(&row.local_path);
                    let resolved_download = corpus.resolve_path(&row.local_path);
                    let materialized = if row.has_complete_pins() {
                        None
                    } else {
                        let declared_materialized = row
                            .local_path
                            .strip_suffix(".xz")
                            .map(PathBuf::from)
                            .unwrap_or_else(|| declared_download.clone());
                        let resolved_materialized = corpus.resolve_path(
                            declared_materialized
                                .to_str()
                                .ok_or_else(|| anyhow!("GBD materialized path is not UTF-8"))?,
                        );
                        Some(CorpusPlanPath {
                            declared: declared_materialized.display().to_string(),
                            resolved: resolved_materialized.display().to_string(),
                        })
                    };
                    let (url, url_redacted) =
                        corpus_plan_public_url(&format!("{GBD_FILE_BASE}/{}", row.hash));
                    Ok(CorpusPlanManifestRow::GbdObject {
                        upstream_object_id: row.hash,
                        url,
                        url_redacted,
                        size_bytes: row.expected_size,
                        sha256: row.expected_sha256,
                        download: CorpusPlanPath {
                            declared: declared_download.display().to_string(),
                            resolved: resolved_download.display().to_string(),
                        },
                        materialized,
                    })
                })
                .collect::<Result<Vec<_>>>()?;
            ("gbd-manifest", "csv-hash-local-path", rows)
        }
        Source::UriList => {
            let rows = parse_uri_list(&resolved_manifest, corpus.uri_list_format)?
                .into_iter()
                .map(|row| {
                    let (url, url_redacted) = corpus_plan_public_url(&row.url);
                    let downloaded = row.downloaded_path(corpus);
                    let declared_download = corpus_plan_uri_declared_download_path(corpus, &row);
                    CorpusPlanManifestRow::Uri {
                        id: row.id,
                        url,
                        url_redacted,
                        size_bytes: row.expected_size,
                        sha256: row.expected_sha256,
                        download: CorpusPlanPath {
                            declared: declared_download.display().to_string(),
                            resolved: downloaded.display().to_string(),
                        },
                    }
                })
                .collect();
            ("uri-list", corpus.uri_list_format.label(), rows)
        }
        Source::Release | Source::Http | Source::Git => {
            bail!(
                "{} source unexpectedly declares a row manifest",
                corpus.source.label()
            )
        }
    };
    Ok(Some(CorpusPlanManifest {
        kind: kind.to_string(),
        format: format.to_string(),
        path,
        sha256,
        size_bytes: metadata.len(),
        row_count: rows.len(),
        rows,
    }))
}

fn corpus_plan_uri_declared_download_path(corpus: &Corpus, row: &UriRow) -> PathBuf {
    let extension = match corpus.uri_list_format {
        UriListFormat::GbdCnf => "cnf.xz",
        UriListFormat::RawJson => "json",
    };
    Path::new(&corpus.extract_to).join(format!("{}.{}", row.id, extension))
}

fn corpus_plan_public_url(url: &str) -> (String, bool) {
    let mut redacted = false;
    let (without_fragment, fragment) = match url.split_once('#') {
        Some((base, _)) => {
            redacted = true;
            (base, Some("#REDACTED"))
        }
        None => (url, None),
    };
    let (base, query) = without_fragment
        .split_once('?')
        .map_or((without_fragment, None), |(base, query)| {
            (base, Some(query))
        });
    let mut public_base = base.to_string();
    if let Some(scheme_end) = public_base.find("://") {
        let authority_start = scheme_end + 3;
        let authority_end = public_base[authority_start..]
            .find('/')
            .map_or(public_base.len(), |offset| authority_start + offset);
        if let Some(at) = public_base[authority_start..authority_end].rfind('@') {
            public_base.replace_range(authority_start..=(authority_start + at), "");
            redacted = true;
        }
    }

    let public_query = query.map(|query| {
        query
            .split('&')
            .map(|field| {
                let (key, value) = field
                    .split_once('=')
                    .map_or((field, None), |(key, value)| (key, Some(value)));
                if corpus_plan_query_key_is_secret(key) {
                    redacted = true;
                    format!("{key}=REDACTED")
                } else if let Some(value) = value {
                    format!("{key}={value}")
                } else {
                    key.to_string()
                }
            })
            .collect::<Vec<_>>()
            .join("&")
    });
    let mut public = public_base;
    if let Some(query) = public_query {
        public.push('?');
        public.push_str(&query);
    }
    if let Some(fragment) = fragment {
        public.push_str(fragment);
    }
    (public, redacted)
}

fn corpus_plan_query_key_is_secret(key: &str) -> bool {
    let key = key.to_ascii_lowercase();
    matches!(
        key.as_str(),
        "api-key"
            | "apikey"
            | "api_key"
            | "auth"
            | "authorization"
            | "key"
            | "passwd"
            | "password"
            | "sig"
            | "token"
    ) || key.contains("credential")
        || key.contains("password")
        || key.contains("secret")
        || key.contains("signature")
        || key.contains("token")
}

fn corpus_plan_local_state(corpus: &Corpus) -> Result<(bool, bool)> {
    match corpus.source {
        Source::Release | Source::Http => {
            let cache = corpus
                .cache_path()
                .ok_or_else(|| anyhow!("{} has no resolvable cache path", corpus.name))?;
            let cache_valid = corpus.cache_is_valid(&cache);
            let installed = if corpus.archive == Archive::None {
                cache_valid
            } else {
                cache_valid && path_is_present(&corpus.extract_path())?
            };
            Ok((installed, !cache_valid))
        }
        Source::Git => {
            let installed = verify_git_checkout(corpus).is_ok();
            Ok((installed, !installed))
        }
        Source::Gbd => {
            let rows = corpus.gbd_rows()?;
            if rows.is_empty() {
                bail!("GBD manifest has no rows");
            }
            let installed = rows.iter().all(GbdRow::is_present);
            Ok((installed, !installed))
        }
        Source::UriList => {
            let rows = corpus.uri_rows()?;
            let installed = rows.iter().all(|row| row.verify(corpus).is_ok());
            Ok((installed, !installed))
        }
    }
}

fn corpus_transfer_estimate(corpus: &Corpus) -> Result<TransferEstimate> {
    if let Some(size) = corpus.size_bytes {
        return Ok(TransferEstimate {
            known_bytes: size,
            has_unknown: false,
        });
    }
    match corpus.source {
        Source::UriList => uri_list_transfer_estimate(corpus, false),
        Source::Gbd => gbd_transfer_estimate(corpus, false),
        Source::Release | Source::Http | Source::Git => Ok(TransferEstimate {
            known_bytes: 0,
            has_unknown: true,
        }),
    }
}

fn corpus_remaining_transfer_estimate(
    corpus: &Corpus,
    network_fetch_required: bool,
) -> Result<TransferEstimate> {
    if !network_fetch_required {
        return Ok(TransferEstimate::default());
    }
    if corpus.source == Source::UriList {
        return uri_list_transfer_estimate(corpus, true);
    }
    if corpus.source == Source::Gbd {
        return gbd_transfer_estimate(corpus, true);
    }
    corpus_transfer_estimate(corpus)
}

fn gbd_transfer_estimate(corpus: &Corpus, missing_only: bool) -> Result<TransferEstimate> {
    let rows = corpus.gbd_rows()?;
    if rows.is_empty() {
        bail!("GBD manifest has no rows");
    }
    let mut objects = BTreeMap::<String, (Option<u64>, Option<String>, bool)>::new();
    for row in rows {
        let verified = row.verify().is_ok();
        let entry = objects
            .entry(row.hash.clone())
            .or_insert_with(|| (row.expected_size, row.expected_sha256.clone(), verified));
        if entry.0 != row.expected_size || entry.1 != row.expected_sha256 {
            bail!(
                "{} GBD object {} repeats with conflicting response pins",
                corpus.name,
                row.hash
            );
        }
        entry.2 |= verified;
    }
    let mut estimate = TransferEstimate::default();
    for (_, (size, _, present)) in objects {
        if missing_only && present {
            continue;
        }
        match size {
            Some(size) => checked_add_bytes(
                &mut estimate.known_bytes,
                size,
                &format!("{} GBD transfer total", corpus.name),
            )?,
            None => estimate.has_unknown = true,
        }
    }
    Ok(estimate)
}

fn uri_list_transfer_estimate(corpus: &Corpus, missing_only: bool) -> Result<TransferEstimate> {
    let rows = corpus.uri_rows()?;
    let mut estimate = TransferEstimate::default();
    for row in rows {
        if missing_only && row.verify(corpus).is_ok() {
            continue;
        }
        match row.expected_size {
            Some(size) => checked_add_bytes(
                &mut estimate.known_bytes,
                size,
                &format!("{} URI-list transfer total", corpus.name),
            )?,
            None => estimate.has_unknown = true,
        }
    }
    Ok(estimate)
}

fn checked_add_bytes(total: &mut u64, value: u64, description: &str) -> Result<()> {
    *total = total
        .checked_add(value)
        .ok_or_else(|| anyhow!("{description} exceeds u64"))?;
    Ok(())
}

fn corpus_plan_tool_requirements(targets: &[&Corpus]) -> Vec<CorpusPlanToolRequirement> {
    let mut requirements = BTreeMap::<&'static str, ToolRequirementAccumulator>::new();
    for corpus in targets {
        match corpus.source {
            Source::Release => {
                add_tool_requirement(
                    &mut requirements,
                    "github-release-download",
                    "download GitHub release assets",
                    &["gh"],
                    corpus,
                );
            }
            Source::Http | Source::Gbd | Source::UriList => {
                add_tool_requirement(
                    &mut requirements,
                    "http-download",
                    "download HTTPS assets",
                    &["curl", "wget"],
                    corpus,
                );
            }
            Source::Git => {
                add_tool_requirement(
                    &mut requirements,
                    "git-checkout",
                    "fetch and verify Git checkouts",
                    &["git"],
                    corpus,
                );
                if corpus.requires_git_lfs {
                    add_tool_requirement(
                        &mut requirements,
                        "git-lfs-materialization",
                        "fetch, materialize, and verify actual Git LFS pointer objects",
                        &["git-lfs"],
                        corpus,
                    );
                }
            }
        }

        match (corpus.source, corpus.archive) {
            (Source::Release | Source::Http, Archive::Tar) => {
                add_tool_requirement(
                    &mut requirements,
                    "tar-extraction",
                    "extract tar archives",
                    &["tar"],
                    corpus,
                );
                if corpus.source == Source::Release {
                    add_tool_requirement(
                        &mut requirements,
                        "zstd-decompression",
                        "decompress release tar.zst archives",
                        &["zstd"],
                        corpus,
                    );
                } else if let Some(tool) = corpus_tar_compression_tool(corpus) {
                    let (id, purpose) = match tool {
                        "xz" => ("xz-decompression", "decompress xz-compressed tar archives"),
                        "gzip" => (
                            "gzip-decompression",
                            "decompress gzip-compressed tar archives",
                        ),
                        "bzip2" => (
                            "bzip2-decompression",
                            "decompress bzip2-compressed tar archives",
                        ),
                        "zstd" => (
                            "zstd-decompression",
                            "decompress zstd-compressed tar archives",
                        ),
                        _ => unreachable!("known compression tool"),
                    };
                    add_tool_requirement(&mut requirements, id, purpose, &[tool], corpus);
                }
            }
            (Source::Http, Archive::Zip) => {
                add_tool_requirement(
                    &mut requirements,
                    "zip-extraction",
                    "extract zip archives",
                    &["unzip"],
                    corpus,
                );
            }
            _ => {}
        }
        if corpus.source == Source::Gbd
            || (corpus.source == Source::UriList && corpus.uri_list_format == UriListFormat::GbdCnf)
        {
            add_tool_requirement(
                &mut requirements,
                "xz-decompression",
                "materialize xz-compressed benchmark-database payloads",
                &["xz"],
                corpus,
            );
        }
    }

    requirements
        .into_iter()
        .map(|(id, requirement)| {
            let alternatives = requirement
                .alternatives
                .into_iter()
                .map(str::to_string)
                .collect::<Vec<_>>();
            let available = alternatives
                .iter()
                .filter(|tool| which(tool))
                .cloned()
                .collect::<Vec<_>>();
            CorpusPlanToolRequirement {
                id: id.to_string(),
                purpose: requirement.purpose.to_string(),
                satisfied: !available.is_empty(),
                alternatives,
                available,
                required_by: requirement.required_by.into_iter().collect(),
            }
        })
        .collect()
}

fn add_tool_requirement(
    requirements: &mut BTreeMap<&'static str, ToolRequirementAccumulator>,
    id: &'static str,
    purpose: &'static str,
    alternatives: &[&'static str],
    corpus: &Corpus,
) {
    let requirement = requirements
        .entry(id)
        .or_insert_with(|| ToolRequirementAccumulator {
            purpose,
            alternatives: BTreeSet::new(),
            required_by: BTreeSet::new(),
        });
    requirement
        .alternatives
        .extend(alternatives.iter().copied());
    requirement.required_by.insert(corpus.name.clone());
}

fn corpus_tar_compression_tool(corpus: &Corpus) -> Option<&'static str> {
    let name = corpus
        .cache_name
        .as_deref()
        .or(corpus.url.as_deref())
        .or(corpus.asset.as_deref())?
        .to_ascii_lowercase();
    if name.contains(".tar.xz") || name.contains(".txz") {
        Some("xz")
    } else if name.contains(".tar.gz") || name.contains(".tgz") {
        Some("gzip")
    } else if name.contains(".tar.bz2") || name.contains(".tbz") {
        Some("bzip2")
    } else if name.contains(".tar.zst") || name.contains(".tar.zstd") || name.contains(".tzst") {
        Some("zstd")
    } else {
        None
    }
}

#[cfg(unix)]
fn available_filesystem_bytes(path: &Path) -> Result<Option<u64>> {
    let existing = path
        .ancestors()
        .find(|candidate| candidate.exists())
        .ok_or_else(|| {
            anyhow!(
                "no existing ancestor for filesystem path {}",
                path.display()
            )
        })?;
    let stats = nix::sys::statvfs::statvfs(existing)
        .with_context(|| format!("inspect filesystem capacity at {}", existing.display()))?;
    let block_size = if stats.fragment_size() == 0 {
        stats.block_size()
    } else {
        stats.fragment_size()
    };
    // Portable width fix: `fsblkcnt_t` is u32 on macOS and u64 on Linux
    // (`u64::from` is the identity there), and `c_ulong` block sizes are u64
    // on both — do the multiply in u64 unconditionally.
    Ok(Some(
        u64::from(stats.blocks_available()).saturating_mul(u64::from(block_size)),
    ))
}

#[cfg(not(unix))]
fn available_filesystem_bytes(path: &Path) -> Result<Option<u64>> {
    let _ = path;
    Ok(None)
}

fn print_corpus_plan(plan: &CorpusPlanSummary) {
    println!("Corpus acquisition plan (read-only)");
    println!("  selected assets:       {}", plan.selected_assets);
    println!("  dependency assets:     {}", plan.dependency_assets);
    println!("  dependency closure:    {}", plan.closure_assets);
    println!("  installed assets:      {}", plan.installed_assets);
    println!("  missing/stale assets:  {}", plan.missing_or_stale_assets);
    println!("  network fetch assets:  {}", plan.network_fetch_assets);
    println!(
        "  known transfer:        {}",
        human_bytes(plan.known_transfer_bytes)
    );
    println!(
        "  known remaining:       {}",
        human_bytes(plan.known_remaining_transfer_bytes)
    );
    println!(
        "  available filesystem:  {} ({})",
        plan.available_filesystem_bytes
            .map(human_bytes)
            .unwrap_or_else(|| "unknown".to_string()),
        plan.filesystem_path
    );
    if plan.unknown_size_sources.is_empty() {
        println!("  unknown-size assets:   none");
    } else {
        let sources = plan
            .unknown_size_sources
            .iter()
            .map(|(source, count)| format!("{source}={count}"))
            .collect::<Vec<_>>()
            .join(", ");
        println!("  unknown-size assets:   {sources}");
    }
    if plan.unknown_remaining_size_sources.is_empty() {
        println!("  unknown remaining:     none");
    } else {
        let sources = plan
            .unknown_remaining_size_sources
            .iter()
            .map(|(source, count)| format!("{source}={count}"))
            .collect::<Vec<_>>()
            .join(", ");
        println!("  unknown remaining:     {sources}");
    }
    println!("Required tools:");
    for requirement in &plan.required_tools {
        let state = if requirement.satisfied {
            "ok"
        } else {
            "MISSING"
        };
        println!(
            "  [{state}] {:<20} {} ({})",
            requirement.alternatives.join(" | "),
            requirement.purpose,
            requirement.required_by.join(", "),
        );
    }
    if let Some(warning) = &plan.capacity_warning {
        println!("WARNING: {warning}");
    }
    println!("NOTE: {}", plan.capacity_note);
}

fn run_list(args: ListArgs) -> Result<i32> {
    let manifest = Manifest::load(&args.manifest.manifest)?;
    let corpora = if args.groups.is_empty() {
        manifest.corpora.iter().collect()
    } else {
        manifest.select(&[], false, &args.groups)?
    };
    println!(
        "{:<32} {:<8} {:>9}  {:<24} GROUPS",
        "NAME", "SOURCE", "SIZE", "STATUS"
    );
    for c in corpora {
        let size = c.size_bytes.map(human_bytes).unwrap_or_else(|| "-".into());
        let groups = if c.groups.is_empty() {
            "-".to_string()
        } else {
            c.groups.join(",")
        };
        println!(
            "{:<32} {:<8} {:>9}  {:<24} {}",
            c.name,
            c.source.label(),
            size,
            c.local_status(),
            groups,
        );
    }
    Ok(0)
}

fn run_download(args: DownloadArgs) -> Result<i32> {
    let manifest = Manifest::load(&args.manifest.manifest)?;
    let selected = manifest.select(&args.names, args.all, &args.groups)?;
    let targets = manifest.dependency_order(&selected)?;
    for c in targets {
        match c.source {
            Source::Release => download_release(&manifest, c, args.force)?,
            Source::Http => download_http(c, args.force)?,
            Source::Git => download_git(c, args.force)?,
            Source::Gbd => download_gbd(c, args.force)?,
            Source::UriList => download_uri_list(c, args.force)?,
        }
    }
    Ok(0)
}

fn run_verify(args: VerifyArgs) -> Result<i32> {
    let manifest = Manifest::load(&args.manifest.manifest)?;
    let selected = manifest.select(&args.names, args.all, &args.groups)?;
    let targets = manifest.dependency_order(&selected)?;
    let mut bad = 0;
    for c in targets {
        if c.source == Source::Gbd {
            // GBD has no single archive. Verify every declared response pin;
            // legacy rows without response pins retain presence-only behavior.
            let rows = c.gbd_rows()?;
            let verified = rows.iter().filter(|row| row.verify().is_ok()).count();
            if verified == rows.len() {
                println!(
                    "{}: ok ({}/{} response rows verified)",
                    c.name,
                    verified,
                    rows.len()
                );
            } else {
                println!(
                    "{}: incomplete or stale ({}/{} response rows verified)",
                    c.name,
                    verified,
                    rows.len()
                );
                bad += 1;
            }
            continue;
        }
        if c.source == Source::UriList {
            let rows = c.uri_rows()?;
            let verified = rows.iter().filter(|row| row.verify(c).is_ok()).count();
            if verified == rows.len() {
                println!(
                    "{}: ok ({}/{} files verified)",
                    c.name,
                    verified,
                    rows.len()
                );
            } else {
                println!(
                    "{}: incomplete or stale ({}/{} files verified)",
                    c.name,
                    verified,
                    rows.len()
                );
                bad += 1;
            }
            continue;
        }
        if c.source == Source::Git {
            match verify_git_checkout(c) {
                Ok(()) if c.commit.is_some() => {
                    println!("{}: ok (commit pin verified)", c.name);
                }
                Ok(()) => {
                    println!("{}: skipped (git source has no commit pin)", c.name);
                }
                Err(error) => {
                    println!("{}: MISMATCH ({error:#})", c.name);
                    bad += 1;
                }
            }
            continue;
        }
        if !c.has_file_pins() {
            println!("{}: skipped (no sha256 or size pin)", c.name);
            continue;
        }
        let Some(cache) = c.cache_path() else {
            println!("{}: skipped (source has no cache)", c.name);
            continue;
        };
        if !path_is_present(&cache)? {
            println!("{}: archive missing ({})", c.name, cache.display());
            bad += 1;
            continue;
        }
        match validate_file_pins(&cache, c.sha256.as_deref(), c.size_bytes)
            .and_then(|()| verify_materialized_archive(c, &cache))
        {
            Ok(()) => {
                let pin = match c.sha256.as_deref() {
                    Some(sha256) => sha256.get(..16).unwrap_or(sha256),
                    None => "size-only",
                };
                println!("{}: ok ({pin})", c.name);
            }
            Err(error) => {
                println!("{}: MISMATCH ({error:#})", c.name);
                bad += 1;
            }
        }
    }
    Ok(if bad == 0 { 0 } else { 1 })
}

fn run_campaign_audit(args: CampaignAuditArgs) -> Result<i32> {
    let manifest_path = resolve_repo_file(&args.manifest.manifest);
    let assets_path = resolve_repo_file(&args.assets);
    let catalog_path = resolve_repo_file(&args.catalog);
    let corpus_manifest = Manifest::load(&manifest_path)?;
    let assets_body = fs::read_to_string(&assets_path)
        .with_context(|| format!("read campaign assets {}", assets_path.display()))?;
    let assets: CampaignAssetManifest = toml::from_str(&assets_body)
        .with_context(|| format!("parse campaign assets {}", assets_path.display()))?;
    let catalog_body = fs::read_to_string(&catalog_path)
        .with_context(|| format!("read campaign catalog {}", catalog_path.display()))?;
    let catalog: CampaignCatalog = toml::from_str(&catalog_body)
        .with_context(|| format!("parse campaign catalog {}", catalog_path.display()))?;

    if assets.schema_version != 1 {
        bail!(
            "campaign assets {}: unsupported schema_version {} (expected 1)",
            assets_path.display(),
            assets.schema_version
        );
    }
    if !declared_path_matches(&assets.catalog, &catalog_path) {
        bail!(
            "campaign assets declare catalog {:?}, but audit uses {}",
            assets.catalog,
            catalog_path.display()
        );
    }
    if !declared_path_matches(&assets.corpora_manifest, &manifest_path) {
        bail!(
            "campaign assets declare corpora_manifest {:?}, but audit uses {}",
            assets.corpora_manifest,
            manifest_path.display()
        );
    }
    if assets.scope != "exactly-one-event-per-catalog-competition-edition-pair" {
        bail!("campaign assets have unsupported scope {:?}", assets.scope);
    }
    let profiles_path = resolve_declared_manifest_path(&assets_path, &assets.profiles_manifest)?;
    let profiles_body = fs::read_to_string(&profiles_path)
        .with_context(|| format!("read campaign profiles {}", profiles_path.display()))?;
    let profiles: CampaignRunProfiles = toml::from_str(&profiles_body)
        .with_context(|| format!("parse campaign profiles {}", profiles_path.display()))?;
    validate_campaign_profiles(&profiles)
        .with_context(|| format!("validate campaign profiles {}", profiles_path.display()))?;

    let mut catalog_track_map = BTreeMap::new();
    let mut catalog_events = BTreeSet::new();
    for track in &catalog.tracks {
        if catalog_track_map
            .insert(
                track.id.as_str(),
                (track.competition.as_str(), track.edition),
            )
            .is_some()
        {
            bail!("campaign catalog repeats track id {:?}", track.id);
        }
        catalog_events.insert((track.competition.as_str(), track.edition));
    }
    if catalog.tracks.is_empty() {
        bail!("campaign catalog contains no tracks");
    }

    let mut event_ids = BTreeSet::new();
    let mut asset_events = BTreeSet::new();
    let mut assigned_tracks = BTreeSet::new();
    let mut referenced_assets = BTreeSet::new();
    let mut referenced_competitor_assets = BTreeSet::new();
    let mut status_counts = BTreeMap::new();
    let mut local_run_support_counts = BTreeMap::new();
    let mut competitor_replay_status_counts = BTreeMap::new();
    const CORPUS_STATUSES: &[&str] = &[
        "complete-public",
        "partial-public",
        "unavailable",
        "not-applicable",
    ];
    for event in &assets.event {
        if event.id != format!("{}-{}", event.competition, event.edition) {
            bail!(
                "campaign event id {:?} must equal <competition>-<edition>",
                event.id
            );
        }
        if !event_ids.insert(event.id.as_str()) {
            bail!("campaign assets repeat event id {:?}", event.id);
        }
        if !asset_events.insert((event.competition.as_str(), event.edition)) {
            bail!(
                "campaign assets repeat competition/edition {} {}",
                event.competition,
                event.edition
            );
        }
        if event.track_ids.is_empty() {
            bail!("campaign event {} contains no explicit track_ids", event.id);
        }
        let mut event_tracks = BTreeSet::new();
        for track_id in &event.track_ids {
            if !event_tracks.insert(track_id.as_str()) {
                bail!(
                    "campaign event {} repeats track id {:?}",
                    event.id,
                    track_id
                );
            }
            let Some((competition, edition)) = catalog_track_map.get(track_id.as_str()) else {
                bail!(
                    "campaign event {} references unknown track id {:?}",
                    event.id,
                    track_id
                );
            };
            if *competition != event.competition.as_str() || *edition != event.edition {
                bail!(
                    "campaign event {} assigns track {} from {}-{}",
                    event.id,
                    track_id,
                    competition,
                    edition
                );
            }
            if !assigned_tracks.insert(track_id.as_str()) {
                bail!("campaign assets assign track {track_id:?} more than once");
            }
        }
        if !CORPUS_STATUSES.contains(&event.corpus_status.as_str()) {
            bail!(
                "campaign event {} has invalid corpus_status {:?}",
                event.id,
                event.corpus_status
            );
        }
        if event.reason.trim().is_empty()
            || event.official_machine_status.trim().is_empty()
            || event.local_run_support.trim().is_empty()
            || event.competitor_replay_status.trim().is_empty()
            || event.subset_policy.trim().is_empty()
        {
            bail!("campaign event {} has an empty audit field", event.id);
        }
        if event.corpus_status == "complete-public" && event.corpora.is_empty() {
            bail!(
                "campaign event {} claims complete-public with no corpus assets",
                event.id
            );
        }
        if event.corpus_status == "not-applicable" && !event.corpora.is_empty() {
            bail!(
                "campaign event {} is not-applicable but references corpus assets",
                event.id
            );
        }
        let mut event_assets = BTreeSet::new();
        for name in &event.corpora {
            if !event_assets.insert(name.as_str()) {
                bail!("campaign event {} repeats corpus {:?}", event.id, name);
            }
            let corpus = corpus_manifest.find(name).with_context(|| {
                format!("campaign event {} references corpus {:?}", event.id, name)
            })?;
            validate_campaign_corpus_pin(corpus, &corpus_manifest)
                .with_context(|| format!("campaign event {} corpus {}", event.id, name))?;
            referenced_assets.insert(name.as_str());
        }
        let mut event_competitor_assets = BTreeSet::new();
        for name in &event.competitor_corpora {
            if !event_competitor_assets.insert(name.as_str()) {
                bail!(
                    "campaign event {} repeats competitor corpus {:?}",
                    event.id,
                    name
                );
            }
            let corpus = corpus_manifest.find(name).with_context(|| {
                format!(
                    "campaign event {} references competitor corpus {:?}",
                    event.id, name
                )
            })?;
            validate_campaign_corpus_pin(corpus, &corpus_manifest).with_context(|| {
                format!("campaign event {} competitor corpus {}", event.id, name)
            })?;
            referenced_competitor_assets.insert(name.as_str());
        }
        *status_counts
            .entry(event.corpus_status.clone())
            .or_insert(0) += 1;
        *local_run_support_counts
            .entry(event.local_run_support.clone())
            .or_insert(0) += 1;
        *competitor_replay_status_counts
            .entry(event.competitor_replay_status.clone())
            .or_insert(0) += 1;
    }

    if catalog_events != asset_events {
        let missing = catalog_events
            .difference(&asset_events)
            .map(|(competition, edition)| format!("{competition}-{edition}"))
            .collect::<Vec<_>>();
        let extra = asset_events
            .difference(&catalog_events)
            .map(|(competition, edition)| format!("{competition}-{edition}"))
            .collect::<Vec<_>>();
        bail!(
            "campaign event coverage mismatch: missing [{}], extra [{}]",
            missing.join(", "),
            extra.join(", ")
        );
    }
    let catalog_track_ids = catalog_track_map.keys().copied().collect::<BTreeSet<_>>();
    if catalog_track_ids != assigned_tracks {
        let missing = catalog_track_ids
            .difference(&assigned_tracks)
            .copied()
            .collect::<Vec<_>>();
        let extra = assigned_tracks
            .difference(&catalog_track_ids)
            .copied()
            .collect::<Vec<_>>();
        bail!(
            "campaign track coverage mismatch: missing [{}], extra [{}]",
            missing.join(", "),
            extra.join(", ")
        );
    }

    let grouped_assets = corpus_manifest
        .corpora
        .iter()
        .filter(|corpus| {
            corpus.groups.iter().any(|group| {
                group == "competition-2025-2026" || group == "competition-2025-2026-external"
            })
        })
        .map(|corpus| corpus.name.as_str())
        .collect::<BTreeSet<_>>();
    if grouped_assets != referenced_assets {
        let unreferenced = grouped_assets
            .difference(&referenced_assets)
            .copied()
            .collect::<Vec<_>>();
        let ungrouped = referenced_assets
            .difference(&grouped_assets)
            .copied()
            .collect::<Vec<_>>();
        bail!(
            "campaign asset join mismatch: unreferenced group assets [{}], referenced ungrouped assets [{}]",
            unreferenced.join(", "),
            ungrouped.join(", ")
        );
    }
    let grouped_competitor_assets = corpus_manifest
        .corpora
        .iter()
        .filter(|corpus| {
            corpus
                .groups
                .iter()
                .any(|group| group == "competition-2025-2026-competitors")
        })
        .map(|corpus| corpus.name.as_str())
        .collect::<BTreeSet<_>>();
    if grouped_competitor_assets != referenced_competitor_assets {
        let unreferenced = grouped_competitor_assets
            .difference(&referenced_competitor_assets)
            .copied()
            .collect::<Vec<_>>();
        let ungrouped = referenced_competitor_assets
            .difference(&grouped_competitor_assets)
            .copied()
            .collect::<Vec<_>>();
        bail!(
            "campaign competitor join mismatch: unreferenced group assets [{}], referenced ungrouped assets [{}]",
            unreferenced.join(", "),
            ungrouped.join(", ")
        );
    }

    let locally_verified_assets = referenced_assets
        .iter()
        .filter(|name| {
            corpus_manifest
                .find(name)
                .is_ok_and(|corpus| verify_local_corpus(corpus, args.require_installed).is_ok())
        })
        .count();
    let locally_missing_or_stale_assets = referenced_assets.len() - locally_verified_assets;
    let locally_verified_competitor_assets = referenced_competitor_assets
        .iter()
        .filter(|name| {
            corpus_manifest
                .find(name)
                .is_ok_and(|corpus| verify_local_corpus(corpus, args.require_installed).is_ok())
        })
        .count();
    let locally_missing_or_stale_competitor_assets =
        referenced_competitor_assets.len() - locally_verified_competitor_assets;
    let summary = CampaignAuditSummary {
        catalog_tracks: catalog.tracks.len(),
        catalog_events: catalog_events.len(),
        asset_events: assets.event.len(),
        referenced_assets: referenced_assets.len(),
        referenced_competitor_assets: referenced_competitor_assets.len(),
        locally_verified_assets,
        locally_missing_or_stale_assets,
        locally_verified_competitor_assets,
        locally_missing_or_stale_competitor_assets,
        run_profiles: profiles.profile.len(),
        subset_profiles: profiles.subset.len(),
        status_counts,
        local_run_support_counts,
        competitor_replay_status_counts,
        scope: assets.scope,
    };

    if args.json {
        println!(
            "{}",
            serde_json::to_string_pretty(&summary).context("serialize campaign audit summary")?
        );
    } else {
        println!(
            "campaign audit: {} tracks / {} events / {} assets",
            summary.catalog_tracks, summary.asset_events, summary.referenced_assets
        );
        println!(
            "local assets: {} verified, {} missing or stale",
            summary.locally_verified_assets, summary.locally_missing_or_stale_assets
        );
        println!(
            "competitor assets: {} referenced; {} verified, {} missing or stale",
            summary.referenced_competitor_assets,
            summary.locally_verified_competitor_assets,
            summary.locally_missing_or_stale_competitor_assets
        );
        println!(
            "profiles: {} run / {} subset",
            summary.run_profiles, summary.subset_profiles
        );
        println!("corpus status: {:?}", summary.status_counts);
        println!("local run support: {:?}", summary.local_run_support_counts);
        println!(
            "competitor replay: {:?}",
            summary.competitor_replay_status_counts
        );
    }
    if args.require_installed
        && (summary.locally_missing_or_stale_assets != 0
            || summary.locally_missing_or_stale_competitor_assets != 0)
    {
        return Ok(1);
    }
    Ok(0)
}

fn declared_path_matches(declared: &str, actual: &Path) -> bool {
    actual == Path::new(declared) || actual.ends_with(declared)
}

fn resolve_declared_manifest_path(owner: &Path, declared: &str) -> Result<PathBuf> {
    let declared = Path::new(declared);
    if declared.is_absolute() {
        return Ok(declared.to_path_buf());
    }
    let owner = if owner.is_absolute() {
        owner.to_path_buf()
    } else {
        std::env::current_dir()
            .context("resolve current directory")?
            .join(owner)
    };
    let parent = owner
        .parent()
        .ok_or_else(|| anyhow!("manifest {} has no parent directory", owner.display()))?;
    let root = if parent.file_name().is_some_and(|name| name == "benchmarks") {
        parent.parent().unwrap_or(parent)
    } else {
        parent
    };
    Ok(root.join(declared))
}

fn validate_campaign_profiles(profiles: &CampaignRunProfiles) -> Result<()> {
    if profiles.schema_version != 1 {
        bail!(
            "unsupported schema_version {} (expected 1)",
            profiles.schema_version
        );
    }
    let mut ids = BTreeSet::new();
    for profile in &profiles.profile {
        if !ids.insert(profile.id.as_str()) {
            bail!("duplicate run profile {:?}", profile.id);
        }
        if profile.run_class.trim().is_empty() {
            bail!("run profile {} has an empty run_class", profile.id);
        }
        if !profile.oom_guard_required {
            bail!("run profile {} does not require _oom_guard.py", profile.id);
        }
        if profile.run_class == "proxy" && profile.score_comparable {
            bail!("proxy run profile {} claims comparable scores", profile.id);
        }
        if profile.run_class == "official-replay" && !profile.requires_exact_hardware {
            bail!(
                "official replay profile {} does not require exact hardware",
                profile.id
            );
        }
    }
    for required in [
        "reviewer-full",
        "canary-proxy",
        "targeted-proxy",
        "same-host-calibrated",
        "official-replay",
        "high-memory-same-host",
    ] {
        if !ids.contains(required) {
            bail!("missing required run profile {required}");
        }
    }
    let mut subset_ids = BTreeSet::new();
    for subset in &profiles.subset {
        if !subset_ids.insert(subset.id.as_str()) {
            bail!("duplicate subset profile {:?}", subset.id);
        }
        if subset.kind.trim().is_empty() || subset.scoring.trim().is_empty() {
            bail!("subset profile {} has an empty field", subset.id);
        }
    }
    for required in ["committed-canary", "rolling-shard-64", "full-corpus"] {
        if !subset_ids.contains(required) {
            bail!("missing required subset profile {required}");
        }
    }
    Ok(())
}

fn validate_campaign_corpus_pin(corpus: &Corpus, manifest: &Manifest) -> Result<()> {
    match corpus.source {
        Source::Release => {
            validate_campaign_file_pins(corpus, "release")?;
        }
        Source::Http => {
            let url = corpus.url.as_deref().unwrap_or_default();
            if !url.starts_with("https://") {
                bail!("HTTP asset URL is not HTTPS");
            }
            validate_campaign_file_pins(corpus, "HTTP")?;
        }
        Source::Git => {
            let commit = corpus.commit.as_deref().unwrap_or_default();
            if commit.len() != 40 || !commit.chars().all(|ch| ch.is_ascii_hexdigit()) {
                bail!("git asset has no exact 40-hex commit pin");
            }
        }
        Source::Gbd => {
            let rows = corpus.gbd_rows()?;
            if rows.is_empty() {
                bail!("GBD asset has no response rows");
            }
            if rows.iter().any(|row| !row.has_complete_pins()) {
                bail!("campaign GBD asset contains a response row without size and SHA-256");
            }
            let destination = corpus.extract_path();
            if rows
                .iter()
                .any(|row| !row.raw_path().starts_with(&destination))
            {
                bail!("campaign GBD row path escapes the corpus destination");
            }
            let unique_paths = rows
                .iter()
                .map(|row| row.local_path.as_str())
                .collect::<BTreeSet<_>>();
            if unique_paths.len() != rows.len() {
                bail!("campaign GBD asset repeats a local benchmark path");
            }
            validate_gbd_upstream(corpus, manifest, &rows)?;
        }
        Source::UriList => match corpus.uri_list_format {
            UriListFormat::RawJson => {
                let rows = corpus.uri_rows()?;
                if rows.iter().any(|row| {
                    row.expected_size.is_none() || row.expected_sha256.as_deref().is_none()
                }) {
                    bail!("raw-json URI list contains an unpinned row");
                }
            }
            UriListFormat::GbdCnf => {
                let rows = corpus.uri_rows()?;
                if rows.iter().any(|row| {
                    row.expected_size.is_none() || row.expected_sha256.as_deref().is_none()
                }) {
                    bail!("GBD URI list contains an unpinned response row");
                }
                validate_uri_list_upstream(corpus, manifest, &rows)?;
            }
        },
    }
    Ok(())
}

fn validate_campaign_file_pins(corpus: &Corpus, source_label: &str) -> Result<()> {
    if corpus.size_bytes.is_none_or(|size| size == 0) {
        bail!("{source_label} asset has no positive size pin");
    }
    let sha256 = corpus.sha256.as_deref().unwrap_or_default();
    if !is_canonical_sha256(sha256) {
        bail!("{source_label} asset has no valid lowercase SHA-256 pin");
    }
    Ok(())
}

fn validate_gbd_upstream(
    corpus: &Corpus,
    manifest: &Manifest,
    pinned_rows: &[GbdRow],
) -> Result<()> {
    let pinned_hashes = pinned_rows
        .iter()
        .map(|row| row.hash.as_str())
        .collect::<Vec<_>>();
    for dependency_name in &corpus.depends_on {
        let dependency = manifest.find(dependency_name)?;
        if dependency.source != Source::Http
            || dependency.archive != Archive::None
            || dependency.sha256.is_none()
        {
            continue;
        }
        let body = fs::read_to_string(dependency.extract_path()).with_context(|| {
            format!(
                "read pinned upstream GBD selection {}",
                dependency.extract_path().display()
            )
        })?;
        let mut lines = body.lines();
        let Some(header) = lines.next() else {
            continue;
        };
        let columns = split_csv_line(header);
        let Some(hash_index) = columns.iter().position(|column| column == "hash") else {
            continue;
        };
        let upstream_hashes = lines
            .filter(|line| !line.trim().is_empty())
            .map(split_csv_line)
            .map(|fields| fields.get(hash_index).cloned().unwrap_or_default())
            .collect::<Vec<_>>();
        if upstream_hashes
            .iter()
            .map(String::as_str)
            .eq(pinned_hashes.iter().copied())
        {
            return Ok(());
        }
    }
    bail!(
        "pinned GBD response rows do not exactly match any SHA-256-pinned HTTP selection dependency"
    )
}

fn validate_uri_list_upstream(
    corpus: &Corpus,
    manifest: &Manifest,
    pinned_rows: &[UriRow],
) -> Result<()> {
    let pinned_urls = pinned_rows
        .iter()
        .map(|row| row.url.as_str())
        .collect::<Vec<_>>();
    let mut checked_dependency = false;
    for dependency_name in &corpus.depends_on {
        let dependency = manifest.find(dependency_name)?;
        if dependency.source != Source::Http
            || dependency.archive != Archive::None
            || dependency.sha256.is_none()
        {
            continue;
        }
        let body = fs::read_to_string(dependency.extract_path()).with_context(|| {
            format!(
                "read pinned upstream URI inventory {}",
                dependency.extract_path().display()
            )
        })?;
        let upstream_urls = body
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
            .collect::<Vec<_>>();
        if upstream_urls == pinned_urls {
            checked_dependency = true;
            break;
        }
    }
    if !checked_dependency {
        bail!("pinned URI rows do not exactly match any SHA-256-pinned HTTP inventory dependency");
    }
    Ok(())
}

fn verify_local_corpus(corpus: &Corpus, verify_materialized: bool) -> Result<()> {
    match corpus.source {
        Source::Git => verify_git_checkout(corpus),
        Source::Gbd => {
            let rows = corpus.gbd_rows()?;
            for row in rows {
                row.verify()?;
            }
            Ok(())
        }
        Source::UriList => {
            let rows = corpus.uri_rows()?;
            for row in rows {
                row.verify(corpus)?;
            }
            Ok(())
        }
        Source::Release | Source::Http => {
            let cache = corpus
                .cache_path()
                .ok_or_else(|| anyhow!("asset has no local cache path"))?;
            validate_file_pins(&cache, corpus.sha256.as_deref(), corpus.size_bytes)?;
            if corpus.archive != Archive::None && !path_is_present(&corpus.extract_path())? {
                bail!("extracted tree {} is missing", corpus.extract_to);
            }
            if verify_materialized {
                verify_materialized_archive(corpus, &cache)?;
            }
            Ok(())
        }
    }
}

fn run_upload(args: UploadArgs) -> Result<i32> {
    let manifest_path = resolve_repo_file(&args.manifest.manifest);
    let mut manifest = Manifest::load(&manifest_path)?;
    let release_tag = args
        .release_tag
        .clone()
        .unwrap_or_else(|| manifest.release_tag.clone());
    let repo = manifest.repo.clone();

    let corpus = manifest.find(&args.name)?.clone();
    if corpus.source != Source::Release {
        bail!(
            "{}: upload only supported for source=release (this corpus is {:?})",
            args.name,
            corpus.source
        );
    }
    let from = args.from.clone().unwrap_or_else(|| corpus.extract_path());
    if !from.is_dir() {
        bail!("upload source {} is not a directory", from.display());
    }
    let cache = corpus.cache_path().expect("release has cache_path");
    println!("==> packing {} -> {}", from.display(), cache.display());
    pack_tarball(&from, &cache)?;

    let size = fs::metadata(&cache)
        .with_context(|| format!("stat {}", cache.display()))?
        .len();
    let sha = local_sha256(&cache)?;
    println!("    sha256: {sha}");
    println!("    bytes:  {size}");

    println!("==> upload to {repo} {release_tag}");
    gh_release_upload(&repo, &release_tag, &cache, args.clobber)?;

    let entry = manifest.find_mut(&args.name)?;
    entry.sha256 = Some(sha);
    entry.size_bytes = Some(size);
    manifest.save(&manifest_path)?;
    println!("==> manifest updated ({})", manifest_path.display());
    Ok(0)
}

fn run_prune(args: PruneArgs) -> Result<i32> {
    let manifest = Manifest::load(&args.manifest.manifest)?;
    let targets = manifest.select(&args.names, args.all, &[])?;
    for c in targets {
        if c.source == Source::Gbd {
            // Remove the per-row files — both the raw .xz artifact and its
            // decompressed sibling — but keep the manifest CSV and the
            // directory, so the corpus can be re-downloaded.
            for row in c.gbd_rows()? {
                for p in [row.raw_path(), row.decompressed_path()] {
                    if p.exists() {
                        println!("rm {}", p.display());
                        fs::remove_file(&p).with_context(|| format!("rm {}", p.display()))?;
                    }
                }
            }
            continue;
        }
        if c.source == Source::UriList {
            for row in c.uri_rows()? {
                for path in row.owned_paths(c) {
                    if path.exists() {
                        println!("rm {}", path.display());
                        fs::remove_file(&path).with_context(|| format!("rm {}", path.display()))?;
                    }
                }
            }
            continue;
        }
        let extract = c.extract_path();
        if c.archive == Archive::None {
            // extract_to is the cached file itself (e.g. qbflib's zip).
            if extract.exists() {
                println!("rm {}", extract.display());
                fs::remove_file(&extract).with_context(|| format!("rm {}", extract.display()))?;
            }
            continue;
        }
        if extract.exists() {
            println!("rm -rf {}", extract.display());
            fs::remove_dir_all(&extract)
                .with_context(|| format!("rm -rf {}", extract.display()))?;
        }
        if args.archive {
            if let Some(cache) = c.cache_path() {
                if cache.exists() {
                    println!("rm {}", cache.display());
                    fs::remove_file(&cache).with_context(|| format!("rm {}", cache.display()))?;
                }
            }
        }
    }
    Ok(0)
}

fn run_check_urls(args: CheckUrlsArgs) -> Result<i32> {
    let manifest = Manifest::load(&args.manifest.manifest)?;
    let targets: Vec<&Corpus> = if !args.groups.is_empty() {
        manifest.select(&args.names, false, &args.groups)?
    } else if args.names.is_empty() {
        manifest.corpora.iter().collect()
    } else {
        args.names
            .iter()
            .map(|n| manifest.find(n))
            .collect::<Result<_>>()?
    };

    // For release entries, fetch the asset list once.
    let release_assets = if targets.iter().any(|c| c.source == Source::Release) {
        Some(gh_release_assets(&manifest.repo, &manifest.release_tag)?)
    } else {
        None
    };

    let mut bad = 0;
    for c in &targets {
        let (target, verdict) = match c.source {
            Source::Release => {
                let asset = c.asset.as_deref().unwrap_or("(missing asset)");
                let assets = release_assets.as_ref().expect("populated above");
                let ok = assets.iter().any(|a| a == asset);
                (
                    format!(
                        "release:{}/{}#{}",
                        manifest.repo, manifest.release_tag, asset
                    ),
                    if ok {
                        "ok".to_string()
                    } else {
                        "MISSING asset".to_string()
                    },
                )
            }
            Source::Http | Source::Git => {
                let url = c.url.as_deref().unwrap_or("(missing url)");
                match http_status(url) {
                    Ok(code) if (200..400).contains(&code) => {
                        (url.to_string(), format!("ok ({code})"))
                    }
                    Ok(code) => (url.to_string(), format!("HTTP {code}")),
                    Err(e) => (url.to_string(), format!("error: {e}")),
                }
            }
            Source::Gbd => {
                // Check one representative hash from the manifest.
                match c.gbd_rows() {
                    Ok(rows) if rows.is_empty() => {
                        ("(empty manifest)".to_string(), "MISSING rows".to_string())
                    }
                    Ok(rows) => {
                        let url = format!("{}/{}", GBD_FILE_BASE, rows[0].hash);
                        match http_status(&url) {
                            Ok(code) if (200..400).contains(&code) => (url, format!("ok ({code})")),
                            Ok(code) => (url, format!("HTTP {code}")),
                            Err(e) => (url, format!("error: {e}")),
                        }
                    }
                    Err(e) => ("(no manifest)".to_string(), format!("error: {e}")),
                }
            }
            Source::UriList => match c.uri_rows() {
                Ok(rows) => {
                    let url = rows[0].url.clone();
                    match http_status(&url) {
                        Ok(code) if (200..400).contains(&code) => (url, format!("ok ({code})")),
                        Ok(code) => (url, format!("HTTP {code}")),
                        Err(error) => (url, format!("error: {error}")),
                    }
                }
                Err(error) => ("(no manifest)".to_string(), format!("error: {error}")),
            },
        };
        if !verdict.starts_with("ok") {
            bad += 1;
        }
        println!(
            "{:<32} {:<8} {} -> {}",
            c.name,
            c.source.label(),
            target,
            verdict,
        );
    }
    if bad > 0 {
        eprintln!(
            "\n{} broken entr{}.",
            bad,
            if bad == 1 { "y" } else { "ies" }
        );
        return Ok(1);
    }
    Ok(0)
}

/// Liveness check via curl. Tries HEAD first (cheap); falls back to a
/// 1-byte range GET if the server returns 405. Follows redirects. Returns
/// the final HTTP status code. Treat 200-399 as live.
fn http_status(url: &str) -> Result<u32> {
    if !which("curl") {
        bail!("curl not available on PATH");
    }
    let head_code = curl_status(&["-sIL", "--max-time", "15", url])?;
    if (200..400).contains(&head_code) {
        return Ok(head_code);
    }
    // Some artifact servers reject or mishandle HEAD; try a one-byte GET
    // before declaring the URL dead.
    curl_status(&["-sSL", "-r", "0-0", "--max-time", "15", url])
}

fn curl_status(args: &[&str]) -> Result<u32> {
    let mut cmd = ProcCommand::new("curl");
    cmd.args(args)
        .args(["-o", "/dev/null", "-w", "%{http_code}"]);
    let out = cmd.output().context("invoke curl")?;
    if !out.status.success() {
        bail!(
            "curl exited with {:?}: {}",
            out.status.code(),
            String::from_utf8_lossy(&out.stderr)
        );
    }
    String::from_utf8_lossy(&out.stdout)
        .trim()
        .parse::<u32>()
        .map_err(|e| anyhow!("parse http_code: {e}"))
}

fn gh_release_assets(repo: &str, tag: &str) -> Result<Vec<String>> {
    let out = ProcCommand::new("gh")
        .args([
            "release",
            "view",
            tag,
            "--repo",
            repo,
            "--json",
            "assets",
            "--jq",
            ".assets[].name",
        ])
        .output()
        .context("invoke gh release view")?;
    if !out.status.success() {
        bail!(
            "gh release view exited with {:?}: {}",
            out.status.code(),
            String::from_utf8_lossy(&out.stderr)
        );
    }
    Ok(String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .collect())
}

fn download_release(manifest: &Manifest, c: &Corpus, force: bool) -> Result<()> {
    let cache = c.cache_path().expect("release has cache_path");
    let extract = c.extract_path();

    let have_good = c.cache_is_valid(&cache);
    let refreshed = force || !have_good;
    if refreshed {
        println!("==> download {} ({})", c.name, cache.display());
        let asset = c.asset.as_deref().expect("validate enforces asset");
        download_file_atomically(
            &c.name,
            &cache,
            c.sha256.as_deref(),
            c.size_bytes,
            |staging| gh_release_download(&manifest.repo, &manifest.release_tag, asset, staging),
        )?;
    } else {
        println!("==> have {} (pins verified)", c.name);
    }
    extract_into_place(
        &cache,
        Archive::Tar,
        &extract,
        c.extraction_layout(),
        c.archive_symlink_policy(),
        refreshed,
    )
}

fn download_http(c: &Corpus, force: bool) -> Result<()> {
    let url = c.url.as_deref().expect("validate enforces url");
    let cache = c.cache_path().expect("http has cache_path");
    let extract = c.extract_path();

    let refreshed = force || !c.cache_is_valid(&cache);
    if refreshed {
        println!("==> download {} ({})", c.name, url);
        download_http_file_atomically(&c.name, &cache, url, c.sha256.as_deref(), c.size_bytes)?;
    } else {
        if c.has_file_pins() {
            println!("==> have {} (pins verified)", c.name);
        } else {
            println!("==> have {} (cached)", c.name);
        }
    }
    if c.archive == Archive::None {
        return Ok(());
    }
    extract_into_place(
        &cache,
        c.archive,
        &extract,
        c.extraction_layout(),
        c.archive_symlink_policy(),
        refreshed,
    )
}

fn download_git(c: &Corpus, force: bool) -> Result<()> {
    let url = c.url.as_deref().expect("validate enforces url");
    if c.requires_git_lfs {
        require_git_lfs(c)?;
    }
    let extract = c.extract_path();
    if extract.exists() {
        if !force && verify_git_checkout(c).is_ok() {
            println!("==> have {} (checkout verified)", c.name);
            return Ok(());
        }
        if !force {
            bail!(
                "{}: existing checkout {} is dirty or not at its manifest pin; pass --force to replace this corpus-owned tree",
                c.name,
                extract.display()
            );
        }
    }
    let depth = c.depth.unwrap_or(1);
    let mut staging = ArchiveStagingDirectory::create_for(&extract)?;
    println!(
        "==> git fetch --depth {} {} -> {}",
        depth,
        url,
        extract.display()
    );
    let status = ProcCommand::new("git")
        .arg("-C")
        .arg(&staging.path)
        .args(["init", "--quiet"])
        .status()
        .context("invoke git init")?;
    if !status.success() {
        bail!("git init exited with {:?}", status.code());
    }
    let status = ProcCommand::new("git")
        .arg("-C")
        .arg(&staging.path)
        .args(["remote", "add", "origin", url])
        .status()
        .context("invoke git remote add")?;
    if !status.success() {
        bail!("git remote add exited with {:?}", status.code());
    }
    let mut fetch = ProcCommand::new("git");
    fetch
        .arg("-C")
        .arg(&staging.path)
        .args(["fetch", "--depth"])
        .arg(depth.to_string())
        .arg("origin");
    if let Some(commit) = &c.commit {
        fetch.arg(commit);
    }
    let status = fetch.status().context("invoke git fetch")?;
    if !status.success() {
        bail!("git fetch exited with {:?}", status.code());
    }
    let status = ProcCommand::new("git")
        .arg("-C")
        .arg(&staging.path)
        .args(["checkout", "--detach", "--quiet", "FETCH_HEAD"])
        .status()
        .context("invoke git checkout")?;
    if !status.success() {
        bail!("git checkout FETCH_HEAD exited with {:?}", status.code());
    }
    if staging.path.join(".gitmodules").is_file() {
        println!("    initializing pinned git submodules");
        let status = ProcCommand::new("git")
            .arg("-C")
            .arg(&staging.path)
            .args(["submodule", "update", "--init", "--recursive", "--depth"])
            .arg(depth.to_string())
            .status()
            .context("invoke git submodule update")?;
        if !status.success() {
            bail!("git submodule update exited with {:?}", status.code());
        }
    }
    if c.requires_git_lfs {
        println!("    fetching and materializing pinned Git LFS objects");
        materialize_git_lfs_recursive(&staging.path, &c.name, 0)?;
    }
    let canonical_staging = fs::canonicalize(&staging.path).with_context(|| {
        format!(
            "canonicalize staged Git checkout {}",
            staging.path.display()
        )
    })?;
    let mut staged_corpus = c.clone();
    staged_corpus.extract_to = canonical_staging.to_string_lossy().into_owned();
    staged_corpus.base_dir = PathBuf::new();
    verify_git_checkout(&staged_corpus)
        .with_context(|| format!("{}: verify staged Git checkout before publication", c.name))?;
    install_staged_path(&staging.path, &extract, extract.exists())?;
    staging.mark_installed();
    verify_git_checkout(c)
}

fn require_git_lfs(corpus: &Corpus) -> Result<()> {
    let output = ProcCommand::new("git-lfs")
        .arg("version")
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .output();
    match output {
        Ok(output) if output.status.success() => Ok(()),
        Ok(output) => bail!(
            "{}: the pinned tree contains actual Git LFS pointer blobs \
             (`requires_git_lfs = true`), but `git-lfs version` failed: {}. \
             Install Git LFS before downloading this corpus",
            corpus.name,
            String::from_utf8_lossy(&output.stderr).trim()
        ),
        Err(error) => bail!(
            "{}: the pinned tree contains actual Git LFS pointer blobs \
             (`requires_git_lfs = true`), but git-lfs is unavailable ({error}). \
             Install Git LFS before downloading this corpus",
            corpus.name
        ),
    }
}

fn materialize_git_lfs_recursive(repository: &Path, label: &str, depth: usize) -> Result<()> {
    if depth > MAX_GIT_SUBMODULE_DEPTH {
        bail!(
            "{label}: Git LFS submodule nesting exceeds {MAX_GIT_SUBMODULE_DEPTH} levels at {}",
            repository.display()
        );
    }
    verified_git_output(
        repository,
        &["lfs", "install", "--local"],
        "lfs install --local",
    )
    .with_context(|| {
        format!(
            "{label}: initialize Git LFS filters in {}",
            repository.display()
        )
    })?;
    verified_git_output(repository, &["lfs", "pull"], "lfs pull").with_context(|| {
        format!(
            "{label}: fetch and materialize Git LFS objects in {}",
            repository.display()
        )
    })?;

    let gitmodules = repository.join(".gitmodules");
    if !gitmodules.is_file() {
        return Ok(());
    }
    for raw_path in gitmodules_values(repository, "path")?.into_values() {
        let relative_path = Path::new(&raw_path);
        if relative_path.as_os_str().is_empty()
            || relative_path.is_absolute()
            || relative_path
                .components()
                .any(|component| !matches!(component, Component::Normal(_)))
        {
            bail!("{label}: unsafe Git LFS submodule path {raw_path:?}");
        }
        let submodule = repository.join(relative_path);
        materialize_git_lfs_recursive(
            &submodule,
            &format!("{label} submodule {raw_path}"),
            depth + 1,
        )?;
    }
    Ok(())
}

fn verify_git_checkout(c: &Corpus) -> Result<()> {
    let extract = c.extract_path();
    let expected_url = c.url.as_deref().expect("validate enforces git url");
    let allowed_unmapped_gitlinks = c
        .allowed_unmapped_gitlinks
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    let has_lfs_pointers = verify_git_repository(
        &extract,
        expected_url,
        c.commit.as_deref(),
        &c.name,
        &allowed_unmapped_gitlinks,
        0,
    )?;
    if has_lfs_pointers != c.requires_git_lfs {
        bail!(
            "{}: manifest `requires_git_lfs = {}` does not match the pinned tree \
             (actual Git LFS pointer blobs: {})",
            c.name,
            c.requires_git_lfs,
            has_lfs_pointers
        );
    }
    Ok(())
}

const MAX_GIT_SUBMODULE_DEPTH: usize = 64;

#[derive(Debug)]
struct GitIndexEntry {
    mode: String,
    object: String,
    path: Vec<u8>,
}

fn verified_git_command(repository: &Path) -> ProcCommand {
    let mut command = ProcCommand::new("git");
    command
        .env("GIT_OPTIONAL_LOCKS", "0")
        .env("GIT_TERMINAL_PROMPT", "0")
        .env_remove("GIT_DIR")
        .env_remove("GIT_WORK_TREE")
        .env_remove("GIT_INDEX_FILE")
        .env_remove("GIT_OBJECT_DIRECTORY")
        .env_remove("GIT_ALTERNATE_OBJECT_DIRECTORIES")
        .env_remove("GIT_COMMON_DIR")
        .env_remove("GIT_CONFIG_COUNT")
        .args([
            "-c",
            "core.fsmonitor=false",
            "-c",
            "core.untrackedCache=false",
            "-C",
        ])
        .arg(repository);
    command
}

fn verified_git_output(repository: &Path, args: &[&str], operation: &str) -> Result<Vec<u8>> {
    let output = verified_git_command(repository)
        .args(args)
        .output()
        .with_context(|| format!("invoke git {operation} in {}", repository.display()))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        bail!(
            "git {operation} in {} exited with {:?}: {}",
            repository.display(),
            output.status.code(),
            stderr.trim()
        );
    }
    Ok(output.stdout)
}

fn split_bytes_once(bytes: &[u8], separator: u8) -> Option<(&[u8], &[u8])> {
    let offset = bytes.iter().position(|byte| *byte == separator)?;
    Some((&bytes[..offset], &bytes[offset + 1..]))
}

fn verify_git_repository(
    repository: &Path,
    expected_url: &str,
    expected_commit: Option<&str>,
    label: &str,
    allowed_unmapped_gitlinks: &BTreeSet<String>,
    depth: usize,
) -> Result<bool> {
    if depth > MAX_GIT_SUBMODULE_DEPTH {
        bail!(
            "{label}: git submodule nesting exceeds {MAX_GIT_SUBMODULE_DEPTH} levels at {}",
            repository.display()
        );
    }

    let metadata = fs::symlink_metadata(repository)
        .with_context(|| format!("{label}: missing git checkout {}", repository.display()))?;
    if !metadata.file_type().is_dir() || metadata.file_type().is_symlink() {
        bail!(
            "{label}: git checkout {} must be a non-symlink directory",
            repository.display()
        );
    }
    let canonical_repository = fs::canonicalize(repository)
        .with_context(|| format!("canonicalize git checkout {}", repository.display()))?;
    let absolute_repository = if repository.is_absolute() {
        repository.to_path_buf()
    } else {
        std::env::current_dir()
            .context("resolve current directory for git verification")?
            .join(repository)
    };
    if absolute_repository != canonical_repository {
        bail!(
            "{label}: git checkout {} must use its canonical non-symlink path {}",
            repository.display(),
            canonical_repository.display()
        );
    }
    let top_level = verified_git_output(
        repository,
        &["rev-parse", "--show-toplevel"],
        "rev-parse --show-toplevel",
    )?;
    let top_level = String::from_utf8(top_level)
        .context("git rev-parse --show-toplevel returned a non-UTF-8 path")?;
    let canonical_top_level = fs::canonicalize(top_level.trim()).with_context(|| {
        format!(
            "canonicalize git repository root reported for {}",
            repository.display()
        )
    })?;
    if canonical_top_level != canonical_repository {
        bail!(
            "{label}: {} is not the exact git repository root (root is {})",
            repository.display(),
            canonical_top_level.display()
        );
    }

    verify_git_repository_config(repository, label)?;
    verify_git_origin(repository, expected_url, label)?;

    let head = verified_git_output(repository, &["rev-parse", "HEAD"], "rev-parse HEAD")?;
    let head = String::from_utf8(head)
        .context("git rev-parse HEAD returned non-UTF-8 output")?
        .trim()
        .to_string();
    if let Some(expected) = expected_commit {
        if head != expected {
            bail!(
                "{label}: git checkout {} is at {}, expected {}",
                repository.display(),
                head,
                expected
            );
        }
    }

    let unmerged = verified_git_output(
        repository,
        &["ls-files", "--unmerged", "-z"],
        "ls-files --unmerged",
    )?;
    if !unmerged.is_empty() {
        bail!(
            "{label}: git checkout {} has unmerged index entries",
            repository.display()
        );
    }
    let index = verified_git_output(
        repository,
        &["ls-files", "--stage", "-v", "-z"],
        "ls-files --stage -v",
    )?;
    let index = parse_verified_git_index(repository, &index, label)?;

    verified_git_output(
        repository,
        &["fsck", "--full", "--no-dangling", "--no-reflogs", "HEAD"],
        "fsck",
    )
    .with_context(|| {
        format!(
            "{label}: current git tree in {} has missing or corrupt objects",
            repository.display()
        )
    })?;
    let has_lfs_pointers = verify_git_lfs_materialization(repository, &index, label)?;

    let status = verified_git_output(
        repository,
        &[
            "status",
            "--porcelain=v1",
            "-z",
            "--untracked-files=all",
            "--ignore-submodules=none",
        ],
        "status",
    )?;
    if !status.is_empty() {
        bail!(
            "{label}: git checkout {} has local modifications or untracked files",
            repository.display()
        );
    }
    let ignored = verified_git_output(
        repository,
        &[
            "ls-files",
            "--others",
            "--ignored",
            "--exclude-standard",
            "-z",
        ],
        "ls-files --others --ignored",
    )?;
    if !ignored.is_empty() {
        bail!(
            "{label}: git checkout {} contains ignored extra files",
            repository.display()
        );
    }

    let submodules_have_lfs_pointers = verify_git_submodules(
        repository,
        &canonical_repository,
        &index,
        label,
        allowed_unmapped_gitlinks,
        depth,
    )?;
    Ok(has_lfs_pointers || submodules_have_lfs_pointers)
}

fn verify_git_repository_config(repository: &Path, label: &str) -> Result<()> {
    let output = verified_git_output(
        repository,
        &["config", "--local", "--null", "--list"],
        "config --local --list",
    )?;
    for record in output.split(|byte| *byte == b'\0') {
        if record.is_empty() {
            continue;
        }
        let (key, value) = split_bytes_once(record, b'\n').unwrap_or((record, &[]));
        let key = String::from_utf8_lossy(key).to_ascii_lowercase();
        let value = String::from_utf8_lossy(value);
        if key == "extensions.partialclone"
            || (key.starts_with("remote.") && key.ends_with(".partialclonefilter"))
            || (key.starts_with("remote.")
                && key.ends_with(".promisor")
                && matches!(
                    value.trim().to_ascii_lowercase().as_str(),
                    "true" | "yes" | "on" | "1"
                ))
        {
            bail!(
                "{label}: git checkout {} uses unsupported partial/promisor configuration ({key})",
                repository.display()
            );
        }
    }

    let sparse = verified_git_command(repository)
        .args(["config", "--local", "--bool", "core.sparseCheckout"])
        .output()
        .with_context(|| {
            format!(
                "invoke git config core.sparseCheckout in {}",
                repository.display()
            )
        })?;
    match sparse.status.code() {
        Some(0) if String::from_utf8_lossy(&sparse.stdout).trim() == "true" => bail!(
            "{label}: git checkout {} uses unsupported sparse checkout",
            repository.display()
        ),
        Some(0) | Some(1) => {}
        _ => bail!(
            "git config core.sparseCheckout in {} exited with {:?}",
            repository.display(),
            sparse.status.code()
        ),
    }
    Ok(())
}

fn verify_git_origin(repository: &Path, expected_url: &str, label: &str) -> Result<()> {
    let output = verified_git_command(repository)
        .args([
            "config",
            "--local",
            "--no-includes",
            "--null",
            "--get-all",
            "remote.origin.url",
        ])
        .output()
        .with_context(|| {
            format!(
                "invoke git config remote.origin.url in {}",
                repository.display()
            )
        })?;
    if !output.status.success() {
        bail!(
            "{label}: git checkout {} has no local origin URL",
            repository.display()
        );
    }
    let urls = output
        .stdout
        .split(|byte| *byte == b'\0')
        .filter(|url| !url.is_empty())
        .collect::<Vec<_>>();
    if urls.len() != 1 || urls[0] != expected_url.as_bytes() {
        let actual = urls
            .iter()
            .map(|url| String::from_utf8_lossy(url))
            .collect::<Vec<_>>()
            .join(", ");
        bail!(
            "{label}: git checkout {} has origin [{}], expected {}",
            repository.display(),
            actual,
            expected_url
        );
    }
    Ok(())
}

fn parse_verified_git_index(
    repository: &Path,
    output: &[u8],
    label: &str,
) -> Result<Vec<GitIndexEntry>> {
    let mut entries = Vec::new();
    for record in output.split(|byte| *byte == b'\0') {
        if record.is_empty() {
            continue;
        }
        if !record.starts_with(b"H ") {
            let tag = record.first().copied().unwrap_or(b'?') as char;
            bail!(
                "{label}: git checkout {} has unsupported index state {tag:?} \
                 (sparse/skip-worktree/assume-unchanged entries are forbidden)",
                repository.display()
            );
        }
        let (header, path) = split_bytes_once(record, b'\t')
            .ok_or_else(|| anyhow!("malformed git ls-files output in {}", repository.display()))?;
        let header = std::str::from_utf8(&header[2..])
            .context("git ls-files returned a non-UTF-8 index header")?;
        let mut fields = header.split_ascii_whitespace();
        let mode = fields
            .next()
            .ok_or_else(|| anyhow!("git ls-files omitted an index mode"))?;
        let object = fields
            .next()
            .ok_or_else(|| anyhow!("git ls-files omitted an object ID"))?;
        let stage = fields
            .next()
            .ok_or_else(|| anyhow!("git ls-files omitted an index stage"))?;
        if stage != "0" || fields.next().is_some() {
            bail!(
                "{label}: git checkout {} has an unsupported index stage",
                repository.display()
            );
        }
        entries.push(GitIndexEntry {
            mode: mode.to_string(),
            object: object.to_string(),
            path: path.to_vec(),
        });
    }
    Ok(entries)
}

fn verify_git_lfs_materialization(
    repository: &Path,
    index: &[GitIndexEntry],
    label: &str,
) -> Result<bool> {
    // Attribute pathspec matching asks Git to emit only LFS-attributed index
    // paths. Unlike `check-attr --stdin`, this has no bidirectional pipe and
    // therefore cannot deadlock when a corpus has a very large index.
    let attributed = verified_git_output(
        repository,
        &["ls-files", "-z", ":(attr:filter=lfs)"],
        "ls-files with Git LFS attribute pathspec",
    )?;
    let index_by_path = index
        .iter()
        .enumerate()
        .map(|(offset, entry)| (entry.path.as_slice(), offset))
        .collect::<BTreeMap<_, _>>();
    let mut pointer_objects = BTreeMap::<String, bool>::new();
    let mut lfs_pointer_paths = Vec::new();
    for raw_path in attributed.split(|byte| *byte == b'\0') {
        if raw_path.is_empty() {
            continue;
        }
        let offset = index_by_path.get(raw_path).ok_or_else(|| {
            anyhow!(
                "Git LFS attribute path is absent from index in {}",
                repository.display()
            )
        })?;
        let entry = &index[*offset];
        let is_pointer = match pointer_objects.get(&entry.object) {
            Some(is_pointer) => *is_pointer,
            None => {
                let is_pointer = git_object_is_lfs_pointer(repository, &entry.object)?;
                pointer_objects.insert(entry.object.clone(), is_pointer);
                is_pointer
            }
        };
        if is_pointer {
            lfs_pointer_paths.push(raw_path);
        }
    }
    if lfs_pointer_paths.is_empty() {
        return Ok(false);
    }

    for raw_path in &lfs_pointer_paths {
        let path = std::str::from_utf8(raw_path).context("Git LFS path is not UTF-8")?;
        let path = repository.join(path);
        let metadata = fs::symlink_metadata(&path)
            .with_context(|| format!("inspect Git LFS path {}", path.display()))?;
        if !metadata.file_type().is_file() || metadata.file_type().is_symlink() {
            bail!(
                "{label}: Git LFS path {} is not a materialized regular file",
                path.display()
            );
        }
        let mut contents = Vec::new();
        fs::File::open(&path)
            .with_context(|| format!("open Git LFS path {}", path.display()))?
            .take(1025)
            .read_to_end(&mut contents)?;
        if is_git_lfs_pointer(&contents) {
            bail!(
                "{label}: Git LFS path {} is only an unresolved pointer",
                path.display()
            );
        }
    }

    verified_git_output(repository, &["lfs", "fsck", "HEAD"], "lfs fsck HEAD").with_context(
        || {
            format!(
                "{label}: Git LFS objects for {} could not be verified",
                repository.display()
            )
        },
    )?;
    Ok(true)
}

fn git_object_is_lfs_pointer(repository: &Path, object: &str) -> Result<bool> {
    let size = verified_git_output(
        repository,
        &["cat-file", "-s", object],
        "cat-file object size",
    )?;
    let size = std::str::from_utf8(&size)
        .context("git cat-file returned a non-UTF-8 object size")?
        .trim()
        .parse::<u64>()
        .context("git cat-file returned an invalid object size")?;
    if size > 1024 {
        return Ok(false);
    }
    let contents = verified_git_output(
        repository,
        &["cat-file", "blob", object],
        "cat-file pointer candidate",
    )?;
    Ok(is_git_lfs_pointer(&contents))
}

fn is_git_lfs_pointer(contents: &[u8]) -> bool {
    if contents.len() > 1024 {
        return false;
    }
    let Ok(contents) = std::str::from_utf8(contents) else {
        return false;
    };
    let mut lines = contents.lines();
    if lines.next() != Some("version https://git-lfs.github.com/spec/v1") {
        return false;
    }
    let has_oid = lines.clone().any(|line| {
        line.strip_prefix("oid sha256:")
            .is_some_and(|oid| oid.len() == 64 && oid.bytes().all(|byte| byte.is_ascii_hexdigit()))
    });
    let has_size = lines.any(|line| {
        line.strip_prefix("size ")
            .is_some_and(|size| !size.is_empty() && size.bytes().all(|byte| byte.is_ascii_digit()))
    });
    has_oid && has_size
}

fn verify_git_submodules(
    repository: &Path,
    canonical_repository: &Path,
    index: &[GitIndexEntry],
    label: &str,
    allowed_unmapped_gitlinks: &BTreeSet<String>,
    depth: usize,
) -> Result<bool> {
    let mut gitlinks = BTreeMap::new();
    for entry in index {
        if entry.mode != "160000" {
            continue;
        }
        let path = std::str::from_utf8(&entry.path)
            .context("git submodule path is not UTF-8")?
            .to_string();
        if gitlinks
            .insert(path.clone(), entry.object.clone())
            .is_some()
        {
            bail!("{label}: duplicate gitlink path {path:?}");
        }
    }

    let gitmodules = repository.join(".gitmodules");
    let gitmodules_metadata = match fs::symlink_metadata(&gitmodules) {
        Ok(metadata) => Some(metadata),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
        Err(error) => return Err(error).context("inspect .gitmodules"),
    };
    let (paths, urls) = if let Some(metadata) = gitmodules_metadata {
        if !metadata.file_type().is_file() {
            bail!(
                "{label}: {} must be a regular .gitmodules file",
                gitmodules.display()
            );
        }
        (
            gitmodules_values(repository, "path")?,
            gitmodules_values(repository, "url")?,
        )
    } else {
        (BTreeMap::new(), BTreeMap::new())
    };
    if paths.keys().ne(urls.keys()) {
        bail!(
            "{label}: every .gitmodules entry in {} must have exactly one path and URL",
            repository.display()
        );
    }
    let mut declared_paths = BTreeSet::new();
    for raw_path in paths.values() {
        if !declared_paths.insert(raw_path.clone()) {
            bail!("{label}: duplicate git submodule path {raw_path:?}");
        }
    }
    let unmapped_gitlinks = gitlinks
        .keys()
        .filter(|path| !declared_paths.contains(*path))
        .cloned()
        .collect::<BTreeSet<_>>();
    let missing_gitlinks = declared_paths
        .iter()
        .filter(|path| !gitlinks.contains_key(*path))
        .cloned()
        .collect::<Vec<_>>();
    if unmapped_gitlinks != *allowed_unmapped_gitlinks || !missing_gitlinks.is_empty() {
        bail!(
            "{label}: .gitmodules declarations and allowed exceptions do not exactly match \
             gitlinks in {} (actual unmapped mode-160000 entries: [{}]; \
             allowed unmapped entries: [{}]; mappings without gitlinks: [{}])",
            repository.display(),
            unmapped_gitlinks
                .iter()
                .cloned()
                .collect::<Vec<_>>()
                .join(", "),
            allowed_unmapped_gitlinks
                .iter()
                .cloned()
                .collect::<Vec<_>>()
                .join(", "),
            missing_gitlinks.join(", "),
        );
    }

    let mut has_lfs_pointers = false;
    for (name, raw_path) in paths {
        let raw_url = &urls[&name];
        let relative_path = Path::new(&raw_path);
        if relative_path.as_os_str().is_empty()
            || relative_path.is_absolute()
            || relative_path
                .components()
                .any(|component| !matches!(component, Component::Normal(_)))
        {
            bail!("{label}: unsafe git submodule path {raw_path:?}");
        }
        let expected_object = gitlinks.get(&raw_path).ok_or_else(|| {
            anyhow!(
                "{label}: .gitmodules path {raw_path:?} has no matching gitlink in {}",
                repository.display()
            )
        })?;
        let submodule = repository.join(relative_path);
        let canonical_submodule = fs::canonicalize(&submodule)
            .with_context(|| format!("{label}: missing git submodule {}", submodule.display()))?;
        if !canonical_submodule.starts_with(canonical_repository)
            || canonical_submodule == canonical_repository
        {
            bail!(
                "{label}: git submodule {} resolves outside its parent repository",
                submodule.display()
            );
        }
        let no_allowed_unmapped_gitlinks = BTreeSet::new();
        has_lfs_pointers |= verify_git_repository(
            &submodule,
            raw_url,
            Some(expected_object),
            &format!("{label} submodule {raw_path}"),
            &no_allowed_unmapped_gitlinks,
            depth + 1,
        )?;
    }
    Ok(has_lfs_pointers)
}

fn gitmodules_values(repository: &Path, field: &str) -> Result<BTreeMap<String, String>> {
    let expression = format!(r"^submodule\..*\.{field}$");
    let output = verified_git_command(repository)
        .args([
            "config",
            "--file",
            ".gitmodules",
            "--no-includes",
            "--null",
            "--get-regexp",
            &expression,
        ])
        .output()
        .with_context(|| {
            format!(
                "parse {field} entries from {}",
                repository.join(".gitmodules").display()
            )
        })?;
    if !output.status.success() && output.status.code() != Some(1) {
        bail!(
            "git config could not parse {}: {}",
            repository.join(".gitmodules").display(),
            String::from_utf8_lossy(&output.stderr).trim()
        );
    }
    let mut values = BTreeMap::new();
    for record in output.stdout.split(|byte| *byte == b'\0') {
        if record.is_empty() {
            continue;
        }
        let (key, value) = split_bytes_once(record, b'\n').ok_or_else(|| {
            anyhow!(
                "malformed git config output for {}",
                repository.join(".gitmodules").display()
            )
        })?;
        let key = std::str::from_utf8(key).context(".gitmodules key is not UTF-8")?;
        let value = std::str::from_utf8(value).context(".gitmodules value is not UTF-8")?;
        let suffix = format!(".{field}");
        let name = key
            .strip_prefix("submodule.")
            .and_then(|key| key.strip_suffix(&suffix))
            .filter(|name| !name.is_empty())
            .ok_or_else(|| anyhow!("unexpected .gitmodules key {key:?}"))?;
        if value.contains('\n') || value.contains('\0') {
            bail!("unsupported newline in .gitmodules {field} for {name:?}");
        }
        if values.insert(name.to_string(), value.to_string()).is_some() {
            bail!("duplicate .gitmodules {field} for {name:?}");
        }
    }
    Ok(values)
}

fn download_gbd(c: &Corpus, force: bool) -> Result<()> {
    let rows = c.gbd_rows()?;
    if rows.is_empty() {
        bail!("{}: gbd manifest has no rows", c.name);
    }
    let mut fetched = 0usize;
    let mut reused = 0usize;
    let mut skipped = 0usize;
    let mut pinned_objects = BTreeMap::<String, (PathBuf, Option<u64>, Option<String>)>::new();
    for row in &rows {
        let raw = row.raw_path();
        let decompressed = row.decompressed_path();
        if let Some((_, size, sha256)) = pinned_objects.get(&row.hash) {
            if *size != row.expected_size || *sha256 != row.expected_sha256 {
                bail!(
                    "{}: GBD object {} repeats with conflicting response pins",
                    c.name,
                    row.hash
                );
            }
        }
        if !force && row.verify().is_ok() {
            if row.has_complete_pins() {
                if let Some((existing, _, _)) = pinned_objects.get(&row.hash) {
                    if gbd_artifacts_alias(existing, &raw)? {
                        publish_independent_gbd_duplicate(c, row, existing, &raw)?;
                        reused += 1;
                    } else {
                        skipped += 1;
                    }
                    continue;
                }
                pinned_objects.insert(
                    row.hash.clone(),
                    (raw, row.expected_size, row.expected_sha256.clone()),
                );
            }
            skipped += 1;
            continue;
        }
        if row.has_complete_pins() {
            if let Some((existing, _, _)) = pinned_objects.get(&row.hash) {
                publish_independent_gbd_duplicate(c, row, existing, &raw)?;
                reused += 1;
                continue;
            }
        }
        let url = format!("{}/{}", GBD_FILE_BASE, row.hash);
        println!("==> {} {} -> {}", c.name, url, raw.display());
        if let Some(parent) = raw.parent() {
            fs::create_dir_all(parent).with_context(|| format!("mkdir -p {}", parent.display()))?;
        }
        if row.expected_size.is_some() || row.expected_sha256.is_some() {
            download_http_file_atomically(
                &c.name,
                &raw,
                &url,
                row.expected_sha256.as_deref(),
                row.expected_size,
            )?;
        } else {
            http_get(&url, &raw)?;
        }
        if row.has_complete_pins() {
            pinned_objects.insert(
                row.hash.clone(),
                (raw, row.expected_size, row.expected_sha256.clone()),
            );
            fetched += 1;
            continue;
        }
        // The unit-test fixtures read the plain `.cnf`, so when `local_path`
        // carries a `.xz` suffix we materialize the decompressed sibling. Note
        // GBD serves the payload with `Content-Encoding`, which curl may have
        // already transparently decoded — so the bytes on disk may be plain CNF
        // even though the URL/filename say `.xz`. Detect the actual bytes:
        //   - real xz on disk  -> `xz -dc` into the sibling;
        //   - already plain     -> copy verbatim into the sibling.
        if raw != decompressed {
            if is_xz(&raw)? {
                xz_decompress(&raw, &decompressed)
                    .with_context(|| format!("{}: decompress {}", c.name, raw.display()))?;
            } else {
                fs::copy(&raw, &decompressed).with_context(|| {
                    format!(
                        "{}: copy {} -> {}",
                        c.name,
                        raw.display(),
                        decompressed.display()
                    )
                })?;
            }
        }
        fetched += 1;
    }
    println!(
        "==> {}: {} fetched, {} duplicate rows reused, {} already present ({} total)",
        c.name,
        fetched,
        reused,
        skipped,
        rows.len()
    );
    Ok(())
}

fn publish_independent_gbd_duplicate(
    corpus: &Corpus,
    row: &GbdRow,
    existing: &Path,
    destination: &Path,
) -> Result<()> {
    download_file_atomically(
        &format!("{} duplicate GBD response", corpus.name),
        destination,
        row.expected_sha256.as_deref(),
        row.expected_size,
        |staging| {
            fs::copy(existing, staging).map(|_| ()).with_context(|| {
                format!(
                    "copy duplicate GBD response {} into private staging",
                    existing.display()
                )
            })
        },
    )?;
    row.verify()
        .with_context(|| format!("verify reused GBD response {}", destination.display()))
}

fn gbd_artifacts_alias(left: &Path, right: &Path) -> Result<bool> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;

        let left = fs::metadata(left)
            .with_context(|| format!("stat duplicate GBD source {}", left.display()))?;
        let right = fs::metadata(right)
            .with_context(|| format!("stat duplicate GBD destination {}", right.display()))?;
        Ok(left.dev() == right.dev() && left.ino() == right.ino())
    }
    #[cfg(not(unix))]
    {
        let _ = (left, right);
        // Rust's portable Metadata API has no stable file identity. Recopying
        // is conservative and guarantees distinct scored rows after publish.
        Ok(true)
    }
}

fn download_uri_list(c: &Corpus, force: bool) -> Result<()> {
    let rows = c.uri_rows()?;
    let mut fetched = 0usize;
    let mut skipped = 0usize;
    for row in &rows {
        let downloaded = row.downloaded_path(c);
        if !force && row.verify(c).is_ok() {
            skipped += 1;
            continue;
        }
        println!("==> {} {} -> {}", c.name, row.url, downloaded.display());
        download_http_file_atomically(
            &c.name,
            &downloaded,
            &row.url,
            row.expected_sha256.as_deref(),
            row.expected_size,
        )?;
        fetched += 1;
    }
    println!(
        "==> {}: {} fetched, {} already present ({} total)",
        c.name,
        fetched,
        skipped,
        rows.len()
    );
    Ok(())
}

/// Magic bytes that prefix an xz stream: FD 37 7A 58 5A 00.
const XZ_MAGIC: [u8; 6] = [0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00];

/// Does the file start with the xz magic bytes?
fn is_xz(path: &Path) -> Result<bool> {
    let mut file = fs::File::open(path).with_context(|| format!("open {}", path.display()))?;
    let mut head = [0u8; 6];
    let mut filled = 0;
    while filled < head.len() {
        let n = file
            .read(&mut head[filled..])
            .with_context(|| format!("read {}", path.display()))?;
        if n == 0 {
            break;
        }
        filled += n;
    }
    Ok(filled == head.len() && head == XZ_MAGIC)
}

/// Decompress an xz file by shelling out to `xz -dc` (matches how this module
/// already shells out to `zstd`/`tar`/`unzip` for the other formats).
fn xz_decompress(src: &Path, dst: &Path) -> Result<()> {
    if !which("xz") {
        bail!("install xz (brew install xz) to decompress GBD downloads");
    }
    let tmp = dst.with_extension("xz-tmp");
    let outfile = fs::File::create(&tmp).with_context(|| format!("create {}", tmp.display()))?;
    let status = ProcCommand::new("xz")
        .args(["-dc"])
        .arg(src)
        .stdout(Stdio::from(outfile))
        .status()
        .context("invoke xz -dc")?;
    if !status.success() {
        let _ = fs::remove_file(&tmp);
        bail!("xz -dc exited with {:?}", status.code());
    }
    fs::rename(&tmp, dst).with_context(|| format!("mv {} -> {}", tmp.display(), dst.display()))?;
    Ok(())
}

fn extract_into_place(
    archive_path: &Path,
    archive: Archive,
    extract_to: &Path,
    layout: ExtractionLayout,
    symlink_policy: ArchiveSymlinkPolicy,
    force: bool,
) -> Result<()> {
    if archive == Archive::None {
        bail!("extract_into_place called with Archive::None");
    }
    extract_transactionally(extract_to, layout, force, |staging| match archive {
        Archive::Tar => extract_tarball(archive_path, staging, symlink_policy),
        Archive::Zip => extract_zip(archive_path, staging, symlink_policy),
        Archive::None => unreachable!("rejected above"),
    })
}

/// Verify the installed tree against a fresh extraction of its already-pinned
/// archive. This deliberately uses private sibling staging rather than trusting
/// timestamps or a marker file: a valid cache cannot mask a missing, modified,
/// or injected benchmark file.
fn verify_materialized_archive(corpus: &Corpus, archive_path: &Path) -> Result<()> {
    if corpus.archive == Archive::None {
        return Ok(());
    }

    let installed = corpus.extract_path();
    let installed_metadata = fs::symlink_metadata(&installed)
        .with_context(|| format!("inspect materialized tree {}", installed.display()))?;
    if !installed_metadata.file_type().is_dir() {
        bail!(
            "materialized tree {} must be a real directory",
            installed.display()
        );
    }

    let staging = ArchiveStagingDirectory::create_for(&installed)?;
    match corpus.archive {
        Archive::Tar => {
            extract_tarball(archive_path, &staging.path, corpus.archive_symlink_policy())
        }
        Archive::Zip => extract_zip(archive_path, &staging.path, corpus.archive_symlink_policy()),
        Archive::None => unreachable!("returned above"),
    }
    .with_context(|| {
        format!(
            "extract {} for integrity verification",
            archive_path.display()
        )
    })?;

    let expected = match corpus.extraction_layout() {
        ExtractionLayout::ArchiveRootInParent => {
            validate_single_archive_root(&staging.path, &installed)?
        }
        ExtractionLayout::WrappedDirectory => {
            validate_nonempty_archive(&staging.path)?;
            staging.path.clone()
        }
    };
    compare_materialized_trees(&expected, &installed).with_context(|| {
        format!(
            "materialized tree {} differs from verified archive {}",
            installed.display(),
            archive_path.display()
        )
    })
}

/// Compare two extracted trees exactly without following links. Archived
/// symlinks are compared by their link-target bytes; an installed symlink is
/// accepted only when the pinned archive has the same symlink at that path.
/// Files are read sequentially with a fixed-size buffer, and only one
/// directory's entry names are retained at a time.
fn compare_materialized_trees(expected: &Path, installed: &Path) -> Result<()> {
    let mut pending = vec![(
        expected.to_path_buf(),
        installed.to_path_buf(),
        PathBuf::new(),
    )];
    while let Some((expected_path, installed_path, relative)) = pending.pop() {
        let expected_metadata = fs::symlink_metadata(&expected_path)
            .with_context(|| format!("inspect archive entry {}", expected_path.display()))?;
        let installed_metadata = fs::symlink_metadata(&installed_path).with_context(|| {
            format!(
                "inspect materialized entry {}",
                materialized_entry_label(&relative)
            )
        })?;
        let expected_type = expected_metadata.file_type();
        let installed_type = installed_metadata.file_type();

        if expected_type.is_symlink() {
            if !installed_type.is_symlink() {
                bail!(
                    "materialized entry {} is not the symlink recorded by the archive",
                    materialized_entry_label(&relative)
                );
            }
            let expected_target = fs::read_link(&expected_path).with_context(|| {
                format!(
                    "read archived symlink {}",
                    materialized_entry_label(&relative)
                )
            })?;
            let installed_target = fs::read_link(&installed_path).with_context(|| {
                format!(
                    "read materialized symlink {}",
                    materialized_entry_label(&relative)
                )
            })?;
            if expected_target != installed_target {
                bail!(
                    "materialized symlink {} targets {}, expected {}",
                    materialized_entry_label(&relative),
                    installed_target.display(),
                    expected_target.display()
                );
            }
            continue;
        }
        if installed_type.is_symlink() {
            bail!(
                "materialized tree contains an unrecorded symlink at {}",
                materialized_entry_label(&relative)
            );
        }

        if expected_type.is_dir() {
            if !installed_type.is_dir() {
                bail!(
                    "materialized entry {} is not a directory",
                    materialized_entry_label(&relative)
                );
            }
            let expected_entries = real_directory_entries(&expected_path)?;
            let installed_entries = real_directory_entries(&installed_path)?;
            for name in expected_entries.keys() {
                if !installed_entries.contains_key(name) {
                    bail!(
                        "materialized tree is missing {}",
                        materialized_entry_label(&relative.join(name))
                    );
                }
            }
            for name in installed_entries.keys() {
                if !expected_entries.contains_key(name) {
                    bail!(
                        "materialized tree has extra entry {}",
                        materialized_entry_label(&relative.join(name))
                    );
                }
            }
            for (name, expected_child) in expected_entries {
                let installed_child = installed_entries
                    .get(&name)
                    .expect("entry sets were checked above");
                pending.push((expected_child, installed_child.clone(), relative.join(name)));
            }
        } else if expected_type.is_file() {
            if !installed_type.is_file() {
                bail!(
                    "materialized entry {} is not a regular file",
                    materialized_entry_label(&relative)
                );
            }
            compare_regular_files(
                &expected_path,
                &installed_path,
                &relative,
                expected_metadata.len(),
                installed_metadata.len(),
            )?;
        } else {
            bail!(
                "archive contains unsupported special file at {}",
                materialized_entry_label(&relative)
            );
        }
    }
    Ok(())
}

fn real_directory_entries(path: &Path) -> Result<BTreeMap<std::ffi::OsString, PathBuf>> {
    let mut entries = BTreeMap::new();
    for entry in fs::read_dir(path).with_context(|| format!("read directory {}", path.display()))? {
        let entry = entry.with_context(|| format!("read entry in {}", path.display()))?;
        entries.insert(entry.file_name(), entry.path());
    }
    Ok(entries)
}

fn compare_regular_files(
    expected: &Path,
    installed: &Path,
    relative: &Path,
    expected_len: u64,
    installed_len: u64,
) -> Result<()> {
    if expected_len != installed_len {
        bail!(
            "materialized file {} has size {}, expected {}",
            materialized_entry_label(relative),
            installed_len,
            expected_len
        );
    }
    let mut expected_file =
        fs::File::open(expected).with_context(|| format!("open {}", expected.display()))?;
    let mut installed_file =
        fs::File::open(installed).with_context(|| format!("open {}", installed.display()))?;
    let mut expected_buf = vec![0_u8; 64 * 1024];
    let mut installed_buf = vec![0_u8; 64 * 1024];
    let mut remaining = expected_len;
    while remaining != 0 {
        let amount = usize::try_from(remaining.min(expected_buf.len() as u64))
            .expect("buffer-sized read fits usize");
        expected_file
            .read_exact(&mut expected_buf[..amount])
            .with_context(|| format!("read {}", expected.display()))?;
        installed_file
            .read_exact(&mut installed_buf[..amount])
            .with_context(|| format!("read {}", installed.display()))?;
        if expected_buf[..amount] != installed_buf[..amount] {
            bail!(
                "materialized file {} has different bytes",
                materialized_entry_label(relative)
            );
        }
        remaining -= amount as u64;
    }
    Ok(())
}

fn materialized_entry_label(relative: &Path) -> String {
    if relative.as_os_str().is_empty() {
        ".".to_string()
    } else {
        relative.display().to_string()
    }
}

fn extract_transactionally(
    extract_to: &Path,
    layout: ExtractionLayout,
    force: bool,
    extract: impl FnOnce(&Path) -> Result<()>,
) -> Result<()> {
    if path_is_present(extract_to)? && !force {
        println!("    already extracted: {}", extract_to.display());
        return Ok(());
    }

    let mut staging = ArchiveStagingDirectory::create_for(extract_to)?;
    println!("    extracting -> {}", extract_to.display());
    extract(&staging.path)?;

    match layout {
        ExtractionLayout::ArchiveRootInParent => {
            let root = validate_single_archive_root(&staging.path, extract_to)?;
            install_staged_path(&root, extract_to, force)
        }
        ExtractionLayout::WrappedDirectory => {
            validate_nonempty_archive(&staging.path)?;
            install_staged_path(&staging.path, extract_to, force)?;
            staging.mark_installed();
            Ok(())
        }
    }
}

fn validate_single_archive_root(staging: &Path, extract_to: &Path) -> Result<PathBuf> {
    let expected = extract_to
        .file_name()
        .ok_or_else(|| anyhow!("extract_to {} has no basename", extract_to.display()))?;
    let mut entries = fs::read_dir(staging)
        .with_context(|| format!("read extracted archive roots in {}", staging.display()))?;
    let Some(entry) = entries.next() else {
        bail!(
            "archive is empty; expected one root named {}",
            expected.display()
        );
    };
    let entry = entry.with_context(|| format!("read archive root in {}", staging.display()))?;
    if entries.next().is_some() {
        bail!(
            "archive must contain exactly one top-level root named {}",
            expected.display()
        );
    }
    if entry.file_name() != expected {
        bail!(
            "archive root {} does not match extract_to basename {}",
            entry.file_name().display(),
            expected.display()
        );
    }
    let metadata = fs::symlink_metadata(entry.path())
        .with_context(|| format!("inspect extracted archive root {}", entry.path().display()))?;
    if !metadata.file_type().is_dir() {
        bail!(
            "archive root {} must be a real directory",
            entry.path().display()
        );
    }
    Ok(entry.path())
}

fn validate_nonempty_archive(staging: &Path) -> Result<()> {
    let mut entries = fs::read_dir(staging)
        .with_context(|| format!("read extracted archive roots in {}", staging.display()))?;
    match entries.next() {
        Some(entry) => {
            entry.with_context(|| format!("read archive root in {}", staging.display()))?;
            Ok(())
        }
        None => bail!("archive is empty"),
    }
}

const ARCHIVE_STAGING_ATTEMPTS: u64 = 128;
static ARCHIVE_STAGING_NONCE: AtomicU64 = AtomicU64::new(0);

struct ArchiveStagingDirectory {
    path: PathBuf,
    armed: bool,
}

impl ArchiveStagingDirectory {
    fn create_for(destination: &Path) -> Result<Self> {
        let parent = staging_parent(destination)?;
        fs::create_dir_all(parent).with_context(|| format!("mkdir -p {}", parent.display()))?;
        let first = ARCHIVE_STAGING_NONCE.fetch_add(ARCHIVE_STAGING_ATTEMPTS, Ordering::Relaxed);
        for offset in 0..ARCHIVE_STAGING_ATTEMPTS {
            let path = sibling_work_path(parent, "stage", first.wrapping_add(offset));
            let mut builder = fs::DirBuilder::new();
            #[cfg(unix)]
            {
                use std::os::unix::fs::DirBuilderExt as _;
                builder.mode(0o700);
            }
            match builder.create(&path) {
                Ok(()) => return Ok(Self { path, armed: true }),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
                Err(error) => {
                    return Err(error).with_context(|| {
                        format!("create archive staging directory {}", path.display())
                    });
                }
            }
        }
        bail!(
            "could not reserve an archive staging directory in {} after {} attempts",
            parent.display(),
            ARCHIVE_STAGING_ATTEMPTS
        )
    }

    fn mark_installed(&mut self) {
        self.armed = false;
    }
}

impl Drop for ArchiveStagingDirectory {
    fn drop(&mut self) {
        if self.armed {
            let _ = remove_path_if_present(&self.path);
        }
    }
}

struct DownloadStagingFile {
    path: PathBuf,
    armed: bool,
}

impl DownloadStagingFile {
    fn create_for(destination: &Path) -> Result<Self> {
        let parent = staging_parent(destination)?;
        fs::create_dir_all(parent).with_context(|| format!("mkdir -p {}", parent.display()))?;
        let first = ARCHIVE_STAGING_NONCE.fetch_add(ARCHIVE_STAGING_ATTEMPTS, Ordering::Relaxed);
        for offset in 0..ARCHIVE_STAGING_ATTEMPTS {
            let path = sibling_work_path(parent, "download", first.wrapping_add(offset));
            let mut options = fs::OpenOptions::new();
            options.write(true).create_new(true);
            #[cfg(unix)]
            {
                use std::os::unix::fs::OpenOptionsExt as _;
                options.mode(0o600);
            }
            match options.open(&path) {
                Ok(file) => {
                    drop(file);
                    return Ok(Self { path, armed: true });
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
                Err(error) => {
                    return Err(error).with_context(|| {
                        format!("create download staging file {}", path.display())
                    });
                }
            }
        }
        bail!(
            "could not reserve a download staging file in {} after {} attempts",
            parent.display(),
            ARCHIVE_STAGING_ATTEMPTS
        )
    }

    fn mark_installed(&mut self) {
        self.armed = false;
    }
}

impl Drop for DownloadStagingFile {
    fn drop(&mut self) {
        if self.armed {
            let _ = remove_path_if_present(&self.path);
        }
    }
}

fn staging_parent(destination: &Path) -> Result<&Path> {
    if destination.file_name().is_none() {
        bail!(
            "destination {} must name an artifact below a parent",
            destination.display()
        );
    }
    match destination.parent() {
        Some(parent) if parent.as_os_str().is_empty() => Ok(Path::new(".")),
        Some(parent) => Ok(parent),
        None => Ok(Path::new(".")),
    }
}

fn sibling_work_path(parent: &Path, purpose: &str, nonce: u64) -> PathBuf {
    parent.join(format!(
        ".ay-corpus-{purpose}-{}-{nonce}",
        std::process::id()
    ))
}

fn path_is_present(path: &Path) -> Result<bool> {
    match fs::symlink_metadata(path) {
        Ok(_) => Ok(true),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(error).with_context(|| format!("inspect {}", path.display())),
    }
}

fn remove_path_if_present(path: &Path) -> Result<()> {
    let metadata = match fs::symlink_metadata(path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(error) => {
            return Err(error).with_context(|| format!("inspect {}", path.display()));
        }
    };
    if metadata.file_type().is_dir() {
        fs::remove_dir_all(path).with_context(|| format!("rm -rf {}", path.display()))
    } else {
        fs::remove_file(path).with_context(|| format!("rm {}", path.display()))
    }
}

fn install_staged_path(staging: &Path, destination: &Path, replace_existing: bool) -> Result<()> {
    let displaced = if replace_existing {
        displace_existing_destination(destination)?
    } else {
        None
    };

    if let Err(publish_error) = ay_sys::fs::rename_noreplace(staging, destination) {
        if let Some(displaced) = displaced {
            let restore = ay_sys::fs::rename_noreplace(&displaced, destination);
            return match restore {
                Ok(()) => Err(publish_error).with_context(|| {
                    format!(
                        "install staged artifact at {}; previous artifact was restored",
                        destination.display()
                    )
                }),
                Err(restore_error) => bail!(
                    "install staged artifact at {} failed: {}; restoring previous artifact from {} also failed: {}",
                    destination.display(),
                    publish_error,
                    displaced.display(),
                    restore_error
                ),
            };
        }
        return Err(publish_error)
            .with_context(|| format!("install staged artifact at {}", destination.display()));
    }

    if let Some(displaced) = displaced {
        remove_path_if_present(&displaced).with_context(|| {
            format!(
                "new artifact installed at {}, but stale replacement remained at {}",
                destination.display(),
                displaced.display()
            )
        })?;
    }
    Ok(())
}

fn displace_existing_destination(destination: &Path) -> Result<Option<PathBuf>> {
    if !path_is_present(destination)? {
        return Ok(None);
    }
    let parent = staging_parent(destination)?;
    let first = ARCHIVE_STAGING_NONCE.fetch_add(ARCHIVE_STAGING_ATTEMPTS, Ordering::Relaxed);
    for offset in 0..ARCHIVE_STAGING_ATTEMPTS {
        let displaced = sibling_work_path(parent, "previous", first.wrapping_add(offset));
        match ay_sys::fs::rename_noreplace(destination, &displaced) {
            Ok(()) => return Ok(Some(displaced)),
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(error) => {
                return Err(error).with_context(|| {
                    format!(
                        "move existing archive directory {} aside",
                        destination.display()
                    )
                });
            }
        }
    }
    bail!(
        "could not reserve a replacement path for {} after {} attempts",
        destination.display(),
        ARCHIVE_STAGING_ATTEMPTS
    )
}

fn download_file_atomically(
    name: &str,
    destination: &Path,
    expected_sha256: Option<&str>,
    expected_size: Option<u64>,
    download: impl FnOnce(&Path) -> Result<()>,
) -> Result<()> {
    let mut staging = DownloadStagingFile::create_for(destination)?;
    download(&staging.path).with_context(|| format!("{name}: download into private staging"))?;
    validate_file_pins(&staging.path, expected_sha256, expected_size)
        .with_context(|| format!("{name}: downloaded file failed validation"))?;
    install_staged_path(&staging.path, destination, true)
        .with_context(|| format!("{name}: publish verified download"))?;
    staging.mark_installed();
    Ok(())
}

fn download_http_file_atomically(
    name: &str,
    destination: &Path,
    url: &str,
    expected_sha256: Option<&str>,
    expected_size: Option<u64>,
) -> Result<()> {
    download_file_with_resume(
        name,
        destination,
        expected_sha256,
        expected_size,
        |partial| http_get_direct(url, partial),
    )
}

/// Download into a stable sibling `.part` file so an interrupted transfer can
/// continue in a later process. The published destination is never modified
/// until the partial file has passed all declared pins.
fn download_file_with_resume(
    name: &str,
    destination: &Path,
    expected_sha256: Option<&str>,
    expected_size: Option<u64>,
    download: impl FnOnce(&Path) -> Result<()>,
) -> Result<()> {
    let partial = download_partial_path(destination)?;
    let parent = staging_parent(destination)?;
    fs::create_dir_all(parent).with_context(|| format!("mkdir -p {}", parent.display()))?;

    if path_is_present(&partial)? {
        let metadata = fs::symlink_metadata(&partial)
            .with_context(|| format!("inspect partial download {}", partial.display()))?;
        if !metadata.file_type().is_file() {
            bail!(
                "partial download path {} is not a regular file",
                partial.display()
            );
        }
    }

    download(&partial).with_context(|| {
        format!(
            "{name}: download into resumable partial {}; partial retained for retry",
            partial.display()
        )
    })?;
    if let Err(validation_error) = validate_file_pins(&partial, expected_sha256, expected_size) {
        remove_path_if_present(&partial).with_context(|| {
            format!(
                "{name}: downloaded file failed validation ({validation_error:#}); \
                 remove unusable partial {}",
                partial.display()
            )
        })?;
        return Err(validation_error)
            .with_context(|| format!("{name}: downloaded file failed validation"));
    }
    install_staged_path(&partial, destination, true)
        .with_context(|| format!("{name}: publish verified download"))?;
    Ok(())
}

fn download_partial_path(destination: &Path) -> Result<PathBuf> {
    let parent = staging_parent(destination)?;
    let mut file_name = destination
        .file_name()
        .expect("staging_parent validates the destination filename")
        .to_os_string();
    file_name.push(".part");
    Ok(parent.join(file_name))
}

fn validate_file_pins(
    path: &Path,
    expected_sha256: Option<&str>,
    expected_size: Option<u64>,
) -> Result<()> {
    if let Some(expected) = expected_size {
        let actual = fs::metadata(path)
            .with_context(|| format!("stat {}", path.display()))?
            .len();
        if actual != expected {
            bail!(
                "size mismatch for {} (expected {} bytes, got {})",
                path.display(),
                expected,
                actual
            );
        }
    }
    if let Some(expected) = expected_sha256 {
        let actual = local_sha256(path)?;
        if actual != expected {
            bail!(
                "SHA256 mismatch for {} (expected {}, got {})",
                path.display(),
                expected,
                actual
            );
        }
    }
    Ok(())
}

fn local_sha256(path: &Path) -> Result<String> {
    let mut file = fs::File::open(path).with_context(|| format!("open {}", path.display()))?;
    let mut hasher = Sha256::new();
    let mut buf = vec![0u8; 64 * 1024];
    loop {
        let n = file
            .read(&mut buf)
            .with_context(|| format!("read {}", path.display()))?;
        if n == 0 {
            break;
        }
        hasher.update(&buf[..n]);
    }
    Ok(hex(&hasher.finalize()))
}

fn hex(bytes: &[u8]) -> String {
    const LUT: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        s.push(LUT[(b >> 4) as usize] as char);
        s.push(LUT[(b & 0xf) as usize] as char);
    }
    s
}

fn human_bytes(n: u64) -> String {
    const UNITS: &[&str] = &["B", "KB", "MB", "GB", "TB"];
    let mut v = n as f64;
    let mut u = 0;
    while v >= 1024.0 && u + 1 < UNITS.len() {
        v /= 1024.0;
        u += 1;
    }
    if u == 0 {
        format!("{} {}", n, UNITS[0])
    } else {
        format!("{:.1} {}", v, UNITS[u])
    }
}

fn http_get(url: &str, out: &Path) -> Result<()> {
    download_http_file_atomically("HTTP download", out, url, None, None)
}

fn http_get_direct(url: &str, out: &Path) -> Result<()> {
    let mut cmd = if which("curl") {
        let mut c = ProcCommand::new("curl");
        c.args([
            "--fail",
            "--location",
            "--progress-bar",
            "--retry",
            "5",
            "--retry-all-errors",
            "--connect-timeout",
            "30",
            "--continue-at",
            "-",
            "-o",
        ])
        .arg(out)
        .arg(url);
        c
    } else if which("wget") {
        let mut c = ProcCommand::new("wget");
        c.args(["-q", "--show-progress", "--tries=5", "--continue", "-O"])
            .arg(out)
            .arg(url);
        c
    } else {
        bail!("neither curl nor wget available on PATH");
    };
    let status = cmd.status().context("invoke http downloader")?;
    if !status.success() {
        bail!("http download exited with {:?}", status.code());
    }
    Ok(())
}

fn is_executable_file(path: &Path) -> bool {
    if !path.is_file() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;

        fs::metadata(path)
            .map(|metadata| metadata.permissions().mode() & 0o111 != 0)
            .unwrap_or(false)
    }
    #[cfg(not(unix))]
    {
        true
    }
}

fn which(tool: &str) -> bool {
    let path = Path::new(tool);
    if path.components().count() > 1 {
        return is_executable_file(path);
    }
    std::env::var_os("PATH").is_some_and(|paths| {
        std::env::split_paths(&paths).any(|directory| is_executable_file(&directory.join(tool)))
    })
}

fn gh_release_download(repo: &str, tag: &str, asset: &str, out: &Path) -> Result<()> {
    if let Some(parent) = out.parent() {
        fs::create_dir_all(parent).with_context(|| format!("mkdir -p {}", parent.display()))?;
    }
    let status = ProcCommand::new("gh")
        .args([
            "release",
            "download",
            tag,
            "--repo",
            repo,
            "--pattern",
            asset,
            "--output",
        ])
        .arg(out)
        .arg("--clobber")
        .status()
        .context("invoke gh release download")?;
    if !status.success() {
        bail!("gh release download exited with {:?}", status.code());
    }
    Ok(())
}

fn gh_release_upload(repo: &str, tag: &str, file: &Path, clobber: bool) -> Result<()> {
    let mut cmd = ProcCommand::new("gh");
    cmd.args(["release", "upload", tag, "--repo", repo])
        .arg(file);
    if clobber {
        cmd.arg("--clobber");
    }
    let status = cmd.status().context("invoke gh release upload")?;
    if !status.success() {
        bail!("gh release upload exited with {:?}", status.code());
    }
    Ok(())
}

fn pack_tarball(from: &Path, out: &Path) -> Result<()> {
    let parent = from
        .parent()
        .ok_or_else(|| anyhow!("source dir {} has no parent", from.display()))?;
    let leaf = from
        .file_name()
        .ok_or_else(|| anyhow!("source dir {} has no basename", from.display()))?;
    let outfile = fs::File::create(out).with_context(|| format!("create {}", out.display()))?;
    let mut tar = ProcCommand::new("tar")
        .arg("-cf")
        .arg("-")
        .arg("-C")
        .arg(parent)
        .arg(leaf)
        .stdout(Stdio::piped())
        .spawn()
        .context("spawn tar")?;
    let tar_stdout = tar.stdout.take().ok_or_else(|| anyhow!("tar stdout"))?;
    let zstd_status = ProcCommand::new("zstd")
        .args(["-19", "-T0", "-q"])
        .stdin(Stdio::from(tar_stdout))
        .stdout(Stdio::from(outfile))
        .status()
        .context("invoke zstd")?;
    let tar_status = tar.wait().context("wait tar")?;
    if !tar_status.success() {
        bail!("tar exited with {:?}", tar_status.code());
    }
    if !zstd_status.success() {
        bail!("zstd exited with {:?}", zstd_status.code());
    }
    Ok(())
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ArchiveMemberKind {
    File,
    Directory,
    Symlink(PathBuf),
    HardLink(PathBuf),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ArchiveSymlinkRewrite {
    member: PathBuf,
    archived_target: PathBuf,
    materialized_target: PathBuf,
    target_is_directory: bool,
}

#[derive(Debug, Default)]
struct ArchiveSafetyPlan {
    symlink_rewrites: Vec<ArchiveSymlinkRewrite>,
}

fn extract_tarball(
    tarball: &Path,
    into: &Path,
    symlink_policy: ArchiveSymlinkPolicy,
) -> Result<()> {
    let safety = inspect_tar_archive(tarball, symlink_policy)?;
    let try_auto = ProcCommand::new("tar")
        .arg("-tf")
        .arg(tarball)
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status();
    if matches!(try_auto, Ok(s) if s.success()) {
        let status = ProcCommand::new("tar")
            .arg("-xf")
            .arg(tarball)
            .arg("-C")
            .arg(into)
            .status()
            .context("invoke tar -xf")?;
        if !status.success() {
            bail!("tar -xf exited with {:?}", status.code());
        }
        apply_archive_symlink_rewrites(into, &safety)?;
        return Ok(());
    }
    let mut zstd = ProcCommand::new("zstd")
        .args(["-dc"])
        .arg(tarball)
        .stdout(Stdio::piped())
        .spawn()
        .context("spawn zstd -dc")?;
    let zstd_stdout = zstd.stdout.take().ok_or_else(|| anyhow!("zstd stdout"))?;
    let tar_status = ProcCommand::new("tar")
        .arg("-xf")
        .arg("-")
        .arg("-C")
        .arg(into)
        .stdin(Stdio::from(zstd_stdout))
        .status()
        .context("invoke tar -xf -")?;
    let zstd_status = zstd.wait().context("wait zstd")?;
    if !zstd_status.success() {
        bail!("zstd -dc exited with {:?}", zstd_status.code());
    }
    if !tar_status.success() {
        bail!("tar -xf exited with {:?}", tar_status.code());
    }
    apply_archive_symlink_rewrites(into, &safety)?;
    Ok(())
}

fn extract_zip(zip: &Path, into: &Path, symlink_policy: ArchiveSymlinkPolicy) -> Result<()> {
    if !which("unzip") {
        bail!("install unzip (brew install unzip) to extract .zip archives");
    }
    let safety = inspect_zip_archive(zip, symlink_policy)?;
    let status = ProcCommand::new("unzip")
        .args(["-q", "-o"])
        .arg(zip)
        .arg("-d")
        .arg(into)
        .status()
        .context("invoke unzip")?;
    if !status.success() {
        bail!("unzip exited with {:?}", status.code());
    }
    apply_archive_symlink_rewrites(into, &safety)?;
    Ok(())
}

fn inspect_tar_archive(
    archive_path: &Path,
    symlink_policy: ArchiveSymlinkPolicy,
) -> Result<ArchiveSafetyPlan> {
    let (reader, mut decompressor) = open_tar_reader(archive_path)?;
    let inspection = inspect_tar_reader(reader, symlink_policy);
    let decompressor_status = match decompressor.as_mut() {
        Some(child) => Some(child.wait().context("wait archive decompressor")?),
        None => None,
    };
    if let Some(status) = decompressor_status {
        if !status.success() && inspection.is_ok() {
            bail!("archive decompressor exited with {:?}", status.code());
        }
    }
    inspection
}

fn open_tar_reader(archive_path: &Path) -> Result<(Box<dyn Read>, Option<Child>)> {
    let mut archive = fs::File::open(archive_path)
        .with_context(|| format!("open archive {}", archive_path.display()))?;
    let mut magic = [0u8; 6];
    let read = archive
        .read(&mut magic)
        .with_context(|| format!("read archive magic {}", archive_path.display()))?;
    drop(archive);

    let decompressor = if read >= XZ_MAGIC.len() && magic == XZ_MAGIC {
        Some(("xz", "-dc"))
    } else if read >= 2 && magic[..2] == [0x1f, 0x8b] {
        Some(("gzip", "-dc"))
    } else if read >= 3 && magic[..3] == *b"BZh" {
        Some(("bzip2", "-dc"))
    } else if read >= 4 && magic[..4] == [0x28, 0xb5, 0x2f, 0xfd] {
        Some(("zstd", "-dc"))
    } else {
        None
    };

    let Some((program, flag)) = decompressor else {
        let archive = fs::File::open(archive_path)
            .with_context(|| format!("open archive {}", archive_path.display()))?;
        return Ok((Box::new(BufReader::new(archive)), None));
    };
    let mut child = ProcCommand::new(program)
        .arg(flag)
        .arg(archive_path)
        .stdout(Stdio::piped())
        .spawn()
        .with_context(|| format!("spawn {program} for {}", archive_path.display()))?;
    let stdout = child
        .stdout
        .take()
        .ok_or_else(|| anyhow!("{program} stdout was not piped"))?;
    Ok((Box::new(BufReader::new(stdout)), Some(child)))
}

fn inspect_tar_reader(
    reader: Box<dyn Read>,
    symlink_policy: ArchiveSymlinkPolicy,
) -> Result<ArchiveSafetyPlan> {
    let mut archive = tar::Archive::new(reader);
    let mut members = BTreeMap::new();
    for entry in archive.entries().context("read tar member table")? {
        let entry = entry.context("read tar member")?;
        let Some(path) = normalized_archive_member_name(&entry.path_bytes())? else {
            continue;
        };
        let entry_type = entry.header().entry_type();
        let kind = if entry_type.is_file() {
            ArchiveMemberKind::File
        } else if entry_type.is_dir() {
            ArchiveMemberKind::Directory
        } else if entry_type.is_symlink() {
            let target = archive_link_target(
                entry
                    .link_name_bytes()
                    .as_deref()
                    .ok_or_else(|| anyhow!("tar symlink {} has no target", path.display()))?,
                &path,
            )?;
            ArchiveMemberKind::Symlink(target)
        } else if entry_type.is_hard_link() {
            let target = archive_link_target(
                entry
                    .link_name_bytes()
                    .as_deref()
                    .ok_or_else(|| anyhow!("tar hard link {} has no target", path.display()))?,
                &path,
            )?;
            ArchiveMemberKind::HardLink(target)
        } else {
            bail!(
                "archive member {} has unsupported special type {:?}",
                path.display(),
                entry_type
            );
        };
        insert_archive_member(&mut members, path, kind)?;
    }
    build_archive_safety_plan(&members, symlink_policy)
}

fn inspect_zip_archive(
    archive_path: &Path,
    symlink_policy: ArchiveSymlinkPolicy,
) -> Result<ArchiveSafetyPlan> {
    let archive_file = fs::File::open(archive_path)
        .with_context(|| format!("open ZIP archive {}", archive_path.display()))?;
    let mut archive = zip::ZipArchive::new(archive_file)
        .with_context(|| format!("read ZIP member table {}", archive_path.display()))?;
    let mut members = BTreeMap::new();
    for index in 0..archive.len() {
        let mut entry = archive
            .by_index(index)
            .with_context(|| format!("read ZIP member {index}"))?;
        let Some(path) = normalized_archive_member_name(entry.name_raw())? else {
            continue;
        };
        let kind = if entry.is_symlink() {
            let mut target = Vec::new();
            (&mut entry)
                .take(65_537)
                .read_to_end(&mut target)
                .with_context(|| format!("read ZIP symlink target {}", path.display()))?;
            if target.len() > 65_536 {
                bail!("ZIP symlink target {} exceeds 64 KiB", path.display());
            }
            ArchiveMemberKind::Symlink(archive_link_target(&target, &path)?)
        } else if entry.is_dir() {
            ArchiveMemberKind::Directory
        } else {
            let unix_type = entry.unix_mode().unwrap_or(0) & 0o170_000;
            if unix_type != 0 && unix_type != 0o100_000 {
                bail!(
                    "ZIP member {} has unsupported special mode {unix_type:#o}",
                    path.display()
                );
            }
            ArchiveMemberKind::File
        };
        insert_archive_member(&mut members, path, kind)?;
    }
    build_archive_safety_plan(&members, symlink_policy)
}

fn normalized_archive_member_name(raw: &[u8]) -> Result<Option<PathBuf>> {
    if raw.contains(&0) {
        bail!("archive member name contains NUL");
    }
    let name = std::str::from_utf8(raw).context("archive member name is not UTF-8")?;
    if name.starts_with('/') || archive_windows_absolute(name) {
        bail!("archive member has absolute path {name:?}");
    }
    if name.contains('\\') {
        bail!("archive member path contains ambiguous backslash {name:?}");
    }

    let components = name.split('/').collect::<Vec<_>>();
    let mut normalized = PathBuf::new();
    let mut saw_component = false;
    for (index, component) in components.iter().enumerate() {
        if component.is_empty() {
            if index + 1 == components.len() {
                continue;
            }
            bail!("archive member has non-normal path {name:?}");
        }
        if *component == "." {
            if index == 0 {
                continue;
            }
            bail!("archive member has non-normal path {name:?}");
        }
        if *component == ".." {
            bail!("archive member escapes extraction root: {name:?}");
        }
        normalized.push(component);
        saw_component = true;
    }
    if !saw_component {
        return Ok(None);
    }
    Ok(Some(normalized))
}

fn archive_windows_absolute(path: &str) -> bool {
    let bytes = path.as_bytes();
    bytes.len() >= 3
        && bytes[0].is_ascii_alphabetic()
        && bytes[1] == b':'
        && matches!(bytes[2], b'/' | b'\\')
}

fn archive_link_target(raw: &[u8], member: &Path) -> Result<PathBuf> {
    if raw.is_empty() || raw.contains(&0) {
        bail!(
            "archive link {} has an empty or NUL target",
            member.display()
        );
    }
    let target = std::str::from_utf8(raw)
        .with_context(|| format!("archive link {} target is not UTF-8", member.display()))?;
    if target.contains('\\') {
        bail!(
            "archive link {} target contains ambiguous backslash {target:?}",
            member.display()
        );
    }
    Ok(PathBuf::from(target))
}

fn insert_archive_member(
    members: &mut BTreeMap<PathBuf, ArchiveMemberKind>,
    path: PathBuf,
    kind: ArchiveMemberKind,
) -> Result<()> {
    if let Some(existing) = members.get(&path) {
        if existing == &ArchiveMemberKind::Directory && kind == ArchiveMemberKind::Directory {
            return Ok(());
        }
        bail!("archive contains duplicate member {}", path.display());
    }
    members.insert(path, kind);
    Ok(())
}

fn build_archive_safety_plan(
    members: &BTreeMap<PathBuf, ArchiveMemberKind>,
    symlink_policy: ArchiveSymlinkPolicy,
) -> Result<ArchiveSafetyPlan> {
    for path in members.keys() {
        let mut ancestor = path.parent();
        while let Some(parent) = ancestor {
            if parent.as_os_str().is_empty() {
                break;
            }
            if matches!(
                members.get(parent),
                Some(ArchiveMemberKind::Symlink(_) | ArchiveMemberKind::HardLink(_))
            ) {
                bail!(
                    "archive member {} traverses archive link {}",
                    path.display(),
                    parent.display()
                );
            }
            ancestor = parent.parent();
        }
    }

    let mut plan = ArchiveSafetyPlan::default();
    for (member, kind) in members {
        match kind {
            ArchiveMemberKind::Symlink(target) => {
                validate_archive_symlink(members, member, target, symlink_policy, &mut plan)?;
            }
            ArchiveMemberKind::HardLink(target) => {
                validate_archive_hard_link(members, member, target)?;
            }
            ArchiveMemberKind::File | ArchiveMemberKind::Directory => {}
        }
    }
    Ok(plan)
}

fn validate_archive_symlink(
    members: &BTreeMap<PathBuf, ArchiveMemberKind>,
    member: &Path,
    target: &Path,
    symlink_policy: ArchiveSymlinkPolicy,
    plan: &mut ArchiveSafetyPlan,
) -> Result<()> {
    let target_text = target
        .to_str()
        .ok_or_else(|| anyhow!("archive symlink {} target is not UTF-8", member.display()))?;
    if target.is_absolute() || archive_windows_absolute(target_text) {
        if symlink_policy != ArchiveSymlinkPolicy::NormalizeUniqueInArchive {
            bail!(
                "archive symlink {} has absolute target {}",
                member.display(),
                target.display()
            );
        }
        let mapped = unique_absolute_link_member(members, member, target)?;
        let parent = member.parent().unwrap_or_else(|| Path::new(""));
        let materialized_target = relative_archive_path(parent, &mapped)?;
        let target_is_directory = archive_member_is_directory(members, &mapped);
        plan.symlink_rewrites.push(ArchiveSymlinkRewrite {
            member: member.to_path_buf(),
            archived_target: target.to_path_buf(),
            materialized_target,
            target_is_directory,
        });
        return Ok(());
    }

    let parent = member.parent().unwrap_or_else(|| Path::new(""));
    let resolved = resolve_relative_archive_link(parent, target).with_context(|| {
        format!(
            "archive symlink {} target {} escapes extraction root",
            member.display(),
            target.display()
        )
    })?;
    if !archive_member_exists(members, &resolved) {
        bail!(
            "archive symlink {} target {} is missing from the archive",
            member.display(),
            target.display()
        );
    }
    Ok(())
}

fn validate_archive_hard_link(
    members: &BTreeMap<PathBuf, ArchiveMemberKind>,
    member: &Path,
    target: &Path,
) -> Result<()> {
    let target_text = target
        .to_str()
        .ok_or_else(|| anyhow!("archive hard link {} target is not UTF-8", member.display()))?;
    if target.is_absolute() || archive_windows_absolute(target_text) {
        bail!(
            "archive hard link {} has absolute target {}",
            member.display(),
            target.display()
        );
    }
    let Some(normalized) = normalized_archive_member_name(target_text.as_bytes())? else {
        bail!(
            "archive hard link {} targets archive root",
            member.display()
        );
    };
    if !matches!(
        members.get(&normalized),
        Some(ArchiveMemberKind::File | ArchiveMemberKind::HardLink(_))
    ) {
        bail!(
            "archive hard link {} target {} is missing or not a file",
            member.display(),
            target.display()
        );
    }
    Ok(())
}

fn resolve_relative_archive_link(parent: &Path, target: &Path) -> Result<PathBuf> {
    let mut components = parent
        .components()
        .filter_map(|component| match component {
            Component::Normal(value) => Some(value.to_os_string()),
            _ => None,
        })
        .collect::<Vec<_>>();
    for component in target.components() {
        match component {
            Component::CurDir => {}
            Component::Normal(value) => components.push(value.to_os_string()),
            Component::ParentDir => {
                if components.pop().is_none() {
                    bail!("link target escapes root");
                }
            }
            Component::RootDir | Component::Prefix(_) => bail!("link target is absolute"),
        }
    }
    if components.is_empty() {
        return Ok(PathBuf::new());
    }
    Ok(components.iter().collect())
}

fn unique_absolute_link_member(
    members: &BTreeMap<PathBuf, ArchiveMemberKind>,
    link: &Path,
    target: &Path,
) -> Result<PathBuf> {
    let target_components = target
        .components()
        .filter_map(|component| match component {
            Component::Normal(value) => value.to_str(),
            Component::RootDir => None,
            Component::CurDir | Component::ParentDir | Component::Prefix(_) => None,
        })
        .collect::<Vec<_>>();
    let mut matches = Vec::new();
    for candidate in members.keys() {
        let candidate_components = candidate
            .components()
            .filter_map(|component| match component {
                Component::Normal(value) => value.to_str(),
                _ => None,
            })
            .collect::<Vec<_>>();
        if !candidate_components.is_empty()
            && target_components.ends_with(candidate_components.as_slice())
        {
            matches.push(candidate.clone());
        }
    }
    match matches.as_slice() {
        [mapped] => Ok(mapped.clone()),
        [] => bail!(
            "archive symlink {} absolute target {} has no in-archive suffix match",
            link.display(),
            target.display()
        ),
        _ => bail!(
            "archive symlink {} absolute target {} has ambiguous in-archive suffix matches: {}",
            link.display(),
            target.display(),
            matches
                .iter()
                .map(|path| path.display().to_string())
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

fn relative_archive_path(from_directory: &Path, to: &Path) -> Result<PathBuf> {
    let from = from_directory
        .components()
        .map(|component| match component {
            Component::Normal(value) => Ok(value.to_os_string()),
            _ => bail!("non-normal source path {}", from_directory.display()),
        })
        .collect::<Result<Vec<_>>>()?;
    let destination = to
        .components()
        .map(|component| match component {
            Component::Normal(value) => Ok(value.to_os_string()),
            _ => bail!("non-normal target path {}", to.display()),
        })
        .collect::<Result<Vec<_>>>()?;
    let common = from
        .iter()
        .zip(&destination)
        .take_while(|(left, right)| left == right)
        .count();
    let mut relative = PathBuf::new();
    for _ in common..from.len() {
        relative.push("..");
    }
    for component in &destination[common..] {
        relative.push(component);
    }
    if relative.as_os_str().is_empty() {
        relative.push(".");
    }
    Ok(relative)
}

fn archive_member_exists(members: &BTreeMap<PathBuf, ArchiveMemberKind>, target: &Path) -> bool {
    if target.as_os_str().is_empty() {
        return false;
    }
    members.contains_key(target)
        || members
            .keys()
            .any(|member| member != target && member.starts_with(target))
}

fn archive_member_is_directory(
    members: &BTreeMap<PathBuf, ArchiveMemberKind>,
    target: &Path,
) -> bool {
    matches!(members.get(target), Some(ArchiveMemberKind::Directory))
        || members
            .keys()
            .any(|member| member != target && member.starts_with(target))
}

fn apply_archive_symlink_rewrites(root: &Path, safety: &ArchiveSafetyPlan) -> Result<()> {
    for rewrite in &safety.symlink_rewrites {
        let path = root.join(&rewrite.member);
        let metadata = fs::symlink_metadata(&path)
            .with_context(|| format!("inspect extracted symlink {}", path.display()))?;
        if !metadata.file_type().is_symlink() {
            bail!(
                "archive extractor did not preserve symlink {}",
                rewrite.member.display()
            );
        }
        let extracted_target =
            fs::read_link(&path).with_context(|| format!("read symlink {}", path.display()))?;
        if extracted_target != rewrite.archived_target {
            bail!(
                "archive extractor changed symlink {} target from {} to {}",
                rewrite.member.display(),
                rewrite.archived_target.display(),
                extracted_target.display()
            );
        }
        fs::remove_file(&path)
            .with_context(|| format!("remove unsafe absolute symlink {}", path.display()))?;
        create_materialized_symlink(
            &rewrite.materialized_target,
            &path,
            rewrite.target_is_directory,
        )
        .with_context(|| {
            format!(
                "normalize archive symlink {} to {}",
                rewrite.member.display(),
                rewrite.materialized_target.display()
            )
        })?;
    }
    if !safety.symlink_rewrites.is_empty() {
        println!(
            "    normalized {} absolute archive symlink(s) to unique in-archive targets",
            safety.symlink_rewrites.len()
        );
    }
    Ok(())
}

#[cfg(unix)]
fn create_materialized_symlink(
    target: &Path,
    link: &Path,
    _target_is_directory: bool,
) -> Result<()> {
    std::os::unix::fs::symlink(target, link)
        .with_context(|| format!("symlink {} -> {}", link.display(), target.display()))
}

#[cfg(windows)]
fn create_materialized_symlink(
    target: &Path,
    link: &Path,
    target_is_directory: bool,
) -> Result<()> {
    let result = if target_is_directory {
        std::os::windows::fs::symlink_dir(target, link)
    } else {
        std::os::windows::fs::symlink_file(target, link)
    };
    result.with_context(|| format!("symlink {} -> {}", link.display(), target.display()))
}

// ---------------------------------------------------------------------------
// `ay corpus fixtures`
// ---------------------------------------------------------------------------

/// Is `name` one of the AY-specific fixtures that has no upstream counterpart?
fn is_ay_specific_fixture(name: &str) -> bool {
    CHC_AY_SPECIFIC_FIXTURES.contains(&name)
}

/// Derive the list of `*_000.smt2` fixture basenames from the vendored dir, so
/// we refresh exactly what the tests need. Sorted and de-duplicated. Returns an
/// empty vec if the directory is absent or holds no `*_000.smt2` files.
fn chc_fixture_list(dest: &Path) -> Result<Vec<String>> {
    if !dest.is_dir() {
        return Ok(Vec::new());
    }
    let mut names = Vec::new();
    for entry in fs::read_dir(dest).with_context(|| format!("read dir {}", dest.display()))? {
        let entry = entry.with_context(|| format!("read entry in {}", dest.display()))?;
        let name = entry.file_name().to_string_lossy().into_owned();
        if name.ends_with("_000.smt2") {
            names.push(name);
        }
    }
    names.sort();
    names.dedup();
    Ok(names)
}

fn run_fixtures(args: FixturesArgs) -> Result<i32> {
    let dest = &args.dest;
    println!("==> chc-fixtures: CHC-COMP 2025 extra-small-lia *_000.smt2 test fixtures");
    let base = format!(
        "https://raw.githubusercontent.com/{CHC_FIXTURE_REPO}/{CHC_FIXTURE_COMMIT}/{CHC_FIXTURE_SUBDIR}"
    );
    println!("    upstream: {CHC_FIXTURE_REPO}@{CHC_FIXTURE_COMMIT} subdir {CHC_FIXTURE_SUBDIR}/");
    println!("    dest:     {}", dest.display());

    let files = chc_fixture_list(dest)?;
    if files.is_empty() {
        eprintln!(
            "    warning: no *_000.smt2 fixtures found to fetch (nothing vendored under {})",
            dest.display()
        );
        println!("\n==> summary");
        println!("    chc-fixtures: nothing to do");
        return Ok(0);
    }

    fs::create_dir_all(dest).with_context(|| format!("mkdir -p {}", dest.display()))?;

    let (mut fetched, mut have, mut skipped_ay, mut fail) = (0usize, 0usize, 0usize, 0usize);
    let total = files.len();
    for name in &files {
        let target = dest.join(name);
        if is_ay_specific_fixture(name) {
            if target.is_file() {
                println!("    skip   {name} (AY-specific, vendored — not on upstream)");
            } else {
                eprintln!(
                    "    skip   {name} (AY-specific, not on upstream; MISSING vendored copy)"
                );
            }
            skipped_ay += 1;
            continue;
        }
        // Re-download from upstream into a temp file first so a failed/empty
        // fetch never clobbers a good vendored copy.
        match fetch_fixture(&base, name, &target) {
            Ok(()) => {
                println!("    fetched {name}");
                fetched += 1;
            }
            Err(_) => {
                if target.is_file() {
                    println!(
                        "    have    {name} (upstream fetch failed/absent; keeping vendored copy)"
                    );
                    have += 1;
                } else {
                    eprintln!("    FAIL    {name} (not on upstream and not vendored)");
                    fail += 1;
                }
            }
        }
    }

    println!("\n==> summary");
    println!(
        "    chc-fixtures: {total} referenced — {fetched} fetched, {have} kept-vendored, \
         {skipped_ay} AY-specific skipped, {fail} failed"
    );
    if fail != 0 {
        eprintln!("    (one or more files failed to fetch — see FAIL lines above)");
        return Ok(1);
    }
    Ok(0)
}

/// Fetch one fixture from `<base>/<name>` into `target`, writing atomically via
/// a sibling temp file. The fetch is treated as a failure (and `target` left
/// untouched) when the download fails or yields an empty file — so a good
/// vendored copy is never clobbered.
fn fetch_fixture(base: &str, name: &str, target: &Path) -> Result<()> {
    let url = format!("{base}/{name}");
    let tmp = target.with_extension("smt2.fetch-tmp");
    let res = (|| -> Result<()> {
        http_get(&url, &tmp)?;
        let meta = fs::metadata(&tmp).with_context(|| format!("stat {}", tmp.display()))?;
        if meta.len() == 0 {
            bail!("empty download for {name}");
        }
        fs::rename(&tmp, target)
            .with_context(|| format!("mv {} -> {}", tmp.display(), target.display()))?;
        Ok(())
    })();
    if res.is_err() {
        let _ = fs::remove_file(&tmp);
    }
    res
}

// ---------------------------------------------------------------------------
// `ay corpus install-tool`
// ---------------------------------------------------------------------------

fn run_install_tool(args: InstallToolArgs) -> Result<i32> {
    eprintln!(
        "note: `ay corpus install-tool` is deprecated; use `ay tool install` \
         (same registry: reference/tools.toml)"
    );
    crate::cmd_tool::install_alias(&args.name, args.force)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    // ---------- Manifest parsing ----------

    #[test]
    fn manifest_v1_parses_with_default_source() {
        let body = r#"
schema_version = 1
repo = "alabsystems/ay"
release_tag = "corpora-v1"

[[corpus]]
name = "foo"
asset = "foo-v1.tar.zst"
extract_to = "benchmarks/foo"
sha256 = "abc123"
size_bytes = 42
"#;
        let m: Manifest = toml::from_str(body).unwrap();
        assert_eq!(m.schema_version, 1);
        assert_eq!(m.corpora.len(), 1);
        assert_eq!(m.corpora[0].source, Source::Release);
        assert_eq!(m.corpora[0].asset.as_deref(), Some("foo-v1.tar.zst"));
    }

    #[test]
    fn manifest_v2_explicit_sources_parse() {
        let body = r#"
schema_version = 2
repo = "alabsystems/ay"
release_tag = "corpora-v1"

[[corpus]]
name = "rel"
asset = "rel-v1.tar.zst"
extract_to = "benchmarks/rel"
sha256 = "deadbeef"

[[corpus]]
name = "h"
source = "http"
url = "https://example.com/h.tar"
extract_to = "benchmarks/h"
wrap_archive = true

[[corpus]]
name = "g"
source = "git"
url = "https://github.com/x/y"
extract_to = "benchmarks/g"

[[corpus]]
name = "zipless"
source = "http"
url = "https://example.com/q.zip"
extract_to = "benchmarks/q.zip"
archive = "none"
"#;
        let m: Manifest = toml::from_str(body).unwrap();
        assert_eq!(
            m.corpora.iter().map(|c| c.source).collect::<Vec<_>>(),
            vec![Source::Release, Source::Http, Source::Git, Source::Http]
        );
        assert_eq!(m.corpora[3].archive, Archive::None);
        assert!(m.corpora[1].wrap_archive);
    }

    fn load_inline(body: &str) -> Result<Manifest> {
        let dir = TempDir::new().unwrap();
        let path = dir.path().join("corpora.toml");
        fs::write(&path, body).unwrap();
        Manifest::load(&path)
    }

    #[test]
    fn load_rejects_unsupported_schema_version() {
        let err = load_inline(
            r#"
schema_version = 99
repo = "x/y"
release_tag = "v1"
"#,
        )
        .unwrap_err();
        assert!(err.to_string().contains("schema_version"));
    }

    #[test]
    fn load_rejects_duplicate_names() {
        let err = load_inline(
            r#"
schema_version = 2
repo = "x/y"
release_tag = "v1"

[[corpus]]
name = "dup"
asset = "a.tar.zst"
extract_to = "a"
sha256 = "00"

[[corpus]]
name = "dup"
asset = "b.tar.zst"
extract_to = "b"
sha256 = "01"
"#,
        )
        .unwrap_err();
        assert!(err.to_string().contains("duplicate"));
    }

    #[test]
    fn manifest_groups_select_a_portable_campaign() {
        let manifest = load_inline(
            r#"
schema_version = 2
repo = "x/y"
release_tag = "v1"

[[corpus]]
name = "campaign-corpus"
groups = ["competition-2025-2026", "sat"]
asset = "a.tar.zst"
extract_to = "a"
sha256 = "00"

[[corpus]]
name = "unrelated"
groups = ["security"]
asset = "b.tar.zst"
extract_to = "b"
sha256 = "01"
"#,
        )
        .unwrap();
        let selected = manifest
            .select(&[], false, &["competition-2025-2026".to_string()])
            .unwrap();
        assert_eq!(
            selected
                .iter()
                .map(|corpus| corpus.name.as_str())
                .collect::<Vec<_>>(),
            vec!["campaign-corpus"]
        );
        assert!(manifest
            .select(&[], false, &["missing-group".to_string()])
            .unwrap_err()
            .to_string()
            .contains("unknown corpus group"));
        assert!(manifest
            .select(
                &["campaign-corpus".to_string()],
                false,
                &["competition-2025-2026".to_string()],
            )
            .unwrap_err()
            .to_string()
            .contains("mutually exclusive"));
    }

    #[test]
    fn corpus_plan_resolves_dependencies_sizes_and_local_state() {
        let directory = TempDir::new().unwrap();
        fs::write(directory.path().join("dependency.bin"), b"0123456789").unwrap();
        let manifest_path = directory.path().join("corpora.toml");
        fs::write(
            &manifest_path,
            r#"
schema_version = 2
repo = "x/y"
release_tag = "v1"

[[corpus]]
name = "dependency"
source = "http"
url = "https://example.test/dependency.bin"
archive = "none"
extract_to = "dependency.bin"
size_bytes = 10

[[corpus]]
name = "target"
source = "http"
url = "https://example.test/target.zip"
archive = "zip"
extract_to = "target"
size_bytes = 100
depends_on = ["dependency"]
"#,
        )
        .unwrap();
        let manifest = Manifest::load(&manifest_path).unwrap();
        let selected = manifest.find("target").map(|corpus| vec![corpus]).unwrap();
        let targets = manifest.dependency_order(&selected).unwrap();
        let before = fs::read_dir(directory.path()).unwrap().count();
        let plan = build_corpus_plan(&manifest, &selected, &targets, directory.path()).unwrap();
        let after = fs::read_dir(directory.path()).unwrap().count();

        assert_eq!(before, after, "planning must not create local artifacts");
        assert_eq!(plan.schema_version, 2);
        assert_eq!(plan.selected_assets, 1);
        assert_eq!(plan.dependency_assets, 1);
        assert_eq!(plan.closure_assets, 2);
        assert_eq!(plan.installed_assets, 1);
        assert_eq!(plan.missing_or_stale_assets, 1);
        assert_eq!(plan.network_fetch_assets, 1);
        assert_eq!(plan.known_transfer_bytes, 110);
        assert_eq!(plan.known_remaining_transfer_bytes, 100);
        assert!(plan.unknown_size_sources.is_empty());
        assert!(plan.unknown_remaining_size_sources.is_empty());
        assert_eq!(
            plan.assets
                .iter()
                .map(|asset| (asset.name.as_str(), asset.selected, asset.installed))
                .collect::<Vec<_>>(),
            vec![("dependency", false, true), ("target", true, false)]
        );
        let target = plan
            .assets
            .iter()
            .find(|asset| asset.name == "target")
            .unwrap();
        assert!(target.groups.is_empty());
        assert_eq!(target.dependencies, ["dependency"]);
        assert_eq!(target.local_layout.destination.declared, "target");
        assert_eq!(
            target.local_layout.destination.resolved,
            directory.path().join("target").display().to_string()
        );
        let cache = target.local_layout.cache.as_ref().unwrap();
        assert_eq!(cache.declared, "target.zip");
        assert_eq!(
            cache.resolved,
            directory.path().join("target.zip").display().to_string()
        );
        assert_eq!(
            target.local_layout.materialization.kind,
            "archive-extraction"
        );
        assert_eq!(
            target
                .local_layout
                .materialization
                .archive_format
                .as_deref(),
            Some("zip")
        );
        assert_eq!(
            target
                .local_layout
                .materialization
                .archive_layout
                .as_deref(),
            Some("archive-root-in-parent")
        );
        match &target.acquisition {
            CorpusPlanAcquisition::Http { url, url_redacted } => {
                assert_eq!(url, "https://example.test/target.zip");
                assert!(!url_redacted);
            }
            other => panic!("unexpected target acquisition: {other:?}"),
        }
        assert_eq!(target.pins.size_bytes, Some(100));
        assert!(target.pins.sha256.is_none());
        assert!(target.pins.git_commit.is_none());
        assert!(target.manifest.is_none());
        let tool_ids = plan
            .required_tools
            .iter()
            .map(|requirement| requirement.id.as_str())
            .collect::<BTreeSet<_>>();
        assert!(tool_ids.contains("http-download"));
        assert!(tool_ids.contains("zip-extraction"));
        assert!(!directory.path().join("target.zip").exists());
        assert!(!directory.path().join("target").exists());
    }

    #[test]
    fn corpus_plan_json_exposes_pinned_sources_and_redacts_url_secrets() {
        let directory = TempDir::new().unwrap();
        fs::write(
            directory.path().join("objects.csv"),
            "hash,local_path\nabc123,downloads/abc123.cnf.xz\n",
        )
        .unwrap();
        fs::write(
            directory.path().join("objects.tsv"),
            format!(
                "https://example.test/result/one?access_token=topsecret\t3\t{}\n",
                "1".repeat(64)
            ),
        )
        .unwrap();
        let manifest_path = directory.path().join("corpora.toml");
        fs::write(
            &manifest_path,
            r#"
schema_version = 2
repo = "reviewer/corpora"
release_tag = "corpora-v7"

[[corpus]]
name = "release"
groups = ["review"]
asset = "release.tar.zst"
extract_to = "release-tree"
sha256 = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
size_bytes = 11

[[corpus]]
name = "git"
groups = ["review"]
source = "git"
url = "https://reviewer:hunter2@example.test/repo.git?token=topsecret&ref=v1"
extract_to = "git-tree"
depth = 3
commit = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
depends_on = ["release"]

[[corpus]]
name = "gbd"
groups = ["review"]
source = "gbd"
extract_to = "downloads"
manifest = "objects.csv"

[[corpus]]
name = "uri"
groups = ["review"]
source = "uri-list"
uri_list_format = "raw-json"
extract_to = "results"
manifest = "objects.tsv"
"#,
        )
        .unwrap();
        let manifest = Manifest::load(&manifest_path).unwrap();
        let selected = manifest.corpora.iter().collect::<Vec<_>>();
        let targets = manifest.dependency_order(&selected).unwrap();
        let plan = build_corpus_plan(&manifest, &selected, &targets, directory.path()).unwrap();
        let json = serde_json::to_value(&plan).unwrap();
        let json_text = serde_json::to_string(&json).unwrap();

        assert_eq!(json["schema_version"], 2);
        assert!(!json_text.contains("hunter2"));
        assert!(!json_text.contains("topsecret"));

        let assets = json["assets"].as_array().unwrap();
        let release = assets
            .iter()
            .find(|asset| asset["name"] == "release")
            .unwrap();
        assert_eq!(release["groups"], serde_json::json!(["review"]));
        assert_eq!(release["acquisition"]["kind"], "release");
        assert_eq!(release["acquisition"]["repository"], "reviewer/corpora");
        assert_eq!(release["acquisition"]["release_tag"], "corpora-v7");
        assert_eq!(release["acquisition"]["asset"], "release.tar.zst");
        assert_eq!(
            release["pins"]["sha256"],
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
        );
        assert_eq!(release["pins"]["size_bytes"], 11);
        assert_eq!(
            release["local_layout"]["cache"]["declared"],
            "release.tar.zst"
        );

        let git = assets.iter().find(|asset| asset["name"] == "git").unwrap();
        assert_eq!(git["dependencies"], serde_json::json!(["release"]));
        assert_eq!(git["acquisition"]["kind"], "git");
        assert_eq!(
            git["acquisition"]["url"],
            "https://example.test/repo.git?token=REDACTED&ref=v1"
        );
        assert_eq!(git["acquisition"]["url_redacted"], true);
        assert_eq!(git["acquisition"]["depth"], 3);
        assert_eq!(
            git["pins"]["git_commit"],
            "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
        );

        let gbd = assets.iter().find(|asset| asset["name"] == "gbd").unwrap();
        assert_eq!(
            gbd["acquisition"]["file_endpoint"],
            "https://benchmark-database.de/file/{upstream_object_id}"
        );
        assert_eq!(gbd["manifest"]["kind"], "gbd-manifest");
        assert_eq!(gbd["manifest"]["format"], "csv-hash-local-path");
        assert_eq!(gbd["manifest"]["row_count"], 1);
        assert_eq!(gbd["manifest"]["rows"][0]["upstream_object_id"], "abc123");
        assert_eq!(
            gbd["manifest"]["rows"][0]["download"]["declared"],
            "downloads/abc123.cnf.xz"
        );
        assert_eq!(
            gbd["manifest"]["rows"][0]["materialized"]["declared"],
            "downloads/abc123.cnf"
        );
        assert_eq!(gbd["manifest"]["sha256"].as_str().unwrap().len(), 64);

        let uri = assets.iter().find(|asset| asset["name"] == "uri").unwrap();
        assert_eq!(uri["acquisition"]["kind"], "uri-list");
        assert_eq!(uri["manifest"]["format"], "raw-json");
        assert_eq!(uri["manifest"]["row_count"], 1);
        assert_eq!(
            uri["manifest"]["rows"][0]["url"],
            "https://example.test/result/one?access_token=REDACTED"
        );
        assert_eq!(uri["manifest"]["rows"][0]["url_redacted"], true);
        assert_eq!(uri["manifest"]["rows"][0]["size_bytes"], 3);
        assert_eq!(
            uri["manifest"]["rows"][0]["sha256"],
            "1111111111111111111111111111111111111111111111111111111111111111"
        );
        assert_eq!(
            uri["manifest"]["rows"][0]["download"]["declared"],
            "results/result-one.json"
        );
    }

    #[test]
    fn corpus_plan_sums_only_missing_pinned_uri_rows() {
        let directory = TempDir::new().unwrap();
        let extract = directory.path().join("rows");
        fs::create_dir(&extract).unwrap();
        let present = b"done";
        fs::write(extract.join("1-1.json"), present).unwrap();
        let uri_list = directory.path().join("rows.tsv");
        fs::write(
            &uri_list,
            format!(
                "https://example.test/api/1/1\t4\t{}\n\
                 https://example.test/api/1/2\t7\t{}\n",
                sha256_bytes(present),
                "0".repeat(64),
            ),
        )
        .unwrap();
        let manifest_path = directory.path().join("corpora.toml");
        fs::write(
            &manifest_path,
            r#"
schema_version = 2
repo = "x/y"
release_tag = "v1"

[[corpus]]
name = "rows"
source = "uri-list"
uri_list_format = "raw-json"
manifest = "rows.tsv"
extract_to = "rows"
"#,
        )
        .unwrap();
        let manifest = Manifest::load(&manifest_path).unwrap();
        let selected = vec![manifest.find("rows").unwrap()];
        let targets = manifest.dependency_order(&selected).unwrap();
        let plan = build_corpus_plan(&manifest, &selected, &targets, directory.path()).unwrap();

        assert_eq!(plan.installed_assets, 0);
        assert_eq!(plan.missing_or_stale_assets, 1);
        assert_eq!(plan.network_fetch_assets, 1);
        assert_eq!(plan.known_transfer_bytes, 11);
        assert_eq!(plan.known_remaining_transfer_bytes, 7);
        assert!(plan.unknown_size_sources.is_empty());
        assert!(plan.unknown_remaining_size_sources.is_empty());
        assert!(plan.assets[0].transfer_size_complete);
        assert!(plan.assets[0].remaining_transfer_size_complete);
        assert_eq!(
            plan.required_tools
                .iter()
                .map(|requirement| requirement.id.as_str())
                .collect::<Vec<_>>(),
            vec!["http-download"]
        );
    }

    #[test]
    fn corpus_plan_reports_unknown_sources_and_lower_bound_capacity_warning() {
        let directory = TempDir::new().unwrap();
        let manifest_path = directory.path().join("corpora.toml");
        fs::write(
            &manifest_path,
            format!(
                r#"
schema_version = 2
repo = "x/y"
release_tag = "v1"

[[corpus]]
name = "huge"
source = "http"
url = "https://example.test/huge.bin"
archive = "none"
extract_to = "huge.bin"
size_bytes = {}

[[corpus]]
name = "unknown-git"
source = "git"
url = "https://example.test/repository.git"
extract_to = "unknown-git"
requires_git_lfs = true
"#,
                i64::MAX,
            ),
        )
        .unwrap();
        let manifest = Manifest::load(&manifest_path).unwrap();
        let selected = manifest.corpora.iter().collect::<Vec<_>>();
        let targets = manifest.dependency_order(&selected).unwrap();
        let plan = build_corpus_plan(&manifest, &selected, &targets, directory.path()).unwrap();

        assert_eq!(plan.known_transfer_bytes, i64::MAX as u64);
        assert_eq!(plan.known_remaining_transfer_bytes, i64::MAX as u64);
        assert_eq!(plan.unknown_size_sources.get("git"), Some(&1));
        assert_eq!(plan.unknown_remaining_size_sources.get("git"), Some(&1));
        assert!(plan.capacity_note.contains("not a guarantee"));
        #[cfg(unix)]
        assert!(plan.capacity_warning.is_some());
        let tool_ids = plan
            .required_tools
            .iter()
            .map(|requirement| requirement.id.as_str())
            .collect::<BTreeSet<_>>();
        assert!(tool_ids.contains("git-checkout"));
        assert!(tool_ids.contains("git-lfs-materialization"));
        assert!(tool_ids.contains("http-download"));
        serde_json::to_value(&plan).expect("plan must have a stable JSON representation");
    }

    #[test]
    fn manifest_rejects_invalid_or_duplicate_groups() {
        for groups in [r#"["Not Kebab"]"#, r#"["campaign", "campaign"]"#] {
            let body = format!(
                r#"
schema_version = 2
repo = "x/y"
release_tag = "v1"

[[corpus]]
name = "bad-group"
groups = {groups}
asset = "a.tar.zst"
extract_to = "a"
sha256 = "00"
"#
            );
            let error = load_inline(&body).expect_err("invalid groups must fail");
            assert!(format!("{error:#}").contains("group"));
        }
    }

    #[test]
    fn validate_release_requires_asset_and_sha256() {
        let err = load_inline(
            r#"
schema_version = 2
repo = "x/y"
release_tag = "v1"

[[corpus]]
name = "missing-sha"
asset = "a.tar.zst"
extract_to = "a"
"#,
        )
        .unwrap_err();
        assert!(format!("{err:#}").contains("sha256"));

        let err = load_inline(
            r#"
schema_version = 2
repo = "x/y"
release_tag = "v1"

[[corpus]]
name = "missing-asset"
extract_to = "a"
sha256 = "00"
"#,
        )
        .unwrap_err();
        assert!(format!("{err:#}").contains("asset"));
    }

    #[test]
    fn validate_gbd_requires_manifest() {
        let err = load_inline(
            r#"
schema_version = 2
repo = "x/y"
release_tag = "v1"

[[corpus]]
name = "g"
source = "gbd"
extract_to = "benchmarks/g"
"#,
        )
        .unwrap_err();
        assert!(format!("{err:#}").contains("manifest"));
    }

    #[test]
    fn gbd_source_parses_and_has_no_cache() {
        let body = r#"
schema_version = 2
repo = "x/y"
release_tag = "v1"

[[corpus]]
name = "g"
source = "gbd"
extract_to = "benchmarks/g"
manifest = "benchmarks/g/manifest.csv"
"#;
        let m: Manifest = toml::from_str(body).unwrap();
        assert_eq!(m.corpora[0].source, Source::Gbd);
        assert_eq!(
            m.corpora[0].manifest.as_deref(),
            Some("benchmarks/g/manifest.csv")
        );
        assert!(m.corpora[0].cache_path().is_none());
    }

    #[test]
    fn split_csv_line_handles_quoted_commas() {
        let cols = split_csv_line(r#"hash,filename,category,track,local_path"#);
        assert_eq!(
            cols,
            vec!["hash", "filename", "category", "track", "local_path"]
        );
        let row = split_csv_line(
            r#"abc123,foo.cnf.xz,industrial,"anni_2022,main_2024",benchmarks/x/abc123-foo.cnf.xz"#,
        );
        assert_eq!(row[0], "abc123");
        assert_eq!(row[3], "anni_2022,main_2024");
        assert_eq!(row[4], "benchmarks/x/abc123-foo.cnf.xz");
    }

    #[test]
    fn parse_gbd_manifest_reads_hash_and_local_path() {
        let dir = TempDir::new().unwrap();
        let path = dir.path().join("manifest.csv");
        fs::write(
            &path,
            "hash,filename,category,track,local_path\n\
             16c5482d,two-trees.cnf.xz,crafted,\"main_2024,submissions_2024\",benchmarks/sat/two-trees.cnf.xz\n\
             dcf5b822,2dlx.cnf.xz,industrial,\"anni_2022,main_2024\",benchmarks/sat/2dlx.cnf.xz\n",
        )
        .unwrap();
        let rows = parse_gbd_manifest(&path).unwrap();
        assert_eq!(rows.len(), 2);
        assert_eq!(rows[0].hash, "16c5482d");
        assert_eq!(rows[0].local_path, "benchmarks/sat/two-trees.cnf.xz");
        assert_eq!(rows[0].expected_size, None);
        assert_eq!(rows[0].expected_sha256, None);
        assert_eq!(rows[1].hash, "dcf5b822");
    }

    #[test]
    fn parse_gbd_manifest_rejects_non_normal_local_paths() {
        let directory = TempDir::new().unwrap();
        let manifest = directory.path().join("invalid-path.csv");
        for local_path in [
            "/absolute.cnf",
            "../escape.cnf",
            "corpus/./file.cnf",
            "corpus//file.cnf",
            r"corpus\file.cnf",
            "C:/windows.cnf",
            "corpus/\u{7}file.cnf",
        ] {
            fs::write(&manifest, format!("hash,local_path\nabc123,{local_path}\n")).unwrap();
            let error = parse_gbd_manifest(&manifest)
                .expect_err("non-normal GBD local_path must fail closed");
            assert!(
                format!("{error:#}").contains("normalized repository-relative path"),
                "unexpected error for {local_path:?}: {error:#}"
            );
        }
    }

    #[test]
    fn parse_gbd_manifest_enforces_response_pins() {
        let directory = TempDir::new().unwrap();
        let response = directory.path().join("response.cnf.xz");
        fs::write(&response, b"p cnf 0 0\n").unwrap();
        let sha256 = local_sha256(&response).unwrap();
        let manifest = directory.path().join("pinned.csv");
        fs::write(
            &manifest,
            format!(
                "hash,local_path,size_bytes,sha256\n\
                 abc123,response.cnf.xz,10,{sha256}\n"
            ),
        )
        .unwrap();
        let mut rows = parse_gbd_manifest(&manifest).unwrap();
        rows[0].local_path = response.to_string_lossy().into_owned();
        assert_eq!(rows.len(), 1);
        assert!(rows[0].has_complete_pins());
        assert!(rows[0].verify().is_ok());
        fs::write(&response, b"mutated\n").unwrap();
        assert!(rows[0].verify().is_err());

        for pins in [
            "10,not-a-sha".to_string(),
            format!("10,{}", "A".repeat(64)),
            format!("0,{sha256}"),
            "10,".to_string(),
        ] {
            fs::write(
                &manifest,
                format!(
                    "hash,local_path,size_bytes,sha256\n\
                     abc123,response.cnf.xz,{pins}\n"
                ),
            )
            .unwrap();
            assert!(
                parse_gbd_manifest(&manifest)
                    .unwrap_err()
                    .to_string()
                    .contains("positive size_bytes and canonical lowercase SHA-256"),
                "pins {pins:?} must fail"
            );
        }
    }

    #[test]
    fn gbd_download_rejects_traversal_before_any_write() {
        let directory = TempDir::new().unwrap();
        let manifest_path = directory.path().join("corpora.toml");
        fs::write(
            directory.path().join("responses.csv"),
            "hash,local_path\nabc123,../outside.cnf\n",
        )
        .unwrap();
        fs::write(
            &manifest_path,
            r#"
schema_version = 2
repo = "x/y"
release_tag = "v1"

[[corpus]]
name = "responses"
source = "gbd"
extract_to = "corpus"
manifest = "responses.csv"
"#,
        )
        .unwrap();
        let manifest = Manifest::load(&manifest_path).unwrap();

        let error = download_gbd(manifest.find("responses").unwrap(), false)
            .expect_err("traversal must fail before network or filesystem writes");
        assert!(format!("{error:#}").contains("normalized repository-relative path"));
        assert!(!directory.path().join("outside.cnf").exists());
        assert!(!directory.path().join("corpus").exists());
        assert!(corpus_work_directories(directory.path()).is_empty());

        fs::write(
            directory.path().join("responses.csv"),
            "hash,local_path\nabc123,other/outside.cnf\n",
        )
        .unwrap();
        let error = download_gbd(manifest.find("responses").unwrap(), false)
            .expect_err("normalized path outside the corpus destination must fail");
        assert!(format!("{error:#}").contains("escapes corpus destination"));
        assert!(!directory.path().join("other").exists());

        fs::write(
            directory.path().join("responses.csv"),
            "hash,local_path\nabc123,corpus/same.cnf\ndef456,corpus/same.cnf\n",
        )
        .unwrap();
        let error = download_gbd(manifest.find("responses").unwrap(), false)
            .expect_err("duplicate destinations must fail before network writes");
        assert!(format!("{error:#}").contains("repeats local benchmark path"));
        assert!(!directory.path().join("corpus").exists());

        fs::write(
            directory.path().join("responses.csv"),
            "hash,local_path\nabc123,corpus/same.cnf.xz\ndef456,corpus/same.cnf\n",
        )
        .unwrap();
        let error = download_gbd(manifest.find("responses").unwrap(), false)
            .expect_err("a decompressed sibling collision must fail before network writes");
        assert!(format!("{error:#}").contains("same.cnf"));
        assert!(!directory.path().join("corpus").exists());

        #[cfg(unix)]
        {
            let destination = directory.path().join("corpus");
            let outside = directory.path().join("outside");
            fs::create_dir(&destination).unwrap();
            fs::create_dir(&outside).unwrap();
            std::os::unix::fs::symlink(&outside, destination.join("link")).unwrap();
            fs::write(
                directory.path().join("responses.csv"),
                "hash,local_path\nabc123,corpus/link/escaped.cnf\n",
            )
            .unwrap();

            let error = download_gbd(manifest.find("responses").unwrap(), false)
                .expect_err("a pre-existing symlink ancestor must fail before network writes");
            assert!(format!("{error:#}").contains("never a symlink"));
            assert!(!outside.join("escaped.cnf").exists());
        }
    }

    #[test]
    fn campaign_http_assets_require_positive_size_and_lowercase_sha256() {
        let valid_sha = "a".repeat(64);
        let valid = load_inline(&format!(
            r#"
schema_version = 2
repo = "x/y"
release_tag = "v1"

[[corpus]]
name = "asset"
source = "http"
archive = "none"
extract_to = "asset.bin"
url = "https://example.test/asset.bin"
size_bytes = 1
sha256 = "{valid_sha}"
"#
        ))
        .unwrap();
        validate_campaign_corpus_pin(valid.find("asset").unwrap(), &valid)
            .expect("complete HTTP pins must pass");

        for (fields, expected) in [
            ("size_bytes = 1".to_string(), "lowercase SHA-256"),
            (format!(r#"sha256 = "{valid_sha}""#), "positive size"),
            (
                format!("size_bytes = 0\nsha256 = \"{valid_sha}\""),
                "positive size",
            ),
            (
                format!("size_bytes = 1\nsha256 = \"{}\"", "A".repeat(64)),
                "lowercase SHA-256",
            ),
        ] {
            let manifest = load_inline(&format!(
                r#"
schema_version = 2
repo = "x/y"
release_tag = "v1"

[[corpus]]
name = "asset"
source = "http"
archive = "none"
extract_to = "asset.bin"
url = "https://example.test/asset.bin"
{fields}
"#
            ))
            .unwrap();
            let error = validate_campaign_corpus_pin(manifest.find("asset").unwrap(), &manifest)
                .expect_err("incomplete or malformed HTTP pins must fail");
            assert!(
                format!("{error:#}").contains(expected),
                "unexpected error: {error:#}"
            );
        }
    }

    #[test]
    fn campaign_gbd_rows_match_pinned_selection_in_order() {
        let directory = TempDir::new().unwrap();
        let selection = directory.path().join("selection.csv");
        let responses = directory.path().join("responses.csv");
        fs::write(&selection, "hash,isohash2\nabc,first\ndef,second\n").unwrap();
        fs::write(
            &responses,
            "hash,local_path,size_bytes,sha256\n\
             abc,instances/001.cnf.xz,10,aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n\
             def,instances/002.cnf.xz,20,bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n",
        )
        .unwrap();
        let manifest_path = directory.path().join("corpora.toml");
        fs::write(
            &manifest_path,
            r#"
schema_version = 2
repo = "x/y"
release_tag = "v1"

[[corpus]]
name = "selection"
source = "http"
archive = "none"
extract_to = "selection.csv"
url = "https://example.test/selection.csv"
sha256 = "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
size_bytes = 37

[[corpus]]
name = "main"
source = "gbd"
extract_to = "instances"
manifest = "responses.csv"
depends_on = ["selection"]
"#,
        )
        .unwrap();
        let manifest = Manifest::load(&manifest_path).unwrap();
        let corpus = manifest.find("main").unwrap();
        validate_campaign_corpus_pin(corpus, &manifest).unwrap();

        fs::write(&selection, "hash,isohash2\ndef,second\nabc,first\n").unwrap();
        assert!(validate_campaign_corpus_pin(corpus, &manifest)
            .unwrap_err()
            .to_string()
            .contains("do not exactly match"));
    }

    #[test]
    fn parse_uri_list_accepts_unique_https_artifacts() {
        let directory = TempDir::new().unwrap();
        let path = directory.path().join("official.uri");
        fs::write(
            &path,
            "# official selection\nhttps://benchmark-database.de/file/abc123\n\
             https://benchmark-database.de/file/def456\n",
        )
        .unwrap();
        let rows = parse_uri_list(&path, UriListFormat::GbdCnf).unwrap();
        assert_eq!(
            rows.iter().map(|row| row.id.as_str()).collect::<Vec<_>>(),
            vec!["abc123", "def456"]
        );
    }

    #[test]
    fn parse_uri_list_rejects_insecure_or_duplicate_artifacts() {
        let directory = TempDir::new().unwrap();
        let insecure = directory.path().join("insecure.uri");
        fs::write(&insecure, "http://benchmark-database.de/file/abc123\n").unwrap();
        assert!(parse_uri_list(&insecure, UriListFormat::GbdCnf)
            .unwrap_err()
            .to_string()
            .contains("not HTTPS"));

        let duplicate = directory.path().join("duplicate.uri");
        fs::write(
            &duplicate,
            "https://example.test/file/abc123\nhttps://mirror.test/file/abc123\n",
        )
        .unwrap();
        assert!(parse_uri_list(&duplicate, UriListFormat::GbdCnf)
            .unwrap_err()
            .to_string()
            .contains("repeats artifact id"));
    }

    #[test]
    fn parse_uri_list_accepts_pinned_raw_json_rows() {
        let directory = TempDir::new().unwrap();
        let path = directory.path().join("results.tsv");
        fs::write(
            &path,
            "https://example.test/api/results/2/7\t42\t\
             0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef\n",
        )
        .unwrap();
        let rows = parse_uri_list(&path, UriListFormat::RawJson).unwrap();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].id, "2-7");
        assert_eq!(rows[0].expected_size, Some(42));
        assert_eq!(
            rows[0].expected_sha256.as_deref(),
            Some("0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef")
        );
    }

    #[test]
    fn parse_uri_list_rejects_zero_size_or_noncanonical_sha256() {
        let directory = TempDir::new().unwrap();
        let path = directory.path().join("invalid-pins.tsv");
        for pins in [
            format!("0\t{}", "a".repeat(64)),
            format!("1\t{}", "A".repeat(64)),
            "1\tnot-a-sha".to_string(),
        ] {
            fs::write(
                &path,
                format!("https://example.test/api/results/2/7\t{pins}\n"),
            )
            .unwrap();
            let error = parse_uri_list(&path, UriListFormat::RawJson)
                .expect_err("noncanonical response pins must fail");
            assert!(
                format!("{error:#}").contains("positive byte size and canonical lowercase SHA-256")
            );
        }
    }

    #[test]
    fn parse_gbd_manifest_rejects_missing_columns() {
        let dir = TempDir::new().unwrap();
        let path = dir.path().join("manifest.csv");
        fs::write(&path, "filename,size_bytes\nfoo.cnf.xz,42\n").unwrap();
        let err = parse_gbd_manifest(&path).unwrap_err();
        assert!(format!("{err:#}").contains("hash"));
    }

    #[test]
    fn gbd_local_status_counts_present_files() {
        let dir = TempDir::new().unwrap();
        let instances = dir.path().join("instances");
        fs::create_dir(&instances).unwrap();
        let present = instances.join("present.cnf");
        fs::write(&present, b"p cnf 0 0\n").unwrap();
        let absent = instances.join("absent.cnf");
        let manifest = dir.path().join("manifest.csv");
        fs::write(
            &manifest,
            "hash,local_path\nh1,instances/present.cnf\nh2,instances/absent.cnf\n",
        )
        .unwrap();

        let mut c = release_corpus();
        c.source = Source::Gbd;
        c.asset = None;
        c.sha256 = None;
        c.extract_to = "instances".to_string();
        c.manifest = Some("manifest.csv".to_string());
        c.base_dir = dir.path().to_path_buf();
        assert_eq!(c.local_status(), "partial (1/2)");

        fs::write(&absent, b"p cnf 0 0\n").unwrap();
        assert_eq!(c.local_status(), "downloaded (2/2)");
    }

    #[test]
    fn duplicate_gbd_rows_publish_independent_files() {
        let dir = TempDir::new().unwrap();
        let source = dir.path().join("source.cnf.xz");
        let duplicate = dir.path().join("duplicate.cnf.xz");
        fs::write(&source, b"abc").unwrap();
        #[cfg(unix)]
        fs::hard_link(&source, &duplicate).unwrap();
        #[cfg(not(unix))]
        fs::copy(&source, &duplicate).unwrap();

        let corpus = release_corpus();
        let row = GbdRow {
            hash: "same-object".to_string(),
            local_path: duplicate.display().to_string(),
            expected_size: Some(3),
            expected_sha256: Some(
                "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad".to_string(),
            ),
        };
        publish_independent_gbd_duplicate(&corpus, &row, &source, &duplicate).unwrap();
        assert_eq!(fs::read(&duplicate).unwrap(), b"abc");
        #[cfg(unix)]
        assert!(!gbd_artifacts_alias(&source, &duplicate).unwrap());
    }

    #[test]
    fn gbd_row_paths_and_presence() {
        let dir = TempDir::new().unwrap();
        let raw = dir.path().join("x.cnf.xz");
        let decompressed = dir.path().join("x.cnf");
        let row = GbdRow {
            hash: "h".into(),
            local_path: raw.to_string_lossy().into(),
            expected_size: None,
            expected_sha256: None,
        };
        assert_eq!(row.raw_path(), raw);
        assert_eq!(row.decompressed_path(), decompressed);
        assert!(!row.is_present());
        // Present via the decompressed sibling alone (the two-trees case).
        fs::write(&decompressed, b"p cnf 0 0\n").unwrap();
        assert!(row.is_present());
        // Present via the raw .xz alone.
        fs::remove_file(&decompressed).unwrap();
        fs::write(&raw, [0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00]).unwrap();
        assert!(row.is_present());

        // No .xz suffix: raw and decompressed coincide.
        let plain = GbdRow {
            hash: "h".into(),
            local_path: "benchmarks/x/foo.cnf".into(),
            expected_size: None,
            expected_sha256: None,
        };
        assert_eq!(plain.raw_path(), plain.decompressed_path());
    }

    #[test]
    fn is_xz_detects_magic() {
        let dir = TempDir::new().unwrap();
        let xz = dir.path().join("a.xz");
        fs::write(&xz, [0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x01, 0x02]).unwrap();
        assert!(is_xz(&xz).unwrap());
        let plain = dir.path().join("b.cnf");
        fs::write(&plain, b"p cnf 1 1\n").unwrap();
        assert!(!is_xz(&plain).unwrap());
        let tiny = dir.path().join("c");
        fs::write(&tiny, [0xFD, 0x37]).unwrap();
        assert!(!is_xz(&tiny).unwrap());
    }

    #[test]
    fn validate_http_and_git_require_url() {
        for source in ["http", "git"] {
            let body = format!(
                r#"
schema_version = 2
repo = "x/y"
release_tag = "v1"

[[corpus]]
name = "no-url"
source = "{source}"
extract_to = "a"
"#
            );
            let err = load_inline(&body).unwrap_err();
            assert!(format!("{err:#}").contains("url"), "source={source}");
        }
    }

    #[test]
    fn validate_wrap_archive_requires_an_extractable_archive_source() {
        let valid = load_inline(
            r#"
schema_version = 2
repo = "x/y"
release_tag = "v1"

[[corpus]]
name = "wrapped"
source = "http"
url = "https://example.com/multi-root.tar"
extract_to = "benchmarks/wrapped"
wrap_archive = true
"#,
        )
        .expect("wrapped HTTP tar is valid");
        assert!(valid.corpora[0].wrap_archive);

        for (name, source_fields) in [
            (
                "release-tree",
                r#"source = "release"
asset = "release.tar.zst"
sha256 = "00""#,
            ),
            (
                "plain-file",
                r#"source = "http"
url = "https://example.com/results.json"
archive = "none""#,
            ),
            (
                "git-tree",
                r#"source = "git"
url = "https://example.com/repository.git""#,
            ),
            (
                "gbd-tree",
                r#"source = "gbd"
manifest = "benchmarks/gbd.csv""#,
            ),
        ] {
            let body = format!(
                r#"
schema_version = 2
repo = "x/y"
release_tag = "v1"

[[corpus]]
name = "{name}"
{source_fields}
extract_to = "benchmarks/{name}"
wrap_archive = true
"#
            );
            let error = load_inline(&body).expect_err("invalid wrapped source must fail");
            assert!(
                format!("{error:#}").contains("wrap_archive"),
                "unexpected error for {name}: {error:#}"
            );
        }
    }

    // ---------- Corpus accessors ----------

    fn release_corpus() -> Corpus {
        Corpus {
            name: "r".into(),
            groups: Vec::new(),
            depends_on: Vec::new(),
            source: Source::Release,
            extract_to: "benchmarks/foo/bar".into(),
            asset: Some("bar-v1.tar.zst".into()),
            sha256: Some("00".into()),
            size_bytes: Some(1),
            url: None,
            cache_name: None,
            archive: Archive::Tar,
            wrap_archive: false,
            normalize_absolute_archive_symlinks: false,
            depth: None,
            commit: None,
            requires_git_lfs: false,
            allowed_unmapped_gitlinks: Vec::new(),
            manifest: None,
            uri_list_format: UriListFormat::GbdCnf,
            base_dir: PathBuf::new(),
        }
    }

    #[test]
    fn cache_path_release_sits_next_to_extract_dir() {
        let c = release_corpus();
        assert_eq!(
            c.cache_path().unwrap(),
            PathBuf::from("benchmarks/foo/bar-v1.tar.zst")
        );
    }

    #[test]
    fn cache_path_http_default_uses_url_basename() {
        let mut c = release_corpus();
        c.source = Source::Http;
        c.asset = None;
        c.sha256 = None;
        c.url = Some("https://example.com/sub/dl/blob.tar".into());
        c.extract_to = "benchmarks/foo/blob".into();
        assert_eq!(
            c.cache_path().unwrap(),
            PathBuf::from("benchmarks/foo/blob.tar")
        );
    }

    #[test]
    fn cache_path_http_none_archive_is_extract_to_itself() {
        let mut c = release_corpus();
        c.source = Source::Http;
        c.asset = None;
        c.sha256 = None;
        c.url = Some("https://example.com/q.zip".into());
        c.extract_to = "benchmarks/foo/q.zip".into();
        c.archive = Archive::None;
        assert_eq!(
            c.cache_path().unwrap(),
            PathBuf::from("benchmarks/foo/q.zip")
        );
    }

    #[test]
    fn cache_path_git_is_none() {
        let mut c = release_corpus();
        c.source = Source::Git;
        c.asset = None;
        c.sha256 = None;
        c.url = Some("https://github.com/x/y".into());
        assert!(c.cache_path().is_none());
    }

    #[test]
    fn local_status_missing_when_nothing_on_disk() {
        let dir = TempDir::new().unwrap();
        let mut c = release_corpus();
        c.extract_to = dir.path().join("never-extracted").to_string_lossy().into();
        assert_eq!(c.local_status(), "missing");
    }

    #[test]
    fn local_status_requires_pinned_cache_for_extracted_tree() {
        let dir = TempDir::new().unwrap();
        let extract = dir.path().join("here");
        fs::create_dir(&extract).unwrap();
        let mut c = release_corpus();
        c.extract_to = extract.to_string_lossy().into();
        assert_eq!(c.local_status(), "unverified");

        let content = b"x";
        let cache = dir.path().join("bar-v1.tar.zst");
        fs::write(&cache, content).unwrap();
        c.sha256 = Some({
            let mut hasher = Sha256::new();
            hasher.update(content);
            hex(&hasher.finalize())
        });
        assert_eq!(c.local_status(), "extracted");
    }

    #[test]
    fn local_status_distinguishes_downloaded_from_stale() {
        let dir = TempDir::new().unwrap();
        let content = b"hello world";
        let expected = {
            let mut h = Sha256::new();
            h.update(content);
            hex(&h.finalize())
        };
        let cache = dir.path().join("t.tar.zst");
        fs::write(&cache, content).unwrap();

        let mut c = release_corpus();
        c.extract_to = dir.path().join("missing-extract").to_string_lossy().into();
        c.asset = Some("t.tar.zst".into());
        c.sha256 = Some(expected);
        c.size_bytes = Some(content.len() as u64);
        assert_eq!(c.local_status(), "downloaded");

        // Now make the SHA mismatch.
        c.sha256 = Some("0000".into());
        assert_eq!(c.local_status(), "stale");

        // A declared size mismatch is independently stale.
        c.sha256 = None;
        c.size_bytes = Some(content.len() as u64 + 1);
        assert_eq!(c.local_status(), "stale");
    }

    #[test]
    fn verify_enforces_size_pin_without_sha256() {
        let directory = TempDir::new().unwrap();
        let artifact = directory.path().join("results.json");
        fs::write(&artifact, b"short").unwrap();
        let manifest = directory.path().join("corpora.toml");
        fs::write(
            &manifest,
            format!(
                r#"
schema_version = 2
repo = "x/y"
release_tag = "v1"

[[corpus]]
name = "results"
source = "http"
archive = "none"
extract_to = "{}"
url = "https://example.com/results.json"
size_bytes = 6
"#,
                artifact.display()
            ),
        )
        .unwrap();

        let args = VerifyArgs {
            manifest: ManifestArgs {
                manifest: manifest.clone(),
            },
            all: false,
            groups: Vec::new(),
            names: vec!["results".to_string()],
        };
        assert_eq!(run_verify(args).unwrap(), 1);

        fs::write(&artifact, b"length").unwrap();
        let args = VerifyArgs {
            manifest: ManifestArgs { manifest },
            all: false,
            groups: Vec::new(),
            names: vec!["results".to_string()],
        };
        assert_eq!(run_verify(args).unwrap(), 0);
    }

    #[test]
    fn verify_includes_dependency_closure() {
        let directory = TempDir::new().unwrap();
        fs::write(directory.path().join("selected.bin"), b"x").unwrap();
        let manifest = directory.path().join("corpora.toml");
        fs::write(
            &manifest,
            r#"
schema_version = 2
repo = "x/y"
release_tag = "v1"

[[corpus]]
name = "dependency"
source = "http"
archive = "none"
extract_to = "missing-dependency.bin"
url = "https://example.test/dependency.bin"
size_bytes = 1

[[corpus]]
name = "selected"
source = "http"
archive = "none"
extract_to = "selected.bin"
url = "https://example.test/selected.bin"
size_bytes = 1
depends_on = ["dependency"]
"#,
        )
        .unwrap();

        let result = run_verify(VerifyArgs {
            manifest: ManifestArgs { manifest },
            all: false,
            groups: Vec::new(),
            names: vec!["selected".to_string()],
        })
        .unwrap();
        assert_eq!(
            result, 1,
            "a missing dependency must fail explicit selected verification"
        );
    }

    fn create_tar_with_files(directory: &Path, name: &str, files: &[(&str, &str)]) -> PathBuf {
        let source = directory.join(format!("{name}-source"));
        fs::create_dir(&source).expect("create tar source");
        for (relative, contents) in files {
            let path = source.join(relative);
            fs::create_dir_all(path.parent().expect("fixture file parent"))
                .expect("create fixture parent");
            fs::write(path, contents).expect("write fixture file");
        }
        let archive = directory.join(format!("{name}.tar"));
        let status = ProcCommand::new("tar")
            .args(["-cf"])
            .arg(&archive)
            .args(["-C"])
            .arg(&source)
            .arg(".")
            .status()
            .expect("invoke tar");
        assert!(status.success(), "create test tar");
        archive
    }

    fn archive_members(
        entries: impl IntoIterator<Item = (&'static str, ArchiveMemberKind)>,
    ) -> BTreeMap<PathBuf, ArchiveMemberKind> {
        entries
            .into_iter()
            .map(|(path, kind)| (PathBuf::from(path), kind))
            .collect()
    }

    #[test]
    fn archive_safety_normalizes_a_unique_absolute_symlink_suffix() {
        let members = archive_members([
            ("author/solver/src/makefile", ArchiveMemberKind::File),
            (
                "author/solver/src/src/makefile",
                ArchiveMemberKind::Symlink(PathBuf::from(
                    "/organizer/solvers/author/solver/src/makefile",
                )),
            ),
        ]);

        let plan =
            build_archive_safety_plan(&members, ArchiveSymlinkPolicy::NormalizeUniqueInArchive)
                .expect("one in-archive suffix match is safe to normalize");

        assert_eq!(
            plan.symlink_rewrites,
            vec![ArchiveSymlinkRewrite {
                member: PathBuf::from("author/solver/src/src/makefile"),
                archived_target: PathBuf::from("/organizer/solvers/author/solver/src/makefile"),
                materialized_target: PathBuf::from("../makefile"),
                target_is_directory: false,
            }]
        );
    }

    #[test]
    fn archive_safety_rejects_ambiguous_absolute_symlink_suffixes() {
        let members = archive_members([
            ("root/a/file", ArchiveMemberKind::File),
            ("a/file", ArchiveMemberKind::File),
            (
                "root/link",
                ArchiveMemberKind::Symlink(PathBuf::from("/build/root/a/file")),
            ),
        ]);

        let error =
            build_archive_safety_plan(&members, ArchiveSymlinkPolicy::NormalizeUniqueInArchive)
                .expect_err("multiple suffix matches are ambiguous");
        assert!(format!("{error:#}").contains("ambiguous"));
    }

    #[test]
    fn archive_safety_rejects_missing_absolute_symlink_target() {
        let members = archive_members([(
            "root/link",
            ArchiveMemberKind::Symlink(PathBuf::from("/build/missing")),
        )]);

        let error =
            build_archive_safety_plan(&members, ArchiveSymlinkPolicy::NormalizeUniqueInArchive)
                .expect_err("missing absolute target must fail");
        assert!(format!("{error:#}").contains("no in-archive suffix match"));
    }

    #[test]
    fn archive_safety_rejects_relative_symlink_escape() {
        let members = archive_members([(
            "root/link",
            ArchiveMemberKind::Symlink(PathBuf::from("../../outside")),
        )]);

        let error = build_archive_safety_plan(&members, ArchiveSymlinkPolicy::RejectAbsolute)
            .expect_err("relative link may not escape the extraction root");
        assert!(format!("{error:#}").contains("escapes extraction root"));
    }

    #[test]
    fn archive_safety_accepts_safe_relative_symlink() {
        let members = archive_members([
            ("root/target", ArchiveMemberKind::File),
            (
                "root/link",
                ArchiveMemberKind::Symlink(PathBuf::from("target")),
            ),
        ]);

        let plan = build_archive_safety_plan(&members, ArchiveSymlinkPolicy::RejectAbsolute)
            .expect("safe relative in-archive link must pass");
        assert!(plan.symlink_rewrites.is_empty());
    }

    #[test]
    fn archive_member_names_reject_absolute_and_non_normal_paths() {
        for name in ["/absolute", "../escape", "root/../escape", "root//file"] {
            assert!(
                normalized_archive_member_name(name.as_bytes()).is_err(),
                "{name:?} must be rejected before extraction"
            );
        }
        assert_eq!(
            normalized_archive_member_name(b"./root/file").unwrap(),
            Some(PathBuf::from("root/file"))
        );
    }

    fn create_stored_zip_with_files(
        directory: &Path,
        name: &str,
        files: &[(&str, &str)],
    ) -> PathBuf {
        fn append_u16(bytes: &mut Vec<u8>, value: u16) {
            bytes.extend_from_slice(&value.to_le_bytes());
        }
        fn append_u32(bytes: &mut Vec<u8>, value: u32) {
            bytes.extend_from_slice(&value.to_le_bytes());
        }
        fn crc32(bytes: &[u8]) -> u32 {
            let mut crc = u32::MAX;
            for byte in bytes {
                crc ^= u32::from(*byte);
                for _ in 0..8 {
                    crc = if crc & 1 == 0 {
                        crc >> 1
                    } else {
                        (crc >> 1) ^ 0xedb8_8320
                    };
                }
            }
            !crc
        }

        let mut archive_bytes = Vec::new();
        let mut central_entries = Vec::new();
        for (path, contents) in files {
            let name_bytes = path.as_bytes();
            let content_bytes = contents.as_bytes();
            let offset = u32::try_from(archive_bytes.len()).expect("small ZIP fixture");
            let size = u32::try_from(content_bytes.len()).expect("small ZIP fixture");
            let checksum = crc32(content_bytes);

            append_u32(&mut archive_bytes, 0x0403_4b50);
            append_u16(&mut archive_bytes, 20);
            append_u16(&mut archive_bytes, 0);
            append_u16(&mut archive_bytes, 0);
            append_u16(&mut archive_bytes, 0);
            append_u16(&mut archive_bytes, 0);
            append_u32(&mut archive_bytes, checksum);
            append_u32(&mut archive_bytes, size);
            append_u32(&mut archive_bytes, size);
            append_u16(
                &mut archive_bytes,
                u16::try_from(name_bytes.len()).expect("small ZIP path"),
            );
            append_u16(&mut archive_bytes, 0);
            archive_bytes.extend_from_slice(name_bytes);
            archive_bytes.extend_from_slice(content_bytes);
            central_entries.push((name_bytes, size, checksum, offset));
        }

        let central_offset = u32::try_from(archive_bytes.len()).expect("small ZIP fixture");
        for (name_bytes, size, checksum, offset) in &central_entries {
            append_u32(&mut archive_bytes, 0x0201_4b50);
            append_u16(&mut archive_bytes, 20);
            append_u16(&mut archive_bytes, 20);
            append_u16(&mut archive_bytes, 0);
            append_u16(&mut archive_bytes, 0);
            append_u16(&mut archive_bytes, 0);
            append_u16(&mut archive_bytes, 0);
            append_u32(&mut archive_bytes, *checksum);
            append_u32(&mut archive_bytes, *size);
            append_u32(&mut archive_bytes, *size);
            append_u16(
                &mut archive_bytes,
                u16::try_from(name_bytes.len()).expect("small ZIP path"),
            );
            append_u16(&mut archive_bytes, 0);
            append_u16(&mut archive_bytes, 0);
            append_u16(&mut archive_bytes, 0);
            append_u16(&mut archive_bytes, 0);
            append_u32(&mut archive_bytes, 0);
            append_u32(&mut archive_bytes, *offset);
            archive_bytes.extend_from_slice(name_bytes);
        }
        let central_size =
            u32::try_from(archive_bytes.len()).expect("small ZIP fixture") - central_offset;
        let entry_count = u16::try_from(central_entries.len()).expect("small ZIP fixture");
        append_u32(&mut archive_bytes, 0x0605_4b50);
        append_u16(&mut archive_bytes, 0);
        append_u16(&mut archive_bytes, 0);
        append_u16(&mut archive_bytes, entry_count);
        append_u16(&mut archive_bytes, entry_count);
        append_u32(&mut archive_bytes, central_size);
        append_u32(&mut archive_bytes, central_offset);
        append_u16(&mut archive_bytes, 0);

        let archive = directory.join(format!("{name}.zip"));
        fs::write(&archive, archive_bytes).expect("write ZIP fixture");
        archive
    }

    fn http_archive_corpus(
        archive: &Path,
        extract_to: &Path,
        format: Archive,
        wrap_archive: bool,
    ) -> Corpus {
        let archive_bytes = fs::read(archive).expect("read archive fixture");
        let mut corpus = release_corpus();
        corpus.name = "http-archive".into();
        corpus.source = Source::Http;
        corpus.asset = None;
        corpus.url = Some("https://example.invalid/archive".into());
        corpus.cache_name = Some(
            archive
                .file_name()
                .expect("archive basename")
                .to_string_lossy()
                .into_owned(),
        );
        corpus.sha256 = Some(sha256_bytes(&archive_bytes));
        corpus.size_bytes = Some(archive_bytes.len() as u64);
        corpus.archive = format;
        corpus.wrap_archive = wrap_archive;
        corpus.extract_to = extract_to.to_string_lossy().into_owned();
        corpus
    }

    fn corpus_work_directories(parent: &Path) -> Vec<PathBuf> {
        fs::read_dir(parent)
            .expect("read test directory")
            .map(|entry| entry.expect("read test entry").path())
            .filter(|path| {
                path.file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| name.starts_with(".ay-corpus-"))
            })
            .collect()
    }

    fn sha256_bytes(bytes: &[u8]) -> String {
        let mut hasher = Sha256::new();
        hasher.update(bytes);
        hex(&hasher.finalize())
    }

    #[test]
    fn bad_download_sha_preserves_last_good_cache() {
        let directory = TempDir::new().unwrap();
        let destination = directory.path().join("corpus.tar");
        fs::write(&destination, b"last-good").unwrap();
        let expected = sha256_bytes(b"expected-download");

        let error = download_file_atomically(
            "test-corpus",
            &destination,
            Some(&expected),
            None,
            |staging| {
                fs::write(staging, b"bad-download").context("write injected bad download")?;
                Ok(())
            },
        )
        .expect_err("bad SHA must reject the staged download");

        assert!(format!("{error:#}").contains("SHA256 mismatch"));
        assert_eq!(fs::read(&destination).unwrap(), b"last-good");
        assert!(corpus_work_directories(directory.path()).is_empty());
    }

    #[test]
    fn bad_download_size_preserves_last_good_cache() {
        let directory = TempDir::new().unwrap();
        let destination = directory.path().join("results.json");
        fs::write(&destination, b"last-good").unwrap();

        let error =
            download_file_atomically("test-results", &destination, None, Some(12), |staging| {
                fs::write(staging, b"short").context("write injected short download")?;
                Ok(())
            })
            .expect_err("bad size must reject the staged download");

        assert!(format!("{error:#}").contains("size mismatch"));
        assert_eq!(fs::read(&destination).unwrap(), b"last-good");
        assert!(corpus_work_directories(directory.path()).is_empty());
    }

    #[test]
    fn interrupted_http_download_resumes_across_invocations() {
        let directory = TempDir::new().unwrap();
        let destination = directory.path().join("corpus.tar");
        let partial = download_partial_path(&destination).unwrap();
        fs::write(&destination, b"last-good").unwrap();
        let expected = b"first-second";
        let expected_sha256 = sha256_bytes(expected);

        let error = download_file_with_resume(
            "test-corpus",
            &destination,
            Some(&expected_sha256),
            Some(expected.len() as u64),
            |partial| {
                fs::write(partial, b"first-").context("write interrupted download")?;
                bail!("injected connection failure")
            },
        )
        .expect_err("interrupted download must fail");

        assert!(format!("{error:#}").contains("partial retained for retry"));
        assert_eq!(fs::read(&destination).unwrap(), b"last-good");
        assert_eq!(fs::read(&partial).unwrap(), b"first-");

        download_file_with_resume(
            "test-corpus",
            &destination,
            Some(&expected_sha256),
            Some(expected.len() as u64),
            |partial| {
                let mut bytes = fs::read(partial).context("read retained partial")?;
                assert_eq!(bytes, b"first-");
                bytes.extend_from_slice(b"second");
                fs::write(partial, bytes).context("finish resumed download")?;
                Ok(())
            },
        )
        .expect("resumed download must publish");

        assert_eq!(fs::read(&destination).unwrap(), expected);
        assert!(!partial.exists());
    }

    #[test]
    fn invalid_completed_http_download_drops_poisoned_partial() {
        let directory = TempDir::new().unwrap();
        let destination = directory.path().join("corpus.tar");
        let partial = download_partial_path(&destination).unwrap();
        fs::write(&destination, b"last-good").unwrap();
        let expected_sha256 = sha256_bytes(b"expected");

        let error = download_file_with_resume(
            "test-corpus",
            &destination,
            Some(&expected_sha256),
            None,
            |partial| {
                fs::write(partial, b"wrong").context("write invalid completed download")?;
                Ok(())
            },
        )
        .expect_err("invalid completed download must fail");

        assert!(format!("{error:#}").contains("SHA256 mismatch"));
        assert_eq!(fs::read(&destination).unwrap(), b"last-good");
        assert!(!partial.exists());
    }

    #[test]
    fn verify_command_rejects_byte_mutated_materialized_http_tar() {
        let directory = TempDir::new().unwrap();
        let archive = create_tar_with_files(
            directory.path(),
            "wrapped-integrity",
            &[("benchmarks/a.cnf", "original"), ("README", "fixture")],
        );
        let destination = directory.path().join("materialized");
        extract_into_place(
            &archive,
            Archive::Tar,
            &destination,
            ExtractionLayout::WrappedDirectory,
            ArchiveSymlinkPolicy::RejectAbsolute,
            false,
        )
        .expect("extract test archive");
        let corpus = http_archive_corpus(&archive, &destination, Archive::Tar, true);
        let manifest_path = directory.path().join("corpora.toml");
        Manifest {
            schema_version: 2,
            repo: "x/y".into(),
            release_tag: "v1".into(),
            corpora: vec![corpus],
        }
        .save(&manifest_path)
        .expect("save test manifest");

        let verify = || {
            run_verify(VerifyArgs {
                manifest: ManifestArgs {
                    manifest: manifest_path.clone(),
                },
                all: true,
                groups: Vec::new(),
                names: Vec::new(),
            })
            .expect("verification command")
        };
        assert_eq!(verify(), 0, "freshly extracted tree must verify");

        fs::write(destination.join("benchmarks/a.cnf"), "mutated!").unwrap();
        assert_eq!(
            verify(),
            1,
            "a same-length materialized file mutation must be rejected"
        );
        #[cfg(unix)]
        {
            fs::remove_file(destination.join("benchmarks/a.cnf")).unwrap();
            std::os::unix::fs::symlink("../../outside", destination.join("benchmarks/a.cnf"))
                .unwrap();
            assert_eq!(
                verify(),
                1,
                "a materialized symlink must be rejected without following it"
            );
        }
        assert!(corpus_work_directories(directory.path()).is_empty());
    }

    #[cfg(unix)]
    #[test]
    fn verify_command_compares_archived_symlink_targets_without_following_them() {
        use std::os::unix::fs::symlink;

        let directory = TempDir::new().unwrap();
        let source = directory.path().join("symlink-source");
        fs::create_dir(&source).unwrap();
        fs::write(source.join("target"), "fixture").unwrap();
        symlink("target", source.join("relative-link")).unwrap();
        symlink("/organizer/build/target", source.join("absolute-link")).unwrap();

        let archive = directory.path().join("symlink-integrity.tar");
        let status = ProcCommand::new("tar")
            .args(["-cf"])
            .arg(&archive)
            .args(["-C"])
            .arg(&source)
            .arg(".")
            .status()
            .expect("invoke tar");
        assert!(status.success(), "create symlink test tar");

        let destination = directory.path().join("materialized");
        extract_into_place(
            &archive,
            Archive::Tar,
            &destination,
            ExtractionLayout::WrappedDirectory,
            ArchiveSymlinkPolicy::NormalizeUniqueInArchive,
            false,
        )
        .expect("extract symlink test archive");
        let mut corpus = http_archive_corpus(&archive, &destination, Archive::Tar, true);
        corpus.normalize_absolute_archive_symlinks = true;
        verify_local_corpus(&corpus, true)
            .expect("exact archived symlinks must verify without being followed");

        fs::remove_file(destination.join("relative-link")).unwrap();
        symlink("different-target", destination.join("relative-link")).unwrap();
        let error = verify_local_corpus(&corpus, true)
            .expect_err("a changed materialized symlink target must be rejected");
        assert!(format!("{error:#}").contains("different-target"));
        assert!(corpus_work_directories(directory.path()).is_empty());
    }

    #[test]
    fn require_installed_integrity_handles_single_root_zip_and_missing_files() {
        let directory = TempDir::new().unwrap();
        let archive = create_stored_zip_with_files(
            directory.path(),
            "single-root-integrity",
            &[
                ("zip-corpus/nested/input.smt2", "(check-sat)"),
                ("zip-corpus/README", "fixture"),
            ],
        );
        let destination = directory.path().join("zip-corpus");
        extract_into_place(
            &archive,
            Archive::Zip,
            &destination,
            ExtractionLayout::ArchiveRootInParent,
            ArchiveSymlinkPolicy::RejectAbsolute,
            false,
        )
        .expect("extract ZIP fixture");
        let corpus = http_archive_corpus(&archive, &destination, Archive::Zip, false);

        verify_local_corpus(&corpus, true).expect("correct materialized ZIP tree must verify");
        fs::remove_file(destination.join("nested/input.smt2")).unwrap();
        let error = verify_local_corpus(&corpus, true)
            .expect_err("missing materialized ZIP entry must be rejected");
        assert!(format!("{error:#}").contains("missing nested/input.smt2"));
        assert!(corpus_work_directories(directory.path()).is_empty());
    }

    #[test]
    fn single_root_tar_installs_only_the_expected_directory() {
        let directory = TempDir::new().unwrap();
        let archive = create_tar_with_files(
            directory.path(),
            "single-root",
            &[("mznc2025_probs/atsp/model.mzn", "model")],
        );
        let destination = directory.path().join("mznc2025_probs");

        extract_into_place(
            &archive,
            Archive::Tar,
            &destination,
            ExtractionLayout::ArchiveRootInParent,
            ArchiveSymlinkPolicy::RejectAbsolute,
            false,
        )
        .expect("extract expected single-root archive");

        assert_eq!(
            fs::read_to_string(destination.join("atsp/model.mzn")).unwrap(),
            "model"
        );
        assert!(corpus_work_directories(directory.path()).is_empty());
    }

    #[test]
    fn wrong_single_archive_root_preserves_existing_tree() {
        let directory = TempDir::new().unwrap();
        let archive = create_tar_with_files(
            directory.path(),
            "wrong-root",
            &[("unexpected/file.txt", "replacement")],
        );
        let destination = directory.path().join("expected");
        fs::create_dir(&destination).unwrap();
        fs::write(destination.join("keep.txt"), "last-good").unwrap();

        let error = extract_into_place(
            &archive,
            Archive::Tar,
            &destination,
            ExtractionLayout::ArchiveRootInParent,
            ArchiveSymlinkPolicy::RejectAbsolute,
            true,
        )
        .expect_err("wrong archive root must fail before replacing destination");

        assert!(format!("{error:#}").contains("does not match"));
        assert_eq!(
            fs::read_to_string(destination.join("keep.txt")).unwrap(),
            "last-good"
        );
        assert!(corpus_work_directories(directory.path()).is_empty());
    }

    #[test]
    fn extraction_failure_preserves_existing_tree_for_both_layouts() {
        for (name, layout) in [
            ("single", ExtractionLayout::ArchiveRootInParent),
            ("wrapped", ExtractionLayout::WrappedDirectory),
        ] {
            let directory = TempDir::new().unwrap();
            let destination = directory.path().join(name);
            fs::create_dir(&destination).unwrap();
            fs::write(destination.join("keep.txt"), "last-good").unwrap();

            let error = extract_transactionally(&destination, layout, true, |staging| {
                fs::write(staging.join("partial"), "partial")
                    .context("write injected partial extraction")?;
                bail!("injected extraction failure");
            })
            .expect_err("injected extraction failure must propagate");

            assert!(format!("{error:#}").contains("injected extraction failure"));
            assert_eq!(
                fs::read_to_string(destination.join("keep.txt")).unwrap(),
                "last-good"
            );
            assert!(corpus_work_directories(directory.path()).is_empty());
        }
    }

    #[test]
    fn wrapped_tar_installs_every_archive_root_inside_exact_destination() {
        let directory = TempDir::new().unwrap();
        let archive = create_tar_with_files(
            directory.path(),
            "multi-root",
            &[
                ("PB24/legacy.opb", "legacy"),
                ("PB25/current.opb", "current"),
                ("README.txt", "selection"),
            ],
        );
        let destination = directory.path().join("selected-PB25");

        extract_into_place(
            &archive,
            Archive::Tar,
            &destination,
            ExtractionLayout::WrappedDirectory,
            ArchiveSymlinkPolicy::RejectAbsolute,
            false,
        )
        .expect("extract wrapped archive");

        assert_eq!(
            fs::read_to_string(destination.join("PB24/legacy.opb")).unwrap(),
            "legacy"
        );
        assert_eq!(
            fs::read_to_string(destination.join("PB25/current.opb")).unwrap(),
            "current"
        );
        assert_eq!(
            fs::read_to_string(destination.join("README.txt")).unwrap(),
            "selection"
        );
        assert!(
            !directory.path().join("PB24").exists(),
            "archive roots must not spill into the destination parent"
        );
        assert!(corpus_work_directories(directory.path()).is_empty());
    }

    #[test]
    fn forced_wrapped_tar_replaces_tree_and_removes_stale_contents() {
        let directory = TempDir::new().unwrap();
        let first = create_tar_with_files(
            directory.path(),
            "first",
            &[("PB24/old.opb", "old"), ("PB25/selected.opb", "first")],
        );
        let second = create_tar_with_files(
            directory.path(),
            "second",
            &[("PB26/selected.opb", "second")],
        );
        let destination = directory.path().join("selected");
        extract_into_place(
            &first,
            Archive::Tar,
            &destination,
            ExtractionLayout::WrappedDirectory,
            ArchiveSymlinkPolicy::RejectAbsolute,
            false,
        )
        .expect("initial extraction");
        fs::write(destination.join("stale-from-previous-run"), "stale").unwrap();

        extract_into_place(
            &second,
            Archive::Tar,
            &destination,
            ExtractionLayout::WrappedDirectory,
            ArchiveSymlinkPolicy::RejectAbsolute,
            true,
        )
        .expect("forced replacement");

        assert_eq!(
            fs::read_to_string(destination.join("PB26/selected.opb")).unwrap(),
            "second"
        );
        assert!(!destination.join("PB24").exists());
        assert!(!destination.join("PB25").exists());
        assert!(!destination.join("stale-from-previous-run").exists());
        assert!(corpus_work_directories(directory.path()).is_empty());
    }

    // ---------- Round-trip ----------

    #[test]
    fn round_trip_preserves_corpora() {
        let body = r#"
schema_version = 2
repo = "alabsystems/ay"
release_tag = "corpora-v1"

[[corpus]]
name = "rel"
extract_to = "benchmarks/rel"
asset = "rel-v1.tar.zst"
sha256 = "deadbeef"
size_bytes = 9

[[corpus]]
name = "g"
source = "git"
extract_to = "benchmarks/g"
url = "https://example.com/x/y"
"#;
        let dir = TempDir::new().unwrap();
        let path = dir.path().join("c.toml");
        fs::write(&path, body).unwrap();
        let m1 = Manifest::load(&path).unwrap();
        m1.save(&path).unwrap();
        let m2 = Manifest::load(&path).unwrap();
        assert_eq!(m1.corpora.len(), m2.corpora.len());
        for (a, b) in m1.corpora.iter().zip(m2.corpora.iter()) {
            assert_eq!(a.name, b.name);
            assert_eq!(a.source, b.source);
            assert_eq!(a.url, b.url);
            assert_eq!(a.asset, b.asset);
            assert_eq!(a.sha256, b.sha256);
            assert_eq!(a.extract_to, b.extract_to);
            assert_eq!(a.wrap_archive, b.wrap_archive);
        }
    }

    // ---------- Pure helpers ----------

    #[test]
    fn hex_encodes_bytes() {
        assert_eq!(hex(&[0u8]), "00");
        assert_eq!(hex(&[0xff]), "ff");
        assert_eq!(hex(&[0xde, 0xad, 0xbe, 0xef]), "deadbeef");
    }

    #[test]
    fn human_bytes_handles_units() {
        assert_eq!(human_bytes(0), "0 B");
        assert_eq!(human_bytes(1023), "1023 B");
        assert_eq!(human_bytes(1024), "1.0 KB");
        assert_eq!(human_bytes(1024 * 1024), "1.0 MB");
        assert_eq!(human_bytes(1024u64.pow(3)), "1.0 GB");
    }

    #[cfg(unix)]
    #[test]
    fn tool_probe_rejects_non_executable_regular_files() {
        use std::os::unix::fs::PermissionsExt as _;

        let directory = TempDir::new().unwrap();
        let path = directory.path().join("tool");
        fs::write(&path, "#!/bin/sh\n").unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o644)).unwrap();
        assert!(!is_executable_file(&path));
        fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).unwrap();
        assert!(is_executable_file(&path));
    }

    #[test]
    fn select_all_xor_explicit_names() {
        let m = load_inline(
            r#"
schema_version = 2
repo = "x/y"
release_tag = "v1"

[[corpus]]
name = "a"
asset = "a.tar.zst"
extract_to = "a"
sha256 = "00"

[[corpus]]
name = "b"
asset = "b.tar.zst"
extract_to = "b"
sha256 = "00"
"#,
        )
        .unwrap();

        assert_eq!(m.select(&[], true, &[]).unwrap().len(), 2);
        let one = m.select(&["a".into()], false, &[]).unwrap();
        assert_eq!(one.len(), 1);
        assert_eq!(one[0].name, "a");

        assert!(m.select(&["a".into()], true, &[]).is_err());
        assert!(m.select(&[], false, &[]).is_err());
        assert!(m.select(&["missing".into()], false, &[]).is_err());
    }

    #[test]
    fn dependencies_are_validated_and_ordered_before_requested_assets() {
        let manifest = load_inline(
            r#"
schema_version = 2
repo = "x/y"
release_tag = "v1"

[[corpus]]
name = "manifest"
source = "http"
archive = "none"
url = "https://example.invalid/selection.uri"
extract_to = "selection.uri"

[[corpus]]
name = "instances"
source = "uri-list"
extract_to = "instances"
manifest = "selection.uri"
depends_on = ["manifest"]
"#,
        )
        .unwrap();
        let selected = manifest
            .select(&["instances".to_string()], false, &[])
            .unwrap();
        let ordered = manifest.dependency_order(&selected).unwrap();
        assert_eq!(
            ordered
                .iter()
                .map(|corpus| corpus.name.as_str())
                .collect::<Vec<_>>(),
            vec!["manifest", "instances"]
        );

        let cyclic = load_inline(
            r#"
schema_version = 2
repo = "x/y"
release_tag = "v1"

[[corpus]]
name = "a"
source = "git"
url = "https://example.invalid/a"
extract_to = "a"
depends_on = ["b"]

[[corpus]]
name = "b"
source = "git"
url = "https://example.invalid/b"
extract_to = "b"
depends_on = ["a"]
"#,
        )
        .unwrap_err();
        assert!(format!("{cyclic:#}").contains("dependency cycle"));
    }

    #[test]
    fn campaign_asset_manifest_covers_the_repository_catalog() {
        let repository = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let code = run_campaign_audit(CampaignAuditArgs {
            assets: repository.join(DEFAULT_CAMPAIGN_ASSETS),
            catalog: repository.join(DEFAULT_CAMPAIGN_CATALOG),
            manifest: ManifestArgs {
                manifest: repository.join(DEFAULT_MANIFEST),
            },
            require_installed: false,
            json: false,
        })
        .expect("repository campaign assets must validate");
        assert_eq!(code, 0);
    }

    struct GitCheckoutFixture {
        _directory: TempDir,
        checkout: PathBuf,
        corpus: Corpus,
    }

    fn test_git(repository: &Path, args: &[&str]) {
        let output = ProcCommand::new("git")
            .arg("-C")
            .arg(repository)
            .args(args)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "git {} failed in {}: {}",
            args.join(" "),
            repository.display(),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    fn test_git_stdout(repository: &Path, args: &[&str]) -> String {
        let output = ProcCommand::new("git")
            .arg("-C")
            .arg(repository)
            .args(args)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "git {} failed in {}: {}",
            args.join(" "),
            repository.display(),
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout).unwrap().trim().to_string()
    }

    fn init_test_git_repository(repository: &Path) {
        fs::create_dir_all(repository).unwrap();
        test_git(repository, &["init", "--quiet", "--initial-branch=main"]);
        test_git(
            repository,
            &["config", "user.email", "corpus-test@example.invalid"],
        );
        test_git(repository, &["config", "user.name", "Corpus Test"]);
    }

    fn test_git_corpus(checkout: &Path, url: &str) -> Corpus {
        let mut corpus = release_corpus();
        corpus.source = Source::Git;
        corpus.asset = None;
        corpus.sha256 = None;
        corpus.size_bytes = None;
        corpus.url = Some(url.to_string());
        corpus.extract_to = checkout.to_string_lossy().to_string();
        corpus.commit = Some(test_git_stdout(checkout, &["rev-parse", "HEAD"]));
        corpus
    }

    fn git_checkout_fixture() -> GitCheckoutFixture {
        let directory = TempDir::new().unwrap();
        let checkout = directory.path().join("checkout");
        init_test_git_repository(&checkout);
        fs::create_dir(checkout.join("nested")).unwrap();
        fs::write(checkout.join("asset.txt"), "pinned\n").unwrap();
        fs::write(checkout.join("nested/data.txt"), "nested\n").unwrap();
        fs::write(checkout.join(".gitignore"), "ignored.tmp\n").unwrap();
        test_git(&checkout, &["add", "."]);
        test_git(&checkout, &["commit", "--quiet", "-m", "pin"]);
        let url = "https://example.invalid/repository.git";
        test_git(&checkout, &["remote", "add", "origin", url]);
        let corpus = test_git_corpus(&checkout, url);
        GitCheckoutFixture {
            _directory: directory,
            checkout,
            corpus,
        }
    }

    #[test]
    fn git_checkout_verification_requires_exact_clean_pin() {
        let fixture = git_checkout_fixture();
        assert!(verify_git_checkout(&fixture.corpus).is_ok());
        fs::write(fixture.checkout.join("asset.txt"), "modified\n").unwrap();
        assert!(verify_git_checkout(&fixture.corpus)
            .unwrap_err()
            .to_string()
            .contains("local modifications"));
    }

    #[test]
    fn forced_git_download_verifies_staging_before_replacing_destination() {
        let directory = TempDir::new().unwrap();
        let source = directory.path().join("source");
        init_test_git_repository(&source);
        fs::write(source.join("asset.txt"), "source\n").unwrap();
        test_git(&source, &["add", "asset.txt"]);
        test_git(&source, &["commit", "--quiet", "-m", "base"]);
        let gitlink_object = test_git_stdout(&source, &["rev-parse", "HEAD"]);
        let cache_info = format!("160000,{gitlink_object},legacy/unmapped");
        test_git(
            &source,
            &["update-index", "--add", "--cacheinfo", &cache_info],
        );
        test_git(&source, &["commit", "--quiet", "-m", "unmapped gitlink"]);

        let destination = directory.path().join("destination");
        fs::create_dir(&destination).unwrap();
        fs::write(destination.join("last-good.txt"), "last-good\n").unwrap();

        let mut corpus = release_corpus();
        corpus.name = "staged-git".into();
        corpus.source = Source::Git;
        corpus.asset = None;
        corpus.sha256 = None;
        corpus.size_bytes = None;
        corpus.url = Some(source.to_string_lossy().into_owned());
        corpus.extract_to = destination.to_string_lossy().into_owned();
        corpus.commit = Some(test_git_stdout(&source, &["rev-parse", "HEAD"]));

        let error = download_git(&corpus, true)
            .expect_err("invalid staged checkout must not replace the prior destination");
        assert!(format!("{error:#}").contains("verify staged Git checkout before publication"));
        assert!(format!("{error:#}").contains("actual unmapped mode-160000 entries"));
        assert_eq!(
            fs::read_to_string(destination.join("last-good.txt")).unwrap(),
            "last-good\n"
        );
        assert!(!destination.join(".git").exists());
        assert!(corpus_work_directories(directory.path()).is_empty());
    }

    #[test]
    fn git_checkout_verification_requires_exact_non_symlink_root() {
        let fixture = git_checkout_fixture();
        let mut nested = fixture.corpus.clone();
        nested.extract_to = fixture
            .checkout
            .join("nested")
            .to_string_lossy()
            .to_string();
        let error = verify_git_checkout(&nested).unwrap_err();
        assert!(format!("{error:#}").contains("not the exact git repository root"));

        #[cfg(unix)]
        {
            let alias = fixture._directory.path().join("checkout-alias");
            std::os::unix::fs::symlink(&fixture.checkout, &alias).unwrap();
            let mut symlinked = fixture.corpus.clone();
            symlinked.extract_to = alias.to_string_lossy().to_string();
            let error = verify_git_checkout(&symlinked).unwrap_err();
            assert!(format!("{error:#}").contains("non-symlink directory"));
        }
    }

    #[test]
    fn git_checkout_verification_rejects_hidden_index_and_config_states() {
        let fixture = git_checkout_fixture();

        test_git(
            &fixture.checkout,
            &["update-index", "--skip-worktree", "asset.txt"],
        );
        let error = verify_git_checkout(&fixture.corpus).unwrap_err();
        assert!(format!("{error:#}").contains("unsupported index state"));
        test_git(
            &fixture.checkout,
            &["update-index", "--no-skip-worktree", "asset.txt"],
        );

        test_git(
            &fixture.checkout,
            &["update-index", "--assume-unchanged", "asset.txt"],
        );
        let error = verify_git_checkout(&fixture.corpus).unwrap_err();
        assert!(format!("{error:#}").contains("unsupported index state"));
        test_git(
            &fixture.checkout,
            &["update-index", "--no-assume-unchanged", "asset.txt"],
        );

        test_git(
            &fixture.checkout,
            &["config", "core.sparseCheckout", "true"],
        );
        let error = verify_git_checkout(&fixture.corpus).unwrap_err();
        assert!(format!("{error:#}").contains("unsupported sparse checkout"));
        test_git(
            &fixture.checkout,
            &["config", "core.sparseCheckout", "false"],
        );

        test_git(
            &fixture.checkout,
            &["config", "remote.origin.promisor", "true"],
        );
        let error = verify_git_checkout(&fixture.corpus).unwrap_err();
        assert!(format!("{error:#}").contains("partial/promisor"));
        test_git(
            &fixture.checkout,
            &["config", "--unset", "remote.origin.promisor"],
        );

        fs::write(fixture.checkout.join("ignored.tmp"), "hidden\n").unwrap();
        let error = verify_git_checkout(&fixture.corpus).unwrap_err();
        assert!(format!("{error:#}").contains("ignored extra files"));
        fs::remove_file(fixture.checkout.join("ignored.tmp")).unwrap();

        fs::write(fixture.checkout.join("untracked.txt"), "extra\n").unwrap();
        let error = verify_git_checkout(&fixture.corpus).unwrap_err();
        assert!(format!("{error:#}").contains("untracked files"));
    }

    #[test]
    fn git_checkout_verification_rejects_unmerged_index() {
        let mut fixture = git_checkout_fixture();
        test_git(&fixture.checkout, &["checkout", "-q", "-b", "other"]);
        fs::write(fixture.checkout.join("asset.txt"), "other\n").unwrap();
        test_git(&fixture.checkout, &["commit", "-qam", "other"]);
        test_git(&fixture.checkout, &["checkout", "-q", "main"]);
        fs::write(fixture.checkout.join("asset.txt"), "main\n").unwrap();
        test_git(&fixture.checkout, &["commit", "-qam", "main"]);
        fixture.corpus.commit = Some(test_git_stdout(&fixture.checkout, &["rev-parse", "HEAD"]));
        let output = ProcCommand::new("git")
            .arg("-C")
            .arg(&fixture.checkout)
            .args(["merge", "other"])
            .output()
            .unwrap();
        assert!(!output.status.success());

        let error = verify_git_checkout(&fixture.corpus).unwrap_err();
        assert!(format!("{error:#}").contains("unmerged index entries"));
    }

    #[test]
    fn git_checkout_verification_rejects_missing_current_tree_object() {
        let fixture = git_checkout_fixture();
        let object = test_git_stdout(&fixture.checkout, &["rev-parse", "HEAD:asset.txt"]);
        let git_directory = test_git_stdout(&fixture.checkout, &["rev-parse", "--git-dir"]);
        let object_path = fixture
            .checkout
            .join(git_directory)
            .join("objects")
            .join(&object[..2])
            .join(&object[2..]);
        fs::remove_file(object_path).unwrap();

        let error = verify_git_checkout(&fixture.corpus).unwrap_err();
        assert!(format!("{error:#}").contains("missing or corrupt objects"));
    }

    #[test]
    fn git_checkout_verification_rejects_unresolved_lfs_pointer() {
        let mut fixture = git_checkout_fixture();
        fs::write(
            fixture.checkout.join(".gitattributes"),
            "large.bin filter=lfs diff=lfs merge=lfs -text\n",
        )
        .unwrap();
        fs::write(
            fixture.checkout.join("large.bin"),
            "version https://git-lfs.github.com/spec/v1\n\
             oid sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef\n\
             size 123\n",
        )
        .unwrap();
        test_git(&fixture.checkout, &["add", ".gitattributes", "large.bin"]);
        test_git(
            &fixture.checkout,
            &["commit", "--quiet", "-m", "lfs pointer"],
        );
        fixture.corpus.commit = Some(test_git_stdout(&fixture.checkout, &["rev-parse", "HEAD"]));

        let error = verify_git_checkout(&fixture.corpus).unwrap_err();
        assert!(format!("{error:#}").contains("only an unresolved pointer"));
    }

    #[test]
    fn git_lfs_attributes_without_pointer_blobs_do_not_require_git_lfs() {
        let mut fixture = git_checkout_fixture();
        fs::write(
            fixture.checkout.join(".gitattributes"),
            "*.mat filter=lfs diff=lfs merge=lfs -text\n",
        )
        .unwrap();
        fs::write(
            fixture.checkout.join("small.mat"),
            "ordinary tracked matrix fixture\n",
        )
        .unwrap();
        fs::write(fixture.checkout.join("large.mat"), vec![0x5a; 4096]).unwrap();
        test_git(
            &fixture.checkout,
            &["add", ".gitattributes", "small.mat", "large.mat"],
        );
        test_git(
            &fixture.checkout,
            &["commit", "--quiet", "-m", "ordinary attributed blobs"],
        );
        fixture.corpus.commit = Some(test_git_stdout(&fixture.checkout, &["rev-parse", "HEAD"]));

        verify_git_checkout(&fixture.corpus)
            .expect("LFS attributes alone must not require the git-lfs executable");
        fixture.corpus.requires_git_lfs = true;
        let error = verify_git_checkout(&fixture.corpus).unwrap_err();
        assert!(format!("{error:#}").contains("does not match the pinned tree"));
    }

    #[test]
    fn git_lfs_attribute_scan_handles_large_path_sets_without_bidirectional_pipe() {
        use std::io::Write as _;

        let fixture = git_checkout_fixture();
        fs::write(
            fixture.checkout.join(".gitattributes"),
            "synthetic/** filter=lfs\n",
        )
        .unwrap();
        test_git(&fixture.checkout, &["add", ".gitattributes"]);
        test_git(
            &fixture.checkout,
            &["commit", "--quiet", "-m", "attribute pathspec"],
        );
        let object = test_git_stdout(&fixture.checkout, &["rev-parse", "HEAD:asset.txt"]);
        let mut child = ProcCommand::new("git")
            .arg("-C")
            .arg(&fixture.checkout)
            .args(["update-index", "-z", "--index-info"])
            .stdin(Stdio::piped())
            .spawn()
            .unwrap();
        {
            let mut stdin = child.stdin.take().unwrap();
            for number in 0..4096 {
                write!(
                    stdin,
                    "100644 {object}\t\
                     synthetic/long/path/for/pipe-capacity-regression/{number:08}/asset.bin\0"
                )
                .unwrap();
            }
        }
        assert!(child.wait().unwrap().success());
        let index = verified_git_output(
            &fixture.checkout,
            &["ls-files", "--stage", "-v", "-z"],
            "test index",
        )
        .unwrap();
        let index = parse_verified_git_index(&fixture.checkout, &index, "pipe regression").unwrap();
        verify_git_lfs_materialization(&fixture.checkout, &index, "pipe regression")
            .expect("attribute pathspec scan must handle output larger than a pipe buffer");
    }

    #[test]
    fn git_checkout_verification_recurses_and_checks_submodule_origin() {
        let directory = TempDir::new().unwrap();
        let child_source = directory.path().join("child-source");
        init_test_git_repository(&child_source);
        fs::write(child_source.join(".gitignore"), "ignored.tmp\n").unwrap();
        fs::write(child_source.join("child.txt"), "child\n").unwrap();
        test_git(&child_source, &["add", "."]);
        test_git(&child_source, &["commit", "--quiet", "-m", "child"]);

        let checkout = directory.path().join("checkout");
        init_test_git_repository(&checkout);
        let child_url = child_source.to_string_lossy().to_string();
        let output = ProcCommand::new("git")
            .arg("-c")
            .arg("protocol.file.allow=always")
            .arg("-C")
            .arg(&checkout)
            .args(["submodule", "add", "--quiet", &child_url, "child"])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        test_git(&checkout, &["commit", "--quiet", "-m", "parent"]);
        let parent_url = "https://example.invalid/parent.git";
        test_git(&checkout, &["remote", "add", "origin", parent_url]);
        let corpus = test_git_corpus(&checkout, parent_url);
        assert!(verify_git_checkout(&corpus).is_ok());

        test_git(&checkout, &["config", "submodule.child.ignore", "all"]);
        fs::write(checkout.join("child/ignored.tmp"), "hidden\n").unwrap();
        let error = verify_git_checkout(&corpus).unwrap_err();
        assert!(format!("{error:#}").contains("ignored extra files"));
        fs::remove_file(checkout.join("child/ignored.tmp")).unwrap();

        test_git(
            &checkout.join("child"),
            &[
                "remote",
                "set-url",
                "origin",
                "https://example.invalid/wrong.git",
            ],
        );
        let error = verify_git_checkout(&corpus).unwrap_err();
        assert!(format!("{error:#}").contains("has origin"));
        test_git(
            &checkout.join("child"),
            &["remote", "set-url", "origin", &child_url],
        );

        let child_object =
            test_git_stdout(&checkout.join("child"), &["rev-parse", "HEAD:child.txt"]);
        let child_git_directory =
            test_git_stdout(&checkout.join("child"), &["rev-parse", "--git-dir"]);
        let child_object_path = checkout
            .join("child")
            .join(child_git_directory)
            .join("objects")
            .join(&child_object[..2])
            .join(&child_object[2..]);
        fs::remove_file(child_object_path).unwrap();
        let error = verify_git_checkout(&corpus).unwrap_err();
        assert!(format!("{error:#}").contains("missing or corrupt objects"));
    }

    #[test]
    fn git_checkout_verification_names_gitlinks_without_gitmodules_mappings() {
        let fixture = git_checkout_fixture();
        let commit = test_git_stdout(&fixture.checkout, &["rev-parse", "HEAD"]);
        fs::write(
            fixture.checkout.join(".gitmodules"),
            "[submodule \"mapped\"]\n\
             \tpath = mapped\n\
             \turl = https://example.invalid/mapped.git\n",
        )
        .unwrap();
        test_git(&fixture.checkout, &["add", ".gitmodules"]);
        for path in ["mapped", "old/unmapped"] {
            test_git(
                &fixture.checkout,
                &[
                    "update-index",
                    "--add",
                    "--cacheinfo",
                    &format!("160000,{commit},{path}"),
                ],
            );
        }
        let index = verified_git_output(
            &fixture.checkout,
            &["ls-files", "--stage", "-v", "-z"],
            "test mismatched gitlinks",
        )
        .unwrap();
        let index =
            parse_verified_git_index(&fixture.checkout, &index, "mismatched gitlinks").unwrap();
        let canonical = fs::canonicalize(&fixture.checkout).unwrap();
        let error = verify_git_submodules(
            &fixture.checkout,
            &canonical,
            &index,
            "mismatched gitlinks",
            &BTreeSet::new(),
            0,
        )
        .unwrap_err();
        assert!(
            format!("{error:#}").contains("actual unmapped mode-160000 entries: [old/unmapped]")
        );
    }

    #[test]
    fn git_checkout_verification_requires_exact_unmapped_gitlink_exceptions() {
        let fixture = git_checkout_fixture();
        let commit = test_git_stdout(&fixture.checkout, &["rev-parse", "HEAD"]);
        for path in ["legacy/cora", "legacy/hyst"] {
            test_git(
                &fixture.checkout,
                &[
                    "update-index",
                    "--add",
                    "--cacheinfo",
                    &format!("160000,{commit},{path}"),
                ],
            );
        }
        let index = verified_git_output(
            &fixture.checkout,
            &["ls-files", "--stage", "-v", "-z"],
            "test allowed unmapped gitlinks",
        )
        .unwrap();
        let index =
            parse_verified_git_index(&fixture.checkout, &index, "allowed unmapped gitlinks")
                .unwrap();
        let canonical = fs::canonicalize(&fixture.checkout).unwrap();
        let exact = ["legacy/cora".to_string(), "legacy/hyst".to_string()]
            .into_iter()
            .collect::<BTreeSet<_>>();

        assert!(!verify_git_submodules(
            &fixture.checkout,
            &canonical,
            &index,
            "allowed unmapped gitlinks",
            &exact,
            0,
        )
        .expect("the exact declared exception set must pass"));

        let stale = [
            "legacy/cora".to_string(),
            "legacy/hyst".to_string(),
            "legacy/stale".to_string(),
        ]
        .into_iter()
        .collect::<BTreeSet<_>>();
        let error = verify_git_submodules(
            &fixture.checkout,
            &canonical,
            &index,
            "stale unmapped gitlinks",
            &stale,
            0,
        )
        .expect_err("a stale declared exception must fail");
        assert!(format!("{error:#}").contains("legacy/stale"));

        let incomplete = ["legacy/cora".to_string()]
            .into_iter()
            .collect::<BTreeSet<_>>();
        let error = verify_git_submodules(
            &fixture.checkout,
            &canonical,
            &index,
            "additional unmapped gitlink",
            &incomplete,
            0,
        )
        .expect_err("an additional actual unmapped gitlink must fail");
        assert!(format!("{error:#}").contains("legacy/hyst"));
    }

    #[test]
    fn git_checkout_verification_preserves_shallow_checkouts() {
        let directory = TempDir::new().unwrap();
        let source = directory.path().join("source");
        init_test_git_repository(&source);
        fs::write(source.join("asset.txt"), "one\n").unwrap();
        test_git(&source, &["add", "asset.txt"]);
        test_git(&source, &["commit", "--quiet", "-m", "one"]);
        fs::write(source.join("asset.txt"), "two\n").unwrap();
        test_git(&source, &["commit", "-qam", "two"]);

        let checkout = directory.path().join("checkout");
        let url = format!("file://{}", source.display());
        let output = ProcCommand::new("git")
            .args(["clone", "--quiet", "--depth", "1", &url])
            .arg(&checkout)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            test_git_stdout(&checkout, &["rev-parse", "--is-shallow-repository"]),
            "true"
        );
        let corpus = test_git_corpus(&checkout, &url);
        assert!(verify_git_checkout(&corpus).is_ok());
    }

    // ---------- fixtures: name derivation ----------

    #[test]
    fn chc_fixture_list_picks_only_000_smt2_sorted() {
        let dir = TempDir::new().unwrap();
        // A mix of fixtures, non-_000 siblings, and unrelated files.
        for name in [
            "s_multipl_10_000.smt2",
            "dillig02_m_000.smt2",
            "dillig02_m.smt2",         // sibling, not a fixture
            "bouncy_one_counter.smt2", // sibling
            "README.md",
            "accumulator_unsafe_000.smt2",
        ] {
            fs::write(dir.path().join(name), b"x").unwrap();
        }
        let got = chc_fixture_list(dir.path()).unwrap();
        assert_eq!(
            got,
            vec![
                "accumulator_unsafe_000.smt2".to_string(),
                "dillig02_m_000.smt2".to_string(),
                "s_multipl_10_000.smt2".to_string(),
            ]
        );
    }

    #[test]
    fn chc_fixture_list_empty_for_missing_dir() {
        let dir = TempDir::new().unwrap();
        let missing = dir.path().join("does-not-exist");
        assert!(chc_fixture_list(&missing).unwrap().is_empty());
    }

    #[test]
    fn ay_specific_fixtures_are_recognized() {
        assert!(is_ay_specific_fixture("accumulator_unsafe_000.smt2"));
        assert!(is_ay_specific_fixture("two_phase_unsafe_000.smt2"));
        assert!(!is_ay_specific_fixture("dillig02_m_000.smt2"));
        assert!(!is_ay_specific_fixture("s_multipl_10_000.smt2"));
    }

    // ---------- install-tool: name validation ----------

    #[test]
    fn install_tool_rejects_unknown_name() {
        // The deprecated alias delegates to the tool registry; an unregistered
        // name is a load-time lookup error naming the registry.
        let err = run_install_tool(InstallToolArgs {
            name: "z3".into(),
            force: false,
        })
        .unwrap_err();
        let msg = format!("{err:#}");
        assert!(msg.contains("not found in registry"), "{msg}");
    }
}
