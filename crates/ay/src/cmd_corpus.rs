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
//!   - `http`: archive fetched from a fixed URL. Optionally SHA256-pinned.
//!     `archive` controls extraction: `tar` (default), `zip`, or `none`.
//!   - `git`: `git clone --depth <depth>` from a URL. Optional `commit` pin.
//!   - `gbd`: per-file fetch from the Global Benchmark Database, driven by a
//!     `manifest` CSV with `hash` and `local_path` columns. Each row's content
//!     is GET from `https://benchmark-database.de/file/<hash>` and written to
//!     `<local_path>` (typically `…cnf.xz`); if the payload is an xz stream the
//!     decompressed sibling (`…cnf`, the path the test fixtures read) is also
//!     written. Rows already present (either form) are skipped unless `--force`.
//!
//! Verbs: `list`, `download`, `verify`, `upload` (release only), `prune`.

use std::collections::BTreeSet;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command as ProcCommand, Stdio};

use anyhow::{anyhow, bail, Context, Result};
use clap::{Args, Subcommand};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const DEFAULT_MANIFEST: &str = "benchmarks/corpora.toml";

#[derive(Subcommand)]
pub(crate) enum CorpusCommand {
    /// Print the corpus table with local status.
    List(ListArgs),
    /// Download one or more corpora.
    Download(DownloadArgs),
    /// Verify the SHA256 of locally-cached archives against the manifest.
    Verify(VerifyArgs),
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
}

#[derive(Args)]
pub(crate) struct DownloadArgs {
    #[command(flatten)]
    manifest: ManifestArgs,
    /// Download every corpus in the manifest.
    #[arg(long)]
    all: bool,
    /// Re-download even if the local copy looks correct.
    #[arg(long)]
    force: bool,
    /// Corpus names. Required unless `--all` is set.
    names: Vec<String>,
}

#[derive(Args)]
pub(crate) struct VerifyArgs {
    #[command(flatten)]
    manifest: ManifestArgs,
    #[arg(long)]
    all: bool,
    names: Vec<String>,
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

#[derive(Debug, Clone, Serialize, Deserialize)]
struct Corpus {
    name: String,
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
    // http: archive format
    #[serde(default, skip_serializing_if = "Archive::is_default")]
    archive: Archive,
    // git: shallow depth (default 1) and optional commit pin
    #[serde(skip_serializing_if = "Option::is_none")]
    depth: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    commit: Option<String>,
    // gbd: path to the CSV manifest with `hash` and `local_path` columns.
    #[serde(skip_serializing_if = "Option::is_none")]
    manifest: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "lowercase")]
enum Source {
    #[default]
    Release,
    Http,
    Git,
    Gbd,
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
}

impl Manifest {
    fn load(path: &Path) -> Result<Self> {
        let body = fs::read_to_string(path)
            .with_context(|| format!("read manifest {}", path.display()))?;
        let manifest: Manifest =
            toml::from_str(&body).with_context(|| format!("parse manifest {}", path.display()))?;
        if manifest.schema_version < 1 || manifest.schema_version > 2 {
            bail!(
                "manifest {}: unsupported schema_version {} (expected 1 or 2)",
                path.display(),
                manifest.schema_version
            );
        }
        let mut seen = BTreeSet::new();
        for c in &manifest.corpora {
            if !seen.insert(c.name.clone()) {
                bail!(
                    "manifest {}: duplicate corpus name {}",
                    path.display(),
                    c.name
                );
            }
            c.validate()
                .with_context(|| format!("corpus {} in {}", c.name, path.display()))?;
        }
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

    fn select<'a>(&'a self, names: &[String], all: bool) -> Result<Vec<&'a Corpus>> {
        if all {
            if !names.is_empty() {
                bail!("--all is mutually exclusive with explicit corpus names");
            }
            return Ok(self.corpora.iter().collect());
        }
        if names.is_empty() {
            bail!("specify at least one corpus name, or pass --all");
        }
        names.iter().map(|n| self.find(n)).collect()
    }
}

impl Corpus {
    fn validate(&self) -> Result<()> {
        match self.source {
            Source::Release => {
                if self.asset.is_none() {
                    bail!("source=release requires `asset`");
                }
                if self.sha256.is_none() {
                    bail!("source=release requires `sha256`");
                }
            }
            Source::Http => {
                if self.url.is_none() {
                    bail!("source=http requires `url`");
                }
            }
            Source::Git => {
                if self.url.is_none() {
                    bail!("source=git requires `url`");
                }
                if self.archive != Archive::Tar {
                    bail!("source=git does not use `archive`");
                }
            }
            Source::Gbd => {
                if self.manifest.is_none() {
                    bail!("source=gbd requires `manifest` (CSV with hash,local_path columns)");
                }
                if self.archive != Archive::Tar {
                    bail!("source=gbd does not use `archive`");
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
                let extract = PathBuf::from(&self.extract_to);
                let parent = extract.parent().unwrap_or_else(|| Path::new("."));
                Some(parent.join(self.asset.as_ref()?))
            }
            (Source::Http, Archive::None) => Some(PathBuf::from(&self.extract_to)),
            (Source::Http, _) => {
                let extract = PathBuf::from(&self.extract_to);
                let parent = extract.parent().unwrap_or_else(|| Path::new("."));
                let basename = self
                    .url
                    .as_deref()?
                    .rsplit('/')
                    .next()
                    .filter(|s| !s.is_empty())?;
                Some(parent.join(basename))
            }
            // git clones a directory; gbd writes per-row files: neither has a
            // single cached archive.
            (Source::Git, _) | (Source::Gbd, _) => None,
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
        // Archive::None: the file at cache_path IS the result.
        if self.archive == Archive::None {
            if let Some(cache) = self.cache_path() {
                if cache.exists() {
                    if let Some(expected) = &self.sha256 {
                        return match local_sha256(&cache).ok() {
                            Some(s) if &s == expected => "downloaded".to_string(),
                            Some(_) => "stale".to_string(),
                            None => "unreadable".to_string(),
                        };
                    }
                    return "downloaded".to_string();
                }
            }
            return "missing".to_string();
        }
        let extract = Path::new(&self.extract_to);
        if extract.exists() {
            return "extracted".to_string();
        }
        if let Some(cache) = self.cache_path() {
            if cache.exists() {
                if let Some(expected) = &self.sha256 {
                    return match local_sha256(&cache).ok() {
                        Some(s) if &s == expected => "downloaded".to_string(),
                        Some(_) => "stale".to_string(),
                        None => "unreadable".to_string(),
                    };
                }
                return "downloaded".to_string();
            }
        }
        "missing".to_string()
    }

    /// Parse the gbd CSV manifest into rows. Errors if the entry has no
    /// `manifest` field or the file cannot be read/parsed.
    fn gbd_rows(&self) -> Result<Vec<GbdRow>> {
        let manifest = self
            .manifest
            .as_deref()
            .ok_or_else(|| anyhow!("source=gbd requires `manifest`"))?;
        parse_gbd_manifest(Path::new(manifest))
    }
}

/// One row of a gbd manifest CSV: a content `hash` and the repo-relative
/// `local_path` of the downloaded (xz) artifact.
#[derive(Debug, Clone)]
struct GbdRow {
    hash: String,
    local_path: String,
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

    /// A row is "present" if either the raw `.xz` artifact or its decompressed
    /// sibling is on disk (two-trees is vendored only as the decompressed
    /// `.cnf`, while other rows are vendored as the raw `.cnf.xz`).
    fn is_present(&self) -> bool {
        self.raw_path().exists() || self.decompressed_path().exists()
    }
}

/// Parse a gbd manifest CSV. The header must include `hash` and `local_path`
/// columns (others are ignored). Fields may be double-quoted (the `category`
/// column embeds commas), so quoted fields are unescaped accordingly.
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
    let mut rows = Vec::new();
    for line in lines {
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
        if hash.is_empty() || local_path.is_empty() {
            continue;
        }
        rows.push(GbdRow { hash, local_path });
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
        CorpusCommand::Download(args) => run_download(args),
        CorpusCommand::Verify(args) => run_verify(args),
        CorpusCommand::Upload(args) => run_upload(args),
        CorpusCommand::Prune(args) => run_prune(args),
        CorpusCommand::CheckUrls(args) => run_check_urls(args),
        CorpusCommand::Fixtures(args) => run_fixtures(args),
        CorpusCommand::InstallTool(args) => run_install_tool(args),
    }
}

fn run_list(args: ListArgs) -> Result<i32> {
    let manifest = Manifest::load(&args.manifest.manifest)?;
    println!("{:<32} {:<8} {:>9}  STATUS", "NAME", "SOURCE", "SIZE");
    for c in &manifest.corpora {
        let size = c.size_bytes.map(human_bytes).unwrap_or_else(|| "-".into());
        println!(
            "{:<32} {:<8} {:>9}  {}",
            c.name,
            c.source.label(),
            size,
            c.local_status(),
        );
    }
    Ok(0)
}

fn run_download(args: DownloadArgs) -> Result<i32> {
    let manifest = Manifest::load(&args.manifest.manifest)?;
    let targets = manifest.select(&args.names, args.all)?;
    for c in targets {
        match c.source {
            Source::Release => download_release(&manifest, c, args.force)?,
            Source::Http => download_http(c, args.force)?,
            Source::Git => download_git(c, args.force)?,
            Source::Gbd => download_gbd(c, args.force)?,
        }
    }
    Ok(0)
}

fn run_verify(args: VerifyArgs) -> Result<i32> {
    let manifest = Manifest::load(&args.manifest.manifest)?;
    let targets = manifest.select(&args.names, args.all)?;
    let mut bad = 0;
    for c in targets {
        if c.source == Source::Gbd {
            // gbd has no single archive/sha256 to verify; report how many rows'
            // files (raw .xz or decompressed sibling) are present on disk.
            let rows = c.gbd_rows()?;
            let present = rows.iter().filter(|r| r.is_present()).count();
            if present == rows.len() {
                println!("{}: ok ({}/{} files present)", c.name, present, rows.len());
            } else {
                println!(
                    "{}: incomplete ({}/{} files present)",
                    c.name,
                    present,
                    rows.len()
                );
                bad += 1;
            }
            continue;
        }
        let Some(expected) = c.sha256.as_deref() else {
            println!("{}: skipped (no sha256 pin)", c.name);
            continue;
        };
        let Some(cache) = c.cache_path() else {
            println!("{}: skipped (source has no cache)", c.name);
            continue;
        };
        if !cache.exists() {
            println!("{}: archive missing ({})", c.name, cache.display());
            bad += 1;
            continue;
        }
        let got = local_sha256(&cache)?;
        if got == expected {
            println!("{}: ok ({})", c.name, &got[..16]);
        } else {
            println!("{}: MISMATCH (expected {}, got {})", c.name, expected, got);
            bad += 1;
        }
    }
    Ok(if bad == 0 { 0 } else { 1 })
}

fn run_upload(args: UploadArgs) -> Result<i32> {
    let mut manifest = Manifest::load(&args.manifest.manifest)?;
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
    let from = args
        .from
        .clone()
        .unwrap_or_else(|| PathBuf::from(&corpus.extract_to));
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
    manifest.save(&args.manifest.manifest)?;
    println!(
        "==> manifest updated ({})",
        args.manifest.manifest.display()
    );
    Ok(0)
}

fn run_prune(args: PruneArgs) -> Result<i32> {
    let manifest = Manifest::load(&args.manifest.manifest)?;
    let targets = manifest.select(&args.names, args.all)?;
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
        let extract = PathBuf::from(&c.extract_to);
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
    let targets: Vec<&Corpus> = if args.names.is_empty() {
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
    if head_code != 405 {
        return Ok(head_code);
    }
    // Some servers reject HEAD; try a 1-byte range GET instead.
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
    let expected = c.sha256.as_deref().expect("validate enforces sha256");
    let extract = PathBuf::from(&c.extract_to);

    let have_good = cache.exists() && local_sha256(&cache).ok().as_deref() == Some(expected);
    if force || !have_good {
        println!("==> download {} ({})", c.name, cache.display());
        let asset = c.asset.as_deref().expect("validate enforces asset");
        gh_release_download(&manifest.repo, &manifest.release_tag, asset, &cache)?;
        let got = local_sha256(&cache)?;
        if got != expected {
            bail!(
                "{}: SHA256 mismatch after download (expected {}, got {})",
                c.name,
                expected,
                got
            );
        }
    } else {
        println!("==> have {} (sha256 verified)", c.name);
    }
    extract_into_place(&cache, Archive::Tar, &extract, force)
}

fn download_http(c: &Corpus, force: bool) -> Result<()> {
    let url = c.url.as_deref().expect("validate enforces url");
    let cache = c.cache_path().expect("http has cache_path");
    let extract = PathBuf::from(&c.extract_to);

    let mut need_download = force || !cache.exists();
    if !need_download {
        if let Some(expected) = c.sha256.as_deref() {
            need_download = local_sha256(&cache).ok().as_deref() != Some(expected);
        }
    }
    if need_download {
        println!("==> download {} ({})", c.name, url);
        if let Some(parent) = cache.parent() {
            fs::create_dir_all(parent).with_context(|| format!("mkdir -p {}", parent.display()))?;
        }
        http_get(url, &cache)?;
        if let Some(expected) = c.sha256.as_deref() {
            let got = local_sha256(&cache)?;
            if got != expected {
                bail!(
                    "{}: SHA256 mismatch after download (expected {}, got {})",
                    c.name,
                    expected,
                    got
                );
            }
        }
    } else {
        println!("==> have {}", c.name);
    }
    if c.archive == Archive::None {
        return Ok(());
    }
    extract_into_place(&cache, c.archive, &extract, force)
}

fn download_git(c: &Corpus, force: bool) -> Result<()> {
    let url = c.url.as_deref().expect("validate enforces url");
    let extract = PathBuf::from(&c.extract_to);
    if extract.exists() {
        if !force {
            println!("==> have {} (cloned)", c.name);
            return Ok(());
        }
        fs::remove_dir_all(&extract).with_context(|| format!("rm -rf {}", extract.display()))?;
    }
    if let Some(parent) = extract.parent() {
        fs::create_dir_all(parent).with_context(|| format!("mkdir -p {}", parent.display()))?;
    }
    let depth = c.depth.unwrap_or(1);
    println!(
        "==> git clone --depth {} {} -> {}",
        depth,
        url,
        extract.display()
    );
    let mut cmd = ProcCommand::new("git");
    cmd.args(["clone", "--depth"])
        .arg(depth.to_string())
        .arg(url)
        .arg(&extract);
    let status = cmd.status().context("invoke git clone")?;
    if !status.success() {
        bail!("git clone exited with {:?}", status.code());
    }
    if let Some(commit) = &c.commit {
        let status = ProcCommand::new("git")
            .args(["-C"])
            .arg(&extract)
            .args(["checkout", commit])
            .status()
            .context("invoke git checkout")?;
        if !status.success() {
            bail!("git checkout {} exited with {:?}", commit, status.code());
        }
    }
    Ok(())
}

fn download_gbd(c: &Corpus, force: bool) -> Result<()> {
    let rows = c.gbd_rows()?;
    if rows.is_empty() {
        bail!("{}: gbd manifest has no rows", c.name);
    }
    let mut fetched = 0usize;
    let mut skipped = 0usize;
    for row in &rows {
        // The raw artifact lives at `local_path` (typically `…cnf.xz`); the
        // decompressed sibling (`…cnf`) is what the unit tests read. A row is
        // satisfied if either is already on disk.
        let raw = row.raw_path();
        let decompressed = row.decompressed_path();
        if !force && row.is_present() {
            skipped += 1;
            continue;
        }
        let url = format!("{}/{}", GBD_FILE_BASE, row.hash);
        println!("==> {} {} -> {}", c.name, url, raw.display());
        if let Some(parent) = raw.parent() {
            fs::create_dir_all(parent).with_context(|| format!("mkdir -p {}", parent.display()))?;
        }
        http_get(&url, &raw)?;
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
    force: bool,
) -> Result<()> {
    if extract_to.exists() && !force {
        println!("    already extracted: {}", extract_to.display());
        return Ok(());
    }
    if extract_to.exists() {
        fs::remove_dir_all(extract_to)
            .with_context(|| format!("rm -rf {}", extract_to.display()))?;
    }
    let parent = extract_to
        .parent()
        .ok_or_else(|| anyhow!("extract_to {} has no parent", extract_to.display()))?;
    fs::create_dir_all(parent).with_context(|| format!("mkdir -p {}", parent.display()))?;
    println!("    extracting -> {}", extract_to.display());
    match archive {
        Archive::Tar => extract_tarball(archive_path, parent)?,
        Archive::Zip => extract_zip(archive_path, parent)?,
        Archive::None => bail!("extract_into_place called with Archive::None"),
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
    let tmp = out.with_extension("tmp");
    let mut cmd = if which("curl") {
        let mut c = ProcCommand::new("curl");
        c.args(["--fail", "--location", "--progress-bar", "-o"])
            .arg(&tmp)
            .arg(url);
        c
    } else if which("wget") {
        let mut c = ProcCommand::new("wget");
        c.args(["-q", "--show-progress", "-O"]).arg(&tmp).arg(url);
        c
    } else {
        bail!("neither curl nor wget available on PATH");
    };
    let status = cmd.status().context("invoke http downloader")?;
    if !status.success() {
        bail!("http download exited with {:?}", status.code());
    }
    fs::rename(&tmp, out).with_context(|| format!("mv {} -> {}", tmp.display(), out.display()))?;
    Ok(())
}

fn which(tool: &str) -> bool {
    ProcCommand::new(tool)
        .arg("--version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

fn gh_release_download(repo: &str, tag: &str, asset: &str, out: &Path) -> Result<()> {
    let tmp = out.with_extension("tmp");
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
        .arg(&tmp)
        .arg("--clobber")
        .status()
        .context("invoke gh release download")?;
    if !status.success() {
        bail!("gh release download exited with {:?}", status.code());
    }
    fs::rename(&tmp, out).with_context(|| format!("mv {} -> {}", tmp.display(), out.display()))?;
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

fn extract_tarball(tarball: &Path, into: &Path) -> Result<()> {
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
    Ok(())
}

fn extract_zip(zip: &Path, into: &Path) -> Result<()> {
    if !which("unzip") {
        bail!("install unzip (brew install unzip) to extract .zip archives");
    }
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
    Ok(())
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
        assert!(format!("{:#}", err).contains("sha256"));

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
        assert!(format!("{:#}", err).contains("asset"));
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
        assert!(format!("{:#}", err).contains("manifest"));
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
        assert_eq!(rows[1].hash, "dcf5b822");
    }

    #[test]
    fn parse_gbd_manifest_rejects_missing_columns() {
        let dir = TempDir::new().unwrap();
        let path = dir.path().join("manifest.csv");
        fs::write(&path, "filename,size_bytes\nfoo.cnf.xz,42\n").unwrap();
        let err = parse_gbd_manifest(&path).unwrap_err();
        assert!(format!("{:#}", err).contains("hash"));
    }

    #[test]
    fn gbd_local_status_counts_present_files() {
        let dir = TempDir::new().unwrap();
        let present = dir.path().join("present.cnf");
        fs::write(&present, b"p cnf 0 0\n").unwrap();
        let absent = dir.path().join("absent.cnf");
        let manifest = dir.path().join("manifest.csv");
        fs::write(
            &manifest,
            format!(
                "hash,local_path\nh1,{}\nh2,{}\n",
                present.display(),
                absent.display()
            ),
        )
        .unwrap();

        let mut c = release_corpus();
        c.source = Source::Gbd;
        c.asset = None;
        c.sha256 = None;
        c.manifest = Some(manifest.to_string_lossy().into());
        assert_eq!(c.local_status(), "partial (1/2)");

        fs::write(&absent, b"p cnf 0 0\n").unwrap();
        assert_eq!(c.local_status(), "downloaded (2/2)");
    }

    #[test]
    fn gbd_row_paths_and_presence() {
        let dir = TempDir::new().unwrap();
        let raw = dir.path().join("x.cnf.xz");
        let decompressed = dir.path().join("x.cnf");
        let row = GbdRow {
            hash: "h".into(),
            local_path: raw.to_string_lossy().into(),
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
            assert!(format!("{:#}", err).contains("url"), "source={source}");
        }
    }

    // ---------- Corpus accessors ----------

    fn release_corpus() -> Corpus {
        Corpus {
            name: "r".into(),
            source: Source::Release,
            extract_to: "benchmarks/foo/bar".into(),
            asset: Some("bar-v1.tar.zst".into()),
            sha256: Some("00".into()),
            size_bytes: Some(1),
            url: None,
            archive: Archive::Tar,
            depth: None,
            commit: None,
            manifest: None,
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
    fn local_status_extracted_when_dir_exists() {
        let dir = TempDir::new().unwrap();
        let extract = dir.path().join("here");
        fs::create_dir(&extract).unwrap();
        let mut c = release_corpus();
        c.extract_to = extract.to_string_lossy().into();
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
        assert_eq!(c.local_status(), "downloaded");

        // Now make the SHA mismatch.
        c.sha256 = Some("0000".into());
        assert_eq!(c.local_status(), "stale");
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

        assert_eq!(m.select(&[], true).unwrap().len(), 2);
        let one = m.select(&["a".into()], false).unwrap();
        assert_eq!(one.len(), 1);
        assert_eq!(one[0].name, "a");

        assert!(m.select(&["a".into()], true).is_err());
        assert!(m.select(&[], false).is_err());
        assert!(m.select(&["missing".into()], false).is_err());
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
        let msg = format!("{:#}", err);
        assert!(msg.contains("not found in registry"), "{msg}");
    }
}
