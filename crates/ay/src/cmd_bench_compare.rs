// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `ay bench compare` — compare AY against a competition's field under
//! labeled run classes (design: the development design notes).
//!
//! Registry: `benchmarks/comparisons.toml`. 0.1.0 verbs: `list`, `show`,
//! `check` — read-only preflight; the runner verbs (`refs`, `run`, `import`,
//! `report`) land post-0.1.0 and the group help states this. `check` is
//! self-contained so it can be run on the machine that would host a replay:
//! it reads local hardware and compares it field by field against the
//! entry's cited official specs.

use std::path::PathBuf;

use clap::{Args, Subcommand, ValueEnum};
use serde::{Deserialize, Serialize};

#[cfg(any(feature = "bench", test))]
use std::collections::BTreeSet;
#[cfg(any(feature = "bench", test))]
use std::fs;
#[cfg(any(feature = "bench", test))]
use std::path::Path;
#[cfg(any(feature = "bench", test))]
use std::process::Command as ProcCommand;

#[cfg(any(feature = "bench", test))]
use anyhow::{anyhow, bail, Context, Result};

const DEFAULT_REGISTRY: &str = "benchmarks/comparisons.toml";
#[cfg(any(feature = "bench", test))]
const CORPORA_MANIFEST: &str = "benchmarks/corpora.toml";
#[cfg(any(feature = "bench", test))]
const TOOLS_REGISTRY: &str = "reference/tools.toml";
#[cfg(any(feature = "bench", test))]
const PACKET_ROOT: &str = "evals/results/compare";

// ---------------------------------------------------------------------------
// Help text (drafted in the design doc; kept verbatim there where possible)
// ---------------------------------------------------------------------------

const GROUP_LONG_ABOUT: &str = "\
Compare AY against a competition's field under labeled run classes

Every number produced here carries exactly one run class and never travels
without it:
  official  imported published results — the only class called a \"result\"
  replay    local run on hardware matching the cited official machine specs
  laptop    developer-machine run; verdict counts meaningful, timings weak

Registry: benchmarks/comparisons.toml — one entry per competition edition:
cited official host specs (or \"unknown\", never guessed), per-job budgets,
scoring rule, corpus pin, and the edition's top-3 winners as locally built,
pinned reference solvers (reference/tools.toml). Classes are verified, not
asserted: replay is granted by a host check and refused on mismatch, with
no override. official packets are created only by `import`, with a citation.";

const GROUP_AFTER_HELP: &str = "\
At 0.1.0 this group provides `list`, `show`, and `check`. Post-0.1.0 roadmap:
  refs    Show or install an entry's winner reference solvers
  run     Execute a replay- or laptop-class comparison run
  import  Record the competition's published results as class=official
  report  Render packets into a per-class scoreboard";

const LIST_LONG_ABOUT: &str = "\
List registry entries with readiness and packet counts

One row per entry: ID, COMPETITION, EDITION, STATUS, SPECS (cited/unknown),
CORPUS (installed?), REFS (built n/3), PACKETS (count per class found under
evals/results/compare/). STATUS specs-pending means official specs are not
yet cited; such entries refuse `run --class replay` and `refs --install`.";

const SHOW_LONG_ABOUT: &str = "\
Print one entry in full, including citations and install state

Official host specs and budgets with their citations, the scoring rule, the
corpus pin with local status (via `ay corpus`), each winner with its
tool-registry pin and install state (via `ay tool`), the exact documented
replay invocation, and existing packets per class. Fields the research pass
has not filled print as \"unknown\" — never a guess.";

const CHECK_LONG_ABOUT: &str = "\
Preflight one entry: corpus, winner builds, scoring, host verdict

Verifies the corpus is installed at the pinned revision, every winner tool
resolves and probes at its pinned version, and the scoring method exists.
Then compares this machine (the same capture `bench run` records into
results.json) field by field against the entry's cited official specs —
arch exact, OS family exact, CPU model substring, cores at least official,
memory within the entry's tolerance — and prints the verdict:

  replay-eligible   this host may run `compare run --class replay`
  laptop-only       with the mismatching fields listed
  specs-pending     the entry has no cited specs

`compare run --class replay` re-runs this same check and refuses on
anything but replay-eligible. There is no override flag — mismatched
hardware is class=laptop by definition.

Exit codes: 0 = entry runnable and replay-eligible; 1 = runnable,
laptop-only; 2 = entry not runnable (missing corpus/tools) or specs unknown.";

// ---------------------------------------------------------------------------
// Clap surface (compiled unconditionally, like the rest of `ay bench`)
// ---------------------------------------------------------------------------

#[derive(Args)]
#[command(
    about = "Compare AY against a competition's field under labeled run classes",
    long_about = GROUP_LONG_ABOUT,
    after_help = GROUP_AFTER_HELP
)]
#[cfg_attr(not(feature = "bench"), allow(dead_code))]
pub(crate) struct BenchCompareArgs {
    #[command(subcommand)]
    command: CompareCommand,

    /// Comparison registry
    #[arg(long, global = true, value_name = "FILE", default_value = DEFAULT_REGISTRY)]
    registry: PathBuf,
}

#[derive(Subcommand)]
#[cfg_attr(not(feature = "bench"), allow(dead_code))]
enum CompareCommand {
    /// List registry entries with readiness and packet counts
    #[command(long_about = LIST_LONG_ABOUT)]
    List(ListArgs),
    /// Print one entry in full, including citations and install state
    #[command(long_about = SHOW_LONG_ABOUT)]
    Show(ShowArgs),
    /// Preflight one entry: corpus, winner builds, scoring, host verdict
    #[command(long_about = CHECK_LONG_ABOUT)]
    Check(CheckArgs),
}

#[derive(Args)]
#[cfg_attr(not(feature = "bench"), allow(dead_code))]
struct ListArgs {
    /// Filter by competition
    #[arg(long, value_name = "COMP", value_enum)]
    competition: Option<Competition>,
    /// Emit the table as JSON
    #[arg(long)]
    json: bool,
}

#[derive(Args)]
#[cfg_attr(not(feature = "bench"), allow(dead_code))]
struct ShowArgs {
    /// Comparison id (e.g. smtcomp-2025-single-query-qf-lia)
    id: String,
    /// Emit the entry as JSON
    #[arg(long)]
    json: bool,
}

#[derive(Args)]
#[cfg_attr(not(feature = "bench"), allow(dead_code))]
struct CheckArgs {
    /// Comparison id (e.g. smtcomp-2025-single-query-qf-lia)
    id: String,
    /// Emit findings as JSON
    #[arg(long)]
    json: bool,
}

/// Closed competition set (design §3.1 plus `qbfeval`, which the research
/// wave recorded an entry for).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, ValueEnum)]
#[serde(rename_all = "lowercase")]
pub(crate) enum Competition {
    Satcomp,
    Smtcomp,
    Chccomp,
    Qbfeval,
    Pbcomp,
    Maxsat,
    Mznc,
    Hwmcc,
    Mcc,
    Miplib,
    Xcsp3,
    Casc,
    Sygus,
}

impl Competition {
    #[cfg(any(feature = "bench", test))]
    fn label(&self) -> &'static str {
        match self {
            Competition::Satcomp => "satcomp",
            Competition::Smtcomp => "smtcomp",
            Competition::Chccomp => "chccomp",
            Competition::Qbfeval => "qbfeval",
            Competition::Pbcomp => "pbcomp",
            Competition::Maxsat => "maxsat",
            Competition::Mznc => "mznc",
            Competition::Hwmcc => "hwmcc",
            Competition::Mcc => "mcc",
            Competition::Miplib => "miplib",
            Competition::Xcsp3 => "xcsp3",
            Competition::Casc => "casc",
            Competition::Sygus => "sygus",
        }
    }
}

// ---------------------------------------------------------------------------
// Registry (benchmarks/comparisons.toml)
// ---------------------------------------------------------------------------

#[cfg(any(feature = "bench", test))]
#[derive(Debug, Serialize, Deserialize)]
struct Registry {
    schema_version: u32,
    #[serde(default, rename = "comparison")]
    comparisons: Vec<Comparison>,
}

#[cfg(any(feature = "bench", test))]
#[derive(Debug, Clone, Serialize, Deserialize)]
struct Comparison {
    id: String,
    competition: Competition,
    edition: u32,
    #[serde(default)]
    track: String,
    status: Status,
    #[serde(default)]
    notes: String,
    #[serde(default)]
    official_hosts: String,
    #[serde(default)]
    budgets: String,
    #[serde(default)]
    scoring: String,
    #[serde(default)]
    corpus: String,
    /// `benchmarks/corpora.toml` entry name when the corpus is locally
    /// managed; empty = external (fetched per the `corpus` prose).
    #[serde(default)]
    corpus_name: String,
    #[serde(default)]
    winners: Vec<String>,
    #[serde(default)]
    citations: Vec<String>,
    /// Host fields parsed from `official_hosts`, consumed by `check`.
    #[serde(default)]
    official: OfficialSpecs,
}

#[cfg(any(feature = "bench", test))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
enum Status {
    SpecsPending,
    Ready,
    Archived,
    /// AY would enter directly but the input frontend does not exist yet;
    /// the entry records the competition and its benchmark corpus honestly.
    Unsupported,
}

#[cfg(any(feature = "bench", test))]
impl Status {
    fn label(&self) -> &'static str {
        match self {
            Status::SpecsPending => "specs-pending",
            Status::Ready => "ready",
            Status::Archived => "archived",
            Status::Unsupported => "unsupported",
        }
    }
}

#[cfg(any(feature = "bench", test))]
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct OfficialSpecs {
    #[serde(default)]
    cpu_model: String,
    #[serde(default)]
    cores: u32,
    #[serde(default)]
    memory_gb: u32,
    #[serde(default)]
    os: String,
    #[serde(default)]
    arch: String,
    #[serde(default)]
    match_tolerance: MatchTolerance,
}

#[cfg(any(feature = "bench", test))]
#[derive(Debug, Clone, Serialize, Deserialize)]
struct MatchTolerance {
    #[serde(default = "default_memory_pct")]
    memory_pct: u32,
}

#[cfg(any(feature = "bench", test))]
impl Default for MatchTolerance {
    fn default() -> Self {
        Self {
            memory_pct: default_memory_pct(),
        }
    }
}

#[cfg(any(feature = "bench", test))]
fn default_memory_pct() -> u32 {
    10
}

/// A field is "stated" when the research wave filled it with a fact —
/// non-empty and not the literal "unknown" / "n/a …" placeholders.
#[cfg(any(feature = "bench", test))]
fn stated(s: &str) -> bool {
    let t = s.trim();
    !t.is_empty()
        && !t.eq_ignore_ascii_case("unknown")
        && !t.to_ascii_lowercase().starts_with("n/a")
}

#[cfg(any(feature = "bench", test))]
impl Registry {
    fn load(path: &Path) -> Result<Self> {
        let body = fs::read_to_string(path)
            .with_context(|| format!("read comparison registry {}", path.display()))?;
        Self::load_str(&body, &path.display().to_string())
    }

    fn load_str(body: &str, origin: &str) -> Result<Self> {
        let registry: Registry =
            toml::from_str(body).with_context(|| format!("parse comparison registry {origin}"))?;
        if registry.schema_version != 1 {
            bail!(
                "comparison registry {origin}: unsupported schema_version {} (expected 1)",
                registry.schema_version
            );
        }
        let mut seen = BTreeSet::new();
        for c in &registry.comparisons {
            c.validate()
                .with_context(|| format!("comparison {} in {origin}", c.id))?;
            if !seen.insert(c.id.clone()) {
                bail!(
                    "comparison registry {origin}: duplicate comparison id {}",
                    c.id
                );
            }
        }
        Ok(registry)
    }

    fn find(&self, id: &str) -> Result<&Comparison> {
        self.comparisons.iter().find(|c| c.id == id).ok_or_else(|| {
            anyhow!("comparison {id} not found in registry (try `ay bench compare list`)")
        })
    }
}

#[cfg(any(feature = "bench", test))]
impl Comparison {
    fn validate(&self) -> Result<()> {
        let kebab = !self.id.is_empty()
            && self
                .id
                .chars()
                .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-')
            && !self.id.starts_with('-')
            && !self.id.ends_with('-');
        if !kebab {
            bail!("id must be non-empty kebab-case [a-z0-9-]: {:?}", self.id);
        }
        if self.edition == 0 {
            bail!("edition must be the edition year (nonzero integer)");
        }
        if self.status == Status::Ready {
            if !self.specs_cited() {
                bail!(
                    "status=ready requires cited official_hosts plus parsed [comparison.official] fields"
                );
            }
            for (field, value) in [
                ("budgets", &self.budgets),
                ("scoring", &self.scoring),
                ("corpus", &self.corpus),
            ] {
                if !stated(value) {
                    bail!("status=ready requires `{field}` to be stated (got {value:?})");
                }
            }
            if self.citations.is_empty() {
                bail!("status=ready requires citations");
            }
        }
        Ok(())
    }

    /// Official specs are cited: the hosts prose is a fact (not "unknown" /
    /// "n/a") and at least one parsed host field was transcribed from it.
    fn specs_cited(&self) -> bool {
        stated(&self.official_hosts)
            && (!self.official.cpu_model.is_empty()
                || self.official.cores > 0
                || self.official.memory_gb > 0)
    }
}

// ---------------------------------------------------------------------------
// Sibling registries (read-only, minimal projections)
// ---------------------------------------------------------------------------

#[cfg(any(feature = "bench", test))]
#[derive(Debug, Deserialize)]
struct CorporaFile {
    #[serde(default, rename = "corpus")]
    corpora: Vec<CorpusRow>,
}

#[cfg(any(feature = "bench", test))]
#[derive(Debug, Clone, Deserialize)]
struct CorpusRow {
    name: String,
    #[serde(default)]
    extract_to: String,
}

#[cfg(any(feature = "bench", test))]
fn load_corpora(root: &Path) -> Option<Vec<CorpusRow>> {
    let body = fs::read_to_string(root.join(CORPORA_MANIFEST)).ok()?;
    toml::from_str::<CorporaFile>(&body).ok().map(|f| f.corpora)
}

#[cfg(any(feature = "bench", test))]
#[derive(Debug, Deserialize)]
struct ToolsFile {
    #[serde(default, rename = "tool")]
    tools: Vec<ToolRow>,
}

#[cfg(any(feature = "bench", test))]
#[derive(Debug, Clone, Deserialize)]
struct ToolRow {
    name: String,
    #[serde(default)]
    bin: String,
    #[serde(default)]
    install_to: String,
    #[serde(default)]
    extra_paths: Vec<String>,
}

#[cfg(any(feature = "bench", test))]
fn load_tools(root: &Path) -> Vec<ToolRow> {
    let Ok(body) = fs::read_to_string(root.join(TOOLS_REGISTRY)) else {
        return Vec::new();
    };
    toml::from_str::<ToolsFile>(&body)
        .map(|f| f.tools)
        .unwrap_or_default()
}

// ---------------------------------------------------------------------------
// Path resolution
// ---------------------------------------------------------------------------

/// Resolve a repo-relative path by walking from the cwd to the repo root
/// (corpora precedent extended per the design: registry-reading verbs work
/// from any subdirectory).
#[cfg(any(feature = "bench", test))]
fn resolve_repo_path(p: &Path) -> PathBuf {
    if p.is_absolute() || p.exists() {
        return p.to_path_buf();
    }
    if let Ok(cwd) = std::env::current_dir() {
        for dir in cwd.ancestors() {
            let cand = dir.join(p);
            if cand.exists() {
                return cand;
            }
        }
    }
    p.to_path_buf()
}

/// Repo root the sibling registries and packet dirs hang off: the parent of
/// the registry's `benchmarks/` dir, else the nearest ancestor with `.git`.
#[cfg(any(feature = "bench", test))]
fn repo_root_for(registry_path: &Path) -> PathBuf {
    if let Some(parent) = registry_path.parent() {
        if parent.file_name().is_some_and(|n| n == "benchmarks") {
            match parent.parent() {
                Some(root) if !root.as_os_str().is_empty() => return root.to_path_buf(),
                _ => return PathBuf::from("."),
            }
        }
    }
    if let Ok(cwd) = std::env::current_dir() {
        for dir in cwd.ancestors() {
            if dir.join(".git").exists() {
                return dir.to_path_buf();
            }
        }
    }
    PathBuf::from(".")
}

// ---------------------------------------------------------------------------
// Install state: corpus, winner references, packets
// ---------------------------------------------------------------------------

#[cfg(any(feature = "bench", test))]
#[derive(Debug, Clone)]
enum CorpusState {
    /// No corpora.toml mapping — fetched per the entry's `corpus` prose.
    External,
    Installed(PathBuf),
    Missing(PathBuf),
    /// `corpus_name` set but absent from corpora.toml.
    Unmapped(String),
    /// corpora.toml itself unreadable.
    NoRegistry,
}

#[cfg(any(feature = "bench", test))]
impl CorpusState {
    fn column(&self) -> &'static str {
        match self {
            CorpusState::External => "external",
            CorpusState::Installed(_) => "installed",
            CorpusState::Missing(_) => "missing",
            CorpusState::Unmapped(_) => "unmapped!",
            CorpusState::NoRegistry => "no-reg!",
        }
    }

    fn detail(&self) -> String {
        match self {
            CorpusState::External => {
                "not mapped to a benchmarks/corpora.toml entry; not verified locally".to_string()
            }
            CorpusState::Installed(p) => format!("installed at {}", p.display()),
            CorpusState::Missing(p) => {
                format!("mapped but not installed (expected at {})", p.display())
            }
            CorpusState::Unmapped(name) => {
                format!("corpus_name {name:?} not found in benchmarks/corpora.toml")
            }
            CorpusState::NoRegistry => "benchmarks/corpora.toml not readable".to_string(),
        }
    }
}

#[cfg(any(feature = "bench", test))]
fn corpus_state(root: &Path, corpora: Option<&[CorpusRow]>, entry: &Comparison) -> CorpusState {
    if entry.corpus_name.is_empty() {
        return CorpusState::External;
    }
    let Some(corpora) = corpora else {
        return CorpusState::NoRegistry;
    };
    let Some(row) = corpora.iter().find(|r| r.name == entry.corpus_name) else {
        return CorpusState::Unmapped(entry.corpus_name.clone());
    };
    let path = root.join(&row.extract_to);
    let present = path.is_file()
        || (path.is_dir()
            && fs::read_dir(&path)
                .map(|mut d| d.next().is_some())
                .unwrap_or(false));
    if present {
        CorpusState::Installed(path)
    } else {
        CorpusState::Missing(path)
    }
}

/// Derive the leading solver token from a researched winner prose line
/// ("1. Golem 0.9.0, 1259/1406 solved (…)" → "Golem"). Returns `None` when
/// the line names no solver ("Open: no medal awarded").
#[cfg(any(feature = "bench", test))]
fn winner_ref_name(winner: &str) -> Option<String> {
    let mut s = winner.trim();
    if s.starts_with(|c: char| c.is_ascii_digit()) {
        // "1." / "2 (tie)." rank prefixes
        if let Some(dot) = s.find('.') {
            if dot <= 8 {
                s = &s[dot + 1..];
            }
        }
    } else if let Some(colon) = s.find(':') {
        // "Gold:" / "Bronze (tie):" / "Local Search Silver:" medal prefixes
        if colon <= 24 && !s[..colon].contains("http") {
            s = &s[colon + 1..];
        }
    }
    let s = s.trim_start();
    let end = s.find([',', '(', ';', '—']).unwrap_or(s.len());
    let head = s[..end].trim();
    let token = head.split_whitespace().next()?;
    let token = token.trim_matches(|c: char| {
        !(c.is_ascii_alphanumeric() || c == '-' || c == '+' || c == '_' || c == '.')
    });
    if token.is_empty() || token.eq_ignore_ascii_case("no") {
        return None;
    }
    Some(token.to_string())
}

#[cfg(any(feature = "bench", test))]
fn is_executable_file(path: &Path) -> bool {
    if !path.is_file() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::metadata(path)
            .map(|m| m.permissions().mode() & 0o111 != 0)
            .unwrap_or(false)
    }
    #[cfg(not(unix))]
    {
        true
    }
}

#[cfg(any(feature = "bench", test))]
fn which(name: &str) -> Option<PathBuf> {
    let path_var = std::env::var_os("PATH")?;
    for dir in std::env::split_paths(&path_var) {
        let cand = dir.join(name);
        if is_executable_file(&cand) {
            return Some(cand);
        }
    }
    None
}

#[cfg(any(feature = "bench", test))]
fn expand_home(path: &str) -> PathBuf {
    if let Some(rest) = path.strip_prefix("~/") {
        if let Some(home) = std::env::var_os("HOME") {
            return PathBuf::from(home).join(rest);
        }
    }
    PathBuf::from(path)
}

/// Resolution order per the design §3.2: `$AY_TOOL_<NAME>` override →
/// `install_to` target → `extra_paths` → `$PATH`.
#[cfg(any(feature = "bench", test))]
fn resolve_tool(root: &Path, tool: &ToolRow) -> Option<PathBuf> {
    let env_key: String = format!(
        "AY_TOOL_{}",
        tool.name
            .to_uppercase()
            .chars()
            .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
            .collect::<String>()
    );
    if let Some(val) = std::env::var_os(&env_key) {
        let p = PathBuf::from(val);
        if p.exists() {
            return Some(p);
        }
    }
    if !tool.install_to.is_empty() {
        let target = expand_home(&tool.install_to);
        let target = if target.is_absolute() {
            target
        } else {
            root.join(target)
        };
        if is_executable_file(&target) {
            return Some(target);
        }
        if target.is_dir() && !tool.bin.is_empty() {
            let bin = target.join(&tool.bin);
            if is_executable_file(&bin) {
                return Some(bin);
            }
        }
    }
    for extra in &tool.extra_paths {
        let p = expand_home(extra);
        let p = if p.is_absolute() { p } else { root.join(p) };
        if is_executable_file(&p) {
            return Some(p);
        }
    }
    which(&tool.name)
}

#[cfg(any(feature = "bench", test))]
#[derive(Debug, Clone, Serialize)]
struct RefCheck {
    winner: String,
    /// Solver token derived from the winner prose; None = no solver named.
    name: Option<String>,
    /// Resolved binary path, when the token resolves at all.
    resolved: Option<PathBuf>,
    /// "tools.toml" or "PATH" when resolved.
    via: Option<&'static str>,
}

#[cfg(any(feature = "bench", test))]
fn check_refs(root: &Path, tools: &[ToolRow], entry: &Comparison) -> Vec<RefCheck> {
    entry
        .winners
        .iter()
        .map(|w| {
            let name = winner_ref_name(w);
            let mut resolved = None;
            let mut via = None;
            if let Some(token) = &name {
                if let Some(tool) = tools.iter().find(|t| t.name.eq_ignore_ascii_case(token)) {
                    if let Some(p) = resolve_tool(root, tool) {
                        resolved = Some(p);
                        via = Some("tools.toml");
                    }
                }
                if resolved.is_none() {
                    if let Some(p) = which(token).or_else(|| which(&token.to_lowercase())) {
                        resolved = Some(p);
                        via = Some("PATH");
                    }
                }
            }
            RefCheck {
                winner: w.clone(),
                name,
                resolved,
                via,
            }
        })
        .collect()
}

#[cfg(any(feature = "bench", test))]
#[derive(Debug, Clone, Copy, Default, Serialize)]
struct PacketCounts {
    official: u32,
    replay: u32,
    laptop: u32,
}

#[cfg(any(feature = "bench", test))]
impl PacketCounts {
    fn total(&self) -> u32 {
        self.official + self.replay + self.laptop
    }

    fn column(&self) -> String {
        if self.total() == 0 {
            return "0".to_string();
        }
        let mut parts = Vec::new();
        for (label, n) in [
            ("official", self.official),
            ("replay", self.replay),
            ("laptop", self.laptop),
        ] {
            if n > 0 {
                parts.push(format!("{label}:{n}"));
            }
        }
        parts.join(" ")
    }
}

/// Count packet dirs `evals/results/compare/<id>/<class>-<run-id>/` per class.
#[cfg(any(feature = "bench", test))]
fn packet_counts(root: &Path, id: &str) -> PacketCounts {
    let mut counts = PacketCounts::default();
    let dir = root.join(PACKET_ROOT).join(id);
    let Ok(entries) = fs::read_dir(&dir) else {
        return counts;
    };
    for e in entries.flatten() {
        if !e.path().is_dir() {
            continue;
        }
        let name = e.file_name();
        let Some(name) = name.to_str() else { continue };
        if name.starts_with("official-") {
            counts.official += 1;
        } else if name.starts_with("replay-") {
            counts.replay += 1;
        } else if name.starts_with("laptop-") {
            counts.laptop += 1;
        }
    }
    counts
}

// ---------------------------------------------------------------------------
// Local host capture + host check
// ---------------------------------------------------------------------------

#[cfg(any(feature = "bench", test))]
#[derive(Debug, Clone, Serialize)]
struct LocalHost {
    cpu_model: String,
    cores: u32,
    memory_bytes: u64,
    os: String,
    arch: String,
    hw_model: String,
}

#[cfg(any(feature = "bench", test))]
fn sysctl(name: &str) -> String {
    ProcCommand::new("sysctl")
        .arg("-n")
        .arg(name)
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_default()
}

/// Extract a stable Linux CPU identity without guessing marketing names.
/// x86 commonly exposes `model name`; ARM systems may expose only numeric
/// implementer/part IDs, so retain every distinct pair in sorted order.
#[cfg(any(feature = "bench", test))]
fn linux_cpu_model(cpuinfo: &str, arch: &str) -> String {
    if let Some(model) = cpuinfo.lines().find_map(|line| {
        let (key, value) = line.split_once(':')?;
        key.trim()
            .eq_ignore_ascii_case("model name")
            .then(|| value.trim())
            .filter(|value| !value.is_empty())
            .map(str::to_string)
    }) {
        return model;
    }

    let mut identities = BTreeSet::new();
    for record in cpuinfo.split("\n\n") {
        let mut implementer = None;
        let mut part = None;
        for line in record.lines() {
            let Some((key, value)) = line.split_once(':') else {
                continue;
            };
            match key.trim() {
                "CPU implementer" => implementer = Some(value.trim()),
                "CPU part" => part = Some(value.trim()),
                _ => {}
            }
        }
        if let (Some(implementer), Some(part)) = (implementer, part) {
            if !implementer.is_empty() && !part.is_empty() {
                identities.insert(format!("implementer {implementer} part {part}"));
            }
        }
    }

    if identities.is_empty() {
        arch.to_string()
    } else {
        format!(
            "{arch} [{}]",
            identities.into_iter().collect::<Vec<_>>().join(", ")
        )
    }
}

/// Read this machine's specs: macOS via `sysctl hw.model
/// machdep.cpu.brand_string hw.memsize hw.ncpu`, Linux via /proc/cpuinfo +
/// /proc/meminfo. Missing values stay 0/"" and print as unverifiable.
#[cfg(any(feature = "bench", test))]
fn read_local_host() -> LocalHost {
    let mut host = LocalHost {
        cpu_model: String::new(),
        cores: 0,
        memory_bytes: 0,
        os: std::env::consts::OS.to_string(),
        arch: std::env::consts::ARCH.to_string(),
        hw_model: String::new(),
    };
    if cfg!(target_os = "macos") {
        host.cpu_model = sysctl("machdep.cpu.brand_string");
        host.hw_model = sysctl("hw.model");
        host.cores = sysctl("hw.ncpu").parse().unwrap_or(0);
        host.memory_bytes = sysctl("hw.memsize").parse().unwrap_or(0);
    } else if cfg!(target_os = "linux") {
        if let Ok(cpuinfo) = fs::read_to_string("/proc/cpuinfo") {
            host.cores = cpuinfo
                .lines()
                .filter(|l| l.starts_with("processor"))
                .count() as u32;
            host.cpu_model = linux_cpu_model(&cpuinfo, &host.arch);
        }
        host.hw_model = fs::read_to_string("/sys/devices/virtual/dmi/id/product_name")
            .ok()
            .map(|value| value.trim().to_string())
            .filter(|value| !value.is_empty())
            .unwrap_or_default();
        if let Ok(meminfo) = fs::read_to_string("/proc/meminfo") {
            if let Some(kb) = meminfo
                .lines()
                .find(|l| l.starts_with("MemTotal:"))
                .and_then(|l| l.split_whitespace().nth(1))
                .and_then(|v| v.parse::<u64>().ok())
            {
                host.memory_bytes = kb * 1024;
            }
        }
    }
    if host.cores == 0 {
        host.cores = std::thread::available_parallelism()
            .map(|n| n.get() as u32)
            .unwrap_or(0);
    }
    host
}

#[cfg(any(feature = "bench", test))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
enum Verdict {
    ReplayEligible,
    LaptopOnly,
    SpecsPending,
}

#[cfg(any(feature = "bench", test))]
impl Verdict {
    fn label(&self) -> &'static str {
        match self {
            Verdict::ReplayEligible => "replay-eligible",
            Verdict::LaptopOnly => "laptop-only",
            Verdict::SpecsPending => "specs-pending",
        }
    }
}

#[cfg(any(feature = "bench", test))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
enum FieldResult {
    Pass,
    Fail,
    Unknown,
}

#[cfg(any(feature = "bench", test))]
#[derive(Debug, Clone, Serialize)]
struct FieldCheck {
    field: &'static str,
    official: String,
    local: String,
    result: FieldResult,
}

#[cfg(any(feature = "bench", test))]
fn norm_model(s: &str) -> String {
    s.to_lowercase()
        .replace("(r)", "")
        .replace("(tm)", "")
        .split_whitespace()
        // Brand strings interleave a "CPU" token ("Intel(R) Xeon(R) CPU
        // E3-1230 v5 @ 3.40GHz"); drop it so cited model names match.
        .filter(|w| *w != "cpu")
        .collect::<Vec<_>>()
        .join(" ")
}

/// Field-by-field host verdict (design §3.1 tolerances): arch exact, OS
/// family exact, CPU model substring, cores at least official, memory within
/// the entry's tolerance. Official fields left 0/"" are UNKNOWN; the three
/// identity fields (cpu_model, cores, memory) must be known AND pass for
/// replay-eligible — anything less is laptop-only, fail-closed.
#[cfg(any(feature = "bench", test))]
fn host_check(spec: &OfficialSpecs, local: &LocalHost) -> (Verdict, Vec<FieldCheck>) {
    let mut fields = Vec::new();

    let arch = if spec.arch.is_empty() {
        FieldResult::Unknown
    } else if spec.arch.eq_ignore_ascii_case(&local.arch) {
        FieldResult::Pass
    } else {
        FieldResult::Fail
    };
    fields.push(FieldCheck {
        field: "arch",
        official: display_or_unknown(&spec.arch),
        local: local.arch.clone(),
        result: arch,
    });

    let os = if spec.os.is_empty() {
        FieldResult::Unknown
    } else if spec.os.eq_ignore_ascii_case(&local.os) {
        FieldResult::Pass
    } else {
        FieldResult::Fail
    };
    fields.push(FieldCheck {
        field: "os",
        official: display_or_unknown(&spec.os),
        local: local.os.clone(),
        result: os,
    });

    let cpu = if spec.cpu_model.is_empty() {
        FieldResult::Unknown
    } else if norm_model(&local.cpu_model).contains(&norm_model(&spec.cpu_model)) {
        FieldResult::Pass
    } else {
        FieldResult::Fail
    };
    fields.push(FieldCheck {
        field: "cpu_model",
        official: display_or_unknown(&spec.cpu_model),
        local: display_or_unknown(&local.cpu_model),
        result: cpu,
    });

    let cores = if spec.cores == 0 {
        FieldResult::Unknown
    } else if local.cores >= spec.cores {
        FieldResult::Pass
    } else {
        FieldResult::Fail
    };
    fields.push(FieldCheck {
        field: "cores",
        official: if spec.cores == 0 {
            "(not stated)".into()
        } else {
            spec.cores.to_string()
        },
        local: local.cores.to_string(),
        result: cores,
    });

    let local_gib = local.memory_bytes as f64 / (1u64 << 30) as f64;
    let local_gb = local.memory_bytes as f64 / 1e9;
    let memory = if spec.memory_gb == 0 {
        FieldResult::Unknown
    } else {
        let official = spec.memory_gb as f64;
        let pct = spec.match_tolerance.memory_pct as f64 / 100.0;
        // The cited "GB" may be either unit convention; pass if the local
        // total is within tolerance under either reading.
        let within = |local: f64| (local - official).abs() <= official * pct;
        if within(local_gib) || within(local_gb) {
            FieldResult::Pass
        } else {
            FieldResult::Fail
        }
    };
    fields.push(FieldCheck {
        field: "memory",
        official: if spec.memory_gb == 0 {
            "(not stated)".into()
        } else {
            format!(
                "{} GB (±{}%)",
                spec.memory_gb, spec.match_tolerance.memory_pct
            )
        },
        local: format!("{local_gib:.1} GiB"),
        result: memory,
    });

    let any_fail = fields.iter().any(|f| f.result == FieldResult::Fail);
    let identity_known = !spec.cpu_model.is_empty() && spec.cores > 0 && spec.memory_gb > 0;
    let verdict = if any_fail || !identity_known {
        Verdict::LaptopOnly
    } else {
        Verdict::ReplayEligible
    };
    (verdict, fields)
}

#[cfg(any(feature = "bench", test))]
fn display_or_unknown(s: &str) -> String {
    if s.is_empty() {
        "(not stated)".to_string()
    } else {
        s.to_string()
    }
}

#[cfg(any(feature = "bench", test))]
fn snippet(s: &str, max_chars: usize) -> String {
    let mut out: String = s.chars().take(max_chars).collect();
    if s.chars().count() > max_chars {
        out.push('…');
    }
    out
}

// ---------------------------------------------------------------------------
// Verb implementations
// ---------------------------------------------------------------------------

/// Entry point for `ay bench compare`, dispatched from `cmd_bench::run`
/// (which carries the `--features bench` gate for the whole group).
#[cfg(any(feature = "bench", test))]
#[cfg_attr(not(feature = "bench"), allow(dead_code))]
pub(crate) fn run(args: BenchCompareArgs) -> Result<()> {
    let registry_path = resolve_repo_path(&args.registry);
    let code = match args.command {
        CompareCommand::List(list) => run_list(&registry_path, list)?,
        CompareCommand::Show(show) => run_show(&registry_path, show)?,
        CompareCommand::Check(check) => run_check(&registry_path, check)?,
    };
    if code != 0 {
        use std::io::Write as _;
        let _ = std::io::stdout().flush();
        let _ = std::io::stderr().flush();
        std::process::exit(code);
    }
    Ok(())
}

#[cfg(any(feature = "bench", test))]
fn run_list(registry_path: &Path, args: ListArgs) -> Result<i32> {
    let registry = Registry::load(registry_path)?;
    let root = repo_root_for(registry_path);
    let corpora = load_corpora(&root);
    let tools = load_tools(&root);

    let mut rows = Vec::new();
    for c in &registry.comparisons {
        if let Some(filter) = args.competition {
            if c.competition != filter {
                continue;
            }
        }
        let corpus = corpus_state(&root, corpora.as_deref(), c);
        let refs = check_refs(&root, &tools, c);
        let built = refs.iter().filter(|r| r.resolved.is_some()).count();
        let packets = packet_counts(&root, &c.id);
        rows.push((c, corpus, built, refs.len(), packets));
    }

    if args.json {
        let json_rows: Vec<serde_json::Value> = rows
            .iter()
            .map(|(c, corpus, built, total, packets)| {
                serde_json::json!({
                    "id": c.id,
                    "competition": c.competition.label(),
                    "edition": c.edition,
                    "status": c.status.label(),
                    "specs": if c.specs_cited() { "cited" } else { "unknown" },
                    "corpus": corpus.column(),
                    "refs": { "built": built, "total": total },
                    "packets": packets,
                })
            })
            .collect();
        println!("{}", serde_json::to_string_pretty(&json_rows)?);
        return Ok(0);
    }

    println!(
        "{:<40} {:<11} {:<7} {:<13} {:<7} {:<10} {:<6} PACKETS",
        "ID", "COMPETITION", "EDITION", "STATUS", "SPECS", "CORPUS", "REFS"
    );
    for (c, corpus, built, total, packets) in rows {
        let refs = if total == 0 {
            "-".to_string()
        } else {
            format!("{built}/{total}")
        };
        println!(
            "{:<40} {:<11} {:<7} {:<13} {:<7} {:<10} {:<6} {}",
            c.id,
            c.competition.label(),
            c.edition,
            c.status.label(),
            if c.specs_cited() { "cited" } else { "unknown" },
            corpus.column(),
            refs,
            packets.column(),
        );
    }
    Ok(0)
}

#[cfg(any(feature = "bench", test))]
fn run_show(registry_path: &Path, args: ShowArgs) -> Result<i32> {
    let registry = Registry::load(registry_path)?;
    let entry = registry.find(&args.id)?;
    let root = repo_root_for(registry_path);
    let corpora = load_corpora(&root);
    let tools = load_tools(&root);
    let corpus = corpus_state(&root, corpora.as_deref(), entry);
    let refs = check_refs(&root, &tools, entry);
    let packets = packet_counts(&root, &entry.id);

    if args.json {
        let value = serde_json::json!({
            "entry": entry,
            "install_state": {
                "corpus": { "state": corpus.column(), "detail": corpus.detail() },
                "refs": refs,
                "packets": packets,
            },
        });
        println!("{}", serde_json::to_string_pretty(&value)?);
        return Ok(0);
    }

    println!("id:            {}", entry.id);
    println!("competition:   {}", entry.competition.label());
    println!("edition:       {}", entry.edition);
    println!("track:         {}", entry.track);
    println!("status:        {}", entry.status.label());
    if !entry.notes.is_empty() {
        println!("notes:         {}", entry.notes);
    }
    println!("official_hosts:");
    println!("    {}", display_or_unknown(&entry.official_hosts));
    if entry.specs_cited() {
        let o = &entry.official;
        println!("parsed official specs (used by `compare check`):");
        println!(
            "    cpu_model={:?}  cores={}  memory_gb={}  os={}  arch={}  memory_tolerance=±{}%",
            o.cpu_model,
            o.cores,
            o.memory_gb,
            display_or_unknown(&o.os),
            display_or_unknown(&o.arch),
            o.match_tolerance.memory_pct,
        );
    }
    println!("budgets:");
    println!("    {}", display_or_unknown(&entry.budgets));
    println!("scoring:");
    println!("    {}", display_or_unknown(&entry.scoring));
    println!("corpus:");
    println!("    {}", display_or_unknown(&entry.corpus));
    println!("    local: {}", corpus.detail());
    if entry.winners.is_empty() {
        println!("winners:       (none recorded)");
    } else {
        println!("winners:");
        for r in &refs {
            println!("  - {}", r.winner);
            match (&r.name, &r.resolved, r.via) {
                (Some(name), Some(path), Some(via)) => {
                    println!("      ref {name}: {} (via {via})", path.display());
                }
                (Some(name), _, _) => {
                    println!("      ref {name}: unresolved (no tools.toml recipe; not on PATH)");
                }
                (None, _, _) => {}
            }
        }
    }
    println!("citations:");
    for c in &entry.citations {
        println!("  - {c}");
    }
    println!(
        "packets:       {} (under {}/{}/)",
        packets.column(),
        PACKET_ROOT,
        entry.id
    );
    Ok(0)
}

#[cfg(any(feature = "bench", test))]
fn run_check(registry_path: &Path, args: CheckArgs) -> Result<i32> {
    let registry = Registry::load(registry_path)?;
    let entry = registry.find(&args.id)?;
    let root = repo_root_for(registry_path);
    let corpora = load_corpora(&root);
    let tools = load_tools(&root);

    let corpus = corpus_state(&root, corpora.as_deref(), entry);
    let refs = check_refs(&root, &tools, entry);
    let built = refs.iter().filter(|r| r.resolved.is_some()).count();
    let scoring_stated = stated(&entry.scoring);
    let budgets_stated = stated(&entry.budgets);

    // Runnable = the comparison could be driven on this machine at all:
    // corpus available (or external-but-stated), every winner reference
    // resolved, scoring and budgets stated.
    let corpus_ok = match &corpus {
        CorpusState::Installed(_) => true,
        CorpusState::External => stated(&entry.corpus),
        CorpusState::Missing(_) | CorpusState::Unmapped(_) | CorpusState::NoRegistry => false,
    };
    let refs_ok = !refs.is_empty() && built == refs.len();
    let mut not_runnable: Vec<String> = Vec::new();
    if !corpus_ok {
        not_runnable.push(format!("corpus: {}", corpus.detail()));
    }
    if !refs_ok {
        not_runnable.push(format!(
            "winner references unresolved ({built}/{})",
            refs.len()
        ));
    }
    if !scoring_stated {
        not_runnable.push("scoring not stated".to_string());
    }
    if !budgets_stated {
        not_runnable.push("budgets not stated".to_string());
    }
    let runnable = not_runnable.is_empty();

    let local = read_local_host();
    let (verdict, fields) = if entry.specs_cited() {
        host_check(&entry.official, &local)
    } else {
        (Verdict::SpecsPending, Vec::new())
    };

    let code = if verdict == Verdict::SpecsPending || !runnable {
        2
    } else if verdict == Verdict::ReplayEligible {
        0
    } else {
        1
    };

    if args.json {
        let value = serde_json::json!({
            "id": entry.id,
            "status": entry.status.label(),
            "corpus": { "state": corpus.column(), "detail": corpus.detail() },
            "refs": refs,
            "scoring_stated": scoring_stated,
            "budgets_stated": budgets_stated,
            "runnable": runnable,
            "local_host": local,
            "official": entry.official,
            "host_fields": fields,
            "verdict": verdict.label(),
            "exit_code": code,
        });
        println!("{}", serde_json::to_string_pretty(&value)?);
        return Ok(code);
    }

    println!(
        "check {} — {} {} — {}",
        entry.id,
        entry.competition.label(),
        entry.edition,
        snippet(&entry.track, 60)
    );
    println!("status:   {}", entry.status.label());
    println!();
    println!("corpus:   {} — {}", corpus.column(), corpus.detail());
    println!("refs:     {built}/{} winner references resolve", refs.len());
    for r in &refs {
        match (&r.name, &r.resolved, r.via) {
            (Some(name), Some(path), Some(via)) => {
                println!("          - {name}: {} (via {via})", path.display());
            }
            (Some(name), _, _) => {
                println!("          - {name}: unresolved (no tools.toml recipe; not on PATH)");
            }
            (None, _, _) => {
                println!("          - (no solver named: {})", snippet(&r.winner, 48));
            }
        }
    }
    println!(
        "scoring:  {}",
        if scoring_stated {
            format!("stated — {}", snippet(&entry.scoring, 60))
        } else {
            "NOT STATED".to_string()
        }
    );
    println!(
        "budgets:  {}",
        if budgets_stated {
            format!("stated — {}", snippet(&entry.budgets, 60))
        } else {
            "NOT STATED".to_string()
        }
    );
    println!();
    println!(
        "host:     {} — {} cores, {:.1} GiB, {}/{}",
        display_or_unknown(&local.cpu_model),
        local.cores,
        local.memory_bytes as f64 / (1u64 << 30) as f64,
        local.os,
        local.arch,
    );
    match verdict {
        Verdict::SpecsPending => {
            println!(
                "official: no cited specs (official_hosts: {})",
                snippet(&entry.official_hosts, 48)
            );
            println!();
            println!("verdict: specs-pending — the entry has no cited specs");
        }
        _ => {
            let o = &entry.official;
            println!(
                "official: {} — {} cores, {} GB, {}/{} (memory tolerance ±{}%)",
                display_or_unknown(&o.cpu_model),
                if o.cores == 0 {
                    "?".to_string()
                } else {
                    o.cores.to_string()
                },
                if o.memory_gb == 0 {
                    "?".to_string()
                } else {
                    o.memory_gb.to_string()
                },
                display_or_unknown(&o.os),
                display_or_unknown(&o.arch),
                o.match_tolerance.memory_pct,
            );
            for f in &fields {
                let mark = match f.result {
                    FieldResult::Pass => "pass",
                    FieldResult::Fail => "FAIL",
                    FieldResult::Unknown => "unknown",
                };
                println!(
                    "  {:<10} {:<8} official {} vs local {}",
                    f.field, mark, f.official, f.local
                );
            }
            println!();
            match verdict {
                Verdict::ReplayEligible => println!(
                    "verdict: replay-eligible — this host may run `compare run --class replay`"
                ),
                Verdict::LaptopOnly => {
                    let mismatched: Vec<&str> = fields
                        .iter()
                        .filter(|f| f.result == FieldResult::Fail)
                        .map(|f| f.field)
                        .collect();
                    if mismatched.is_empty() {
                        println!(
                            "verdict: laptop-only — official specs incomplete; replay cannot be verified (fail-closed)"
                        );
                    } else {
                        println!(
                            "verdict: laptop-only — mismatched: {}",
                            mismatched.join(", ")
                        );
                    }
                }
                Verdict::SpecsPending => unreachable!(),
            }
        }
    }
    if !runnable {
        println!("not runnable:");
        for reason in &not_runnable {
            println!("  - {reason}");
        }
    }
    println!("exit: {code}");
    Ok(code)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn repo_path(rel: &str) -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .join(rel)
    }

    fn minimal_entry(id: &str, status: &str) -> String {
        format!(
            r#"
[[comparison]]
id          = "{id}"
competition = "smtcomp"
edition     = 2025
track       = "t"
status      = "{status}"
official_hosts = "Intel Xeon E3-1230 v5, 4 cores, 33 GB"
budgets     = "20 min"
scoring     = "sequential"
corpus      = "https://example.org/corpus.tar"
citations   = ["https://example.org"]

  [comparison.official]
  cpu_model = "Intel Xeon E3-1230 v5"
  cores     = 4
  memory_gb = 33
  os        = "linux"
  arch      = "x86_64"
"#
        )
    }

    // ---------- shipped registry ----------

    #[test]
    fn shipped_registry_parses_and_validates() {
        let path = repo_path(DEFAULT_REGISTRY);
        let registry = Registry::load(&path).expect("shipped comparisons.toml loads");
        assert_eq!(registry.comparisons.len(), 37);
        let ids: BTreeSet<&str> = registry.comparisons.iter().map(|c| c.id.as_str()).collect();
        assert_eq!(ids.len(), 37, "ids must be unique");
        assert!(ids.contains("smtcomp-2025-single-query-qf-lia"));
        assert!(ids.contains("satcomp-2025-main"));
        // Every ready entry has cited + parsed specs; specs-pending entries
        // are exactly the two with "n/a" hosts.
        for c in &registry.comparisons {
            match c.status {
                Status::Ready => assert!(c.specs_cited(), "{}: ready without cited specs", c.id),
                Status::SpecsPending => {
                    assert!(!c.specs_cited(), "{}: specs-pending but specs cited", c.id)
                }
                Status::Archived => {}
                Status::Unsupported => {}
            }
        }
        let pending: Vec<&str> = registry
            .comparisons
            .iter()
            .filter(|c| c.status == Status::SpecsPending)
            .map(|c| c.id.as_str())
            .collect();
        assert_eq!(
            pending,
            vec!["smtcomp-2025-proof-exhibition", "miplib-2017-benchmark"]
        );
    }

    #[test]
    fn shipped_corpus_names_resolve_in_corpora_toml() {
        let registry = Registry::load(&repo_path(DEFAULT_REGISTRY)).unwrap();
        let corpora = load_corpora(&repo_path("")).expect("corpora.toml parses");
        for c in &registry.comparisons {
            if c.corpus_name.is_empty() {
                continue;
            }
            assert!(
                corpora.iter().any(|r| r.name == c.corpus_name),
                "{}: corpus_name {:?} not in benchmarks/corpora.toml",
                c.id,
                c.corpus_name
            );
        }
    }

    // ---------- registry validation ----------

    #[test]
    fn duplicate_ids_rejected() {
        let body = format!(
            "schema_version = 1\n{}{}",
            minimal_entry("dup-id", "ready"),
            minimal_entry("dup-id", "ready")
        );
        let err = Registry::load_str(&body, "inline").unwrap_err();
        assert!(
            err.to_string().contains("duplicate comparison id"),
            "{err:#}"
        );
    }

    #[test]
    fn status_enum_is_closed() {
        // The old research-wave label is not a valid status.
        let body = format!(
            "schema_version = 1\n{}",
            minimal_entry("x-1", "specs-recorded")
        );
        assert!(Registry::load_str(&body, "inline").is_err());
        for status in ["specs-pending", "ready", "archived"] {
            let body = format!("schema_version = 1\n{}", minimal_entry("x-1", status));
            Registry::load_str(&body, "inline")
                .unwrap_or_else(|e| panic!("status {status} should parse: {e:#}"));
        }
    }

    #[test]
    fn competition_set_is_closed() {
        let body = minimal_entry("x-1", "ready").replace("\"smtcomp\"", "\"smtco\"");
        let body = format!("schema_version = 1\n{body}");
        assert!(Registry::load_str(&body, "inline").is_err());
    }

    #[test]
    fn ids_must_be_kebab_case() {
        for bad in ["Bad-Id", "x_1", "", "-x", "x-"] {
            let body = format!("schema_version = 1\n{}", minimal_entry(bad, "ready"));
            assert!(
                Registry::load_str(&body, "inline").is_err(),
                "id {bad:?} should be rejected"
            );
        }
    }

    #[test]
    fn ready_requires_cited_specs() {
        let body = minimal_entry("x-1", "ready").replace(
            "official_hosts = \"Intel Xeon E3-1230 v5, 4 cores, 33 GB\"",
            "official_hosts = \"unknown\"",
        );
        let body = format!("schema_version = 1\n{body}");
        let err = Registry::load_str(&body, "inline").unwrap_err();
        assert!(format!("{err:#}").contains("status=ready"), "{err:#}");
        // The same entry is fine as specs-pending.
        let body = minimal_entry("x-1", "specs-pending").replace(
            "official_hosts = \"Intel Xeon E3-1230 v5, 4 cores, 33 GB\"",
            "official_hosts = \"unknown\"",
        );
        let body = format!("schema_version = 1\n{body}");
        Registry::load_str(&body, "inline").expect("specs-pending entry loads");
    }

    #[test]
    fn wrong_schema_version_rejected() {
        let body = format!("schema_version = 2\n{}", minimal_entry("x-1", "ready"));
        assert!(Registry::load_str(&body, "inline").is_err());
    }

    // ---------- winner prose → ref token ----------

    #[test]
    fn winner_ref_name_extracts_solver_tokens() {
        let cases = [
            (
                "AE-Kissat-MAB, package AE_kissat2025_MAB (Kissat 4.0.2 base)",
                Some("AE-Kissat-MAB"),
            ),
            ("cvc5 1.3.0 release (SMT-COMP 2025 build)", Some("cvc5")),
            ("OpenSMT v2.9.2 (5471 solved)", Some("OpenSMT")),
            ("1. Golem 0.9.0, 1259/1406 solved, 0 wrong", Some("Golem")),
            ("2 (tie). Cara (Petr Illner, Charles Univ.)", Some("Cara")),
            (
                "2. d4 (Lagniez/Marquis, CRIL) — https://github.com/crillab/d4v2",
                Some("d4"),
            ),
            (
                "Gold: OR-Tools CP-SAT (version not published)",
                Some("OR-Tools"),
            ),
            (
                "Bronze (tie): SICStus Prolog (https://sicstus.sics.se/)",
                Some("SICStus"),
            ),
            (
                "Local Search Silver: Yuck — https://github.com/informarte/yuck",
                Some("Yuck"),
            ),
            (
                "Silver: PicatSAT — http://picat-lang.org/",
                Some("PicatSAT"),
            ),
            (
                "roundingsat+pbsuma-log, 387 solved incl. uncertified",
                Some("roundingsat+pbsuma-log"),
            ),
            ("Open: no medal awarded (no portfolio entrants)", None),
        ];
        for (prose, want) in cases {
            assert_eq!(winner_ref_name(prose).as_deref(), want, "prose: {prose:?}");
        }
    }

    // ---------- host capture + verdict ----------

    #[test]
    fn linux_cpu_model_prefers_marketing_model_when_present() {
        let cpuinfo = "processor : 0\nmodel name : Example CPU 123\n";
        assert_eq!(linux_cpu_model(cpuinfo, "x86_64"), "Example CPU 123");
    }

    #[test]
    fn linux_cpu_model_falls_back_to_sorted_distinct_arm_ids() {
        let cpuinfo = "\
processor : 0\n\
CPU implementer : 0x41\n\
CPU part : 0xd87\n\
\n\
processor : 1\n\
CPU implementer : 0x41\n\
CPU part : 0xd87\n\
\n\
processor : 2\n\
CPU implementer : 0x41\n\
CPU part : 0xd4f\n";
        assert_eq!(
            linux_cpu_model(cpuinfo, "aarch64"),
            "aarch64 [implementer 0x41 part 0xd4f, implementer 0x41 part 0xd87]"
        );
    }

    #[test]
    fn local_host_parse_smoke() {
        let host = read_local_host();
        assert!(host.cores > 0, "cores should be detected");
        if cfg!(any(target_os = "macos", target_os = "linux")) {
            assert!(host.memory_bytes > 0, "memory should be detected");
            assert!(!host.cpu_model.is_empty(), "cpu model should be detected");
        }
        assert!(!host.os.is_empty());
        assert!(!host.arch.is_empty());
    }

    fn local(cpu: &str, cores: u32, gib: u64, os: &str, arch: &str) -> LocalHost {
        LocalHost {
            cpu_model: cpu.to_string(),
            cores,
            memory_bytes: gib << 30,
            os: os.to_string(),
            arch: arch.to_string(),
            hw_model: String::new(),
        }
    }

    fn spec(cpu: &str, cores: u32, memory_gb: u32, os: &str, arch: &str) -> OfficialSpecs {
        OfficialSpecs {
            cpu_model: cpu.to_string(),
            cores,
            memory_gb,
            os: os.to_string(),
            arch: arch.to_string(),
            match_tolerance: MatchTolerance::default(),
        }
    }

    #[test]
    fn host_check_matching_host_is_replay_eligible() {
        let official = spec("Intel Xeon E3-1230 v5", 4, 33, "linux", "x86_64");
        let host = local(
            "Intel(R) Xeon(R) CPU E3-1230 v5 @ 3.40GHz",
            8,
            32,
            "linux",
            "x86_64",
        );
        let (verdict, fields) = host_check(&official, &host);
        assert_eq!(verdict, Verdict::ReplayEligible, "fields: {fields:?}");
    }

    #[test]
    fn host_check_arch_mismatch_is_laptop_only() {
        let official = spec("Intel Xeon E3-1230 v5", 4, 33, "linux", "x86_64");
        let host = local("Apple M2 Max", 12, 96, "macos", "aarch64");
        let (verdict, fields) = host_check(&official, &host);
        assert_eq!(verdict, Verdict::LaptopOnly);
        let arch = fields.iter().find(|f| f.field == "arch").unwrap();
        assert_eq!(arch.result, FieldResult::Fail);
    }

    #[test]
    fn host_check_incomplete_specs_fail_closed() {
        // memory not stated → cannot verify → laptop-only even if the rest match.
        let official = spec("AMD EPYC 7313", 32, 0, "linux", "x86_64");
        let host = local(
            "AMD EPYC 7313 32-Core Processor",
            32,
            256,
            "linux",
            "x86_64",
        );
        let (verdict, _) = host_check(&official, &host);
        assert_eq!(verdict, Verdict::LaptopOnly);
    }

    #[test]
    fn host_check_memory_tolerance_accepts_both_unit_readings() {
        // Official "30 GB": a 32-GiB machine is within 10% under the GiB
        // reading; a 20-GiB machine is not under either.
        let official = spec("Intel Xeon E3-1230 v5", 8, 30, "", "x86_64");
        let ok = local("Intel Xeon E3-1230 v5", 8, 32, "linux", "x86_64");
        let (verdict, _) = host_check(&official, &ok);
        assert_eq!(verdict, Verdict::ReplayEligible);
        let small = local("Intel Xeon E3-1230 v5", 8, 20, "linux", "x86_64");
        let (verdict, fields) = host_check(&official, &small);
        assert_eq!(verdict, Verdict::LaptopOnly);
        let mem = fields.iter().find(|f| f.field == "memory").unwrap();
        assert_eq!(mem.result, FieldResult::Fail);
    }

    // ---------- verbs against the shipped registry ----------

    #[test]
    fn verbs_run_against_shipped_registry() {
        let registry = repo_path(DEFAULT_REGISTRY);
        let code = run_list(
            &registry,
            ListArgs {
                competition: Some(Competition::Smtcomp),
                json: true,
            },
        )
        .expect("list runs");
        assert_eq!(code, 0);
        let code = run_show(
            &registry,
            ShowArgs {
                id: "satcomp-2025-main".to_string(),
                json: false,
            },
        )
        .expect("show runs");
        assert_eq!(code, 0);
        // check's exit code is host-dependent (0/1/2 per the help contract);
        // a nonexistent id is a hard error instead.
        let code = run_check(
            &registry,
            CheckArgs {
                id: "chccomp-2026-lia-lin".to_string(),
                json: true,
            },
        )
        .expect("check runs");
        assert!(
            (0..=2).contains(&code),
            "check exit code {code} out of contract"
        );
        assert!(run_check(
            &registry,
            CheckArgs {
                id: "no-such-entry".to_string(),
                json: false
            }
        )
        .is_err());
    }

    // ---------- help text (the design's drafts are the spec) ----------

    #[test]
    fn help_matches_design_drafts() {
        let cmd = <BenchCompareArgs as Args>::augment_args(clap::Command::new("compare"));
        let group = cmd.clone().render_long_help().to_string();
        assert!(group.contains("Every number produced here carries exactly one run class"));
        assert!(group.contains("official  imported published results"));
        assert!(group.contains("replay is granted by a host check and refused on mismatch"));
        // 0.1.0 verbs present; runner verbs only as roadmap.
        for verb in ["list", "show", "check"] {
            assert!(
                cmd.find_subcommand(verb).is_some(),
                "verb {verb} missing from the compare group"
            );
        }
        for verb in ["refs", "run", "import", "report"] {
            assert!(
                cmd.find_subcommand(verb).is_none(),
                "post-0.1.0 verb {verb} must not exist at 0.1.0"
            );
            assert!(
                group.contains(verb),
                "group help must state the {verb} roadmap"
            );
        }
        assert!(group.contains("--registry"));
        assert!(group.contains("benchmarks/comparisons.toml"));

        let check = cmd
            .find_subcommand("check")
            .unwrap()
            .clone()
            .render_long_help()
            .to_string();
        assert!(check.contains("replay-eligible   this host may run `compare run --class replay`"));
        assert!(check.contains("Exit codes: 0 = entry runnable and replay-eligible"));
        assert!(check.contains("There is no override flag"));

        let list = cmd
            .find_subcommand("list")
            .unwrap()
            .clone()
            .render_long_help()
            .to_string();
        assert!(list.contains("ID, COMPETITION, EDITION, STATUS, SPECS (cited/unknown)"));
        assert!(list.contains("--competition"));
    }

    // ---------- packets ----------

    #[test]
    fn packet_counts_reads_class_prefixed_dirs() {
        let dir = tempfile::TempDir::new().unwrap();
        let base = dir.path().join(PACKET_ROOT).join("x-1");
        for d in ["official-2026-01-01", "laptop-a", "laptop-b", "unrelated"] {
            fs::create_dir_all(base.join(d)).unwrap();
        }
        let counts = packet_counts(dir.path(), "x-1");
        assert_eq!(counts.official, 1);
        assert_eq!(counts.replay, 0);
        assert_eq!(counts.laptop, 2);
        assert_eq!(counts.column(), "official:1 laptop:2");
        assert_eq!(packet_counts(dir.path(), "missing").column(), "0");
    }
}
