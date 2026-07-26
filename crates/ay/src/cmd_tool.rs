// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `ay tool` — build, verify, and locate external tools from pinned recipes.
//!
//! Registry: `reference/tools.toml` (schema:
//! the development design notes §3.2). Data chooses, code executes:
//! `recipe` is the closed enum below and build arguments are argv arrays,
//! never shell strings — an unknown recipe, or a string where an argv array
//! belongs, is a load error, so the registry cannot smuggle arbitrary code.
//! Installs are idempotent: probe-if-working, fetch pinned source, build,
//! install, re-verify, print resolved paths.
//!
//! Resolution order (fixed; one implementation used by every consumer):
//! `$AY_TOOL_<NAME>` env override → `install_to` target → `extra_paths` →
//! `$PATH`.
//!
//! The drat-trim and cadical recipes are transcribed from the hard-coded
//! `ay corpus install-tool` implementation (cmd_corpus.rs) — behavior and
//! install targets byte-identical; that verb is becoming a deprecated alias
//! for `ay tool install` reading this same registry.

use std::collections::BTreeSet;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command as ProcCommand, Stdio};

use anyhow::{anyhow, bail, Context, Result};
use clap::{Args, Subcommand, ValueEnum};
use serde::{Deserialize, Serialize};

const DEFAULT_MANIFEST: &str = "reference/tools.toml";

// ---------------------------------------------------------------------------
// CLI surface
// ---------------------------------------------------------------------------

#[derive(Args)]
#[command(
    about = "Build, verify, and locate external tools from pinned recipes",
    long_about = "Build, verify, and locate external tools from pinned recipes

Registry: reference/tools.toml. Recipes pin each tool's source, revision,
and build steps — proof checkers (drat-trim, cadical, veripb, carcara) and
competition-pinned reference solvers (e.g. kissat-sc2025) share one install
and resolution story. Installs are idempotent: probe-if-working, fetch
pinned source, build, install, re-verify, print resolved paths. Build steps
are a closed recipe set executed by this binary; the registry cannot run
arbitrary code. `ay corpus install-tool` is a deprecated alias for
`ay tool install`."
)]
pub(crate) struct ToolArgs {
    /// Tool registry
    #[arg(long, global = true, value_name = "FILE", default_value = DEFAULT_MANIFEST)]
    manifest: PathBuf,
    #[command(subcommand)]
    command: ToolCommand,
}

#[derive(Subcommand)]
enum ToolCommand {
    /// List recipes with kind, pin, and install status
    #[command(long_about = "List recipes with kind, pin, and install status

Columns: NAME, KIND, SOURCE, PIN, STATUS, RESOLVED PATH. STATUS is
installed (verify probe passes), stale (installed but pin changed), or
missing.")]
    List(ListArgs),
    /// Build and install a tool (or a group) from its pinned recipe
    #[command(
        long_about = "Build and install a tool (or a group) from its pinned recipe

Each install is: preflight the recipe's `requires` list on PATH, probe the
existing binary (exit 0 if it already verifies, unless --force), fetch the
pinned source, run the recipe's build steps (argv arrays, never
shell-interpreted), install to the recipe target, re-run the verify probe,
print every path in the resolution order. Unpinned recipes install with a
warning; reference-solver recipes must be pinned."
    )]
    Install(InstallArgs),
    /// Print the resolved path of a tool
    #[command(long_about = "Print the resolved path of a tool

Resolution order: $AY_TOOL_<NAME> override, the recipe's install target,
the recipe's extra fallback paths, then $PATH. Exit 1 with every searched
path when unresolved. Scripts should use this instead of hard-coding tool
locations:
  VERIPB=$(ay tool which veripb)")]
    Which(WhichArgs),
    /// Re-run the verify probe for installed tools
    Verify(VerifyArgs),
}

#[derive(Args)]
struct ListArgs {
    /// Only this kind
    #[arg(long, value_enum)]
    kind: Option<Kind>,
    /// Only recipes in a group (e.g. audit, sat, pb)
    #[arg(long)]
    group: Option<String>,
    /// Emit the table as JSON
    #[arg(long)]
    json: bool,
}

#[derive(Args)]
struct InstallArgs {
    /// Tool names (e.g. drat-trim cadical)
    names: Vec<String>,
    /// Install every recipe in a group (e.g. --group audit)
    #[arg(long)]
    group: Option<String>,
    /// Rebuild even if the existing binary verifies
    #[arg(long)]
    force: bool,
}

#[derive(Args)]
struct WhichArgs {
    /// Tool name from reference/tools.toml
    name: String,
    /// Print every candidate with hit/miss instead of the first hit
    #[arg(long)]
    all: bool,
}

#[derive(Args)]
struct VerifyArgs {
    /// Tool names; all registered tools when omitted
    names: Vec<String>,
}

// ---------------------------------------------------------------------------
// Registry schema (design §3.2)
// ---------------------------------------------------------------------------

#[derive(Debug, Serialize, Deserialize)]
struct Registry {
    schema_version: u32,
    #[serde(default, rename = "tool")]
    tools: Vec<Tool>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct Tool {
    name: String,
    kind: Kind,
    /// Install groups, e.g. `ay tool install --group audit`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    groups: Vec<String>,
    source: SourceKind,
    // git / http-archive / cargo: upstream URL.
    #[serde(skip_serializing_if = "Option::is_none")]
    url: Option<String>,
    /// Commit pin. `Some("")` is declared-but-unpinned: the tip builds with an
    /// install-time warning (the design's sanctioned pre-0.1.0 state for
    /// cadical: "transcribed as-is pre-0.1.0; pin post-0.1.0").
    #[serde(skip_serializing_if = "Option::is_none")]
    commit: Option<String>,
    /// Tag pin (alternative to `commit`).
    #[serde(skip_serializing_if = "Option::is_none")]
    tag: Option<String>,
    // http-archive: tarball pin.
    #[serde(skip_serializing_if = "Option::is_none")]
    sha256: Option<String>,
    // pip: package spec (may itself be a pinned `pkg==v` / `git+url@tag` spec).
    #[serde(skip_serializing_if = "Option::is_none")]
    spec: Option<String>,
    // script: scripts/index.toml entry name for genuinely custom installs.
    #[serde(skip_serializing_if = "Option::is_none")]
    script: Option<String>,
    /// Closed build-step set implemented by this binary.
    #[serde(skip_serializing_if = "Option::is_none")]
    recipe: Option<Recipe>,
    /// Recipe-specific argv fragments; NEVER shell-interpreted.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    recipe_args: Vec<String>,
    /// Clone/build inside `install_to` (the reference/cadical convention).
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    in_place: bool,
    /// Produced artifact, relative to the build tree (cargo: the installed
    /// binary name in ~/.cargo/bin).
    #[serde(skip_serializing_if = "Option::is_none")]
    bin: Option<String>,
    /// Install target: either the final binary path (~ expands) or the build
    /// tree the artifact sits in. Repo-relative paths resolve from the root.
    #[serde(skip_serializing_if = "Option::is_none")]
    install_to: Option<String>,
    /// Verify probe argv; `{bin}` substitutes the resolved binary. Run after
    /// install and by `ay tool verify`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    verify: Vec<String>,
    /// Substring expected in the probe's stdout+stderr (case-insensitive).
    /// When set, the probe's exit code is ignored — drat-trim prints its
    /// usage banner and exits non-zero (legacy semantics preserved).
    #[serde(skip_serializing_if = "Option::is_none")]
    verify_expect: Option<String>,
    /// PATH preflight before an install.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    requires: Vec<String>,
    /// Legacy resolver fallbacks; a directory entry probes `<dir>/<bin>`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    extra_paths: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, ValueEnum)]
#[serde(rename_all = "kebab-case")]
enum Kind {
    Checker,
    ReferenceSolver,
    Utility,
}

impl Kind {
    fn label(&self) -> &'static str {
        match self {
            Kind::Checker => "checker",
            Kind::ReferenceSolver => "reference-solver",
            Kind::Utility => "utility",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
enum SourceKind {
    Git,
    HttpArchive,
    Pip,
    Cargo,
    Script,
}

impl SourceKind {
    fn label(&self) -> &'static str {
        match self {
            SourceKind::Git => "git",
            SourceKind::HttpArchive => "http-archive",
            SourceKind::Pip => "pip",
            SourceKind::Cargo => "cargo",
            SourceKind::Script => "script",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
enum Recipe {
    CcSingleFile,
    ConfigureMake,
    Make,
    Cmake,
    CargoBuild,
}

impl Registry {
    fn load(path: &Path) -> Result<Self> {
        let body = fs::read_to_string(path)
            .with_context(|| format!("read tool registry {}", path.display()))?;
        let registry: Registry = toml::from_str(&body)
            .with_context(|| format!("parse tool registry {}", path.display()))?;
        if registry.schema_version != 1 {
            bail!(
                "tool registry {}: unsupported schema_version {} (expected 1)",
                path.display(),
                registry.schema_version
            );
        }
        let mut seen = BTreeSet::new();
        for t in &registry.tools {
            if !seen.insert(t.name.clone()) {
                bail!(
                    "tool registry {}: duplicate tool name {}",
                    path.display(),
                    t.name
                );
            }
            t.validate()
                .with_context(|| format!("tool {} in {}", t.name, path.display()))?;
        }
        Ok(registry)
    }

    fn find(&self, name: &str) -> Result<&Tool> {
        self.tools
            .iter()
            .find(|t| t.name == name)
            .ok_or_else(|| anyhow!("tool {name} not found in registry"))
    }
}

impl Tool {
    fn validate(&self) -> Result<()> {
        if self.name.is_empty()
            || !self
                .name
                .chars()
                .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-')
        {
            bail!("tool names are kebab-case ([a-z0-9-])");
        }
        if self.verify.is_empty() {
            bail!("`verify` requires a non-empty argv array");
        }
        if self.verify.iter().any(String::is_empty) {
            bail!("`verify` argv elements must be non-empty");
        }
        if self.recipe_args.iter().any(String::is_empty) {
            bail!("`recipe_args` argv elements must be non-empty");
        }
        match self.source {
            SourceKind::Git => {
                if self.url.is_none() {
                    bail!("source=git requires `url`");
                }
                let recipe = self
                    .recipe
                    .ok_or_else(|| anyhow!("source=git requires `recipe`"))?;
                if self.bin.is_none() {
                    bail!("source=git requires `bin`");
                }
                if self.install_to.is_none() {
                    bail!("source=git requires `install_to`");
                }
                if recipe == Recipe::CcSingleFile && self.recipe_args.is_empty() {
                    bail!("recipe=cc-single-file requires `recipe_args` (the C source files)");
                }
                if self.spec.is_some() {
                    bail!("source=git does not use `spec`");
                }
                if self.script.is_some() {
                    bail!("source=git does not use `script`");
                }
            }
            SourceKind::HttpArchive => {
                if self.url.is_none() {
                    bail!("source=http-archive requires `url`");
                }
                if self.sha256.is_none() {
                    bail!("source=http-archive requires `sha256`");
                }
                if self.recipe.is_none() {
                    bail!("source=http-archive requires `recipe`");
                }
                if self.bin.is_none() || self.install_to.is_none() {
                    bail!("source=http-archive requires `bin` and `install_to`");
                }
            }
            SourceKind::Pip => {
                if self.spec.is_none() {
                    bail!("source=pip requires `spec`");
                }
                if self.recipe.is_some() {
                    bail!("source=pip does not use `recipe` (a pip install has no build steps)");
                }
                if self.url.is_some() {
                    bail!("source=pip does not use `url` — put a `git+<url>` spec in `spec`");
                }
            }
            SourceKind::Cargo => {
                if self.url.is_none() {
                    bail!("source=cargo requires `url`");
                }
                if self.bin.is_none() {
                    bail!("source=cargo requires `bin` (the installed binary name)");
                }
                if self.recipe.is_some() {
                    bail!("source=cargo does not use `recipe` (`cargo install` is the build)");
                }
                if self.spec.is_some() {
                    bail!("source=cargo does not use `spec`");
                }
                // Pin-drift detectability. `cargo install` drops a bare binary
                // in ~/.cargo/bin with no record of the revision that built it,
                // and `pin_mismatch` can only interrogate an in-place git
                // checkout — so for a commit-pinned cargo tool the version
                // probe is the ONLY drift signal there is. Without a
                // `verify_expect` naming the pin, an arbitrarily old binary
                // reports `installed`, which for a proof CHECKER means audits
                // silently replay against un-pinned rules. Require the probe to
                // name the pin (a prefix of `commit`, i.e. the short hash a
                // version banner prints). A tool whose `--version` cannot
                // reveal its revision must be pinned by `tag` instead.
                if let Some(commit) = self.commit.as_deref().filter(|c| !c.is_empty()) {
                    let expect = self.verify_expect.as_deref().unwrap_or_default();
                    if expect.is_empty() {
                        bail!(
                            "source=cargo with a `commit` pin requires `verify_expect` \
                             (a prefix of the commit) so pin drift is detectable"
                        );
                    }
                    if !commit.eq_ignore_ascii_case(expect)
                        && !commit
                            .to_ascii_lowercase()
                            .starts_with(expect.to_ascii_lowercase().as_str())
                    {
                        bail!(
                            "`verify_expect` ({expect}) must be a prefix of `commit` ({commit}) \
                             so the version probe actually pins the revision"
                        );
                    }
                }
            }
            SourceKind::Script => {
                if self.script.is_none() {
                    bail!("source=script requires `script` (a scripts/index.toml entry name)");
                }
                if self.recipe.is_some() {
                    bail!("source=script does not use `recipe` (the indexed script is the build)");
                }
            }
        }
        // reference-solver recipes must declare their pin field (`tag` or
        // `commit`). `commit = ""` is declared-but-unpinned — the design's
        // sanctioned pre-0.1.0 state for cadical; installs warn until pinned.
        if self.kind == Kind::ReferenceSolver && self.tag.is_none() && self.commit.is_none() {
            bail!("kind=reference-solver requires a `tag` or `commit` pin field");
        }
        Ok(())
    }

    /// The effective pin, if any: a non-empty tag or commit, or (for pip) a
    /// version/revision embedded in the package spec.
    fn pin_label(&self) -> String {
        if let Some(tag) = self.tag.as_deref().filter(|t| !t.is_empty()) {
            return tag.to_string();
        }
        if let Some(commit) = self.commit.as_deref().filter(|c| !c.is_empty()) {
            return commit.chars().take(12).collect();
        }
        if self.source == SourceKind::Pip {
            if let Some(spec) = self.spec.as_deref() {
                if let Some((_, v)) = spec.split_once("==") {
                    return v.to_string();
                }
                if let Some((_, v)) = spec.rsplit_once('@') {
                    return v.to_string();
                }
            }
        }
        "tip".to_string()
    }

    fn pinned(&self) -> bool {
        self.pin_label() != "tip"
    }
}

// ---------------------------------------------------------------------------
// Path resolution ($AY_TOOL_<NAME> → install target → extra_paths → $PATH)
// ---------------------------------------------------------------------------

/// One entry of the resolution order. `path` is `None` when the candidate has
/// no path at all (env override unset / no `$PATH` hit); `absent` is the text
/// printed for that case.
struct Candidate {
    label: String,
    path: Option<PathBuf>,
    absent: &'static str,
}

impl Candidate {
    fn hit(&self) -> bool {
        self.path.as_deref().is_some_and(is_executable_file)
    }

    fn describe(&self) -> String {
        match &self.path {
            None => self.absent.to_string(),
            Some(p) if is_executable_file(p) => format!("hit  {}", p.display()),
            Some(p) => format!("miss {}", p.display()),
        }
    }
}

/// `$AY_TOOL_<NAME>`: name uppercased, non-alphanumeric → `_`.
fn env_override_name(name: &str) -> String {
    let mut out = String::from("AY_TOOL_");
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch.to_ascii_uppercase());
        } else {
            out.push('_');
        }
    }
    out
}

/// Basename the tool is looked up as on `$PATH` (and under directory
/// `extra_paths`): the `bin` file name when set, else the tool name.
fn bin_file_name(tool: &Tool) -> String {
    tool.bin
        .as_deref()
        .and_then(|b| Path::new(b).file_name())
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_else(|| tool.name.clone())
}

/// The recipe's install target, resolved: `install_to` may name the final
/// binary itself (drat-trim's `~/.local/bin/drat-trim`) or the build tree the
/// artifact sits in (cadical's `reference/cadical` + `build/cadical`). Cargo
/// recipes without `install_to` land in `$CARGO_HOME/bin` (default
/// `~/.cargo/bin`).
fn install_target(tool: &Tool, root: &Path) -> Option<PathBuf> {
    if let Some(install_to) = tool.install_to.as_deref() {
        let base = expand_path(root, install_to);
        if let Some(bin) = tool.bin.as_deref() {
            if base.ends_with(bin) {
                return Some(base);
            }
            return Some(base.join(bin));
        }
        return Some(base);
    }
    if tool.source == SourceKind::Cargo {
        if let Some(bin) = tool.bin.as_deref() {
            return Some(cargo_bin_dir().join(bin));
        }
    }
    None
}

fn cargo_bin_dir() -> PathBuf {
    if let Some(home) = env::var_os("CARGO_HOME") {
        return PathBuf::from(home).join("bin");
    }
    match env::var_os("HOME") {
        Some(home) => PathBuf::from(home).join(".cargo/bin"),
        None => PathBuf::from(".cargo/bin"),
    }
}

/// Expand a registry path: `~/` → `$HOME`, relative → repo-root-relative.
fn expand_path(root: &Path, raw: &str) -> PathBuf {
    if let Some(rest) = raw.strip_prefix("~/") {
        if let Some(home) = env::var_os("HOME") {
            return PathBuf::from(home).join(rest);
        }
    }
    let path = PathBuf::from(raw);
    if path.is_absolute() {
        path
    } else {
        root.join(path)
    }
}

fn path_lookup(bin_name: &str) -> Option<PathBuf> {
    let path_var = env::var_os("PATH")?;
    env::split_paths(&path_var)
        .map(|dir| dir.join(bin_name))
        .find(|p| is_executable_file(p))
}

fn is_executable_file(path: &Path) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::metadata(path)
            .map(|m| m.is_file() && m.permissions().mode() & 0o111 != 0)
            .unwrap_or(false)
    }
    #[cfg(not(unix))]
    {
        path.is_file()
    }
}

/// Every candidate in the fixed resolution order.
fn candidates(tool: &Tool, root: &Path) -> Vec<Candidate> {
    let mut out = Vec::new();
    let env_name = env_override_name(&tool.name);
    out.push(Candidate {
        label: format!("${env_name}"),
        path: env::var_os(&env_name).map(PathBuf::from),
        absent: "unset",
    });
    if let Some(target) = install_target(tool, root) {
        out.push(Candidate {
            label: "install target".to_string(),
            path: Some(target),
            absent: "",
        });
    }
    let bin_name = bin_file_name(tool);
    for raw in &tool.extra_paths {
        let p = expand_path(root, raw);
        let p = if p.is_dir() { p.join(&bin_name) } else { p };
        out.push(Candidate {
            label: "extra path".to_string(),
            path: Some(p),
            absent: "",
        });
    }
    out.push(Candidate {
        label: format!("$PATH ({bin_name})"),
        path: path_lookup(&bin_name),
        absent: "miss (not on $PATH)",
    });
    out
}

/// First hit in the resolution order, if any.
fn resolve(tool: &Tool, root: &Path) -> Option<PathBuf> {
    candidates(tool, root)
        .into_iter()
        .find(Candidate::hit)
        .and_then(|c| c.path)
}

// ---------------------------------------------------------------------------
// Verify probe
// ---------------------------------------------------------------------------

/// The probe argv with `{bin}` substituted. When the registry wrote a plain
/// PATH name as argv[0] (e.g. `["veripb", "--help"]`), the resolved binary is
/// run instead, so probe and resolution can never diverge.
fn probe_argv(tool: &Tool, bin: &Path) -> Vec<String> {
    let bin_str = bin.to_string_lossy();
    let mut argv: Vec<String> = tool
        .verify
        .iter()
        .map(|a| a.replace("{bin}", &bin_str))
        .collect();
    if !tool.verify.iter().any(|a| a.contains("{bin}")) {
        if let Some(first) = argv.first_mut() {
            *first = bin_str.into_owned();
        }
    }
    argv
}

/// Run the verify probe against the resolved binary. With `verify_expect` the
/// probe passes iff stdout+stderr contain the substring (case-insensitive;
/// exit code deliberately ignored — drat-trim prints its usage banner and
/// exits non-zero). Without it the probe passes iff the command exits 0.
fn probe_passes(tool: &Tool, bin: &Path) -> bool {
    let argv = probe_argv(tool, bin);
    let Some((program, args)) = argv.split_first() else {
        return false;
    };
    let mut cmd = ProcCommand::new(program);
    cmd.args(args).stdin(Stdio::null());
    match tool.verify_expect.as_deref() {
        Some(expect) => match cmd.output() {
            Ok(out) => {
                let mut text = String::from_utf8_lossy(&out.stdout).into_owned();
                text.push_str(&String::from_utf8_lossy(&out.stderr));
                text.to_lowercase().contains(&expect.to_lowercase())
            }
            Err(_) => false,
        },
        None => matches!(
            cmd.stdout(Stdio::null()).stderr(Stdio::null()).status(),
            Ok(s) if s.success()
        ),
    }
}

/// STATUS for `list`: missing (unresolved), stale (resolved but the probe
/// fails, or an in-place checkout moved off its commit pin), installed.
fn install_state(tool: &Tool, root: &Path) -> (&'static str, Option<PathBuf>) {
    let Some(path) = resolve(tool, root) else {
        return ("missing", None);
    };
    if !probe_passes(tool, &path) {
        return ("stale", Some(path));
    }
    if pin_mismatch(tool, root) {
        return ("stale", Some(path));
    }
    ("installed", Some(path))
}

/// Pin drift is only checkable for in-place git build trees with a commit
/// pin: compare the checkout's HEAD against the pin.
fn pin_mismatch(tool: &Tool, root: &Path) -> bool {
    if tool.source != SourceKind::Git || !tool.in_place {
        return false;
    }
    let Some(pin) = tool.commit.as_deref().filter(|c| !c.is_empty()) else {
        return false;
    };
    let Some(dir) = tool.install_to.as_deref() else {
        return false;
    };
    let out = ProcCommand::new("git")
        .arg("-C")
        .arg(expand_path(root, dir))
        .args(["rev-parse", "HEAD"])
        .stderr(Stdio::null())
        .output();
    match out {
        Ok(o) if o.status.success() => {
            let head = String::from_utf8_lossy(&o.stdout).trim().to_string();
            !head.starts_with(pin)
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Verb dispatch
// ---------------------------------------------------------------------------

pub(crate) fn run(args: ToolArgs) -> Result<i32> {
    let root = repo_root();
    let manifest = resolve_registry_path(&root, &args.manifest);
    let registry = Registry::load(&manifest)?;
    match args.command {
        ToolCommand::List(a) => run_list(&registry, &root, a),
        ToolCommand::Install(a) => run_install(&registry, &root, a),
        ToolCommand::Which(a) => run_which(&registry, &root, a),
        ToolCommand::Verify(a) => run_verify(&registry, &root, a),
    }
}

/// Entry point for the deprecated `ay corpus install-tool` alias: install
/// `name` from the default registry — same behavior as `ay tool install NAME`.
/// (Consumed by the `ay corpus install-tool` wiring in cmd_corpus.rs.)
pub(crate) fn install_alias(name: &str, force: bool) -> Result<i32> {
    let root = repo_root();
    let manifest = resolve_registry_path(&root, Path::new(DEFAULT_MANIFEST));
    let registry = Registry::load(&manifest)?;
    install_tool(registry.find(name)?, &root, force)?;
    Ok(0)
}

/// Walk up from the current directory to the repo root (`.git` is a directory
/// in a primary checkout and a file in a worktree). Falls back to the current
/// directory outside a repo, preserving the plain-relative-path behavior the
/// corpus manifest precedent relies on.
fn repo_root() -> PathBuf {
    let cwd = env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let mut dir = cwd.clone();
    loop {
        if dir.join(".git").exists() {
            return dir;
        }
        if !dir.pop() {
            return cwd;
        }
    }
}

/// Resolve `--manifest`: absolute (or cwd-resolvable) paths as given, else
/// repo-root-relative — so the default `reference/tools.toml` works from any
/// subdirectory.
fn resolve_registry_path(root: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() || path.exists() {
        return path.to_path_buf();
    }
    let rooted = root.join(path);
    if rooted.exists() {
        rooted
    } else {
        path.to_path_buf()
    }
}

fn run_list(registry: &Registry, root: &Path, args: ListArgs) -> Result<i32> {
    let rows: Vec<&Tool> = registry
        .tools
        .iter()
        .filter(|t| args.kind.is_none_or(|k| t.kind == k))
        .filter(|t| {
            args.group
                .as_deref()
                .is_none_or(|g| t.groups.iter().any(|x| x == g))
        })
        .collect();
    if args.json {
        let table: Vec<serde_json::Value> = rows
            .iter()
            .map(|t| {
                let (status, path) = install_state(t, root);
                serde_json::json!({
                    "name": t.name,
                    "kind": t.kind.label(),
                    "source": t.source.label(),
                    "pin": t.pin_label(),
                    "status": status,
                    "path": path.map(|p| p.display().to_string()),
                })
            })
            .collect();
        println!("{}", serde_json::to_string_pretty(&table)?);
        return Ok(0);
    }
    println!(
        "{:<16} {:<17} {:<13} {:<14} {:<10} RESOLVED PATH",
        "NAME", "KIND", "SOURCE", "PIN", "STATUS"
    );
    for t in rows {
        let (status, path) = install_state(t, root);
        println!(
            "{:<16} {:<17} {:<13} {:<14} {:<10} {}",
            t.name,
            t.kind.label(),
            t.source.label(),
            t.pin_label(),
            status,
            path.map(|p| p.display().to_string())
                .unwrap_or_else(|| "-".into()),
        );
    }
    Ok(0)
}

fn run_install(registry: &Registry, root: &Path, args: InstallArgs) -> Result<i32> {
    let targets = select_tools(registry, &args.names, args.group.as_deref())?;
    for tool in targets {
        install_tool(tool, root, args.force)?;
    }
    Ok(0)
}

fn select_tools<'a>(
    registry: &'a Registry,
    names: &[String],
    group: Option<&str>,
) -> Result<Vec<&'a Tool>> {
    match (names.is_empty(), group) {
        (false, Some(_)) => bail!("--group is mutually exclusive with explicit tool names"),
        (true, Some(group)) => {
            let tools: Vec<&Tool> = registry
                .tools
                .iter()
                .filter(|t| t.groups.iter().any(|g| g == group))
                .collect();
            if tools.is_empty() {
                bail!("no recipes in group {group:?}");
            }
            Ok(tools)
        }
        (true, None) => bail!("specify at least one tool name, or --group"),
        (false, None) => names.iter().map(|n| registry.find(n)).collect(),
    }
}

fn run_which(registry: &Registry, root: &Path, args: WhichArgs) -> Result<i32> {
    let tool = registry.find(&args.name)?;
    if args.all {
        let cands = candidates(tool, root);
        let any_hit = cands.iter().any(Candidate::hit);
        for c in &cands {
            println!("{:<28} {}", c.label, c.describe());
        }
        return Ok(if any_hit { 0 } else { 1 });
    }
    match resolve(tool, root) {
        Some(path) => {
            println!("{}", path.display());
            Ok(0)
        }
        None => {
            eprintln!("{}: not found; searched:", tool.name);
            for c in candidates(tool, root) {
                eprintln!("  {:<28} {}", c.label, c.describe());
            }
            Ok(1)
        }
    }
}

fn run_verify(registry: &Registry, root: &Path, args: VerifyArgs) -> Result<i32> {
    let targets: Vec<&Tool> = if args.names.is_empty() {
        registry.tools.iter().collect()
    } else {
        args.names
            .iter()
            .map(|n| registry.find(n))
            .collect::<Result<_>>()?
    };
    let mut bad = 0usize;
    for tool in targets {
        match resolve(tool, root) {
            None => {
                println!(
                    "{}: not installed (try `ay tool install {}`)",
                    tool.name, tool.name
                );
                bad += 1;
            }
            Some(path) => {
                if probe_passes(tool, &path) {
                    println!("{}: ok ({})", tool.name, path.display());
                } else {
                    println!(
                        "{}: FAIL (probe `{}` on {})",
                        tool.name,
                        tool.verify.join(" "),
                        path.display()
                    );
                    bad += 1;
                }
            }
        }
    }
    Ok(if bad == 0 { 0 } else { 1 })
}

// ---------------------------------------------------------------------------
// Install
// ---------------------------------------------------------------------------

fn install_tool(tool: &Tool, root: &Path, force: bool) -> Result<()> {
    let name = &tool.name;
    // Preflight the recipe's `requires` list on PATH (cadical precedent).
    for req in &tool.requires {
        if !runs_on_path(req) {
            bail!("{name}: required tool {req:?} not found on PATH");
        }
    }
    // Idempotent fast path: probe the existing binary.
    if !force {
        if let Some(path) = resolve(tool, root) {
            if probe_passes(tool, &path) {
                println!("{name}: already installed and working");
                println!("  path: {}", path.display());
                println!("  (re-run with --force to rebuild)");
                print_resolution(tool, root);
                return Ok(());
            }
            eprintln!(
                "{name}: found {} but its verify probe failed; rebuilding...",
                path.display()
            );
        }
    }
    if !tool.pinned() {
        eprintln!("warning: {name}: no commit/tag pin — building the upstream tip");
        if tool.kind == Kind::ReferenceSolver {
            eprintln!(
                "warning: {name}: reference-solver recipes should be pinned \
                 (pre-0.1.0 transcription exception; pin post-0.1.0)"
            );
        }
    }
    match tool.source {
        SourceKind::Git => install_from_git(tool, root)?,
        SourceKind::Cargo => install_from_cargo(tool)?,
        SourceKind::Pip => install_from_pip(tool)?,
        SourceKind::HttpArchive => bail!(
            "{name}: source=http-archive install is not implemented in 0.1.0 \
             (no registry entry uses it)"
        ),
        SourceKind::Script => bail!(
            "{name}: source=script recipes install via their indexed script — \
             see `ay scripts run`"
        ),
    }
    // Re-verify, fail closed.
    let Some(path) = resolve(tool, root) else {
        print_resolution(tool, root);
        bail!("{name}: install completed but no binary resolved");
    };
    if !probe_passes(tool, &path) {
        bail!(
            "{name}: installed binary at {} failed its verify probe",
            path.display()
        );
    }
    println!();
    println!("{name}: installed and verified.");
    println!("  path: {}", path.display());
    print_resolution(tool, root);
    Ok(())
}

/// Print every path in the resolution order with hit/miss (the generalized
/// form of the legacy drat-trim fallback note).
fn print_resolution(tool: &Tool, root: &Path) {
    println!("  resolution order:");
    for c in candidates(tool, root) {
        println!("    {:<28} {}", c.label, c.describe());
    }
}

fn install_from_git(tool: &Tool, root: &Path) -> Result<()> {
    let url = tool.url.as_deref().expect("validate: git requires url");
    match tool.recipe.expect("validate: git requires recipe") {
        Recipe::CcSingleFile => {
            let target = install_target(tool, root).expect("validate: git requires install_to");
            let build_dir = make_temp_dir(&format!("{}-build", tool.name))?;
            let result = build_cc_single_file(tool, url, &build_dir, &target);
            let _ = fs::remove_dir_all(&build_dir);
            result
        }
        Recipe::ConfigureMake | Recipe::Make | Recipe::Cmake | Recipe::CargoBuild => {
            build_in_tree(tool, url, root)
        }
    }
}

/// cc-single-file: clone into a scratch dir, `cc -O2 -o <bin> <recipe_args>`,
/// copy the artifact to the install target (drat-trim, byte-identical).
fn build_cc_single_file(tool: &Tool, url: &str, build_dir: &Path, target: &Path) -> Result<()> {
    let name = &tool.name;
    let src_dir = build_dir.join("src");
    git_fetch(tool, url, &src_dir)?;
    let bin_name = bin_file_name(tool);
    let built = src_dir.join(&bin_name);
    println!(
        "{name}: building (cc -O2 -o {bin_name} {}) ...",
        tool.recipe_args.join(" ")
    );
    let mut cmd = ProcCommand::new("cc");
    cmd.current_dir(&src_dir).arg("-O2").arg("-o").arg(&built);
    // argv array straight into exec — never a shell.
    cmd.args(&tool.recipe_args);
    let status = cmd.status().context("invoke cc")?;
    if !status.success() {
        bail!("cc exited with {:?}", status.code());
    }
    if !built.is_file() {
        bail!("build did not produce an executable");
    }
    println!("{name}: installing to {} ...", target.display());
    if let Some(parent) = target.parent() {
        fs::create_dir_all(parent).with_context(|| format!("mkdir -p {}", parent.display()))?;
    }
    fs::copy(&built, target)
        .with_context(|| format!("install {} -> {}", built.display(), target.display()))?;
    make_executable(target)?;
    Ok(())
}

/// configure-make / make / cmake / cargo-build: the build tree IS the install
/// tree (`install_to`), with the artifact at `install_to`/`bin` — the
/// reference/cadical convention, byte-identical for cadical.
fn build_in_tree(tool: &Tool, url: &str, root: &Path) -> Result<()> {
    let name = &tool.name;
    let recipe = tool.recipe.expect("validate: git requires recipe");
    let tree = expand_path(
        root,
        tool.install_to
            .as_deref()
            .expect("validate: git requires install_to"),
    );
    // Fresh clone unless the tree already looks like a checkout (cadical
    // keeps its gitignored reference/cadical checkout between rebuilds).
    let marker = match recipe {
        Recipe::ConfigureMake => "configure",
        _ => ".git",
    };
    if !tree.join(marker).exists() {
        if tree.exists() {
            fs::remove_dir_all(&tree)
                .with_context(|| format!("rm -rf stale {}", tree.display()))?;
        }
        if let Some(parent) = tree.parent() {
            fs::create_dir_all(parent).with_context(|| format!("mkdir -p {}", parent.display()))?;
        }
        git_fetch(tool, url, &tree)?;
    }
    let run_step = |program: &str, args: &[&str], extra: &[String]| -> Result<()> {
        let mut shown = args.join(" ");
        if !extra.is_empty() {
            if !shown.is_empty() {
                shown.push(' ');
            }
            shown.push_str(&extra.join(" "));
        }
        println!("{name}: {program} {shown}...");
        let status = ProcCommand::new(program)
            .args(args)
            .args(extra)
            .current_dir(&tree)
            .status()
            .with_context(|| format!("invoke {program}"))?;
        if !status.success() {
            bail!("{name}: {program} exited with {:?}", status.code());
        }
        Ok(())
    };
    match recipe {
        Recipe::ConfigureMake => {
            run_step("./configure", &[], &tool.recipe_args)?;
            run_step("make", &[], &[])?;
        }
        Recipe::Make => {
            run_step("make", &[], &tool.recipe_args)?;
        }
        Recipe::Cmake => {
            run_step(
                "cmake",
                &["-B", "build", "-DCMAKE_BUILD_TYPE=Release"],
                &tool.recipe_args,
            )?;
            run_step("cmake", &["--build", "build"], &[])?;
        }
        Recipe::CargoBuild => {
            run_step("cargo", &["build", "--release"], &tool.recipe_args)?;
        }
        Recipe::CcSingleFile => unreachable!("dispatched to build_cc_single_file"),
    }
    Ok(())
}

/// Clone `url` into `dir` at the tool's pin. Unpinned and tag pins clone
/// shallow (`--depth 1`, the legacy behavior); a commit pin needs history, so
/// it clones full and checks the commit out.
fn git_fetch(tool: &Tool, url: &str, dir: &Path) -> Result<()> {
    let name = &tool.name;
    let commit = tool.commit.as_deref().filter(|c| !c.is_empty());
    let tag = tool.tag.as_deref().filter(|t| !t.is_empty());
    let mut cmd = ProcCommand::new("git");
    cmd.args(["clone", "--quiet"]);
    match (commit, tag) {
        (Some(commit), _) => {
            println!("{name}: cloning {url} at {commit} ...");
        }
        (None, Some(tag)) => {
            println!("{name}: cloning {url} at tag {tag} (shallow) ...");
            cmd.args(["--depth", "1", "--branch", tag]);
        }
        (None, None) => {
            println!("{name}: cloning {url} (shallow) ...");
            cmd.args(["--depth", "1"]);
        }
    }
    cmd.arg(url).arg(dir);
    let status = cmd.status().context("invoke git clone")?;
    if !status.success() {
        bail!("git clone exited with {:?}", status.code());
    }
    if let Some(commit) = commit {
        let status = ProcCommand::new("git")
            .arg("-C")
            .arg(dir)
            .args(["checkout", "--quiet", commit])
            .status()
            .context("invoke git checkout")?;
        if !status.success() {
            bail!("git checkout {commit} exited with {:?}", status.code());
        }
    }
    Ok(())
}

/// cargo: `cargo install --git <url> [--tag <tag> | --rev <commit>]`.
fn install_from_cargo(tool: &Tool) -> Result<()> {
    let name = &tool.name;
    if !runs_on_path("cargo") {
        bail!("{name}: required tool \"cargo\" not found on PATH");
    }
    let url = tool.url.as_deref().expect("validate: cargo requires url");
    let mut cmd = ProcCommand::new("cargo");
    cmd.args(["install", "--git", url]);
    let mut pin = String::new();
    if let Some(tag) = tool.tag.as_deref().filter(|t| !t.is_empty()) {
        cmd.args(["--tag", tag]);
        pin = format!(" --tag {tag}");
    } else if let Some(commit) = tool.commit.as_deref().filter(|c| !c.is_empty()) {
        cmd.args(["--rev", commit]);
        pin = format!(" --rev {commit}");
    }
    println!("{name}: cargo install --git {url}{pin} ...");
    let status = cmd.status().context("invoke cargo install")?;
    if !status.success() {
        bail!("{name}: cargo install exited with {:?}", status.code());
    }
    Ok(())
}

/// pip: `pip3 install <spec>` (or `python3 -m pip install <spec>`).
fn install_from_pip(tool: &Tool) -> Result<()> {
    let name = &tool.name;
    let spec = tool.spec.as_deref().expect("validate: pip requires spec");
    let mut cmd = if runs_on_path("pip3") {
        let mut c = ProcCommand::new("pip3");
        c.arg("install");
        c
    } else if runs_on_path("python3") {
        let mut c = ProcCommand::new("python3");
        c.args(["-m", "pip", "install"]);
        c
    } else {
        bail!("{name}: neither pip3 nor python3 found on PATH");
    };
    cmd.arg(spec);
    println!("{name}: pip install {spec} ...");
    let status = cmd.status().context("invoke pip install")?;
    if !status.success() {
        bail!("{name}: pip install exited with {:?}", status.code());
    }
    Ok(())
}

/// Does `tool --version` run cleanly on PATH? (Shared probe shape with the
/// corpus module's `which`.)
fn runs_on_path(tool: &str) -> bool {
    ProcCommand::new(tool)
        .arg("--version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

/// Make `path` executable (chmod +x equivalent). No-op without Unix perms.
fn make_executable(path: &Path) -> Result<()> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut perms = fs::metadata(path)
            .with_context(|| format!("stat {}", path.display()))?
            .permissions();
        perms.set_mode(perms.mode() | 0o755);
        fs::set_permissions(path, perms).with_context(|| format!("chmod +x {}", path.display()))?;
    }
    Ok(())
}

/// Create a fresh temp directory `<TMPDIR>/<prefix>.<nonce>` (the corpus
/// module's `mktemp -d` mirror; duplicated because that helper is private).
fn make_temp_dir(prefix: &str) -> Result<PathBuf> {
    let base = env::temp_dir();
    for _ in 0..16 {
        let nonce = format!(
            "{:x}-{:x}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0)
        );
        let dir = base.join(format!("{prefix}.{nonce}"));
        match fs::create_dir(&dir) {
            Ok(()) => return Ok(dir),
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(e) => {
                return Err(e).with_context(|| format!("mkdir {}", dir.display()));
            }
        }
    }
    bail!(
        "could not create a unique temp dir under {}",
        base.display()
    )
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    fn load_inline(body: &str) -> Result<Registry> {
        let dir = TempDir::new().unwrap();
        let path = dir.path().join("tools.toml");
        fs::write(&path, body).unwrap();
        Registry::load(&path)
    }

    fn git_entry(name: &str) -> String {
        format!(
            r#"
[[tool]]
name = "{name}"
kind = "checker"
source = "git"
url = "https://example.com/{name}"
recipe = "cc-single-file"
recipe_args = ["{name}.c"]
bin = "{name}"
install_to = "/opt/{name}/{name}"
verify = ["{{bin}}"]
"#
        )
    }

    // ---------- parsing ----------

    #[test]
    fn registry_parses_all_source_kinds() {
        let body = r#"
schema_version = 1

[[tool]]
name = "g"
kind = "checker"
groups = ["audit"]
source = "git"
url = "https://example.com/g"
commit = ""
recipe = "configure-make"
in_place = true
bin = "build/g"
install_to = "reference/g"
verify = ["{bin}", "--version"]
requires = ["git", "make"]

[[tool]]
name = "h"
kind = "utility"
source = "http-archive"
url = "https://example.com/h.tar.gz"
sha256 = "00"
recipe = "make"
bin = "h"
install_to = "reference/h"
verify = ["{bin}", "--version"]

[[tool]]
name = "p"
kind = "checker"
source = "pip"
spec = "p==1.2.3"
verify = ["p", "--help"]

[[tool]]
name = "c"
kind = "checker"
source = "cargo"
url = "https://example.com/c"
commit = "deadbeef"
bin = "c"
verify = ["c", "--version"]
verify_expect = "deadbee"

[[tool]]
name = "s"
kind = "reference-solver"
tag = "v1"
source = "script"
script = "install-s"
verify = ["s", "--version"]
"#;
        let registry = load_inline(body).unwrap();
        assert_eq!(registry.tools.len(), 5);
        assert_eq!(
            registry.tools.iter().map(|t| t.source).collect::<Vec<_>>(),
            vec![
                SourceKind::Git,
                SourceKind::HttpArchive,
                SourceKind::Pip,
                SourceKind::Cargo,
                SourceKind::Script,
            ]
        );
        assert_eq!(registry.tools[0].recipe, Some(Recipe::ConfigureMake));
        assert!(registry.tools[0].in_place);
        assert_eq!(
            registry.find("p").unwrap().spec.as_deref(),
            Some("p==1.2.3")
        );
        assert!(registry.find("nope").is_err());
    }

    #[test]
    fn shipped_registry_parses_and_preserves_legacy_targets() {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../reference/tools.toml");
        let registry = Registry::load(&path).unwrap();
        let names: Vec<&str> = registry.tools.iter().map(|t| t.name.as_str()).collect();
        assert_eq!(names, vec!["drat-trim", "cadical", "veripb", "carcara"]);

        // drat-trim: legacy install target and probe transcribed verbatim.
        let drat = registry.find("drat-trim").unwrap();
        assert_eq!(drat.recipe, Some(Recipe::CcSingleFile));
        assert_eq!(drat.recipe_args, vec!["drat-trim.c"]);
        assert_eq!(drat.install_to.as_deref(), Some("~/.local/bin/drat-trim"));
        assert_eq!(drat.verify_expect.as_deref(), Some("usage"));

        // cadical: the in-place tree the SAT cross-validation tests resolve.
        let cadical = registry.find("cadical").unwrap();
        assert_eq!(cadical.kind, Kind::ReferenceSolver);
        assert!(cadical.in_place);
        assert_eq!(cadical.install_to.as_deref(), Some("reference/cadical"));
        assert_eq!(cadical.bin.as_deref(), Some("build/cadical"));
        assert_eq!(cadical.commit.as_deref(), Some("")); // pre-0.1.0: declared, unpinned

        // veripb + carcara: pinned cargo installs.
        assert!(registry.find("veripb").unwrap().pinned());
        assert!(registry.find("carcara").unwrap().pinned());

        // carcara is the SMT proof checker the z3-audit replays Alethe against,
        // so its probe must name the pinned revision — otherwise an older
        // ~/.cargo/bin/carcara reports `installed` and audits check against
        // different rules than the repo pins (measured: the pre-pin 1.1.0
        // a963237 build knows no `arrays_*` rule at all).
        let carcara = registry.find("carcara").unwrap();
        let commit = carcara.commit.as_deref().unwrap();
        let expect = carcara.verify_expect.as_deref().unwrap();
        assert!(!expect.is_empty());
        assert!(
            commit.starts_with(expect),
            "carcara verify_expect ({expect}) must be a prefix of commit ({commit})"
        );
    }

    /// A commit-pinned `cargo install` leaves no revision record on disk, so a
    /// registry entry without a pin-naming probe is silently drift-blind.
    #[test]
    fn load_rejects_commit_pinned_cargo_tool_without_pin_naming_probe() {
        let body = r#"
schema_version = 1

[[tool]]
name = "c"
kind = "checker"
source = "cargo"
url = "https://example.com/c"
commit = "9a352eea6c935ad35cb8ec22e521a7620ec5d474"
bin = "c"
verify = ["c", "--version"]
"#;
        let msg = format!("{:#}", load_inline(body).unwrap_err());
        assert!(msg.contains("verify_expect"), "{msg}");
    }

    #[test]
    fn load_rejects_cargo_probe_that_does_not_name_the_pinned_commit() {
        let body = r#"
schema_version = 1

[[tool]]
name = "c"
kind = "checker"
source = "cargo"
url = "https://example.com/c"
commit = "9a352eea6c935ad35cb8ec22e521a7620ec5d474"
bin = "c"
verify = ["c", "--version"]
verify_expect = "usage"
"#;
        let msg = format!("{:#}", load_inline(body).unwrap_err());
        assert!(msg.contains("prefix of `commit`"), "{msg}");
    }

    /// The probe must be satisfied by the pinned revision's own banner and
    /// rejected by any other build — this is the whole drift signal.
    #[test]
    fn cargo_pin_probe_accepts_only_the_pinned_revision_banner() {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../reference/tools.toml");
        let registry = Registry::load(&path).unwrap();
        let carcara = registry.find("carcara").unwrap();
        let expect = carcara.verify_expect.as_deref().unwrap();
        // The banner the pinned build prints, and the one the stale build printed.
        assert!(format!("carcara 1.1.0 [git master {expect}]").contains(expect));
        assert!(!"carcara 1.1.0 [git master a963237]".contains(expect));
    }

    // ---------- validation ----------

    #[test]
    fn load_rejects_unknown_recipe_kind() {
        let body = git_entry("t").replace("cc-single-file", "curl-pipe-sh");
        let err = load_inline(&format!("schema_version = 1\n{body}")).unwrap_err();
        let msg = format!("{err:#}");
        assert!(msg.contains("curl-pipe-sh"), "{msg}");
    }

    #[test]
    fn load_rejects_shell_string_where_argv_array_belongs() {
        // verify as a shell string, not an argv array.
        let body = git_entry("t").replace(r#"verify = ["{bin}"]"#, r#"verify = "t --version""#);
        let err = load_inline(&format!("schema_version = 1\n{body}")).unwrap_err();
        let msg = format!("{err:#}");
        assert!(msg.contains("verify"), "{msg}");

        // recipe_args as a shell string.
        let body = git_entry("t").replace(r#"recipe_args = ["t.c"]"#, r#"recipe_args = "t.c -O3""#);
        let err = load_inline(&format!("schema_version = 1\n{body}")).unwrap_err();
        let msg = format!("{err:#}");
        assert!(msg.contains("recipe_args"), "{msg}");
    }

    #[test]
    fn load_rejects_duplicate_names() {
        let body = format!(
            "schema_version = 1\n{}{}",
            git_entry("dup"),
            git_entry("dup")
        );
        let err = load_inline(&body).unwrap_err();
        assert!(format!("{err:#}").contains("duplicate"));
    }

    #[test]
    fn load_rejects_unsupported_schema_version() {
        let err = load_inline("schema_version = 99\n").unwrap_err();
        assert!(format!("{err:#}").contains("schema_version"));
    }

    #[test]
    fn validate_reference_solver_requires_pin_field() {
        // No tag/commit key at all: rejected.
        let body = format!(
            "schema_version = 1\n{}",
            git_entry("t").replace("kind = \"checker\"", "kind = \"reference-solver\"")
        );
        let err = load_inline(&body).unwrap_err();
        assert!(format!("{err:#}").contains("reference-solver"));

        // Declared-but-unpinned (`commit = ""`) loads: the sanctioned
        // pre-0.1.0 cadical state (warns at install time instead).
        let body = format!(
            "schema_version = 1\n{}",
            git_entry("t").replace(
                "kind = \"checker\"",
                "kind = \"reference-solver\"\ncommit = \"\""
            )
        );
        let registry = load_inline(&body).unwrap();
        assert!(!registry.find("t").unwrap().pinned());
    }

    #[test]
    fn validate_source_field_requirements() {
        let cases: &[(&str, &str)] = &[
            // pip without spec.
            (
                r#"
[[tool]]
name = "p"
kind = "checker"
source = "pip"
verify = ["p", "--help"]
"#,
                "spec",
            ),
            // cargo without bin.
            (
                r#"
[[tool]]
name = "c"
kind = "checker"
source = "cargo"
url = "https://example.com/c"
verify = ["c", "--version"]
"#,
                "bin",
            ),
            // git without recipe.
            (
                r#"
[[tool]]
name = "g"
kind = "checker"
source = "git"
url = "https://example.com/g"
bin = "g"
install_to = "/opt/g/g"
verify = ["g"]
"#,
                "recipe",
            ),
            // pip must not carry a recipe (data must not pick build steps
            // outside the closed source semantics).
            (
                r#"
[[tool]]
name = "p"
kind = "checker"
source = "pip"
spec = "p==1"
recipe = "make"
verify = ["p", "--help"]
"#,
                "recipe",
            ),
            // empty verify argv.
            (
                r#"
[[tool]]
name = "v"
kind = "checker"
source = "pip"
spec = "v==1"
verify = []
"#,
                "verify",
            ),
            // non-kebab name.
            (
                r#"
[[tool]]
name = "Bad_Name"
kind = "checker"
source = "pip"
spec = "b==1"
verify = ["b", "--help"]
"#,
                "kebab-case",
            ),
        ];
        for (entry, needle) in cases {
            let err = load_inline(&format!("schema_version = 1\n{entry}")).unwrap_err();
            let msg = format!("{err:#}");
            assert!(msg.contains(needle), "expected {needle:?} in: {msg}");
        }
    }

    // ---------- resolution ----------

    #[test]
    fn env_override_name_uppercases_and_underscores() {
        assert_eq!(env_override_name("drat-trim"), "AY_TOOL_DRAT_TRIM");
        assert_eq!(env_override_name("veripb"), "AY_TOOL_VERIPB");
        assert_eq!(env_override_name("kissat-sc2025"), "AY_TOOL_KISSAT_SC2025");
    }

    fn sample_tool() -> Tool {
        let registry = load_inline(&format!("schema_version = 1\n{}", git_entry("t"))).unwrap();
        registry.tools[0].clone()
    }

    #[test]
    fn pin_labels() {
        let mut t = sample_tool();
        assert_eq!(t.pin_label(), "tip");
        assert!(!t.pinned());
        t.commit = Some("81f0df827297245f1370353924784325d8adab51".into());
        assert_eq!(t.pin_label(), "81f0df827297");
        assert!(t.pinned());
        t.tag = Some("sc2025".into());
        assert_eq!(t.pin_label(), "sc2025");

        let mut p = sample_tool();
        p.source = SourceKind::Pip;
        p.spec = Some("veripb==3.0.2".into());
        assert_eq!(p.pin_label(), "3.0.2");
        p.spec = Some("git+https://example.com/x.git@v9".into());
        assert_eq!(p.pin_label(), "v9");
    }

    #[test]
    fn install_target_file_vs_tree_shapes() {
        let root = Path::new("/repo");
        // install_to names the final binary (drat-trim shape).
        let mut t = sample_tool();
        t.bin = Some("drat-trim".into());
        t.install_to = Some("/home/u/.local/bin/drat-trim".into());
        assert_eq!(
            install_target(&t, root).unwrap(),
            PathBuf::from("/home/u/.local/bin/drat-trim")
        );
        // install_to is the build tree (cadical shape); repo-root-relative.
        t.bin = Some("build/cadical".into());
        t.install_to = Some("reference/cadical".into());
        assert_eq!(
            install_target(&t, root).unwrap(),
            PathBuf::from("/repo/reference/cadical/build/cadical")
        );
    }

    #[test]
    fn probe_argv_substitutes_bin() {
        let mut t = sample_tool();
        t.verify = vec!["{bin}".into(), "--version".into()];
        assert_eq!(
            probe_argv(&t, Path::new("/x/t")),
            vec!["/x/t".to_string(), "--version".to_string()]
        );
        // Plain PATH-name argv: the resolved binary is run instead.
        t.verify = vec!["t".into(), "--help".into()];
        assert_eq!(
            probe_argv(&t, Path::new("/x/t")),
            vec!["/x/t".to_string(), "--help".to_string()]
        );
    }

    #[test]
    fn candidates_order_and_directory_extra_path() {
        let dir = TempDir::new().unwrap();
        let fallback_dir = dir.path().join("fallback");
        fs::create_dir(&fallback_dir).unwrap();
        let hit = fallback_dir.join("t");
        fs::write(&hit, b"#!/bin/sh\n").unwrap();
        make_executable(&hit).unwrap();

        let mut t = sample_tool();
        t.install_to = Some(dir.path().join("missing/t").to_string_lossy().into_owned());
        // A directory extra_path probes <dir>/<bin> (the /tmp/drat-trim shape).
        t.extra_paths = vec![fallback_dir.to_string_lossy().into_owned()];

        let root = dir.path();
        let cands = candidates(&t, root);
        // env override, install target, extra path, $PATH — in that order.
        assert_eq!(cands.len(), 4);
        assert!(cands[0].label.starts_with("$AY_TOOL_"));
        assert_eq!(cands[1].label, "install target");
        assert_eq!(cands[2].label, "extra path");
        assert!(cands[3].label.starts_with("$PATH"));
        assert_eq!(cands[2].path.as_deref(), Some(hit.as_path()));

        assert_eq!(resolve(&t, root), Some(hit));
    }

    #[test]
    fn select_tools_group_xor_names() {
        let registry = load_inline(&format!(
            "schema_version = 1\n{}{}",
            git_entry("a").replace("[[tool]]", "[[tool]]\ngroups = [\"audit\"]"),
            git_entry("b")
        ))
        .unwrap();
        assert_eq!(
            select_tools(&registry, &[], Some("audit")).unwrap().len(),
            1
        );
        assert_eq!(
            select_tools(&registry, &["b".into()], None).unwrap()[0].name,
            "b"
        );
        assert!(select_tools(&registry, &["a".into()], Some("audit")).is_err());
        assert!(select_tools(&registry, &[], None).is_err());
        assert!(select_tools(&registry, &[], Some("nope")).is_err());
        assert!(select_tools(&registry, &["missing".into()], None).is_err());
    }
}
