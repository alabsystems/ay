// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use anyhow::{Context, Result};
use clap::{Args, Subcommand};
use serde_json::{json, Map, Value};
use sha2::{Digest, Sha256};

const PUBLIC_AY_URL: &str = "https://github.com/alabsystems/ay.git";
const PUBLIC_AY_REF: &str = "refs/heads/main";
const PUBLIC_COMMIT_SCHEMA: &str = "ay-public-commit-evidence/v1";
const RELEASE_PINS_SCHEMA: &str = "ay-public-release-pins/v1";
const RELEASE_MANIFEST_SCHEMA: &str = "ay-release-manifest/v1";
const RELEASE_MANIFEST_VERIFICATION_SCHEMA: &str = "ay-release-manifest-verification/v1";
const RELEASE_GATE_SUMMARY_SCHEMA: &str = "ay-release-gate-summary/v1";
const DEFAULT_VERSION_COMMIT_PREFIX_LEN: usize = 12;

// Expected release-pin repository URLs are deployment configuration: override
// them with AY_RELEASE_EXTERNAL_CODEGEN_URL / AY_RELEASE_EXTERNAL_CODEGEN_IR_URL to match the
// hosting setup being verified. The defaults are neutral placeholders.
const DEFAULT_EXTERNAL_CODEGEN_URL: &str = "ssh://git@github.com/example/EXTERNAL_CODEGEN.git";
// The canonical repo slug is `external-codegen-ir`; the legacy `external_codegen_ir` slug is still
// accepted via canonical_url() normalization for back-compat with existing
// lockfiles and release evidence.
const DEFAULT_EXTERNAL_CODEGEN_IR_URL: &str =
    "ssh://git@github.com/example/external-codegen-ir.git";

pub(crate) fn external_codegen_url() -> String {
    url_env_or_default(
        "AY_RELEASE_EXTERNAL_CODEGEN_URL",
        DEFAULT_EXTERNAL_CODEGEN_URL,
    )
}

pub(crate) fn external_codegen_ir_url() -> String {
    url_env_or_default(
        "AY_RELEASE_EXTERNAL_CODEGEN_IR_URL",
        DEFAULT_EXTERNAL_CODEGEN_IR_URL,
    )
}

fn url_env_or_default(name: &str, default: &str) -> String {
    env::var(name)
        .ok()
        .filter(|value| !value.trim().is_empty())
        .unwrap_or_else(|| default.to_owned())
}

fn expected_repos() -> [(&'static str, String); 2] {
    [
        ("EXTERNAL_CODEGEN", external_codegen_url()),
        ("ExternalCodegenIr", external_codegen_ir_url()),
    ]
}
const DEPENDENCY_TABLES: &[&str] = &["build-dependencies", "dependencies", "dev-dependencies"];
const GIT_DEP_ROOT_TABLES: &[&str] = &["patch", "replace"];

// clap subcommand enum: constructed once at CLI parse; boxing arg fields would
// break the derive and buys nothing at this scale.
#[allow(clippy::large_enum_variant)]
#[derive(Subcommand)]
pub(crate) enum ReleaseCommand {
    /// Verify the cited private ay commit is fetchable from the public mirror.
    #[command(name = "verify-public-ay-commit")]
    VerifyPublicAYCommit(VerifyPublicAYCommitArgs),
    /// Verify external code generation release pins and Cargo auto-bump coverage.
    #[command(name = "verify-public-pins")]
    VerifyPublicPins(VerifyPublicPinsArgs),
    /// Generate ay-release-manifest/v1 JSON from local evidence.
    #[command(name = "generate-manifest")]
    GenerateManifest(GenerateManifestArgs),
    /// Verify a generated public ay-release-manifest/v1 JSON.
    #[command(name = "verify-manifest")]
    VerifyManifest(VerifyManifestArgs),
}

#[derive(Args)]
pub(crate) struct VerifyPublicAYCommitArgs {
    /// Full 40-hex AY commit to verify.
    commit: String,
    /// Public AY URL to fetch from.
    #[arg(long, default_value = PUBLIC_AY_URL)]
    url: String,
    /// Public branch/tag ref that must resolve to the commit.
    #[arg(long = "ref", default_value = PUBLIC_AY_REF)]
    public_ref: String,
    /// Attempt git push <commit>:<ref>, then run sanitized public verification.
    #[arg(long)]
    publish: bool,
}

#[derive(Args)]
pub(crate) struct VerifyPublicPinsArgs {
    /// Repository root for default Cargo.toml/cargo_wrapper.toml/Cargo.lock.
    #[arg(long, default_value = ".")]
    repo_root: PathBuf,
    /// Cargo.lock path to inspect.
    #[arg(long, default_value = "Cargo.lock")]
    lockfile: PathBuf,
    /// cargo_wrapper.toml path to inspect.
    #[arg(long = "cargo-wrapper", default_value = "cargo_wrapper.toml")]
    cargo_wrapper: PathBuf,
    /// Cargo.toml manifest to inspect; may be passed multiple times.
    #[arg(long = "manifest")]
    manifests: Vec<PathBuf>,
    /// Only parse/report Cargo.lock pins; do not fetch release commits.
    #[arg(long)]
    no_fetch: bool,
    /// Emit the resolved pins as JSON after validation.
    #[arg(long)]
    json: bool,
}

#[derive(Args)]
pub(crate) struct GenerateManifestArgs {
    /// Repository root used when --private-commit is omitted.
    #[arg(long, default_value = ".")]
    repo_root: PathBuf,
    /// Release channel described by this manifest.
    #[arg(long, default_value = "public", value_parser = ["private", "public-candidate", "public"])]
    channel: String,
    /// Full 40-hex private ay commit; defaults to git rev-parse HEAD.
    #[arg(long)]
    private_commit: Option<String>,
    /// JSON from `ay release verify-public-ay-commit`.
    #[arg(long)]
    public_evidence: PathBuf,
    /// JSON from `ay release verify-public-pins --json`.
    #[arg(long)]
    dependency_pins: PathBuf,
    /// Exact build command used for the release artifact.
    #[arg(long)]
    build_command: String,
    /// Optional release binary or archive path.
    #[arg(long)]
    artifact_path: Option<PathBuf>,
    /// Literal ay --version output.
    #[arg(
        long,
        conflicts_with = "binary_version_file",
        required_unless_present = "binary_version_file"
    )]
    binary_version: Option<String>,
    /// File containing ay --version output.
    #[arg(
        long,
        conflicts_with = "binary_version",
        required_unless_present = "binary_version"
    )]
    binary_version_file: Option<PathBuf>,
    /// Launch gate status/log path to record; repeatable NAME=PATH.
    #[arg(long = "launch-gate-status")]
    launch_gate_status: Vec<String>,
    /// Launch gate summary JSON path to validate and record; repeatable NAME=PATH.
    #[arg(long = "launch-gate-summary")]
    launch_gate_summary: Vec<String>,
    /// Commit prefix length required in ay --version output.
    #[arg(long, default_value_t = DEFAULT_VERSION_COMMIT_PREFIX_LEN)]
    version_commit_prefix_len: usize,
    /// Override generated_at_utc for deterministic tests.
    #[arg(long)]
    generated_at: Option<String>,
    /// Write manifest JSON to this path instead of stdout.
    #[arg(long)]
    output: Option<PathBuf>,
}

#[derive(Args)]
pub(crate) struct VerifyManifestArgs {
    /// Path to ay-release-manifest.json.
    #[arg(long)]
    manifest: PathBuf,
    /// Path to the published artifact.
    #[arg(long)]
    artifact: Option<PathBuf>,
    /// Run ARTIFACT --version and compare it with the manifest output.
    #[arg(long)]
    run_version: bool,
}

pub(crate) fn run(cmd: ReleaseCommand) -> Result<i32> {
    match cmd {
        ReleaseCommand::VerifyPublicAYCommit(args) => verify_public_ay_commit(args),
        ReleaseCommand::VerifyPublicPins(args) => verify_public_pins(args),
        ReleaseCommand::GenerateManifest(args) => generate_manifest(args),
        ReleaseCommand::VerifyManifest(args) => verify_manifest_command(args),
    }
}

fn verify_public_ay_commit(args: VerifyPublicAYCommitArgs) -> Result<i32> {
    let (code, evidence) = if args.publish {
        publish_then_verify_commit(&args.url, &args.commit, &args.public_ref)?
    } else {
        verify_commit(&args.url, &args.commit, &args.public_ref)?
    };
    println!("{}", serde_json::to_string_pretty(&evidence)?);
    Ok(code)
}

fn verify_public_pins(args: VerifyPublicPinsArgs) -> Result<i32> {
    let repo_root = args.repo_root.canonicalize().unwrap_or(args.repo_root);
    let lockfile = resolve_repo_path(&repo_root, &args.lockfile);
    let config_path = resolve_repo_path(&repo_root, &args.cargo_wrapper);
    let manifest_paths = if args.manifests.is_empty() {
        discover_manifest_paths(&repo_root)
    } else {
        args.manifests
            .iter()
            .map(|path| resolve_repo_path(&repo_root, path))
            .collect()
    };

    let (pins, mut errors) = load_release_pins(&lockfile);
    let (auto_bump_coverage, auto_bump_errors) =
        verify_auto_bump_coverage(&repo_root, &manifest_paths, &config_path, &lockfile);
    errors.extend(auto_bump_errors);

    if !args.json {
        for pin in &pins {
            let packages = pin.packages.to_vec().join(",");
            let rev = pin.rev.as_deref().unwrap_or("lockfile-only");
            let component_version = pin.component_version.as_deref().unwrap_or("mixed");
            println!(
                "release-pin: {} url={} commit={} rev={} component_version={} packages={}",
                pin.name, pin.url, pin.commit, rev, component_version, packages
            );
        }
        for coverage in &auto_bump_coverage {
            let rev = coverage.rev.as_deref().unwrap_or("lockfile-only");
            let kind = coverage
                .kind
                .as_deref()
                .map(|kind| format!(" kind={kind}"))
                .unwrap_or_default();
            println!(
                "auto-bump: {} {}:{} url={} rev={}{}",
                coverage.status, coverage.manifest, coverage.dependency, coverage.url, rev, kind
            );
        }
    }

    let mut public_fetch_checked = false;
    if errors.is_empty() && !args.no_fetch {
        public_fetch_checked = true;
        errors.extend(verify_release_fetch(&pins, args.json)?);
    }

    if !errors.is_empty() {
        for error in &errors {
            eprintln!("release-pin: FAIL {error}");
        }
        if args.json {
            println!(
                "{}",
                serde_json::to_string_pretty(&release_pins_json_evidence(
                    &repo_root,
                    &lockfile,
                    &config_path,
                    &manifest_paths,
                    &pins,
                    &auto_bump_coverage,
                    &errors,
                    public_fetch_checked,
                ))?
            );
        }
        return Ok(1);
    }

    if args.json {
        println!(
            "{}",
            serde_json::to_string_pretty(&release_pins_json_evidence(
                &repo_root,
                &lockfile,
                &config_path,
                &manifest_paths,
                &pins,
                &auto_bump_coverage,
                &[],
                public_fetch_checked,
            ))?
        );
    }
    Ok(0)
}

fn generate_manifest(args: GenerateManifestArgs) -> Result<i32> {
    let (code, manifest) = build_manifest(&args)?;
    let text = serde_json::to_string_pretty(&manifest)? + "\n";
    if let Some(output) = args.output {
        fs::write(output, text)?;
    } else {
        print!("{text}");
    }
    Ok(code)
}

fn verify_manifest_command(args: VerifyManifestArgs) -> Result<i32> {
    let (code, payload) =
        verify_manifest(&args.manifest, args.artifact.as_deref(), args.run_version)?;
    println!("{}", serde_json::to_string_pretty(&payload)?);
    Ok(code)
}

fn full_sha(value: &str) -> bool {
    value.len() == 40 && value.bytes().all(|b| b.is_ascii_hexdigit())
}

fn sha256_hex(path: &Path) -> Result<String> {
    let mut file = fs::File::open(path)?;
    let mut digest = Sha256::new();
    let mut buf = vec![0_u8; 1024 * 1024];
    loop {
        let n = file.read(&mut buf)?;
        if n == 0 {
            break;
        }
        digest.update(&buf[..n]);
    }
    Ok(format!("{:x}", digest.finalize()))
}

fn git_head(repo_root: &Path) -> Result<String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(repo_root)
        .arg("rev-parse")
        .arg("HEAD")
        .output()
        .context("run git rev-parse HEAD")?;
    if !output.status.success() {
        anyhow::bail!("{}", command_detail(&output));
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

fn current_git_head(repo_root: &Path) -> (Option<String>, Option<String>) {
    match git_head(repo_root) {
        Ok(commit) if full_sha(&commit) => (Some(commit), None),
        Ok(commit) => (
            None,
            Some(format!(
                "git rev-parse HEAD returned non-commit value: {commit}"
            )),
        ),
        Err(err) => (None, Some(err.to_string())),
    }
}

fn command_detail(output: &std::process::Output) -> String {
    let stderr = String::from_utf8_lossy(&output.stderr).trim().to_owned();
    if !stderr.is_empty() {
        return stderr;
    }
    let stdout = String::from_utf8_lossy(&output.stdout).trim().to_owned();
    if !stdout.is_empty() {
        return stdout;
    }
    format!("process exited {}", output.status)
}

fn resolve_repo_path(repo_root: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        repo_root.join(path)
    }
}

fn repo_relative_path(repo_root: &Path, path: &Path) -> String {
    let root = repo_root
        .canonicalize()
        .unwrap_or_else(|_| repo_root.to_path_buf());
    let absolute = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    absolute
        .strip_prefix(&root)
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/")
}

fn public_git_env() -> [(&'static str, &'static str); 3] {
    [
        ("GIT_CONFIG_GLOBAL", "/dev/null"),
        ("GIT_CONFIG_NOSYSTEM", "1"),
        ("GIT_TERMINAL_PROMPT", "0"),
    ]
}

fn public_git_env_json() -> Value {
    json!({
        "GIT_CONFIG_GLOBAL": "/dev/null",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_TERMINAL_PROMPT": "0",
    })
}

fn run_git(args: &[&str], cwd: &Path, envs: &[(&str, &str)]) -> io::Result<std::process::Output> {
    let mut command = Command::new("git");
    command.args(args).current_dir(cwd);
    for (key, value) in envs {
        command.env(key, value);
    }
    command.output()
}

struct TempWorkDir {
    path: PathBuf,
}

impl TempWorkDir {
    fn new(prefix: &str) -> Result<Self> {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos();
        let path = env::temp_dir().join(format!("{prefix}.{}.{}", std::process::id(), nanos));
        fs::create_dir_all(&path)?;
        Ok(Self { path })
    }
}

impl Drop for TempWorkDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn publish_command(url: &str, commit: &str, public_ref: &str) -> Vec<String> {
    vec![
        "git".to_owned(),
        "push".to_owned(),
        url.to_owned(),
        format!("{commit}:{public_ref}"),
    ]
}

fn handoff_command(url: &str, commit: &str, public_ref: &str) -> Vec<String> {
    vec![
        "ay".to_owned(),
        "release".to_owned(),
        "verify-public-ay-commit".to_owned(),
        "--publish".to_owned(),
        "--url".to_owned(),
        url.to_owned(),
        "--ref".to_owned(),
        public_ref.to_owned(),
        commit.to_owned(),
    ]
}

fn verify_public_ay_command(url: &str, commit: &str, public_ref: &str) -> Vec<String> {
    vec![
        "ay".to_owned(),
        "release".to_owned(),
        "verify-public-ay-commit".to_owned(),
        "--url".to_owned(),
        url.to_owned(),
        "--ref".to_owned(),
        public_ref.to_owned(),
        commit.to_owned(),
    ]
}

fn shell_quote(value: &str) -> String {
    if !value.is_empty()
        && value.bytes().all(|b| {
            b.is_ascii_alphanumeric()
                || matches!(
                    b,
                    b'_' | b'@' | b'%' | b'+' | b'=' | b':' | b',' | b'.' | b'/' | b'-'
                )
        })
    {
        value.to_owned()
    } else {
        format!("'{}'", value.replace('\'', "'\\''"))
    }
}

fn shell_join(args: &[String]) -> String {
    args.iter()
        .map(|arg| shell_quote(arg))
        .collect::<Vec<_>>()
        .join(" ")
}

fn current_head_handoff_shell_command(url: &str, public_ref: &str) -> String {
    let mut command = handoff_command(url, "$AY_RELEASE_COMMIT", public_ref);
    let quoted = shell_join(&command).replace("'$AY_RELEASE_COMMIT'", "\"$AY_RELEASE_COMMIT\"");
    command.clear();
    [
        "git fetch origin main".to_owned(),
        "AY_RELEASE_COMMIT=\"$(git rev-parse origin/main)\"".to_owned(),
        format!("{quoted} > ay-public-commit-evidence.json"),
    ]
    .join("\n")
}

fn parse_ls_remote_commit(output: &str, public_ref: &str) -> Option<String> {
    let peeled_ref = format!("{public_ref}^{{}}");
    let mut direct_match = None;
    for line in output.lines() {
        let mut parts = line.split_whitespace();
        let Some(commit) = parts.next() else { continue };
        let Some(reference) = parts.next() else {
            continue;
        };
        if reference == peeled_ref {
            return Some(commit.to_owned());
        }
        if reference == public_ref {
            direct_match = Some(commit.to_owned());
        }
    }
    direct_match
}

fn record_public_ref_check(
    evidence: &mut Map<String, Value>,
    url: &str,
    commit: &str,
    public_ref: &str,
    workdir: &Path,
) -> io::Result<std::process::Output> {
    let mut refs = vec![public_ref.to_owned()];
    if public_ref.starts_with("refs/tags/") {
        refs.push(format!("{public_ref}^{{}}"));
    }
    let mut git_args = vec![
        "ls-remote".to_owned(),
        "--exit-code".to_owned(),
        url.to_owned(),
    ];
    git_args.extend(refs);
    let arg_refs = git_args.iter().map(String::as_str).collect::<Vec<_>>();
    let output = run_git(&arg_refs, workdir, &public_git_env())?;
    let mut command = vec!["git".to_owned()];
    command.extend(git_args);
    evidence.insert("ls_remote_command".to_owned(), json!(command));
    evidence.insert(
        "ls_remote_exit".to_owned(),
        json!(output.status.code().unwrap_or(-1)),
    );
    evidence.insert("ref_checked".to_owned(), json!(true));
    if output.status.success() {
        let stdout = String::from_utf8_lossy(&output.stdout);
        let ref_commit = parse_ls_remote_commit(&stdout, public_ref);
        evidence.insert("ref_commit".to_owned(), json!(ref_commit));
        evidence.insert(
            "ref_matches_commit".to_owned(),
            json!(ref_commit
                .as_deref()
                .is_some_and(|actual| actual.eq_ignore_ascii_case(commit))),
        );
    }
    Ok(output)
}

fn mirror_action(
    url: &str,
    commit: &str,
    public_ref: &str,
    failure_kind: &str,
    ref_commit: Option<&str>,
) -> Value {
    let required_actor = format!("maintainer with write access to {url}");
    let handoff = handoff_command(url, commit, public_ref);
    let mut action = Map::new();
    action.insert("failure_kind".to_owned(), json!(failure_kind));
    action.insert(
        "current_head_handoff_shell_command".to_owned(),
        json!(current_head_handoff_shell_command(url, public_ref)),
    );
    action.insert(
        "current_head_handoff_note".to_owned(),
        json!("Use current_head_handoff_shell_command when origin/main may have advanced since this evidence was generated; it fetches origin/main and publishes that exact commit."),
    );
    action.insert("handoff_command".to_owned(), json!(handoff));
    action.insert(
        "handoff_output".to_owned(),
        json!("ay-public-commit-evidence.json"),
    );
    action.insert(
        "handoff_shell_command".to_owned(),
        json!(format!(
            "{} > ay-public-commit-evidence.json",
            shell_join(&handoff_command(url, commit, public_ref))
        )),
    );
    action.insert("public_ref".to_owned(), json!(public_ref));
    action.insert(
        "publish_permission".to_owned(),
        json!({
            "checked": false,
            "reason": "ay release verify-public-ay-commit is read-only unless --publish is passed and read-only mode does not attempt git push; a public ay maintainer must run the handoff_shell_command to publish and re-verify.",
            "required": true,
            "required_access": "write",
            "required_actor": required_actor,
            "required_url": url,
            "status": "not-checked",
        }),
    );
    action.insert("required_actor".to_owned(), json!(required_actor));
    action.insert("required_commit".to_owned(), json!(commit));
    action.insert("required_ref".to_owned(), json!(public_ref));
    action.insert("required_url".to_owned(), json!(url));
    action.insert("stale_pass_evidence_allowed".to_owned(), json!(false));
    action.insert(
        "verify_command".to_owned(),
        json!(verify_public_ay_command(url, commit, public_ref)),
    );
    if let Some(ref_commit) = ref_commit {
        action.insert("current_ref_commit".to_owned(), json!(ref_commit));
    }
    let summary = match failure_kind {
        "public-object-not-fetchable" => "The requested commit is not fetchable from the unauthenticated public ay remote. Publish the exact private commit object and make the public launch ref resolve to it; stale public-source PASS evidence for another commit must not be counted.",
        "public-ref-mismatch" => "The commit object is public, but the public launch ref points at a different commit.",
        "public-ref-not-advertised" => "Create or advertise the public launch ref at the required commit.",
        _ => "Resolve the public mirror verification failure.",
    };
    action.insert("summary".to_owned(), json!(summary));
    action.insert(
        "example_publish_command".to_owned(),
        json!(publish_command(url, commit, public_ref)),
    );
    action.insert(
        "note".to_owned(),
        json!("Run the handoff shell command only from a checkout containing the required commit and only with public ay write access. If the branch update is not a fast-forward, reconcile private/public history instead of force-pushing release evidence."),
    );
    Value::Object(action)
}

fn stale_public_mirror_diagnostic(
    url: &str,
    commit: &str,
    public_ref: &str,
    ref_commit: Option<&str>,
    fetch_error: Option<&str>,
    reason: &str,
) -> Value {
    let mut diagnostic = Map::new();
    diagnostic.insert("kind".to_owned(), json!("stale-public-mirror"));
    diagnostic.insert("public_source_row_status".to_owned(), json!("fail"));
    diagnostic.insert("reason".to_owned(), json!(reason));
    diagnostic.insert("requested_commit".to_owned(), json!(commit));
    diagnostic.insert(
        "required_evidence".to_owned(),
        json!("fresh unauthenticated fetch/build evidence for the requested commit, not a PASS from the public mirror's stale head"),
    );
    diagnostic.insert("stale_pass_evidence_allowed".to_owned(), json!(false));
    diagnostic.insert("url".to_owned(), json!(url));
    diagnostic.insert("public_ref".to_owned(), json!(public_ref));
    if let Some(ref_commit) = ref_commit {
        diagnostic.insert("public_ref_commit".to_owned(), json!(ref_commit));
        diagnostic.insert(
            "public_ref_matches_requested".to_owned(),
            json!(ref_commit.eq_ignore_ascii_case(commit)),
        );
    }
    if let Some(fetch_error) = fetch_error {
        diagnostic.insert("fetch_error".to_owned(), json!(fetch_error));
    }
    Value::Object(diagnostic)
}

fn stale_public_mirror_error(
    commit: &str,
    public_ref: &str,
    ref_commit: Option<&str>,
    fetch_error: Option<&str>,
) -> String {
    let mut message = if let Some(ref_commit) =
        ref_commit.filter(|actual| !actual.eq_ignore_ascii_case(commit))
    {
        format!(
            "stale-public-mirror: requested commit {commit} is not the commit advertised by {public_ref} ({ref_commit}); stale PASS evidence for {ref_commit} must not be counted for {commit}"
        )
    } else {
        format!(
            "stale-public-mirror: requested commit {commit} is not fetchable from the public mirror; stale PASS evidence from any other public commit must not be counted"
        )
    };
    if let Some(fetch_error) = fetch_error {
        message.push_str("; fetch_error: ");
        message.push_str(fetch_error);
    }
    message
}

fn verify_commit(url: &str, commit: &str, public_ref: &str) -> Result<(i32, Value)> {
    let mut evidence = Map::new();
    evidence.insert("commit".to_owned(), json!(commit));
    evidence.insert("expected_commit".to_owned(), json!(commit));
    evidence.insert("fetchable".to_owned(), json!(false));
    evidence.insert("failure_kind".to_owned(), Value::Null);
    evidence.insert("git_env".to_owned(), public_git_env_json());
    evidence.insert("public_ref".to_owned(), json!(public_ref));
    evidence.insert("ref_checked".to_owned(), json!(false));
    evidence.insert("ref_matches_commit".to_owned(), json!(false));
    evidence.insert("schema".to_owned(), json!(PUBLIC_COMMIT_SCHEMA));
    evidence.insert("status".to_owned(), json!("fail"));
    evidence.insert("url".to_owned(), json!(url));

    if !full_sha(commit) {
        evidence.insert(
            "error".to_owned(),
            json!("commit must be a full 40-hex object id"),
        );
        evidence.insert("failure_kind".to_owned(), json!("invalid-commit"));
        return Ok((2, Value::Object(evidence)));
    }

    let temp = TempWorkDir::new("ay-public-commit")?;
    let init = run_git(&["init", "-q"], &temp.path, &public_git_env())?;
    if !init.status.success() {
        evidence.insert("error".to_owned(), json!(command_detail(&init)));
        evidence.insert("failure_kind".to_owned(), json!("git-init-failed"));
        return Ok((1, Value::Object(evidence)));
    }

    let fetch = run_git(
        &["fetch", "--depth", "1", url, commit],
        &temp.path,
        &public_git_env(),
    )?;
    evidence.insert(
        "fetch_command".to_owned(),
        json!(["git", "fetch", "--depth", "1", url, commit]),
    );
    evidence.insert(
        "fetch_exit".to_owned(),
        json!(fetch.status.code().unwrap_or(-1)),
    );
    if !fetch.status.success() {
        let ls_remote =
            record_public_ref_check(&mut evidence, url, commit, public_ref, &temp.path)?;
        let fetch_error = command_detail(&fetch);
        let ref_commit = evidence
            .get("ref_commit")
            .and_then(Value::as_str)
            .map(str::to_owned);
        evidence.insert(
            "failure_kind".to_owned(),
            json!("public-object-not-fetchable"),
        );
        evidence.insert(
            "error".to_owned(),
            json!(stale_public_mirror_error(
                commit,
                public_ref,
                ref_commit.as_deref(),
                Some(&fetch_error)
            )),
        );
        evidence.insert("stale_public_mirror".to_owned(), json!(true));
        evidence.insert(
            "stale_public_mirror_diagnostic".to_owned(),
            stale_public_mirror_diagnostic(
                url,
                commit,
                public_ref,
                ref_commit.as_deref(),
                Some(&fetch_error),
                "requested commit is not fetchable from public mirror",
            ),
        );
        evidence.insert(
            "mirror_action".to_owned(),
            mirror_action(
                url,
                commit,
                public_ref,
                "public-object-not-fetchable",
                ref_commit.as_deref(),
            ),
        );
        if !ls_remote.status.success() {
            evidence.insert("ref_error".to_owned(), json!(command_detail(&ls_remote)));
        }
        return Ok((1, Value::Object(evidence)));
    }

    let rev_parse = run_git(&["rev-parse", "FETCH_HEAD"], &temp.path, &public_git_env())?;
    evidence.insert(
        "rev_parse_exit".to_owned(),
        json!(rev_parse.status.code().unwrap_or(-1)),
    );
    if !rev_parse.status.success() {
        evidence.insert("error".to_owned(), json!(command_detail(&rev_parse)));
        evidence.insert("failure_kind".to_owned(), json!("fetch-head-unreadable"));
        return Ok((1, Value::Object(evidence)));
    }
    let fetched_commit = String::from_utf8_lossy(&rev_parse.stdout).trim().to_owned();
    evidence.insert("fetched_commit".to_owned(), json!(fetched_commit));
    if !fetched_commit.eq_ignore_ascii_case(commit) {
        evidence.insert(
            "error".to_owned(),
            json!(format!(
                "FETCH_HEAD resolved to {fetched_commit}, expected {commit}"
            )),
        );
        evidence.insert("failure_kind".to_owned(), json!("fetched-commit-mismatch"));
        return Ok((1, Value::Object(evidence)));
    }
    evidence.insert("fetchable".to_owned(), json!(true));

    let ls_remote = record_public_ref_check(&mut evidence, url, commit, public_ref, &temp.path)?;
    if !ls_remote.status.success() {
        evidence.insert("error".to_owned(), json!(command_detail(&ls_remote)));
        evidence.insert(
            "failure_kind".to_owned(),
            json!("public-ref-not-advertised"),
        );
        evidence.insert(
            "mirror_action".to_owned(),
            mirror_action(url, commit, public_ref, "public-ref-not-advertised", None),
        );
        return Ok((1, Value::Object(evidence)));
    }
    let ref_commit = evidence
        .get("ref_commit")
        .and_then(Value::as_str)
        .map(str::to_owned);
    let Some(ref_commit) = ref_commit else {
        evidence.insert(
            "error".to_owned(),
            json!(format!(
                "public ref {public_ref} not found in ls-remote output"
            )),
        );
        evidence.insert(
            "failure_kind".to_owned(),
            json!("public-ref-not-advertised"),
        );
        evidence.insert(
            "mirror_action".to_owned(),
            mirror_action(url, commit, public_ref, "public-ref-not-advertised", None),
        );
        return Ok((1, Value::Object(evidence)));
    };
    if !ref_commit.eq_ignore_ascii_case(commit) {
        evidence.insert(
            "error".to_owned(),
            json!(format!(
                "stale-public-mirror: public ref {public_ref} resolves to {ref_commit}, expected {commit}; stale PASS evidence for {ref_commit} must not be counted for {commit}"
            )),
        );
        evidence.insert("failure_kind".to_owned(), json!("public-ref-mismatch"));
        evidence.insert("stale_public_mirror".to_owned(), json!(true));
        evidence.insert(
            "stale_public_mirror_diagnostic".to_owned(),
            stale_public_mirror_diagnostic(
                url,
                commit,
                public_ref,
                Some(&ref_commit),
                None,
                "public launch ref does not point at requested commit",
            ),
        );
        evidence.insert(
            "mirror_action".to_owned(),
            mirror_action(
                url,
                commit,
                public_ref,
                "public-ref-mismatch",
                Some(&ref_commit),
            ),
        );
        return Ok((1, Value::Object(evidence)));
    }

    evidence.insert("fetchable".to_owned(), json!(true));
    evidence.insert("ref_matches_commit".to_owned(), json!(true));
    evidence.insert("status".to_owned(), json!("pass"));
    Ok((0, Value::Object(evidence)))
}

fn publish_attempt_evidence(
    url: &str,
    commit: &str,
    public_ref: &str,
    result: Option<&std::process::Output>,
    status: &str,
    reason: Option<&str>,
) -> Value {
    let mut evidence = Map::new();
    evidence.insert("checked".to_owned(), json!(result.is_some()));
    evidence.insert(
        "command".to_owned(),
        json!(publish_command(url, commit, public_ref)),
    );
    evidence.insert("required_access".to_owned(), json!("write"));
    evidence.insert(
        "required_actor".to_owned(),
        json!(format!("maintainer with write access to {url}")),
    );
    evidence.insert("status".to_owned(), json!(status));
    if let Some(reason) = reason {
        evidence.insert("reason".to_owned(), json!(reason));
    }
    if let Some(result) = result {
        evidence.insert(
            "exit_code".to_owned(),
            json!(result.status.code().unwrap_or(-1)),
        );
        if !result.status.success() {
            evidence.insert("error".to_owned(), json!(command_detail(result)));
        }
    }
    Value::Object(evidence)
}

fn publish_then_verify_commit(url: &str, commit: &str, public_ref: &str) -> Result<(i32, Value)> {
    if !full_sha(commit) {
        let (code, mut evidence) = verify_commit(url, commit, public_ref)?;
        if let Value::Object(ref mut map) = evidence {
            map.insert(
                "publish_attempt".to_owned(),
                publish_attempt_evidence(
                    url,
                    commit,
                    public_ref,
                    None,
                    "skipped",
                    Some("commit must be a full 40-hex object id"),
                ),
            );
        }
        return Ok((code, evidence));
    }
    let publish = Command::new("git")
        .args(["push", url, &format!("{commit}:{public_ref}")])
        .env("GIT_TERMINAL_PROMPT", "0")
        .output()
        .context("run git push for public release handoff")?;
    let (code, mut evidence) = verify_commit(url, commit, public_ref)?;
    if let Value::Object(ref mut map) = evidence {
        let status = if publish.status.success() {
            "pass"
        } else {
            "fail"
        };
        map.insert(
            "publish_attempt".to_owned(),
            publish_attempt_evidence(url, commit, public_ref, Some(&publish), status, None),
        );
        if !publish.status.success() && code != 0 {
            map.insert("publish_error".to_owned(), json!(command_detail(&publish)));
        }
    }
    Ok((code, evidence))
}

#[derive(Clone, Debug)]
struct GitSource {
    url: String,
    commit: String,
    rev: Option<String>,
}

#[derive(Clone, Debug)]
struct LockEntry {
    package_name: String,
    package_version: String,
    source: GitSource,
}

#[derive(Clone, Debug)]
struct ReleasePin {
    name: String,
    url: String,
    commit: String,
    rev: Option<String>,
    packages: Vec<String>,
    component_version: Option<String>,
    package_versions: BTreeMap<String, String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct ManifestGitDependency {
    manifest: String,
    table: String,
    dependency: String,
    url: String,
    rev: Option<String>,
}

#[derive(Clone, Debug)]
struct AutoBumpExemption {
    repo: String,
    dependency: String,
    manifest: String,
    kind: String,
    lockfile_package: String,
    requires_revless_manifest: bool,
    bump_command: String,
    reason: String,
    review_check: String,
}

#[derive(Clone, Debug)]
struct AutoBumpCoverage {
    manifest: String,
    dependency: String,
    url: String,
    rev: Option<String>,
    status: String,
    bump_method: Option<String>,
    bump_command: Option<String>,
    check_command: Option<String>,
    kind: Option<String>,
    reason: Option<String>,
    review_check: Option<String>,
    updates: Vec<String>,
}

impl ReleasePin {
    fn to_json(&self) -> Value {
        json!({
            "name": self.name,
            "url": self.url,
            "commit": self.commit,
            "rev": self.rev,
            "packages": self.packages,
            "component_version": self.component_version,
            "package_versions": self.package_versions,
        })
    }
}

impl AutoBumpCoverage {
    fn to_json(&self) -> Value {
        json!({
            "manifest": self.manifest,
            "dependency": self.dependency,
            "url": self.url,
            "rev": self.rev,
            "status": self.status,
            "bump_method": self.bump_method,
            "bump_command": self.bump_command,
            "check_command": self.check_command,
            "kind": self.kind,
            "reason": self.reason,
            "review_check": self.review_check,
            "updates": self.updates,
        })
    }
}

fn canonical_url(url: &str) -> String {
    let mut url = url.trim_end_matches('/').to_owned();
    if let Some(stripped) = url.strip_suffix(".git") {
        url = stripped.to_owned();
    }
    if let Some(rest) = url.strip_prefix("ssh://git@github.com:22/") {
        url = format!("ssh://git@github.com/{rest}");
    }
    // The external-codegen-ir repo was historically referenced by the underscore slug
    // `external_codegen_ir`; treat the legacy and canonical slugs as the same key so old
    // lockfiles/release evidence still match the canonical pin URL.
    if let Some(prefix) = url.strip_suffix("/external_codegen_ir") {
        url = format!("{prefix}/external-codegen-ir");
    }
    url
}

fn parse_git_source(source: &str) -> Result<Option<GitSource>, String> {
    let Some(raw) = source.strip_prefix("git+") else {
        return Ok(None);
    };
    let Some((url_with_query, commit)) = raw.rsplit_once('#') else {
        return Err(format!("git source is missing commit fragment: {source}"));
    };
    let (url, query) = url_with_query
        .split_once('?')
        .map_or((url_with_query, ""), |(url, query)| (url, query));
    let rev = query
        .split('&')
        .filter_map(|part| part.split_once('='))
        .find_map(|(key, value)| (key == "rev").then(|| value.to_owned()));
    Ok(Some(GitSource {
        url: url.to_owned(),
        commit: commit.to_owned(),
        rev,
    }))
}

fn parse_string_assignment(line: &str, key: &str) -> Option<String> {
    let trimmed = strip_comment(line).trim();
    let rest = trimmed.strip_prefix(key)?.trim_start();
    let rest = rest.strip_prefix('=')?.trim_start();
    parse_quoted_string(rest)
}

fn parse_bool_assignment(line: &str, key: &str) -> Option<bool> {
    let trimmed = strip_comment(line).trim();
    let rest = trimmed.strip_prefix(key)?.trim_start();
    let rest = rest.strip_prefix('=')?.trim();
    match rest {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

fn parse_quoted_string(value: &str) -> Option<String> {
    let start = value.find('"')?;
    let mut escaped = false;
    let mut result = String::new();
    for ch in value[start + 1..].chars() {
        if escaped {
            let decoded = match ch {
                'n' => '\n',
                'r' => '\r',
                't' => '\t',
                '"' => '"',
                '\\' => '\\',
                other => other,
            };
            result.push(decoded);
            escaped = false;
        } else if ch == '\\' {
            escaped = true;
        } else if ch == '"' {
            return Some(result);
        } else {
            result.push(ch);
        }
    }
    None
}

fn quoted_strings(value: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut chars = value.char_indices().peekable();
    while let Some((index, ch)) = chars.next() {
        if ch != '"' {
            continue;
        }
        if let Some(parsed) = parse_quoted_string(&value[index..]) {
            let skip_to = index + parsed.len() + 2;
            out.push(parsed);
            while chars
                .peek()
                .is_some_and(|(next_index, _)| *next_index < skip_to)
            {
                chars.next();
            }
        }
    }
    out
}

fn strip_comment(line: &str) -> &str {
    let mut in_string = false;
    let mut escaped = false;
    for (index, ch) in line.char_indices() {
        if escaped {
            escaped = false;
            continue;
        }
        match ch {
            '\\' if in_string => escaped = true,
            '"' => in_string = !in_string,
            '#' if !in_string => return &line[..index],
            _ => {}
        }
    }
    line
}

fn load_git_lock_sources(lockfile: &Path) -> (BTreeMap<String, Vec<LockEntry>>, Vec<String>) {
    let text = match fs::read_to_string(lockfile) {
        Ok(text) => text,
        Err(err) => {
            return (
                BTreeMap::new(),
                vec![format!("{}: {err}", lockfile.display())],
            )
        }
    };
    let mut entries = Vec::<BTreeMap<String, String>>::new();
    let mut current = BTreeMap::<String, String>::new();
    for line in text.lines() {
        let trimmed = strip_comment(line).trim();
        if trimmed == "[[package]]" {
            if !current.is_empty() {
                entries.push(std::mem::take(&mut current));
            }
            continue;
        }
        for key in ["name", "version", "source"] {
            if let Some(value) = parse_string_assignment(trimmed, key) {
                current.insert(key.to_owned(), value);
            }
        }
    }
    if !current.is_empty() {
        entries.push(current);
    }

    let mut by_repo: BTreeMap<String, Vec<LockEntry>> = BTreeMap::new();
    let mut errors = Vec::new();
    for package in entries {
        let Some(source) = package.get("source") else {
            continue;
        };
        let git_source = match parse_git_source(source) {
            Ok(Some(git_source)) => git_source,
            Ok(None) => continue,
            Err(err) => {
                errors.push(err);
                continue;
            }
        };
        let package_name = package
            .get("name")
            .cloned()
            .unwrap_or_else(|| "<unknown>".to_owned());
        let package_version = package.get("version").cloned().unwrap_or_default();
        by_repo
            .entry(canonical_url(&git_source.url))
            .or_default()
            .push(LockEntry {
                package_name,
                package_version,
                source: git_source,
            });
    }
    (by_repo, errors)
}

fn valid_package_version(version: &str) -> bool {
    let mut parts = version.splitn(3, '.');
    let Some(major) = parts.next() else {
        return false;
    };
    let Some(minor) = parts.next() else {
        return false;
    };
    let Some(patch_and_meta) = parts.next() else {
        return false;
    };
    if !major.bytes().all(|b| b.is_ascii_digit()) || !minor.bytes().all(|b| b.is_ascii_digit()) {
        return false;
    }
    let patch = patch_and_meta.split(['-', '+']).next().unwrap_or_default();
    !patch.is_empty() && patch.bytes().all(|b| b.is_ascii_digit())
}

fn load_release_pins(lockfile: &Path) -> (Vec<ReleasePin>, Vec<String>) {
    let (by_repo, mut errors) = load_git_lock_sources(lockfile);
    let mut pins = Vec::new();
    for (name, expected_url) in expected_repos() {
        let expected_key = canonical_url(&expected_url);
        let Some(entries) = by_repo.get(&expected_key) else {
            errors.push(format!("{name}: missing locked source for {expected_url}"));
            continue;
        };
        let urls = entries
            .iter()
            .map(|entry| entry.source.url.clone())
            .collect::<BTreeSet<_>>();
        let commits = entries
            .iter()
            .map(|entry| entry.source.commit.clone())
            .collect::<BTreeSet<_>>();
        let revs = entries
            .iter()
            .map(|entry| entry.source.rev.clone())
            .collect::<BTreeSet<_>>();
        if urls.len() != 1 {
            errors.push(format!(
                "{name}: multiple source URLs in Cargo.lock: {urls:?}"
            ));
            continue;
        }
        if commits.len() != 1 {
            errors.push(format!(
                "{name}: multiple locked commits in Cargo.lock: {commits:?}"
            ));
            continue;
        }
        let url = urls.into_iter().next().unwrap_or_default();
        let commit = commits.into_iter().next().unwrap_or_default();
        let rev = (revs.len() == 1)
            .then(|| revs.iter().next().cloned().flatten())
            .flatten();
        if revs.len() != 1 {
            let rev_list = revs
                .iter()
                .map(|rev| rev.clone().unwrap_or_else(|| "<none>".to_owned()))
                .collect::<Vec<_>>();
            errors.push(format!(
                "{name}: multiple rev queries in Cargo.lock: {rev_list:?}"
            ));
        } else if let Some(rev) = &rev {
            if !full_sha(rev) {
                errors.push(format!(
                    "{name}: Cargo.lock rev query is not a full 40-hex id: {rev}"
                ));
            } else if rev != &commit {
                errors.push(format!(
                    "{name}: Cargo.lock rev query {rev} must match locked commit {commit}"
                ));
            }
        }

        let mut package_versions = BTreeMap::new();
        let mut locked_versions = Vec::new();
        for entry in entries {
            if entry.package_version.is_empty() {
                errors.push(format!(
                    "{name}: {} is missing a Cargo.lock version",
                    entry.package_name
                ));
                continue;
            }
            if !valid_package_version(&entry.package_version) {
                errors.push(format!(
                    "{name}: {} has invalid package version {:?}",
                    entry.package_name, entry.package_version
                ));
            }
            if let Some(previous) = package_versions.get(&entry.package_name) {
                if previous != &entry.package_version {
                    errors.push(format!(
                        "{name}: {} has multiple locked versions: {previous}, {}",
                        entry.package_name, entry.package_version
                    ));
                }
            }
            package_versions.insert(entry.package_name.clone(), entry.package_version.clone());
            locked_versions.push((entry.package_name.clone(), entry.package_version.clone()));
        }
        let component_versions = locked_versions
            .iter()
            .map(|(_, version)| version.clone())
            .collect::<BTreeSet<_>>();
        let component_version = (component_versions.len() == 1)
            .then(|| component_versions.iter().next().cloned())
            .flatten();
        if component_versions.is_empty() {
            errors.push(format!(
                "{name}: package_versions must include at least one version"
            ));
        } else if component_version.is_none() {
            let detail = locked_versions
                .iter()
                .map(|(package, version)| format!("{package}={version}"))
                .collect::<Vec<_>>()
                .join(", ");
            errors.push(format!(
                "{name}: locked package versions must be consistent for one release component: {detail}"
            ));
        }
        let packages = entries
            .iter()
            .map(|entry| entry.package_name.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        pins.push(ReleasePin {
            name: (*name).to_owned(),
            url,
            commit,
            rev,
            packages,
            component_version,
            package_versions,
        });
    }
    (pins, errors)
}

fn discover_manifest_paths(repo_root: &Path) -> Vec<PathBuf> {
    let output = Command::new("git")
        .arg("-C")
        .arg(repo_root)
        .arg("ls-files")
        .arg("Cargo.toml")
        .arg("*/Cargo.toml")
        .output();
    if let Ok(output) = output {
        if output.status.success() && !output.stdout.is_empty() {
            let mut paths = String::from_utf8_lossy(&output.stdout)
                .lines()
                .filter(|line| !line.trim().is_empty())
                .map(|line| repo_root.join(line))
                .collect::<Vec<_>>();
            paths.sort();
            paths.dedup();
            return paths;
        }
    }
    let mut manifests = Vec::new();
    discover_manifest_paths_fallback(repo_root, repo_root, &mut manifests);
    manifests.sort();
    manifests
}

fn discover_manifest_paths_fallback(root: &Path, dir: &Path, manifests: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if path.is_dir() {
            if matches!(
                name.as_ref(),
                ".cargo"
                    | ".flags"
                    | ".git"
                    | ".venv"
                    | "build"
                    | "dist"
                    | "env"
                    | "metrics"
                    | "node_modules"
                    | "reports"
                    | "target"
                    | "venv"
                    | "vendor"
            ) || name.starts_with("target_")
            {
                continue;
            }
            discover_manifest_paths_fallback(root, &path, manifests);
        } else if name == "Cargo.toml" {
            manifests.push(
                path.strip_prefix(root)
                    .map_or(path.clone(), |rel| root.join(rel)),
            );
        }
    }
}

fn parse_table_header(line: &str) -> Option<Vec<String>> {
    let trimmed = strip_comment(line).trim();
    if !trimmed.starts_with('[') || !trimmed.ends_with(']') || trimmed.starts_with("[[") {
        return None;
    }
    let inner = &trimmed[1..trimmed.len() - 1];
    Some(split_toml_path(inner))
}

fn split_toml_path(path: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut part = String::new();
    let mut in_quote = false;
    let mut escaped = false;
    for ch in path.chars() {
        if escaped {
            part.push(ch);
            escaped = false;
            continue;
        }
        match ch {
            '\\' if in_quote => escaped = true,
            '"' => in_quote = !in_quote,
            '.' if !in_quote => {
                parts.push(part.trim().trim_matches('"').to_owned());
                part.clear();
            }
            _ => part.push(ch),
        }
    }
    if !part.is_empty() {
        parts.push(part.trim().trim_matches('"').to_owned());
    }
    parts
}

fn is_dependency_container(path: &[String]) -> bool {
    path.last()
        .is_some_and(|last| DEPENDENCY_TABLES.contains(&last.as_str()))
}

fn is_dependency_table(path: &[String]) -> bool {
    path.len() >= 2 && DEPENDENCY_TABLES.contains(&path[path.len() - 2].as_str())
}

fn is_patch_or_replace_container(path: &[String]) -> bool {
    path.len() >= 2 && GIT_DEP_ROOT_TABLES.contains(&path[0].as_str())
}

fn is_patch_or_replace_table(path: &[String]) -> bool {
    path.len() >= 3 && GIT_DEP_ROOT_TABLES.contains(&path[0].as_str())
}

fn table_name(path: &[String]) -> String {
    path.join(".")
}

fn parse_inline_git_dependency(line: &str) -> Option<(String, String, Option<String>)> {
    let trimmed = strip_comment(line).trim();
    let (name, rest) = trimmed.split_once('=')?;
    if !rest.contains('{') || !rest.contains("git") {
        return None;
    }
    let git = parse_field_string(rest, "git")?;
    let rev = parse_field_string(rest, "rev");
    Some((name.trim().to_owned(), git, rev))
}

fn parse_field_string(text: &str, field: &str) -> Option<String> {
    let bytes = text.as_bytes();
    let field_bytes = field.as_bytes();
    let mut i = 0;
    while i + field_bytes.len() <= bytes.len() {
        if &bytes[i..i + field_bytes.len()] == field_bytes {
            let before_ok =
                i == 0 || bytes[i - 1].is_ascii_whitespace() || matches!(bytes[i - 1], b'{' | b',');
            let mut j = i + field_bytes.len();
            while j < bytes.len() && bytes[j].is_ascii_whitespace() {
                j += 1;
            }
            if before_ok && j < bytes.len() && bytes[j] == b'=' {
                return parse_quoted_string(&text[j + 1..]);
            }
        }
        i += 1;
    }
    None
}

fn load_manifest_git_dependencies(
    manifest_paths: &[PathBuf],
    repo_root: &Path,
) -> (Vec<ManifestGitDependency>, Vec<String>) {
    let mut dependencies = BTreeSet::new();
    let mut errors = Vec::new();
    for manifest_path in manifest_paths {
        let manifest = repo_relative_path(repo_root, manifest_path);
        let text = match fs::read_to_string(manifest_path) {
            Ok(text) => text,
            Err(err) => {
                errors.push(format!("{manifest}: cannot parse manifest: {err}"));
                continue;
            }
        };
        let mut table = Vec::<String>::new();
        let mut pending_dep: Option<String> = None;
        let mut pending_git: Option<String> = None;
        let mut pending_rev: Option<String> = None;
        let flush_pending = |dependencies: &mut BTreeSet<ManifestGitDependency>,
                             manifest: &str,
                             table: &[String],
                             pending_dep: &mut Option<String>,
                             pending_git: &mut Option<String>,
                             pending_rev: &mut Option<String>| {
            if let (Some(dependency), Some(url)) = (pending_dep.take(), pending_git.take()) {
                let parent = if table.is_empty() {
                    String::new()
                } else {
                    table[..table.len().saturating_sub(1)].join(".")
                };
                dependencies.insert(ManifestGitDependency {
                    manifest: manifest.to_owned(),
                    table: parent,
                    dependency,
                    url,
                    rev: pending_rev.take(),
                });
            }
            *pending_rev = None;
        };

        for line in text.lines() {
            if let Some(next_table) = parse_table_header(line) {
                flush_pending(
                    &mut dependencies,
                    &manifest,
                    &table,
                    &mut pending_dep,
                    &mut pending_git,
                    &mut pending_rev,
                );
                table = next_table;
                if is_dependency_table(&table) || is_patch_or_replace_table(&table) {
                    pending_dep = table.last().cloned();
                }
                continue;
            }
            if is_dependency_container(&table) || is_patch_or_replace_container(&table) {
                if let Some((dependency, url, rev)) = parse_inline_git_dependency(line) {
                    dependencies.insert(ManifestGitDependency {
                        manifest: manifest.clone(),
                        table: table_name(&table),
                        dependency,
                        url,
                        rev,
                    });
                    continue;
                }
            }
            if pending_dep.is_some() {
                if let Some(git) = parse_string_assignment(line, "git") {
                    pending_git = Some(git);
                } else if let Some(rev) = parse_string_assignment(line, "rev") {
                    pending_rev = Some(rev);
                }
            }
        }
        flush_pending(
            &mut dependencies,
            &manifest,
            &table,
            &mut pending_dep,
            &mut pending_git,
            &mut pending_rev,
        );
    }
    (dependencies.into_iter().collect(), errors)
}

#[derive(Default)]
struct ExemptionBuilder {
    repo: Option<String>,
    dependency: Option<String>,
    manifest: Option<String>,
    kind: Option<String>,
    lockfile_package: Option<String>,
    requires_revless_manifest: Option<bool>,
    bump_command: Option<String>,
    reason: Option<String>,
    review_check: Option<String>,
}

fn load_auto_bump_config(
    config_path: &Path,
) -> (BTreeSet<String>, Vec<AutoBumpExemption>, Vec<String>) {
    if !config_path.exists() {
        return (BTreeSet::new(), Vec::new(), Vec::new());
    }
    let text = match fs::read_to_string(config_path) {
        Ok(text) => text,
        Err(err) => {
            return (
                BTreeSet::new(),
                Vec::new(),
                vec![format!("{}: {err}", config_path.display())],
            )
        }
    };
    let mut errors = Vec::new();
    let mut repos = BTreeSet::new();
    let mut exemptions = Vec::new();
    let mut section = String::new();
    let mut builder: Option<ExemptionBuilder> = None;
    let mut exemption_index = 0_usize;

    let finish_builder = |builder: Option<ExemptionBuilder>,
                          exemption_index: usize,
                          exemptions: &mut Vec<AutoBumpExemption>,
                          errors: &mut Vec<String>| {
        let Some(raw) = builder else { return };
        let prefix = format!(
            "{}: [[auto_bump.exemptions]] #{}",
            config_path.display(),
            exemption_index
        );
        fn require_field(
            value: Option<String>,
            key: &str,
            prefix: &str,
            errors: &mut Vec<String>,
        ) -> String {
            match value.filter(|value| !value.trim().is_empty()) {
                Some(value) => value.trim().to_owned(),
                None => {
                    errors.push(format!("{prefix} missing non-empty {key:?}"));
                    String::new()
                }
            }
        }
        let requires_revless_manifest = match raw.requires_revless_manifest {
            Some(value) => value,
            None => {
                errors.push(format!(
                    "{prefix} missing boolean 'requires_revless_manifest'"
                ));
                false
            }
        };
        exemptions.push(AutoBumpExemption {
            repo: require_field(raw.repo, "repo", &prefix, errors),
            dependency: require_field(raw.dependency, "dependency", &prefix, errors),
            manifest: require_field(raw.manifest, "manifest", &prefix, errors)
                .trim_start_matches("./")
                .to_owned(),
            kind: require_field(raw.kind, "kind", &prefix, errors),
            lockfile_package: require_field(
                raw.lockfile_package,
                "lockfile_package",
                &prefix,
                errors,
            ),
            requires_revless_manifest,
            bump_command: require_field(raw.bump_command, "bump_command", &prefix, errors),
            reason: require_field(raw.reason, "reason", &prefix, errors),
            review_check: require_field(raw.review_check, "review_check", &prefix, errors),
        });
    };

    let mut lines = text.lines();
    while let Some(line) = lines.next() {
        let trimmed = strip_comment(line).trim();
        if trimmed.is_empty() {
            continue;
        }
        if trimmed == "[auto_bump]" {
            finish_builder(
                builder.take(),
                exemption_index,
                &mut exemptions,
                &mut errors,
            );
            section = "auto_bump".to_owned();
            continue;
        }
        if trimmed == "[[auto_bump.exemptions]]" {
            finish_builder(
                builder.take(),
                exemption_index,
                &mut exemptions,
                &mut errors,
            );
            exemption_index += 1;
            section = "auto_bump.exemptions".to_owned();
            builder = Some(ExemptionBuilder::default());
            continue;
        }
        if section == "auto_bump" && trimmed.starts_with("repos") {
            let mut array_text = trimmed.to_owned();
            while !array_text.contains(']') {
                let Some(next) = lines.next() else { break };
                array_text.push('\n');
                array_text.push_str(strip_comment(next));
            }
            for repo in quoted_strings(&array_text) {
                repos.insert(canonical_url(&repo));
            }
            continue;
        }
        if section == "auto_bump.exemptions" {
            let Some(raw) = builder.as_mut() else {
                continue;
            };
            if let Some(value) = parse_string_assignment(trimmed, "repo") {
                raw.repo = Some(value);
            } else if let Some(value) = parse_string_assignment(trimmed, "dependency") {
                raw.dependency = Some(value);
            } else if let Some(value) = parse_string_assignment(trimmed, "manifest") {
                raw.manifest = Some(value);
            } else if let Some(value) = parse_string_assignment(trimmed, "kind") {
                raw.kind = Some(value);
            } else if let Some(value) = parse_string_assignment(trimmed, "lockfile_package") {
                raw.lockfile_package = Some(value);
            } else if let Some(value) = parse_bool_assignment(trimmed, "requires_revless_manifest")
            {
                raw.requires_revless_manifest = Some(value);
            } else if let Some(value) = parse_string_assignment(trimmed, "bump_command") {
                raw.bump_command = Some(value);
            } else if let Some(value) = parse_string_assignment(trimmed, "reason") {
                raw.reason = Some(value);
            } else if let Some(value) = parse_string_assignment(trimmed, "review_check") {
                raw.review_check = Some(value);
            }
        }
    }
    finish_builder(
        builder.take(),
        exemption_index,
        &mut exemptions,
        &mut errors,
    );
    (repos, exemptions, errors)
}

fn validate_exemption_text(exemption: &AutoBumpExemption) -> Vec<String> {
    let mut errors = Vec::new();
    if exemption.bump_command.len() < 20 {
        errors.push(format!(
            "{}: auto-bump exemption bump_command is too short to review",
            exemption.dependency
        ));
    }
    if exemption.reason.len() < 40 {
        errors.push(format!(
            "{}: auto-bump exemption reason is too short to review",
            exemption.dependency
        ));
    }
    if exemption.review_check.len() < 40 {
        errors.push(format!(
            "{}: auto-bump exemption review_check is too short",
            exemption.dependency
        ));
    }
    if !["Cargo.lock", "Cargo.toml", "cargo update", "ay release"]
        .iter()
        .any(|token| exemption.review_check.contains(token))
    {
        errors.push(format!(
            "{}: auto-bump exemption review_check must name a verifiable file or ay release command",
            exemption.dependency
        ));
    }
    if !exemption
        .review_check
        .contains("ay release verify-public-pins")
    {
        errors.push(format!(
            "{}: auto-bump exemption review_check must name ay release verify-public-pins",
            exemption.dependency
        ));
    }
    errors
}

fn validate_lockfile_only_exemption(
    dependency: &ManifestGitDependency,
    exemption: &AutoBumpExemption,
    lock_sources: &BTreeMap<String, Vec<LockEntry>>,
) -> Vec<String> {
    let mut errors = validate_exemption_text(exemption);
    if exemption.kind != "lockfile-only" {
        errors.push(format!(
            "{}: unsupported auto-bump exemption kind {:?}",
            dependency.dependency, exemption.kind
        ));
        return errors;
    }
    if !exemption.requires_revless_manifest {
        errors.push(format!(
            "{}: lockfile-only exemption must set requires_revless_manifest = true",
            dependency.dependency
        ));
    }
    if dependency.rev.is_some() {
        errors.push(format!(
            "{}: lockfile-only exemption requires a rev-less manifest dependency",
            dependency.dependency
        ));
    }
    let bump_tokens = exemption
        .bump_command
        .split_whitespace()
        .collect::<BTreeSet<_>>();
    if !(bump_tokens.contains("cargo")
        && bump_tokens.contains("update")
        && bump_tokens.contains("--precise")
        && bump_tokens.contains(exemption.lockfile_package.as_str()))
    {
        errors.push(format!(
            "{}: lockfile-only exemption bump_command must use cargo update -p <package> --precise <commit>",
            dependency.dependency
        ));
    }
    let entries = lock_sources
        .get(&canonical_url(&dependency.url))
        .cloned()
        .unwrap_or_default();
    let package_entries = entries
        .iter()
        .filter(|entry| entry.package_name == exemption.lockfile_package)
        .collect::<Vec<_>>();
    if package_entries.is_empty() {
        let packages = entries
            .iter()
            .map(|entry| entry.package_name.clone())
            .collect::<BTreeSet<_>>();
        errors.push(format!(
            "{}: exemption lockfile_package {:?} not found for {}; found packages={packages:?}",
            dependency.dependency, exemption.lockfile_package, dependency.url
        ));
        return errors;
    }
    let commits = package_entries
        .iter()
        .map(|entry| entry.source.commit.clone())
        .collect::<BTreeSet<_>>();
    let urls = package_entries
        .iter()
        .map(|entry| canonical_url(&entry.source.url))
        .collect::<BTreeSet<_>>();
    let revs = package_entries
        .iter()
        .map(|entry| entry.source.rev.clone())
        .collect::<BTreeSet<_>>();
    if urls.len() != 1 || !urls.contains(&canonical_url(&dependency.url)) {
        errors.push(format!(
            "{}: lockfile source URLs do not match manifest repo {}: {urls:?}",
            dependency.dependency, dependency.url
        ));
    }
    if commits.len() != 1 {
        errors.push(format!(
            "{}: multiple lockfile commits for exemption: {commits:?}",
            dependency.dependency
        ));
    } else if commits
        .iter()
        .next()
        .is_some_and(|commit| !full_sha(commit))
    {
        errors.push(format!(
            "{}: lockfile commit is not a full 40-hex id: {}",
            dependency.dependency,
            commits.iter().next().unwrap()
        ));
    }
    if revs != BTreeSet::from([None]) {
        let rendered = revs
            .iter()
            .map(|rev| rev.clone().unwrap_or_else(|| "<none>".to_owned()))
            .collect::<Vec<_>>();
        errors.push(format!(
            "{}: lockfile-only exemption expected no Cargo.lock rev query, found {rendered:?}",
            dependency.dependency
        ));
    }
    errors
}

fn validate_manifest_rev_pin(
    dependency: &ManifestGitDependency,
    lock_sources: &BTreeMap<String, Vec<LockEntry>>,
) -> Vec<String> {
    let mut errors = Vec::new();
    let Some(rev) = &dependency.rev else {
        return errors;
    };
    if !full_sha(rev) {
        errors.push(format!(
            "{}:{} manifest rev is not a full 40-hex id: {rev}",
            dependency.manifest, dependency.dependency
        ));
    }
    let entries = lock_sources
        .get(&canonical_url(&dependency.url))
        .cloned()
        .unwrap_or_default();
    if entries.is_empty() {
        errors.push(format!(
            "{}:{} manifest rev {rev} has no matching Cargo.lock source for {}",
            dependency.manifest, dependency.dependency, dependency.url
        ));
        return errors;
    }
    let lock_revs = entries
        .iter()
        .map(|entry| entry.source.rev.clone())
        .collect::<BTreeSet<_>>();
    if lock_revs != BTreeSet::from([Some(rev.clone())]) {
        let rendered = lock_revs
            .iter()
            .map(|rev| rev.clone().unwrap_or_else(|| "<none>".to_owned()))
            .collect::<Vec<_>>()
            .join(", ");
        errors.push(format!(
            "{}:{} manifest rev {rev} must match Cargo.lock rev query {rendered}",
            dependency.manifest, dependency.dependency
        ));
    }
    let lock_commits = entries
        .iter()
        .map(|entry| entry.source.commit.clone())
        .collect::<BTreeSet<_>>();
    if lock_commits != BTreeSet::from([rev.clone()]) {
        errors.push(format!(
            "{}:{} manifest rev {rev} must match Cargo.lock commit {}",
            dependency.manifest,
            dependency.dependency,
            lock_commits.into_iter().collect::<Vec<_>>().join(", ")
        ));
    }
    errors
}

fn verify_auto_bump_coverage(
    repo_root: &Path,
    manifest_paths: &[PathBuf],
    config_path: &Path,
    lockfile: &Path,
) -> (Vec<AutoBumpCoverage>, Vec<String>) {
    let (manifest_deps, mut errors) = load_manifest_git_dependencies(manifest_paths, repo_root);
    let (repos, exemptions, config_errors) = load_auto_bump_config(config_path);
    errors.extend(config_errors);
    if manifest_deps.is_empty() {
        return (Vec::new(), errors);
    }
    if !config_path.exists() {
        errors
            .push("manifest git dependencies exist, but cargo_wrapper.toml is missing".to_owned());
    }
    let exemption_by_dep = exemptions
        .iter()
        .map(|exemption| {
            (
                (
                    exemption.manifest.clone(),
                    exemption.dependency.clone(),
                    canonical_url(&exemption.repo),
                ),
                exemption.clone(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let dependency_keys = manifest_deps
        .iter()
        .map(|dependency| {
            (
                dependency.manifest.clone(),
                dependency.dependency.clone(),
                canonical_url(&dependency.url),
            )
        })
        .collect::<BTreeSet<_>>();
    for (key, exemption) in &exemption_by_dep {
        if !dependency_keys.contains(key) {
            errors.push(format!(
                "unused auto-bump exemption {}:{} {}",
                exemption.manifest, exemption.dependency, exemption.repo
            ));
        }
    }
    let (lock_sources, lock_errors) = load_git_lock_sources(lockfile);
    errors.extend(lock_errors);

    let mut coverage = Vec::new();
    for dependency in manifest_deps {
        let repo_key = canonical_url(&dependency.url);
        if repos.contains(&repo_key) {
            if dependency.rev.is_none() {
                errors.push(format!(
                    "{}:{} is listed in [auto_bump].repos but has no manifest rev for manifest-rev bump coverage; add a rev or use a machine-checked lockfile-only exemption",
                    dependency.manifest, dependency.dependency
                ));
            } else {
                errors.extend(validate_manifest_rev_pin(&dependency, &lock_sources));
            }
            coverage.push(AutoBumpCoverage {
                manifest: dependency.manifest.clone(),
                dependency: dependency.dependency.clone(),
                url: dependency.url.clone(),
                rev: dependency.rev.clone(),
                status: "listed".to_owned(),
                bump_method: Some("manifest-rev".to_owned()),
                bump_command: Some(format!(
                    "edit {} rev for {} to <new-commit>; cargo update -p {} --precise <new-commit>",
                    dependency.manifest, dependency.dependency, dependency.dependency
                )),
                check_command: Some("ay release verify-public-pins".to_owned()),
                kind: None,
                reason: None,
                review_check: None,
                updates: vec![dependency.manifest, repo_relative_path(repo_root, lockfile)],
            });
            continue;
        }
        let Some(exemption) = exemption_by_dep.get(&(
            dependency.manifest.clone(),
            dependency.dependency.clone(),
            repo_key,
        )) else {
            errors.push(format!(
                "{}:{} git dependency {} is not covered by [auto_bump].repos or [[auto_bump.exemptions]]",
                dependency.manifest, dependency.dependency, dependency.url
            ));
            continue;
        };
        errors.extend(validate_lockfile_only_exemption(
            &dependency,
            exemption,
            &lock_sources,
        ));
        coverage.push(AutoBumpCoverage {
            manifest: dependency.manifest,
            dependency: dependency.dependency,
            url: dependency.url,
            rev: dependency.rev,
            status: "exempt".to_owned(),
            bump_method: Some(exemption.kind.clone()),
            bump_command: Some(exemption.bump_command.clone()),
            check_command: Some("ay release verify-public-pins".to_owned()),
            kind: Some(exemption.kind.clone()),
            reason: Some(exemption.reason.clone()),
            review_check: Some(exemption.review_check.clone()),
            updates: vec![repo_relative_path(repo_root, lockfile)],
        });
    }
    (coverage, errors)
}

fn verify_release_fetch(pins: &[ReleasePin], quiet: bool) -> Result<Vec<String>> {
    let mut errors = Vec::new();
    let temp = TempWorkDir::new("ay-release-pins")?;
    let init = run_git(&["init", "-q"], &temp.path, &[])?;
    if !init.status.success() {
        return Ok(vec![command_detail(&init)]);
    }
    for pin in pins {
        let fetch = run_git(
            &["fetch", "--quiet", "--depth", "1", &pin.url, &pin.commit],
            &temp.path,
            &[],
        )?;
        if fetch.status.success() {
            if !quiet {
                println!("release-pin: FETCH {} {}", pin.name, pin.commit);
            }
        } else {
            errors.push(format!(
                "{}: cannot fetch {} from {}: {}",
                pin.name,
                pin.commit,
                pin.url,
                command_detail(&fetch)
            ));
        }
    }
    Ok(errors)
}

fn release_pins_json_evidence(
    repo_root: &Path,
    lockfile: &Path,
    config_path: &Path,
    manifest_paths: &[PathBuf],
    pins: &[ReleasePin],
    auto_bump_coverage: &[AutoBumpCoverage],
    errors: &[String],
    public_fetch_checked: bool,
) -> Value {
    let (source_commit, source_error) = current_git_head(repo_root);
    let mut source = Map::new();
    source.insert(
        "cargo_wrapper".to_owned(),
        json!(repo_relative_path(repo_root, config_path)),
    );
    source.insert(
        "lockfile".to_owned(),
        json!(repo_relative_path(repo_root, lockfile)),
    );
    source.insert(
        "manifests".to_owned(),
        json!(manifest_paths
            .iter()
            .map(|manifest| repo_relative_path(repo_root, manifest))
            .collect::<Vec<_>>()),
    );
    source.insert(
        "public_fetch_checked".to_owned(),
        json!(public_fetch_checked),
    );
    source.insert("ay_commit".to_owned(), json!(source_commit));
    if let Some(source_error) = source_error {
        source.insert("git_head_error".to_owned(), json!(source_error));
    }
    let mut payload = Map::new();
    payload.insert(
        "auto_bump".to_owned(),
        Value::Array(
            auto_bump_coverage
                .iter()
                .map(AutoBumpCoverage::to_json)
                .collect(),
        ),
    );
    payload.insert(
        "pins".to_owned(),
        Value::Array(pins.iter().map(ReleasePin::to_json).collect()),
    );
    payload.insert("schema".to_owned(), json!(RELEASE_PINS_SCHEMA));
    payload.insert("source".to_owned(), Value::Object(source));
    payload.insert(
        "status".to_owned(),
        json!(if errors.is_empty() { "pass" } else { "fail" }),
    );
    if !errors.is_empty() {
        payload.insert("errors".to_owned(), json!(errors));
    }
    Value::Object(payload)
}

fn load_json(path: &Path) -> Result<Value> {
    let text = fs::read_to_string(path)?;
    let value: Value = serde_json::from_str(&text)?;
    if !value.is_object() {
        anyhow::bail!("{} must contain a JSON object", path.display());
    }
    Ok(value)
}

fn nested<'a>(value: &'a Value, path: &[&str]) -> Option<&'a Value> {
    let mut current = value;
    for key in path {
        current = current.get(*key)?;
    }
    Some(current)
}

fn nested_str<'a>(value: &'a Value, path: &[&str]) -> Option<&'a str> {
    nested(value, path).and_then(Value::as_str)
}

fn nested_obj<'a>(value: &'a Value, path: &[&str]) -> Option<&'a Map<String, Value>> {
    nested(value, path).and_then(Value::as_object)
}

fn read_text_argument(
    value: &Option<String>,
    path: &Option<PathBuf>,
    label: &str,
) -> Result<String> {
    if let Some(value) = value {
        return Ok(value.clone());
    }
    if let Some(path) = path {
        return Ok(fs::read_to_string(path)?.trim().to_owned());
    }
    anyhow::bail!("{label} is required")
}

fn extract_build_field<'a>(text: &'a str, key: &str) -> Option<&'a str> {
    let prefix = format!("{key}=");
    text.lines()
        .find_map(|line| line.strip_prefix(&prefix).map(str::trim))
        .filter(|value| !value.is_empty())
}

fn parse_name_path(value: &str, label: &str) -> Result<(String, PathBuf)> {
    let Some((name, path)) = value.split_once('=') else {
        anyhow::bail!("{label} must be NAME=PATH: {value:?}");
    };
    if name.is_empty() || path.is_empty() {
        anyhow::bail!("{label} must be NAME=PATH: {value:?}");
    }
    Ok((name.to_owned(), PathBuf::from(path)))
}

fn gate_status_marker(name: &str, outcome: &str) -> String {
    format!(
        "{}: {}",
        name.replace('_', "-"),
        outcome.to_ascii_uppercase()
    )
}

fn infer_gate_outcome(name: &str, path: &Path) -> String {
    let Ok(text) = fs::read_to_string(path) else {
        return "missing".to_owned();
    };
    if text.contains(&gate_status_marker(name, "fail")) {
        "fail".to_owned()
    } else if text.contains(&gate_status_marker(name, "pass")) {
        "pass".to_owned()
    } else {
        "unknown".to_owned()
    }
}

fn path_status(name: &str, path: &Path) -> Value {
    let mut status = Map::new();
    status.insert("exists".to_owned(), json!(path.exists()));
    status.insert("name".to_owned(), json!(name));
    status.insert("path".to_owned(), json!(path.to_string_lossy()));
    if path.exists() {
        status.insert("outcome".to_owned(), json!(infer_gate_outcome(name, path)));
        if let Ok(metadata) = path.metadata() {
            status.insert("size_bytes".to_owned(), json!(metadata.len()));
        }
    }
    Value::Object(status)
}

fn launch_gate_summary_status(name: &str, path: &Path) -> Value {
    let mut status = Map::new();
    status.insert("exists".to_owned(), json!(path.exists()));
    status.insert("name".to_owned(), json!(name));
    status.insert("path".to_owned(), json!(path.to_string_lossy()));
    if !path.exists() {
        return Value::Object(status);
    }
    match load_json(path) {
        Ok(summary) => {
            for key in [
                "schema",
                "status",
                "evidence_gate_failures",
                "launch_blocker_count",
                "advisory_failures",
            ] {
                status.insert(
                    key.to_owned(),
                    summary.get(key).cloned().unwrap_or(Value::Null),
                );
            }
            if let Some(packet_checklist) =
                summary.get("packet_checklist").filter(|v| v.is_object())
            {
                status.insert("packet_checklist".to_owned(), packet_checklist.clone());
            }
            if let Some(blockers) = summary.get("blockers").filter(|v| v.is_array()) {
                status.insert("blockers".to_owned(), blockers.clone());
            }
        }
        Err(err) => {
            status.insert("parse_error".to_owned(), json!(err.to_string()));
        }
    }
    Value::Object(status)
}

fn artifact_status(repo_root: &Path, path: Option<&Path>) -> Result<Option<Value>> {
    let Some(path) = path else { return Ok(None) };
    let resolved_path = if path.is_absolute() {
        path.to_path_buf()
    } else {
        repo_root.join(path)
    };
    let mut status = Map::new();
    status.insert("exists".to_owned(), json!(resolved_path.exists()));
    status.insert("path".to_owned(), json!(path.to_string_lossy()));
    status.insert(
        "resolved_path".to_owned(),
        json!(resolved_path.to_string_lossy()),
    );
    if resolved_path.exists() {
        status.insert("sha256".to_owned(), json!(sha256_hex(&resolved_path)?));
        status.insert(
            "size_bytes".to_owned(),
            json!(resolved_path.metadata()?.len()),
        );
    }
    Ok(Some(Value::Object(status)))
}

fn bool_check(
    checks: &mut Map<String, Value>,
    errors: &mut Vec<String>,
    key: &str,
    passed: bool,
    error: &str,
) {
    checks.insert(key.to_owned(), json!(passed));
    if !passed {
        errors.push(error.to_owned());
    }
}

fn dependency_pin_components(dependency_pins: &Value) -> (Map<String, Value>, Vec<String>) {
    let mut errors = Vec::new();
    let mut components = Map::new();
    let Some(raw_pins) = dependency_pins.get("pins").and_then(Value::as_array) else {
        return (
            components,
            vec!["dependency pin evidence pins must be a list".to_owned()],
        );
    };
    for raw_pin in raw_pins {
        let Some(pin) = raw_pin.as_object() else {
            errors.push("dependency pin evidence pins must contain objects".to_owned());
            continue;
        };
        let Some(name) = pin
            .get("name")
            .and_then(Value::as_str)
            .filter(|value| !value.is_empty())
        else {
            errors.push("dependency pin evidence pin.name must be non-empty".to_owned());
            continue;
        };
        let Some(expected_url) = expected_repos()
            .into_iter()
            .find(|(expected_name, _)| *expected_name == name)
            .map(|(_, url)| url)
        else {
            continue;
        };
        let packages = pin
            .get("packages")
            .and_then(Value::as_array)
            .cloned()
            .unwrap_or_default();
        if packages.is_empty()
            || !packages
                .iter()
                .all(|package| package.as_str().is_some_and(|value| !value.is_empty()))
        {
            errors.push(format!("{name}: packages must be a non-empty string list"));
        }
        let package_versions = pin
            .get("package_versions")
            .and_then(Value::as_object)
            .cloned()
            .unwrap_or_default();
        if package_versions.is_empty() {
            errors.push(format!(
                "{name}: package_versions must be a non-empty object"
            ));
        }
        for package in &packages {
            if let Some(package) = package.as_str() {
                if package_versions
                    .get(package)
                    .and_then(Value::as_str)
                    .is_none_or(|value| value.is_empty())
                {
                    errors.push(format!("{name}: package_versions must include {package}"));
                }
            }
        }
        let component_version = pin.get("component_version").and_then(Value::as_str);
        if component_version.is_none_or(str::is_empty) {
            errors.push(format!(
                "{name}: component_version must be a non-empty string"
            ));
        } else if let Some(component_version) = component_version {
            let mismatches = package_versions
                .iter()
                .filter_map(|(package, version)| {
                    let version = version.as_str()?;
                    (version != component_version).then(|| format!("{package}={version}"))
                })
                .collect::<Vec<_>>();
            if !mismatches.is_empty() {
                errors.push(format!(
                    "{name}: component_version {component_version:?} must match all package_versions ({})",
                    mismatches.join(", ")
                ));
            }
        }
        if pin
            .get("url")
            .and_then(Value::as_str)
            .is_none_or(|url| canonical_url(url) != canonical_url(&expected_url))
        {
            errors.push(format!(
                "{name}: url={:?}, expected {:?}",
                pin.get("url").unwrap_or(&Value::Null),
                expected_url
            ));
        }
        if !pin
            .get("commit")
            .and_then(Value::as_str)
            .is_some_and(full_sha)
        {
            errors.push(format!("{name}: commit must be a full 40-hex object id"));
        }
        components.insert(
            name.to_owned(),
            json!({
                "component_version": pin.get("component_version").cloned().unwrap_or(Value::Null),
                "commit": pin.get("commit").cloned().unwrap_or(Value::Null),
                "package_versions": pin.get("package_versions").cloned().unwrap_or(Value::Null),
                "packages": pin.get("packages").cloned().unwrap_or(Value::Null),
                "rev": pin.get("rev").cloned().unwrap_or(Value::Null),
                "url": pin.get("url").cloned().unwrap_or(Value::Null),
            }),
        );
    }
    let missing = expected_repos()
        .iter()
        .map(|(name, _)| *name)
        .filter(|name| !components.contains_key(*name))
        .collect::<Vec<_>>();
    if !missing.is_empty() {
        errors.push(format!(
            "dependency pin evidence missing public components: {}",
            missing.join(", ")
        ));
    }
    (components, errors)
}

fn public_mirror_action_errors(public_evidence: &Value, private_commit: &str) -> Vec<String> {
    let failure_kind = public_evidence.get("failure_kind").and_then(Value::as_str);
    if public_evidence.get("status").and_then(Value::as_str) == Some("pass") {
        return Vec::new();
    }
    if !matches!(
        failure_kind,
        Some("public-object-not-fetchable" | "public-ref-mismatch" | "public-ref-not-advertised")
    ) {
        return Vec::new();
    }
    let Some(action) = public_evidence
        .get("mirror_action")
        .and_then(Value::as_object)
    else {
        return vec![
            "public mirror failure evidence must include mirror_action handoff".to_owned(),
        ];
    };
    let mut errors = Vec::new();
    let public_url = public_evidence.get("url").and_then(Value::as_str);
    let public_ref = public_evidence.get("public_ref").and_then(Value::as_str);
    for (key, expected) in [
        ("failure_kind", failure_kind),
        ("required_commit", Some(private_commit)),
        ("required_ref", public_ref),
        ("required_url", public_url),
    ] {
        if action.get(key).and_then(Value::as_str) != expected {
            errors.push(format!(
                "public mirror_action.{key} must match public evidence"
            ));
        }
    }
    if failure_kind == Some("public-ref-mismatch")
        && action.get("current_ref_commit") != public_evidence.get("ref_commit")
    {
        errors.push(
            "public mirror_action.current_ref_commit must match public ref_commit".to_owned(),
        );
    }
    let (Some(public_url), Some(public_ref)) = (public_url, public_ref) else {
        errors.push("public mirror_action requires public evidence url and ref".to_owned());
        return errors;
    };
    if action.get("example_publish_command")
        != Some(&json!(publish_command(
            public_url,
            private_commit,
            public_ref
        )))
    {
        errors.push("public mirror_action.example_publish_command must publish the private commit to the public ref".to_owned());
    }
    if action.get("verify_command")
        != Some(&json!(verify_public_ay_command(
            public_url,
            private_commit,
            public_ref
        )))
    {
        errors.push(
            "public mirror_action.verify_command must rerun the exact public commit verifier"
                .to_owned(),
        );
    }
    let expected_handoff = handoff_command(public_url, private_commit, public_ref);
    if action.get("handoff_command") != Some(&json!(expected_handoff)) {
        errors.push(
            "public mirror_action.handoff_command must run the public publish-and-verify handoff"
                .to_owned(),
        );
    }
    if action.get("handoff_output").and_then(Value::as_str)
        != Some("ay-public-commit-evidence.json")
    {
        errors.push(
            "public mirror_action.handoff_output must name ay-public-commit-evidence.json"
                .to_owned(),
        );
    }
    let expected_handoff_shell = format!(
        "{} > ay-public-commit-evidence.json",
        shell_join(&expected_handoff)
    );
    if action.get("handoff_shell_command").and_then(Value::as_str)
        != Some(expected_handoff_shell.as_str())
    {
        errors.push("public mirror_action.handoff_shell_command must write the publish-and-verify evidence JSON".to_owned());
    }
    if !action
        .get("required_actor")
        .and_then(Value::as_str)
        .is_some_and(|actor| actor.contains("write access"))
    {
        errors.push("public mirror_action.required_actor must name write access".to_owned());
    }
    if !action
        .get("note")
        .and_then(Value::as_str)
        .is_some_and(|note| note.contains("force-pushing"))
    {
        errors.push(
            "public mirror_action.note must warn against force-pushing release evidence".to_owned(),
        );
    }
    let Some(permission) = action.get("publish_permission").and_then(Value::as_object) else {
        errors.push(
            "public mirror_action.publish_permission must record required write access".to_owned(),
        );
        return errors;
    };
    if permission.get("checked") != Some(&json!(false))
        || permission.get("required") != Some(&json!(true))
        || permission.get("required_access").and_then(Value::as_str) != Some("write")
        || permission.get("required_url").and_then(Value::as_str) != Some(public_url)
        || permission.get("status").and_then(Value::as_str) != Some("not-checked")
    {
        errors.push(
            "public mirror_action.publish_permission must match required public write handoff"
                .to_owned(),
        );
    }
    if !permission
        .get("reason")
        .and_then(Value::as_str)
        .is_some_and(|reason| reason.contains("read-only") && reason.contains("git push"))
    {
        errors.push("public mirror_action.publish_permission.reason must explain that the verifier is read-only".to_owned());
    }
    errors
}

fn public_publish_attempt_errors(public_evidence: &Value, private_commit: &str) -> Vec<String> {
    let Some(attempt) = public_evidence.get("publish_attempt") else {
        return Vec::new();
    };
    let Some(attempt) = attempt.as_object() else {
        return vec!["public evidence publish_attempt must be an object when present".to_owned()];
    };
    let mut errors = Vec::new();
    let public_url = public_evidence.get("url").and_then(Value::as_str);
    let public_ref = public_evidence.get("public_ref").and_then(Value::as_str);
    if let (Some(public_url), Some(public_ref)) = (public_url, public_ref) {
        if attempt.get("command")
            != Some(&json!(publish_command(
                public_url,
                private_commit,
                public_ref
            )))
        {
            errors.push("public evidence publish_attempt.command must publish the private commit to the public ref".to_owned());
        }
    } else {
        errors.push(
            "public evidence publish_attempt requires non-empty url and public_ref".to_owned(),
        );
    }
    let status = attempt.get("status").and_then(Value::as_str);
    if !matches!(status, Some("pass" | "fail" | "skipped")) {
        errors.push(
            "public evidence publish_attempt.status must be pass, fail, or skipped".to_owned(),
        );
    }
    let checked = attempt.get("checked").and_then(Value::as_bool);
    if matches!(status, Some("pass" | "fail")) && checked != Some(true) {
        errors.push(
            "public evidence publish_attempt.checked must be true for a recorded publish attempt"
                .to_owned(),
        );
    }
    if status == Some("skipped") && checked != Some(false) {
        errors
            .push("public evidence publish_attempt.checked must be false when skipped".to_owned());
    }
    if !attempt
        .get("required_actor")
        .and_then(Value::as_str)
        .is_some_and(|actor| actor.contains("write access"))
    {
        errors.push(
            "public evidence publish_attempt.required_actor must name write access".to_owned(),
        );
    }
    if attempt.get("required_access").and_then(Value::as_str) != Some("write") {
        errors.push("public evidence publish_attempt.required_access must be write".to_owned());
    }
    let exit_code = attempt.get("exit_code").and_then(Value::as_i64);
    if status == Some("pass") {
        if exit_code != Some(0) {
            errors.push(
                "public evidence publish_attempt.exit_code must be 0 when status is pass"
                    .to_owned(),
            );
        }
        if public_evidence.get("status").and_then(Value::as_str) != Some("pass") {
            errors.push("public evidence publish_attempt pass cannot replace sanitized public verifier status pass".to_owned());
        }
    } else if status == Some("fail") && exit_code.is_none_or(|code| code == 0) {
        errors.push(
            "public evidence publish_attempt.exit_code must be nonzero when status is fail"
                .to_owned(),
        );
    }
    errors
}

fn ls_remote_refs_for(public_ref: &str) -> Vec<String> {
    let mut refs = vec![public_ref.to_owned()];
    if public_ref.starts_with("refs/tags/") {
        refs.push(format!("{public_ref}^{{}}"));
    }
    refs
}

fn should_validate_public_verifier_provenance(public_evidence: &Value) -> bool {
    public_evidence.get("status").and_then(Value::as_str) == Some("pass")
        || matches!(
            public_evidence.get("failure_kind").and_then(Value::as_str),
            Some(
                "public-object-not-fetchable" | "public-ref-mismatch" | "public-ref-not-advertised"
            )
        )
}

fn public_verifier_git_env_errors(public_evidence: &Value) -> Vec<String> {
    if !should_validate_public_verifier_provenance(public_evidence) {
        return Vec::new();
    }
    if public_evidence.get("git_env") != Some(&public_git_env_json()) {
        return vec![
            "public evidence git_env must match the sanitized public verifier environment"
                .to_owned(),
        ];
    }
    Vec::new()
}

fn public_verifier_command_errors(public_evidence: &Value, private_commit: &str) -> Vec<String> {
    if !should_validate_public_verifier_provenance(public_evidence) {
        return Vec::new();
    }
    let mut errors = Vec::new();
    let Some(public_url) = public_evidence
        .get("url")
        .and_then(Value::as_str)
        .filter(|value| !value.is_empty())
    else {
        return vec!["public evidence url must be a non-empty string".to_owned()];
    };
    let Some(public_ref) = public_evidence
        .get("public_ref")
        .and_then(Value::as_str)
        .filter(|value| !value.is_empty())
    else {
        return vec!["public evidence public_ref must be a non-empty string".to_owned()];
    };
    if public_evidence.get("fetch_command")
        != Some(&json!([
            "git",
            "fetch",
            "--depth",
            "1",
            public_url,
            private_commit
        ]))
    {
        errors.push(
            "public evidence fetch_command must fetch the private commit from the public URL"
                .to_owned(),
        );
    }
    let ref_checked_status = public_evidence.get("status").and_then(Value::as_str) == Some("pass")
        || matches!(
            public_evidence.get("failure_kind").and_then(Value::as_str),
            Some("public-ref-mismatch" | "public-ref-not-advertised")
        );
    if ref_checked_status {
        let mut expected = vec![
            "git".to_owned(),
            "ls-remote".to_owned(),
            "--exit-code".to_owned(),
            public_url.to_owned(),
        ];
        expected.extend(ls_remote_refs_for(public_ref));
        if public_evidence.get("ls_remote_command") != Some(&json!(expected)) {
            errors.push(
                "public evidence ls_remote_command must check the public launch ref".to_owned(),
            );
        }
    }
    errors
}

fn release_channel_semantics(channel: &str) -> Value {
    match channel {
        "private" => json!({
            "audience": "private-validation",
            "completed_public_release": false,
            "public_release_claim_allowed": false,
        }),
        "public-candidate" => json!({
            "audience": "public-release-candidate",
            "completed_public_release": false,
            "public_release_claim_allowed": false,
        }),
        _ => json!({
            "audience": "public-release",
            "completed_public_release": true,
            "public_release_claim_allowed": true,
        }),
    }
}

fn release_claim_status(
    channel: &str,
    manifest_pass: bool,
    public_commit_synced: bool,
    blocked_handoff_required: bool,
    blocked_handoff_complete: bool,
) -> &'static str {
    if channel == "public" && manifest_pass && public_commit_synced {
        "public-release-ready"
    } else if blocked_handoff_required && blocked_handoff_complete {
        "blocked-public-mirror-handoff"
    } else if channel == "public-candidate" && manifest_pass {
        "public-candidate-ready"
    } else if channel == "private" && manifest_pass {
        "private-validation"
    } else {
        "not-release-ready"
    }
}

fn public_mirror_handoff_status(
    public_commit_synced: bool,
    blocked_handoff_required: bool,
    blocked_handoff_complete: bool,
) -> &'static str {
    if public_commit_synced {
        "synced"
    } else if blocked_handoff_required && blocked_handoff_complete {
        "handoff-ready-for-maintainer"
    } else if blocked_handoff_required {
        "handoff-incomplete"
    } else {
        "not-synced"
    }
}

fn build_manifest(args: &GenerateManifestArgs) -> Result<(i32, Value)> {
    let repo_root = args
        .repo_root
        .canonicalize()
        .unwrap_or_else(|_| args.repo_root.clone());
    let private_commit = args
        .private_commit
        .clone()
        .map_or_else(|| git_head(&repo_root), Ok)?;
    let public_evidence = load_json(&args.public_evidence)?;
    let dependency_pins = load_json(&args.dependency_pins)?;
    let binary_version = read_text_argument(
        &args.binary_version,
        &args.binary_version_file,
        "binary version output",
    )?;

    let mut checks = Map::new();
    let mut errors = Vec::new();
    bool_check(
        &mut checks,
        &mut errors,
        "private_commit_full_hex",
        full_sha(&private_commit),
        "private ay commit must be a full 40-hex object id",
    );

    let public_status = public_evidence.get("status").and_then(Value::as_str);
    let public_expected_commit = public_evidence
        .get("expected_commit")
        .and_then(Value::as_str);
    let public_fetched_commit = public_evidence
        .get("fetched_commit")
        .and_then(Value::as_str);
    let public_ref_commit = public_evidence.get("ref_commit").and_then(Value::as_str);
    let dependency_source = dependency_pins.get("source").and_then(Value::as_object);
    let dependency_source_commit = dependency_source
        .and_then(|source| source.get("ay_commit"))
        .and_then(Value::as_str);
    let dependency_public_fetch_checked = dependency_source
        .and_then(|source| source.get("public_fetch_checked"))
        .and_then(Value::as_bool);

    bool_check(
        &mut checks,
        &mut errors,
        "public_evidence_schema",
        public_evidence.get("schema").and_then(Value::as_str) == Some(PUBLIC_COMMIT_SCHEMA),
        &format!("public evidence schema must be {PUBLIC_COMMIT_SCHEMA}"),
    );
    bool_check(
        &mut checks,
        &mut errors,
        "public_evidence_pass",
        public_status == Some("pass"),
        "public ay commit evidence status must be pass",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "public_expected_matches_private",
        public_expected_commit == Some(private_commit.as_str()),
        "public evidence expected_commit must match private ay commit",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "public_commit_field_matches_private",
        public_evidence.get("commit").and_then(Value::as_str) == Some(private_commit.as_str()),
        "public evidence commit must match private ay commit",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "public_fetch_matches_private",
        public_fetched_commit == Some(private_commit.as_str())
            && public_evidence.get("fetchable").and_then(Value::as_bool) == Some(true),
        "public fetched_commit must match private ay commit and be fetchable",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "public_ref_matches_private",
        public_ref_commit == Some(private_commit.as_str())
            && public_evidence
                .get("ref_matches_commit")
                .and_then(Value::as_bool)
                == Some(true),
        "public ref_commit must match private ay commit",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "public_evidence_failure_kind_clear",
        public_status != Some("pass")
            || public_evidence
                .get("failure_kind")
                .is_none_or(Value::is_null),
        "passing public ay commit evidence must not record a failure_kind",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "public_fetch_exit_zero",
        public_status != Some("pass")
            || (public_evidence.get("fetch_exit").and_then(Value::as_i64) == Some(0)
                && public_evidence
                    .get("rev_parse_exit")
                    .and_then(Value::as_i64)
                    == Some(0)),
        "passing public ay commit evidence must record zero fetch and rev-parse exits",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "public_ref_check_exit_zero",
        public_status != Some("pass")
            || (public_evidence.get("ref_checked").and_then(Value::as_bool) == Some(true)
                && public_evidence
                    .get("ls_remote_exit")
                    .and_then(Value::as_i64)
                    == Some(0)),
        "passing public ay commit evidence must record a zero public ref check exit",
    );
    let mirror_action_errors = public_mirror_action_errors(&public_evidence, &private_commit);
    checks.insert(
        "public_mirror_action_complete".to_owned(),
        json!(mirror_action_errors.is_empty()),
    );
    errors.extend(mirror_action_errors);
    let verifier_command_errors = public_verifier_command_errors(&public_evidence, &private_commit);
    checks.insert(
        "public_verifier_commands_match".to_owned(),
        json!(verifier_command_errors.is_empty()),
    );
    errors.extend(verifier_command_errors);
    let verifier_git_env_errors = public_verifier_git_env_errors(&public_evidence);
    checks.insert(
        "public_verifier_git_env_sanitized".to_owned(),
        json!(verifier_git_env_errors.is_empty()),
    );
    errors.extend(verifier_git_env_errors);
    let publish_attempt_errors = public_publish_attempt_errors(&public_evidence, &private_commit);
    checks.insert(
        "public_publish_attempt_consistent".to_owned(),
        json!(publish_attempt_errors.is_empty()),
    );
    errors.extend(publish_attempt_errors);

    bool_check(
        &mut checks,
        &mut errors,
        "dependency_pins_schema",
        dependency_pins.get("schema").and_then(Value::as_str) == Some(RELEASE_PINS_SCHEMA),
        &format!("dependency pin evidence schema must be {RELEASE_PINS_SCHEMA}"),
    );
    bool_check(
        &mut checks,
        &mut errors,
        "dependency_pins_pass",
        dependency_pins.get("status").and_then(Value::as_str) == Some("pass"),
        "dependency pin evidence status must be pass",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "dependency_pins_present",
        dependency_pins
            .get("pins")
            .and_then(Value::as_array)
            .is_some_and(|pins| !pins.is_empty()),
        "dependency pin evidence must contain pins",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "dependency_pins_source_matches_private",
        dependency_source_commit == Some(private_commit.as_str()),
        "dependency pin evidence source ay_commit must match private ay commit",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "dependency_pins_public_fetch_checked",
        args.channel != "public" || dependency_public_fetch_checked == Some(true),
        "public release manifest requires dependency pin evidence generated with public fetch checks",
    );
    let (dependency_components, dependency_component_errors) =
        dependency_pin_components(&dependency_pins);
    checks.insert(
        "dependency_public_components_complete".to_owned(),
        json!(dependency_component_errors.is_empty()),
    );
    errors.extend(dependency_component_errors);

    bool_check(
        &mut checks,
        &mut errors,
        "version_commit_prefix_len_positive",
        args.version_commit_prefix_len > 0,
        "version commit prefix length must be positive",
    );
    let prefix_len = args.version_commit_prefix_len.min(private_commit.len());
    let version_prefix = &private_commit[..prefix_len];
    let binary_build_version =
        extract_build_field(&binary_version, "build.version").map(str::to_owned);
    let binary_build_commit =
        extract_build_field(&binary_version, "build.commit").map(str::to_owned);
    let binary_build_stamp = extract_build_field(&binary_version, "build.stamp").map(str::to_owned);
    bool_check(
        &mut checks,
        &mut errors,
        "binary_version_present",
        !binary_version.trim().is_empty(),
        "binary version output must be non-empty",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "binary_version_build_version_present",
        binary_build_version.is_some(),
        "binary version output must contain build.version",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "binary_version_build_commit_present",
        binary_build_commit.is_some(),
        "binary version output must contain build.commit",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "binary_version_mentions_private_commit_prefix",
        !version_prefix.is_empty() && binary_version.contains(version_prefix),
        "binary version output must mention the private ay commit prefix",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "binary_version_build_commit_matches_private_prefix",
        binary_build_commit
            .as_deref()
            .is_some_and(|commit| !version_prefix.is_empty() && commit.starts_with(version_prefix)),
        "binary version build.commit must start with the private ay commit prefix",
    );

    let launch_gates = args
        .launch_gate_status
        .iter()
        .map(|value| {
            parse_name_path(value, "launch gate status")
                .map(|(name, path)| path_status(&name, &path))
        })
        .collect::<Result<Vec<_>>>()?;
    let launch_gate_summaries = args
        .launch_gate_summary
        .iter()
        .map(|value| {
            parse_name_path(value, "launch gate summary")
                .map(|(name, path)| launch_gate_summary_status(&name, &path))
        })
        .collect::<Result<Vec<_>>>()?;
    bool_check(
        &mut checks,
        &mut errors,
        "launch_gate_status_paths_present",
        !launch_gates.is_empty(),
        "at least one launch gate status path is required",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "launch_gate_status_paths_exist",
        launch_gates
            .iter()
            .all(|gate| gate.get("exists").and_then(Value::as_bool) == Some(true)),
        "all launch gate status paths must exist",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "launch_gate_status_paths_pass",
        !launch_gates.is_empty()
            && launch_gates
                .iter()
                .all(|gate| gate.get("outcome").and_then(Value::as_str) == Some("pass")),
        "all launch gate status paths must report PASS",
    );
    if !launch_gate_summaries.is_empty() {
        bool_check(
            &mut checks,
            &mut errors,
            "launch_gate_summary_paths_exist",
            launch_gate_summaries
                .iter()
                .all(|summary| summary.get("exists").and_then(Value::as_bool) == Some(true)),
            "all launch gate summary paths must exist",
        );
        bool_check(
            &mut checks,
            &mut errors,
            "launch_gate_summary_schemas",
            launch_gate_summaries.iter().all(|summary| {
                summary.get("schema").and_then(Value::as_str) == Some(RELEASE_GATE_SUMMARY_SCHEMA)
            }),
            &format!("all launch gate summaries must use schema {RELEASE_GATE_SUMMARY_SCHEMA}"),
        );
        bool_check(
            &mut checks,
            &mut errors,
            "launch_gate_summaries_pass",
            launch_gate_summaries.iter().all(|summary| {
                summary.get("status").and_then(Value::as_str) == Some("pass")
                    && summary
                        .get("evidence_gate_failures")
                        .and_then(Value::as_i64)
                        == Some(0)
                    && summary.get("launch_blocker_count").and_then(Value::as_i64) == Some(0)
            }),
            "all launch gate summaries must report PASS with zero blockers",
        );
    }

    let artifact_path = args
        .artifact_path
        .as_ref()
        .map(|path| path.to_string_lossy().to_string());
    let artifact = artifact_status(&repo_root, args.artifact_path.as_deref())?;
    let artifact_exists = artifact
        .as_ref()
        .and_then(|artifact| artifact.get("exists"))
        .and_then(Value::as_bool)
        == Some(true);
    let artifact_sha256 = artifact
        .as_ref()
        .and_then(|artifact| artifact.get("sha256"))
        .and_then(Value::as_str)
        .map(str::to_owned);
    let artifact_size_bytes = artifact
        .as_ref()
        .and_then(|artifact| artifact.get("size_bytes"))
        .and_then(Value::as_u64);
    bool_check(
        &mut checks,
        &mut errors,
        "public_release_artifact_path_present",
        args.channel != "public" || args.artifact_path.is_some(),
        "public release manifest requires --artifact-path",
    );
    if args.artifact_path.is_some() {
        bool_check(
            &mut checks,
            &mut errors,
            "artifact_path_exists",
            artifact_exists,
            "artifact path must exist so release manifest records SHA256 evidence",
        );
        bool_check(
            &mut checks,
            &mut errors,
            "artifact_sha256_recorded",
            artifact_sha256.as_ref().is_some_and(|sha| sha.len() == 64),
            "artifact SHA256 must be recorded for the provided artifact path",
        );
        bool_check(
            &mut checks,
            &mut errors,
            "artifact_size_recorded",
            artifact_size_bytes.is_some_and(|size| size > 0),
            "artifact size must be recorded for the provided artifact path",
        );
    }

    let check_true = |key: &str| checks.get(key).and_then(Value::as_bool) == Some(true);
    let public_commit_synced = check_true("public_evidence_pass")
        && check_true("public_expected_matches_private")
        && check_true("public_fetch_matches_private")
        && check_true("public_ref_matches_private")
        && check_true("public_evidence_failure_kind_clear")
        && check_true("public_fetch_exit_zero")
        && check_true("public_ref_check_exit_zero")
        && check_true("public_verifier_commands_match")
        && check_true("public_verifier_git_env_sanitized")
        && check_true("public_publish_attempt_consistent");
    let blocked_handoff_required = public_status != Some("pass")
        && matches!(
            public_evidence.get("failure_kind").and_then(Value::as_str),
            Some(
                "public-object-not-fetchable" | "public-ref-mismatch" | "public-ref-not-advertised"
            )
        );
    let blocked_handoff_complete = blocked_handoff_required
        && check_true("public_mirror_action_complete")
        && check_true("public_verifier_commands_match")
        && check_true("public_verifier_git_env_sanitized");
    let mirror_action = public_evidence
        .get("mirror_action")
        .cloned()
        .unwrap_or(Value::Null);
    let mirror_publish_permission = public_evidence
        .get("mirror_action")
        .and_then(|action| action.get("publish_permission"))
        .cloned()
        .unwrap_or(Value::Null);
    let manifest_pass = errors.is_empty();
    let claim_status = release_claim_status(
        &args.channel,
        manifest_pass,
        public_commit_synced,
        blocked_handoff_required,
        blocked_handoff_complete,
    );
    let mirror_handoff_status = public_mirror_handoff_status(
        public_commit_synced,
        blocked_handoff_required,
        blocked_handoff_complete,
    );

    let manifest = json!({
        "schema": RELEASE_MANIFEST_SCHEMA,
        "generated_at_utc": args.generated_at.clone().unwrap_or_else(utc_now_iso),
        "channel": args.channel,
        "release": {
            "blocked_handoff": {
                "complete": blocked_handoff_complete,
                "failure_kind": public_evidence.get("failure_kind").cloned().unwrap_or(Value::Null),
                "mirror_action": if blocked_handoff_required { mirror_action.clone() } else { Value::Null },
                "publish_permission": if blocked_handoff_required { mirror_publish_permission } else { Value::Null },
                "public_release_blocking": !public_commit_synced,
                "required": blocked_handoff_required,
                "status": mirror_handoff_status,
            },
            "channel": args.channel,
            "channel_semantics": release_channel_semantics(&args.channel),
            "claim_status": claim_status,
            "private_commit": private_commit,
            "public_mirror_handoff_status": mirror_handoff_status,
            "public_mirror_commit": public_ref_commit,
            "public_mirror_synced": public_commit_synced,
            "public_release_ready": claim_status == "public-release-ready",
            "version": {
                "build_commit": binary_build_commit.clone(),
                "build_stamp": binary_build_stamp.clone(),
                "build_version": binary_build_version.clone(),
                "commit_prefix_required": version_prefix,
                "output": binary_version.clone(),
            },
        },
        "private": {
            "ay_commit": private_commit,
        },
        "public": {
            "commit_evidence_path": args.public_evidence.to_string_lossy(),
            "commit_synced": public_commit_synced,
            "evidence": public_evidence,
            "failure_kind": public_evidence.get("failure_kind").cloned().unwrap_or(Value::Null),
            "mirror_action": public_evidence.get("mirror_action").cloned().unwrap_or(Value::Null),
            "mirror_handoff_status": mirror_handoff_status,
            "ay_commit": public_ref_commit,
            "ay_ref": public_evidence.get("public_ref").cloned().unwrap_or(Value::Null),
            "ay_url": public_evidence.get("url").cloned().unwrap_or(Value::Null),
        },
        "dependencies": {
            "auto_bump": dependency_pins.get("auto_bump").cloned().unwrap_or_else(|| json!([])),
            "components": dependency_components,
            "evidence_path": args.dependency_pins.to_string_lossy(),
            "pins": dependency_pins.get("pins").cloned().unwrap_or_else(|| json!([])),
            "source": dependency_pins.get("source").cloned().unwrap_or(Value::Null),
            "status": dependency_pins.get("status").cloned().unwrap_or(Value::Null),
        },
        "build": {
            "artifact": artifact,
            "artifact_exists": if args.artifact_path.is_some() { json!(artifact_exists) } else { Value::Null },
            "artifact_path": artifact_path,
            "artifact_sha256": artifact_sha256,
            "artifact_size_bytes": artifact_size_bytes,
            "binary_build_commit": binary_build_commit,
            "binary_build_stamp": binary_build_stamp,
            "binary_build_version": binary_build_version,
            "binary_version_output": binary_version,
            "command": args.build_command,
            "version_commit_prefix_len": args.version_commit_prefix_len,
        },
        "launch_gates": launch_gates,
        "launch_gate_summaries": launch_gate_summaries,
        "checks": checks,
        "errors": errors,
        "status": if manifest_pass { "pass" } else { "fail" },
    });
    Ok((if manifest_pass { 0 } else { 1 }, manifest))
}

fn utc_now_iso() -> String {
    let seconds = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs() as i64;
    let days = seconds.div_euclid(86_400);
    let secs = seconds.rem_euclid(86_400);
    let (year, month, day) = civil_from_days(days);
    let hour = secs / 3600;
    let minute = (secs % 3600) / 60;
    let second = secs % 60;
    format!("{year:04}-{month:02}-{day:02}T{hour:02}:{minute:02}:{second:02}Z")
}

fn civil_from_days(days_since_epoch: i64) -> (i64, i64, i64) {
    let z = days_since_epoch + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 }.div_euclid(146_097);
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096).div_euclid(365);
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2).div_euclid(153);
    let d = doy - (153 * mp + 2).div_euclid(5) + 1;
    let m = mp + if mp < 10 { 3 } else { -9 };
    let year = y + if m <= 2 { 1 } else { 0 };
    (year, m, d)
}

fn resolve_artifact_path(
    manifest_path: &Path,
    manifest: &Value,
    explicit_artifact: Option<&Path>,
) -> Option<PathBuf> {
    if let Some(explicit_artifact) = explicit_artifact {
        return Some(explicit_artifact.to_path_buf());
    }
    if let Some(artifact) = nested_obj(manifest, &["build", "artifact"]) {
        if let Some(resolved_path) = artifact
            .get("resolved_path")
            .and_then(Value::as_str)
            .filter(|path| !path.is_empty())
        {
            return Some(PathBuf::from(resolved_path));
        }
        if let Some(path) = artifact
            .get("path")
            .and_then(Value::as_str)
            .filter(|path| !path.is_empty())
        {
            let raw = PathBuf::from(path);
            return Some(if raw.is_absolute() {
                raw
            } else {
                manifest_path
                    .parent()
                    .unwrap_or_else(|| Path::new("."))
                    .join(raw)
            });
        }
    }
    let artifact_path = nested_str(manifest, &["build", "artifact_path"])?;
    let raw = PathBuf::from(artifact_path);
    Some(if raw.is_absolute() {
        raw
    } else {
        manifest_path
            .parent()
            .unwrap_or_else(|| Path::new("."))
            .join(raw)
    })
}

fn verify_dependency_components(
    manifest: &Value,
    checks: &mut Map<String, Value>,
    errors: &mut Vec<String>,
) {
    let components = nested_obj(manifest, &["dependencies", "components"]);
    for (name, expected_url) in expected_repos() {
        let component = components.and_then(|components| components.get(name));
        let Some(component) = component.and_then(Value::as_object) else {
            bool_check(
                checks,
                errors,
                &format!("dependency_{name}_present"),
                false,
                &format!("dependency component {name} must be present"),
            );
            continue;
        };
        bool_check(
            checks,
            errors,
            &format!("dependency_{name}_public_url"),
            component
                .get("url")
                .and_then(Value::as_str)
                .is_some_and(|url| canonical_url(url) == canonical_url(&expected_url)),
            &format!("dependency component {name} must use public URL {expected_url}"),
        );
        bool_check(
            checks,
            errors,
            &format!("dependency_{name}_commit_full_hex"),
            component
                .get("commit")
                .and_then(Value::as_str)
                .is_some_and(full_sha),
            &format!("dependency component {name} commit must be a full 40-hex object id"),
        );
        bool_check(
            checks,
            errors,
            &format!("dependency_{name}_component_version_present"),
            component
                .get("component_version")
                .and_then(Value::as_str)
                .is_some_and(|value| !value.is_empty()),
            &format!("dependency component {name} must record component_version"),
        );
        let packages = component.get("packages").and_then(Value::as_array);
        let package_names = packages
            .map(|packages| {
                packages
                    .iter()
                    .filter_map(Value::as_str)
                    .filter(|package| !package.is_empty())
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let packages_ok = packages.is_some_and(|packages| {
            !package_names.is_empty() && packages.len() == package_names.len()
        });
        let package_versions = component.get("package_versions").and_then(Value::as_object);
        let package_versions_ok = package_versions.is_some_and(|package_versions| {
            !package_versions.is_empty()
                && packages_ok
                && package_names.iter().all(|package| {
                    package_versions
                        .get(*package)
                        .and_then(Value::as_str)
                        .is_some_and(|version| !version.is_empty())
                })
        });
        bool_check(
            checks,
            errors,
            &format!("dependency_{name}_package_versions_present"),
            package_versions_ok,
            &format!("dependency component {name} must record package_versions for every package"),
        );
    }
}

fn verify_launch_gate_evidence(
    manifest: &Value,
    checks: &mut Map<String, Value>,
    errors: &mut Vec<String>,
) {
    let launch_gates = manifest.get("launch_gates").and_then(Value::as_array);
    let launch_gate_rows_ok =
        launch_gates.is_some_and(|rows| !rows.is_empty() && rows.iter().all(Value::is_object));
    bool_check(
        checks,
        errors,
        "launch_gate_status_rows_present",
        launch_gate_rows_ok,
        "release manifest must record at least one launch gate status row",
    );
    if let Some(rows) = launch_gates.filter(|_| launch_gate_rows_ok) {
        bool_check(
            checks,
            errors,
            "launch_gate_status_rows_pass",
            rows.iter().all(|row| {
                row.get("exists").and_then(Value::as_bool) == Some(true)
                    && row.get("outcome").and_then(Value::as_str) == Some("pass")
            }),
            "all release manifest launch gate status rows must exist and report pass",
        );
    }
    let Some(summaries) = manifest.get("launch_gate_summaries") else {
        return;
    };
    let summary_rows = summaries.as_array();
    let summary_rows_ok = summary_rows.is_some_and(|rows| rows.iter().all(Value::is_object));
    bool_check(
        checks,
        errors,
        "launch_gate_summary_rows_well_formed",
        summary_rows_ok,
        "release manifest launch gate summaries must be a list of objects",
    );
    if let Some(rows) = summary_rows.filter(|_| summary_rows_ok) {
        bool_check(
            checks,
            errors,
            "launch_gate_summary_rows_pass",
            rows.iter().all(|row| {
                row.get("exists").and_then(Value::as_bool) == Some(true)
                    && row.get("schema").and_then(Value::as_str) == Some(RELEASE_GATE_SUMMARY_SCHEMA)
                    && row.get("status").and_then(Value::as_str) == Some("pass")
                    && row.get("evidence_gate_failures").and_then(Value::as_i64) == Some(0)
                    && row.get("launch_blocker_count").and_then(Value::as_i64) == Some(0)
            }),
            "all release manifest launch gate summaries must exist and report pass with zero blockers",
        );
    }
}

fn run_artifact_version(path: &Path) -> Result<(i32, String, String)> {
    let output = Command::new(path).arg("--version").output()?;
    Ok((
        output.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&output.stdout).trim().to_owned(),
        String::from_utf8_lossy(&output.stderr).trim().to_owned(),
    ))
}

fn verify_manifest(
    manifest_path: &Path,
    artifact_path: Option<&Path>,
    run_version: bool,
) -> Result<(i32, Value)> {
    let manifest = load_json(manifest_path)?;
    let mut checks = Map::new();
    let mut errors = Vec::new();

    let private_commit = nested_str(&manifest, &["release", "private_commit"]);
    let public_commit = nested_str(&manifest, &["release", "public_mirror_commit"]);
    let build_commit = nested_str(&manifest, &["build", "binary_build_commit"]);
    let binary_version_output = nested_str(&manifest, &["build", "binary_version_output"]);
    let artifact = nested_obj(&manifest, &["build", "artifact"])
        .cloned()
        .unwrap_or_default();
    let artifact_file = resolve_artifact_path(manifest_path, &manifest, artifact_path);
    let public_evidence = nested_obj(&manifest, &["public", "evidence"])
        .cloned()
        .unwrap_or_default();

    bool_check(
        &mut checks,
        &mut errors,
        "manifest_schema",
        manifest.get("schema").and_then(Value::as_str) == Some(RELEASE_MANIFEST_SCHEMA),
        &format!("manifest schema must be {RELEASE_MANIFEST_SCHEMA}"),
    );
    bool_check(
        &mut checks,
        &mut errors,
        "manifest_status_pass",
        manifest.get("status").and_then(Value::as_str) == Some("pass"),
        "release manifest status must be pass",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "manifest_checks_all_true",
        manifest
            .get("checks")
            .and_then(Value::as_object)
            .is_some_and(|checks| {
                !checks.is_empty() && checks.values().all(|value| value.as_bool() == Some(true))
            }),
        "all embedded release manifest checks must be true",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "public_channel",
        manifest.get("channel").and_then(Value::as_str) == Some("public")
            && nested_str(&manifest, &["release", "channel"]) == Some("public"),
        "manifest must describe the public release channel",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "public_release_ready",
        nested_str(&manifest, &["release", "claim_status"]) == Some("public-release-ready")
            && nested(&manifest, &["release", "public_release_ready"]).and_then(Value::as_bool)
                == Some(true),
        "manifest must be a public-release-ready claim",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "private_commit_full_hex",
        private_commit.is_some_and(full_sha),
        "private ay commit must be a full 40-hex object id",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "public_commit_matches_private",
        public_commit == private_commit
            && nested(&manifest, &["public", "commit_synced"]).and_then(Value::as_bool)
                == Some(true),
        "public mirror commit must match the private ay commit",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "public_evidence_pass",
        public_evidence.get("status").and_then(Value::as_str) == Some("pass")
            && public_evidence.get("commit").and_then(Value::as_str) == private_commit
            && public_evidence
                .get("expected_commit")
                .and_then(Value::as_str)
                == private_commit
            && public_evidence
                .get("fetched_commit")
                .and_then(Value::as_str)
                == private_commit
            && public_evidence.get("ref_commit").and_then(Value::as_str) == private_commit
            && public_evidence
                .get("failure_kind")
                .is_none_or(Value::is_null)
            && public_evidence.get("fetchable").and_then(Value::as_bool) == Some(true)
            && public_evidence.get("ref_checked").and_then(Value::as_bool) == Some(true)
            && public_evidence
                .get("ref_matches_commit")
                .and_then(Value::as_bool)
                == Some(true)
            && public_evidence.get("fetch_exit").and_then(Value::as_i64) == Some(0)
            && public_evidence
                .get("rev_parse_exit")
                .and_then(Value::as_i64)
                == Some(0)
            && public_evidence
                .get("ls_remote_exit")
                .and_then(Value::as_i64)
                == Some(0),
        "embedded public commit evidence must pass for the private ay commit",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "public_evidence_location",
        public_evidence.get("url").and_then(Value::as_str) == Some(PUBLIC_AY_URL)
            && public_evidence.get("public_ref").and_then(Value::as_str) == Some(PUBLIC_AY_REF),
        &format!("embedded public commit evidence must check {PUBLIC_AY_URL} {PUBLIC_AY_REF}"),
    );
    bool_check(
        &mut checks,
        &mut errors,
        "public_evidence_git_env_sanitized",
        public_evidence.get("git_env") == Some(&public_git_env_json()),
        "embedded public commit evidence must use the sanitized git environment",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "public_evidence_fetch_command",
        private_commit.is_some_and(|commit| {
            public_evidence.get("fetch_command")
                == Some(&json!([
                    "git",
                    "fetch",
                    "--depth",
                    "1",
                    PUBLIC_AY_URL,
                    commit
                ]))
        }),
        "embedded public commit evidence fetch command must fetch the private commit",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "public_evidence_ls_remote_command",
        public_evidence.get("ls_remote_command")
            == Some(&json!([
                "git",
                "ls-remote",
                "--exit-code",
                PUBLIC_AY_URL,
                PUBLIC_AY_REF
            ])),
        "embedded public commit evidence must check the public launch ref",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "dependency_evidence_pass",
        nested_str(&manifest, &["dependencies", "status"]) == Some("pass")
            && nested_str(&manifest, &["dependencies", "source", "ay_commit"]) == private_commit,
        "dependency pin evidence must pass and come from the private ay commit",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "dependency_public_fetch_checked",
        nested(
            &manifest,
            &["dependencies", "source", "public_fetch_checked"],
        )
        .and_then(Value::as_bool)
            == Some(true),
        "dependency pin evidence must include public fetch checks",
    );
    verify_dependency_components(&manifest, &mut checks, &mut errors);
    verify_launch_gate_evidence(&manifest, &mut checks, &mut errors);
    bool_check(
        &mut checks,
        &mut errors,
        "binary_build_commit_matches_private",
        build_commit.is_some_and(|build_commit| {
            (7..=40).contains(&build_commit.len())
                && build_commit.bytes().all(|b| b.is_ascii_hexdigit())
                && private_commit
                    .is_some_and(|private_commit| private_commit.starts_with(build_commit))
        }),
        "binary build.commit must be a prefix of the private ay commit",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "binary_version_output_mentions_build_commit",
        binary_version_output
            .is_some_and(|output| build_commit.is_some_and(|commit| output.contains(commit))),
        "binary version output must mention the recorded build.commit",
    );
    bool_check(
        &mut checks,
        &mut errors,
        "artifact_path_available",
        artifact_file.is_some(),
        "artifact path must be supplied or recorded in the manifest",
    );
    let mut artifact_evidence = Map::new();
    artifact_evidence.insert(
        "manifest_path".to_owned(),
        artifact.get("path").cloned().unwrap_or(Value::Null),
    );
    artifact_evidence.insert(
        "manifest_resolved_path".to_owned(),
        artifact
            .get("resolved_path")
            .cloned()
            .unwrap_or(Value::Null),
    );
    if let Some(artifact_file) = &artifact_file {
        artifact_evidence.insert("path".to_owned(), json!(artifact_file.to_string_lossy()));
        let exists = artifact_file.exists();
        artifact_evidence.insert("exists".to_owned(), json!(exists));
        bool_check(
            &mut checks,
            &mut errors,
            "artifact_exists",
            exists,
            "artifact path must exist",
        );
        if exists {
            let actual_sha256 = sha256_hex(artifact_file)?;
            let actual_size = artifact_file.metadata()?.len();
            artifact_evidence.insert("sha256".to_owned(), json!(actual_sha256));
            artifact_evidence.insert("size_bytes".to_owned(), json!(actual_size));
            bool_check(
                &mut checks,
                &mut errors,
                "artifact_sha256_matches_manifest",
                artifact_evidence.get("sha256").and_then(Value::as_str)
                    == artifact.get("sha256").and_then(Value::as_str)
                    && artifact_evidence.get("sha256").and_then(Value::as_str)
                        == nested_str(&manifest, &["build", "artifact_sha256"])
                    && artifact_evidence
                        .get("sha256")
                        .and_then(Value::as_str)
                        .is_some_and(|sha| {
                            sha.len() == 64
                                && sha
                                    .bytes()
                                    .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
                        }),
                "artifact SHA256 must match the release manifest",
            );
            bool_check(
                &mut checks,
                &mut errors,
                "artifact_size_matches_manifest",
                artifact.get("size_bytes").and_then(Value::as_u64) == Some(actual_size)
                    && nested(&manifest, &["build", "artifact_size_bytes"]).and_then(Value::as_u64)
                        == Some(actual_size),
                "artifact size must match the release manifest",
            );
        }
    }
    if run_version {
        if let Some(artifact_file) = artifact_file.filter(|path| path.exists()) {
            let (returncode, stdout, stderr) = run_artifact_version(&artifact_file)?;
            artifact_evidence.insert("version_returncode".to_owned(), json!(returncode));
            artifact_evidence.insert("version_stdout".to_owned(), json!(stdout));
            if !stderr.is_empty() {
                artifact_evidence.insert("version_stderr".to_owned(), json!(stderr));
            }
            bool_check(
                &mut checks,
                &mut errors,
                "artifact_version_matches_manifest",
                returncode == 0 && Some(stdout.as_str()) == binary_version_output,
                "artifact --version output must match the release manifest",
            );
        } else {
            bool_check(
                &mut checks,
                &mut errors,
                "artifact_version_matches_manifest",
                false,
                "cannot run artifact --version because artifact is missing",
            );
        }
    }

    let payload = json!({
        "schema": RELEASE_MANIFEST_VERIFICATION_SCHEMA,
        "manifest": {
            "channel": manifest.get("channel").cloned().unwrap_or(Value::Null),
            "claim_status": nested(&manifest, &["release", "claim_status"]).cloned().unwrap_or(Value::Null),
            "path": manifest_path.to_string_lossy(),
            "private_commit": private_commit,
            "public_mirror_commit": public_commit,
        },
        "artifact": artifact_evidence,
        "checks": checks,
        "errors": errors,
        "status": if errors.is_empty() { "pass" } else { "fail" },
    });
    Ok((if errors.is_empty() { 0 } else { 1 }, payload))
}
