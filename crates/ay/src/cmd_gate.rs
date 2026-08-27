// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native local/release gates.

use anyhow::{bail, Context, Result};
use clap::{Args, Subcommand};
use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command as ProcessCommand, Stdio};
use std::time::{Duration, UNIX_EPOCH};
use wait_timeout::ChildExt;

mod publish;
mod solver_steps;
use self::{publish::is_executable_file, solver_steps::solver_gate_cargo_steps};

#[derive(Subcommand)]
pub(crate) enum GateCommand {
    /// Run the fast local repository health smoke check.
    Health(HealthGateArgs),
    /// Run repo-local staged-tree pre-commit guards.
    Precommit(PrecommitGateArgs),
    /// Run the checked-in local solver gate.
    Solver(SolverGateArgs),
    /// Run the checked-in local publication gate.
    Publish(PublishGateArgs),
}

#[derive(Args)]
pub(crate) struct HealthGateArgs {
    /// Repository root to check.
    #[arg(long)]
    repo_root: Option<PathBuf>,

    /// Print the health checks without running them.
    #[arg(long)]
    list_checks: bool,

    /// Do not invoke cargo build if the release binary is stale or missing.
    #[arg(long)]
    no_build: bool,
}

#[derive(Args)]
pub(crate) struct PrecommitGateArgs {
    /// Repository root to check.
    #[arg(long)]
    repo_root: Option<PathBuf>,

    /// Print the pre-commit checks without running them.
    #[arg(long)]
    list_checks: bool,
}

#[derive(Args)]
pub(crate) struct SolverGateArgs {
    /// Repository root to check.
    #[arg(long)]
    repo_root: Option<PathBuf>,

    /// Critical solver landing range. Defaults to SOLVER_GATE_CRITICAL_SOLVER_RANGE
    /// or the upstream-ahead range.
    #[arg(long)]
    critical_solver_range: Option<String>,

    /// Print the gate steps without running heavyweight checks.
    #[arg(long)]
    list_steps: bool,
}

#[derive(Args)]
pub(crate) struct PublishGateArgs {
    /// Repository root to check.
    #[arg(long)]
    repo_root: Option<PathBuf>,

    /// Critical solver landing range. Defaults to PUBLISH_GATE_CRITICAL_SOLVER_RANGE
    /// or the upstream-ahead range.
    #[arg(long)]
    critical_solver_range: Option<String>,

    /// Print the gate steps without running heavyweight checks.
    #[arg(long)]
    list_steps: bool,
}

#[derive(Clone)]
struct ExternalStep {
    name: &'static str,
    program: &'static str,
    args: Vec<String>,
    env: Vec<(&'static str, String)>,
}

impl ExternalStep {
    fn new(name: &'static str, program: &'static str, args: &[&str]) -> Self {
        Self {
            name,
            program,
            args: args.iter().map(|arg| (*arg).to_string()).collect(),
            env: Vec::new(),
        }
    }

    fn with_env(mut self, key: &'static str, value: &str) -> Self {
        self.env.push((key, value.to_string()));
        self
    }

    fn rendered(&self) -> String {
        render_command(self.program, &self.args, &self.env)
    }
}

pub(crate) fn run(command: GateCommand) -> Result<i32> {
    match command {
        GateCommand::Health(args) => run_health_gate(&args),
        GateCommand::Precommit(args) => run_precommit_gate(&args),
        GateCommand::Solver(args) => run_solver_gate(&args),
        GateCommand::Publish(args) => publish::run(&args),
    }
}

fn run_health_gate(args: &HealthGateArgs) -> Result<i32> {
    let repo_root = resolve_repo_root(args.repo_root.as_deref())?;
    if args.list_checks {
        println!("[health-gate] checks");
        for check in HealthCheck::all() {
            println!("{}", check.name());
        }
        return Ok(0);
    }

    let failed = run_health_checks(&repo_root, !args.no_build)?;
    Ok(if failed { 1 } else { 0 })
}

fn run_precommit_gate(args: &PrecommitGateArgs) -> Result<i32> {
    let repo_root = resolve_repo_root(args.repo_root.as_deref())?;
    let checks = [
        "theory-verification",
        "todo-issue-refs",
        "reject-colon-filenames",
        "reject-transient-worktree-paths",
    ];
    if args.list_checks {
        println!("[precommit-gate] checks");
        for check in checks {
            println!("{check}");
        }
        return Ok(0);
    }

    println!("[precommit-gate] Root: {}", repo_root.display());
    run_native_step("precommit-gate", "theory-verification", || {
        check_staged_theory_verification(&repo_root)
    })?;
    run_native_step("precommit-gate", "todo-issue-refs", || {
        check_staged_todo_issue_refs(&repo_root)
    })?;
    run_native_step("precommit-gate", "reject-colon-filenames", || {
        check_staged_colon_filenames(&repo_root)
    })?;
    run_native_step("precommit-gate", "reject-transient-worktree-paths", || {
        check_staged_transient_worktree_paths(&repo_root)
    })?;
    println!("[precommit-gate] PASS");
    Ok(0)
}

#[derive(Clone, Copy)]
enum HealthCheck {
    GitRebaseState,
    SubmoduleMetadata,
    ReportsDirectory,
    Compile,
    SmtSat,
    SmtUnsat,
    ChcSafe,
}

impl HealthCheck {
    fn all() -> &'static [Self] {
        &[
            Self::GitRebaseState,
            Self::SubmoduleMetadata,
            Self::ReportsDirectory,
            Self::Compile,
            Self::SmtSat,
            Self::SmtUnsat,
            Self::ChcSafe,
        ]
    }

    fn name(self) -> &'static str {
        match self {
            Self::GitRebaseState => "Git Rebase State",
            Self::SubmoduleMetadata => "Submodule Metadata",
            Self::ReportsDirectory => "Reports Directory",
            Self::Compile => "Compile",
            Self::SmtSat => "SMT SAT",
            Self::SmtUnsat => "SMT UNSAT",
            Self::ChcSafe => "CHC Safe",
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum HealthStatus {
    Pass,
    Warn,
    Fail,
}

impl HealthStatus {
    fn as_str(self) -> &'static str {
        match self {
            Self::Pass => "PASS",
            Self::Warn => "WARN",
            Self::Fail => "FAIL",
        }
    }
}

struct HealthResult {
    status: HealthStatus,
    message: String,
}

impl HealthResult {
    fn pass(message: impl Into<String>) -> Self {
        Self {
            status: HealthStatus::Pass,
            message: message.into(),
        }
    }

    fn warn(message: impl Into<String>) -> Self {
        Self {
            status: HealthStatus::Warn,
            message: message.into(),
        }
    }

    fn fail(message: impl Into<String>) -> Self {
        Self {
            status: HealthStatus::Fail,
            message: message.into(),
        }
    }
}

fn run_health_checks(repo_root: &Path, allow_build: bool) -> Result<bool> {
    println!("AY System Health Check");
    println!("========================================");

    let mut failed = 0usize;
    let mut warned = 0usize;
    for check in HealthCheck::all() {
        let result = match run_one_health_check(repo_root, *check, allow_build) {
            Ok(result) => result,
            Err(error) => HealthResult::fail(format!("Exception - {error:#}")),
        };
        let first_line = result.message.lines().next().unwrap_or("");
        println!(
            "[{}] {}: {}",
            result.status.as_str(),
            check.name(),
            first_line
        );
        if result.status == HealthStatus::Fail {
            failed += 1;
            for line in result.message.lines().skip(1) {
                println!("       {line}");
            }
            break;
        }
        if result.status == HealthStatus::Warn {
            warned += 1;
        }
    }

    println!("========================================");
    if failed > 0 {
        println!("HEALTH CHECK FAILED: {failed} check(s) failed");
        return Ok(true);
    }
    if warned > 0 {
        println!("HEALTH CHECK PASSED (with {warned} warning(s))");
        return Ok(false);
    }
    println!("HEALTH CHECK PASSED: All checks OK");
    Ok(false)
}

fn run_one_health_check(
    repo_root: &Path,
    check: HealthCheck,
    allow_build: bool,
) -> Result<HealthResult> {
    match check {
        HealthCheck::GitRebaseState => check_git_rebase_state(repo_root),
        HealthCheck::SubmoduleMetadata => check_submodule_metadata(repo_root),
        HealthCheck::ReportsDirectory => check_reports_directory(repo_root),
        HealthCheck::Compile => check_cargo_build_health(repo_root, allow_build),
        HealthCheck::SmtSat => check_smt_smoke(repo_root, "SAT", "sat", SMT_SAT_SMOKE, &[]),
        HealthCheck::SmtUnsat => check_smt_smoke(repo_root, "UNSAT", "unsat", SMT_UNSAT_SMOKE, &[]),
        HealthCheck::ChcSafe => {
            check_smt_smoke(repo_root, "SAFE", "safe", CHC_SAFE_SMOKE, &["--chc"])
        }
    }
}

fn run_solver_gate(args: &SolverGateArgs) -> Result<i32> {
    let repo_root = resolve_repo_root(args.repo_root.as_deref())?;
    let critical_range = resolve_critical_range(
        &repo_root,
        args.critical_solver_range.as_deref(),
        "SOLVER_GATE_CRITICAL_SOLVER_RANGE",
    )?;

    println!("[solver-gate] Root: {}", repo_root.display());
    println!("[solver-gate] critical_solver_range={critical_range}");

    let mut steps = Vec::new();
    steps.push(ExternalStep::new(
        "critical_solver_policy",
        "bash",
        &[CRITICAL_SOLVER_POLICY_PATH, "--rev-range", &critical_range],
    ));
    steps.push(ExternalStep::new("z3_version", "z3", &["--version"]));
    steps.extend(solver_gate_cargo_steps());

    if args.list_steps {
        print_steps("solver-gate", &steps, &["solver_gate_wiring"]);
        return Ok(0);
    }

    run_native_step("solver-gate", "solver_gate_wiring", || {
        check_local_solver_gate_entrypoint(&repo_root)
    })?;
    for step in &steps {
        run_external_step("solver-gate", &repo_root, step)?;
    }
    println!("[solver-gate] PASS");
    Ok(0)
}

fn check_staged_theory_verification(repo_root: &Path) -> Result<()> {
    let mut errors = Vec::new();
    for file in git_lines(
        repo_root,
        &["diff", "--cached", "--name-only", "--diff-filter=ACM"],
    )? {
        if !(file.starts_with("crates/ay-theories/") && file.ends_with("/src/lib.rs")) {
            continue;
        }
        let theory_dir = Path::new(&file)
            .parent()
            .with_context(|| format!("resolve parent for {file}"))?;
        let verification_file = theory_dir.join("verification.rs");
        let verification_dir = theory_dir.join("verification");
        if path_contains_kani_proof(repo_root, Path::new(&file))?
            || path_contains_kani_proof(repo_root, &verification_file)?
            || dir_contains_kani_proof(repo_root, &verification_dir)?
        {
            continue;
        }
        errors.push(format!(
            "{file} missing Kani proof coverage in lib.rs, verification.rs, or verification/"
        ));
    }
    if errors.is_empty() {
        return Ok(());
    }
    bail!(
        "theory verification failed:\n{}",
        errors
            .iter()
            .map(|error| format!("  - {error}"))
            .collect::<Vec<_>>()
            .join("\n")
    )
}

fn check_staged_todo_issue_refs(repo_root: &Path) -> Result<()> {
    let mut errors = Vec::new();
    for file in git_lines(
        repo_root,
        &["diff", "--cached", "--name-only", "--diff-filter=ACM"],
    )? {
        if !(file.starts_with("crates/")
            && Path::new(&file).extension().is_some_and(|ext| ext == "rs"))
        {
            continue;
        }
        let Some(text) = staged_text(repo_root, Path::new(&file))? else {
            continue;
        };
        let bad_lines = text
            .lines()
            .enumerate()
            .filter(|&(_index, line)| has_bare_todo_comment(line))
            .map(|(index, line)| format!("{}:{}", index + 1, line.trim_end()))
            .collect::<Vec<_>>();
        if !bad_lines.is_empty() {
            errors.push(format!(
                "{file} has bare TODO comments missing issue refs:\n{}",
                bad_lines
                    .iter()
                    .map(|line| format!("    {line}"))
                    .collect::<Vec<_>>()
                    .join("\n")
            ));
        }
    }
    if errors.is_empty() {
        return Ok(());
    }
    bail!(
        "TODO enforcement failed:\n{}",
        errors
            .iter()
            .map(|error| format!("  - {error}"))
            .collect::<Vec<_>>()
            .join("\n")
    )
}

fn check_staged_colon_filenames(repo_root: &Path) -> Result<()> {
    let offenders = git_lines(
        repo_root,
        &[
            "diff",
            "--cached",
            "--name-only",
            "--diff-filter=A",
            "--",
            "crates/",
        ],
    )?
    .into_iter()
    .filter(|file| {
        Path::new(file)
            .file_name()
            .and_then(|name| name.to_str())
            .is_some_and(|name| name.contains(':'))
    })
    .collect::<Vec<_>>();
    if offenders.is_empty() {
        return Ok(());
    }
    bail!(
        "colon filenames are not allowed under crates/:\n{}",
        offenders
            .iter()
            .map(|file| format!("  - {file}"))
            .collect::<Vec<_>>()
            .join("\n")
    )
}

fn check_staged_transient_worktree_paths(repo_root: &Path) -> Result<()> {
    let tree = git_stdout(repo_root, &["write-tree"])?;
    if tree.is_empty() {
        return Ok(());
    }
    let paths = git_lines(
        repo_root,
        &["ls-tree", "-r", "--name-only", &tree, "--", ".worktrees/"],
    )?;
    if paths.is_empty() {
        return Ok(());
    }
    bail!(
        "staged tree contains transient worktree paths:\n{}",
        paths
            .iter()
            .map(|path| format!("  - {path}"))
            .collect::<Vec<_>>()
            .join("\n")
    )
}

fn git_lines(repo_root: &Path, args: &[&str]) -> Result<Vec<String>> {
    Ok(git_stdout(repo_root, args)?
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(ToOwned::to_owned)
        .collect())
}

fn staged_text(repo_root: &Path, path: &Path) -> Result<Option<String>> {
    let spec = format!(":{}", path.display());
    let output = ProcessCommand::new("git")
        .args(["show", &spec])
        .current_dir(repo_root)
        .output()
        .with_context(|| format!("read staged content for {}", path.display()))?;
    if !output.status.success() {
        return Ok(None);
    }
    Ok(Some(String::from_utf8_lossy(&output.stdout).into_owned()))
}

fn path_contains_kani_proof(repo_root: &Path, path: &Path) -> Result<bool> {
    if let Some(text) = staged_text(repo_root, path)? {
        return Ok(text.contains("kani::proof"));
    }
    let full_path = repo_root.join(path);
    if !full_path.is_file() {
        return Ok(false);
    }
    Ok(fs::read_to_string(&full_path)
        .with_context(|| format!("read {}", full_path.display()))?
        .contains("kani::proof"))
}

fn dir_contains_kani_proof(repo_root: &Path, path: &Path) -> Result<bool> {
    let full_path = repo_root.join(path);
    if !full_path.is_dir() {
        return Ok(false);
    }
    dir_contains_text(&full_path, "kani::proof")
}

fn dir_contains_text(dir: &Path, needle: &str) -> Result<bool> {
    for entry in fs::read_dir(dir).with_context(|| format!("scan {}", dir.display()))? {
        let entry = entry.with_context(|| format!("read entry under {}", dir.display()))?;
        let path = entry.path();
        if path.is_dir() {
            if dir_contains_text(&path, needle)? {
                return Ok(true);
            }
        } else if path.is_file()
            && fs::read_to_string(&path)
                .with_context(|| format!("read {}", path.display()))?
                .contains(needle)
        {
            return Ok(true);
        }
    }
    Ok(false)
}

fn has_bare_todo_comment(line: &str) -> bool {
    let trimmed = line.trim_start();
    let Some(comment) = trimmed.strip_prefix("//") else {
        return false;
    };
    let comment = comment.trim_start();
    let Some(rest) = comment.strip_prefix("TODO") else {
        return false;
    };
    if rest
        .chars()
        .next()
        .is_some_and(|ch| ch.is_ascii_alphanumeric() || ch == '_')
    {
        return false;
    }
    !todo_has_issue_ref(rest)
}

fn todo_has_issue_ref(rest: &str) -> bool {
    let Some(rest) = rest.strip_prefix("(#") else {
        return false;
    };
    let Some((digits, _suffix)) = rest.split_once(')') else {
        return false;
    };
    !digits.is_empty() && digits.chars().all(|ch| ch.is_ascii_digit())
}

const SMT_SAT_SMOKE: &str = r#"
(set-logic QF_LRA)
(declare-fun x () Real)
(assert (and (> x 0) (< x 10)))
(check-sat)
"#;

const SMT_UNSAT_SMOKE: &str = r#"
(set-logic QF_LRA)
(declare-fun x () Real)
(assert (and (> x 5) (< x 3)))
(check-sat)
"#;

const CHC_SAFE_SMOKE: &str = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (inv x) (inv (+ x 1)))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))
(check-sat)
"#;

struct CapturedCommand {
    success: bool,
    stdout: String,
    stderr: String,
    timed_out: bool,
}

impl CapturedCommand {
    fn combined_output(&self) -> String {
        format!("{}{}", self.stdout, self.stderr)
    }
}

fn capture_command(
    repo_root: &Path,
    program: &Path,
    args: &[&str],
    timeout: Duration,
) -> Result<CapturedCommand> {
    let mut child = ProcessCommand::new(program)
        .args(args)
        .current_dir(repo_root)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .with_context(|| format!("spawn {}", render_path_command(program, args)))?;
    match child
        .wait_timeout(timeout)
        .with_context(|| format!("wait for {}", render_path_command(program, args)))?
    {
        Some(_) => {
            let output = child
                .wait_with_output()
                .with_context(|| format!("collect {}", render_path_command(program, args)))?;
            Ok(CapturedCommand {
                success: output.status.success(),
                stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
                stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
                timed_out: false,
            })
        }
        None => {
            let _ = child.kill();
            let output = child.wait_with_output().with_context(|| {
                format!("collect timed-out {}", render_path_command(program, args))
            })?;
            Ok(CapturedCommand {
                success: false,
                stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
                stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
                timed_out: true,
            })
        }
    }
}

fn render_path_command(program: &Path, args: &[&str]) -> String {
    let mut parts = vec![program.display().to_string()];
    parts.extend(args.iter().map(|arg| (*arg).to_string()));
    parts.join(" ")
}

fn check_git_rebase_state(repo_root: &Path) -> Result<HealthResult> {
    let git_dir = match git_stdout(
        repo_root,
        &["rev-parse", "--path-format=absolute", "--git-dir"],
    ) {
        Ok(path) if !path.is_empty() => PathBuf::from(path),
        Ok(_) => {
            return Ok(HealthResult::fail(
                "git rebase state: empty git metadata path",
            ))
        }
        Err(error) => {
            return Ok(HealthResult::fail(format!(
                "git rebase state: unable to resolve git metadata ({error:#})"
            )))
        }
    };
    let active: Vec<_> = ["rebase-merge", "rebase-apply"]
        .into_iter()
        .map(|name| git_dir.join(name))
        .filter(|path| path.exists())
        .collect();
    if active.is_empty() {
        return Ok(HealthResult::pass("git rebase state: clean"));
    }
    let active = active
        .iter()
        .map(|path| display_path_for_gate(repo_root, path))
        .collect::<Vec<_>>()
        .join(", ");
    Ok(HealthResult::fail(format!(
        "git rebase in progress ({active}); resolve with `git rebase --continue` or `git rebase --abort`"
    )))
}

fn check_submodule_metadata(repo_root: &Path) -> Result<HealthResult> {
    let tree = match git_stdout(repo_root, &["ls-tree", "-r", "--full-tree", "HEAD"]) {
        Ok(tree) => tree,
        Err(error) => {
            return Ok(HealthResult::fail(format!(
                "git submodule metadata: unable to list git tree ({error:#})"
            )))
        }
    };
    let gitlinks: Vec<String> = tree
        .lines()
        .filter_map(|line| {
            line.strip_prefix("160000 commit ")
                .and_then(|rest| rest.split_once('\t'))
                .map(|(_, path)| path.trim().to_string())
        })
        .collect();
    if gitlinks.is_empty() {
        return Ok(HealthResult::pass(
            "git submodule metadata: no tracked gitlinks",
        ));
    }

    let gitmodules = repo_root.join(".gitmodules");
    if !gitmodules.is_file() {
        return Ok(HealthResult::fail(
            "git submodule metadata: tracked gitlinks present but .gitmodules is missing",
        ));
    }

    let config = capture_command(
        repo_root,
        Path::new("git"),
        &[
            "config",
            "--file",
            ".gitmodules",
            "--get-regexp",
            r"^submodule\..*\.(path|url)$",
        ],
        Duration::from_secs(10),
    )?;
    if !config.success {
        return Ok(HealthResult::fail(format!(
            "git submodule metadata: failed to parse .gitmodules ({})",
            first_output_line(&config.combined_output())
        )));
    }

    #[derive(Default)]
    struct ModuleEntry {
        path: Option<String>,
        url: Option<String>,
    }

    let mut by_section: BTreeMap<String, ModuleEntry> = BTreeMap::new();
    for line in config.stdout.lines() {
        let Some((key, value)) = line.split_once(' ') else {
            continue;
        };
        let Some((section, field)) = key.rsplit_once('.') else {
            continue;
        };
        let entry = by_section.entry(section.to_string()).or_default();
        match field {
            "path" => entry.path = Some(value.trim().to_string()),
            "url" => entry.url = Some(value.trim().to_string()),
            _ => {}
        }
    }

    let mut path_to_url = BTreeMap::new();
    for entry in by_section.values() {
        if let Some(path) = &entry.path {
            path_to_url.insert(path.clone(), entry.url.clone().unwrap_or_default());
        }
    }

    let missing_path: Vec<_> = gitlinks
        .iter()
        .filter(|path| !path_to_url.contains_key(*path))
        .cloned()
        .collect();
    let missing_url: Vec<_> = gitlinks
        .iter()
        .filter(|path| path_to_url.get(*path).is_some_and(|url| url.is_empty()))
        .cloned()
        .collect();
    if missing_path.is_empty() && missing_url.is_empty() {
        return Ok(HealthResult::pass(format!(
            "git submodule metadata: {} tracked gitlink(s) mapped",
            gitlinks.len()
        )));
    }

    let mut details = Vec::new();
    if !missing_path.is_empty() {
        details.push(format!("missing path entry: {}", missing_path.join(", ")));
    }
    if !missing_url.is_empty() {
        details.push(format!("missing url: {}", missing_url.join(", ")));
    }
    Ok(HealthResult::fail(format!(
        "git submodule metadata: {}",
        details.join("; ")
    )))
}

fn check_reports_directory(repo_root: &Path) -> Result<HealthResult> {
    let reports_dir = repo_root.join("reports");
    if !reports_dir.exists() {
        return Ok(HealthResult::pass("reports directory: not present"));
    }
    if !reports_dir.is_dir() {
        return Ok(HealthResult::warn(format!(
            "reports directory: expected directory at {}",
            display_path_for_gate(repo_root, &reports_dir)
        )));
    }

    let mut total_files = 0usize;
    let mut top_level_files = 0usize;
    let mut by_subdir: BTreeMap<String, usize> = BTreeMap::new();
    collect_report_counts(
        &reports_dir,
        &reports_dir,
        &mut total_files,
        &mut top_level_files,
        &mut by_subdir,
    )?;
    let warn_threshold = env::var("REPORTS_MAX_FILE_COUNT")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .filter(|value| *value > 0)
        .unwrap_or(2500);
    if total_files <= warn_threshold {
        return Ok(HealthResult::pass(format!(
            "reports directory: {total_files} files (threshold={warn_threshold})"
        )));
    }

    let mut busiest = by_subdir.into_iter().collect::<Vec<_>>();
    busiest.sort_by(|left, right| right.1.cmp(&left.1).then_with(|| left.0.cmp(&right.0)));
    let busiest_summary = busiest
        .iter()
        .take(3)
        .map(|(name, count)| format!("{name}={count}"))
        .collect::<Vec<_>>()
        .join(", ");
    let top_subdirs = if busiest_summary.is_empty() {
        String::new()
    } else {
        format!(", top subdirs: {busiest_summary}")
    };
    Ok(HealthResult::warn(format!(
        "reports directory bloat: {total_files} files > threshold {warn_threshold} (top-level={top_level_files}{top_subdirs}). Review old report files and delete stale artifacts after confirming they are no longer needed."
    )))
}

fn collect_report_counts(
    root: &Path,
    dir: &Path,
    total_files: &mut usize,
    top_level_files: &mut usize,
    by_subdir: &mut BTreeMap<String, usize>,
) -> Result<()> {
    for entry in fs::read_dir(dir).with_context(|| format!("scan {}", dir.display()))? {
        let entry = entry.with_context(|| format!("read entry under {}", dir.display()))?;
        let path = entry.path();
        if path.is_dir() {
            collect_report_counts(root, &path, total_files, top_level_files, by_subdir)?;
        } else if path.is_file() {
            *total_files += 1;
            let rel = path.strip_prefix(root).unwrap_or(&path);
            if rel.components().count() == 1 {
                *top_level_files += 1;
            } else if let Some(first) = rel.components().next() {
                let key = first.as_os_str().to_string_lossy().to_string();
                *by_subdir.entry(key).or_default() += 1;
            }
        }
    }
    Ok(())
}

fn check_cargo_build_health(repo_root: &Path, allow_build: bool) -> Result<HealthResult> {
    if let Some(result) = maybe_reuse_fresh_release_binary(repo_root)? {
        return Ok(result);
    }

    let release_bin = find_release_binary(repo_root);
    let release_mtime_before = release_bin
        .as_deref()
        .and_then(|path| modified_nanos(path).ok());
    if !allow_build {
        if let Some(ay_bin) = find_ay_binary(repo_root) {
            return Ok(HealthResult::warn(format!(
                "cargo build -p ay --release: SKIPPED ({})",
                format_reused_binary_message(repo_root, &ay_bin)?
            )));
        }
        return Ok(HealthResult::fail(
            "cargo build -p ay --release: SKIPPED and ay binary not found",
        ));
    }

    let output = capture_command(
        repo_root,
        Path::new("cargo"),
        &["build", "-p", "ay", "--release"],
        Duration::from_secs(40),
    )?;
    handle_cargo_build_result(repo_root, &output, release_mtime_before)
}

fn handle_cargo_build_result(
    repo_root: &Path,
    output: &CapturedCommand,
    release_mtime_before: Option<u128>,
) -> Result<HealthResult> {
    let release_bin = find_release_binary(repo_root);
    if output.success {
        let Some(release_bin) = release_bin else {
            return Ok(HealthResult::fail(
                "cargo build succeeded but no release ay binary was found",
            ));
        };
        let release_mtime_after = modified_nanos(&release_bin).ok();
        if release_mtime_before.is_none() || release_mtime_after > release_mtime_before {
            return Ok(HealthResult::pass(format!(
                "cargo build -p ay --release: OK (freshly built {})",
                format_binary_identity(repo_root, &release_bin)?
            )));
        }
        let (fresh, detail) = describe_binary_freshness(repo_root, &release_bin)?;
        if fresh {
            return Ok(HealthResult::pass(format!(
                "cargo build -p ay --release: OK (reused fresh {}; {detail})",
                format_binary_identity(repo_root, &release_bin)?
            )));
        }
        return Ok(HealthResult::warn(format!(
            "cargo build -p ay --release: OK (reusing stale {}; {detail})",
            format_binary_identity(repo_root, &release_bin)?
        )));
    }

    if output.timed_out {
        if let Some(ay_bin) = find_ay_binary(repo_root) {
            return Ok(HealthResult::warn(format!(
                "cargo build -p ay --release: TIMED OUT ({})",
                format_reused_binary_message(repo_root, &ay_bin)?
            )));
        }
        return Ok(HealthResult::fail(
            "cargo build -p ay --release: TIMED OUT and ay binary not found",
        ));
    }

    Ok(HealthResult::fail(format!(
        "cargo build -p ay --release: FAILED\n{}",
        truncate_output(&output.combined_output(), 500)
    )))
}

fn maybe_reuse_fresh_release_binary(repo_root: &Path) -> Result<Option<HealthResult>> {
    let Some(release_bin) = find_release_binary(repo_root) else {
        return Ok(None);
    };
    let (fresh, detail) = describe_binary_freshness(repo_root, &release_bin)?;
    if !fresh {
        return Ok(None);
    }
    Ok(Some(HealthResult::pass(format!(
        "cargo build -p ay --release: OK (reused fresh {}; {detail})",
        format_binary_identity(repo_root, &release_bin)?
    ))))
}

fn check_smt_smoke(
    repo_root: &Path,
    label: &str,
    expected: &str,
    input: &str,
    extra_args: &[&str],
) -> Result<HealthResult> {
    let Some(ay_bin) = find_ay_binary(repo_root) else {
        return Ok(HealthResult::fail(format!(
            "SMT {label} test: FAILED (ay binary not found)"
        )));
    };
    let smoke_dir = repo_root.join("target").join("ay-health");
    fs::create_dir_all(&smoke_dir)
        .with_context(|| format!("create health smoke dir {}", smoke_dir.display()))?;
    let input_path = smoke_dir.join(format!(
        "smoke-{}-{}.smt2",
        label.to_ascii_lowercase(),
        std::process::id()
    ));
    fs::write(&input_path, input)
        .with_context(|| format!("write health smoke input {}", input_path.display()))?;

    let mut args = extra_args.to_vec();
    let input_arg = input_path.to_string_lossy().to_string();
    args.push(&input_arg);
    let output = capture_command(repo_root, &ay_bin, &args, Duration::from_secs(30));
    let _ = fs::remove_file(&input_path);
    let output = output?;
    let combined = output.combined_output();
    let result = extract_result_token(&combined);
    if output.success && result.as_deref() == Some(expected) {
        return Ok(HealthResult::pass(format!("SMT {label} test: OK")));
    }
    if label == "SAFE" && output.success && result.as_deref() == Some("sat") {
        return Ok(HealthResult::pass("CHC SAFE test: OK"));
    }
    if label == "SAFE" && result.as_deref() == Some("unknown") {
        return Ok(HealthResult::warn("CHC SAFE test: WARN (unknown)"));
    }
    let got = result.as_deref().unwrap_or("<missing>");
    Ok(HealthResult::fail(format!(
        "SMT {label} test: FAILED (expected '{expected}', got {got})\n{}",
        truncate_output(&combined, 200)
    )))
}

fn find_release_binary(repo_root: &Path) -> Option<PathBuf> {
    select_newest_binary(vec![
        repo_root.join("target/user/release/ay"),
        repo_root.join("target/release/ay"),
    ])
}

fn find_debug_binary(repo_root: &Path) -> Option<PathBuf> {
    select_newest_binary(vec![
        repo_root.join("target/user/debug/ay"),
        repo_root.join("target/debug/ay"),
    ])
}

fn find_ay_binary(repo_root: &Path) -> Option<PathBuf> {
    find_release_binary(repo_root).or_else(|| find_debug_binary(repo_root))
}

fn select_newest_binary(candidates: Vec<PathBuf>) -> Option<PathBuf> {
    candidates
        .into_iter()
        .filter(|path| is_executable_file(path))
        .max_by_key(|path| modified_nanos(path).unwrap_or(0))
}

fn format_binary_identity(repo_root: &Path, ay_bin: &Path) -> Result<String> {
    let version = probe_binary_version(repo_root, ay_bin)?;
    Ok(format!(
        "{} [{version}]",
        display_path_for_gate(repo_root, ay_bin)
    ))
}

fn probe_binary_version(repo_root: &Path, ay_bin: &Path) -> Result<String> {
    let output = capture_command(repo_root, ay_bin, &["--version"], Duration::from_secs(5))?;
    if output.success {
        if let Some(line) = output
            .combined_output()
            .lines()
            .find(|line| !line.trim().is_empty())
        {
            return Ok(line.trim().to_string());
        }
    }
    Ok("version unavailable".to_string())
}

fn format_reused_binary_message(repo_root: &Path, ay_bin: &Path) -> Result<String> {
    let (fresh, detail) = describe_binary_freshness(repo_root, ay_bin)?;
    let freshness = if fresh { "fresh" } else { "stale" };
    Ok(format!(
        "reusing {freshness} {}; {detail}",
        format_binary_identity(repo_root, ay_bin)?
    ))
}

fn describe_binary_freshness(repo_root: &Path, ay_bin: &Path) -> Result<(bool, String)> {
    let binary_mtime =
        modified_nanos(ay_bin).with_context(|| format!("stat binary {}", ay_bin.display()))?;
    let mut newest_input: Option<PathBuf> = None;
    let mut newest_input_mtime = 0u128;
    for path in iter_release_build_inputs(repo_root)? {
        let Ok(input_mtime) = modified_nanos(&path) else {
            continue;
        };
        if input_mtime > newest_input_mtime {
            newest_input = Some(path);
            newest_input_mtime = input_mtime;
        }
    }
    let Some(newest_input) = newest_input else {
        return Ok((true, "no release build inputs found".to_string()));
    };
    let detail = if binary_mtime >= newest_input_mtime {
        format!(
            "newest source {}",
            display_path_for_gate(repo_root, &newest_input)
        )
    } else {
        format!(
            "newer source {}",
            display_path_for_gate(repo_root, &newest_input)
        )
    };
    Ok((binary_mtime >= newest_input_mtime, detail))
}

fn iter_release_build_inputs(repo_root: &Path) -> Result<Vec<PathBuf>> {
    let mut inputs = Vec::new();
    for relative in ["Cargo.toml", "Cargo.lock"] {
        let path = repo_root.join(relative);
        if path.is_file() {
            inputs.push(path);
        }
    }
    for root_name in ["build_support", "crates", "src"] {
        let root = repo_root.join(root_name);
        if root.exists() {
            collect_release_build_inputs(repo_root, &root, &mut inputs)?;
        }
    }
    Ok(inputs)
}

fn collect_release_build_inputs(
    repo_root: &Path,
    dir: &Path,
    inputs: &mut Vec<PathBuf>,
) -> Result<()> {
    for entry in fs::read_dir(dir).with_context(|| format!("scan {}", dir.display()))? {
        let entry = entry.with_context(|| format!("read entry under {}", dir.display()))?;
        let path = entry.path();
        if path.is_dir() {
            collect_release_build_inputs(repo_root, &path, inputs)?;
        } else if should_track_release_input(repo_root, &path) {
            inputs.push(path);
        }
    }
    Ok(())
}

fn should_track_release_input(repo_root: &Path, path: &Path) -> bool {
    if !path.is_file() {
        return false;
    }
    let rel = path.strip_prefix(repo_root).unwrap_or(path);
    if rel.components().any(|part| {
        let part = part.as_os_str();
        part == "tests" || part == "benches" || part == "examples"
    }) {
        return false;
    }
    if path.extension().is_some_and(|extension| extension == "rs") {
        let name = path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("");
        return !(name == "tests.rs"
            || name == "test_helpers.rs"
            || name.starts_with("test_")
            || name.ends_with("_test.rs")
            || name.ends_with("_tests.rs"));
    }
    path.file_name().is_some_and(|name| name == "Cargo.toml")
}

fn modified_nanos(path: &Path) -> Result<u128> {
    let modified = fs::metadata(path)
        .with_context(|| format!("stat {}", path.display()))?
        .modified()
        .with_context(|| format!("read mtime for {}", path.display()))?;
    Ok(modified
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos())
}

fn extract_result_token(output: &str) -> Option<String> {
    output
        .lines()
        .map(|line| line.trim().to_ascii_lowercase())
        .find(|token| {
            matches!(
                token.as_str(),
                "sat" | "unsat" | "unknown" | "safe" | "unsafe"
            )
        })
}

fn first_output_line(output: &str) -> String {
    output
        .lines()
        .find(|line| !line.trim().is_empty())
        .map(|line| line.trim().to_string())
        .unwrap_or_else(|| "<no output>".to_string())
}

fn truncate_output(output: &str, limit: usize) -> String {
    output.chars().take(limit).collect()
}

fn display_path_for_gate(repo_root: &Path, path: &Path) -> String {
    path.strip_prefix(repo_root)
        .unwrap_or(path)
        .display()
        .to_string()
}

fn resolve_repo_root(repo_root: Option<&Path>) -> Result<PathBuf> {
    let raw = match repo_root {
        Some(path) => path.to_path_buf(),
        None => {
            let output = ProcessCommand::new("git")
                .args(["rev-parse", "--show-toplevel"])
                .output()
                .context("run git rev-parse --show-toplevel")?;
            if output.status.success() {
                PathBuf::from(String::from_utf8_lossy(&output.stdout).trim())
            } else {
                env::current_dir().context("resolve current directory")?
            }
        }
    };
    if !raw.is_dir() {
        bail!("repo root does not exist: {}", raw.display());
    }
    fs::canonicalize(&raw).with_context(|| format!("canonicalize repo root {}", raw.display()))
}

fn resolve_critical_range(
    repo_root: &Path,
    arg_value: Option<&str>,
    env_name: &str,
) -> Result<String> {
    if let Some(value) = arg_value.filter(|value| !value.trim().is_empty()) {
        return Ok(value.to_string());
    }
    if let Ok(value) = env::var(env_name) {
        if !value.trim().is_empty() {
            return Ok(value);
        }
    }
    determine_critical_solver_range(repo_root)
}

// `@{upstream}` is git revision syntax, not a Rust formatting placeholder.
#[allow(clippy::literal_string_with_formatting_args)]
fn determine_critical_solver_range(repo_root: &Path) -> Result<String> {
    if let Ok(upstream) = git_stdout(
        repo_root,
        &[
            "rev-parse",
            "--abbrev-ref",
            "--symbolic-full-name",
            "@{upstream}",
        ],
    ) {
        if !upstream.is_empty() {
            if let Ok(ahead) = git_stdout(
                repo_root,
                &["rev-list", "--count", &format!("{upstream}..HEAD")],
            ) {
                if ahead.parse::<u64>().unwrap_or(0) > 0 {
                    return Ok(format!("{upstream}..HEAD"));
                }
            }
        }
    }
    if git_status(repo_root, &["rev-parse", "--verify", "HEAD~1"]) {
        Ok("HEAD~1..HEAD".to_string())
    } else {
        Ok("HEAD".to_string())
    }
}

fn git_stdout(repo_root: &Path, args: &[&str]) -> Result<String> {
    let output = ProcessCommand::new("git")
        .args(args)
        .current_dir(repo_root)
        .output()
        .with_context(|| format!("run git {}", args.join(" ")))?;
    if !output.status.success() {
        bail!(
            "git {} failed: {}",
            args.join(" "),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

fn git_status(repo_root: &Path, args: &[&str]) -> bool {
    ProcessCommand::new("git")
        .args(args)
        .current_dir(repo_root)
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|status| status.success())
}

fn run_native_step<F>(prefix: &str, name: &str, action: F) -> Result<()>
where
    F: FnOnce() -> Result<()>,
{
    println!("[{prefix}] START {name}");
    action().with_context(|| format!("{prefix} native step failed: {name}"))?;
    println!("[{prefix}] DONE  {name}");
    Ok(())
}

fn run_external_step(prefix: &str, repo_root: &Path, step: &ExternalStep) -> Result<()> {
    println!("[{prefix}] START {}", step.name);
    println!("[{prefix}] command: {}", step.rendered());
    let mut command = ProcessCommand::new(step.program);
    command.args(&step.args).current_dir(repo_root);
    for (key, value) in &step.env {
        command.env(key, value);
    }
    let status = command
        .status()
        .with_context(|| format!("spawn {}", step.rendered()))?;
    if !status.success() {
        bail!("{} failed with status {status}", step.name);
    }
    println!("[{prefix}] DONE  {}", step.name);
    Ok(())
}

fn print_steps(prefix: &str, external: &[ExternalStep], native: &[&str]) {
    println!("[{prefix}] steps");
    for name in native {
        println!("{name}\t<native>");
    }
    for step in external {
        println!("{}\t{}", step.name, step.rendered());
    }
}

const CRITICAL_SOLVER_POLICY_NAME: &str = "critical-solver-policy-gate";
const CRITICAL_SOLVER_POLICY_PATH: &str = "scripts/check_critical_solver_policy.sh";

fn check_local_solver_gate_entrypoint(repo_root: &Path) -> Result<()> {
    let policy_script = repo_root.join(CRITICAL_SOLVER_POLICY_PATH);
    let script_text = fs::read_to_string(&policy_script)
        .with_context(|| format!("read local solver policy {}", policy_script.display()))?;
    require_contains(
        &script_text,
        &format!("# ay-script: {CRITICAL_SOLVER_POLICY_NAME}"),
        "local solver policy must declare its indexed script identity",
    )?;

    let index_path = repo_root.join("scripts/index.toml");
    let index_text = fs::read_to_string(&index_path)
        .with_context(|| format!("read script index {}", index_path.display()))?;
    let index: toml::Value = toml::from_str(&index_text)
        .with_context(|| format!("parse script index {}", index_path.display()))?;
    let entries = index
        .get("script")
        .and_then(toml::Value::as_array)
        .with_context(|| {
            format!(
                "script index {} has no script entries",
                index_path.display()
            )
        })?;
    let entry = entries
        .iter()
        .find(|entry| {
            entry
                .get("name")
                .and_then(toml::Value::as_str)
                .is_some_and(|name| name == CRITICAL_SOLVER_POLICY_NAME)
        })
        .with_context(|| {
            format!(
                "script index {} does not register {CRITICAL_SOLVER_POLICY_NAME}",
                index_path.display()
            )
        })?;

    let indexed_path = entry
        .get("path")
        .and_then(toml::Value::as_str)
        .context("critical solver policy index entry has no path")?;
    if indexed_path != CRITICAL_SOLVER_POLICY_PATH {
        bail!(
            "critical solver policy index path must be {CRITICAL_SOLVER_POLICY_PATH}, found {indexed_path}"
        );
    }
    let indexed_cli = entry
        .get("cli")
        .and_then(toml::Value::as_str)
        .context("critical solver policy index entry has no fronting CLI")?;
    if indexed_cli != "ay gate" {
        bail!("critical solver policy must be fronted by `ay gate`, found {indexed_cli}");
    }
    Ok(())
}

fn require_contains(text: &str, needle: &str, message: &str) -> Result<()> {
    if text.contains(needle) {
        Ok(())
    } else {
        bail!("{message}")
    }
}

fn render_command<S: AsRef<str>>(
    program: &str,
    args: &[S],
    envs: &[(&str, impl AsRef<str>)],
) -> String {
    let mut parts = Vec::new();
    for (key, value) in envs {
        parts.push(format!("{key}={}", shell_quote(value.as_ref())));
    }
    parts.push(shell_quote(program));
    parts.extend(args.iter().map(|arg| shell_quote(arg.as_ref())));
    parts.join(" ")
}

fn shell_quote(arg: &str) -> String {
    if !arg.is_empty()
        && arg
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || b"@%_+=:,./-".contains(&byte))
    {
        arg.to_string()
    } else {
        format!("'{}'", arg.replace('\'', "'\\''"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    fn write_local_solver_gate_fixture(index_entry: &str) -> TempDir {
        let repo = TempDir::new().expect("temporary repository");
        let scripts = repo.path().join("scripts");
        fs::create_dir(&scripts).expect("create scripts directory");
        fs::write(
            scripts.join("check_critical_solver_policy.sh"),
            "#!/usr/bin/env bash\n# ay-script: critical-solver-policy-gate\n",
        )
        .expect("write local solver policy");
        fs::write(
            scripts.join("index.toml"),
            format!("schema_version = 1\n\n{index_entry}\n"),
        )
        .expect("write script index");
        repo
    }

    fn cargo_args_before_separator(step: &ExternalStep) -> &[String] {
        assert_eq!(step.program, "cargo", "unexpected step: {}", step.name);
        let separator = step
            .args
            .iter()
            .position(|arg| arg == "--")
            .unwrap_or_else(|| panic!("Cargo step has no argument separator: {}", step.rendered()));
        &step.args[..separator]
    }

    fn cargo_option_value<'a>(args: &'a [String], short: &str, long: &str) -> Option<&'a str> {
        args.windows(2)
            .find(|pair| pair[0] == short || pair[0] == long)
            .map(|pair| pair[1].as_str())
    }

    const EXPECTED_SOLVER_GATE_STEP_NAMES: [&str; 20] = [
        "code_quality",
        "debug_ay_build_version_stamp",
        "debug_ay_cli_external_codegen_consumer_canaries",
        "debug_ay_smtlib_conformance_summary",
        "debug_ay_dpll_external_codegen_consumer_differential",
        "debug_ay_dpll_external_codegen_fp_canary",
        "debug_ay_sat_integration_basic",
        "debug_ay_dpll_qf_lia_packet",
        "debug_ay_dpll_qf_lra_packet",
        "debug_ay_dpll_qf_uf_packet",
        "debug_ay_dpll_qf_bv_packet",
        "debug_ay_dpll_qf_abv_packet",
        "debug_ay_dpll_qf_ax_packet",
        "release_ay_sat_soundness_regressions",
        "release_only_ay_dpll_lra_regressions",
        "release_ay_chc_dillig12_m_deadline_guard",
        "debug_ay_lra_release_fixture_integrity",
        "release_ay_lra_cli_mechanism_regressions",
        "release_ay_lra_cli_hermetic_sweep",
        "release_ay_dpll_qf_bv_differential_strict",
    ];

    const PINNED_LRA_STEPS: [(&str, &[&str]); 4] = [
        (
            "release_only_ay_dpll_lra_regressions",
            &[
                "test",
                "--locked",
                "-p",
                "ay-dpll",
                "--release",
                "--test",
                "group_lra",
                "qf_lra_release_soundness_",
                "--",
                "--nocapture",
            ],
        ),
        (
            "debug_ay_lra_release_fixture_integrity",
            &[
                "test",
                "--locked",
                "-p",
                "ay",
                "--features",
                "cli",
                "--test",
                "group_lra",
                "qf_lra_release_fixture_integrity::qf_lra_release_fixtures_exist_and_match_pinned_bytes",
                "--",
                "--exact",
                "--nocapture",
            ],
        ),
        (
            "release_ay_lra_cli_mechanism_regressions",
            &[
                "test",
                "--locked",
                "-p",
                "ay",
                "--features",
                "cli",
                "--release",
                "--test",
                "group_lra",
                "qf_lra_cli_release_mechanism_",
                "--",
                "--nocapture",
            ],
        ),
        (
            "release_ay_lra_cli_hermetic_sweep",
            &[
                "test",
                "--locked",
                "-p",
                "ay",
                "--features",
                "cli",
                "--release",
                "--test",
                "group_lra",
                "qf_lra_cli_release_sweep_6564::qf_lra_cli_release_soundness_selected_batch_6564",
                "--",
                "--exact",
                "--nocapture",
            ],
        ),
    ];

    const QF_ABV_PACKET_ARGS: [&str; 9] = [
        "test",
        "--locked",
        "-p",
        "ay-dpll",
        "--test",
        "group_theory_misc",
        "smt_soundness_gate::abv::",
        "--",
        "--nocapture",
    ];

    fn assert_step_args(steps: &[ExternalStep], name: &str, expected_args: &[&str]) {
        let step = steps
            .iter()
            .find(|step| step.name == name)
            .unwrap_or_else(|| panic!("solver gate must include {name}"));
        assert_eq!(step.program, "cargo");
        assert_eq!(
            step.args.iter().map(String::as_str).collect::<Vec<_>>(),
            expected_args,
            "solver gate step {name} changed"
        );
    }

    #[test]
    fn local_solver_gate_entrypoint_accepts_indexed_policy_without_workflow() {
        let repo = write_local_solver_gate_fixture(
            r#"[[script]]
name = "critical-solver-policy-gate"
path = "scripts/check_critical_solver_policy.sh"
cli = "ay gate""#,
        );

        assert!(
            !repo.path().join(".github").exists(),
            "fixture must not acquire a hosted workflow"
        );
        check_local_solver_gate_entrypoint(repo.path())
            .expect("indexed local policy should satisfy solver gate wiring");
    }

    #[test]
    fn local_solver_gate_entrypoint_rejects_misindexed_policy_path() {
        let repo = write_local_solver_gate_fixture(
            r#"[[script]]
name = "critical-solver-policy-gate"
path = "scripts/ci/not-the-policy.sh"
cli = "ay gate""#,
        );

        let error = check_local_solver_gate_entrypoint(repo.path())
            .expect_err("misindexed local policy must fail closed");
        assert!(
            format!("{error:#}").contains(
                "critical solver policy index path must be scripts/check_critical_solver_policy.sh"
            ),
            "unexpected wiring error: {error:#}"
        );
    }

    #[test]
    fn solver_gate_cargo_step_order_and_quality_entry_are_stable() {
        let steps = solver_gate_cargo_steps();
        assert_eq!(
            steps.iter().map(|step| step.name).collect::<Vec<_>>(),
            EXPECTED_SOLVER_GATE_STEP_NAMES,
            "solver gate step order changed"
        );
        assert!(
            steps.iter().any(|step| {
                step.name == "code_quality"
                    && step.program == "cargo"
                    && step
                        .args
                        .windows(2)
                        .any(|args| args[0] == "-p" && args[1] == "ay-quality-gate")
            }),
            "solver gate must enforce the in-tree code-quality ratchets"
        );
    }

    #[test]
    fn solver_gate_lra_step_arguments_are_stable() {
        let steps = solver_gate_cargo_steps();
        for (name, expected_args) in PINNED_LRA_STEPS {
            assert_step_args(&steps, name, expected_args);
        }
    }

    #[test]
    fn solver_gate_qf_abv_packet_arguments_are_stable() {
        assert_step_args(
            &solver_gate_cargo_steps(),
            "debug_ay_dpll_qf_abv_packet",
            &QF_ABV_PACKET_ARGS,
        );
    }

    #[test]
    fn solver_gate_environment_overrides_are_stable() {
        let steps = solver_gate_cargo_steps();
        for step in &steps {
            let expected = match step.name {
                "release_ay_lra_cli_hermetic_sweep" => {
                    vec![("AY_QF_LRA_RELEASE_FULL_SWEEP", "0".to_string())]
                }
                "release_ay_dpll_qf_bv_differential_strict" => {
                    vec![("Z3_DIFFERENTIAL_REQUIRED", "1".to_string())]
                }
                _ => Vec::new(),
            };
            assert_eq!(step.env, expected, "solver gate env changed: {}", step.name);
        }
    }

    #[test]
    fn solver_gate_cargo_steps_are_locked_and_cli_enabled() {
        let steps = solver_gate_cargo_steps();
        assert_eq!(
            steps.len(),
            EXPECTED_SOLVER_GATE_STEP_NAMES.len(),
            "solver gate cargo step count changed"
        );
        for step in &steps {
            let cargo_args = cargo_args_before_separator(step);
            let package = cargo_option_value(cargo_args, "-p", "--package")
                .unwrap_or_else(|| panic!("Cargo package is missing: {}", step.rendered()));
            let expected_subcommand = if package == "ay-quality-gate" {
                "run"
            } else {
                "test"
            };
            assert_eq!(
                cargo_args.first().map(String::as_str),
                Some(expected_subcommand),
                "solver gate Cargo subcommand must be positional: {}",
                step.rendered()
            );
            assert!(
                cargo_args.iter().any(|arg| arg == "--locked"),
                "solver gate Cargo step is not locked: {}",
                step.rendered()
            );
            if package == "ay" {
                assert_eq!(
                    cargo_option_value(cargo_args, "-F", "--features"),
                    Some("cli"),
                    "ay test step does not enable its required CLI feature: {}",
                    step.rendered()
                );
            }
        }
    }
}
