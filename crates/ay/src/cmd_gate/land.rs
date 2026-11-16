// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native landing: validate source, check composition, then push the exact tree.

use anyhow::{bail, Context, Result};
use clap::Args;
use std::path::{Path, PathBuf};

#[path = "land_plan.rs"]
mod plan;
#[path = "land_process.rs"]
mod process;
#[path = "land_scope.rs"]
mod scope;
#[cfg(test)]
#[path = "land_tests.rs"]
mod tests;
#[path = "land_tooling.rs"]
mod tooling;

use process::Runner;

const REMOTE_MAIN: &str = "refs/remotes/origin/main";

#[derive(Args)]
pub(crate) struct LandArgs {
    /// Worktree to validate and land (defaults to the current worktree).
    #[arg(long)]
    repo_root: Option<PathBuf>,
    /// Absolute native Agh executable; leaves the compiler PATH unchanged.
    /// The default uses the ordinary agh command on PATH.
    #[arg(long, value_name = "ABSOLUTE_EXECUTABLE")]
    agh: Option<PathBuf>,
    /// Validation base; must be an ancestor of origin/main.
    #[arg(long, default_value = "origin/main")]
    base: String,
    /// Validate without pushing.
    #[arg(long)]
    no_push: bool,
    /// Print the current local plan without fetching, merging or validating.
    #[arg(long)]
    plan: bool,
}

pub(super) fn run(args: LandArgs) -> Result<i32> {
    let directory = args.repo_root.unwrap_or(std::env::current_dir()?);
    let mut runner = Runner::new(directory);
    if let Some(agh) = args.agh.as_deref() {
        runner.select_agh(agh)?;
    }
    let root = runner.git(&["rev-parse", "--show-toplevel"])?;
    runner.root = PathBuf::from(root.trim());
    runner.clean()?;
    if args.plan {
        let head = runner.head()?;
        let plan = make_plan(&mut runner, &args.base)?;
        println!(
            "{}",
            serde_json::to_string_pretty(&serde_json::json!({
                "head": head, "base": args.base, "local_only": true,
                "agh_program": runner.agh_program(), "plan": plan
            }))?
        );
        return Ok(0);
    }
    // Reject ambient policy replacements rather than silently modifying the
    // caller's environment. Targo provenance and explicit resource caps pass
    // through unchanged, and build-slot bounds compiler concurrency.
    #[expect(
        clippy::unnecessary_debug_formatting,
        reason = "caller-controlled environment names retain exact quoting and escaping"
    )]
    for (name, value) in std::env::vars_os() {
        if name.to_str().is_some_and(is_policy_override) && !value.is_empty() {
            bail!("ambient policy override {name:?}; use the checked-in Trust policy");
        }
    }
    // All worktrees share this kernel-owned lease. Acquire it before fetching
    // or spending compiler admission: two cooperating landers must not make
    // each other's completed validation stale by publishing concurrently.
    // External pushes are composed and checked before any evidence is reused.
    let _publication = publication_lock(&mut runner)?;
    let mut previous = None;
    for _ in 0..5 {
        runner.clean()?;
        runner.fetch()?;
        runner.git(&["merge", "--no-edit", REMOTE_MAIN])?;
        runner.clean()?;
        let validated = runner.head()?;
        let remote = runner.git(&["rev-parse", REMOTE_MAIN])?;
        let composed = match previous.as_ref() {
            Some(seal) => runner.compose_documentation(seal, &validated)?,
            None => None,
        };
        let seal = match composed {
            Some(seal) => seal,
            None => {
                let plan = make_plan(&mut runner, &args.base)?;
                println!(
                    "{}",
                    serde_json::to_string_pretty(&serde_json::json!({
                        "head": validated, "base": args.base,
                        "agh_program": runner.agh_program(), "plan": plan
                    }))?
                );
                runner.validate(&plan.steps, &validated)?
            }
        };
        if args.no_push {
            println!("Validated {validated}; --no-push requested. No full-proof claim.");
            return Ok(0);
        }
        if runner.push_validated(&seal, &remote)? {
            println!("Landed validated {validated} on origin/main. No full-proof claim.");
            return Ok(0);
        }
        previous = Some(seal);
    }
    bail!("origin/main kept moving; stopped after five landing rounds")
}

fn publication_lock_file(runner: &mut Runner) -> Result<std::fs::File> {
    let common = runner.git(&["rev-parse", "--git-common-dir"])?;
    let directory = runner.root.join(common.trim());
    let mut options = std::fs::OpenOptions::new();
    options.read(true).write(true).create(true).truncate(false);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    options
        .open(directory.join("ay-land.lock"))
        .context("open shared repository landing lease")
}

struct PublicationLease(std::fs::File);

impl Drop for PublicationLease {
    fn drop(&mut self) {
        // A concurrent fork can temporarily inherit this open description until
        // exec closes it. Release our ownership explicitly rather than waiting
        // for those non-owning copies to close. Closing remains the crash path.
        if let Err(error) = self.0.unlock() {
            eprintln!("release repository landing lease: {error}");
        }
    }
}

fn publication_lock(runner: &mut Runner) -> Result<PublicationLease> {
    let lease = publication_lock_file(runner)?;
    eprintln!("Waiting for repository landing lease before starting compiler checks.");
    lease
        .lock()
        .context("acquire shared repository landing lease")?;
    eprintln!("Acquired repository landing lease.");
    Ok(PublicationLease(lease))
}

fn is_policy_override(name: &str) -> bool {
    let name = name.to_ascii_uppercase();
    matches!(
        name.as_str(),
        "TRUSTFLAGS"
            | "RUSTC"
            | "RUSTDOC"
            | "CARGO_BUILD_RUSTC"
            | "RUSTC_WRAPPER"
            | "RUSTC_WORKSPACE_WRAPPER"
            | "CARGO_BUILD_RUSTC_WRAPPER"
            | "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER"
            | "CARGO_ENCODED_TRUSTFLAGS"
            | "RUSTFLAGS"
            | "CARGO_ENCODED_RUSTFLAGS"
            | "CARGO_BUILD_RUSTFLAGS"
            | "RUSTDOCFLAGS"
            | "CARGO_ENCODED_RUSTDOCFLAGS"
            | "CARGO_BUILD_RUSTDOCFLAGS"
    ) || (name.starts_with("CARGO_TARGET_")
        && (name.ends_with("_RUSTFLAGS") || name.ends_with("_RUSTDOCFLAGS")))
}

fn make_plan(runner: &mut Runner, base: &str) -> Result<plan::Plan> {
    // Resolve caller input as one revision before constructing a range.
    let base = runner.git(&[
        "rev-parse",
        "--verify",
        "--end-of-options",
        &format!("{base}^{{commit}}"),
    ])?;
    if !runner.git_status(&["merge-base", "--is-ancestor", base.trim(), REMOTE_MAIN])? {
        bail!(
            "--base must be an ancestor of origin/main; it cannot hide unvalidated branch changes"
        );
    }
    let ancestor = runner.git(&["merge-base", base.trim(), "HEAD"])?;
    let range = format!("{}..HEAD", ancestor.trim());
    // No rename detection: both the old and new path must influence the plan.
    let changed = runner.git_bytes(&["diff", "--no-renames", "--name-only", "-z", &range, "--"])?;
    let paths = changed
        .split(|byte| *byte == 0)
        .filter(|s| !s.is_empty())
        .map(|s| std::str::from_utf8(s).map(PathBuf::from))
        .collect::<std::result::Result<Vec<_>, _>>()
        .context("changed path is not UTF-8")?;
    let metadata = runner.metadata()?;
    let old_lock = if paths.iter().any(|p| p == Path::new("Cargo.lock")) {
        Some(runner.git(&["show", &format!("{}:Cargo.lock", ancestor.trim())])?)
    } else {
        None
    };
    let mut scope = scope::RustScope::read(runner, ancestor.trim(), &paths)?;
    scope.retired_tooling = tooling::owned_removals(runner, ancestor.trim(), &paths, &metadata)?;
    plan::select(&runner.root, &metadata, paths, old_lock.as_deref(), &scope)
}
