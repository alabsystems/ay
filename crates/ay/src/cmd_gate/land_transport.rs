// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Private GitHub graph transport. A write without acknowledgement never permits retry.
use super::{Runner, Step};
use anyhow::{bail, Context, Result};
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::Stdio;

const TRACKING: &str = "refs/remotes/origin/main";
const FETCHED: &str = "refs/agh/fetched-main";
const REPOSITORY: &str = "alabsystems/ay";

#[derive(PartialEq, Eq)]
enum Source {
    Private,
    Local(PathBuf),
}

fn source(runner: &mut Runner) -> Result<Source> {
    // get-url expands Git's URL rewrites. Do not allow extra fetch destinations.
    let urls = runner.git(&["remote", "get-url", "--all", "origin"])?;
    let urls: Vec<_> = urls.lines().collect();
    let [url] = urls.as_slice() else {
        bail!("landing requires exactly one origin URL");
    };
    // Keep every spelling bound to the same repository. Publication rewrites
    // that identity; a developer's literal SSH alias must not escape with it.
    let (owner, _) = REPOSITORY
        .split_once('/')
        .context("landing repository must name an owner and project")?;
    let github = [
        format!("https://github.com/{REPOSITORY}.git"),
        format!("https://github.com/{REPOSITORY}"),
        format!("git@github.com:{REPOSITORY}.git"),
        format!("git@gh-{owner}:{REPOSITORY}.git"),
    ];
    if github.iter().any(|expected| expected == *url) {
        return Ok(Source::Private);
    }
    let path = runner.root.join(*url);
    if !path.is_dir() {
        bail!("landing requires this AY GitHub origin or an existing local repository");
    }
    let path = path.canonicalize()?;
    // Use this physical destination, never a separately configured push URL.
    runner.git(&[
        "-C",
        path.to_str().context("local origin is not UTF-8")?,
        "rev-parse",
        "--git-dir",
    ])?;
    Ok(Source::Local(path))
}

fn oid(value: &str) -> Result<&str> {
    let value = value.trim();
    if value.len() != 40
        || !value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        bail!("landing requires an exact SHA-1 object identity");
    }
    Ok(value)
}

fn paths(runner: &mut Runner) -> Result<()> {
    let common = runner.git(&["rev-parse", "--path-format=absolute", "--git-common-dir"])?;
    let common = Path::new(common.trim()).canonicalize()?;
    for name in [
        TRACKING,
        "logs/refs/remotes/origin/main",
        FETCHED,
        "logs/refs/agh/fetched-main",
        "packed-refs",
    ] {
        let mut path = common.clone();
        for part in name.split('/') {
            path.push(part);
            let meta = match fs::symlink_metadata(&path) {
                Ok(meta) => meta,
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
                Err(error) => return Err(error.into()),
            };
            #[cfg(unix)]
            let linked = {
                use std::os::unix::fs::MetadataExt;
                meta.is_file() && meta.nlink() != 1
            };
            #[cfg(not(unix))]
            // Never silently omit the hard-link boundary on a platform where
            // this lander has no physical link-count implementation.
            let linked = meta.is_file();
            if meta.file_type().is_symlink() || linked || !(meta.is_dir() || meta.is_file()) {
                bail!("unsafe tracking ref or reflog path: {}", path.display());
            }
        }
    }
    Ok(())
}

fn direct(runner: &mut Runner, reference: &str) -> Result<()> {
    let step = Step::new("git", &["symbolic-ref", "--quiet", reference]);
    let output = runner.command(&step)?.output()?;
    runner.result(&step, output.status)?;
    if output.status.code() != Some(1) {
        bail!("{reference} must be a direct ref");
    }
    Ok(())
}

fn read_ref(runner: &mut Runner, reference: &str) -> Result<Option<String>> {
    direct(runner, reference)?;
    let step = Step::new("git", &["rev-parse", "--verify", "--quiet", reference]);
    let output = runner.command(&step)?.output()?;
    runner.result(&step, output.status)?;
    if output.status.code() == Some(1) {
        return Ok(None);
    }
    if !output.status.success() {
        bail!("cannot read {reference}");
    }
    let text = String::from_utf8(output.stdout)?;
    let value = oid(&text)?.to_owned();
    if runner.git(&["cat-file", "-t", &value])?.trim() != "commit" {
        bail!("{reference} does not name a commit");
    }
    Ok(Some(value))
}

trait Agh {
    fn fetch(&mut self, runner: &mut Runner) -> Result<()>;
    fn push(&mut self, runner: &mut Runner, receipts: &Path, dry_run: bool) -> Result<()>;
}
struct Native;
impl Agh for Native {
    fn fetch(&mut self, runner: &mut Runner) -> Result<()> {
        let root = runner
            .root
            .to_str()
            .context("worktree path is not UTF-8")?
            .to_owned();
        let step = runner.agh_step(&["repo", "fetch-main", REPOSITORY, &root]);
        runner.execute(&step)
    }
    fn push(&mut self, runner: &mut Runner, receipts: &Path, dry_run: bool) -> Result<()> {
        let root = runner.root.to_str().context("worktree path is not UTF-8")?;
        let input = receipts.join("intent.json");
        let mut args = vec![
            "repo",
            "push",
            REPOSITORY,
            root,
            "--input",
            input.to_str().context("receipt path is not UTF-8")?,
        ];
        if dry_run {
            args.push("--dry-run");
        }
        let step = runner.agh_step(&args);
        let out = receipts.join(if dry_run { "dry-run.json" } else { "ack.json" });
        let err = receipts.join(if dry_run {
            "dry-run-error.json"
        } else {
            "error.json"
        });
        let status = runner
            .command(&step)?
            .stdout(Stdio::from(fs::File::create(out)?))
            .stderr(Stdio::from(fs::File::create(err)?))
            .status()
            .context("start native Agh push")?;
        runner.result(&step, status)?;
        if !status.success() {
            bail!("native Agh push returned {status}");
        }
        Ok(())
    }
}

pub(super) fn fetch(runner: &mut Runner) -> Result<()> {
    fetch_with(runner, &mut Native)
}
fn fetch_with(runner: &mut Runner, agh: &mut impl Agh) -> Result<()> {
    let origin = source(runner)?;
    paths(runner)?;
    let before = read_ref(runner, TRACKING)?;
    match &origin {
        Source::Local(path) => {
            runner.git(&[
                "-c",
                "protocol.allow=never",
                "-c",
                "protocol.file.allow=always",
                "fetch",
                path.to_str().context("local origin is not UTF-8")?,
                "refs/heads/main:refs/agh/fetched-main",
            ])?;
        }
        Source::Private => agh.fetch(runner)?,
    }
    let after = read_ref(runner, FETCHED)?.context("transport did not return fetched main")?;
    if let Some(before) = &before {
        if !runner.git_status(&["merge-base", "--is-ancestor", before, &after])? {
            bail!("origin/main would move backwards or sideways");
        }
    }
    if source(runner)? != origin {
        bail!("origin changed during fetch");
    }
    paths(runner)?;
    direct(runner, TRACKING)?;
    runner.git(&[
        "update-ref",
        "--no-deref",
        "-m",
        "AY Agh main refresh",
        TRACKING,
        &after,
        before
            .as_deref()
            .unwrap_or("0000000000000000000000000000000000000000"),
    ])?;
    Ok(())
}

pub(super) fn push(runner: &mut Runner, head: &str, remote: &str) -> Result<bool> {
    push_with(runner, head, remote, &mut Native)
}

fn dry_run_ref_conflict(receipts: &Path) -> bool {
    fn read(path: &Path) -> Option<String> {
        let mut text = String::new();
        fs::File::open(path)
            .ok()?
            .take(65_537)
            .read_to_string(&mut text)
            .ok()?;
        (text.len() <= 65_536).then_some(text)
    }
    let Some(output) = read(&receipts.join("dry-run.json")) else {
        return false;
    };
    let Ok(output) = serde_json::from_str::<serde_json::Value>(&output) else {
        return false;
    };
    if output["repo"].as_str() != Some(REPOSITORY)
        || output["op"].as_str() != Some("ref.update-atomic")
        || output["dry_run"].as_bool() != Some(true)
        || output["outcome"].as_str() != Some("refused")
    {
        return false;
    }
    let Some(stderr) = read(&receipts.join("dry-run-error.json")) else {
        return false;
    };
    // Agh emits its human summary before one structured error. Never infer
    // permission or side effects from that human text or an exit code alone.
    let mut errors = stderr
        .lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok());
    let Some(error) = errors.next() else {
        return false;
    };
    // Native Agh may leave the error's optional repo explicitly null. The
    // exact request and stdout receipt above already bind this dry run to our
    // repository. Missing, malformed and foreign error fields still refuse.
    let repository = match error.get("error").and_then(|error| error.get("repo")) {
        Some(serde_json::Value::Null) => true,
        Some(serde_json::Value::String(repo)) => repo == REPOSITORY,
        _ => false,
    };
    errors.next().is_none()
        && repository
        && error["error"]["kind"].as_str() == Some("conflict")
        && error["error"]["exit"].as_u64() == Some(9)
        && error["error"]["side_effect"].as_str() == Some("none")
}

fn push_with(runner: &mut Runner, head: &str, remote: &str, agh: &mut impl Agh) -> Result<bool> {
    let head = oid(head)?;
    let remote = oid(remote)?;
    runner.exact_clean(head)?;
    fetch_with(runner, agh)?;
    runner.exact_clean(head)?;
    if read_ref(runner, TRACKING)?.as_deref() != Some(remote) {
        return Ok(false);
    }
    if !runner.git_status(&["merge-base", "--is-ancestor", remote, head])? {
        bail!("validated graph is not a fast-forward from expected main");
    }
    match source(runner)? {
        Source::Local(path) => {
            let refspec = format!("{head}:refs/heads/main");
            let success = runner.git_status(&[
                "-c",
                "protocol.allow=never",
                "-c",
                "protocol.file.allow=always",
                "push",
                path.to_str().context("local origin is not UTF-8")?,
                &refspec,
            ])?;
            if !success {
                bail!("local push was not acknowledged; no automatic retry");
            }
        }
        Source::Private => {
            // Keep every receipt even on success: an acknowledged write followed by
            // failed readback is terminal, not another candidate for the outer loop.
            let receipts = tempfile::Builder::new()
                .prefix("ay-land-agh-")
                .tempdir()?
                .keep();
            eprintln!("Agh landing receipts: {}", receipts.display());
            fs::write(
                receipts.join("intent.json"),
                serde_json::to_vec(&serde_json::json!([
                    {"ref": "refs/heads/main", "before": remote, "after": head}
                ]))?,
            )?;
            if let Err(error) = agh.push(runner, &receipts, true) {
                if dry_run_ref_conflict(&receipts) {
                    runner.exact_clean(head)?;
                    fetch_with(runner, agh).with_context(|| {
                        format!(
                            "read main after non-writing Agh conflict; receipts {}",
                            receipts.display()
                        )
                    })?;
                    runner.exact_clean(head)?;
                    if read_ref(runner, TRACKING)?.as_deref() != Some(remote) {
                        // No write was attempted. The outer owner must compose
                        // the new main and qualify its affected read set.
                        return Ok(false);
                    }
                }
                return Err(error).with_context(|| {
                    format!("Agh dry run refused; receipts {}", receipts.display())
                });
            }
            runner.exact_clean(head)?;
            paths(runner)?;
            if source(runner)? != Source::Private {
                bail!(
                    "origin changed before write; receipts {}",
                    receipts.display()
                );
            }
            if read_ref(runner, TRACKING)?.as_deref() != Some(remote) {
                // Dry-run is not a write. A new validation round remains safe.
                return Ok(false);
            }
            agh.push(runner, &receipts, false).with_context(|| {
                format!(
                    "Agh write not acknowledged; outcome unknown, no automatic retry; receipts {}",
                    receipts.display()
                )
            })?;
            fetch_with(runner, agh).with_context(|| {
                format!(
                    "Agh acknowledged write but readback refused; no second push; receipts {}",
                    receipts.display()
                )
            })?;
            let contains = runner
                .git_status(&["merge-base", "--is-ancestor", head, FETCHED])
                .with_context(|| format!("Agh acknowledged write but ancestry readback failed; no second push; receipts {}", receipts.display()))?;
            if !contains {
                bail!("Agh acknowledged write but readback lacks validated commit; no second push; receipts {}", receipts.display());
            }
            runner.exact_clean(head).with_context(|| {
                format!(
                    "write acknowledged; local HEAD changed; receipts {}",
                    receipts.display()
                )
            })?;
            return Ok(true);
        }
    }
    runner.exact_clean(head)?;
    Ok(true)
}

#[cfg(all(test, unix))]
#[path = "land_transport_tests.rs"]
mod tests;
