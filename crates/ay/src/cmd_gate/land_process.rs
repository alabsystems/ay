// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use anyhow::{bail, Context, Result};
use serde::Serialize;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

#[path = "land_documentation.rs"]
mod documentation;
#[path = "land_ffi_artifact.rs"]
mod ffi_artifact;
#[path = "land_transport.rs"]
mod transport;

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub(super) enum StepKind {
    Command,
    /// Workspace resolution with the checked-in lockfile and no network.
    Metadata,
    RustTests,
    FfiArtifactBuild,
    FfiArtifactTests,
    ScriptIntegrity,
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub(super) struct Step {
    pub(super) program: String,
    pub(super) args: Vec<String>,
    pub(super) kind: StepKind,
}

impl Step {
    pub(super) fn new(program: &str, args: &[&str]) -> Self {
        Self {
            program: program.into(),
            args: args.iter().map(|s| (*s).into()).collect(),
            kind: StepKind::Command,
        }
    }

    /// `targo metadata` with the checked-in lockfile: the resolution check of a
    /// version-only landing, and the planner's conservative read when the
    /// feature-resolved one fails. It compiles nothing, so it takes no
    /// build-slot admission, and Targo refuses `--unverified` on it.
    pub(super) fn metadata() -> Self {
        Self {
            kind: StepKind::Metadata,
            ..Self::new(
                "targo",
                &["metadata", "--locked", "--offline", "--format-version", "1"],
            )
        }
    }

    /// Scheduling metadata only. The actual shared lease remains mandatory.
    pub(super) fn needs_quiet_host(&self) -> bool {
        self.kind == StepKind::RustTests
            && self.program == "build-slot"
            && self.args.first().is_some_and(|arg| arg == "--exclusive")
    }

    pub(super) fn compiler(args: Vec<String>) -> Self {
        let kind = if args.first().is_some_and(|a| a == "test") {
            StepKind::RustTests
        } else {
            StepKind::Command
        };
        // These targets execute real benchmark planners, which correctly refuse
        // concurrent compiler work. Take the existing shared pool's exclusive
        // lease for that target, rather than bypassing its production fence.
        let cli_benchmark_controls = args
            .windows(2)
            .any(|pair| matches!(pair[0].as_str(), "-p" | "--package") && pair[1] == "ay")
            && args
                .windows(2)
                .any(|pair| pair[0] == "--test" && pair[1] == "group_cli");
        let parity_benchmark_controls = args.windows(2).any(|pair| {
            matches!(pair[0].as_str(), "-p" | "--package") && pair[1] == "ay-z3-parity"
        }) && args.iter().any(|arg| arg == "--bins");
        let mut command = Vec::new();
        if kind == StepKind::RustTests && (cli_benchmark_controls || parity_benchmark_controls) {
            command.push("--exclusive".into());
        }
        command.extend(["--".into(), "targo".into(), "--unverified".into()]);
        command.extend(args);
        Self {
            program: "build-slot".into(),
            args: command,
            kind,
        }
    }
}

pub(super) struct Runner {
    pub(super) root: PathBuf,
    agh_program: String,
    ffi_artifact: Option<ffi_artifact::Library>,
}

/// A successful plan and any subsequently checked documentation composition.
/// Original check/artifact provenance is never rewritten to the composed HEAD.
pub(super) struct ValidatedHead {
    head: String,
    checked_head: String,
    checked_tree: String,
    checks: Vec<Step>,
    documentation: Vec<documentation::Composition>,
}

impl Runner {
    pub(super) fn new(root: PathBuf) -> Self {
        Self {
            root,
            agh_program: "agh".into(),
            ffi_artifact: None,
        }
    }

    /// Select a command, not an authority or an alternate transport. Native
    /// Agh still owns credentials, policy and the ordinary atomic push.
    /// Keep PATH unchanged: it is also a compiler tool-input context.
    pub(super) fn select_agh(&mut self, path: &Path) -> Result<()> {
        if !path.is_absolute() {
            bail!("--agh requires an absolute executable path");
        }
        let metadata = std::fs::metadata(path).context("read explicit Agh executable")?;
        if !metadata.is_file() {
            bail!("--agh must name an executable file");
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if metadata.permissions().mode() & 0o111 == 0 {
                bail!("--agh must name an executable file");
            }
        }
        self.agh_program = path
            .to_str()
            .context("explicit Agh executable path is not UTF-8")?
            .to_owned();
        Ok(())
    }

    pub(super) fn agh_program(&self) -> &str {
        &self.agh_program
    }

    pub(super) fn agh_step(&self, args: &[&str]) -> Step {
        Step::new(&self.agh_program, args)
    }

    fn command(&self, step: &Step) -> Result<Command> {
        eprintln!(
            "{}",
            serde_json::to_string(&serde_json::json!({
                "event": "command", "cwd": self.root, "command": step
            }))?
        );
        let mut command = Command::new(&step.program);
        command
            .args(&step.args)
            .current_dir(&self.root)
            .stdin(Stdio::null());
        Ok(command)
    }

    fn result(&self, step: &Step, status: std::process::ExitStatus) -> Result<()> {
        eprintln!(
            "{}",
            serde_json::to_string(&serde_json::json!({
                "event": "result", "command": step, "success": status.success(), "code": status.code()
            }))?
        );
        Ok(())
    }

    pub(super) fn execute(&mut self, step: &Step) -> Result<()> {
        if step.kind == StepKind::ScriptIntegrity {
            let code = crate::cmd_scripts::check_at(&self.root)?;
            println!(
                "{}",
                serde_json::json!({"event":"native_validation", "owner":"cmd_scripts", "code":code, "success":code == 0})
            );
            if code != 0 {
                bail!("native script registry/publication integrity failed");
            }
            return Ok(());
        }
        if step.kind == StepKind::Metadata {
            // Decode the resolved workspace rather than print it.
            let metadata = self.resolve(step)?;
            println!(
                "{}",
                serde_json::json!({"event":"native_validation", "owner":"targo metadata",
                    "workspace_members":metadata.workspace_members.len(), "success":true})
            );
            return Ok(());
        }
        if step.kind == StepKind::FfiArtifactBuild {
            self.ffi_artifact = None;
            let log = tempfile::NamedTempFile::new()?;
            let status = self
                .command(step)?
                .stdout(Stdio::from(log.reopen()?))
                .status()?;
            self.result(step, status)?;
            if !status.success() {
                // Compiler diagnostics share stdout with artifact JSON. Keep
                // that exact stream on failure instead of deleting the only
                // detailed explanation when this temporary file drops.
                let (_messages, path) = log.keep().with_context(|| {
                    format!("retain diagnostics after FFI artifact preparation failed: {status}")
                })?;
                bail!(
                    "FFI artifact preparation failed: {status}; compiler messages retained at {}",
                    path.display()
                );
            }
            self.ffi_artifact = Some(ffi_artifact::Library::from_messages(
                &self.root,
                log.reopen()?,
            )?);
            return Ok(());
        }
        if matches!(step.kind, StepKind::RustTests | StepKind::FfiArtifactTests) {
            return self.execute_tests(step).map(|_| ());
        }
        let status = self
            .command(step)?
            .status()
            .with_context(|| format!("start {}", step.program))?;
        self.result(step, status)?;
        if !status.success() {
            bail!("{} failed: {status}", step.program);
        }
        Ok(())
    }

    fn execute_tests(&mut self, step: &Step) -> Result<Vec<u8>> {
        // A regular file avoids waiting for EOF from an escaped descendant
        // that inherited a test's stdout. Wait only for the command we own.
        let log = tempfile::NamedTempFile::new()?;
        let mut command = self.command(step)?;
        let library = if step.kind == StepKind::FfiArtifactTests {
            let library = self
                .ffi_artifact
                .as_ref()
                .context("FFI tests have no produced library")?;
            library.verify()?;
            library.bind(&mut command);
            Some(library)
        } else {
            None
        };
        let status = command.stdout(Stdio::from(log.reopen()?)).status()?;
        let output = std::fs::read(log.path())?;
        std::io::stdout().write_all(&output)?;
        self.result(step, status)?;
        if let Some(library) = library {
            library.verify()?;
        }
        if !status.success() {
            bail!("{} failed: {status}", step.program);
        }
        let passed = passed_tests(&output);
        println!(
            "{}",
            serde_json::json!({
                "event": "test_coverage", "passed": passed,
                "coverage": if passed > 0 { "runtime-tests" } else { "compile-only" },
                "command": step,
            })
        );
        Ok(output)
    }

    fn capture(&mut self, step: &Step) -> Result<Vec<u8>> {
        let output = self
            .command(step)?
            .stderr(Stdio::inherit())
            .output()
            .with_context(|| format!("start {}", step.program))?;
        self.result(step, output.status)?;
        if !output.status.success() {
            bail!("{} failed: {}", step.program, output.status);
        }
        Ok(output.stdout)
    }

    pub(super) fn git_bytes(&mut self, args: &[&str]) -> Result<Vec<u8>> {
        self.capture(&Step::new("git", args))
    }

    pub(super) fn git(&mut self, args: &[&str]) -> Result<String> {
        String::from_utf8(self.git_bytes(args)?).context("git output is not UTF-8")
    }

    pub(super) fn git_status(&mut self, args: &[&str]) -> Result<bool> {
        let step = Step::new("git", args);
        let status = self.command(&step)?.status().context("start git")?;
        self.result(&step, status)?;
        Ok(status.success())
    }

    pub(super) fn git_search(&mut self, args: &[&str]) -> Result<Vec<u8>> {
        let step = Step::new("git", args);
        let output = self.command(&step)?.stderr(Stdio::inherit()).output()?;
        self.result(&step, output.status)?;
        match output.status.code() {
            Some(0 | 1) => Ok(output.stdout),
            _ => bail!("Git consumer census failed: {}", output.status),
        }
    }

    pub(super) fn fetch(&mut self) -> Result<()> {
        transport::fetch(self)
    }

    pub(super) fn head(&mut self) -> Result<String> {
        Ok(self.git(&["rev-parse", "HEAD"])?.trim().to_string())
    }

    pub(super) fn clean(&mut self) -> Result<()> {
        if !self
            .git_bytes(&[
                "status",
                "--porcelain=v1",
                "-z",
                "--untracked-files=all",
                "--ignore-submodules=none",
            ])?
            .is_empty()
        {
            bail!("landing requires a clean tracked and untracked worktree");
        }
        for marker in [
            "MERGE_HEAD",
            "CHERRY_PICK_HEAD",
            "REVERT_HEAD",
            "rebase-merge",
            "rebase-apply",
        ] {
            let path = self.git(&["rev-parse", "--git-path", marker])?;
            if self.root.join(path.trim()).exists() {
                bail!("unfinished git operation: {marker}");
            }
        }
        Ok(())
    }

    pub(super) fn exact_clean(&mut self, expected: &str) -> Result<()> {
        self.clean()?;
        if self.head()? != expected {
            bail!("HEAD changed during validation; refusing push");
        }
        Ok(())
    }

    pub(super) fn validate(&mut self, steps: &[Step], head: &str) -> Result<ValidatedHead> {
        self.exact_clean(head)?;
        for step in steps {
            self.execute(step)?;
            self.exact_clean(head)?;
        }
        let tree = self.git(&["rev-parse", &format!("{head}^{{tree}}")])?;
        Ok(ValidatedHead {
            head: head.into(),
            checked_head: head.into(),
            checked_tree: tree.trim().into(),
            checks: steps.to_vec(),
            documentation: Vec::new(),
        })
    }

    /// Return false only when the remote changed and a fresh round is needed.
    pub(super) fn push_validated(
        &mut self,
        validated: &ValidatedHead,
        remote: &str,
    ) -> Result<bool> {
        transport::push(self, &validated.head, remote)
    }

    pub(super) fn metadata(&mut self) -> Result<super::plan::Metadata> {
        let features = super::plan::CLI_FEATURES
            .split(',')
            .map(|feature| format!("ay/{feature}"))
            .collect::<Vec<_>>()
            .join(",");
        let output = self.capture(&Step::new(
            "targo",
            &[
                "metadata",
                "--locked",
                "--offline",
                "--features",
                &features,
                "--format-version",
                "1",
            ],
        ));
        let output = match output {
            Ok(output) => output,
            Err(error) => {
                // Optional feature sources may be absent in an offline cache.
                // Preserve the original broad CLI integration check rather
                // than inferring a negative dependency from a partial graph.
                eprintln!(
                    "{}",
                    serde_json::json!({"event":"cli_dependency_scope", "complete":false, "conservative_cli":true, "reason":error.to_string()})
                );
                return self
                    .resolve(&Step::metadata())
                    .context("conservative Targo workspace metadata");
            }
        };
        serde_json::from_slice(&output).context("decode Targo workspace metadata")
    }

    fn resolve(&mut self, step: &Step) -> Result<super::plan::Metadata> {
        let output = self.capture(step)?;
        serde_json::from_slice(&output).context("decode Targo workspace metadata")
    }
}

pub(super) fn passed_tests(output: &[u8]) -> usize {
    String::from_utf8_lossy(output)
        .lines()
        .filter_map(|line| {
            line.strip_prefix("test result: ok. ")?
                .split_whitespace()
                .next()?
                .parse::<usize>()
                .ok()
        })
        .sum()
}
