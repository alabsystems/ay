// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `_oom_guard.py` admission planning for parallel bisect trials.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::error::{BisectError, Result};

const EMBEDDED_OOM_GUARD: &str = include_str!("../../../scripts/_oom_guard.py");

#[derive(Debug, Clone, PartialEq, Eq)]
enum PlannerSource {
    Checkout(PathBuf),
    Embedded,
}

impl PlannerSource {
    fn provenance(&self) -> String {
        match self {
            Self::Checkout(path) => path.display().to_string(),
            Self::Embedded => "embedded:scripts/_oom_guard.py".to_string(),
        }
    }

    fn command(&self) -> Command {
        let mut command = Command::new("python3");
        match self {
            Self::Checkout(path) => {
                command.arg(path);
            }
            // Execute the build-time copy of the repository's authoritative
            // planner. This keeps standalone installed binaries usable without
            // creating a second Rust implementation whose policy could drift.
            Self::Embedded => {
                ay_sys::embedded_python::embed_program(
                    &mut command,
                    "embedded:scripts/_oom_guard.py",
                    EMBEDDED_OOM_GUARD,
                );
            }
        }
        command
    }
}

/// Persistable resource envelope applied to every concrete AY trial.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResourcePlan {
    pub requested_jobs: usize,
    pub jobs: usize,
    pub memlimit_mb_per_child: usize,
    pub nbcore_per_child: usize,
    pub headroom_mb: usize,
    pub planner: String,
}

pub(crate) fn plan(requested_jobs: usize, ay_binary: &Path) -> Result<ResourcePlan> {
    let requested_jobs = requested_jobs.max(1);
    let planner =
        locate_planner(ay_binary).map_or(PlannerSource::Embedded, PlannerSource::Checkout);
    let output = planner
        .command()
        .arg("plan")
        .arg("--jobs")
        .arg(requested_jobs.to_string())
        .arg("--label")
        .arg("ay-bisect")
        .arg("--warn-concurrent-build")
        .output()
        .map_err(|source| BisectError::SpawnFailed {
            binary: "python3".to_string(),
            source,
        })?;
    if !output.stderr.is_empty() {
        eprint!("{}", String::from_utf8_lossy(&output.stderr));
    }
    if !output.status.success() {
        return Err(BisectError::ResourcePlan {
            message: format!("{} exited with {}", planner.provenance(), output.status),
        });
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    let values = parse_plan(&stdout)?;
    let jobs = value(&values, "PLAN_JOBS")?;
    let memlimit_mb_per_child = value(&values, "PLAN_MEMLIMIT_MB")?;
    let nbcore_per_child = value(&values, "PLAN_NBCORE")?;
    let headroom_mb = value(&values, "PLAN_HEADROOM_MB")?;
    if jobs == 0 || jobs > requested_jobs || memlimit_mb_per_child == 0 || nbcore_per_child == 0 {
        return Err(BisectError::ResourcePlan {
            message: format!(
                "invalid plan: requested_jobs={requested_jobs} jobs={jobs} memory={memlimit_mb_per_child}MiB NBCORE={nbcore_per_child}"
            ),
        });
    }
    Ok(ResourcePlan {
        requested_jobs,
        jobs,
        memlimit_mb_per_child,
        nbcore_per_child,
        headroom_mb,
        planner: planner.provenance(),
    })
}

fn locate_planner(ay_binary: &Path) -> Option<PathBuf> {
    let mut starts = Vec::new();
    if let Ok(cwd) = std::env::current_dir() {
        starts.push(cwd);
    }
    let binary = ay_binary
        .canonicalize()
        .unwrap_or_else(|_| ay_binary.to_path_buf());
    if let Some(parent) = binary.parent() {
        starts.push(parent.to_path_buf());
    }
    starts.push(PathBuf::from(env!("CARGO_MANIFEST_DIR")));
    for start in starts {
        for ancestor in start.ancestors() {
            let candidate = ancestor.join("scripts").join("_oom_guard.py");
            if candidate.is_file() {
                return Some(candidate);
            }
        }
    }
    None
}

fn parse_plan(output: &str) -> Result<BTreeMap<&str, usize>> {
    let mut values = BTreeMap::new();
    for line in output.lines() {
        let Some((key, raw)) = line.trim().split_once('=') else {
            continue;
        };
        if !key.starts_with("PLAN_") {
            continue;
        }
        let parsed = raw
            .parse::<usize>()
            .map_err(|_| BisectError::ResourcePlan {
                message: format!("invalid {key}={raw:?}"),
            })?;
        values.insert(key, parsed);
    }
    Ok(values)
}

fn value(values: &BTreeMap<&str, usize>, key: &'static str) -> Result<usize> {
    values
        .get(key)
        .copied()
        .ok_or_else(|| BisectError::ResourcePlan {
            message: format!("planner omitted {key}"),
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plan_parser_is_strict_and_does_not_evaluate_shell() {
        let err = parse_plan("PLAN_JOBS=$(oops)\n").expect_err("reject shell text");
        assert!(err.to_string().contains("invalid PLAN_JOBS"));
    }

    #[test]
    fn locates_repository_planner() {
        let planner = locate_planner(Path::new("target/debug/ay")).expect("planner");
        assert!(planner.ends_with("scripts/_oom_guard.py"));
    }

    /// THE EMBEDDED PLANNER MUST STAY ON THE INTERPRETER FLOOR IT DECLARES.
    ///
    /// [`PlannerSource::command`] runs the planner as a bare `python3`, and a
    /// stock macOS resolves that to `/usr/bin/python3` == 3.9.x with nothing
    /// newer installed. `scripts/_oom_guard.py` declares `MIN_PYTHON = (3, 9)`
    /// for exactly that reason, and this test reads the floor back OUT of the
    /// script so the two cannot drift.
    ///
    /// The failure it pins is one that happened: `CapturedRun.guard_evidence`
    /// was annotated `dict | None`, which PARSES on 3.9 and raises
    /// `TypeError: unsupported operand type(s) for |` when the class body
    /// executes — so every `ay-bisect` resource plan on a stock macOS died
    /// inside the planner, with a Python traceback for a diagnostic.
    ///
    /// Two checks, and both run on whatever `python3` this host has, which is
    /// the point: the sibling test above only exercises the floor on a host
    /// whose `python3` already IS the floor.
    ///
    /// * the floor's GRAMMAR, via `ast.parse(.., feature_version=MIN_PYTHON)`,
    ///   which rejects `match`, 3.12 type parameters and anything else the
    ///   floor cannot parse;
    /// * PEP 604 `X | Y` inside an annotation, which the grammar accepts at
    ///   every version and the floor's RUNTIME rejects. Skipped only when the
    ///   module opts into lazy annotations with `from __future__ import
    ///   annotations`, under which the expression is never evaluated.
    ///
    /// It fails loudly when `python3` is missing, when the floor declaration
    /// cannot be found, or when the source does not parse. It never skips.
    #[test]
    fn embedded_planner_runs_on_the_declared_interpreter_floor() {
        // Reads MIN_PYTHON out of the script under test, so the floor has ONE
        // declaration; a script with no floor is itself a failure.
        const CHECK: &str = r#"
import ast, re, sys
src = sys.stdin.read()
m = re.search(r"^MIN_PYTHON = \((\d+), (\d+)\)$", src, re.M)
if not m:
    print("scripts/_oom_guard.py declares no `MIN_PYTHON = (major, minor)` floor")
    raise SystemExit(1)
floor = (int(m.group(1)), int(m.group(2)))
try:
    tree = ast.parse(src, feature_version=floor)
except SyntaxError as e:
    print("line %s: syntax newer than Python %d.%d: %s" % (e.lineno, floor[0], floor[1], e.msg))
    raise SystemExit(1)
lazy = any(
    isinstance(n, ast.ImportFrom)
    and n.module == "__future__"
    and any(a.name == "annotations" for a in n.names)
    for n in tree.body
)
bad = []
if not lazy:
    anns = []
    for n in ast.walk(tree):
        if isinstance(n, ast.AnnAssign):
            anns.append(n.annotation)
        elif isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if n.returns is not None:
                anns.append(n.returns)
            a = n.args
            for arg in list(a.posonlyargs) + list(a.args) + list(a.kwonlyargs) + [a.vararg, a.kwarg]:
                if arg is not None and arg.annotation is not None:
                    anns.append(arg.annotation)
    for a in anns:
        for n in ast.walk(a):
            if isinstance(n, ast.BinOp) and isinstance(n.op, ast.BitOr):
                bad.append(n.lineno)
for line in sorted(set(bad)):
    print(
        "line %d: PEP 604 `X | Y` in an annotation is a RUNTIME expression; it "
        "raises TypeError before 3.10. Spell it typing.Optional[X] / typing.Union[..]."
        % line
    )
raise SystemExit(1 if bad else 0)
"#;
        use std::io::Write as _;
        use std::process::Stdio;
        let mut child = Command::new("python3")
            .arg("-c")
            .arg(CHECK)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("python3 must be on PATH: it is the interpreter the planner runs on");
        child
            .stdin
            .take()
            .expect("stdin")
            .write_all(EMBEDDED_OOM_GUARD.as_bytes())
            .expect("feed the embedded planner to the floor check");
        let output = child.wait_with_output().expect("floor check");
        assert!(
            output.status.success(),
            "scripts/_oom_guard.py uses something its own declared interpreter floor \
             cannot run. ay-bisect executes it as a bare `python3`, which is 3.9 on a \
             stock macOS, so this is a broken planner and not a style question.\n{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
    }

    #[test]
    fn embedded_planner_is_the_authoritative_script_and_reports_provenance() {
        let source = PlannerSource::Embedded;
        assert_eq!(source.provenance(), "embedded:scripts/_oom_guard.py");
        let output = source
            .command()
            .args(["plan", "--jobs", "1", "--label", "ay-bisect-test"])
            .output()
            .expect("run embedded planner");
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let stdout = String::from_utf8_lossy(&output.stdout);
        let values = parse_plan(&stdout).expect("parse plan");
        assert_eq!(value(&values, "PLAN_JOBS").unwrap(), 1);
        assert!(value(&values, "PLAN_MEMLIMIT_MB").unwrap() > 0);
    }
}
