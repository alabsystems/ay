// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unmodified upstream C++ example as a bounded downstream consumer.
//!
//! Upstream main catches exceptions and still returns zero. Completion thus
//! requires its final `done` marker, no `unexpected error:`, and a separate
//! assertion-abort control built with the same headers and flags. This checks
//! example completion and actual upstream assertions, not every printed answer.

use super::*;
use std::ffi::OsString;

const SCHEMA: &str = "ay-z3-stock-cpp-example/v1";
const EXAMPLE: &str = "examples/c++/example.cpp";
const LIMIT: u64 = 64 * 1024 * 1024;
const ASSERTION_MARKER: &str = "AY_STOCK_CPP_ASSERTION_REACHED";
const ASSERTION_CONTROL: &str = "#include \"z3++.h\"\n#include <cstdio>\n#ifdef NDEBUG\n#error NDEBUG must be undefined\n#endif\nint main() { if (std::fputs(\"AY_STOCK_CPP_ASSERTION_REACHED\\n\", stderr) < 0 || std::fflush(stderr) != 0) return 2; assert(false && \"ay-stock-cpp-assertions-enabled\"); return 0; }\n";

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
struct Capture {
    id: String,
    exit_code: Option<i32>,
    signal: Option<i32>,
    timed_out: bool,
    memout: bool,
    stdin_complete: bool,
    stdout_truncated: bool,
    stderr_truncated: bool,
    stdout_utf8: bool,
    stderr_utf8: bool,
    stdout: String,
    stderr: String,
    stdout_sha256: String,
    stderr_sha256: String,
}

impl Capture {
    fn from_output(id: &str, output: GuardedTranscriptOutput) -> Self {
        #[cfg(unix)]
        let signal = {
            output
                .status
                .as_ref()
                .and_then(std::os::unix::process::ExitStatusExt::signal)
        };
        #[cfg(not(unix))]
        let signal = None;
        Self {
            id: id.to_string(),
            exit_code: output.status.and_then(|status| status.code()),
            signal,
            timed_out: output.timed_out,
            memout: output.memout,
            stdin_complete: output.stdin_complete,
            stdout_truncated: output.stdout_truncated,
            stderr_truncated: output.stderr_truncated,
            stdout_utf8: std::str::from_utf8(&output.stdout).is_ok(),
            stderr_utf8: std::str::from_utf8(&output.stderr).is_ok(),
            stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
            stdout_sha256: sha256_bytes(&output.stdout),
            stderr_sha256: sha256_bytes(&output.stderr),
        }
    }
    fn bounded(&self) -> bool {
        !self.timed_out
            && !self.memout
            && self.stdin_complete
            && !self.stdout_truncated
            && !self.stderr_truncated
            && self.stdout_utf8
            && self.stderr_utf8
    }
    fn success(&self) -> bool {
        self.bounded() && self.exit_code == Some(0)
    }
    fn example_completed(&self) -> bool {
        self.success()
            && !self.stdout.contains("unexpected error:")
            && !self.stderr.contains("unexpected error:")
            && self
                .stdout
                .lines()
                .rev()
                .find(|line| !line.trim().is_empty())
                == Some("done")
    }
    fn assertion_aborted(&self) -> bool {
        self.bounded()
            && self.signal == Some(6)
            && self.exit_code.is_none()
            && self.stdout.is_empty()
            // dyld and other failures can also raise SIGABRT before main.
            // The flushed first line proves this exact control reached its
            // assertion, after the authenticated provider was loaded.
            && self.stderr.lines().next() == Some(ASSERTION_MARKER)
    }
}

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
struct Report {
    schema: String,
    profile_sha256: String,
    source_root: PathBuf,
    source_revision: String,
    example_path: String,
    example_sha256: String,
    header_sha256: BTreeMap<String, String>,
    assertion_control_sha256: String,
    compiler: PathBuf,
    compiler_sha256: String,
    compiler_version: Capture,
    compiler_flags: Vec<String>,
    ay_library: Artifact,
    z3_library: Artifact,
    validator_sha256: String,
    timeout_seconds: u64,
    resource_envelope: String,
    compile_resource_envelope: String,
    execution_resource_envelope: String,
    captures: Vec<Capture>,
    compiled_binary_sha256: BTreeMap<String, String>,
    reference_completed: bool,
    ay_completed: bool,
    assertion_control_passed: bool,
    stock_example_passed: bool,
    exhaustive_cpp_semantics_complete: bool,
    limitation: String,
}

fn compiler() -> &'static str {
    #[cfg(target_os = "macos")]
    {
        "/usr/bin/clang++"
    }
    #[cfg(not(target_os = "macos"))]
    {
        "/usr/bin/c++"
    }
}

fn flags() -> Vec<String> {
    ["-std=c++17", "-O1", "-UNDEBUG"]
        .into_iter()
        .map(str::to_string)
        .collect()
}

/// Every subprocess here inherits the caller's guarded process group. The
/// ordinary orchestrator invokes this worker only through PlannedResources,
/// including its exclusive aggregate host lease. A second nested build-slot
/// claim would double-count this same admitted compiler process tree.
/// Reuse the existing canonical library rebinding policy.
pub(super) fn build_child(args: &[String]) -> Result<i32, String> {
    if args.len() != 4 {
        return Err(
            "stock-cpp-build-child requires directory, source-kind, subject, library".to_string(),
        );
    }
    if !matches!(args[1].as_str(), "example" | "assertions")
        || !matches!(args[2].as_str(), "ay" | "z3")
    {
        return Err("unknown stock C++ source or subject".to_string());
    }
    let directory = Path::new(&args[0]);
    let library = Path::new(&args[3]);
    let binary = directory.join(format!("{}-{}", args[1], args[2]));
    let source = directory.join(format!("{}.cpp", args[1]));
    let mut command = Command::new(compiler());
    scrub_stock_c_compile_environment(&mut command);
    command
        .args(flags())
        .arg("-I")
        .arg(directory)
        .arg("-I")
        .arg(directory.join("c++"))
        .arg(&source)
        .arg("-o")
        .arg(&binary);
    link_stock_c_library(&mut command, library)?;
    let status = command
        .status()
        .map_err(|error| format!("invoke stock C++ compiler: {error}"))?;
    if !status.success() {
        return Err(format!(
            "stock C++ {}/{} compilation failed: {status}",
            args[1], args[2]
        ));
    }
    rebind_stock_c_library(&binary, library)?;
    Ok(0)
}

fn capture(
    resources: &PlannedResources,
    program: &Path,
    args: &[OsString],
    timeout: Duration,
    id: &str,
) -> Result<Capture, String> {
    resources
        .run_external_transcript_scrubbed_with_file_limit(program, args, b"", timeout, id, LIMIT)
        .map(|output| Capture::from_output(id, output))
        .map_err(|error| error.to_string())
}

fn snapshot_sources(
    source: &Path,
    inventory: &Value,
    directory: &Path,
) -> Result<(String, BTreeMap<String, String>), String> {
    let expected = inventory
        .get("source_files")
        .and_then(Value::as_array)
        .and_then(|files| files.iter().find(|row| row["path"] == EXAMPLE))
        .and_then(|row| row["sha256"].as_str())
        .ok_or("authenticated source inventory omits stock C++ example")?;
    let example = read_bounded_bytes(&source.join(EXAMPLE), LIMIT, "stock C++ example", true)?;
    if sha256_bytes(&example) != expected {
        return Err("stock C++ example differs from authenticated source".to_string());
    }
    atomic_write_new(&directory.join("example.cpp"), &example)?;
    atomic_write_new(
        &directory.join("assertions.cpp"),
        ASSERTION_CONTROL.as_bytes(),
    )?;
    let headers = inventory
        .get("header_sha256")
        .and_then(Value::as_object)
        .ok_or("source header inventory missing")?;
    if !headers.contains_key("c++/z3++.h") || !headers.contains_key("z3.h") {
        return Err("authenticated current headers omit C++ wrapper or root include".to_string());
    }
    let mut copied = BTreeMap::new();
    for (name, hash) in headers {
        validate_relative_path(name, "stock C++ header")?;
        let hash = hash.as_str().ok_or("invalid header digest")?;
        let bytes = read_bounded_bytes(
            &source.join("src/api").join(name),
            LIMIT,
            "stock C++ header",
            true,
        )?;
        if sha256_bytes(&bytes) != hash {
            return Err(format!("stock C++ header changed: {name}"));
        }
        let target = directory.join(name);
        if let Some(parent) = target.parent() {
            fs::create_dir_all(parent).map_err(|error| error.to_string())?;
        }
        atomic_write_new(&target, &bytes)?;
        copied.insert(name.clone(), hash.to_string());
    }
    Ok((expected.to_string(), copied))
}

fn measure(source: &Path, ay_library: &Path, timeout: u64) -> Result<Report, String> {
    let source = fs::canonicalize(source).map_err(|error| error.to_string())?;
    let ay_library = fs::canonicalize(ay_library).map_err(|error| error.to_string())?;
    let ay_sha256 = sha256_file(&ay_library, "AY stock C++ library")?;
    let profile = canonical_profile()?;
    let reference = reference_library_path()?;
    let ay = stage_authenticated_library(&ay_library, &ay_sha256, "stock C++ AY library")?;
    let z3 = stage_authenticated_library(
        &reference,
        &profile.z3_overlay.reference_shared_library.sha256,
        "stock C++ reference library",
    )?;
    let directory = tempfile::tempdir().map_err(|error| error.to_string())?;
    let inventory_path = directory.path().join("source-inventory.json");
    current_release::write_inventory(
        &source,
        &reference_artifact_path(&profile.z3_overlay.reference_executable.path)?,
        &inventory_path,
    )?;
    let inventory: Value = serde_json::from_slice(&read_bounded_bytes(
        &inventory_path,
        LIMIT,
        "stock C++ source inventory",
        true,
    )?)
    .map_err(|error| error.to_string())?;
    let (example_sha256, header_sha256) = snapshot_sources(&source, &inventory, directory.path())?;
    let resources = PlannedResources::plan(&locate_repo_root()?, 1, "stock upstream C++ example")
        .map_err(|error| error.to_string())?;
    let timeout_duration = Duration::from_secs(timeout);
    let resource_envelope =
        effective_execution_envelope(&resources.plan, ENFORCEMENT_RSS_WATCHDOG_V1, timeout as f64)
            .map_err(|error| error.to_string())?;
    let compiler_path = fs::canonicalize(compiler())
        .map_err(|error| format!("find stock C++ compiler: {error}"))?;
    let compiler_sha256 = sha256_file(&compiler_path, "stock C++ compiler")?;
    let compiler_version = capture(
        &resources,
        &compiler_path,
        &["--version".into()],
        Duration::from_secs(30),
        "compiler-version",
    )?;
    let validator = std::env::current_exe().map_err(|error| error.to_string())?;
    let validator_sha256 = sha256_file(&validator, "stock C++ runner")?;
    let mut captures = Vec::new();
    let mut binaries = BTreeMap::new();
    for (subject, library) in [("z3", &z3.path), ("ay", &ay.path)] {
        for kind in ["assertions", "example"] {
            let build_id = format!("build.{subject}.{kind}");
            let args = vec![
                "smtlib-conformance".into(),
                "stock-cpp-build-child".into(),
                directory.path().as_os_str().to_owned(),
                kind.into(),
                subject.into(),
                library.as_os_str().to_owned(),
            ];
            let built = capture(&resources, &validator, &args, timeout_duration, &build_id)?;
            let build_passed = built.success();
            captures.push(built);
            if !build_passed {
                continue;
            }
            let binary = directory.path().join(format!("{kind}-{subject}"));
            binaries.insert(
                format!("{subject}.{kind}"),
                sha256_file(&binary, "stock C++ linked consumer")?,
            );
            captures.push(capture(
                &resources,
                &binary,
                &[],
                timeout_duration,
                &format!("run.{subject}.{kind}"),
            )?);
        }
    }
    let has = |id: &str, predicate: fn(&Capture) -> bool| {
        captures
            .iter()
            .find(|row| row.id == id)
            .is_some_and(predicate)
    };
    let reference_completed = has("run.z3.example", Capture::example_completed);
    let ay_completed = has("run.ay.example", Capture::example_completed);
    let assertion_control_passed = has("run.z3.assertions", Capture::assertion_aborted)
        && has("run.ay.assertions", Capture::assertion_aborted);
    if sha256_file(&ay.path, "post-run AY library")? != ay_sha256
        || sha256_file(&z3.path, "post-run reference library")?
            != profile.z3_overlay.reference_shared_library.sha256
        || sha256_file(&compiler_path, "post-run compiler")? != compiler_sha256
    {
        return Err("stock C++ artifact changed during execution".to_string());
    }
    Ok(Report {
        schema: SCHEMA.to_string(), profile_sha256: canonical_profile_sha256()?, source_root: source,
        source_revision: profile.z3_overlay.source_commit, example_path: EXAMPLE.to_string(), example_sha256,
        header_sha256, assertion_control_sha256: sha256_bytes(ASSERTION_CONTROL.as_bytes()),
        compiler: compiler_path, compiler_sha256, compiler_version: compiler_version.clone(), compiler_flags: flags(),
        ay_library: Artifact { path: ay_library.to_string_lossy().into_owned(), sha256: ay_sha256 },
        z3_library: Artifact { path: reference.to_string_lossy().into_owned(), sha256: profile.z3_overlay.reference_shared_library.sha256 },
        validator_sha256, timeout_seconds: timeout,
        compile_resource_envelope: resource_envelope.clone(),
        execution_resource_envelope: resource_envelope.clone(),
        resource_envelope,
        stock_example_passed: compiler_version.success() && reference_completed && ay_completed && assertion_control_passed,
        reference_completed, ay_completed, assertion_control_passed, captures, compiled_binary_sha256: binaries,
        exhaustive_cpp_semantics_complete: false,
        limitation: "Only the unmodified upstream examples/c++/example.cpp program's assertions, explicit exception checks and final completion are qualified. Printed SAT/UNSAT answers, arbitrary model values and the whole C++/C API are not independently validated by this example. Missing symbols, compile failures, exceptions, assertion failures, timeouts and memory/output limits remain failures.".to_string(),
    })
}

pub(super) fn run(args: &[String]) -> Result<i32, String> {
    if args
        .iter()
        .any(|arg| matches!(arg.as_str(), "--help" | "-h"))
    {
        println!("smtlib-conformance stock-cpp --source DIR --ay-library FILE --out FILE [--timeout SECONDS]\n\nCompile the exact current upstream C++ example against stock headers and each\nlibrary. Assert-enabled control must abort; complete example must print final\ndone without caught unexpected errors. This is bounded example coverage only.\nTimeout covers each compilation or complete example process (default120s).");
        return Ok(0);
    }
    let mut source = None;
    let mut library = None;
    let mut output = None;
    let mut timeout = 120u64;
    let mut iter = args.iter();
    while let Some(flag) = iter.next() {
        let value = iter.next().ok_or_else(|| format!("{flag} needs a value"))?;
        match flag.as_str() {
            "--source" => source = Some(PathBuf::from(value)),
            "--ay-library" => library = Some(PathBuf::from(value)),
            "--out" => output = Some(PathBuf::from(value)),
            "--timeout" => {
                timeout = value
                    .parse()
                    .map_err(|_| "timeout must be integer seconds")?;
                if !(1..=3600).contains(&timeout) {
                    return Err("timeout must be1..3600".to_string());
                }
            }
            _ => return Err(format!("unknown stock-cpp option{flag}")),
        }
    }
    let output = output.ok_or("stock-cpp requires --out")?;
    let report = measure(
        &source.ok_or("stock-cpp requires --source")?,
        &library.ok_or("stock-cpp requires --ay-library")?,
        timeout,
    )?;
    atomic_write_new(&output, &pretty_json(&report)?)?;
    println!("stock_cpp={} reference_completed={} ay_completed={} assertions_enabled={} exhaustive_cpp_semantics_complete=false", output.display(), report.reference_completed, report.ay_completed, report.assertion_control_passed);
    Ok(i32::from(!report.stock_example_passed))
}

pub(super) fn check(args: &[String]) -> Result<i32, String> {
    if args.len() != 1 {
        return Err("usage: stock-cpp-check REPORT".to_string());
    }
    let report: Report = serde_json::from_slice(&read_bounded_bytes(
        Path::new(&args[0]),
        LIMIT,
        "stock C++ report",
        true,
    )?)
    .map_err(|error| error.to_string())?;
    if report.schema != SCHEMA
        || report.profile_sha256 != canonical_profile_sha256()?
        || report.example_path != EXAMPLE
        || report.compiler_flags != flags()
        || report.assertion_control_sha256 != sha256_bytes(ASSERTION_CONTROL.as_bytes())
        || report.exhaustive_cpp_semantics_complete
        || report.compile_resource_envelope != report.resource_envelope
        || report.execution_resource_envelope != report.resource_envelope
        || report.source_revision != canonical_profile()?.z3_overlay.source_commit
        || report.z3_library.sha256
            != canonical_profile()?
                .z3_overlay
                .reference_shared_library
                .sha256
        || sha256_file(
            &std::env::current_exe().map_err(|error| error.to_string())?,
            "stock C++ replay validator",
        )? != report.validator_sha256
        || !(1..=3600).contains(&report.timeout_seconds)
        || sha256_file(Path::new(&report.ay_library.path), "stock C++ replay AY")?
            != report.ay_library.sha256
        || sha256_file(&report.compiler, "stock C++ replay compiler")? != report.compiler_sha256
    {
        return Err("stock C++ report identity/scope drift".to_string());
    }
    validate_observations(&report)?;
    let fresh = measure(
        &report.source_root,
        Path::new(&report.ay_library.path),
        report.timeout_seconds,
    )?;
    if report.example_sha256 != fresh.example_sha256
        || report.header_sha256 != fresh.header_sha256
        || report.compiler_sha256 != fresh.compiler_sha256
        || report.z3_library.sha256 != fresh.z3_library.sha256
        || report.reference_completed != fresh.reference_completed
        || report.ay_completed != fresh.ay_completed
        || report.assertion_control_passed != fresh.assertion_control_passed
        || report.stock_example_passed != fresh.stock_example_passed
        || report.resource_envelope != fresh.resource_envelope
        || report.compiler_version != fresh.compiler_version
    {
        return Err("stock C++ result differs from fresh authenticated replay".to_string());
    }
    println!(
        "stock_cpp_replay=PASS stock_example_passed={} exhaustive_cpp_semantics_complete=false",
        fresh.stock_example_passed
    );
    Ok(i32::from(!fresh.stock_example_passed))
}

fn validate_observations(report: &Report) -> Result<(), String> {
    let mut ids = BTreeSet::new();
    for capture in &report.captures {
        if !ids.insert(capture.id.as_str())
            || capture.stdout_utf8
                && sha256_bytes(capture.stdout.as_bytes()) != capture.stdout_sha256
            || capture.stderr_utf8
                && sha256_bytes(capture.stderr.as_bytes()) != capture.stderr_sha256
        {
            return Err("stock C++ transcript identity/hash drift".to_string());
        }
    }
    let has = |id: &str, predicate: fn(&Capture) -> bool| {
        report
            .captures
            .iter()
            .find(|row| row.id == id)
            .is_some_and(predicate)
    };
    let reference = has("run.z3.example", Capture::example_completed);
    let ay = has("run.ay.example", Capture::example_completed);
    let assertions = has("run.z3.assertions", Capture::assertion_aborted)
        && has("run.ay.assertions", Capture::assertion_aborted);
    for subject in ["z3", "ay"] {
        for kind in ["assertions", "example"] {
            let build = format!("build.{subject}.{kind}");
            let run = format!("run.{subject}.{kind}");
            if !ids.contains(build.as_str())
                || has(&build, Capture::success) != ids.contains(run.as_str())
            {
                return Err("stock C++ build/execution population mismatch".to_string());
            }
        }
    }
    if report.reference_completed != reference
        || report.ay_completed != ay
        || report.assertion_control_passed != assertions
        || report.stock_example_passed
            != (report.compiler_version.success() && reference && ay && assertions)
    {
        return Err("stock C++ completion does not follow retained observations".to_string());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn capture(stdout: &str) -> Capture {
        Capture {
            id: "control".to_string(),
            exit_code: Some(0),
            signal: None,
            timed_out: false,
            memout: false,
            stdin_complete: true,
            stdout_truncated: false,
            stderr_truncated: false,
            stdout_utf8: true,
            stderr_utf8: true,
            stdout: stdout.to_string(),
            stderr: String::new(),
            stdout_sha256: sha256_bytes(stdout.as_bytes()),
            stderr_sha256: sha256_bytes(b""),
        }
    }
    #[test]
    fn caught_exception_is_failure_even_with_zero_exit_and_done_spoof() {
        assert!(capture("many expected examples\ndone\n").example_completed());
        assert!(!capture("unexpected error: failed model\ndone\n").example_completed());
        assert!(!capture("partial example\n").example_completed());
    }
    #[test]
    fn truncated_timed_out_or_disabled_assertions_never_pass() {
        let mut output = capture("done\n");
        output.stdout_truncated = true;
        assert!(!output.example_completed());
        let mut output = capture("done\n");
        output.timed_out = true;
        assert!(!output.example_completed());
        assert!(!capture("").assertion_aborted());
        let mut control = capture("");
        control.exit_code = None;
        control.signal = Some(6);
        assert!(!control.assertion_aborted());
    }

    #[test]
    fn loader_abort_cannot_pass_the_assertion_control() {
        let mut control = capture("");
        control.exit_code = None;
        control.signal = Some(6);
        control.stderr = "dyld: Library not loaded: libay_ffi.dylib\n".to_string();
        assert!(!control.assertion_aborted());
        control.stderr = format!(
            "{ASSERTION_MARKER}\nAssertion failed: (false && \"ay-stock-cpp-assertions-enabled\")\n"
        );
        assert!(control.assertion_aborted());
        control
            .stderr
            .insert_str(0, "unexpected initialization diagnostic\n");
        assert!(!control.assertion_aborted());
    }

    #[test]
    fn nested_cpp_header_paths_are_retained_without_flattening() {
        let source = tempfile::tempdir().unwrap();
        let staged = tempfile::tempdir().unwrap();
        fs::create_dir_all(source.path().join("examples/c++")).unwrap();
        fs::create_dir_all(source.path().join("src/api/c++")).unwrap();
        let example = b"#include \"z3++.h\"\nint main(){}\n";
        let wrapper = b"#include <z3.h>\n";
        let header = b"/* root C API */\n";
        fs::write(source.path().join(EXAMPLE), example).unwrap();
        fs::write(source.path().join("src/api/c++/z3++.h"), wrapper).unwrap();
        fs::write(source.path().join("src/api/z3.h"), header).unwrap();
        let inventory = serde_json::json!({
            "source_files": [{"path": EXAMPLE, "sha256": sha256_bytes(example)}],
            "header_sha256": {"c++/z3++.h": sha256_bytes(wrapper), "z3.h": sha256_bytes(header)}
        });
        let (_, hashes) = snapshot_sources(source.path(), &inventory, staged.path()).unwrap();
        assert_eq!(hashes["c++/z3++.h"], sha256_bytes(wrapper));
        assert_eq!(fs::read(staged.path().join("c++/z3++.h")).unwrap(), wrapper);
        assert_eq!(fs::read(staged.path().join("z3.h")).unwrap(), header);
        assert!(!staged.path().join("z3++.h").exists());
    }
}
