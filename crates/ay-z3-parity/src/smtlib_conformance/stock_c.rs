// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The pinned upstream C example, compiled without changing its bytes.
//!
//! Its checks call `exitf`, rather than C `assert`. Require the complete ordered
//! example census and final model checks, and exercise both failure mechanisms
//! separately. A successful finite example never closes the whole C API.

use super::*;
use std::ffi::OsString;

const SCHEMA: &str = "ay-z3-stock-c-example/v1";
const EXAMPLE: &str = "examples/c/test_capi.c";
const EXAMPLE_SHA256: &str = "60017afabac4064a6ce311568635a975c328d0566e107722a60eb6ca72b54c36";
const LIMIT: u64 = 64 * 1024 * 1024;
const ASSERTION_MARKER: &str = "AY_STOCK_C_ASSERTION_REACHED";
const RESULT_MARKER: &str = "AY_STOCK_C_EXPECTED_RESULT_REACHED";
const ASSERTION_CONTROL: &str = "#include <z3.h>\n#include <stdio.h>\n#include <assert.h>\n#ifdef NDEBUG\n#error NDEBUG must be undefined\n#endif\nint main(void) { Z3_config cfg = Z3_mk_config(); Z3_context ctx = Z3_mk_context(cfg); Z3_del_config(cfg); Z3_del_context(ctx); if (fputs(\"AY_STOCK_C_ASSERTION_REACHED\\n\", stderr) < 0 || fflush(stderr) != 0) return 2; assert(0 && \"ay-stock-c-assertions-enabled\"); return 0; }\n";
// This separate negative control reuses the unmodified upstream `check` and
// `exitf`. Only its entry point is renamed; the actual example has no adapter.
const RESULT_CONTROL: &str = "#define main ay_stock_c_upstream_main\n#include \"example.c\"\n#undef main\nint main(void) { Z3_context ctx = mk_context(); Z3_solver s = mk_solver(ctx); if (fputs(\"AY_STOCK_C_EXPECTED_RESULT_REACHED\\n\", stderr) < 0 || fflush(stderr) != 0) return 2; check(ctx, s, Z3_L_FALSE); del_solver(ctx, s); Z3_del_context(ctx); return 0; }\n";
const KINDS: [&str; 3] = ["assertions", "expected-result", "example"];

// Exact straight-line main-call census in EXAMPLE_SHA256, including the two
// initial examples without a heading and the version query.
const MAIN_CALLS: [&str; 39] = [
    "complex_example",
    "divides_example",
    "display_version",
    "simple_example",
    "demorgan",
    "find_model_example1",
    "find_model_example2",
    "prove_example1",
    "prove_example2",
    "push_pop_example1",
    "quantifier_example1",
    "array_example1",
    "array_example2",
    "array_example3",
    "tuple_example1",
    "bitvector_example1",
    "bitvector_example2",
    "eval_example1",
    "two_contexts_example1",
    "error_code_example1",
    "error_code_example2",
    "parser_example2",
    "parser_example3",
    "parser_example5",
    "numeral_example",
    "ite_example",
    "list_example",
    "tree_example",
    "forest_example",
    "binary_tree_example",
    "enum_example",
    "unsat_core_and_proof_example",
    "incremental_example1",
    "reference_counter_example",
    "smt2parser_example",
    "substitute_example",
    "substitute_vars_example",
    "fpa_example",
    "mk_model_example",
];
const MARKERS: [&str; 36] = [
    "simple_example",
    "DeMorgan",
    "find_model_example1",
    "find_model_example2",
    "prove_example1",
    "prove_example2",
    "push_pop_example1",
    "quantifier_example1",
    "array_example1",
    "array_example2",
    "array_example3",
    "tuple_example1",
    "bitvector_example1",
    "bitvector_example2",
    "eval_example1",
    "two_contexts_example1",
    "error_code_example1",
    "error_code_example2",
    "parser_example2",
    "parser_example3",
    "parser_example5",
    "numeral_example",
    "ite_example",
    "list_example",
    "tree_example",
    "forest_example",
    "binary_tree_example",
    "enum_example",
    "unsat_core_and_proof_example",
    "incremental_example1",
    "reference_counter_example",
    "smt2parser_example",
    "substitute_example",
    "substitute_vars_example",
    "FPA-example",
    "mk_model_example",
];
const FINAL_MARKERS: [&str; 5] = [
    "Found interpretation for \"(declare-fun a () Int)\"",
    "Found interpretation for \"(declare-fun b () Int)\"",
    "Found interpretation for \"(declare-fun c () (Array Int Int))\"",
    "Evaluated a + b = 3",
    "Evaluated c[0] + c[1] + c[2] = 7",
];

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
    // Byte arrays retain invalid UTF-8 failures without replacement characters.
    stdout: Vec<u8>,
    stderr: Vec<u8>,
    stdout_sha256: String,
    stderr_sha256: String,
}

impl Capture {
    fn from_output(id: &str, output: GuardedTranscriptOutput) -> Self {
        #[cfg(unix)]
        let signal = output
            .status
            .as_ref()
            .and_then(std::os::unix::process::ExitStatusExt::signal);
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
            stdout_sha256: sha256_bytes(&output.stdout),
            stderr_sha256: sha256_bytes(&output.stderr),
            stdout: output.stdout,
            stderr: output.stderr,
        }
    }
    fn bounded(&self) -> bool {
        !self.timed_out
            && !self.memout
            && self.stdin_complete
            && !self.stdout_truncated
            && !self.stderr_truncated
            && std::str::from_utf8(&self.stdout).is_ok()
            && std::str::from_utf8(&self.stderr).is_ok()
    }
    fn success(&self) -> bool {
        self.bounded() && self.exit_code == Some(0) && self.signal.is_none()
    }
    fn assertion_aborted(&self) -> bool {
        self.bounded()
            && self.signal == Some(6)
            && self.exit_code.is_none()
            && self.stdout.is_empty()
            && self
                .stderr
                .starts_with(format!("{ASSERTION_MARKER}\n").as_bytes())
    }
    fn wrong_expectation_refused(&self) -> bool {
        self.bounded()
            && self.exit_code == Some(1)
            && self.signal.is_none()
            && self.stderr == format!("{RESULT_MARKER}\nBUG: unexpected result.\n").as_bytes()
            && self.stdout.starts_with(b"sat\n")
    }
    fn example_observation(&self) -> ExampleObservation {
        let stdout = std::str::from_utf8(&self.stdout).unwrap_or("");
        let markers = stdout
            .lines()
            .filter(|line| MARKERS.contains(line))
            .map(str::to_string)
            .collect::<Vec<_>>();
        let final_output = stdout
            .rsplit_once("\nmk_model_example\n")
            .map(|(_, tail)| tail)
            .unwrap_or("");
        let final_markers = final_output
            .lines()
            .filter(|line| FINAL_MARKERS.contains(line))
            .map(str::to_string)
            .collect::<Vec<_>>();
        let completed = self.success()
            && self.stderr.is_empty()
            && !stdout.contains("BUG:")
            && markers == MARKERS
            && final_markers == FINAL_MARKERS
            && stdout
                .lines()
                .filter(|line| numeric_version_line(line))
                .count()
                == 1
            && stdout
                .lines()
                .filter(|line| *line == "DeMorgan is valid")
                .count()
                == 1
            && stdout.lines().rev().find(|line| !line.trim().is_empty())
                == FINAL_MARKERS.last().copied();
        ExampleObservation {
            markers,
            final_markers,
            completed,
        }
    }
}

// Upstream's deliberate invalid-sort/parser cases also print `Z3 error:` to
// stdout. Only display_version's four unsigned decimal components witness the
// version query; those expected error diagnostics remain visible and accepted.
fn numeric_version_line(line: &str) -> bool {
    let Some(version) = line.strip_prefix("Z3 ") else {
        return false;
    };
    let components = version.split('.').collect::<Vec<_>>();
    components.len() == 4
        && components.iter().all(|component| {
            !component.is_empty()
                && component.bytes().all(|byte| byte.is_ascii_digit())
                && component.parse::<u32>().is_ok()
        })
}

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
struct ExampleObservation {
    markers: Vec<String>,
    final_markers: Vec<String>,
    completed: bool,
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
    expected_main_calls: Vec<String>,
    expected_markers: Vec<String>,
    expected_final_markers: Vec<String>,
    control_sha256: BTreeMap<String, String>,
    compiler: PathBuf,
    compiler_sha256: String,
    compiler_version: Capture,
    compiler_flags: Vec<String>,
    retained_source: BTreeMap<String, Artifact>,
    ay_library: Artifact,
    z3_library: Artifact,
    validator_sha256: String,
    timeout_seconds: u64,
    resource_envelope: String,
    per_file_limit_bytes: u64,
    captures: Vec<Capture>,
    retained_binary: BTreeMap<String, Artifact>,
    reference: ExampleObservation,
    ay: ExampleObservation,
    assertions_enabled: bool,
    wrong_expectation_refused: bool,
    stock_example_passed: bool,
    exhaustive_c_semantics_complete: bool,
    limitation: String,
}

fn compiler() -> &'static str {
    if cfg!(target_os = "macos") {
        "/usr/bin/clang"
    } else {
        "/usr/bin/cc"
    }
}
fn flags() -> Vec<String> {
    ["-std=c99", "-O1", "-UNDEBUG"]
        .into_iter()
        .map(str::to_string)
        .collect()
}
fn controls() -> BTreeMap<String, String> {
    [
        ("assertions", ASSERTION_CONTROL),
        ("expected-result", RESULT_CONTROL),
    ]
    .into_iter()
    .map(|(name, source)| (name.to_string(), sha256_bytes(source.as_bytes())))
    .collect()
}

/// Called only inside the parent's admitted, bounded child process group.
pub(super) fn build_child(args: &[String]) -> Result<i32, String> {
    if args.len() != 5
        || !KINDS.contains(&args[1].as_str())
        || !["ay", "z3"].contains(&args[2].as_str())
    {
        return Err(
            "stock-c-build-child requires directory, source-kind, subject, library, compiler"
                .to_string(),
        );
    }
    let directory = Path::new(&args[0]);
    let library = Path::new(&args[3]);
    let binary = directory.join(format!("{}-{}", args[1], args[2]));
    let mut command = Command::new(&args[4]);
    scrub_stock_c_compile_environment(&mut command);
    command
        .args(flags())
        .arg("-I")
        .arg(directory)
        .arg(directory.join(format!("{}.c", args[1])))
        .arg("-o")
        .arg(&binary);
    link_stock_c_library(&mut command, library)?;
    let status = command
        .status()
        .map_err(|error| format!("invoke stock C compiler: {error}"))?;
    if !status.success() {
        return Err(format!(
            "stock C {}/{} compilation failed: {status}",
            args[1], args[2]
        ));
    }
    rebind_stock_c_library(&binary, library)?;
    Ok(0)
}

/// Exec preserves the supervised PID/group and assertion signal. The upstream
/// source opens z3.log relative to its cwd; never let it write into the checkout.
pub(super) fn run_child(args: &[String]) -> Result<i32, String> {
    if args.len() != 2 {
        return Err("stock-c-run-child requires directory and binary".to_string());
    }
    let mut command = Command::new(&args[1]);
    command.current_dir(&args[0]);
    scrub_stock_c_compile_environment(&mut command);
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        Err(format!("exec stock C consumer: {}", command.exec()))
    }
    #[cfg(not(unix))]
    {
        Err("stock C execution requires native Unix supervision".to_string())
    }
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
) -> Result<BTreeMap<String, String>, String> {
    let expected = inventory["source_files"]
        .as_array()
        .and_then(|files| files.iter().find(|row| row["path"] == EXAMPLE))
        .and_then(|row| row["sha256"].as_str())
        .ok_or("authenticated source inventory omits stock C example")?;
    let example = read_bounded_bytes(&source.join(EXAMPLE), LIMIT, "stock C example", true)?;
    if expected != EXAMPLE_SHA256 || sha256_bytes(&example) != EXAMPLE_SHA256 {
        return Err("stock C example differs from its pinned census".to_string());
    }
    atomic_write_new(&directory.join("example.c"), &example)?;
    atomic_write_new(
        &directory.join("assertions.c"),
        ASSERTION_CONTROL.as_bytes(),
    )?;
    atomic_write_new(
        &directory.join("expected-result.c"),
        RESULT_CONTROL.as_bytes(),
    )?;
    let headers = inventory["header_sha256"]
        .as_object()
        .ok_or("source header inventory missing")?;
    if !headers.contains_key("z3.h") {
        return Err("authenticated C root header missing".to_string());
    }
    let mut copied = BTreeMap::new();
    for (name, hash) in headers {
        if name.contains('/') {
            continue;
        } // C++ wrappers are not C inputs.
        validate_relative_path(name, "stock C header")?;
        let hash = hash.as_str().ok_or("invalid C header digest")?;
        let bytes = read_bounded_bytes(
            &source.join("src/api").join(name),
            LIMIT,
            "stock C header",
            true,
        )?;
        if sha256_bytes(&bytes) != hash {
            return Err(format!("stock C header changed: {name}"));
        }
        atomic_write_new(&directory.join(name), &bytes)?;
        copied.insert(name.clone(), hash.to_string());
    }
    Ok(copied)
}

fn observation(captures: &[Capture], subject: &str) -> ExampleObservation {
    captures
        .iter()
        .find(|row| row.id == format!("run.{subject}.example"))
        .map(Capture::example_observation)
        .unwrap_or(ExampleObservation {
            markers: vec![],
            final_markers: vec![],
            completed: false,
        })
}

fn measure(
    source: &Path,
    ay_library: &Path,
    timeout: u64,
    retained: Option<&Path>,
) -> Result<Report, String> {
    let source = fs::canonicalize(source).map_err(|error| error.to_string())?;
    let ay_library = fs::canonicalize(ay_library).map_err(|error| error.to_string())?;
    let ay_sha256 = sha256_file(&ay_library, "AY stock C library")?;
    let profile = canonical_profile()?;
    let reference = reference_library_path()?;
    let ay = stage_authenticated_library(&ay_library, &ay_sha256, "stock C AY library")?;
    let z3 = stage_authenticated_library(
        &reference,
        &profile.z3_overlay.reference_shared_library.sha256,
        "stock C reference library",
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
        "stock C source inventory",
        true,
    )?)
    .map_err(|error| error.to_string())?;
    let header_sha256 = snapshot_sources(&source, &inventory, directory.path())?;
    let mut retained_source = BTreeMap::new();
    if let Some(retained) = retained {
        for name in header_sha256.keys().map(String::as_str).chain([
            "example.c",
            "assertions.c",
            "expected-result.c",
        ]) {
            let bytes = read_bounded_bytes(
                &directory.path().join(name),
                LIMIT,
                "stock C retained source",
                true,
            )?;
            let path = retained.join(name);
            atomic_write_new(&path, &bytes)?;
            retained_source.insert(
                name.to_string(),
                Artifact {
                    path: path.to_string_lossy().into_owned(),
                    sha256: sha256_bytes(&bytes),
                },
            );
        }
    }
    let resources = PlannedResources::plan(&locate_repo_root()?, 1, "stock upstream C example")
        .map_err(|error| error.to_string())?;
    let resource_envelope =
        effective_execution_envelope(&resources.plan, ENFORCEMENT_RSS_WATCHDOG_V1, timeout as f64)
            .map_err(|error| error.to_string())?;
    let compiler_path =
        fs::canonicalize(compiler()).map_err(|error| format!("find stock C compiler: {error}"))?;
    let compiler_sha256 = sha256_file(&compiler_path, "stock C compiler")?;
    let compiler_version = capture(
        &resources,
        &compiler_path,
        &["--version".into()],
        Duration::from_secs(30),
        "compiler-version",
    )?;
    let validator = std::env::current_exe().map_err(|error| error.to_string())?;
    let validator_sha256 = sha256_file(&validator, "stock C runner")?;
    let mut captures = Vec::new();
    let mut retained_binary = BTreeMap::new();
    for (subject, library) in [("z3", &z3.path), ("ay", &ay.path)] {
        for kind in KINDS {
            let id = format!("{subject}.{kind}");
            let mut built = capture(
                &resources,
                &validator,
                &[
                    "smtlib-conformance".into(),
                    "stock-c-build-child".into(),
                    directory.path().as_os_str().to_owned(),
                    kind.into(),
                    subject.into(),
                    library.as_os_str().to_owned(),
                    compiler_path.as_os_str().to_owned(),
                ],
                Duration::from_secs(timeout),
                &format!("build.{id}"),
            )?;
            // Retain exact raw captures. Replay compares checked outcomes;
            // arbitrary model output and compiler paths are not semantic checks.
            let build_passed = built.success();
            built.id = format!("build.{id}");
            captures.push(built);
            if !build_passed {
                continue;
            }
            let binary = directory.path().join(format!("{kind}-{subject}"));
            let binary_sha256 = sha256_file(&binary, "stock C linked consumer")?;
            if let Some(retained) = retained {
                let destination = retained.join(format!("{kind}-{subject}"));
                let bytes = read_bounded_bytes(&binary, LIMIT, "stock C retained binary", true)?;
                atomic_write_new(&destination, &bytes)?;
                retained_binary.insert(
                    id.clone(),
                    Artifact {
                        path: destination.to_string_lossy().into_owned(),
                        sha256: binary_sha256.clone(),
                    },
                );
            }
            let run_directory = directory.path().join(format!("run-{id}"));
            fs::create_dir(&run_directory).map_err(|error| error.to_string())?;
            let output = capture(
                &resources,
                &validator,
                &[
                    "smtlib-conformance".into(),
                    "stock-c-run-child".into(),
                    run_directory.as_os_str().to_owned(),
                    binary.as_os_str().to_owned(),
                ],
                Duration::from_secs(timeout),
                &format!("run.{id}"),
            )?;
            if sha256_file(&binary, "post-run stock C consumer")? != binary_sha256 {
                return Err("stock C consumer changed during execution".to_string());
            }
            captures.push(output);
        }
    }
    let reference_observation = observation(&captures, "z3");
    let ay_observation = observation(&captures, "ay");
    let both = |predicate: fn(&Capture) -> bool, kind: &str| {
        ["z3", "ay"].iter().all(|subject| {
            captures
                .iter()
                .find(|row| row.id == format!("run.{subject}.{kind}"))
                .is_some_and(predicate)
        })
    };
    let assertions_enabled = both(Capture::assertion_aborted, "assertions");
    let wrong_expectation_refused = both(Capture::wrong_expectation_refused, "expected-result");
    if sha256_file(&ay.path, "post-run stock C AY")? != ay_sha256
        || sha256_file(&z3.path, "post-run stock C Z3")?
            != profile.z3_overlay.reference_shared_library.sha256
        || sha256_file(&compiler_path, "post-run stock C compiler")? != compiler_sha256
    {
        return Err("stock C artifact changed during execution".to_string());
    }
    Ok(Report {
        schema: SCHEMA.to_string(), profile_sha256: canonical_profile_sha256()?, source_root: source,
        source_revision: profile.z3_overlay.source_commit, example_path: EXAMPLE.to_string(), example_sha256: EXAMPLE_SHA256.to_string(), header_sha256,
        expected_main_calls: MAIN_CALLS.map(str::to_string).to_vec(), expected_markers: MARKERS.map(str::to_string).to_vec(), expected_final_markers: FINAL_MARKERS.map(str::to_string).to_vec(),
        control_sha256: controls(), compiler: compiler_path, compiler_sha256, compiler_flags: flags(), compiler_version: compiler_version.clone(), retained_source,
        ay_library: Artifact { path: ay_library.to_string_lossy().into_owned(), sha256: ay_sha256 },
        z3_library: Artifact { path: reference.to_string_lossy().into_owned(), sha256: profile.z3_overlay.reference_shared_library.sha256 },
        validator_sha256, timeout_seconds: timeout, resource_envelope, per_file_limit_bytes: LIMIT,
        stock_example_passed: compiler_version.success() && reference_observation.completed && ay_observation.completed && assertions_enabled && wrong_expectation_refused,
        reference: reference_observation, ay: ay_observation, assertions_enabled, wrong_expectation_refused, captures, retained_binary,
        exhaustive_c_semantics_complete: false,
        limitation: "Unmodified pinned examples/c/test_capi.c: 39 main calls, 36 ordered headings, 5 final model checks, explicit upstream failure checks and separate assertion/incorrect-expectation controls. Only the negative incorrect-expectation control renames main to reuse upstream check/exitf. Arbitrary printed models, intermediate answers and compiler diagnostic wording are not independently validated here; this finite example does not close the 817 full-domain C ABI contracts. Captures retain raw bytes; regenerated binary bytes and arbitrary model printing need not be identical on replay.".to_string(),
    })
}

fn validate_observations(report: &Report) -> Result<(), String> {
    let mut expected_ids = Vec::new();
    let mut binaries = BTreeSet::new();
    let has = |id: &str, predicate: fn(&Capture) -> bool| {
        report
            .captures
            .iter()
            .find(|row| row.id == id)
            .is_some_and(predicate)
    };
    for subject in ["z3", "ay"] {
        for kind in KINDS {
            let id = format!("{subject}.{kind}");
            expected_ids.push(format!("build.{id}"));
            if has(&format!("build.{id}"), Capture::success) {
                expected_ids.push(format!("run.{id}"));
                binaries.insert(id);
            }
        }
    }
    if report
        .captures
        .iter()
        .map(|row| row.id.clone())
        .collect::<Vec<_>>()
        != expected_ids
        || report
            .retained_binary
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>()
            != binaries
    {
        return Err("stock C build/execution population mismatch".to_string());
    }
    for row in report
        .captures
        .iter()
        .chain(std::iter::once(&report.compiler_version))
    {
        if row.exit_code.is_some() && row.signal.is_some() {
            return Err("stock C process has both exit code and signal".to_string());
        }
        if sha256_bytes(&row.stdout) != row.stdout_sha256
            || sha256_bytes(&row.stderr) != row.stderr_sha256
        {
            return Err("stock C raw transcript hash drift".to_string());
        }
    }
    if report.compiler_version.id != "compiler-version" {
        return Err("stock C compiler transcript identity drift".to_string());
    }
    let assertions = ["z3", "ay"].iter().all(|subject| {
        has(
            &format!("run.{subject}.assertions"),
            Capture::assertion_aborted,
        )
    });
    let refused = ["z3", "ay"].iter().all(|subject| {
        has(
            &format!("run.{subject}.expected-result"),
            Capture::wrong_expectation_refused,
        )
    });
    let reference = observation(&report.captures, "z3");
    let ay = observation(&report.captures, "ay");
    if report.reference != reference
        || report.ay != ay
        || report.assertions_enabled != assertions
        || report.wrong_expectation_refused != refused
        || report.stock_example_passed
            != (report.compiler_version.success()
                && reference.completed
                && ay.completed
                && assertions
                && refused)
    {
        return Err("stock C completion differs from retained observations".to_string());
    }
    Ok(())
}

pub(super) fn run(args: &[String]) -> Result<i32, String> {
    if args
        .iter()
        .any(|arg| matches!(arg.as_str(), "--help" | "-h"))
    {
        println!("smtlib-conformance stock-c --source DIR --ay-library FILE --out FILE [--timeout SECONDS]\n\nCompile unmodified pinned upstream C consumer with stock headers; require its\ncomplete ordered example census, final model checks and active failure controls.\nRetain linked binaries and raw transcripts. Finite coverage only; C API remains open.\nEach compile/run defaults to 120s; an explicit timeout of 1..3600s is honored.\nThe qualify command separately enforces a 120s minimum for stock consumers.");
        return Ok(0);
    }
    let (mut source, mut library, mut output) = (None, None, None);
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
            _ => return Err(format!("unknown stock-c option {flag}")),
        }
    }
    let output = output.ok_or("stock-c requires --out")?;
    let parent = output
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let retained = parent.join(format!(
        "{}.inputs",
        output
            .file_name()
            .ok_or("stock C output has no filename")?
            .to_string_lossy()
    ));
    fs::create_dir(&retained)
        .map_err(|error| format!("create stock C retained inputs: {error}"))?;
    let retained = fs::canonicalize(retained).map_err(|error| error.to_string())?;
    let report = measure(
        &source.ok_or("stock-c requires --source")?,
        &library.ok_or("stock-c requires --ay-library")?,
        timeout,
        Some(&retained),
    )?;
    validate_observations(&report)?;
    atomic_write_new(&output, &pretty_json(&report)?)?;
    println!("stock_c={} reference_completed={} ay_completed={} assertions_enabled={} wrong_expectation_refused={} exhaustive_c_semantics_complete=false", output.display(), report.reference.completed, report.ay.completed, report.assertions_enabled, report.wrong_expectation_refused);
    Ok(i32::from(!report.stock_example_passed))
}

pub(super) fn check(args: &[String]) -> Result<i32, String> {
    if args.len() != 1 {
        return Err("usage: stock-c-check REPORT".to_string());
    }
    let report: Report = serde_json::from_slice(&read_bounded_bytes(
        Path::new(&args[0]),
        LIMIT,
        "stock C report",
        true,
    )?)
    .map_err(|error| error.to_string())?;
    if report.schema != SCHEMA
        || report.profile_sha256 != canonical_profile_sha256()?
        || report.source_revision != canonical_profile()?.z3_overlay.source_commit
        || report.example_path != EXAMPLE
        || report.example_sha256 != EXAMPLE_SHA256
        || report.compiler_flags != flags()
        || report.control_sha256 != controls()
        || report.expected_main_calls != MAIN_CALLS
        || report.expected_markers != MARKERS
        || report.expected_final_markers != FINAL_MARKERS
        || report.exhaustive_c_semantics_complete
        || report.per_file_limit_bytes != LIMIT
        || !(1..=3600).contains(&report.timeout_seconds)
        || report.z3_library.sha256
            != canonical_profile()?
                .z3_overlay
                .reference_shared_library
                .sha256
        || sha256_file(
            &std::env::current_exe().map_err(|error| error.to_string())?,
            "stock C replay validator",
        )? != report.validator_sha256
        || sha256_file(Path::new(&report.ay_library.path), "stock C replay AY")?
            != report.ay_library.sha256
        || sha256_file(&report.compiler, "stock C replay compiler")? != report.compiler_sha256
    {
        return Err("stock C report identity/scope drift".to_string());
    }
    validate_observations(&report)?;
    let mut expected_source = report.header_sha256.clone();
    expected_source.insert("example.c".to_string(), EXAMPLE_SHA256.to_string());
    expected_source.insert("assertions.c".to_string(), controls()["assertions"].clone());
    expected_source.insert(
        "expected-result.c".to_string(),
        controls()["expected-result"].clone(),
    );
    if report
        .retained_source
        .iter()
        .map(|(name, artifact)| (name.clone(), artifact.sha256.clone()))
        .collect::<BTreeMap<_, _>>()
        != expected_source
    {
        return Err("stock C retained source population/digest drift".to_string());
    }
    let retained_directory = fs::canonicalize(format!("{}.inputs", args[0]))
        .map_err(|error| format!("stock C retained directory: {error}"))?;
    for (name, artifact) in report
        .retained_source
        .iter()
        .chain(report.retained_binary.iter())
    {
        let leaf = if report.retained_source.contains_key(name) {
            name.to_string()
        } else {
            let (subject, kind) = name
                .split_once('.')
                .ok_or("invalid stock C binary identity")?;
            format!("{kind}-{subject}")
        };
        if Path::new(&artifact.path) != retained_directory.join(leaf) {
            return Err(
                "stock C retained artifact path differs from report-owned directory".to_string(),
            );
        }
        validate_sha256(&artifact.sha256, "retained stock C artifact")?;
        if sha256_bytes(&read_bounded_bytes(
            Path::new(&artifact.path),
            LIMIT,
            "retained stock C artifact",
            true,
        )?) != artifact.sha256
        {
            return Err("retained stock C source or binary changed".to_string());
        }
    }
    let fresh = measure(
        &report.source_root,
        Path::new(&report.ay_library.path),
        report.timeout_seconds,
        None,
    )?;
    // Printed arbitrary models may vary. Compare the complete source-fixed
    // execution census and checked results, not arbitrary value formatting.
    if report.header_sha256 != fresh.header_sha256
        || report.compiler != fresh.compiler
        || report.ay_library != fresh.ay_library
        || report.z3_library != fresh.z3_library
        || report.compiler_version != fresh.compiler_version
        || report.compiler_sha256 != fresh.compiler_sha256
        || report.resource_envelope != fresh.resource_envelope
        || report.reference != fresh.reference
        || report.ay != fresh.ay
        || report.assertions_enabled != fresh.assertions_enabled
        || report.wrong_expectation_refused != fresh.wrong_expectation_refused
        || report.stock_example_passed != fresh.stock_example_passed
        || report
            .captures
            .iter()
            .map(replay_status)
            .collect::<Vec<_>>()
            != fresh.captures.iter().map(replay_status).collect::<Vec<_>>()
    {
        return Err("stock C result differs from fresh authenticated replay".to_string());
    }
    println!(
        "stock_c_replay=PASS stock_example_passed={} exhaustive_c_semantics_complete=false",
        fresh.stock_example_passed
    );
    Ok(i32::from(!fresh.stock_example_passed))
}

fn replay_status(row: &Capture) -> (&str, Option<i32>, Option<i32>, [bool; 7]) {
    (
        &row.id,
        row.exit_code,
        row.signal,
        [
            row.timed_out,
            row.memout,
            row.stdin_complete,
            row.stdout_truncated,
            row.stderr_truncated,
            std::str::from_utf8(&row.stdout).is_ok(),
            std::str::from_utf8(&row.stderr).is_ok(),
        ],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    fn output(stdout: &str) -> Capture {
        Capture {
            id: "test".to_string(),
            exit_code: Some(0),
            signal: None,
            timed_out: false,
            memout: false,
            stdin_complete: true,
            stdout_truncated: false,
            stderr_truncated: false,
            stdout: stdout.as_bytes().to_vec(),
            stderr: vec![],
            stdout_sha256: sha256_bytes(stdout.as_bytes()),
            stderr_sha256: sha256_bytes(b""),
        }
    }
    fn complete() -> Capture {
        output(&format!(
            "sat\nZ3 5.3.3.0\n{}\nDeMorgan is valid\n{}\n",
            MARKERS.join("\n"),
            FINAL_MARKERS.join("\n")
        ))
    }
    #[test]
    fn complete_census_and_final_checks_are_required_in_order() {
        assert!(complete().example_observation().completed);
        for marker in MARKERS {
            let text = String::from_utf8(complete().stdout).unwrap();
            assert!(
                !output(&text.replacen(&format!("{marker}\n"), "", 1))
                    .example_observation()
                    .completed,
                "missing {marker}"
            );
            assert!(
                !output(&text.replacen(marker, &format!("{marker}\n{marker}"), 1))
                    .example_observation()
                    .completed,
                "duplicate {marker}"
            );
        }
        let text = String::from_utf8(complete().stdout).unwrap();
        assert!(
            !output(&text.replace("Evaluated a + b = 3", "Evaluated a + b = 4"))
                .example_observation()
                .completed
        );
        assert!(
            !output(&text.replace(
                "Evaluated c[0] + c[1] + c[2] = 7",
                "Evaluated c[0] + c[1] + c[2] = 6"
            ))
            .example_observation()
            .completed
        );
        assert!(
            !output(&text.replace("simple_example\nDeMorgan", "DeMorgan\nsimple_example"))
                .example_observation()
                .completed
        );
    }

    #[test]
    fn intentional_upstream_error_output_is_not_an_extra_version_witness() {
        let text = String::from_utf8(complete().stdout).unwrap();
        let text = text.replace("Z3 5.3.3.0\n", "Z3 5.3.3.0\nZ3 error: Sorts Int and Bool are incompatible.\nZ3 error: (error \"invalid command\").\n");
        assert!(output(&text).example_observation().completed);
        assert!(!numeric_version_line("Z3 error: 5.3.3.0"));
        for invalid in [
            "Z3 5.3.3",
            "Z3 5.3.3.0.1",
            "Z3 5.3.error.0",
            "Z3 5.3.3.4294967296",
        ] {
            assert!(!numeric_version_line(invalid));
            assert!(
                !output(&text.replace("Z3 5.3.3.0", invalid))
                    .example_observation()
                    .completed
            );
        }
        assert!(
            !output(&format!("Z3 5.3.3.0\n{text}"))
                .example_observation()
                .completed
        );
    }
    #[test]
    fn exit_zero_loader_failure_and_partial_output_cannot_pass() {
        assert!(!output("").example_observation().completed);
        let mut row = complete();
        row.timed_out = true;
        assert!(!row.example_observation().completed);
        let mut row = complete();
        row.stdout_truncated = true;
        assert!(!row.example_observation().completed);
        let mut row = complete();
        row.stderr = b"BUG: unexpected result.\n".to_vec();
        assert!(!row.example_observation().completed);
        let mut row = output("");
        row.exit_code = None;
        row.signal = Some(6);
        row.stderr = b"dyld: missing library\n".to_vec();
        assert!(!row.assertion_aborted());
        row.stderr = format!("{ASSERTION_MARKER}\nAssertion failed\n").into_bytes();
        assert!(row.assertion_aborted());
        row.signal = None;
        row.exit_code = Some(0);
        assert!(!row.assertion_aborted());
    }
    #[test]
    fn wrong_expectation_control_requires_upstream_failure_after_reaching_check() {
        let mut row = output("sat\n\n");
        row.exit_code = Some(1);
        row.stderr = format!("{RESULT_MARKER}\nBUG: unexpected result.\n").into_bytes();
        assert!(row.wrong_expectation_refused());
        row.exit_code = Some(0);
        assert!(!row.wrong_expectation_refused());
        row.exit_code = Some(1);
        row.stderr = b"BUG: unexpected result.\n".to_vec();
        assert!(!row.wrong_expectation_refused());
        row.stderr = format!("{RESULT_MARKER}\nBUG: incorrect use of Z3.\n").into_bytes();
        assert!(!row.wrong_expectation_refused());
    }

    fn failed_report() -> Report {
        let mut captures = Vec::new();
        for subject in ["z3", "ay"] {
            for kind in KINDS {
                let mut row = output("");
                row.id = format!("build.{subject}.{kind}");
                row.exit_code = Some(1);
                captures.push(row);
            }
        }
        let mut version = output("compiler version\n");
        version.id = "compiler-version".to_string();
        Report {
            schema: SCHEMA.to_string(),
            profile_sha256: String::new(),
            source_root: PathBuf::new(),
            source_revision: String::new(),
            example_path: EXAMPLE.to_string(),
            example_sha256: EXAMPLE_SHA256.to_string(),
            header_sha256: BTreeMap::new(),
            expected_main_calls: MAIN_CALLS.map(str::to_string).to_vec(),
            expected_markers: MARKERS.map(str::to_string).to_vec(),
            expected_final_markers: FINAL_MARKERS.map(str::to_string).to_vec(),
            control_sha256: controls(),
            compiler: PathBuf::new(),
            compiler_sha256: String::new(),
            compiler_version: version,
            compiler_flags: flags(),
            retained_source: BTreeMap::new(),
            ay_library: Artifact {
                path: String::new(),
                sha256: String::new(),
            },
            z3_library: Artifact {
                path: String::new(),
                sha256: String::new(),
            },
            validator_sha256: String::new(),
            timeout_seconds: 1,
            resource_envelope: String::new(),
            per_file_limit_bytes: LIMIT,
            reference: observation(&captures, "z3"),
            ay: observation(&captures, "ay"),
            captures,
            retained_binary: BTreeMap::new(),
            assertions_enabled: false,
            wrong_expectation_refused: false,
            stock_example_passed: false,
            exhaustive_c_semantics_complete: false,
            limitation: String::new(),
        }
    }

    #[test]
    fn failed_evidence_cannot_be_promoted_or_lose_required_rows() {
        let report = failed_report();
        validate_observations(&report).unwrap();
        let mut changed = report.clone();
        changed.stock_example_passed = true;
        assert!(validate_observations(&changed).is_err());
        let mut changed = report.clone();
        changed.captures.remove(0);
        assert!(validate_observations(&changed).is_err());
        let mut changed = report.clone();
        changed.captures.swap(0, 1);
        assert!(validate_observations(&changed).is_err());
        let mut changed = report.clone();
        changed.captures[0].stdout.push(b'x');
        assert!(validate_observations(&changed).is_err());
        let mut changed = report.clone();
        let mut fake_run = complete();
        fake_run.id = "run.z3.example".to_string();
        changed.captures.push(fake_run);
        assert!(validate_observations(&changed).is_err());
        let mut changed = report;
        changed.captures[0].signal = Some(6);
        assert!(validate_observations(&changed).is_err());
    }

    #[test]
    fn changed_source_cannot_rebaseline_its_expected_hash() {
        let source = tempfile::tempdir().unwrap();
        let staged = tempfile::tempdir().unwrap();
        fs::create_dir_all(source.path().join("examples/c")).unwrap();
        let bytes = b"int main(void) { return 0; }\n";
        fs::write(source.path().join(EXAMPLE), bytes).unwrap();
        let inventory = json!({"source_files": [{"path": EXAMPLE, "sha256": sha256_bytes(bytes)}]});
        assert!(snapshot_sources(source.path(), &inventory, staged.path()).is_err());
    }

    #[test]
    fn resource_failure_categories_and_invalid_bytes_survive_replay_comparison() {
        let mut row = output("");
        row.timed_out = true;
        let timed_out = replay_status(&row);
        let mut changed = row.clone();
        changed.timed_out = false;
        changed.memout = true;
        assert_ne!(timed_out, replay_status(&changed));
        changed.memout = false;
        changed.stdout = vec![0xff];
        assert!(!changed.bounded());
        assert_ne!(replay_status(&output("")), replay_status(&changed));
    }
}
