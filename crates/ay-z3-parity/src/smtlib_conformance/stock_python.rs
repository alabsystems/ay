// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exercise unmodified upstream z3py against each provider. The embedded Python
//! is a consumer test, not an alternate binding or campaign orchestrator.
use super::*;
use std::ffi::OsString;

const SCHEMA: &str = "ay-stock-z3py-consumer/v2";
const FILES: &[(&str, &str)] = &[
    (
        "__init__.py",
        "54e1833c2df2ca01c33b487180f75580eab8364dc1800a259263b64310069bf3",
    ),
    (
        "z3.py",
        "c36442f9b29d54e8ee220c1ec3b0e9e2c8f3ca63e5d92cea089306dc220a4898",
    ),
    (
        "z3consts.py",
        "648f64a6dedf2fcb5fd899f58d3a2e52f60fd8a6b1cda322315207a43276a977",
    ),
    (
        "z3core.py",
        "919f8057ccc75d9f46ed77375a46be59c350385711b57cb65fd60ef3d7173d03",
    ),
    (
        "z3num.py",
        "b099dee2352be581ef96fbedc183ac324f03002ee7cf71fbebf6aa1355cd4341",
    ),
    (
        "z3poly.py",
        "fd06029418e5899b300fe3b3a300d110c8e174e633cba8b751314f22a583394e",
    ),
    (
        "z3printer.py",
        "0962d30b9543e04f0bdd4636d91983973a604d6ab2b76a028300db37dfa0154e",
    ),
    (
        "z3rcf.py",
        "504e0339b1bb06075c19ca52e51457716671218a2f2191d0c9754e0b75bede87",
    ),
    (
        "z3regex.py",
        "4f64903cce356c6fb541041d9c50ce70c8d12a0824592611d87bd603290f83e4",
    ),
    (
        "z3test.py",
        "398c5c3404fe8ddd1c56836620808592bbf46a0691e1a3ffd39e1b5746e6029a",
    ),
    (
        "z3types.py",
        "ba728354b4a9ee40bcfbd899f405d904bc4bb023e41807044c06c318548c3080",
    ),
    (
        "z3util.py",
        "bd1b436749b0d7700100a6a49fd09f09975c025f156925fc8805ac99e6db50f8",
    ),
];

fn binding_digest<'a>(name: &str, common: &'a str) -> Result<&'a str, String> {
    Ok(binding_digest_for(
        reference_platform::Platform::native()?,
        name,
        common,
    ))
}

fn binding_digest_for<'a>(
    platform: reference_platform::Platform,
    name: &str,
    common: &'a str,
) -> &'a str {
    if name == "z3core.py" {
        platform.python_core_sha256()
    } else {
        common
    }
}
const CASES: &[&str] = &[
    "import",
    "solver-isolation",
    "incremental",
    "retained-model",
    "translation",
    "lifetime",
    "invalid-sorts",
    "optimization",
    "fixedpoint",
];
const DOCTESTS: &[&str] = &["doctest-z3", "doctest-z3num", "doctest-z3regex"];
const DRIVER: &str = r#"import sys, os, builtins, json, gc, ctypes
sys.dont_write_bytecode = True
bindings, library, case = sys.argv[1:]
for key in ('PATH', 'PYTHONPATH', 'Z3_LIBRARY_PATH'):
    os.environ.pop(key, None)
sys.path.insert(0, bindings)
builtins.Z3_LIB_DIRS = [os.path.dirname(library)]
loads = []
def audit(event, args):
    if event == 'ctypes.dlopen':
        if not args or not isinstance(args[0], str) or not os.path.samefile(args[0], library):
            raise RuntimeError('foreign native provider')
        loads.append(os.path.realpath(args[0]))
sys.addaudithook(audit)
try:
    import z3
    assert loads == [os.path.realpath(library)], 'native provider was not observed'
    assert os.path.samefile(z3.__file__, os.path.join(bindings, 'z3', '__init__.py')), 'foreign z3py'
    c = z3.Context()
    if case.startswith('doctest-'):
        import doctest, runpy, importlib, warnings
        name = case[len('doctest-'):]
        assert name in ('z3', 'z3num', 'z3regex'), 'unknown upstream suite'
        module = importlib.import_module('z3.' + name)
        examples = [example for test in doctest.DocTestFinder().find(module) for example in test.examples]
        skipped = sum(bool(example.options.get(doctest.SKIP, False)) for example in examples)
        sys.argv = ['z3test.py', name]
        upstream_exit = 0
        with warnings.catch_warnings(record=True) as observed_warnings:
            try:
                runpy.run_module('z3.z3test', run_name='__main__')
            except SystemExit as error:
                upstream_exit = error.code if isinstance(error.code, int) else int(error.code is not None)
        assert doctest.master is not None, 'upstream runner produced no doctest result'
        result = doctest.master.summarize(verbose=False)
        warning_rows = [{'category': w.category.__name__, 'message': str(w.message), 'filename': w.filename, 'line': w.lineno} for w in observed_warnings]
        print('AY_Z3PY_DOCTEST ' + json.dumps({'module': name, 'attempted': result.attempted, 'failed': result.failed, 'skipped': skipped, 'discovered': len(examples), 'upstream_exit': upstream_exit, 'warnings': warning_rows}, sort_keys=True))
        assert upstream_exit == 0 and result.failed == 0, 'upstream doctest expectations failed'
        assert len(examples) > 0 and skipped == 0 and result.attempted == len(examples), 'upstream doctest coverage incomplete'
    elif case == 'import':
        assert z3.IntVal(7, c).as_long() == 7
    elif case == 'solver-isolation':
        x = z3.Int('x', c)
        a, b = z3.Solver(ctx=c), z3.Solver(ctx=c)
        a.add(x == 1)
        b.add(x == 2)
        assert a.check() == z3.sat and a.model().eval(x).as_long() == 1
        assert b.check() == z3.sat and b.model().eval(x).as_long() == 2
    elif case == 'incremental':
        x = z3.Int('x', c)
        a, b = z3.Solver(ctx=c), z3.Solver(ctx=c)
        a.add(x == 1)
        b.add(x == 2)
        a.push()
        a.add(x == 3)
        assert a.check() == z3.unsat
        assert b.check() == z3.sat
        a.pop()
        assert a.check() == z3.sat and a.model().eval(x).as_long() == 1
        b.reset()
        b.add(x == 4)
        assert b.check() == z3.sat and b.model().eval(x).as_long() == 4
        assert a.check() == z3.sat and a.model().eval(x).as_long() == 1
    elif case == 'retained-model':
        x = z3.Int('x', c)
        a = z3.Solver(ctx=c)
        a.add(x == 1)
        assert a.check() == z3.sat
        old = a.model()
        a.push()
        a.add(x == 2)
        assert a.check() == z3.unsat
        assert old.eval(x).as_long() == 1
        a.pop()
        a.reset()
        a.add(x == 3)
        assert a.check() == z3.sat and a.model().eval(x).as_long() == 3
        assert old.eval(x).as_long() == 1
    elif case == 'translation':
        x = z3.Int('x', c)
        a = z3.Solver(ctx=c)
        a.add(x == 9)
        other = z3.Context()
        translated = a.translate(other)
        y = x.translate(other)
        del a
        gc.collect()
        assert translated.check() == z3.sat
        assert translated.model().eval(y).as_long() == 9
    elif case == 'lifetime':
        x = z3.Int('x', c)
        a = z3.Solver(ctx=c)
        terms = [x == k for k in range(40)]
        formula = z3.Or(*terms)
        a.add(formula, x > 37)
        del terms, formula
        gc.collect()
        assert a.check() == z3.sat
        model = a.model()
        del a
        gc.collect()
        assert model.eval(x).as_long() in (38, 39)
    elif case == 'invalid-sorts':
        try:
            z3.parse_smt2_string('(declare-const x Int)(assert (and x true))', ctx=c)
        except z3.Z3Exception:
            pass
        else:
            raise AssertionError('ill-sorted assertion accepted')
        a = z3.Solver(ctx=c)
        a.add(z3.Int('x', c) == 5)
        assert a.check() == z3.sat
    elif case == 'optimization':
        x = z3.Int('x', c)
        a = z3.Optimize(ctx=c)
        a.add(x >= 0, x <= 4)
        objective = a.maximize(x)
        assert a.check() == z3.sat
        assert a.model().eval(x).as_long() == 4
        assert objective.value().as_long() == 4
    elif case == 'fixedpoint':
        x = z3.Int('x', c)
        p = z3.Function('p', z3.IntSort(c), z3.BoolSort(c))
        a = z3.Fixedpoint(ctx=c)
        a.register_relation(p)
        a.declare_var(x)
        a.fact(p(0))
        a.rule(p(x + 1), [p(x), x < 2])
        assert a.query(p(2)) == z3.sat
    else:
        raise AssertionError('unknown consumer case')
    print(json.dumps({'case': case, 'result': 'pass'}, sort_keys=True))
except BaseException as error:
    print(json.dumps({'case': case, 'result': 'fail', 'type': type(error).__name__, 'detail': str(error)}, sort_keys=True))
    sys.exit(1)
"#;

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct Capture {
    case: String,
    subject: String,
    exit: Option<i32>,
    stdin_complete: bool,
    timed_out: bool,
    memout: bool,
    stdout_truncated: bool,
    stderr_truncated: bool,
    stdout: String,
    stderr: String,
    doctest: Option<DoctestCounts>,
    passed: bool,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct DoctestCounts {
    module: String,
    attempted: usize,
    failed: usize,
    skipped: usize,
    discovered: usize,
    upstream_exit: i32,
    warnings: Vec<DoctestWarning>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct DoctestWarning {
    category: String,
    message: String,
    filename: String,
    line: usize,
}

impl DoctestCounts {
    fn passed(&self, case: &str) -> bool {
        let expected = match case {
            "doctest-z3" => 2355,
            "doctest-z3num" => 118,
            "doctest-z3regex" => 7,
            _ => return false,
        };
        case.strip_prefix("doctest-") == Some(self.module.as_str())
            && self.discovered == expected
            && self.attempted == self.discovered
            && self.failed == 0
            && self.skipped == 0
            && self.upstream_exit == 0
    }
}

fn doctest_counts(stdout: &str) -> Option<DoctestCounts> {
    let mut reports = stdout
        .lines()
        .filter_map(|line| line.strip_prefix("AY_Z3PY_DOCTEST "));
    let counts = serde_json::from_str(reports.next()?).ok()?;
    reports.next().is_none().then_some(counts)
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct Report {
    schema: String,
    profile_sha256: String,
    validator_sha256: String,
    source_revision: String,
    upstream_archive_sha256: String,
    python: Artifact,
    python_version: String,
    bindings: PathBuf,
    binding_sha256: BTreeMap<String, String>,
    driver: Artifact,
    ay_library: Artifact,
    z3_library: Artifact,
    timeout_seconds: u64,
    resource_envelope: String,
    cases: Vec<Capture>,
    fragment_passed: bool,
    exhaustive: bool,
    full_replacement_ready: bool,
}

pub(super) fn run(args: &[String]) -> Result<i32, String> {
    if args.iter().any(|arg| arg == "--help" || arg == "-h") {
        println!("smtlib-conformance stock-python --ay-library FILE --directory NEW [--bindings Z3_PACKAGE_DIR] [--python FILE] [--timeout SECONDS]\nRuns unmodified release-pinned z3py against both providers in isolated processes.\nNine consumer controls plus all three suites dispatched by upstream z3test.py\n(z3, z3num, z3regex). Reports attempted/failed/discovered/skipped counts; zero\ntests, skipped examples, errors or timeouts fail. --timeout applies per child.\nUpstream bindings are downloaded when absent. Exit 0 means this finite suite\npasses, never full API coverage. Replay with stock-python-check REPORT.");
        return Ok(0);
    }
    reference_platform::Platform::native()?;
    let mut ay = None;
    let mut directory = None;
    let mut bindings = None;
    let mut python = PathBuf::from("python3");
    // Whole upstream modules contain thousands of examples; their process
    // deadline is distinct from a single SMT-LIB query deadline.
    let mut timeout = 120u64;
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        let value = args.next().ok_or_else(|| format!("{arg} needs a value"))?;
        match arg.as_str() {
            "--ay-library" => ay = Some(PathBuf::from(value)),
            "--directory" => directory = Some(PathBuf::from(value)),
            "--bindings" => bindings = Some(PathBuf::from(value)),
            "--python" => python = PathBuf::from(value),
            "--timeout" => timeout = value.parse().map_err(|_| "invalid timeout")?,
            _ => return Err(format!("unknown stock-python option {arg}")),
        }
    }
    if !(1..=3600).contains(&timeout) {
        return Err("timeout must be 1..3600 seconds".to_string());
    }
    let ay = ay.ok_or("stock-python requires --ay-library")?;
    let directory = directory.ok_or("stock-python requires --directory")?;
    fs::create_dir(&directory)
        .map_err(|error| format!("create fresh consumer directory: {error}"))?;
    let directory = fs::canonicalize(directory).map_err(|error| error.to_string())?;
    let resources = PlannedResources::plan(&locate_repo_root()?, 1, "stock z3py consumers")
        .map_err(|error| error.to_string())?;
    let bindings = prepare_bindings(&directory, bindings.as_deref(), &resources)?;
    let driver = directory.join("driver.py");
    atomic_write_new(&driver, DRIVER.as_bytes())?;
    let ay = retain_library(&ay, &directory.join("ay"), None)?;
    let target = &canonical_profile()?.z3_overlay.reference_shared_library;
    let z3 = retain_library(
        &reference_artifact_path(&target.path)?,
        &directory.join("z3"),
        Some(&target.sha256),
    )?;
    let report = measure(
        &python, &bindings, &driver, ay, z3, timeout, None, &resources,
    )?;
    atomic_write_new(&directory.join("stock-python.json"), &pretty_json(&report)?)?;
    println!(
        "stock_python_fragment_passed={} consumer_cases={} upstream_suites={} exhaustive=false full_replacement_ready=false",
        report.fragment_passed,
        CASES.len(), DOCTESTS.len()
    );
    for capture in &report.cases {
        if let Some(counts) = &capture.doctest {
            println!("stock_python_doctest subject={} module={} attempted={} failed={} skipped={} discovered={} warnings={}", capture.subject, counts.module, counts.attempted, counts.failed, counts.skipped, counts.discovered, counts.warnings.len());
        }
    }
    Ok(i32::from(!report.fragment_passed))
}

pub(super) fn check(args: &[String]) -> Result<i32, String> {
    if args.len() != 1 {
        return Err("stock-python-check requires one report".to_string());
    }
    let bytes = read_bounded_bytes(
        Path::new(&args[0]),
        4 * 1024 * 1024,
        "stock Python report",
        true,
    )?;
    let recorded: Report = serde_json::from_slice(&bytes).map_err(|error| error.to_string())?;
    if recorded.schema != SCHEMA
        || recorded.exhaustive
        || recorded.full_replacement_ready
        || recorded.profile_sha256 != canonical_profile_sha256()?
        || recorded.source_revision != canonical_profile()?.z3_overlay.source_commit
        || recorded.upstream_archive_sha256 != reference_platform::Release::native()?.archive_sha256
        || !(1..=3600).contains(&recorded.timeout_seconds)
        || recorded.driver.sha256 != sha256_bytes(DRIVER.as_bytes())
    {
        return Err("stock Python report scope/profile/driver drift".to_string());
    }
    verify_artifact(&recorded.driver, Path::new("."), "consumer driver")?;
    verify_artifact(&recorded.python, Path::new("."), "Python interpreter")?;
    let resources = PlannedResources::plan(&locate_repo_root()?, 1, "stock z3py replay")
        .map_err(|error| error.to_string())?;
    let fresh = measure(
        Path::new(&recorded.python.path),
        &recorded.bindings,
        Path::new(&recorded.driver.path),
        recorded.ay_library.clone(),
        recorded.z3_library.clone(),
        recorded.timeout_seconds,
        Some(&recorded.resource_envelope),
        &resources,
    )?;
    if fresh != recorded {
        return Err("stock Python report differs from fresh executable replay".to_string());
    }
    println!(
        "stock_python_replay=PASS fragment_passed={} exhaustive=false",
        fresh.fragment_passed
    );
    Ok(i32::from(!fresh.fragment_passed))
}

fn retained(path: &Path) -> Result<Artifact, String> {
    Ok(Artifact {
        path: fs::canonicalize(path)
            .map_err(|e| e.to_string())?
            .to_string_lossy()
            .into_owned(),
        sha256: sha256_file(path, "consumer artifact")?,
    })
}

fn retain_library(
    source: &Path,
    directory: &Path,
    required: Option<&str>,
) -> Result<Artifact, String> {
    let digest = sha256_file(source, "native provider")?;
    if required.is_some_and(|expected| digest != expected) {
        return Err("reference provider hash mismatch".to_string());
    }
    fs::create_dir(directory).map_err(|e| e.to_string())?;
    let target = directory.join(reference_platform::Platform::native()?.python_library_name());
    fs::copy(source, &target).map_err(|e| e.to_string())?;
    let artifact = retained(&target)?;
    if artifact.sha256 != digest {
        return Err("provider changed during retention".to_string());
    }
    Ok(artifact)
}

fn complete(output: &GuardedTranscriptOutput) -> bool {
    output
        .status
        .as_ref()
        .is_some_and(|status| status.success())
        && output.stdin_complete
        && !output.timed_out
        && !output.memout
        && !output.stdout_truncated
        && !output.stderr_truncated
}

fn measure(
    python: &Path,
    bindings: &Path,
    driver: &Path,
    ay: Artifact,
    z3: Artifact,
    timeout: u64,
    expected_envelope: Option<&str>,
    resources: &PlannedResources,
) -> Result<Report, String> {
    if read_bounded_bytes(driver, 64 * 1024, "consumer driver", true)? != DRIVER.as_bytes() {
        return Err("consumer driver differs from the compiled test definition".to_string());
    }
    let binding_sha256 = authenticate_bindings(bindings)?;
    verify_artifact(&ay, Path::new("."), "AY provider")?;
    verify_artifact(&z3, Path::new("."), "Z3 provider")?;
    if z3.sha256
        != canonical_profile()?
            .z3_overlay
            .reference_shared_library
            .sha256
    {
        return Err("foreign reference provider".to_string());
    }
    let identity = resources
        .run_external_transcript_scrubbed(
            python,
            [
                "-I",
                "-S",
                "-c",
                "import sys; print(sys.executable); print(sys.version)",
            ],
            b"",
            Duration::from_secs(timeout),
            "stock Python identity",
        )
        .map_err(|e| e.to_string())?;
    if !complete(&identity) || !identity.stderr.is_empty() {
        return Err("Python identity query failed".to_string());
    }
    let identity = String::from_utf8(identity.stdout).map_err(|e| e.to_string())?;
    let (python_path, python_version) = identity
        .trim_end()
        .split_once('\n')
        .ok_or("missing Python runtime identity")?;
    let python = retained(Path::new(python_path))?;
    let envelope =
        effective_execution_envelope(&resources.plan, ENFORCEMENT_RSS_WATCHDOG_V1, timeout as f64)
            .map_err(|e| e.to_string())?;
    if expected_envelope.is_some_and(|value| value != envelope) {
        return Err("stock Python resource envelope drift".to_string());
    }
    let mut cases = Vec::new();
    for case in CASES.iter().chain(DOCTESTS.iter()) {
        for (subject, library) in [("z3", &z3), ("ay", &ay)] {
            let args: Vec<OsString> = vec![
                "-I".into(),
                "-S".into(),
                driver.as_os_str().to_owned(),
                bindings.as_os_str().to_owned(),
                library.path.clone().into(),
                (*case).into(),
            ];
            let label = format!("stock z3py consumer case={case} subject={subject}");
            let output = match resources.run_external_transcript_scrubbed_with_file_limit(
                &python.path,
                args,
                b"",
                Duration::from_secs(timeout),
                &label,
                1024 * 1024,
            ) {
                Ok(output) => output,
                Err(error) => {
                    let error = format!("{label}: {error}");
                    // A supervision failure may invalidate admission. Stop
                    // issuing work, but retain the completed observations as
                    // explicitly partial diagnostics, never a passing receipt.
                    let directory = driver.parent().unwrap_or_else(|| Path::new("."));
                    return Err(match retain_partial_diagnostic(directory, &cases, case, subject, &error, &envelope) {
                        Ok(path) => format!("{error}; partial_diagnostic={}", path.display()),
                        Err(retention_error) => format!("{error}; partial diagnostic could not be retained: {retention_error}"),
                    });
                }
            };
            let expected = format!("{{\"case\": \"{case}\", \"result\": \"pass\"}}");
            let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
            let doctest = doctest_counts(&stdout);
            let content_passed = if case.starts_with("doctest-") {
                doctest.as_ref().is_some_and(|counts| counts.passed(case))
                    && stdout.lines().last() == Some(expected.as_str())
            } else {
                stdout == format!("{expected}\n") && doctest.is_none()
            };
            let passed = complete(&output) && output.stderr.is_empty() && content_passed;
            cases.push(Capture {
                case: (*case).to_string(),
                subject: subject.to_string(),
                exit: output.status.and_then(|s| s.code()),
                stdin_complete: output.stdin_complete,
                timed_out: output.timed_out,
                memout: output.memout,
                stdout_truncated: output.stdout_truncated,
                stderr_truncated: output.stderr_truncated,
                stdout,
                stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
                doctest,
                passed,
            });
        }
    }
    verify_artifact(&python, Path::new("."), "Python after consumer run")?;
    verify_artifact(&ay, Path::new("."), "AY after consumer run")?;
    verify_artifact(&z3, Path::new("."), "Z3 after consumer run")?;
    if authenticate_bindings(bindings)? != binding_sha256 {
        return Err("bindings changed during run".to_string());
    }
    if read_bounded_bytes(driver, 64 * 1024, "consumer driver", true)? != DRIVER.as_bytes() {
        return Err("consumer driver changed during run".to_string());
    }
    Ok(Report {
        schema: SCHEMA.to_string(),
        profile_sha256: canonical_profile_sha256()?,
        validator_sha256: sha256_file(
            &std::env::current_exe().map_err(|e| e.to_string())?,
            "validator",
        )?,
        source_revision: canonical_profile()?.z3_overlay.source_commit,
        upstream_archive_sha256: reference_platform::Release::native()?
            .archive_sha256
            .to_string(),
        python,
        python_version: python_version.to_string(),
        bindings: bindings.to_path_buf(),
        binding_sha256,
        driver: retained(driver)?,
        ay_library: ay,
        z3_library: z3,
        timeout_seconds: timeout,
        resource_envelope: envelope,
        fragment_passed: cases.iter().all(|case| case.passed),
        cases,
        exhaustive: false,
        full_replacement_ready: false,
    })
}

fn retain_partial_diagnostic(
    directory: &Path,
    completed: &[Capture],
    case: &str,
    subject: &str,
    error: &str,
    envelope: &str,
) -> Result<PathBuf, String> {
    let path = directory.join(format!(
        "stock-python-partial-{}-{}.json",
        std::process::id(),
        unix_time_ms()?
    ));
    let diagnostic = serde_json::json!({
        "schema": "ay-stock-z3py-partial-diagnostic/v1",
        "profile_sha256": canonical_profile_sha256()?,
        "resource_envelope": envelope,
        "completed_cases": completed,
        "failed_case": case,
        "failed_subject": subject,
        "error": error,
        "fragment_passed": false,
        "exhaustive": false,
        "full_replacement_ready": false,
    });
    atomic_write_new(&path, &pretty_json(&diagnostic)?)?;
    Ok(path)
}

fn authenticate_bindings(root: &Path) -> Result<BTreeMap<String, String>, String> {
    let package = root.join("z3");
    let roots = fs::read_dir(root)
        .map_err(|error| error.to_string())?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| error.to_string())?;
    if roots.len() != 1 || roots[0].file_name() != "z3" {
        return Err("unexpected module in upstream import root".to_string());
    }
    let metadata = fs::symlink_metadata(&package).map_err(|error| error.to_string())?;
    if !metadata.file_type().is_dir() || metadata.file_type().is_symlink() {
        return Err("upstream package must be a regular directory".to_string());
    }
    let mut found = BTreeMap::new();
    for entry in fs::read_dir(&package).map_err(|e| e.to_string())? {
        let entry = entry.map_err(|e| e.to_string())?;
        let name = entry
            .file_name()
            .into_string()
            .map_err(|_| "non-UTF-8 binding path")?;
        let expected = FILES
            .iter()
            .find(|(file, _)| *file == name)
            .ok_or("unexpected file in upstream binding package")?
            .1;
        let expected = binding_digest(&name, expected)?;
        let bytes = read_bounded_bytes(&entry.path(), 1024 * 1024, "upstream Python source", true)?;
        let digest = sha256_bytes(&bytes);
        if digest != expected {
            return Err(format!("upstream binding digest mismatch: {name}"));
        }
        found.insert(name, digest);
    }
    if found.len() != FILES.len() {
        return Err("incomplete upstream Python binding package".to_string());
    }
    Ok(found)
}

fn prepare_bindings(
    directory: &Path,
    provided: Option<&Path>,
    resources: &PlannedResources,
) -> Result<PathBuf, String> {
    let root = directory.join("upstream");
    let package = root.join("z3");
    fs::create_dir_all(&package).map_err(|e| e.to_string())?;
    if let Some(source) = provided {
        for (name, expected) in FILES {
            let bytes = read_bounded_bytes(
                &source.join(name),
                1024 * 1024,
                "upstream Python source",
                true,
            )?;
            if sha256_bytes(&bytes) != binding_digest(name, expected)? {
                return Err(format!("provided binding differs: {name}"));
            }
            atomic_write_new(&package.join(name), &bytes)?;
        }
    } else {
        let release = reference_platform::Release::native()?;
        let archive = directory.join(release.archive);
        let url = format!(
            "https://github.com/Z3Prover/z3/releases/download/z3-5.3.3/{}",
            release.archive
        );
        let args: Vec<OsString> = vec![
            "--fail".into(),
            "--location".into(),
            "--silent".into(),
            "--show-error".into(),
            "--proto".into(),
            "=https".into(),
            "--proto-redir".into(),
            "=https".into(),
            "--connect-timeout".into(),
            "30".into(),
            "--max-time".into(),
            "540".into(),
            "--max-filesize".into(),
            release.archive_size.to_string().into(),
            "--output".into(),
            archive.as_os_str().to_owned(),
            url.into(),
        ];
        let output = resources
            .run_external_transcript_scrubbed(
                "curl",
                args,
                b"",
                Duration::from_secs(600),
                "upstream z3py acquisition",
            )
            .map_err(|e| e.to_string())?;
        if !complete(&output)
            || fs::metadata(&archive).map_err(|e| e.to_string())?.len() != release.archive_size
            || sha256_file(&archive, "upstream archive")? != release.archive_sha256
        {
            return Err("upstream Python archive download failed authentication".to_string());
        }
        for (name, expected) in FILES {
            let output = resources
                .run_external_transcript_scrubbed(
                    "unzip",
                    [
                        OsString::from("-p"),
                        archive.as_os_str().to_owned(),
                        release.member(&format!("python/z3/{name}")).into(),
                    ],
                    b"",
                    Duration::from_secs(30),
                    "extract authenticated upstream binding",
                )
                .map_err(|e| e.to_string())?;
            if !complete(&output)
                || !output.stderr.is_empty()
                || sha256_bytes(&output.stdout) != binding_digest(name, expected)?
            {
                return Err(format!("upstream binding extraction failed: {name}"));
            }
            atomic_write_new(&package.join(name), &output.stdout)?;
        }
    }
    authenticate_bindings(&root)?;
    Ok(root)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn generated_python_shim_is_authenticated_for_its_native_platform() {
        use reference_platform::Platform;
        let darwin = binding_digest_for(Platform::MacosArm64, "z3core.py", "unused");
        let linux = binding_digest_for(Platform::LinuxX86_64, "z3core.py", "unused");
        assert_ne!(darwin, linux);
        assert_eq!(
            linux,
            binding_digest_for(Platform::LinuxArm64, "z3core.py", "unused")
        );
        assert_eq!(
            darwin,
            binding_digest_for(Platform::MacosX86_64, "z3core.py", "unused")
        );
        for platform in Platform::ALL {
            assert_eq!(
                binding_digest_for(platform, "z3.py", "source digest"),
                "source digest"
            );
        }
    }

    #[test]
    fn altered_binding_is_refused_before_execution() {
        let temp = tempfile::tempdir().unwrap();
        fs::create_dir(temp.path().join("z3")).unwrap();
        fs::write(temp.path().join("z3/z3core.py"), "print('pass')").unwrap();
        assert!(authenticate_bindings(temp.path()).is_err());
    }
    #[test]
    fn missing_binding_is_refused_before_execution() {
        let temp = tempfile::tempdir().unwrap();
        fs::create_dir(temp.path().join("z3")).unwrap();
        assert!(authenticate_bindings(temp.path()).is_err());
    }

    #[test]
    fn shadowing_module_outside_the_package_is_refused() {
        let temp = tempfile::tempdir().unwrap();
        fs::create_dir(temp.path().join("z3")).unwrap();
        fs::write(temp.path().join("ctypes.py"), "raise SystemExit(0)").unwrap();
        assert!(authenticate_bindings(temp.path())
            .unwrap_err()
            .contains("unexpected module in upstream import root"));
    }

    #[test]
    fn zero_shortened_skipped_or_failed_upstream_suites_cannot_pass() {
        let mut counts = DoctestCounts {
            module: "z3regex".to_string(),
            attempted: 7,
            failed: 0,
            skipped: 0,
            discovered: 7,
            upstream_exit: 0,
            warnings: vec![],
        };
        assert!(counts.passed("doctest-z3regex"));
        counts.attempted = 0;
        assert!(!counts.passed("doctest-z3regex"));
        counts.discovered = 0;
        assert!(!counts.passed("doctest-z3regex"));
        counts.attempted = 6;
        counts.discovered = 6;
        assert!(!counts.passed("doctest-z3regex"));
        counts.attempted = 7;
        counts.discovered = 7;
        counts.skipped = 1;
        assert!(!counts.passed("doctest-z3regex"));
        counts.skipped = 0;
        counts.failed = 1;
        assert!(!counts.passed("doctest-z3regex"));
    }

    #[test]
    fn missing_or_duplicate_upstream_count_reports_are_refused() {
        let report = "AY_Z3PY_DOCTEST {\"module\":\"z3regex\",\"attempted\":7,\"failed\":0,\"skipped\":0,\"discovered\":7,\"upstream_exit\":0,\"warnings\":[]}\n";
        assert!(doctest_counts(report).unwrap().passed("doctest-z3regex"));
        assert!(doctest_counts("no report").is_none());
        assert!(doctest_counts(&format!("{report}{report}")).is_none());
    }

    #[test]
    fn supervision_failure_retains_owner_and_stays_explicitly_partial() {
        let directory = tempfile::tempdir().unwrap();
        let path = retain_partial_diagnostic(
            directory.path(),
            &[],
            "doctest-z3",
            "ay",
            "watchdog unavailable",
            "bounded-test-envelope",
        )
        .unwrap();
        let diagnostic: Value = serde_json::from_slice(&fs::read(path).unwrap()).unwrap();
        assert_eq!(diagnostic["failed_case"], "doctest-z3");
        assert_eq!(diagnostic["failed_subject"], "ay");
        assert_eq!(diagnostic["error"], "watchdog unavailable");
        assert_eq!(diagnostic["fragment_passed"], false);
        assert_eq!(diagnostic["full_replacement_ready"], false);
    }
}
