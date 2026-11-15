// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Current-release ABI measurement using the maintained isolated probes and
//! linked C consumers. Public type/export coverage and executed examples are
//! reported separately from exhaustive per-function semantic contracts.

use super::*;
use crate::z3_abi_500::{LibraryObservation, StockCProbe};
use sha2::Digest as _;
use std::ffi::OsString;
use std::io::Read as _;

mod registered;
mod semantic_contracts;

pub(super) const VALIDATOR_ID: &str = registered::VALIDATOR_ID;

pub(super) fn run_registered(args: &[String]) -> Result<i32, String> {
    registered::run(args)
}

pub(super) fn validate_and_replay(
    receipt: &ValidatorReceipt,
    context: EvidenceContext<'_>,
) -> Result<(), String> {
    registered::validate_and_replay(receipt, context)
}

const SCHEMA: &str = "ay-current-z3-abi-measurement/v6";
const TIMEOUT: Duration = Duration::from_secs(30);
const MAX_REPORT_BYTES: u64 = 64 * 1024 * 1024;
const STAGING_PATH_POLICY: &str = "Only path-boundary-delimited owned ABI work and library staging roots (including their canonical aliases) are replaced by stable role tokens; statuses, values and all other text remain unchanged.";

enum Provider {
    Ay,
    Z3,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Capture {
    id: String,
    exit_code: Option<i32>,
    timed_out: bool,
    memout: bool,
    stdin_complete: bool,
    stdout_truncated: bool,
    stderr_truncated: bool,
    stdout: String,
    stderr: String,
}

impl Capture {
    fn process_completed(&self) -> bool {
        self.exit_code == Some(0)
            && !self.timed_out
            && !self.memout
            && self.stdin_complete
            && !self.stdout_truncated
            && !self.stderr_truncated
    }

    fn exact_stdout(&self, expected: &[u8]) -> bool {
        self.process_completed() && self.stderr.is_empty() && self.stdout.as_bytes() == expected
    }
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Function {
    name: String,
    reference_signature: Value,
    ay_signature: Option<Value>,
    signature_matches: bool,
    reference_symbol_resolves: bool,
    ay_symbol_resolves: bool,
    linked_consumer_exercised: bool,
    semantic_contract: semantic_contracts::FunctionContract,
    semantic_contract_complete: bool,
    remaining: String,
}

/// This binds the type inventory to immutable header bytes and the source
/// revision declared inside the tested library. It is not a reproducible-build
/// proof: an embedded source stamp is a claim made by those library bytes.
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct HeaderProvenance {
    checkout_root: PathBuf,
    checkout_commit: Option<String>,
    header_sha256: BTreeMap<String, String>,
    header_git_blob: BTreeMap<String, String>,
    library_build_stamp: Option<String>,
    library_source_commit: Option<String>,
    headers_match_checkout_commit: bool,
    headers_match_library_source_commit: bool,
    gaps: Vec<String>,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Report {
    schema: String,
    capture_path_normalization: String,
    profile_sha256: String,
    validator_sha256: String,
    semantic_compiler: Artifact,
    consumer_source_sha256: BTreeMap<String, String>,
    ay_header_provenance: HeaderProvenance,
    source: PathBuf,
    ay_library: PathBuf,
    ay_library_sha256: String,
    z3_library: PathBuf,
    z3_library_sha256: String,
    resource_envelope: String,
    reference_source_inventory: Value,
    reference_observation: Option<LibraryObservation>,
    ay_observation: Option<LibraryObservation>,
    captures: Vec<Capture>,
    semantic_contracts: semantic_contracts::Execution,
    functions: Vec<Function>,
    enum_differences: Vec<String>,
    probe_differences: Vec<String>,
    non_runtime_probe_fields: Vec<String>,
    fragment_passed: bool,
    abi_complete: bool,
    full_replacement_ready: bool,
    blockers: Vec<String>,
}

pub(super) fn run(args: &[String]) -> Result<i32, String> {
    if args
        .iter()
        .any(|arg| matches!(arg.as_str(), "--help" | "-h"))
    {
        println!("smtlib-conformance current-abi --source DIR --ay-library FILE --out FILE [--z3-library FILE]\n\nMeasure the current 817-declaration ABI against authenticated Z3 5.3.3.\nRuns isolated symbol/finite-set probes and linked C consumers using current\nstock headers, plus named context, lifetime, solver state, model, error,\ncontainer, Optimize and Fixedpoint contracts. Every function retains its unproved\nexhaustive semantic contract; unregistered functions remain explicit. Exit 1 until\nthe ABI contract is complete. No declaration or call count grants semantic parity.");
        return Ok(0);
    }
    let mut source = None;
    let mut ay = None;
    let mut z3 = None;
    let mut output = None;
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        let value = args.next().ok_or_else(|| format!("{arg} needs a path"))?;
        match arg.as_str() {
            "--source" => source = Some(PathBuf::from(value)),
            "--ay-library" => ay = Some(PathBuf::from(value)),
            "--z3-library" => z3 = Some(PathBuf::from(value)),
            "--out" => output = Some(PathBuf::from(value)),
            other => return Err(format!("unknown current-abi argument {other:?}")),
        }
    }
    let source = source.ok_or("current-abi requires --source DIR")?;
    let ay = ay.ok_or("current-abi requires --ay-library FILE")?;
    let output = output.ok_or("current-abi requires --out FILE")?;
    let z3 = z3.unwrap_or(reference_library_path()?);
    let report = measure(&source, &ay, &z3)?;
    let bytes = pretty_json(&report)?;
    if bytes.len() as u64 > MAX_REPORT_BYTES {
        return Err("ABI report exceeds its bound".to_string());
    }
    atomic_write_new(&output, &bytes)?;
    println!(
        "current_abi={} functions={} exercised={} fragment_passed={} abi_complete=false",
        output.display(),
        report.functions.len(),
        report
            .functions
            .iter()
            .filter(|row| row.linked_consumer_exercised)
            .count(),
        report.fragment_passed
    );
    println!(
        "current_abi_semantic_contracts registered_functions={} passing_functions={} uncovered_functions={} families_passed={}/{}",
        report.semantic_contracts.registered_functions,
        report.semantic_contracts.passed_functions,
        report.semantic_contracts.uncovered_functions,
        report.semantic_contracts.families.iter().filter(|family| family.passed).count(),
        report.semantic_contracts.families.len()
    );
    Ok(1)
}

pub(super) fn check(args: &[String]) -> Result<i32, String> {
    if args.len() != 1 {
        return Err("usage: smtlib-conformance current-abi-check FILE".to_string());
    }
    let bytes = read_bounded(Path::new(&args[0]))?;
    let recorded: Report = serde_json::from_slice(&bytes).map_err(|error| error.to_string())?;
    validate_report(&recorded)?;
    let timeout = parse_resource_envelope(&recorded.resource_envelope)?.timeout;
    let fresh = measure_with_timeout(
        &recorded.source,
        &recorded.ay_library,
        &recorded.z3_library,
        timeout,
    )?;
    if recorded != fresh {
        return Err("ABI measurement differs from fresh authenticated execution".to_string());
    }
    println!(
        "current_abi_replay=PASS fragment_passed={} abi_complete=false",
        recorded.fragment_passed
    );
    Ok(1)
}

/// This worker is only a compiler invocation; the caller places its complete
/// process group under PlannedResources. Reuse the maintained linking and
/// loader-binding policy instead of introducing an independent linker driver.
pub(super) fn build_child(args: &[String]) -> Result<i32, String> {
    if args.len() != 4 {
        return Err("current-abi-build-child needs directory, probe, subject, library".to_string());
    }
    let probe = semantic_contracts::probe(&args[1])
        .or_else(|| {
            crate::z3_abi_500::stock_c_probes()
                .into_iter()
                .find(|probe| probe.id == args[1])
        })
        .ok_or("unknown maintained stock C probe")?;
    if !matches!(args[2].as_str(), "ay" | "z3") {
        return Err("unknown ABI subject".to_string());
    }
    let expected = semantic_contracts::build_source(&args[1], &args[2])?
        .unwrap_or_else(|| probe.source.to_vec());
    let source_path = Path::new(&args[0]).join(format!("{}.c", probe.id));
    verify_compiler_input(&source_path, &expected)?;
    compile_stock_c_probe(Path::new(&args[0]), &probe, &args[2], Path::new(&args[3]))?;
    verify_compiler_input(&source_path, &expected)?;
    Ok(0)
}

fn verify_compiler_input(path: &Path, expected: &[u8]) -> Result<(), String> {
    if read_bounded(path)? != expected {
        return Err("ABI compiler input differs from its maintained source".to_string());
    }
    Ok(())
}

fn read_bounded(path: &Path) -> Result<Vec<u8>, String> {
    let mut bytes = Vec::new();
    fs::File::open(path)
        .map_err(|error| error.to_string())?
        .take(MAX_REPORT_BYTES + 1)
        .read_to_end(&mut bytes)
        .map_err(|error| error.to_string())?;
    if bytes.len() as u64 > MAX_REPORT_BYTES {
        return Err("ABI input exceeds its bound".to_string());
    }
    Ok(bytes)
}

fn measure(source: &Path, ay_library: &Path, z3_library: &Path) -> Result<Report, String> {
    measure_with_timeout(source, ay_library, z3_library, TIMEOUT)
}

fn measure_with_timeout(
    source: &Path,
    ay_library: &Path,
    z3_library: &Path,
    timeout: Duration,
) -> Result<Report, String> {
    if timeout.is_zero() || timeout > Duration::from_secs(3600) {
        return Err("current ABI timeout must be between 1ns and 3600 seconds".to_string());
    }
    let source = fs::canonicalize(source).map_err(|error| error.to_string())?;
    let ay_library = fs::canonicalize(ay_library).map_err(|error| error.to_string())?;
    let z3_library = fs::canonicalize(z3_library).map_err(|error| error.to_string())?;
    let profile = canonical_profile()?;
    let ay_library_sha256 = sha256_file(&ay_library, "AY library")?;
    let z3_library_sha256 = profile.z3_overlay.reference_shared_library.sha256.clone();
    let staged_ay = stage_authenticated_library(&ay_library, &ay_library_sha256, "AY library")?;
    let staged_z3 =
        stage_authenticated_library(&z3_library, &z3_library_sha256, "pinned Z3 library")?;
    let directory = tempfile::tempdir().map_err(|error| error.to_string())?;
    let inventory_file = directory.path().join("source.json");
    let z3_executable = reference_artifact_path(&profile.z3_overlay.reference_executable.path)?;
    current_release::write_inventory(&source, &z3_executable, &inventory_file)?;
    let reference_source_inventory: Value = serde_json::from_slice(&read_bounded(&inventory_file)?)
        .map_err(|error| error.to_string())?;
    let declarations = reference_source_inventory["declarations"]
        .as_object()
        .ok_or("source inventory lacks declarations")?;
    let enums = reference_source_inventory["enum_constants"]
        .as_object()
        .ok_or("source inventory lacks enum constants")?;
    if declarations.len() != 817 || enums.len() != 370 {
        return Err("source inventory is not the current complete type surface".to_string());
    }
    copy_current_headers(&source, &reference_source_inventory, directory.path())?;
    for probe in crate::z3_abi_500::stock_c_probes() {
        fs::write(
            directory.path().join(format!("{}.c", probe.id)),
            probe.source,
        )
        .map_err(|error| error.to_string())?;
    }
    let root = locate_repo_root()?;
    let resources = PlannedResources::plan(&root, 1, "current Z3 ABI execution")
        .map_err(|error| error.to_string())?;
    let staged_ay_headers = directory.path().join("ay-headers");
    let (header_sha256, header_git_blob) =
        snapshot_ay_headers(&root.join("crates/ay-ffi/include"), &staged_ay_headers)?;
    let (ay_declarations, ay_enums) =
        crate::release_inventory::clang_inventory(&staged_ay_headers)?;
    let mut names = declarations.keys().cloned().collect::<Vec<_>>();
    names.sort();
    let manifest = required_symbol_manifest_bytes(&names);
    let resource_envelope = effective_execution_envelope(
        &resources.plan,
        ENFORCEMENT_RSS_WATCHDOG_V1,
        timeout.as_secs_f64(),
    )
    .map_err(|error| error.to_string())?;
    let executable = std::env::current_exe().map_err(|error| error.to_string())?;
    let validator_sha256 = sha256_file(&executable, "current ABI validator")?;
    let compiler = fs::canonicalize(semantic_contracts::compiler())
        .map_err(|error| format!("locate ABI semantic compiler: {error}"))?;
    let semantic_compiler = Artifact {
        path: compiler.to_string_lossy().into_owned(),
        sha256: sha256_file(&compiler, "ABI semantic compiler")?,
    };
    let mut consumer_source_sha256: BTreeMap<String, String> = crate::z3_abi_500::stock_c_probes()
        .into_iter()
        .map(|probe| (probe.id.to_string(), sha256_bytes(probe.source)))
        .collect();
    consumer_source_sha256.extend(
        semantic_contracts::sources().map(|(id, bytes)| (id.to_string(), sha256_bytes(bytes))),
    );
    let mut captures = Vec::new();
    let reference_capture = capture(
        &resources,
        &executable,
        &["z3-abi-probe".into(), staged_z3.path.as_os_str().to_owned()],
        &manifest,
        "z3.symbols-and-finite-sets",
        timeout,
    )?;
    let mut reference_observation = parse_observation(&reference_capture, Provider::Z3)?;
    captures.push(reference_capture);
    let ay_capture = capture(
        &resources,
        &executable,
        &["z3-abi-probe".into(), staged_ay.path.as_os_str().to_owned()],
        &manifest,
        "ay.symbols-and-finite-sets",
        timeout,
    )?;
    let mut ay_observation = parse_observation(&ay_capture, Provider::Ay)?;
    captures.push(ay_capture);
    let ay_header_provenance = header_provenance(
        &resources,
        &root,
        timeout,
        header_sha256,
        header_git_blob,
        ay_observation
            .as_ref()
            .and_then(|observation| observation.ay_build_stamp.as_deref()),
    );
    let mut exercised = BTreeSet::new();
    let mut consumers_passed = true;
    for probe in crate::z3_abi_500::stock_c_probes() {
        let (passed, called) = execute_consumer(
            &resources,
            &executable,
            directory.path(),
            &probe,
            &staged_ay.path,
            &staged_z3.path,
            &mut captures,
            timeout,
        )?;
        consumers_passed &= passed;
        if passed {
            exercised.extend(called);
        }
    }
    let semantic_contracts = semantic_contracts::execute(
        &resources,
        &executable,
        directory.path(),
        &staged_ay.path,
        &staged_z3.path,
        &names,
        &mut captures,
        timeout,
    )?;
    if sha256_file(&staged_ay.path, "ABI AY library after execution")? != ay_library_sha256
        || sha256_file(&staged_z3.path, "ABI Z3 library after execution")? != z3_library_sha256
    {
        return Err("ABI provider bytes changed during execution".to_string());
    }
    let mut functions = Vec::with_capacity(names.len());
    for name in names {
        let reference_signature = declarations[&name].clone();
        let ay_signature = ay_declarations.get(&name).cloned();
        let reference_symbol_resolves = observation_resolves(reference_observation.as_ref(), &name);
        let ay_symbol_resolves = observation_resolves(ay_observation.as_ref(), &name);
        functions.push(Function {
            signature_matches: ay_signature.as_ref() == Some(&reference_signature), reference_signature, ay_signature,
            reference_symbol_resolves, ay_symbol_resolves, linked_consumer_exercised: exercised.contains(&name),
            semantic_contract: semantic_contracts::function_contract(&name, &semantic_contracts),
            semantic_contract_complete: false,
            remaining: "Full-domain input, lifetime, context, state, invalid-argument and result semantics remain open; named semantic obligations record measured subcases, while stock consumers provide separate corroboration.".to_string(), name,
        });
    }
    let enum_differences = enums
        .iter()
        .filter(|(name, value)| ay_enums.get(*name) != Some(*value))
        .map(|(name, _)| name.clone())
        .collect::<Vec<_>>();
    let probe_differences =
        finite_probe_differences(reference_observation.as_ref(), ay_observation.as_ref());
    let reference_identity_matches = reference_observation
        .as_ref()
        .and_then(|value| value.full_version.as_deref())
        == Some(
            profile
                .z3_overlay
                .reference_shared_library
                .full_version
                .as_str(),
        );
    let fragment_passed = ay_header_provenance.headers_match_library_source_commit
        && reference_identity_matches
        && consumers_passed
        && semantic_contracts.passed
        && enum_differences.is_empty()
        && probe_differences.is_empty()
        && functions.iter().all(|row| {
            row.signature_matches && row.reference_symbol_resolves && row.ay_symbol_resolves
        });
    let mut blockers = vec!["Full-domain semantic contracts for all 817 functions remain open. Registered finite semantic obligations and stock examples establish only their named input/state sequences.".to_string()];
    if !ay_header_provenance.headers_match_library_source_commit {
        blockers.push("The captured AY header bytes could not be matched to the source revision declared by the tested library; type coherence is unestablished.".to_string());
    }
    // Classify original process output before replacing ephemeral locations.
    // Only retained diagnostics and probe error text use stable role tokens.
    let paths = StagingPaths::new(&[
        (directory.path(), "@ABI_WORKDIR@"),
        (
            staged_ay.path.parent().ok_or("AY staging root missing")?,
            "@ABI_AY_LIBRARY@",
        ),
        (
            staged_z3.path.parent().ok_or("Z3 staging root missing")?,
            "@ABI_Z3_LIBRARY@",
        ),
    ])?;
    for capture in &mut captures {
        paths.normalize_capture(capture);
    }
    for observation in [&mut reference_observation, &mut ay_observation]
        .into_iter()
        .flatten()
    {
        for value in observation.probes.values_mut() {
            *value = paths.normalize(value);
        }
    }
    verify_artifact(
        &semantic_compiler,
        Path::new("."),
        "ABI semantic compiler after execution",
    )?;
    let report = Report {
        schema: SCHEMA.to_string(),
        capture_path_normalization: STAGING_PATH_POLICY.to_string(),
        profile_sha256: canonical_profile_sha256()?,
        validator_sha256,
        semantic_compiler,
        consumer_source_sha256,
        ay_header_provenance,
        source,
        ay_library,
        ay_library_sha256,
        z3_library,
        z3_library_sha256,
        resource_envelope,
        reference_source_inventory,
        reference_observation,
        ay_observation,
        captures,
        semantic_contracts,
        functions,
        enum_differences,
        probe_differences,
        non_runtime_probe_fields: vec![
            "decl-kind.finite-set-ext".to_string(),
            "decl-kind.finite-set-map-inverse".to_string(),
        ],
        fragment_passed,
        abi_complete: false,
        full_replacement_ready: false,
        blockers,
    };
    validate_report(&report)?;
    Ok(report)
}

pub(super) struct StagingPaths {
    roots: Vec<(String, &'static str)>,
}

impl StagingPaths {
    pub(super) fn new(paths: &[(&Path, &'static str)]) -> Result<Self, String> {
        let mut roots = BTreeMap::new();
        for (path, role) in paths {
            let canonical = fs::canonicalize(path)
                .map_err(|error| format!("canonicalize ABI staging root: {error}"))?;
            for path in [*path, canonical.as_path()] {
                let path = path.to_str().ok_or("ABI staging root is not UTF-8")?;
                if path.is_empty() || path == "/" {
                    return Err("invalid ABI staging root".to_string());
                }
                if roots
                    .insert(path.to_string(), *role)
                    .is_some_and(|previous| previous != *role)
                {
                    return Err("overlapping ABI staging role identities".to_string());
                }
            }
        }
        let mut roots = roots.into_iter().collect::<Vec<_>>();
        roots.sort_by(|(left, _), (right, _)| right.len().cmp(&left.len()).then(left.cmp(right)));
        Ok(Self { roots })
    }

    pub(super) fn normalize(&self, value: &str) -> String {
        let mut normalized = value.to_string();
        for (path, role) in &self.roots {
            normalized = replace_staging_path(&normalized, path, role);
        }
        normalized
    }

    fn normalize_capture(&self, capture: &mut Capture) {
        capture.stdout = self.normalize(&capture.stdout);
        capture.stderr = self.normalize(&capture.stderr);
    }
}

fn replace_staging_path(text: &str, path: &str, role: &str) -> String {
    fn delimiter(character: char) -> bool {
        character.is_whitespace()
            || matches!(
                character,
                '\'' | '"' | '(' | ')' | '[' | ']' | '{' | '}' | ':' | ',' | '=' | ';'
            )
    }
    let mut output = String::with_capacity(text.len());
    let mut copied = 0;
    for (start, _) in text.match_indices(path) {
        let end = start + path.len();
        let before = text[..start].chars().next_back();
        let after = text[end..].chars().next();
        if before.is_none_or(delimiter)
            && after.is_none_or(|character| character == '/' || delimiter(character))
        {
            output.push_str(&text[copied..start]);
            output.push_str(role);
            copied = end;
        }
    }
    output.push_str(&text[copied..]);
    output
}

fn observation_resolves(observation: Option<&LibraryObservation>, name: &str) -> bool {
    observation.is_some_and(|observation| {
        observation
            .required_resolvable_symbols
            .iter()
            .any(|symbol| symbol == name)
    })
}

fn snapshot_ay_headers(
    source: &Path,
    destination: &Path,
) -> Result<(BTreeMap<String, String>, BTreeMap<String, String>), String> {
    let mut pending = vec![source.to_path_buf()];
    let mut sha256 = BTreeMap::new();
    let mut git_blob = BTreeMap::new();
    let mut visited = 0usize;
    fs::create_dir_all(destination).map_err(|error| error.to_string())?;
    while let Some(directory) = pending.pop() {
        for entry in fs::read_dir(directory).map_err(|error| error.to_string())? {
            let entry = entry.map_err(|error| error.to_string())?;
            visited += 1;
            if visited > 10_000 {
                return Err("AY header traversal exceeds its bound".to_string());
            }
            let path = entry.path();
            let kind = entry.file_type().map_err(|error| error.to_string())?;
            if kind.is_symlink() {
                return Err("AY header source contains a symlink".to_string());
            }
            if kind.is_dir() {
                pending.push(path);
                continue;
            }
            if path.extension().is_none_or(|extension| extension != "h") {
                continue;
            }
            if !kind.is_file() {
                return Err("AY header source contains a nonregular header".to_string());
            }
            let relative = path
                .strip_prefix(source)
                .map_err(|error| error.to_string())?;
            let name = relative
                .to_str()
                .ok_or("non-UTF-8 AY header path")?
                .to_string();
            validate_relative_path(&name, "AY header")?;
            let bytes = read_bounded(&path)?;
            let mut blob = sha1::Sha1::new();
            blob.update(format!("blob {}\0", bytes.len()).as_bytes());
            blob.update(&bytes);
            git_blob.insert(name.clone(), format!("{:x}", blob.finalize()));
            sha256.insert(name, sha256_bytes(&bytes));
            let target = destination.join(relative);
            if let Some(parent) = target.parent() {
                fs::create_dir_all(parent).map_err(|error| error.to_string())?;
            }
            fs::write(target, bytes).map_err(|error| error.to_string())?;
        }
    }
    if sha256.is_empty() {
        return Err("AY header source is empty".to_string());
    }
    Ok((sha256, git_blob))
}

fn source_git(
    resources: &PlannedResources,
    root: &Path,
    args: &[&str],
    timeout: Duration,
) -> Result<String, String> {
    let mut command = vec![OsString::from("-C"), root.as_os_str().to_owned()];
    command.extend(args.iter().map(OsString::from));
    let output = capture(
        resources,
        Path::new("git"),
        &command,
        b"",
        "ay-header-source",
        timeout,
    )?;
    if !output.process_completed() || !output.stderr.is_empty() {
        return Err(format!(
            "Git header provenance unavailable: {}",
            output.stderr.trim()
        ));
    }
    Ok(output.stdout)
}

fn stamped_source_commit(stamp: &str) -> Result<String, String> {
    let commit = build_stamp_commit(stamp).ok_or("AY library has no parseable source stamp")?;
    if commit.ends_with("-dirty") {
        return Err("AY library source stamp is dirty".to_string());
    }
    validate_full_commit(commit, "AY library stamped source commit")?;
    Ok(commit.to_string())
}

fn header_tree(text: &str) -> Result<BTreeMap<String, String>, String> {
    let mut headers = BTreeMap::new();
    for line in text.lines() {
        let (meta, path) = line
            .split_once('\t')
            .ok_or("malformed header source tree")?;
        let Some(name) = path.strip_prefix("crates/ay-ffi/include/") else {
            return Err("header source tree escaped requested prefix".to_string());
        };
        if !name.ends_with(".h") {
            continue;
        }
        validate_relative_path(name, "committed AY header")?;
        let meta = meta.split_whitespace().collect::<Vec<_>>();
        if meta.len() != 3
            || !matches!(meta[0], "100644" | "100755")
            || meta[1] != "blob"
            || meta[2].len() != 40
            || !meta[2].bytes().all(|byte| byte.is_ascii_hexdigit())
        {
            return Err("committed AY header is not a regular Git blob".to_string());
        }
        if headers
            .insert(name.to_string(), meta[2].to_string())
            .is_some()
        {
            return Err("duplicate committed AY header".to_string());
        }
    }
    if headers.is_empty() {
        return Err("source commit has no AY headers".to_string());
    }
    Ok(headers)
}

fn headers_match_commit(
    resources: &PlannedResources,
    root: &Path,
    commit: &str,
    observed: &BTreeMap<String, String>,
    timeout: Duration,
) -> Result<bool, String> {
    validate_full_commit(commit, "AY header comparison commit")?;
    let listing = source_git(
        resources,
        root,
        &[
            "ls-tree",
            "-r",
            "--full-tree",
            commit,
            "--",
            "crates/ay-ffi/include",
        ],
        timeout,
    )?;
    Ok(header_tree(&listing)? == *observed)
}

fn header_provenance(
    resources: &PlannedResources,
    root: &Path,
    timeout: Duration,
    header_sha256: BTreeMap<String, String>,
    header_git_blob: BTreeMap<String, String>,
    stamp: Option<&str>,
) -> HeaderProvenance {
    let mut gaps = Vec::new();
    let checkout_commit = source_git(resources, root, &["rev-parse", "HEAD"], timeout)
        .and_then(|commit| {
            let commit = commit.trim();
            validate_full_commit(commit, "AY checkout commit")?;
            Ok(commit.to_string())
        })
        .map_err(|error| gaps.push(error))
        .ok();
    let library_source_commit = stamp
        .ok_or_else(|| "AY library source stamp is unavailable".to_string())
        .and_then(stamped_source_commit)
        .map_err(|error| gaps.push(error))
        .ok();
    let mut compare = |commit: Option<&str>, label: &str| {
        let Some(commit) = commit else {
            return false;
        };
        match headers_match_commit(resources, root, commit, &header_git_blob, timeout) {
            Ok(true) => true,
            Ok(false) => {
                gaps.push(format!(
                    "captured AY header set differs from {label} {commit}"
                ));
                false
            }
            Err(error) => {
                gaps.push(format!("{label}: {error}"));
                false
            }
        }
    };
    let headers_match_checkout_commit = compare(checkout_commit.as_deref(), "checkout commit");
    let headers_match_library_source_commit =
        compare(library_source_commit.as_deref(), "library source commit");
    HeaderProvenance {
        checkout_root: root.to_path_buf(),
        checkout_commit,
        header_sha256,
        header_git_blob,
        library_build_stamp: stamp.map(str::to_string),
        library_source_commit,
        headers_match_checkout_commit,
        headers_match_library_source_commit,
        gaps,
    }
}

fn copy_current_headers(
    source: &Path,
    inventory: &Value,
    destination: &Path,
) -> Result<(), String> {
    let headers = inventory["header_sha256"]
        .as_object()
        .ok_or("source inventory lacks header hashes")?;
    for (name, hash) in headers {
        validate_relative_path(name, "current public header")?;
        let path = source.join("src/api").join(name);
        let bytes = read_bounded(&path)?;
        if hash.as_str() != Some(sha256_bytes(&bytes).as_str()) {
            return Err(format!(
                "current header changed after source authentication: {name}"
            ));
        }
        let target = destination.join(name);
        if let Some(parent) = target.parent() {
            fs::create_dir_all(parent).map_err(|error| error.to_string())?;
        }
        fs::write(target, bytes).map_err(|error| error.to_string())?;
    }
    Ok(())
}

fn capture(
    resources: &PlannedResources,
    program: &Path,
    args: &[OsString],
    input: &[u8],
    id: &str,
    timeout: Duration,
) -> Result<Capture, String> {
    let output = resources
        .run_external_transcript_scrubbed(program, args, input, timeout, id)
        .map_err(|error| error.to_string())?;
    Ok(Capture {
        id: id.to_string(),
        exit_code: output.status.and_then(|status| status.code()),
        timed_out: output.timed_out,
        memout: output.memout,
        stdin_complete: output.stdin_complete,
        stdout_truncated: output.stdout_truncated,
        stderr_truncated: output.stderr_truncated,
        stdout: String::from_utf8(output.stdout)
            .map_err(|error| format!("{id} stdout: {error}"))?,
        stderr: String::from_utf8(output.stderr)
            .map_err(|error| format!("{id} stderr: {error}"))?,
    })
}

fn parse_observation(
    capture: &Capture,
    provider: Provider,
) -> Result<Option<LibraryObservation>, String> {
    if !capture.process_completed()
        || !(capture.stderr.is_empty()
            || (matches!(provider, Provider::Ay)
                && is_expected_ay_abi_stderr(capture.stderr.as_bytes())))
    {
        return Ok(None);
    }
    let observation: LibraryObservation = serde_json::from_str(&capture.stdout)
        .map_err(|error| format!("{} malformed observation: {error}", capture.id))?;
    Ok(Some(observation))
}

fn execute_consumer(
    resources: &PlannedResources,
    executable: &Path,
    directory: &Path,
    probe: &StockCProbe,
    ay: &Path,
    z3: &Path,
    captures: &mut Vec<Capture>,
    timeout: Duration,
) -> Result<(bool, BTreeSet<String>), String> {
    let mut passed = true;
    for (subject, library) in [("z3", z3), ("ay", ay)] {
        let args = [
            "smtlib-conformance".into(),
            "current-abi-build-child".into(),
            directory.as_os_str().to_owned(),
            probe.id.into(),
            subject.into(),
            library.as_os_str().to_owned(),
        ];
        let build = capture(
            resources,
            executable,
            &args,
            b"",
            &format!("build.{}.{subject}", probe.id),
            timeout,
        )?;
        let built = build.exact_stdout(b"");
        captures.push(build);
        if built {
            let binary = directory.join(format!("{}-{subject}", probe.id));
            let run = capture(
                resources,
                &binary,
                &[library.as_os_str().to_owned()],
                b"",
                &format!("consumer.{}.{subject}", probe.id),
                timeout,
            )?;
            passed &= run.exact_stdout(&crate::z3_abi_500::stock_c_probe_expected_stdout(probe));
            captures.push(run);
        } else {
            passed = false;
        }
    }
    Ok((
        passed,
        crate::z3_abi_500::stock_c_probe_callability_symbols(probe),
    ))
}

fn finite_probe_differences(
    reference: Option<&LibraryObservation>,
    ay: Option<&LibraryObservation>,
) -> Vec<String> {
    let mut differences = Vec::new();
    for (name, expected) in crate::z3_abi_500::expected_probe_values() {
        // The legacy probe assigns these reserved constants rather than
        // constructing an AST. Their actual values are checked by Clang's
        // header inventory, never credited as runtime observations.
        if matches!(
            name.as_str(),
            "decl-kind.finite-set-ext" | "decl-kind.finite-set-map-inverse"
        ) {
            continue;
        }
        if reference.and_then(|value| value.probes.get(&name)) != Some(&expected)
            || ay.and_then(|value| value.probes.get(&name)) != Some(&expected)
        {
            differences.push(name);
        }
    }
    differences
}

fn validate_report(report: &Report) -> Result<(), String> {
    if report.schema != SCHEMA
        || report.capture_path_normalization != STAGING_PATH_POLICY
        || report.profile_sha256 != canonical_profile_sha256()?
        || report.abi_complete
        || report.full_replacement_ready
        || report.functions.len() != 817
        || report
            .functions
            .iter()
            .any(|row| row.semantic_contract_complete || row.remaining.is_empty())
        || report.blockers.is_empty()
    {
        return Err(
            "current ABI report invents completeness or loses required semantic gaps".to_string(),
        );
    }
    validate_header_provenance(&report.ay_header_provenance, report.fragment_passed)?;
    verify_artifact(
        &report.semantic_compiler,
        Path::new("."),
        "ABI semantic compiler",
    )?;
    if report
        .functions
        .windows(2)
        .any(|rows| rows[0].name >= rows[1].name)
    {
        return Err("ABI function inventory is not sorted and unique".to_string());
    }
    let names = report
        .functions
        .iter()
        .map(|function| function.name.clone())
        .collect::<Vec<_>>();
    semantic_contracts::validate(&report.semantic_contracts, &names, &report.captures)?;
    for function in &report.functions {
        if function.semantic_contract
            != semantic_contracts::function_contract(&function.name, &report.semantic_contracts)
        {
            return Err(format!(
                "ABI semantic obligations drift for {}",
                function.name
            ));
        }
    }
    for (id, source) in semantic_contracts::sources() {
        if report.consumer_source_sha256.get(id) != Some(&sha256_bytes(source)) {
            return Err(format!(
                "ABI semantic contract source identity drift for {id}"
            ));
        }
    }
    Ok(())
}

fn validate_header_provenance(
    provenance: &HeaderProvenance,
    fragment_passed: bool,
) -> Result<(), String> {
    if provenance.header_sha256.is_empty()
        || provenance
            .header_sha256
            .keys()
            .ne(provenance.header_git_blob.keys())
        || (fragment_passed && !provenance.headers_match_library_source_commit)
    {
        return Err("current ABI report lacks coherent AY header provenance".to_string());
    }
    for hash in provenance.header_sha256.values() {
        validate_sha256(hash, "AY header SHA-256")?;
    }
    for hash in provenance.header_git_blob.values() {
        validate_full_commit(hash, "AY header Git blob")?;
    }
    if provenance.headers_match_library_source_commit {
        let commit = provenance
            .library_source_commit
            .as_deref()
            .ok_or("header coherence has no source commit")?;
        if stamped_source_commit(
            provenance
                .library_build_stamp
                .as_deref()
                .ok_or("header coherence has no library stamp")?,
        )? != commit
        {
            return Err("AY header/library source identity mismatch".to_string());
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn complete_capture() -> Capture {
        Capture {
            id: "fixture".to_string(),
            exit_code: Some(0),
            timed_out: false,
            memout: false,
            stdin_complete: true,
            stdout_truncated: false,
            stderr_truncated: false,
            stdout: "ok\n".to_string(),
            stderr: String::new(),
        }
    }

    #[test]
    fn successful_exit_never_hides_incomplete_consumers() {
        let capture = complete_capture();
        assert!(capture.exact_stdout(b"ok\n"));
        let mut timed_out = capture.clone();
        timed_out.timed_out = true;
        let mut truncated = capture.clone();
        truncated.stdout_truncated = true;
        let mut wrong = capture.clone();
        wrong.stdout = "wrong\n".to_string();
        let mut error = capture;
        error.stderr = "diagnostic\n".to_string();
        for failure in [timed_out, truncated, wrong, error] {
            assert!(!failure.exact_stdout(b"ok\n"));
        }
    }

    #[test]
    fn missing_reference_or_subject_never_passes_finite_probes() {
        assert_eq!(
            finite_probe_differences(None, None).len(),
            crate::z3_abi_500::expected_probe_values().len() - 2
        );
    }

    #[test]
    fn equivalent_staging_diagnostics_replay_but_semantic_changes_do_not() {
        let first = StagingPaths {
            roots: vec![("/tmp/abi-first".to_string(), "@ABI_WORKDIR@")],
        };
        let second = StagingPaths {
            roots: vec![("/tmp/abi-second".to_string(), "@ABI_WORKDIR@")],
        };
        let diagnostic = "/tmp/abi-first/remaining.c:7: error: expected int, got double\n";
        assert_eq!(
            first.normalize(diagnostic),
            second.normalize(&diagnostic.replace("abi-first", "abi-second"))
        );
        assert_ne!(
            first.normalize(diagnostic),
            first.normalize(&diagnostic.replace("got double", "got pointer"))
        );
        let mut capture = complete_capture();
        capture.exit_code = Some(2);
        capture.stdout.clear();
        capture.stderr = diagnostic.to_string();
        first.normalize_capture(&mut capture);
        assert_eq!(capture.exit_code, Some(2));
        assert!(!capture.process_completed());
        assert_eq!(
            capture.stderr,
            "@ABI_WORKDIR@/remaining.c:7: error: expected int, got double\n"
        );
    }

    #[test]
    fn staging_normalization_preserves_other_paths_and_values() {
        let paths = StagingPaths {
            roots: vec![("/tmp/abi-first".to_string(), "@ABI_WORKDIR@")],
        };
        let unrelated =
            "/tmp/abi-first-sibling/x.c /other/tmp/abi-first/x.c value=42 version=5.3.3";
        assert_eq!(paths.normalize(unrelated), unrelated);
        assert_eq!(
            paths.normalize("error: '/tmp/abi-first/x.c'"),
            "error: '@ABI_WORKDIR@/x.c'"
        );
        assert_eq!(
            paths.normalize("{\"path\":\"/tmp/abi-first/x.c\"}"),
            "{\"path\":\"@ABI_WORKDIR@/x.c\"}"
        );
    }

    #[test]
    fn canonical_and_requested_staging_roots_have_one_role() {
        let directory = tempfile::tempdir().unwrap();
        let canonical = fs::canonicalize(directory.path()).unwrap();
        let paths = StagingPaths::new(&[(directory.path(), "@ABI_WORKDIR@")]).unwrap();
        for path in [directory.path(), canonical.as_path()] {
            assert_eq!(
                paths.normalize(&format!("{}/input.c", path.display())),
                "@ABI_WORKDIR@/input.c"
            );
        }
    }

    #[test]
    fn header_coherence_requires_full_clean_library_source_identity() {
        let commit = "a".repeat(40);
        let stamp = format!("0.28.0+build.42.{commit}@2026-11-11T00:00:00Z");
        assert_eq!(stamped_source_commit(&stamp).unwrap(), commit);
        assert!(
            stamped_source_commit(&stamp.replace(&commit, &format!("{commit}-dirty"))).is_err()
        );
        assert!(stamped_source_commit("0.28.0+build.42.aaaaaaa@now").is_err());
        assert!(stamped_source_commit("unknown").is_err());
        let mut provenance = HeaderProvenance {
            checkout_root: PathBuf::from("source"),
            checkout_commit: Some(commit.clone()),
            header_sha256: BTreeMap::from([("z3.h".to_string(), "0".repeat(64))]),
            header_git_blob: BTreeMap::from([("z3.h".to_string(), "1".repeat(40))]),
            library_build_stamp: Some(stamp),
            library_source_commit: Some(commit),
            headers_match_checkout_commit: true,
            headers_match_library_source_commit: true,
            gaps: Vec::new(),
        };
        validate_header_provenance(&provenance, true).unwrap();
        provenance.library_source_commit = Some("b".repeat(40));
        assert!(validate_header_provenance(&provenance, true).is_err());
        provenance.headers_match_library_source_commit = false;
        assert!(validate_header_provenance(&provenance, true).is_err());
        validate_header_provenance(&provenance, false).unwrap();
    }

    #[test]
    fn header_tree_requires_exact_regular_path_inventory() {
        let row = format!(
            "100644 blob {}\tcrates/ay-ffi/include/z3.h\n",
            "a".repeat(40)
        );
        let tree = header_tree(&row).unwrap();
        assert_eq!(tree.len(), 1);
        assert!(tree.contains_key("z3.h"));
        assert!(header_tree(&format!("{row}{row}")).is_err());
        assert!(header_tree(&row.replace("100644", "120000")).is_err());
        assert!(header_tree(&row.replace("include/z3.h", "include/../z3.h")).is_err());
        assert!(header_tree(&row.replace("include/", "other/")).is_err());
    }

    #[test]
    fn staged_headers_keep_the_exact_bytes_used_for_type_inventory() {
        let directory = tempfile::tempdir().unwrap();
        let source = directory.path().join("source");
        let staged = directory.path().join("staged");
        fs::create_dir(&source).unwrap();
        fs::write(source.join("z3.h"), b"typedef int Z3_fixture;\n").unwrap();
        let (hashes, _) = snapshot_ay_headers(&source, &staged).unwrap();
        fs::write(source.join("z3.h"), b"typedef double Z3_fixture;\n").unwrap();
        assert_eq!(
            fs::read(staged.join("z3.h")).unwrap(),
            b"typedef int Z3_fixture;\n"
        );
        assert_eq!(hashes["z3.h"], sha256_bytes(b"typedef int Z3_fixture;\n"));
    }

    #[test]
    fn compiler_input_rejects_stale_or_equal_length_changed_reference_wrappers() {
        let directory = tempfile::tempdir().unwrap();
        let source = directory.path().join("model.c");
        let expected = semantic_contracts::build_source("contract-model", "z3")
            .unwrap()
            .unwrap();
        fs::write(&source, &expected).unwrap();
        verify_compiler_input(&source, &expected).unwrap();
        let original = semantic_contracts::probe("contract-model").unwrap();
        fs::write(&source, original.source).unwrap();
        assert!(verify_compiler_input(&source, &expected).is_err());
        let mut changed = expected.clone();
        changed[0] ^= 1;
        fs::write(&source, &changed).unwrap();
        assert_eq!(changed.len(), expected.len());
        assert!(verify_compiler_input(&source, &expected).is_err());
    }
}
