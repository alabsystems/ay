// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Provision the exact inputs of the closed conformance profile. Downloads are
//! conveniences; archive, executable, library, and source identities remain
//! independently checked before a path is returned to the qualification run.

use super::*;
use reference_inventory::SnapshotKind;
use std::ffi::OsString;
use std::io;

#[derive(Clone, Copy)]
pub(super) enum NetworkAccess {
    Online,
    Offline,
}

const CHILD_TIMEOUT: Duration = Duration::from_secs(600);
const MAX_SOURCE_FILE_BYTES: u64 = 64 * 1024 * 1024;
// Complete verification reads every extracted query and every archive, rather
// than sampling. Four hours allows a slow single-worker full-population pass
// while retaining a finite wall deadline on storage or parser stalls.
const CORPUS_PHASE_TIMEOUT: Duration = Duration::from_hours(4);
const CORPUS_MANIFEST_LIMIT: u64 = 1024 * 1024 * 1024;
const CORPUS_COMPLETION_PREFIX: &str = "AY_OFFICIAL_CORPUS_VERIFIED ";

#[derive(Clone, Copy, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(rename_all = "kebab-case")]
enum CorpusPhase {
    Create,
    Authenticate,
}

impl CorpusPhase {
    fn name(self) -> &'static str {
        match self {
            Self::Create => "create",
            Self::Authenticate => "authenticate",
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
struct CorpusCompletion {
    schema: String,
    phase: CorpusPhase,
    manifest: PathBuf,
    manifest_sha256: String,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct CorpusWorkerRequest {
    schema: String,
    phase: CorpusPhase,
    manifest: PathBuf,
    create: Option<official_corpus::CorpusCreateInputs>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct CorpusPhaseCapture {
    exit_code: Option<i32>,
    signal: Option<i32>,
    timed_out: bool,
    memout: bool,
    stdin_complete: bool,
    stdout_truncated: bool,
    stderr_truncated: bool,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
}

impl CorpusPhaseCapture {
    fn from_output(output: GuardedTranscriptOutput) -> Self {
        #[cfg(unix)]
        let signal = output
            .status
            .as_ref()
            .and_then(std::os::unix::process::ExitStatusExt::signal);
        #[cfg(not(unix))]
        let signal = None;
        Self {
            exit_code: output.status.and_then(|status| status.code()),
            signal,
            timed_out: output.timed_out,
            memout: output.memout,
            stdin_complete: output.stdin_complete,
            stdout_truncated: output.stdout_truncated,
            stderr_truncated: output.stderr_truncated,
            stdout: output.stdout,
            stderr: output.stderr,
        }
    }
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct CorpusPhaseReceipt {
    schema: String,
    phase: CorpusPhase,
    directory: PathBuf,
    manifest: PathBuf,
    create: Option<official_corpus::CorpusCreateInputs>,
    worker_sha256: Option<String>,
    expected_manifest_sha256: Option<String>,
    input_manifest_sha256: Option<String>,
    timeout_seconds: u64,
    per_file_limit_bytes: u64,
    per_stream_limit_bytes: usize,
    resource_envelope: Option<String>,
    capture: Option<CorpusPhaseCapture>,
    completion: Option<CorpusCompletion>,
    passed: bool,
    error: Option<String>,
}

#[derive(Debug, Serialize)]
pub(super) struct Provisioned {
    pub(super) schema: String,
    pub(super) profile_id: String,
    pub(super) profile_sha256: String,
    pub(super) z3: PathBuf,
    pub(super) z3_library: PathBuf,
    pub(super) z3_source: PathBuf,
    pub(super) z3_snapshot: PathBuf,
    pub(super) language_source: PathBuf,
    pub(super) registry_source: PathBuf,
    pub(super) language_snapshot: PathBuf,
    pub(super) registry_snapshot: PathBuf,
    pub(super) normative_pdf: PathBuf,
}

pub(super) fn run(args: &[String]) -> Result<i32, String> {
    if args
        .iter()
        .any(|arg| matches!(arg.as_str(), "--help" | "-h"))
    {
        println!("smtlib-conformance provision --directory DIR [--offline]\n\nDownloads and authenticates the immutable native conformance-profile inputs.\nWrites DIR/provision.json. Offline mode validates existing inputs only.\nZ3 5.3.3 archive and library identities are pinned for macOS and Linux on\narm64 and x86_64. Provisioning alone grants no runtime compatibility claim.");
        return Ok(0);
    }
    let mut directory = None;
    let mut access = NetworkAccess::Online;
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--directory" => {
                directory = Some(PathBuf::from(
                    args.next().ok_or("--directory needs a path")?,
                ));
            }
            "--offline" => access = NetworkAccess::Offline,
            other => return Err(format!("unknown provision argument {other:?}")),
        }
    }
    let directory = directory.ok_or("provision requires --directory DIR")?;
    let inputs = prepare(&directory, access)?;
    print_utf8(&pretty_json(&inputs)?)?;
    Ok(0)
}

pub(super) fn run_corpus(args: &[String]) -> Result<i32, String> {
    if args
        .iter()
        .any(|arg| matches!(arg.as_str(), "--help" | "-h"))
    {
        println!("smtlib-conformance provision-corpus --directory DIR [--offline]\n\nDownload, extract and authenticate all 84 pinned SMT-LIB archives.\nRetains archives and writes DIR/official-corpus.json for a later qualification.\nOffline mode authenticates the complete retained population without downloading.\nAcquisition is not a solver compatibility or performance result.");
        return Ok(0);
    }
    let mut directory = None;
    let mut access = NetworkAccess::Online;
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--directory" => {
                directory = Some(PathBuf::from(
                    args.next().ok_or("--directory needs a path")?,
                ));
            }
            "--offline" => access = NetworkAccess::Offline,
            other => return Err(format!("unknown provision-corpus argument {other:?}")),
        }
    }
    let directory = directory.ok_or("provision-corpus requires --directory DIR")?;
    let manifest = prepare_corpus_with_access(&directory, access)?;
    println!("{}", manifest.display());
    Ok(0)
}

/// Materialize every official corpus archive and retain a closed manifest.
/// An existing manifest is only a locator: consuming validators authenticate
/// all of its files and source archives again before accepting evidence.
pub(super) fn prepare_corpus(directory: &Path) -> Result<PathBuf, String> {
    prepare_corpus_with_access(directory, NetworkAccess::Online)
}

fn prepare_corpus_with_access(directory: &Path, access: NetworkAccess) -> Result<PathBuf, String> {
    if !directory.exists() {
        require_online(access, "official corpus directory")?;
    }
    fs::create_dir_all(directory).map_err(|error| error.to_string())?;
    let directory = fs::canonicalize(directory).map_err(|error| error.to_string())?;
    let manifest = directory.join("official-corpus.json");
    if manifest.exists() {
        guarded_corpus_phase(&manifest, CorpusPhase::Authenticate, None, None)?;
        return Ok(manifest);
    }
    require_online(access, "complete official corpus manifest")?;
    let corpus = directory.join("corpus");
    let archives = directory.join("archives");
    let metadata = directory.join("zenodo-11061097.json");
    crate::fetch::provision_official(&corpus, &archives, &metadata)?;
    // The acquisition owner has returned and released its lease. Only then
    // acquire the final phase's lease; the worker below never acquires another.
    create_corpus_manifest(&official_corpus::CorpusCreateInputs {
        root: corpus,
        archive_root: archives,
        metadata,
        output: manifest.clone(),
    })?;
    Ok(manifest)
}

fn manifest_digest(path: &Path) -> Result<String, String> {
    let mut options = fs::OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC);
    }
    let mut file = options
        .open(path)
        .map_err(|error| format!("open corpus manifest: {error}"))?;
    let metadata = file
        .metadata()
        .map_err(|error| format!("inspect corpus manifest: {error}"))?;
    if !metadata.file_type().is_file() || metadata.len() > CORPUS_MANIFEST_LIMIT {
        return Err("corpus manifest is not a bounded regular file".to_string());
    }
    let mut hash = Sha256::new();
    let mut bytes = 0u64;
    let mut buffer = vec![0u8; 64 * 1024].into_boxed_slice();
    loop {
        let count = file
            .read(&mut buffer)
            .map_err(|error| format!("hash corpus manifest: {error}"))?;
        if count == 0 {
            break;
        }
        bytes = bytes
            .checked_add(count as u64)
            .ok_or("corpus manifest size overflow")?;
        if bytes > CORPUS_MANIFEST_LIMIT {
            return Err("corpus manifest grew past its byte limit".to_string());
        }
        hash.update(&buffer[..count]);
    }
    if bytes != metadata.len() {
        return Err("corpus manifest size changed during hashing".to_string());
    }
    Ok(format!("{:x}", hash.finalize()))
}

/// This internal worker inherits its parent's admitted process group, RSS
/// watchdog and file limit. It deliberately calls only the full pure corpus
/// APIs, so it cannot deadlock on a second aggregate admission lease.
pub(super) fn corpus_verify_child(args: &[String]) -> Result<i32, String> {
    if args.len() != 1 || args[0].len() > 64 * 1024 {
        return Err("corpus verification child needs one bounded typed request".to_string());
    }
    let request: CorpusWorkerRequest = serde_json::from_str(&args[0])
        .map_err(|error| format!("invalid corpus worker request: {error}"))?;
    if request.schema != "ay-official-corpus-worker-request/v1" {
        return Err("unsupported corpus worker request".to_string());
    }
    let phase = request.phase;
    let manifest = canonical_manifest_path(&request.manifest)?;
    if manifest != request.manifest {
        return Err("corpus worker manifest path is not canonical".to_string());
    }
    let manifest_sha256 = match phase {
        CorpusPhase::Create => {
            let create = request
                .create
                .as_ref()
                .ok_or("corpus creation inputs missing")?;
            if create.output != manifest {
                return Err("corpus creation output differs from worker manifest".to_string());
            }
            official_corpus::create_manifest_child(create)?;
            manifest_digest(&manifest)?
        }
        CorpusPhase::Authenticate => {
            if request.create.is_some() {
                return Err("authentication worker has unexpected creation inputs".to_string());
            }
            official_corpus::authenticate_materialization_child(&manifest)?
        }
    };
    let completion = CorpusCompletion {
        schema: "ay-official-corpus-completion/v1".to_string(),
        phase,
        manifest,
        manifest_sha256,
    };
    println!(
        "{CORPUS_COMPLETION_PREFIX}{}",
        serde_json::to_string(&completion).map_err(|error| error.to_string())?
    );
    Ok(0)
}

fn corpus_completion(
    phase: CorpusPhase,
    manifest: &Path,
    capture: &CorpusPhaseCapture,
) -> Result<CorpusCompletion, String> {
    if capture.exit_code != Some(0)
        || capture.signal.is_some()
        || capture.timed_out
        || capture.memout
        || !capture.stdin_complete
        || capture.stdout_truncated
        || capture.stderr_truncated
        || !capture.stderr.is_empty()
    {
        return Err(format!("corpus {} child failed: exit={:?}, signal={:?}, timeout={}, memout={}, stdin_complete={}, stdout_truncated={}, stderr_truncated={}; {}",
            phase.name(), capture.exit_code, capture.signal, capture.timed_out, capture.memout, capture.stdin_complete, capture.stdout_truncated, capture.stderr_truncated,
            String::from_utf8_lossy(&capture.stderr).chars().take(2048).collect::<String>()));
    }
    let stdout =
        std::str::from_utf8(&capture.stdout).map_err(|_| "corpus child stdout is not UTF-8")?;
    let lines = stdout
        .lines()
        .filter(|line| !line.trim().is_empty())
        .collect::<Vec<_>>();
    let completion_lines = lines
        .iter()
        .filter_map(|line| line.strip_prefix(CORPUS_COMPLETION_PREFIX))
        .collect::<Vec<_>>();
    if completion_lines.len() != 1
        || !lines
            .last()
            .is_some_and(|line| line.starts_with(CORPUS_COMPLETION_PREFIX))
    {
        return Err("corpus child lacks its unique final authenticated completion".to_string());
    }
    let completion: CorpusCompletion = serde_json::from_str(completion_lines[0])
        .map_err(|error| format!("invalid corpus completion: {error}"))?;
    if completion.schema != "ay-official-corpus-completion/v1"
        || completion.phase != phase
        || completion.manifest != manifest
    {
        return Err("corpus completion phase/path binding mismatch".to_string());
    }
    validate_sha256(&completion.manifest_sha256, "corpus completion manifest")?;
    Ok(completion)
}

fn canonical_manifest_path(manifest: &Path) -> Result<PathBuf, String> {
    let name = manifest
        .file_name()
        .ok_or("corpus manifest needs a file name")?;
    let parent = manifest
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let directory = fs::canonicalize(parent)
        .map_err(|error| format!("canonicalizing corpus manifest parent: {error}"))?;
    Ok(directory.join(name))
}

/// Authenticate the exact manifest selected by the caller. Existing semantic
/// owners lend their admission; only independent inventory/performance callers
/// acquire a new lease. The worker never calls this entry point recursively.
pub(super) fn authenticate_corpus_manifest(
    manifest: &Path,
    expected_sha256: &str,
    resources: Option<&PlannedResources>,
) -> Result<(), String> {
    validate_sha256(expected_sha256, "expected corpus manifest")?;
    if let Some(resources) = resources {
        corpus_phase_with_admission(
            manifest,
            CorpusPhase::Authenticate,
            Some(expected_sha256),
            None,
            Ok(resources),
        )
    } else {
        guarded_corpus_phase(
            manifest,
            CorpusPhase::Authenticate,
            Some(expected_sha256),
            None,
        )
    }
}

pub(super) fn create_corpus_manifest(
    inputs: &official_corpus::CorpusCreateInputs,
) -> Result<(), String> {
    guarded_corpus_phase(&inputs.output, CorpusPhase::Create, None, Some(inputs))
}

fn guarded_corpus_phase(
    manifest: &Path,
    phase: CorpusPhase,
    expected_sha256: Option<&str>,
    create: Option<&official_corpus::CorpusCreateInputs>,
) -> Result<(), String> {
    let admission = locate_repo_root().and_then(|root| {
        PlannedResources::plan(&root, 1, "complete official corpus verification")
            .map_err(|error| error.to_string())
    });
    // The owner remains alive through bounded parent identity checks and the
    // receipt write. Borrowing cannot release or reacquire its aggregate lease.
    corpus_phase_with_admission(
        manifest,
        phase,
        expected_sha256,
        create,
        admission.as_ref().map_err(Clone::clone),
    )
}

fn validate_completed_manifest(
    completion: &CorpusCompletion,
    after: &str,
    before: Option<&str>,
) -> Result<(), String> {
    if completion.manifest_sha256 != after || before.is_some_and(|before| before != after) {
        return Err(
            "corpus manifest changed or does not match completed full verification".to_string(),
        );
    }
    Ok(())
}

fn corpus_phase_with_admission(
    manifest: &Path,
    phase: CorpusPhase,
    expected_sha256: Option<&str>,
    create: Option<&official_corpus::CorpusCreateInputs>,
    admission: Result<&PlannedResources, String>,
) -> Result<(), String> {
    let manifest = canonical_manifest_path(manifest)?;
    let directory = manifest.parent().ok_or("corpus manifest has no parent")?;
    let mut receipt = CorpusPhaseReceipt {
        schema: "ay-official-corpus-provision-phase/v2".to_string(),
        phase,
        directory: directory.to_path_buf(),
        manifest: manifest.clone(),
        create: create.cloned(),
        worker_sha256: None,
        expected_manifest_sha256: expected_sha256.map(str::to_string),
        input_manifest_sha256: None,
        timeout_seconds: CORPUS_PHASE_TIMEOUT.as_secs(),
        per_file_limit_bytes: CORPUS_MANIFEST_LIMIT,
        per_stream_limit_bytes: ay_bench::GUARDED_TRANSCRIPT_STREAM_LIMIT,
        resource_envelope: None,
        capture: None,
        completion: None,
        passed: false,
        error: None,
    };
    // Keep the admitted owner in this scope through the parent's final bounded
    // identity checks and receipt write. No full-population work is repeated here.
    let resources = admission;
    let result = (|| -> Result<(), String> {
        let resources = resources.as_ref().map_err(Clone::clone)?;
        receipt.resource_envelope = Some(
            effective_execution_envelope(
                &resources.plan,
                ENFORCEMENT_RSS_WATCHDOG_V1,
                CORPUS_PHASE_TIMEOUT.as_secs_f64(),
            )
            .map_err(|error| error.to_string())?,
        );
        let worker = std::env::current_exe().map_err(|error| error.to_string())?;
        let worker_sha256 = sha256_file(&worker, "corpus verification worker")?;
        receipt.worker_sha256 = Some(worker_sha256.clone());
        if phase == CorpusPhase::Authenticate {
            receipt.input_manifest_sha256 = Some(manifest_digest(&manifest)?);
            if expected_sha256
                .is_some_and(|expected| receipt.input_manifest_sha256.as_deref() != Some(expected))
            {
                return Err(
                    "corpus manifest differs from the caller's authenticated input".to_string(),
                );
            }
        }
        let mut create = create.cloned();
        match (phase, create.as_mut()) {
            (CorpusPhase::Create, Some(inputs)) => inputs.output = manifest.clone(),
            (CorpusPhase::Authenticate, None) => {}
            _ => return Err("corpus phase/creation inputs mismatch".to_string()),
        }
        let request = CorpusWorkerRequest {
            schema: "ay-official-corpus-worker-request/v1".to_string(),
            phase,
            manifest: manifest.clone(),
            create,
        };
        receipt.create = request.create.clone();
        let args: Vec<OsString> = vec![
            "smtlib-conformance".into(),
            "provision-corpus-verify-child".into(),
            serde_json::to_string(&request)
                .map_err(|error| error.to_string())?
                .into(),
        ];
        let output = resources
            .run_external_transcript_scrubbed_with_file_limit(
                &worker,
                args,
                b"",
                CORPUS_PHASE_TIMEOUT,
                "complete official corpus verification",
                CORPUS_MANIFEST_LIMIT,
            )
            .map_err(|error| format!("corpus verification supervision failed: {error}"))?;
        receipt.capture = Some(CorpusPhaseCapture::from_output(output));
        let capture = receipt
            .capture
            .as_ref()
            .ok_or("corpus verification capture missing")?;
        let completion = corpus_completion(phase, &manifest, capture)?;
        let after = manifest_digest(&manifest)?;
        validate_completed_manifest(
            &completion,
            &after,
            receipt.input_manifest_sha256.as_deref(),
        )?;
        if sha256_file(&worker, "post-run corpus verification worker")? != worker_sha256 {
            return Err("corpus verification worker changed during execution".to_string());
        }
        receipt.completion = Some(completion);
        Ok(())
    })();
    receipt.passed = result.is_ok();
    receipt.error = result.as_ref().err().cloned();
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|error| error.to_string())?
        .as_nanos();
    let path = directory.join(format!(
        "corpus-{}-{}-{nonce}.json",
        phase.name(),
        std::process::id()
    ));
    atomic_write_new(&path, &pretty_json(&receipt)?)?;
    match result {
        Ok(()) => {
            println!("corpus_verification_receipt={}", path.display());
            Ok(())
        }
        Err(error) => Err(format!(
            "{error}; retained corpus verification receipt {}",
            path.display()
        )),
    }
}

pub(super) fn prepare(directory: &Path, access: NetworkAccess) -> Result<Provisioned, String> {
    reference_platform::Platform::native()?;
    fs::create_dir_all(directory)
        .map_err(|error| format!("create {}: {error}", directory.display()))?;
    let directory = fs::canonicalize(directory).map_err(|error| error.to_string())?;
    let profile = canonical_profile()?;
    let resources =
        PlannedResources::plan(&locate_repo_root()?, 1, "conformance input provisioning")
            .map_err(|error| error.to_string())?;
    let z3 = reference_artifact_path(&profile.z3_overlay.reference_executable.path)?;
    let z3_library = reference_artifact_path(&profile.z3_overlay.reference_shared_library.path)?;
    provision_release(&resources, &directory, &z3, &z3_library, access)?;

    let z3_source = directory.join("z3-source");
    provision_checkout(
        &resources,
        &z3_source,
        &profile.z3_overlay.source_repository,
        &profile.z3_overlay.source_commit,
        access,
    )?;
    provision_tag(
        &resources,
        &z3_source,
        &profile.z3_overlay.source_repository,
        &profile.z3_overlay.source_tag,
        &profile.z3_overlay.source_commit,
        access,
    )?;
    authenticate_z3_source(&resources, &z3_source, &profile.z3_overlay)?;

    let language_source = directory.join("smtlib-language-source");
    provision_checkout(
        &resources,
        &language_source,
        &profile.standard.language_sources.repository,
        &profile.standard.language_sources.revision,
        access,
    )?;
    let registry_source = directory.join("smtlib-registry-source");
    provision_checkout(
        &resources,
        &registry_source,
        &profile.standard.registry.repository,
        &profile.standard.registry.revision,
        access,
    )?;
    let normative_pdf = directory.join("smt-lib-reference-v2.7-r2026-03-27.pdf");
    if !normative_pdf.exists() {
        require_online(access, "normative SMT-LIB PDF")?;
        let url = format!("https://raw.githubusercontent.com/SMT-LIB/SMT-LIB.github.io/{}/papers/smt-lib-reference-v2.7-r2026-03-27.pdf", profile.standard.normative_pdf.revision);
        download(&resources, &url, &normative_pdf, 16 * 1024 * 1024)?;
    }
    verify_digest(
        &normative_pdf,
        &profile.standard.normative_pdf.sha256,
        "normative SMT-LIB PDF",
    )?;
    // The native Z3 snapshot extractor acquires its own supervised resource
    // lease. Finish provisioning children before entering that owner.
    drop(resources);
    let language_snapshot = directory.join("language-source.json");
    let registry_snapshot = directory.join("registry-source.json");
    let z3_snapshot = directory.join("z3-source.json");
    retain_authenticated_snapshot(
        &reference_inventory::create_snapshot(SnapshotKind::Language, &language_source, &profile)?,
        &language_snapshot,
    )?;
    retain_authenticated_snapshot(
        &reference_inventory::create_snapshot(SnapshotKind::Registry, &registry_source, &profile)?,
        &registry_snapshot,
    )?;
    retain_authenticated_snapshot(
        &z3_source_inventory::create_snapshot(&z3_source, &profile)?,
        &z3_snapshot,
    )?;
    let inputs = Provisioned {
        schema: "ay-conformance-provision/v2".to_string(),
        profile_id: profile.id,
        profile_sha256: canonical_profile_sha256()?,
        z3,
        z3_library,
        z3_source,
        z3_snapshot,
        language_source,
        registry_source,
        language_snapshot,
        registry_snapshot,
        normative_pdf,
    };
    replace_generated(&directory.join("provision.json"), &pretty_json(&inputs)?)?;
    Ok(inputs)
}

fn run_child(
    resources: &PlannedResources,
    program: &str,
    args: &[OsString],
    label: &str,
) -> Result<Vec<u8>, String> {
    let output = resources
        .run_external_transcript(program, args, b"", CHILD_TIMEOUT, label)
        .map_err(|error| format!("{label}: {error}"))?;
    if output.timed_out
        || output.memout
        || output.stdout_truncated
        || output.stderr_truncated
        || !output.status.is_some_and(|status| status.success())
    {
        return Err(format!(
            "{label}: child failed (timeout={}, memout={}, truncated={}); {}",
            output.timed_out,
            output.memout,
            output.stdout_truncated || output.stderr_truncated,
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    Ok(output.stdout)
}

fn require_online(access: NetworkAccess, missing: &str) -> Result<(), String> {
    if matches!(access, NetworkAccess::Offline) {
        Err(format!("offline provisioning: missing {missing}"))
    } else {
        Ok(())
    }
}

fn download(
    resources: &PlannedResources,
    url: &str,
    destination: &Path,
    max_bytes: u64,
) -> Result<(), String> {
    let parent = destination
        .parent()
        .ok_or("download destination has no parent")?;
    fs::create_dir_all(parent).map_err(|error| error.to_string())?;
    let temporary = tempfile::NamedTempFile::new_in(parent).map_err(|error| error.to_string())?;
    run_child(
        resources,
        "curl",
        &[
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
            max_bytes.to_string().into(),
            "--output".into(),
            temporary.path().as_os_str().to_owned(),
            url.into(),
        ],
        "download conformance input",
    )?;
    if temporary
        .as_file()
        .metadata()
        .map_err(|error| error.to_string())?
        .len()
        > max_bytes
    {
        return Err("download exceeded its byte limit".to_string());
    }
    temporary
        .persist_noclobber(destination)
        .map_err(|error| error.to_string())?;
    Ok(())
}

fn verify_digest(path: &Path, expected: &str, label: &str) -> Result<(), String> {
    let metadata = fs::symlink_metadata(path).map_err(|error| format!("{label}: {error}"))?;
    if !metadata.file_type().is_file() || metadata.file_type().is_symlink() {
        return Err(format!("{label} must be a regular non-symlink file"));
    }
    let actual = sha256_file(path, label)?;
    if actual != expected {
        return Err(format!("{label} digest mismatch: {actual} != {expected}"));
    }
    Ok(())
}

fn provision_release(
    resources: &PlannedResources,
    directory: &Path,
    z3: &Path,
    library: &Path,
    access: NetworkAccess,
) -> Result<(), String> {
    let profile = canonical_profile()?;
    let release = reference_platform::Release::native()?;
    if z3.exists() {
        verify_digest(
            z3,
            &profile.z3_overlay.reference_executable.sha256,
            "Z3 executable",
        )?;
    }
    if library.exists() {
        verify_digest(
            library,
            &profile.z3_overlay.reference_shared_library.sha256,
            "Z3 library",
        )?;
    }
    if z3.exists() && library.exists() {
        return Ok(());
    }
    require_online(access, "pinned Z3 release")?;
    let archive = directory.join(release.archive);
    if !archive.exists() {
        download(
            resources,
            &format!(
                "https://github.com/Z3Prover/z3/releases/download/z3-5.3.3/{}",
                release.archive
            ),
            &archive,
            release.archive_size,
        )?;
    }
    if fs::metadata(&archive)
        .map_err(|error| error.to_string())?
        .len()
        != release.archive_size
    {
        return Err("pinned Z3 archive has the wrong size".to_string());
    }
    verify_digest(&archive, release.archive_sha256, "Z3 archive")?;
    let cache_bin = z3.parent().ok_or("invalid canonical reference location")?;
    let cache_release = cache_bin
        .parent()
        .ok_or("invalid canonical release location")?;
    let cache_root = cache_release
        .parent()
        .ok_or("invalid canonical cache location")?;
    fs::create_dir_all(cache_root).map_err(|error| error.to_string())?;
    let staging = tempfile::tempdir_in(cache_root).map_err(|error| error.to_string())?;
    // Only explicitly named, flat members are extracted. Unrelated archive
    // paths, links, permissions, and traversal names are never materialized.
    run_child(
        resources,
        "unzip",
        &[
            "-j".into(),
            archive.as_os_str().to_owned(),
            release.member("z3").into(),
            release.member(release.platform.library_name()).into(),
            "-d".into(),
            staging.path().as_os_str().to_owned(),
        ],
        "extract pinned Z3 executable and library",
    )?;
    verify_digest(
        &staging.path().join("z3"),
        &profile.z3_overlay.reference_executable.sha256,
        "downloaded Z3 executable",
    )?;
    verify_digest(
        &staging.path().join(release.platform.library_name()),
        &profile.z3_overlay.reference_shared_library.sha256,
        "downloaded Z3 library",
    )?;
    fs::create_dir_all(cache_bin).map_err(|error| error.to_string())?;
    for (source, target) in [
        (staging.path().join("z3"), z3),
        (
            staging.path().join(release.platform.library_name()),
            library,
        ),
    ] {
        // A previously authenticated member may exist after an interrupted
        // installation. Never overwrite it; install only the missing member.
        if target.exists() {
            continue;
        }
        let mut output = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(target)
            .map_err(|error| format!("install {}: {error}", target.display()))?;
        let mut input = fs::File::open(&source).map_err(|error| error.to_string())?;
        io::copy(&mut input, &mut output).map_err(|error| error.to_string())?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(target, fs::Permissions::from_mode(0o555))
                .map_err(|error| error.to_string())?;
        }
    }
    verify_digest(
        z3,
        &profile.z3_overlay.reference_executable.sha256,
        "installed Z3 executable",
    )?;
    verify_digest(
        library,
        &profile.z3_overlay.reference_shared_library.sha256,
        "installed Z3 library",
    )
}

fn git(resources: &PlannedResources, path: &Path, args: &[&str]) -> Result<Vec<u8>, String> {
    let mut command = vec![
        "-c".into(),
        "core.hooksPath=/dev/null".into(),
        "-C".into(),
        path.as_os_str().to_owned(),
    ];
    command.extend(args.iter().map(OsString::from));
    run_child(resources, "git", &command, "provision authenticated source")
}

fn provision_checkout(
    resources: &PlannedResources,
    path: &Path,
    repository: &str,
    revision: &str,
    access: NetworkAccess,
) -> Result<(), String> {
    if !path.exists() {
        require_online(access, &format!("source {repository}@{revision}"))?;
        let parent = path.parent().ok_or("source destination has no parent")?;
        let staging = tempfile::tempdir_in(parent).map_err(|error| error.to_string())?;
        git(resources, staging.path(), &["init", "--quiet"])?;
        git(
            resources,
            staging.path(),
            &["fetch", "--quiet", "--depth=1", repository, revision],
        )?;
        git(
            resources,
            staging.path(),
            &["checkout", "--quiet", "--detach", revision],
        )?;
        fs::rename(staging.path(), path).map_err(|error| error.to_string())?;
    }
    let head = git(resources, path, &["rev-parse", "HEAD"])?;
    if String::from_utf8_lossy(&head).trim() != revision {
        return Err(format!(
            "{} is not the pinned source revision {revision}",
            path.display()
        ));
    }
    let dirty = git(
        resources,
        path,
        &["status", "--porcelain", "--untracked-files=all"],
    )?;
    if !dirty.is_empty() {
        return Err(format!(
            "{} contains modified or untracked source",
            path.display()
        ));
    }
    Ok(())
}

fn provision_tag(
    resources: &PlannedResources,
    path: &Path,
    repository: &str,
    tag: &str,
    revision: &str,
    access: NetworkAccess,
) -> Result<(), String> {
    let tag_ref = format!("refs/tags/{tag}");
    let present = git(
        resources,
        path,
        &["for-each-ref", "--format=%(refname)", &tag_ref],
    )?;
    if !String::from_utf8_lossy(&present)
        .lines()
        .any(|name| name == tag_ref)
    {
        require_online(access, &format!("source tag {tag}"))?;
        let refspec = format!("{tag_ref}:{tag_ref}");
        git(
            resources,
            path,
            &[
                "fetch",
                "--quiet",
                "--no-tags",
                "--depth=1",
                repository,
                &refspec,
            ],
        )?;
    }
    let resolved = git(
        resources,
        path,
        &["rev-parse", "--verify", &format!("{tag_ref}^{{commit}}")],
    )?;
    if String::from_utf8_lossy(&resolved).trim() != revision {
        return Err(format!(
            "source tag {tag} does not resolve to pinned revision {revision}"
        ));
    }
    Ok(())
}

fn authenticate_z3_source(
    resources: &PlannedResources,
    source: &Path,
    target: &Z3Target,
) -> Result<(), String> {
    let tree = git(
        resources,
        source,
        &["ls-tree", "-r", "-l", "-z", &target.source_commit],
    )?;
    let mut entries = BTreeMap::new();
    for raw in tree
        .split(|byte| *byte == 0)
        .filter(|entry| !entry.is_empty())
    {
        let raw = std::str::from_utf8(raw).map_err(|error| error.to_string())?;
        let (header, path) = raw.split_once('\t').ok_or("malformed Z3 tree record")?;
        validate_relative_path(path, "Z3 source file")?;
        let fields = header.split_whitespace().collect::<Vec<_>>();
        if fields.len() != 4 || fields[1] != "blob" || !matches!(fields[0], "100644" | "100755") {
            return Err(format!("unsupported Z3 source tree entry: {path}"));
        }
        let size = fields[3]
            .parse::<u64>()
            .map_err(|error| error.to_string())?;
        if size > MAX_SOURCE_FILE_BYTES {
            return Err(format!("oversized source file: {path}"));
        }
        let file = source.join(path);
        let metadata = fs::symlink_metadata(&file).map_err(|error| error.to_string())?;
        if !metadata.file_type().is_file() || metadata.len() != size {
            return Err(format!("source file size/type mismatch: {path}"));
        }
        let bytes = fs::read(file).map_err(|error| error.to_string())?;
        let mut hash = sha1::Sha1::new();
        hash.update(format!("blob {size}\0").as_bytes());
        hash.update(&bytes);
        if format!("{:x}", hash.finalize()) != fields[2] {
            return Err(format!("source blob mismatch: {path}"));
        }
        if entries
            .insert(path.to_owned(), format!("{path}\t{}\t{size}\n", fields[2]))
            .is_some()
        {
            return Err(format!("duplicate source path: {path}"));
        }
    }
    let manifest = entries.values().cloned().collect::<String>();
    if entries.len() != target.tracked_source_file_count
        || sha256_bytes(manifest.as_bytes()) != target.tracked_source_tree_sha256
    {
        return Err("Z3 full source tree does not match the closed profile".to_string());
    }
    Ok(())
}

fn retain_authenticated_snapshot<T: Serialize>(
    snapshot: &T,
    destination: &Path,
) -> Result<(), String> {
    // The extractors have authenticated the selected path/blob/size manifests
    // and contents. Compare the fresh serialization byte-for-byte.
    let bytes = pretty_json(snapshot)?;
    if destination.exists() {
        if fs::read(destination).map_err(|error| error.to_string())? != bytes {
            return Err(format!(
                "{} is not the authenticated source snapshot",
                destination.display()
            ));
        }
        Ok(())
    } else {
        atomic_write_new(destination, &bytes)
    }
}

fn replace_generated(path: &Path, bytes: &[u8]) -> Result<(), String> {
    if path.exists() {
        if fs::read(path).map_err(|error| error.to_string())? == bytes {
            return Ok(());
        }
        return Err(format!(
            "refusing to replace different provisioning manifest {}",
            path.display()
        ));
    }
    atomic_write_new(path, bytes)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn commit_only_checkouts_acquire_the_pinned_tag_and_refuse_a_foreign_one() {
        let _resource_guard = resource_test_lock();
        let temporary = tempfile::tempdir().unwrap();
        let source = temporary.path().join("source");
        let destination = temporary.path().join("destination");
        fs::create_dir(&source).unwrap();
        let resources = PlannedResources::plan(
            &locate_repo_root().unwrap(),
            1,
            "pinned source tag regression",
        )
        .unwrap();
        git(&resources, &source, &["init", "--quiet", "-b", "main"]).unwrap();
        git(
            &resources,
            &source,
            &[
                "-c",
                "user.name=AY test",
                "-c",
                "user.email=ay-test@example.invalid",
                "-c",
                "commit.gpgsign=false",
                "commit",
                "--quiet",
                "--allow-empty",
                "-m",
                "fixture",
            ],
        )
        .unwrap();
        git(
            &resources,
            &source,
            &["-c", "tag.gpgsign=false", "tag", "fixture"],
        )
        .unwrap();
        let commit = git(&resources, &source, &["rev-parse", "HEAD"]).unwrap();
        let commit = std::str::from_utf8(&commit).unwrap().trim();
        let repository = source.to_str().unwrap();
        provision_checkout(
            &resources,
            &destination,
            repository,
            commit,
            NetworkAccess::Online,
        )
        .unwrap();
        git(
            &resources,
            &destination,
            &["update-ref", "-d", "refs/tags/fixture"],
        )
        .unwrap();
        git(
            &resources,
            &destination,
            &["update-ref", "refs/tags/fixture-other", "HEAD"],
        )
        .unwrap();
        assert!(provision_tag(
            &resources,
            &destination,
            repository,
            "fixture",
            commit,
            NetworkAccess::Offline
        )
        .is_err());
        provision_tag(
            &resources,
            &destination,
            repository,
            "fixture",
            commit,
            NetworkAccess::Online,
        )
        .unwrap();
        provision_tag(
            &resources,
            &destination,
            repository,
            "fixture",
            commit,
            NetworkAccess::Offline,
        )
        .unwrap();
        #[expect(
            clippy::literal_string_with_formatting_args,
            reason = "HEAD^{tree} is Git revision syntax with literal braces"
        )]
        let tree = git(&resources, &destination, &["rev-parse", "HEAD^{tree}"]).unwrap();
        let tree = std::str::from_utf8(&tree).unwrap().trim();
        git(
            &resources,
            &destination,
            &["update-ref", "refs/tags/fixture", tree],
        )
        .unwrap();
        assert!(provision_tag(
            &resources,
            &destination,
            repository,
            "fixture",
            commit,
            NetworkAccess::Offline
        )
        .is_err());
    }

    #[test]
    fn corrupted_cached_artifact_is_refused() {
        let directory = tempfile::tempdir().unwrap();
        let file = directory.path().join("artifact");
        fs::write(&file, b"wrong").unwrap();
        assert!(verify_digest(&file, &sha256_bytes(b"right"), "fixture").is_err());
        assert!(verify_digest(&file, &sha256_bytes(b"wrong"), "fixture").is_ok());
    }

    #[test]
    fn offline_missing_input_is_not_success() {
        assert!(require_online(NetworkAccess::Offline, "reference executable").is_err());
        assert!(require_online(NetworkAccess::Online, "reference executable").is_ok());
    }

    #[test]
    fn offline_corpus_requires_retained_evidence_without_creating_it() {
        let directory = tempfile::tempdir().unwrap();
        let absent = directory.path().join("absent");
        assert!(prepare_corpus_with_access(&absent, NetworkAccess::Offline).is_err());
        assert!(!absent.exists());
        assert!(prepare_corpus_with_access(directory.path(), NetworkAccess::Offline).is_err());
        assert_eq!(fs::read_dir(directory.path()).unwrap().count(), 0);
    }

    #[test]
    fn corpus_provisioning_does_not_replace_an_invalid_manifest() {
        let directory = tempfile::tempdir().unwrap();
        let manifest = directory.path().join("official-corpus.json");
        fs::write(&manifest, b"invalid retained evidence").unwrap();
        for phase in [CorpusPhase::Create, CorpusPhase::Authenticate] {
            let request = CorpusWorkerRequest {
                schema: "ay-official-corpus-worker-request/v1".to_string(),
                phase,
                manifest: canonical_manifest_path(&manifest).unwrap(),
                create: (phase == CorpusPhase::Create).then(|| {
                    official_corpus::CorpusCreateInputs {
                        root: directory.path().join("corpus"),
                        archive_root: directory.path().join("archives"),
                        metadata: directory.path().join("metadata.json"),
                        output: canonical_manifest_path(&manifest).unwrap(),
                    }
                }),
            };
            assert!(corpus_verify_child(&[serde_json::to_string(&request).unwrap()]).is_err());
            assert_eq!(fs::read(&manifest).unwrap(), b"invalid retained evidence");
            assert_eq!(fs::read_dir(directory.path()).unwrap().count(), 1);
        }
    }

    fn completed_capture(manifest: &Path, phase: CorpusPhase) -> CorpusPhaseCapture {
        let completion = CorpusCompletion {
            schema: "ay-official-corpus-completion/v1".to_string(),
            phase,
            manifest: manifest.to_path_buf(),
            manifest_sha256: sha256_bytes(b"manifest"),
        };
        CorpusPhaseCapture {
            exit_code: Some(0),
            signal: None,
            timed_out: false,
            memout: false,
            stdin_complete: true,
            stdout_truncated: false,
            stderr_truncated: false,
            stdout: format!(
                "{CORPUS_COMPLETION_PREFIX}{}\n",
                serde_json::to_string(&completion).unwrap()
            )
            .into_bytes(),
            stderr: vec![],
        }
    }

    #[test]
    fn corpus_completion_requires_exact_binding_and_restricted_subset_termination() {
        let directory = tempfile::tempdir().unwrap();
        // The caller's explicit path is authoritative, not a conventional
        // file name inferred from its directory.
        let manifest = directory.path().join("custom-corpus-evidence.json");
        let captured = completed_capture(&manifest, CorpusPhase::Create);
        let completed = corpus_completion(CorpusPhase::Create, &manifest, &captured).unwrap();
        validate_completed_manifest(&completed, &sha256_bytes(b"manifest"), None).unwrap();
        assert!(validate_completed_manifest(&completed, &sha256_bytes(b"changed"), None).is_err());
        assert!(validate_completed_manifest(
            &completed,
            &sha256_bytes(b"manifest"),
            Some(&sha256_bytes(b"before"))
        )
        .is_err());
        assert!(corpus_completion(CorpusPhase::Authenticate, &manifest, &captured).is_err());
        assert!(corpus_completion(
            CorpusPhase::Create,
            &directory.path().join("official-corpus.json"),
            &captured
        )
        .is_err());
        for failure in 0..8 {
            let mut changed = captured.clone();
            match failure {
                0 => changed.exit_code = Some(1),
                1 => changed.signal = Some(9),
                2 => changed.timed_out = true,
                3 => changed.memout = true,
                4 => changed.stdin_complete = false,
                5 => changed.stdout_truncated = true,
                6 => changed.stderr_truncated = true,
                _ => changed.stderr = b"incomplete validation".to_vec(),
            }
            assert!(corpus_completion(CorpusPhase::Create, &manifest, &changed).is_err());
        }
        let mut changed = captured.clone();
        changed.stdout.clear();
        assert!(corpus_completion(CorpusPhase::Create, &manifest, &changed).is_err());
        let mut changed = captured.clone();
        changed.stdout.extend_from_slice(&captured.stdout);
        assert!(corpus_completion(CorpusPhase::Create, &manifest, &changed).is_err());
        let mut changed = captured;
        changed.stdout.extend_from_slice(b"unfinished work\n");
        assert!(corpus_completion(CorpusPhase::Create, &manifest, &changed).is_err());
    }

    #[test]
    fn admission_failure_retains_failure_and_performs_no_corpus_work() {
        let directory = tempfile::tempdir().unwrap();
        let manifest = directory.path().join("custom-manifest.json");
        fs::write(&manifest, b"unchanged malformed manifest").unwrap();
        let error = corpus_phase_with_admission(
            &manifest,
            CorpusPhase::Authenticate,
            Some(&sha256_bytes(b"unchanged malformed manifest")),
            None,
            Err("fixture admission refused".to_string()),
        )
        .unwrap_err();
        assert!(error.contains("fixture admission refused"));
        assert_eq!(
            fs::read(&manifest).unwrap(),
            b"unchanged malformed manifest"
        );
        assert!(!directory.path().join("corpus").exists());
        let receipts = fs::read_dir(directory.path())
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| {
                path.file_name()
                    .unwrap()
                    .to_string_lossy()
                    .starts_with("corpus-authenticate-")
            })
            .collect::<Vec<_>>();
        assert_eq!(receipts.len(), 1);
        let receipt: CorpusPhaseReceipt =
            serde_json::from_slice(&fs::read(&receipts[0]).unwrap()).unwrap();
        assert!(!receipt.passed);
        assert_eq!(
            receipt.manifest,
            canonical_manifest_path(&manifest).unwrap()
        );
        assert_eq!(
            receipt.expected_manifest_sha256,
            Some(sha256_bytes(b"unchanged malformed manifest"))
        );
        assert_eq!(receipt.error.as_deref(), Some("fixture admission refused"));
        assert!(
            receipt.resource_envelope.is_none()
                && receipt.capture.is_none()
                && receipt.completion.is_none()
                && receipt.worker_sha256.is_none()
        );
    }

    #[test]
    fn create_admission_refusal_never_enters_raw_scan_or_changes_output() {
        let directory = tempfile::tempdir().unwrap();
        let output = directory.path().join("arbitrary-output.json");
        fs::write(&output, b"existing evidence").unwrap();
        let inputs = official_corpus::CorpusCreateInputs {
            root: directory.path().join("missing-corpus"),
            archive_root: directory.path().join("missing-archives"),
            metadata: directory.path().join("missing-metadata"),
            output: output.clone(),
        };
        let error = corpus_phase_with_admission(
            &output,
            CorpusPhase::Create,
            None,
            Some(&inputs),
            Err("creation admission refused".to_string()),
        )
        .unwrap_err();
        assert!(error.contains("creation admission refused"));
        assert_eq!(fs::read(&output).unwrap(), b"existing evidence");
        assert!(!inputs.root.exists());
        // The raw worker reports its input failure directly; it never tries to
        // reacquire admission or manufacture another phase receipt.
        let before = fs::read_dir(directory.path()).unwrap().count();
        let request = CorpusWorkerRequest {
            schema: "ay-official-corpus-worker-request/v1".to_string(),
            phase: CorpusPhase::Create,
            manifest: canonical_manifest_path(&output).unwrap(),
            create: Some(official_corpus::CorpusCreateInputs {
                output: canonical_manifest_path(&output).unwrap(),
                ..inputs
            }),
        };
        assert!(
            corpus_verify_child(&[serde_json::to_string(&request).unwrap()])
                .unwrap_err()
                .contains("missing-metadata")
        );
        assert_eq!(fs::read_dir(directory.path()).unwrap().count(), before);
        assert_eq!(fs::read(&output).unwrap(), b"existing evidence");
    }

    #[test]
    fn manifest_hash_refuses_nonregular_and_oversized_inputs_before_reading() {
        let directory = tempfile::tempdir().unwrap();
        assert!(manifest_digest(directory.path()).is_err());
        let path = directory.path().join("manifest.json");
        let file = fs::File::create(&path).unwrap();
        file.set_len(CORPUS_MANIFEST_LIMIT + 1).unwrap();
        assert!(manifest_digest(&path).is_err());
        file.set_len(0).unwrap();
        fs::write(&path, b"exact bytes").unwrap();
        assert_eq!(
            manifest_digest(&path).unwrap(),
            sha256_bytes(b"exact bytes")
        );
        #[cfg(unix)]
        {
            let linked = directory.path().join("linked.json");
            std::os::unix::fs::symlink(&path, &linked).unwrap();
            assert!(manifest_digest(&linked).is_err());
        }
    }

    #[test]
    fn resume_does_not_overwrite_provenance() {
        let directory = tempfile::tempdir().unwrap();
        let file = directory.path().join("manifest.json");
        replace_generated(&file, b"first").unwrap();
        replace_generated(&file, b"first").unwrap();
        assert!(replace_generated(&file, b"second").is_err());
        assert_eq!(fs::read(file).unwrap(), b"first");
    }
}
