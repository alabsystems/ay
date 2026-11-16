// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Current-profile source and public metadata custody. This replaces the
//! obsolete 5.1.0 extractor as a way to MEASURE 5.3.3; it does not turn a list
//! of names into evidence that AY implements their behavior.

use super::*;
use std::ffi::OsString;

const SCHEMA: &str = "ay-current-z3-source-inventory/v1";
const MAX_SOURCE_BYTES: u64 = 64 * 1024 * 1024;
const MAX_SNAPSHOT_BYTES: u64 = 64 * 1024 * 1024;
const MAX_CANDIDATES: usize = 100_000;
const TIMEOUT: Duration = Duration::from_secs(30);

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct SourceFile {
    path: String,
    git_blob: String,
    size: u64,
    sha256: String,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct SourceCandidate {
    path: String,
    line: usize,
    text: String,
    /// Candidates deliberately remain unclassified. Classifying all source
    /// occurrences needs an actual ownership argument, not a keyword match.
    disposition: String,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Catalog {
    flag: String,
    entries: BTreeMap<String, String>,
    stdout: String,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Snapshot {
    schema: String,
    profile_id: String,
    profile_sha256: String,
    source_repository: String,
    source_commit: String,
    source_path: PathBuf,
    source_tree_sha256: String,
    source_files: Vec<SourceFile>,
    header_sha256: BTreeMap<String, String>,
    declarations: BTreeMap<String, Value>,
    enum_constants: BTreeMap<String, Value>,
    catalogs: BTreeMap<String, Catalog>,
    source_candidates: Vec<SourceCandidate>,
    z3_executable_sha256: String,
    z3_version_stdout: String,
    clang_version_stdout: String,
    source_bytes_authenticated: bool,
    measured_public_metadata_complete: bool,
    source_semantics_inventory_complete: bool,
    ay_behavior_validated: bool,
    blockers: Vec<String>,
}

pub(super) fn run(args: &[String]) -> Result<i32, String> {
    if args
        .iter()
        .any(|arg| matches!(arg.as_str(), "--help" | "-h"))
    {
        println!("smtlib-conformance current-release-inventory --source DIR --out FILE [--z3 FILE]\n\nAuthenticate the profile-pinned source tree and executable; extract the current\nC declarations, enum values and full public catalogs. Source registration\ncandidates remain explicit unresolved obligations. This command does not\nclaim API behavior, complete source semantics, or Z3 replacement parity.");
        return Ok(0);
    }
    let mut source = None;
    let mut output = None;
    let mut z3 = None;
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--source" => source = Some(PathBuf::from(args.next().ok_or("--source needs a path")?)),
            "--out" => output = Some(PathBuf::from(args.next().ok_or("--out needs a path")?)),
            "--z3" => z3 = Some(PathBuf::from(args.next().ok_or("--z3 needs a path")?)),
            other => {
                return Err(format!(
                    "unknown current-release-inventory argument {other:?}"
                ))
            }
        }
    }
    let source = source.ok_or("current-release-inventory requires --source DIR")?;
    let output = output.ok_or("current-release-inventory requires --out FILE")?;
    let profile = canonical_profile()?;
    let z3 = z3.unwrap_or(reference_artifact_path(
        &profile.z3_overlay.reference_executable.path,
    )?);
    write_inventory(&source, &z3, &output)?;
    println!("current_release_inventory={} source_authenticated=true public_metadata_measured=true source_semantics_complete=false ay_behavior_validated=false", output.display());
    Ok(0)
}

pub(super) fn write_inventory(source: &Path, z3: &Path, output: &Path) -> Result<(), String> {
    let snapshot = collect(source, z3)?;
    let bytes = pretty_json(&snapshot)?;
    if bytes.len() as u64 > MAX_SNAPSHOT_BYTES {
        return Err("current source inventory exceeds its byte bound".to_string());
    }
    atomic_write_new(output, &bytes)
}

pub(super) fn check(args: &[String]) -> Result<i32, String> {
    if args.len() != 1 {
        return Err("usage: smtlib-conformance current-release-check FILE".to_string());
    }
    let file = Path::new(&args[0]);
    let mut reader = fs::File::open(file)
        .map_err(|error| error.to_string())?
        .take(MAX_SNAPSHOT_BYTES + 1);
    let mut bytes = Vec::new();
    reader
        .read_to_end(&mut bytes)
        .map_err(|error| error.to_string())?;
    if bytes.len() as u64 > MAX_SNAPSHOT_BYTES {
        return Err("current source inventory exceeds its bound".to_string());
    }
    let snapshot: Snapshot = serde_json::from_slice(&bytes).map_err(|error| error.to_string())?;
    validate_shape(&snapshot)?;
    let z3 = reference_artifact_path(&canonical_profile()?.z3_overlay.reference_executable.path)?;
    let current = collect(&snapshot.source_path, &z3)?;
    if snapshot != current {
        return Err(
            "current release inventory differs from authenticated source/runtime replay"
                .to_string(),
        );
    }
    println!("current_release_inventory_replay=PASS source_semantics_complete=false ay_behavior_validated=false");
    Ok(0)
}

fn collect(source: &Path, z3: &Path) -> Result<Snapshot, String> {
    let profile = canonical_profile()?;
    let target = &profile.z3_overlay;
    let source = fs::canonicalize(source).map_err(|error| error.to_string())?;
    let resources = PlannedResources::plan(&locate_repo_root()?, 1, "current Z3 source inventory")
        .map_err(|error| error.to_string())?;
    let git = |args: &[&str]| {
        let mut flags = vec![OsString::from("-C"), source.as_os_str().to_owned()];
        flags.extend(args.iter().map(OsString::from));
        capture(
            &resources,
            Path::new("git"),
            &flags,
            "read pinned Z3 source",
        )
    };
    if git(&["rev-parse", "HEAD"])?.trim() != target.source_commit {
        return Err("Z3 source checkout is not the profile-pinned revision".to_string());
    }
    if !git(&["status", "--porcelain", "--untracked-files=all"])?.is_empty() {
        return Err("Z3 source checkout has modified or untracked files".to_string());
    }
    let tree = parse_tree(&git(&["ls-tree", "-r", "-l", "-z", &target.source_commit])?)?;
    let source_tree_sha256 = tree_digest(&tree);
    if tree.len() != target.tracked_source_file_count
        || source_tree_sha256 != target.tracked_source_tree_sha256
    {
        return Err("current Z3 source tree does not match profile count/digest".to_string());
    }
    let staged_headers = tempfile::tempdir().map_err(|error| error.to_string())?;
    let mut source_files = Vec::with_capacity(tree.len());
    let mut source_candidates = Vec::new();
    let mut header_sha256 = BTreeMap::new();
    for (path, blob, size) in tree {
        let bytes = authenticated_source_bytes(&source.join(&path), &blob, size)?;
        let sha256 = sha256_bytes(&bytes);
        #[expect(
            clippy::case_sensitive_file_extension_comparisons,
            reason = "pinned source paths require the exact lowercase .h suffix"
        )]
        if let Some(relative) = path
            .strip_prefix("src/api/")
            .filter(|path| path.ends_with(".h"))
        {
            let destination = staged_headers.path().join(relative);
            if let Some(parent) = destination.parent() {
                fs::create_dir_all(parent).map_err(|error| error.to_string())?;
            }
            fs::write(destination, &bytes).map_err(|error| error.to_string())?;
            header_sha256.insert(relative.to_string(), sha256.clone());
        }
        if path.starts_with("src/") || path.starts_with("scripts/") {
            if let Ok(text) = std::str::from_utf8(&bytes) {
                for (line, text) in text.lines().enumerate() {
                    if registration_candidate(text) {
                        if source_candidates.len() >= MAX_CANDIDATES {
                            return Err("source candidate inventory exceeds its bound".to_string());
                        }
                        source_candidates.push(SourceCandidate {
                            path: path.clone(),
                            line: line + 1,
                            text: text.to_string(),
                            disposition: "unclassified-source-obligation".to_string(),
                        });
                    }
                }
            }
        }
        source_files.push(SourceFile {
            path,
            git_blob: blob,
            size,
            sha256,
        });
    }
    if !header_sha256.contains_key("z3.h") {
        return Err("authenticated source has no public z3.h".to_string());
    }
    let (declarations, enum_constants) =
        crate::release_inventory::clang_inventory(staged_headers.path())?;
    // These are invariants of this immutable profile, not floors that a new
    // release may silently extend without revisiting the measured inventory.
    if declarations.len() != 817 || enum_constants.len() != 370 {
        return Err(format!(
            "current public header inventory drift: {}/817 declarations, {}/370 enums",
            declarations.len(),
            enum_constants.len()
        ));
    }
    let staged_z3 = stage_authenticated_executable(
        z3,
        &target.reference_executable.sha256,
        "current Z3 executable",
    )?;
    let z3_version_stdout = capture(
        &resources,
        &staged_z3.path,
        &["-version".into()],
        "Z3 identity",
    )?;
    if z3_version_stdout.trim() != target.reference_executable.version_output {
        return Err("profile-pinned Z3 version transcript drift".to_string());
    }
    let mut catalogs = BTreeMap::new();
    for (name, flag, expected) in [
        ("tactics", "-tactics", 123),
        ("probes", "-probes", 42),
        ("simplifiers", "-simplifiers", 44),
        ("parameters", "-p", 763),
    ] {
        let stdout = capture(
            &resources,
            &staged_z3.path,
            &[flag.into(), "-in".into()],
            name,
        )?;
        let entries = if name == "parameters" {
            parameters(&stdout)?
        } else {
            public_catalog(&stdout)?
        };
        if entries.len() != expected {
            return Err(format!(
                "pinned {name} inventory drift: {}/{expected}",
                entries.len()
            ));
        }
        catalogs.insert(
            name.to_string(),
            Catalog {
                flag: flag.to_string(),
                entries,
                stdout,
            },
        );
    }
    let clang_version_stdout = capture(
        &resources,
        Path::new("clang"),
        &["--version".into()],
        "Clang inventory parser identity",
    )?;
    let snapshot = Snapshot {
        schema: SCHEMA.to_string(), profile_id: profile.id.clone(), profile_sha256: canonical_profile_sha256()?,
        source_repository: target.source_repository.clone(), source_commit: target.source_commit.clone(), source_path: source,
        source_tree_sha256, source_files, header_sha256, declarations, enum_constants, catalogs, source_candidates,
        z3_executable_sha256: target.reference_executable.sha256.clone(), z3_version_stdout, clang_version_stdout,
        source_bytes_authenticated: true, measured_public_metadata_complete: true,
        source_semantics_inventory_complete: false, ay_behavior_validated: false,
        blockers: vec!["Source registration candidates require item-level classification and behavioral ownership; complete source bytes are not complete semantic coverage.".to_string(),
            "Public declarations and catalogs do not establish AY exported-symbol resolution, API lifetimes, solver effects, binding behavior, or CLI transcript compatibility.".to_string()],
    };
    validate_shape(&snapshot)?;
    Ok(snapshot)
}

fn capture(
    resources: &PlannedResources,
    program: &Path,
    args: &[OsString],
    label: &str,
) -> Result<String, String> {
    let output = resources
        .run_external_transcript(program, args, b"", TIMEOUT, label)
        .map_err(|error| error.to_string())?;
    if output.timed_out
        || output.memout
        || output.stdout_truncated
        || output.stderr_truncated
        || !output.status.is_some_and(|status| status.success())
        || !output.stderr.is_empty()
    {
        return Err(format!(
            "{label} failed or incomplete: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    String::from_utf8(output.stdout).map_err(|error| format!("{label} is not UTF-8: {error}"))
}

fn parse_tree(text: &str) -> Result<Vec<(String, String, u64)>, String> {
    let mut tree = BTreeMap::new();
    for record in text.split('\0').filter(|record| !record.is_empty()) {
        let (header, path) = record
            .split_once('\t')
            .ok_or("malformed source tree entry")?;
        validate_relative_path(path, "source tree path")?;
        let fields = header.split_whitespace().collect::<Vec<_>>();
        if fields.len() != 4 || fields[1] != "blob" || !matches!(fields[0], "100644" | "100755") {
            return Err("source tree contains a link or unsupported object".to_string());
        }
        let size = fields[3]
            .parse::<u64>()
            .map_err(|error| error.to_string())?;
        if size > MAX_SOURCE_BYTES
            || fields[2].len() != 40
            || !fields[2].bytes().all(|byte| byte.is_ascii_hexdigit())
        {
            return Err("invalid source blob identity or size".to_string());
        }
        if tree
            .insert(path.to_string(), (fields[2].to_string(), size))
            .is_some()
        {
            return Err("duplicate source tree path".to_string());
        }
    }
    if tree.is_empty() {
        return Err("empty source tree".to_string());
    }
    Ok(tree
        .into_iter()
        .map(|(path, (blob, size))| (path, blob, size))
        .collect())
}

fn tree_digest(tree: &[(String, String, u64)]) -> String {
    let mut hash = Sha256::new();
    for (path, blob, size) in tree {
        hash.update(format!("{path}\t{blob}\t{size}\n").as_bytes());
    }
    format!("{:x}", hash.finalize())
}

fn authenticated_source_bytes(path: &Path, blob: &str, size: u64) -> Result<Vec<u8>, String> {
    let metadata = fs::symlink_metadata(path).map_err(|error| error.to_string())?;
    if !metadata.file_type().is_file() || metadata.len() != size {
        return Err(format!("source file type/size drift: {}", path.display()));
    }
    let mut bytes = Vec::new();
    fs::File::open(path)
        .map_err(|error| error.to_string())?
        .take(MAX_SOURCE_BYTES + 1)
        .read_to_end(&mut bytes)
        .map_err(|error| error.to_string())?;
    let mut hash = sha1::Sha1::new();
    hash.update(format!("blob {}\0", bytes.len()).as_bytes());
    hash.update(&bytes);
    if bytes.len() as u64 != size || format!("{:x}", hash.finalize()) != blob {
        return Err(format!("source blob mismatch: {}", path.display()));
    }
    Ok(bytes)
}

fn registration_candidate(line: &str) -> bool {
    [
        "tactic",
        "probe",
        "simplif",
        "install_cmd",
        "register_cmd",
        "cmd_context",
        "REG_PARAMS",
        "gparams",
        "parameter",
        "IN_",
        "is_option",
        "strcmp",
        "extension",
    ]
    .iter()
    .any(|token| line.contains(token))
}

fn public_catalog(text: &str) -> Result<BTreeMap<String, String>, String> {
    if !text.ends_with('\n') {
        return Err("truncated public catalog line".to_string());
    }
    for line in text.lines().filter(|line| !line.trim().is_empty()) {
        let (name, _) = line
            .strip_prefix("- ")
            .and_then(|line| line.split_once(' '))
            .ok_or("unrecognized public catalog output")?;
        if !catalog_identifier(name) {
            return Err("invalid public catalog name".to_string());
        }
    }
    let parsed = crate::release_inventory::observed_catalog(text)?;
    parsed
        .into_iter()
        .map(|(name, value)| {
            value
                .as_str()
                .map(|value| (name, value.to_string()))
                .ok_or("catalog descriptor is not text".to_string())
        })
        .collect()
}

fn parameters(text: &str) -> Result<BTreeMap<String, String>, String> {
    if !text.ends_with('\n') {
        return Err("truncated parameter catalog".to_string());
    }
    let mut entries = BTreeMap::new();
    let mut modules = BTreeSet::new();
    let mut module = "";
    let mut global_header = false;
    for raw in text.lines() {
        let line = raw.trim();
        if line.is_empty() {
            continue;
        }
        if line == "Global parameters" {
            if global_header {
                return Err("duplicate global parameter header".to_string());
            }
            global_header = true;
            continue;
        }
        if !global_header {
            return Err("missing global parameter header".to_string());
        }
        if line == "To set a module parameter, use <module-name>.<parameter-name>=value"
            || line == "Example:  pp.decimal=true"
        {
            if !module.is_empty() {
                return Err("global parameter advice inside module".to_string());
            }
            continue;
        }
        if let Some(rest) = line.strip_prefix("[module] ") {
            let name = rest
                .split_once(", description: ")
                .map_or(rest, |(name, _)| name);
            if !catalog_identifier(name) || !modules.insert(name) {
                return Err("invalid/duplicate parameter module".to_string());
            }
            module = name;
            continue;
        }
        let (name, descriptor) = line
            .split_once(" (")
            .ok_or("invalid parameter descriptor")?;
        let (kind, suffix) = descriptor
            .split_once(')')
            .ok_or("truncated parameter kind")?;
        if !catalog_identifier(name)
            || kind.is_empty()
            || kind.contains('(')
            || !(suffix.is_empty() || suffix.starts_with(" (default: ") && suffix.ends_with(')'))
        {
            return Err("malformed parameter row".to_string());
        }
        let key = if module.is_empty() {
            name.to_string()
        } else {
            format!("{module}.{name}")
        };
        if entries.insert(key, format!("({descriptor}")).is_some() {
            return Err("duplicate parameter name".to_string());
        }
    }
    if entries.is_empty() {
        return Err("empty parameter catalog".to_string());
    }
    Ok(entries)
}

fn catalog_identifier(text: &str) -> bool {
    !text.is_empty()
        && text
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'.' | b'-'))
}

fn validate_shape(snapshot: &Snapshot) -> Result<(), String> {
    let profile = canonical_profile()?;
    if snapshot.schema != SCHEMA
        || snapshot.profile_id != profile.id
        || snapshot.profile_sha256 != canonical_profile_sha256()?
        || snapshot.source_repository != profile.z3_overlay.source_repository
        || snapshot.source_commit != profile.z3_overlay.source_commit
        || snapshot.source_tree_sha256 != profile.z3_overlay.tracked_source_tree_sha256
        || snapshot.source_files.len() != profile.z3_overlay.tracked_source_file_count
        || snapshot.z3_executable_sha256 != profile.z3_overlay.reference_executable.sha256
        || !snapshot.source_bytes_authenticated
        || !snapshot.measured_public_metadata_complete
        || snapshot.source_semantics_inventory_complete
        || snapshot.ay_behavior_validated
        || snapshot.blockers.len() != 2
        || snapshot.source_candidates.is_empty()
        || snapshot
            .source_candidates
            .iter()
            .any(|row| row.disposition != "unclassified-source-obligation")
    {
        return Err("current release snapshot has invalid scope, source identity, or unsupported completion claim".to_string());
    }
    if snapshot.declarations.len() != 817
        || snapshot.enum_constants.len() != 370
        || snapshot.catalogs.len() != 4
    {
        return Err(
            "current release snapshot dropped part of its measured public surface".to_string(),
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tree_inventory_is_ordered_and_rejects_links_duplicates_traversal() {
        let blob = "a".repeat(40);
        let tree = parse_tree(&format!(
            "100644 blob {blob} 2\tb\0 100644 blob {blob} 1\ta\0"
        ))
        .unwrap();
        assert_eq!(tree[0].0, "a");
        for text in [
            format!("120000 blob {blob} 1\ta\0"),
            format!("100644 blob {blob} 1\t../a\0"),
            format!("100644 blob {blob} 1\ta\0100644 blob {blob} 1\ta\0"),
        ] {
            assert!(parse_tree(&text).is_err());
        }
    }

    #[test]
    fn parameter_inventory_includes_globals_and_preserves_defaultless_rows() {
        let rows = parameters("Global parameters\n    proof (bool) (default: false)\nTo set a module parameter, use <module-name>.<parameter-name>=value\nExample:  pp.decimal=true\n[module] smt, description: SMT\n    timeout (unsigned int)\n").unwrap();
        assert_eq!(rows.len(), 2);
        assert_eq!(rows["proof"], "(bool) (default: false)");
        assert_eq!(rows["smt.timeout"], "(unsigned int)");
        assert!(parameters("Global parameters\n x (bool)\n x (bool)\n").is_err());
        assert!(parameters("Global parameters\n x (bool)\nforeign line\n").is_err());
    }

    #[test]
    fn source_blob_authentication_detects_equal_length_changes() {
        let directory = tempfile::tempdir().unwrap();
        let file = directory.path().join("x");
        fs::write(&file, b"ab").unwrap();
        let mut hash = sha1::Sha1::new();
        hash.update(b"blob 2\0ab");
        let identity = format!("{:x}", hash.finalize());
        assert_eq!(
            authenticated_source_bytes(&file, &identity, 2).unwrap(),
            b"ab"
        );
        fs::write(&file, b"cd").unwrap();
        assert!(authenticated_source_bytes(&file, &identity, 2).is_err());
    }

    #[test]
    fn public_catalog_does_not_discard_unrecognized_lines() {
        assert_eq!(
            public_catalog("- simplify simplification\n").unwrap().len(),
            1
        );
        assert!(public_catalog("unexpected hidden entry\n- simplify simplification\n").is_err());
        assert!(public_catalog("- simplify simplification").is_err());
        assert!(public_catalog("- simplify a\n- simplify b\n").is_err());
    }
}
