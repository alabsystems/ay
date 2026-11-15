// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Current catalog DATA, distinct from historical overlays and implementation
//! capability. Exact pinned reference bytes are captured before any process.
use super::*;
use std::time::Duration;

const LIMITS: ay_sys::metadata_capture::CaptureLimits = ay_sys::metadata_capture::CaptureLimits {
    timeout: Duration::from_secs(5),
    output_bytes: 2 * 1024 * 1024,
    resident_bytes: Some(256 * 1024 * 1024),
};

pub(super) fn bounded(program: &std::ffi::OsStr, args: &[&str]) -> io::Result<Output> {
    let mut command = ProcessCommand::new(program);
    command.args(args);
    ay_sys::metadata_capture::capture(command, LIMITS, "Z3 catalog metadata")
}

#[derive(Clone, Copy)]
pub(super) enum Catalog {
    Parameters,
    Tactics,
}
#[derive(Clone, Copy)]
enum Producer {
    Reference,
    Candidate,
}
impl Catalog {
    fn flag(self) -> &'static str {
        match self {
            Self::Parameters => "-p",
            Self::Tactics => "-tactics",
        }
    }
    fn id(self) -> &'static str {
        match self {
            Self::Parameters => "current_parameter_catalog",
            Self::Tactics => "current_tactic_catalog",
        }
    }
}

fn identifier(text: &str) -> bool {
    !text.is_empty()
        && text
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'.' | b'-'))
}

fn catalog_status(
    expected: &BTreeMap<String, String>,
    actual: &BTreeMap<String, String>,
) -> CheckStatus {
    if expected == actual {
        CheckStatus::Pass
    } else {
        CheckStatus::Fail
    }
}

// Grammar from pinned Z3 util/gparams.cpp and util/params.cpp. Descriptors
// without printed defaults are valid. Unknown body lines are never discarded.
fn entries(kind: Catalog, text: &str) -> Result<BTreeMap<String, String>> {
    if !text.ends_with('\n') {
        anyhow::bail!("catalog ends with an incomplete line");
    }
    let mut found = BTreeMap::new();
    let mut module = "";
    let mut modules = BTreeSet::new();
    let mut global_header = false;
    for raw in text.lines() {
        let line = raw.trim_start().trim_end_matches('\r');
        if line.trim().is_empty() {
            continue;
        }
        let entry = match kind {
            Catalog::Parameters => {
                if line == "Global parameters" {
                    if global_header {
                        anyhow::bail!("duplicate global parameter header");
                    }
                    global_header = true;
                    continue;
                }
                if !global_header {
                    anyhow::bail!("missing global parameter header");
                }
                if matches!(
                    line,
                    "To set a module parameter, use <module-name>.<parameter-name>=value"
                        | "Example:  pp.decimal=true"
                ) {
                    if !module.is_empty() {
                        anyhow::bail!("global advice inside a module table");
                    }
                    continue;
                }
                if let Some(rest) = line.strip_prefix("[module] ") {
                    let name = rest
                        .split_once(", description: ")
                        .map_or(rest, |(name, _)| name);
                    if !identifier(name) || !modules.insert(name) {
                        anyhow::bail!("malformed or duplicate parameter module");
                    }
                    module = name;
                    continue;
                }
                let (name, descriptor) = line
                    .split_once(" (")
                    .ok_or_else(|| anyhow::anyhow!("unrecognized parameter body line"))?;
                let (kind, suffix) = descriptor
                    .split_once(')')
                    .ok_or_else(|| anyhow::anyhow!("truncated parameter kind"))?;
                if !identifier(name)
                    || !matches!(
                        kind,
                        "unsigned int"
                            | "bool"
                            | "double"
                            | "rational"
                            | "string"
                            | "optional-value"
                            | "keyword"
                            | "symbol"
                            | "symbol-list"
                            | "sort"
                            | "sort-list"
                            | "expression"
                            | "expression-list"
                            | "declaration"
                            | "declaration-list"
                            | "sorted-variable"
                            | "sorted-variable-list"
                            | "s-expression"
                            | "unknown"
                    )
                {
                    anyhow::bail!("unrecognized parameter descriptor");
                }
                if !suffix.is_empty()
                    && !(suffix.starts_with(" (default: ") && suffix.ends_with(')'))
                {
                    anyhow::bail!("truncated or unknown parameter descriptor suffix");
                }
                (
                    if module.is_empty() {
                        name.to_owned()
                    } else {
                        format!("{module}.{name}")
                    },
                    format!("({descriptor}"),
                )
            }
            Catalog::Tactics => {
                let rest = line
                    .strip_prefix("- ")
                    .ok_or_else(|| anyhow::anyhow!("unrecognized tactic body line"))?;
                let (name, description) = rest
                    .split_once(' ')
                    .ok_or_else(|| anyhow::anyhow!("truncated tactic descriptor"))?;
                if !identifier(name) {
                    anyhow::bail!("malformed tactic name");
                }
                (name.to_owned(), description.to_owned())
            }
        };
        if found.insert(entry.0, entry.1).is_some() {
            anyhow::bail!("duplicate catalog entry");
        }
    }
    if found.is_empty() {
        anyhow::bail!("catalog has no recognized entries");
    }
    Ok(found)
}

fn observe(
    program: &Path,
    kind: Catalog,
    producer: Producer,
) -> Result<(Output, BTreeMap<String, String>)> {
    let mut args = match producer {
        Producer::Reference => vec!["-T:5", "-memory:256", kind.flag()],
        Producer::Candidate => vec![kind.flag()],
    };
    if matches!(kind, Catalog::Tactics) {
        args.push("-in");
    }
    let output = bounded(program.as_os_str(), &args)?;
    if !output.status.success() || !output.stderr.is_empty() {
        anyhow::bail!(
            "catalog query failed: status={:?} stderr={}",
            output.status.code(),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let parsed = entries(
        kind,
        std::str::from_utf8(&output.stdout).context("catalog is not UTF-8")?,
    )?;
    Ok((output, parsed))
}

/// CLI discovery checks syntax and successful bounded execution. Catalog size
/// belongs to the pinned-reference comparison, not an archived line count.
pub(super) fn discovery(ay: &Path, kind: Catalog) -> AuditCheck {
    let id = match kind {
        Catalog::Parameters => "z3_param_discovery_smoke",
        Catalog::Tactics => "z3_tactic_catalog_smoke",
    };
    let command = format!(
        "{} {}{}",
        ay.display(),
        kind.flag(),
        if matches!(kind, Catalog::Tactics) {
            " -in"
        } else {
            ""
        }
    );
    match observe(ay, kind, Producer::Candidate) {
        Ok((_, parsed)) => AuditCheck::pass(
            id,
            format!(
                "bounded {} discovery returned {} complete parsed entries; metadata syntax only, not pinned-reference equality or implementation coverage",
                kind.flag(), parsed.len()
            ),
        ),
        Err(error) => AuditCheck::fail(id, format!("bounded catalog discovery refused: {error:#}")),
    }
    .with_command(command)
}

pub(super) fn measure(root: &Path, ay: &Path, z3: &str) -> Vec<AuditCheck> {
    let snapshot = match reference::Snapshot::capture(root, z3) {
        Ok(snapshot) => snapshot,
        Err(error) => {
            let unavailable = error
                .chain()
                .filter_map(|cause| cause.downcast_ref::<io::Error>())
                .any(|cause| cause.kind() == io::ErrorKind::NotFound);
            return vec![AuditCheck::fail(
                "current_reference_catalog",
                format!("current pinned catalog source unavailable/refused: {error}"),
            )
            .with_status(if unavailable {
                CheckStatus::Missing
            } else {
                CheckStatus::FailError
            })];
        }
    };
    // Observe a private image, not a pathname another build can replace between
    // its metadata hash and execution. This is observed AY DATA, not a signed
    // package/source/SDK grant.
    let image = match tempfile::tempdir().and_then(|directory| {
        let path = directory.path().join("ay-catalog");
        let source = fs::canonicalize(ay)?;
        let mut options = fs::OpenOptions::new();
        options.read(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt as _;
            options.custom_flags(nix::libc::O_NOFOLLOW | nix::libc::O_NONBLOCK);
        }
        let mut input = options.open(source)?;
        let metadata = input.metadata()?;
        if !metadata.is_file() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "selected AY image is not a regular file",
            ));
        }
        let mut output = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)?;
        let deadline = std::time::Instant::now() + LIMITS.timeout;
        let mut remaining = metadata.len();
        let mut chunk = [0u8; 64 * 1024];
        while remaining != 0 {
            if std::time::Instant::now() >= deadline {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "AY image preparation deadline exceeded",
                ));
            }
            let limit =
                usize::try_from(remaining.min(chunk.len() as u64)).map_err(io::Error::other)?;
            let count = input.read(&mut chunk[..limit])?;
            if count == 0 {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "AY image changed during capture",
                ));
            }
            output.write_all(&chunk[..count])?;
            remaining -= count as u64;
        }
        if input.read(&mut chunk[..1])? != 0 {
            return Err(io::Error::other("AY image grew during capture"));
        }
        output.sync_all()?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            fs::set_permissions(&path, fs::Permissions::from_mode(0o500))?;
        }
        Ok((directory, path))
    }) {
        Ok(image) => image,
        Err(error) => {
            return vec![AuditCheck::fail(
                "current_reference_catalog",
                format!("cannot capture selected AY catalog image: {error}"),
            )
            .with_status(CheckStatus::FailError)]
        }
    };
    let ay_hash = match sha256_file(&image.1) {
        Ok(hash) => hash,
        Err(error) => {
            return vec![
                AuditCheck::fail("current_reference_catalog", error.to_string())
                    .with_status(CheckStatus::FailError),
            ]
        }
    };
    [Catalog::Parameters,Catalog::Tactics].into_iter().map(|kind| {
        match (observe(snapshot.path(),kind,Producer::Reference),observe(&image.1,kind,Producer::Candidate)) {
            (Ok((reference,expected)),Ok((candidate,actual)))=> {
                let missing=expected.keys().filter(|name|!actual.contains_key(*name)).collect::<Vec<_>>();
                let extra=actual.keys().filter(|name|!expected.contains_key(*name)).collect::<Vec<_>>();
                let changed=expected.iter().filter(|(name,value)|actual.get(*name).is_some_and(|v|v!=*value)).map(|(name,_)|name).collect::<Vec<_>>();
                let same=reference.stdout==candidate.stdout;
                let finding=format!("current Z3 {} {} metadata: reference_entries={} ay_entries={} missing={} extra={} changed={} text_equal={same}; metadata only, not tactic/parameter implementation coverage",snapshot.identity.version(),kind.flag(),expected.len(),actual.len(),missing.len(),extra.len(),changed.len());
                AuditCheck::fail(kind.id(),finding).with_status(catalog_status(&expected, &actual))
                    .with_details(json!({"reference":&snapshot.identity,"ay_executable_sha256":&ay_hash,"reference_entries":expected.len(),"ay_entries":actual.len(),"missing_in_ay":missing,"extra_in_ay":extra,"changed_entries":changed,"text_equal":same,"reference_stdout_sha256":sha256_hex(&reference.stdout),"ay_stdout_sha256":sha256_hex(&candidate.stdout),"timeout_ms":LIMITS.timeout.as_millis(),"output_bytes":LIMITS.output_bytes,"sampled_group_rss_bytes":LIMITS.resident_bytes}))
            }
            (reference,candidate)=> {
                let errors=[reference.err(),candidate.err()].into_iter().flatten().collect::<Vec<_>>();
                let unsupported=errors.iter().any(|error|error.chain().filter_map(|cause|cause.downcast_ref::<io::Error>()).any(|cause|cause.kind()==io::ErrorKind::Unsupported));
                let timed_out=errors.iter().any(|error|error.chain().filter_map(|cause|cause.downcast_ref::<io::Error>()).any(|cause|cause.kind()==io::ErrorKind::TimedOut));
                AuditCheck::fail(kind.id(),format!("bounded catalog measurement unavailable: {}",errors.iter().map(ToString::to_string).collect::<Vec<_>>().join("; "))).with_status(if unsupported { CheckStatus::NotRun } else if timed_out { CheckStatus::FailTimeout } else { CheckStatus::FailError })
            }
        }
    }).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn catalog_comparison_preserves_entries_and_descriptors_without_freezing_print_order() {
        let expected = entries(
            Catalog::Tactics,
            "- smt SMT solver\n- ff-simplify simplify fields\n",
        )
        .unwrap();
        let reordered = entries(
            Catalog::Tactics,
            "- ff-simplify simplify fields\n- smt SMT solver\n",
        )
        .unwrap();
        assert_eq!(catalog_status(&expected, &reordered), CheckStatus::Pass);
        let missing = entries(Catalog::Tactics, "- smt SMT solver\n").unwrap();
        assert_eq!(catalog_status(&expected, &missing), CheckStatus::Fail);
        let changed = entries(
            Catalog::Tactics,
            "- ff-simplify different semantics\n- smt SMT solver\n",
        )
        .unwrap();
        assert_eq!(catalog_status(&expected, &changed), CheckStatus::Fail);
    }

    #[test]
    fn catalog_keys_retain_parameter_modules_and_reject_duplicate_or_empty_data() {
        let parsed=entries(Catalog::Parameters,"Global parameters\n timeout (unsigned int) (default: 0)\n[module] smt, description: solver\n timeout (unsigned int) (default: 1)\n").unwrap();
        assert_eq!(parsed.len(), 2);
        assert_ne!(parsed.get("timeout"), parsed.get("smt.timeout"));
        assert!(entries(
            Catalog::Tactics,
            "- simplify simplify formulas\n- simplify repeated\n"
        )
        .is_err());
        assert!(entries(Catalog::Parameters, "not a catalog").is_err());
    }

    #[test]
    fn malformed_catalog_body_cannot_masquerade_as_a_smaller_complete_table() {
        let prefix = "Global parameters\n    timeout (unsigned int) (default: 0)\n";
        for broken in [
            "unknown body\n",
            "    dropped_parameter (bool\n",
            "    hidden (bool) unexplained suffix\n",
            "[module] smt, unknown header\n",
        ] {
            assert!(entries(Catalog::Parameters, &format!("{prefix}{broken}")).is_err());
        }
        let complete=format!("{prefix}[module] smt\n    no_default (symbol)\n    cost (string) (default: (+ weight generation))\n");
        let parsed = entries(Catalog::Parameters, &complete).unwrap();
        assert!(parsed.contains_key("smt.no_default"));
        assert!(parsed.contains_key("smt.cost"));
        assert!(entries(Catalog::Parameters, complete.trim_end()).is_err());
        assert!(entries(Catalog::Tactics, "- smt SMT solver\nunknown body\n").is_err());
    }

    #[test]
    fn current_pinned_catalog_queries_are_bounded_and_record_actual_metadata() {
        let Some(program) = ay_test_support::z3::optional_z3("current Z3 catalogs") else {
            return;
        };
        let root = resolve_repo_root(None).unwrap();
        let snapshot =
            reference::Snapshot::capture(&root, program.path().to_str().unwrap()).unwrap();
        for kind in [Catalog::Parameters, Catalog::Tactics] {
            let (output, entries) = observe(snapshot.path(), kind, Producer::Reference).unwrap();
            let expected_key = match kind {
                Catalog::Parameters => "timeout",
                Catalog::Tactics => "smt",
            };
            assert!(entries.contains_key(expected_key));
            eprintln!(
                "CURRENT_REFERENCE_CATALOG {}",
                json!({"reference":&snapshot.identity,"query":kind.flag(),"recognized_entries":entries.len(),"stdout_sha256":sha256_hex(&output.stdout),"timeout_ms":LIMITS.timeout.as_millis(),"sampled_rss_bytes":LIMITS.resident_bytes,"output_bytes":LIMITS.output_bytes})
            );
        }
    }
}
