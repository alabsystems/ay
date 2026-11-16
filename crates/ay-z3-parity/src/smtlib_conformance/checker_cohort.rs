// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact executable cohorts for the same upstream Carcara source revision.
//!
//! The packaged cohort changes the compiler and build metadata, not the checker
//! policy. Callers still apply the pinned-Carcara semantic guard, strict replay,
//! and the positive and negative controls. A source match or version banner on
//! its own never admits an executable. These are explicit byte identities.

use super::*;
use std::ffi::OsString;

pub(super) const LEGACY_SHA256: &str =
    "edd0457d7eb71132ac505297ad493c3b0b3a52e9938108d9b365157277bd2bdf";
pub(super) const PACKAGED_SHA256: &str =
    "e27cb05e4119ac8ece1b3ba70cab2b7aae710fae70ad2252d0086be8d3b363a9";
const PACKAGED_X86_64_SHA256: &str =
    "db27f7fe19c26ee14e53981e333b159dd216a757972ff4fc24d6c8c01703a532";
pub(super) const SOURCE_REVISION: &str = "9a352eea6c935ad35cb8ec22e521a7620ec5d474";
const SOURCE_TREE: &str = "80e8ca1f905ccd843ab784f6f9669d995010a505";
const SOURCE_KIT_SHA256: &str = "eb69f57363031e8ba97e1936807434a0be31f9679685b53948f61afd315621a6";
const SOURCE_LOCK_SHA256: &str = "55f48e70a8c943437b0d56cc4848ce4e86dfe6194a3c9f7a5f052c0c0788b6a4";
const COMPILER_SHA256: &str = "c8c019cab02c90d11961e41e1cace4ef5dcf9181babfb0866c6517fd038c6897";
const TREE_ROOT: &str = "353d1910a83c8faa89ba8a03326217ff59fd49f21440544d54128bd57e55c6c5";
const RELEASE_URL: &str = "https://github.com/alabsystems/aterm/releases/download/atpkg-carcara-1";
const ARCHIVE: &str = "carcara-1.tar.zst";
const ARCHIVE_SIZE: u64 = 56_116_865;
const ARCHIVE_SHA256: &str = "b2a7d7b54cb18828c95c00c2171867a46a8db82e9733b20592c8d49e87f59547";
const EXECUTABLE_SIZE: u64 = 4_658_712;
const QUALIFICATION: &str = "carcara-1.tar.zst.qualification.json";
const QUALIFICATION_SHA256: &str =
    "911a0bbfb58c8f2203d6b15dc8b735bf32503213f7bcf51561700432ac0845d3";
const MANIFEST: &str = "pkg-carcara-1.toml";
const MANIFEST_SHA256: &str = "3c8a4e7003ec1bbd0b2704a88018354b4c21d64be05526300c1275904bf8a312";
const SIGNATURE_SHA256: &str = "7f8a722c26c7a7e4e856fa54e8e1c44be58aa0e632fdcb2b056d747aabfec10c";

#[derive(Clone, Copy, Debug)]
struct PackageCohort {
    target: &'static str,
    platform_label: &'static str,
    id: &'static str,
    archive: &'static str,
    archive_size: u64,
    archive_sha256: &'static str,
    executable_size: u64,
    executable_sha256: &'static str,
    tree_root: &'static str,
    qualification: &'static str,
    qualification_size: u64,
    qualification_sha256: &'static str,
    qualified_manifest_sha256: &'static str,
    compiler_sha256: &'static str,
    compiler_revision: &'static str,
    compiler_build: u64,
}

const MACOS_ARM64: PackageCohort = PackageCohort {
    target: "aarch64-apple-darwin",
    platform_label: "macos-aarch64",
    id: "carcara-1.1.0-9a352ee-atpkg-1-macos-arm64",
    archive: ARCHIVE,
    archive_size: ARCHIVE_SIZE,
    archive_sha256: ARCHIVE_SHA256,
    executable_size: EXECUTABLE_SIZE,
    executable_sha256: PACKAGED_SHA256,
    tree_root: TREE_ROOT,
    qualification: QUALIFICATION,
    qualification_size: 2_079,
    qualification_sha256: QUALIFICATION_SHA256,
    qualified_manifest_sha256: "c909da17a2f1e719a0c6db478ba1743a031ec33cb2e0156687fe8d9c2cabb301",
    compiler_sha256: COMPILER_SHA256,
    compiler_revision: "29ebb403de7a102850d6cb10a62d5cc3baf723ed",
    compiler_build: 16387,
};

const MACOS_X86_64: PackageCohort = PackageCohort {
    target: "x86_64-apple-darwin",
    platform_label: "macos-x86_64",
    id: "carcara-1.1.0-9a352ee-atpkg-1-macos-x86_64",
    archive: "carcara-1-x86_64-apple-darwin.tar.zst",
    archive_size: 56_358_978,
    archive_sha256: "0348280840e1668514d8c46ddbbb2b3e16362e8b50c1153b25d1e337fef46eee",
    executable_size: 6_081_424,
    executable_sha256: PACKAGED_X86_64_SHA256,
    tree_root: "bf089d0b2f3415c260928eadaeef49fc2129f20ff6482597594a725ea231fb88",
    qualification: "carcara-1-x86_64-apple-darwin.tar.zst.qualification.json",
    qualification_size: 2_514,
    qualification_sha256: "aebef50209dacc22726d48cc8c2e55ed01d2a632b58511e8fe3f5ff239f3ddfc",
    qualified_manifest_sha256: MANIFEST_SHA256,
    compiler_sha256: "cbb2ecb561be3c70df9c4448a4b1827bcfb8456b6ef06f9147b335a27be39bce",
    compiler_revision: "3d7768caf6dcba0e4f5083a854bb77805ea1aafd",
    compiler_build: 6808,
};

fn package_for_platform(platform: reference_platform::Platform) -> Option<&'static PackageCohort> {
    match platform {
        reference_platform::Platform::MacosArm64 => Some(&MACOS_ARM64),
        reference_platform::Platform::MacosX86_64 => Some(&MACOS_X86_64),
        reference_platform::Platform::LinuxArm64 | reference_platform::Platform::LinuxX86_64 => {
            None
        }
    }
}

#[derive(Debug, Serialize)]
pub(super) struct Identity {
    pub(super) path: PathBuf,
    pub(super) sha256: String,
    pub(super) expected_version: &'static str,
    pub(super) cohort_id: &'static str,
    pub(super) source_revision: &'static str,
}

/// Expected exact stdout line, without its terminating newline. This metadata
/// lookup does not grant native authority: `authenticate` also checks the host
/// platform before an executable can run.
pub(super) fn version_for_sha(sha256: &str) -> Option<&'static str> {
    match sha256 {
        LEGACY_SHA256 => Some("carcara 1.1.0 [git master 9a352ee]"),
        PACKAGED_SHA256 | PACKAGED_X86_64_SHA256 => Some("carcara 1.1.0 [git none 9a352ee]"),
        _ => None,
    }
}

fn version_for_platform(
    platform: reference_platform::Platform,
    sha256: &str,
) -> Option<&'static str> {
    if platform == reference_platform::Platform::MacosArm64 && sha256 == LEGACY_SHA256 {
        return Some("carcara 1.1.0 [git master 9a352ee]");
    }
    package_for_platform(platform)
        .filter(|cohort| cohort.executable_sha256 == sha256)
        .map(|_| "carcara 1.1.0 [git none 9a352ee]")
}

/// Authenticate bytes only; the execution owner separately runs and compares
/// the exact cohort-specific version line under its ordinary process limits.
pub(super) fn authenticate(path: &Path) -> Result<Identity, String> {
    let platform = reference_platform::Platform::native()?;
    let metadata = fs::symlink_metadata(path)
        .map_err(|error| format!("inspect Carcara {}: {error}", path.display()))?;
    if !metadata.file_type().is_file() || metadata.file_type().is_symlink() {
        return Err("Carcara must be a regular non-symlink executable".to_string());
    }
    let sha256 = sha256_file(path, "Carcara executable")?;
    let expected_version = version_for_platform(platform, &sha256)
        .ok_or_else(|| format!("unqualified Carcara executable SHA-256: {sha256}"))?;
    let package =
        package_for_platform(platform).filter(|cohort| cohort.executable_sha256 == sha256);
    if package.is_some_and(|cohort| metadata.len() != cohort.executable_size) {
        return Err("packaged Carcara executable size mismatch".to_string());
    }
    Ok(Identity {
        path: fs::canonicalize(path).map_err(|error| error.to_string())?,
        cohort_id: if sha256 == LEGACY_SHA256 {
            "carcara-1.1.0-9a352ee-original"
        } else {
            package
                .ok_or("Carcara package is not native to this platform")?
                .id
        },
        sha256,
        expected_version,
        source_revision: SOURCE_REVISION,
    })
}

/// Download the immutable native macOS package, retaining exact release metadata
/// and source/compiler provenance. Checked-in digests are this reader's trust
/// anchor; retaining the publisher's signature is not a claim that this reader
/// independently verified the package-signing chain.
pub(super) fn provision(directory: &Path) -> Result<PathBuf, String> {
    let platform = reference_platform::Platform::native()?;
    let cohort = package_for_platform(platform).ok_or_else(|| format!(
        "no downloadable qualified Carcara cohort for {}; macOS arm64 and x86_64 are available, Linux pinned-source artifacts remain unavailable", platform.row()
    ))?;
    fs::create_dir_all(directory).map_err(|error| error.to_string())?;
    let directory = fs::canonicalize(directory).map_err(|error| error.to_string())?;
    let resources = PlannedResources::plan(&locate_repo_root()?, 1, "pinned Carcara acquisition")
        .map_err(|error| error.to_string())?;
    for (name, size, digest) in [
        (
            cohort.qualification,
            cohort.qualification_size,
            cohort.qualification_sha256,
        ),
        (MANIFEST, 942, MANIFEST_SHA256),
        ("pkg-carcara-1.toml.sig", 64, SIGNATURE_SHA256),
        (cohort.archive, cohort.archive_size, cohort.archive_sha256),
    ] {
        download(&resources, &directory.join(name), name, size, digest)?;
    }
    let qualification = read_bounded_bytes(
        &directory.join(cohort.qualification),
        cohort.qualification_size,
        "Carcara qualification",
        true,
    )?;
    validate_qualification(&qualification, cohort)?;
    let executable = directory.join(format!("carcara-{}", &cohort.executable_sha256[..16]));
    if executable.exists() {
        let identity = authenticate(&executable)?;
        if identity.sha256 != cohort.executable_sha256 {
            return Err("download destination contains a different Carcara cohort".to_string());
        }
    } else {
        let bytes = extract_executable(&directory.join(cohort.archive), cohort)?;
        let temporary =
            tempfile::NamedTempFile::new_in(&directory).map_err(|error| error.to_string())?;
        fs::write(temporary.path(), &bytes).map_err(|error| error.to_string())?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            fs::set_permissions(temporary.path(), fs::Permissions::from_mode(0o500))
                .map_err(|error| error.to_string())?;
        }
        authenticate(temporary.path())?;
        temporary
            .persist_noclobber(&executable)
            .map_err(|error| error.to_string())?;
    }
    let identity = authenticate(&executable)?;
    let evidence = json!({
        "schema":"ay-carcara-cohort-provision/v1",
        "identity":identity,
        "source_repository":"https://github.com/ufmg-smite/carcara",
        "source_revision":SOURCE_REVISION,
        "source_tree":SOURCE_TREE,
        "source_lock_sha256":SOURCE_LOCK_SHA256,
        "source_kit_sha256":SOURCE_KIT_SHA256,
        "compiler_query_sha256":cohort.compiler_sha256,
        "compiler_revision":cohort.compiler_revision,
        "compiler_build":cohort.compiler_build,
        "compiler_lane":"unverified",
        "compiler_proof_claim":false,
        "archive":{"url":format!("{RELEASE_URL}/{}", cohort.archive),"size":cohort.archive_size,"sha256":cohort.archive_sha256,"member":"bin/carcara"},
        "package_tree_root":cohort.tree_root,
        "manifest_sha256":MANIFEST_SHA256,
        "qualification_sha256":cohort.qualification_sha256,
        "signature_sha256":SIGNATURE_SHA256,
        "metadata_authentication":"exact checked-in SHA-256 identities; publisher signature retained; signature-chain verification not claimed by this reader",
        "semantic_acceptance":"requires exact version pairing, pinned-Carcara guard, strict proof replay, and positive/negative controls; provisioning alone grants no verdict authority"
    });
    let evidence = pretty_json(&evidence)?;
    let evidence_path = directory.join("carcara-cohort.json");
    if evidence_path.exists() {
        if read_bounded_bytes(&evidence_path, 64 * 1024, "Carcara cohort record", true)? != evidence
        {
            return Err(
                "existing Carcara cohort record differs from authenticated inputs".to_string(),
            );
        }
    } else {
        atomic_write_new(&evidence_path, &evidence)?;
    }
    Ok(executable)
}

fn validate_qualification(bytes: &[u8], cohort: &PackageCohort) -> Result<(), String> {
    if bytes.len() as u64 != cohort.qualification_size
        || sha256_bytes(bytes) != cohort.qualification_sha256
    {
        return Err("Carcara qualification digest or size mismatch".to_string());
    }
    let value: Value = serde_json::from_slice(bytes).map_err(|error| error.to_string())?;
    let source = &value["source_cohort"];
    let qualified_manifest = value["qualified_manifest"]
        .as_str()
        .ok_or("Carcara qualification lacks its manifest")?;
    if value["status"] != "native-pass"
        || value["target"] != cohort.target
        || value["native_host"] != cohort.target
        || value["native_translation"] != "native"
        || value["control_count"] != 7
        || value["controls"]
            != json!([
                "exact-version",
                "honest",
                "false-resolution",
                "wrong-problem",
                "truncated",
                "invalid-utf8",
                "missing"
            ])
        || value["archive"] != cohort.archive
        || value["archive_sha256"] != cohort.archive_sha256
        || value["archive_size"] != cohort.archive_size
        || value["tree_root"] != cohort.tree_root
        || value["manifest_sha256"] != cohort.qualified_manifest_sha256
        || sha256_bytes(qualified_manifest.as_bytes()) != cohort.qualified_manifest_sha256
        || source["artifact"]["sha256"] != cohort.executable_sha256
        || source["artifact"]["platform"] != cohort.platform_label
        || source["source"]["revision"] != SOURCE_REVISION
        || source["source"]["tree"] != SOURCE_TREE
        || source["source"]["cargo_lock_sha256"] != SOURCE_LOCK_SHA256
        || source["source_kit_sha256"] != SOURCE_KIT_SHA256
        || source["build"]["compiler_query_sha256"] != cohort.compiler_sha256
        || source["build"]["compiler_revision"] != cohort.compiler_revision
        || source["build"]["trust_build"] != cohort.compiler_build
        || source["build"]["lane"] != "unverified"
        || source["build"]["locked"] != true
        || source["build"]["offline"] != true
    {
        return Err(
            "Carcara qualification platform/source/compiler/archive binding mismatch".to_string(),
        );
    }
    Ok(())
}

fn download(
    resources: &PlannedResources,
    destination: &Path,
    name: &str,
    size: u64,
    digest: &str,
) -> Result<(), String> {
    if destination.exists() {
        return verify_file(destination, size, digest);
    }
    let parent = destination.parent().ok_or("download has no parent")?;
    let temporary = tempfile::NamedTempFile::new_in(parent).map_err(|error| error.to_string())?;
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
        size.to_string().into(),
        "--output".into(),
        temporary.path().as_os_str().to_owned(),
        format!("{RELEASE_URL}/{name}").into(),
    ];
    let output = resources
        .run_external_transcript(
            "curl",
            args,
            b"",
            Duration::from_secs(600),
            "download pinned Carcara artifact",
        )
        .map_err(|error| error.to_string())?;
    if output.timed_out
        || output.memout
        || output.stdout_truncated
        || output.stderr_truncated
        || !output.status.is_some_and(|status| status.success())
    {
        return Err(format!(
            "Carcara download failed: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    verify_file(temporary.path(), size, digest)?;
    temporary
        .persist_noclobber(destination)
        .map_err(|error| error.to_string())?;
    Ok(())
}

fn verify_file(path: &Path, size: u64, digest: &str) -> Result<(), String> {
    let metadata = fs::symlink_metadata(path).map_err(|error| error.to_string())?;
    if !metadata.file_type().is_file()
        || metadata.file_type().is_symlink()
        || metadata.len() != size
    {
        return Err(format!(
            "Carcara artifact size/type mismatch: {}",
            path.display()
        ));
    }
    if sha256_file(path, "Carcara artifact")? != digest {
        return Err(format!(
            "Carcara artifact digest mismatch: {}",
            path.display()
        ));
    }
    Ok(())
}

fn extract_executable(path: &Path, cohort: &PackageCohort) -> Result<Vec<u8>, String> {
    verify_file(path, cohort.archive_size, cohort.archive_sha256)?;
    let file = fs::File::open(path).map_err(|error| error.to_string())?;
    let decoder = zstd::stream::read::Decoder::new(file).map_err(|error| error.to_string())?;
    // The complete immutable archive expands to about 60 MB. Never materialize
    // its source kit, paths, links, or permission bits on the destination tree.
    let mut archive = tar::Archive::new(decoder.take(64 * 1024 * 1024));
    let mut executable = None;
    for entry in archive.entries().map_err(|error| error.to_string())? {
        let mut entry = entry.map_err(|error| error.to_string())?;
        if entry.path().map_err(|error| error.to_string())?.as_ref() != Path::new("bin/carcara") {
            continue;
        }
        if executable.is_some()
            || !entry.header().entry_type().is_file()
            || entry.size() != cohort.executable_size
        {
            return Err(
                "Carcara archive executable is duplicated or has wrong size/type".to_string(),
            );
        }
        let mut bytes = Vec::with_capacity(cohort.executable_size as usize);
        entry
            .by_ref()
            .take(cohort.executable_size + 1)
            .read_to_end(&mut bytes)
            .map_err(|error| error.to_string())?;
        if bytes.len() as u64 != cohort.executable_size
            || sha256_bytes(&bytes) != cohort.executable_sha256
        {
            return Err("Carcara archive executable digest mismatch".to_string());
        }
        executable = Some(bytes);
    }
    executable.ok_or_else(|| "Carcara archive is missing bin/carcara".to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_bytes_select_one_exact_banner() {
        assert_eq!(
            version_for_platform(reference_platform::Platform::MacosArm64, LEGACY_SHA256),
            Some("carcara 1.1.0 [git master 9a352ee]")
        );
        assert_eq!(
            version_for_platform(reference_platform::Platform::MacosArm64, PACKAGED_SHA256),
            Some("carcara 1.1.0 [git none 9a352ee]")
        );
        assert_eq!(
            version_for_platform(
                reference_platform::Platform::MacosX86_64,
                PACKAGED_X86_64_SHA256
            ),
            Some("carcara 1.1.0 [git none 9a352ee]")
        );
        assert_eq!(version_for_sha(&"0".repeat(64)), None);
    }

    #[test]
    fn foreign_machine_cohorts_and_old_linux_release_never_gain_authority() {
        use reference_platform::Platform;
        for platform in Platform::ALL {
            assert_eq!(
                version_for_platform(platform, LEGACY_SHA256).is_some(),
                platform == Platform::MacosArm64
            );
            assert_eq!(
                version_for_platform(platform, PACKAGED_SHA256).is_some(),
                platform == Platform::MacosArm64
            );
            assert_eq!(
                version_for_platform(platform, PACKAGED_X86_64_SHA256).is_some(),
                platform == Platform::MacosX86_64
            );
        }
        assert!(package_for_platform(Platform::LinuxArm64).is_none());
        assert!(package_for_platform(Platform::LinuxX86_64).is_none());
    }

    #[test]
    fn platform_qualification_binds_exact_native_controls_and_source_tuple() {
        let arm = include_bytes!("../../data/carcara-1/macos-arm64.qualification.json");
        let x86 = include_bytes!("../../data/carcara-1/macos-x86_64.qualification.json");
        validate_qualification(arm, &MACOS_ARM64).unwrap();
        validate_qualification(x86, &MACOS_X86_64).unwrap();
        assert!(validate_qualification(arm, &MACOS_X86_64).is_err());
        assert!(validate_qualification(x86, &MACOS_ARM64).is_err());
        let mut changed = x86.to_vec();
        changed[0] = b'[';
        assert!(validate_qualification(&changed, &MACOS_X86_64).is_err());
    }

    #[test]
    fn matching_banner_without_admitted_bytes_is_refused() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("carcara");
        fs::write(&path, b"carcara 1.1.0 [git none 9a352ee]\n").unwrap();
        assert!(authenticate(&path).is_err());
    }

    #[test]
    fn altered_metadata_or_cached_bytes_are_refused() {
        assert!(validate_qualification(b"{\"status\":\"native-pass\"}", &MACOS_ARM64).is_err());
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("artifact");
        fs::write(&path, b"x").unwrap();
        assert!(verify_file(&path, 2, &sha256_bytes(b"x")).is_err());
        assert!(verify_file(&path, 1, &sha256_bytes(b"y")).is_err());
    }
}
