// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native release selection. Archive and executable identities have one owner,
//! `ci/z3.pin`; the library and generated Python shim digests below were measured
//! from those exact authenticated archives. A platform is not a runtime pass.

use super::*;

const PIN: &str = include_str!("../../../../ci/z3.pin");

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Platform {
    MacosArm64,
    MacosX86_64,
    LinuxArm64,
    LinuxX86_64,
}

impl Platform {
    pub(super) const ALL: [Self; 4] = [
        Self::MacosArm64,
        Self::MacosX86_64,
        Self::LinuxArm64,
        Self::LinuxX86_64,
    ];

    pub(super) fn native() -> Result<Self, String> {
        Self::for_host(std::env::consts::OS, std::env::consts::ARCH)
    }

    fn for_host(os: &str, architecture: &str) -> Result<Self, String> {
        match (os, architecture) {
            ("macos", "aarch64") => Ok(Self::MacosArm64),
            ("macos", "x86_64") => Ok(Self::MacosX86_64),
            ("linux", "aarch64") => Ok(Self::LinuxArm64),
            ("linux", "x86_64") => Ok(Self::LinuxX86_64),
            _ => Err(format!(
                "no authenticated Z3 conformance release for {os}/{architecture}"
            )),
        }
    }

    pub(super) fn row(self) -> &'static str {
        match self {
            Self::MacosArm64 => "darwin_arm64",
            Self::MacosX86_64 => "darwin_x86_64",
            Self::LinuxArm64 => "linux_aarch64",
            Self::LinuxX86_64 => "linux_x86_64",
        }
    }

    pub(super) fn architecture(self) -> &'static str {
        match self {
            Self::MacosArm64 | Self::LinuxArm64 => "aarch64",
            Self::MacosX86_64 | Self::LinuxX86_64 => "x86_64",
        }
    }

    pub(super) fn library_name(self) -> &'static str {
        match self {
            Self::MacosArm64 | Self::MacosX86_64 => "libz3.dylib",
            Self::LinuxArm64 | Self::LinuxX86_64 => "libz3.so",
        }
    }

    pub(super) fn python_library_name(self) -> &'static str {
        match self {
            Self::MacosArm64 | Self::MacosX86_64 => "libz3.dylib",
            Self::LinuxArm64 | Self::LinuxX86_64 => "libz3.so.5.3",
        }
    }

    fn library_sha256(self) -> &'static str {
        match self {
            Self::MacosArm64 => "a24ed85970d2ba11f22e3c06dfe91c9d6a2ed51a47a4fee37734a4f5cb1178a0",
            Self::MacosX86_64 => "37bce693f9e1885fca1c1c29eba307c0f1ec7ea807dbfff2237aae7052664df9",
            Self::LinuxArm64 => "6276560e7c749f4d72c7856a9747cc01f21c1f31529caa575356db319e47102a",
            Self::LinuxX86_64 => "4d83373fbbb02f28bc5fe974246113f5940723d16ecb2c449d07d6a4fba92f16",
        }
    }

    pub(super) fn python_core_sha256(self) -> &'static str {
        match self {
            Self::MacosArm64 | Self::MacosX86_64 => {
                "919f8057ccc75d9f46ed77375a46be59c350385711b57cb65fd60ef3d7173d03"
            }
            Self::LinuxArm64 | Self::LinuxX86_64 => {
                "cc7df279fb0bc2e504db1b12bbef250fd6016d749c61d7dd01777bb92432b5cc"
            }
        }
    }

    pub(super) fn release(self) -> Result<Release, String> {
        let values = parse_pin(PIN)?;
        let value = |key: &str| {
            values
                .get(key)
                .copied()
                .ok_or_else(|| format!("ci/z3.pin is missing {key}"))
        };
        if value("Z3_VERSION")? != "5.3.3"
            || value("Z3_RELEASE_URL")?
                != "https://github.com/Z3Prover/z3/releases/download/z3-5.3.3"
        {
            return Err("conformance library identities need remeasurement for this Z3 pin".into());
        }
        let archive = value(&format!("Z3_ASSET_{}", self.row()))?;
        if !archive.starts_with("z3-5.3.3-")
            || !archive.ends_with(".zip")
            || !archive
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'-' | b'_'))
        {
            return Err("invalid conformance release archive name".into());
        }
        let archive_size = value(&format!("Z3_ASSET_SIZE_{}", self.row()))?
            .parse::<u64>()
            .map_err(|_| "invalid conformance archive size")?;
        if archive_size == 0 {
            return Err("empty conformance archive".into());
        }
        let archive_sha256 = value(&format!("Z3_ASSET_SHA256_{}", self.row()))?;
        let executable_sha256 = value(&format!("Z3_BIN_SHA256_{}", self.row()))?;
        for digest in [archive_sha256, executable_sha256, self.library_sha256()] {
            validate_sha256(digest, "native Z3 release identity")?;
        }
        Ok(Release {
            platform: self,
            archive,
            archive_size,
            archive_sha256,
            executable_sha256,
            library_sha256: self.library_sha256(),
        })
    }
}

#[derive(Clone, Copy, Debug)]
pub(super) struct Release {
    pub(super) platform: Platform,
    pub(super) archive: &'static str,
    pub(super) archive_size: u64,
    pub(super) archive_sha256: &'static str,
    pub(super) executable_sha256: &'static str,
    pub(super) library_sha256: &'static str,
}

impl Release {
    pub(super) fn native() -> Result<Self, String> {
        Platform::native()?.release()
    }

    pub(super) fn stem(self) -> &'static str {
        // `release` only constructs this type after checking the suffix.
        self.archive.trim_end_matches(".zip")
    }

    pub(super) fn member(self, filename: &str) -> String {
        format!("{}/bin/{filename}", self.stem())
    }

    pub(super) fn cache_locator(self, filename: &str) -> String {
        format!(
            "cache:ay-z3/{}/{}",
            self.archive_sha256,
            self.member(filename)
        )
    }
}

fn parse_pin(text: &'static str) -> Result<BTreeMap<&'static str, &'static str>, String> {
    let mut values = BTreeMap::new();
    for line in text.lines().map(str::trim) {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let (key, value) = line.split_once('=').ok_or("invalid Z3 pin line")?;
        if key.is_empty() || value.is_empty() || values.insert(key, value).is_some() {
            return Err("empty or duplicate Z3 pin key".into());
        }
    }
    let mut expected = BTreeSet::from([
        "Z3_VERSION".to_string(),
        "Z3_RELEASE_URL".to_string(),
        "Z3_REFERENCE_ROW".to_string(),
        "Z3_ROWS".to_string(),
    ]);
    for platform in Platform::ALL {
        for prefix in [
            "Z3_ASSET_",
            "Z3_ASSET_SIZE_",
            "Z3_ASSET_SHA256_",
            "Z3_BIN_SHA256_",
        ] {
            expected.insert(format!("{prefix}{}", platform.row()));
        }
    }
    if values
        .keys()
        .map(|key| (*key).to_string())
        .collect::<BTreeSet<_>>()
        != expected
    {
        return Err("unknown or missing native Z3 pin keys".into());
    }
    let rows = values["Z3_ROWS"].split(',').collect::<BTreeSet<_>>();
    if rows != Platform::ALL.map(Platform::row).into_iter().collect()
        || values["Z3_ROWS"].split(',').count() != Platform::ALL.len()
        || !rows.contains(values["Z3_REFERENCE_ROW"])
    {
        return Err("native Z3 pin row inventory differs".into());
    }
    Ok(values)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn platform_selection_refuses_unmeasured_hosts() {
        for (os, arch, expected) in [
            ("macos", "aarch64", Platform::MacosArm64),
            ("macos", "x86_64", Platform::MacosX86_64),
            ("linux", "aarch64", Platform::LinuxArm64),
            ("linux", "x86_64", Platform::LinuxX86_64),
        ] {
            assert_eq!(Platform::for_host(os, arch).unwrap(), expected);
        }
        for (os, arch) in [
            ("windows", "x86_64"),
            ("linux", "riscv64"),
            ("freebsd", "aarch64"),
        ] {
            assert!(Platform::for_host(os, arch).is_err());
        }
    }

    #[test]
    fn native_release_identities_share_the_single_pin_owner() {
        for platform in Platform::ALL {
            let release = platform.release().unwrap();
            assert!(release.member("z3").ends_with("/bin/z3"));
            assert!(release
                .cache_locator(platform.library_name())
                .contains(release.archive_sha256));
            assert_ne!(release.executable_sha256, release.library_sha256);
        }
        let darwin = Platform::MacosArm64.release().unwrap();
        assert_eq!(darwin.cache_locator("z3"), "cache:ay-z3/6957e6c75266d7ca8fa77030e86e83d78624567dcdf34cc11f4192fdc6f93c6b/z3-5.3.3-arm64-osx-13.3/bin/z3");
        assert_eq!(Platform::LinuxX86_64.python_library_name(), "libz3.so.5.3");
        assert_ne!(
            Platform::LinuxX86_64.python_core_sha256(),
            Platform::MacosArm64.python_core_sha256()
        );
    }

    #[test]
    fn malformed_pin_never_selects_an_archive() {
        assert!(parse_pin("Z3_VERSION=5.3.3\nZ3_VERSION=5.3.3\n").is_err());
        assert!(parse_pin("Z3_VERSION=5.3.3\nunknown=yes\n").is_err());
    }
}
