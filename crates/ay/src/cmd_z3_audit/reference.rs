// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Current reference bytes, distinct from historical compatibility evidence.

use super::*;
use serde::Serialize;

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub(super) struct Identity {
    version: String,
    row: String,
    pin_sha256: String,
    executable_sha256: String,
}

impl Identity {
    pub(super) fn version(&self) -> &str {
        &self.version
    }
}

fn banner_matches(banner: &str, version: &str) -> bool {
    let expected = ay_sys::z3_oracle::parse_banner_version(&format!("Z3 version {version}"));
    expected.is_some() && ay_sys::z3_oracle::parse_banner_version(banner) == expected
}

pub(crate) struct Pin {
    values: BTreeMap<String, String>,
    digest: String,
}

impl Pin {
    pub(super) fn version(&self) -> &str {
        &self.values["Z3_VERSION"]
    }
    pub(crate) fn load(root: &Path) -> Result<Self> {
        Self::parse(&fs::read_to_string(root.join("ci/z3.pin"))?)
    }

    fn parse(text: &str) -> Result<Self> {
        let mut values = BTreeMap::new();
        for line in text.lines().map(str::trim) {
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let (key, value) = line.split_once('=').context("malformed Z3 pin entry")?;
            if key.is_empty()
                || value.is_empty()
                || line.chars().any(char::is_whitespace)
                || values.insert(key.to_owned(), value.to_owned()).is_some()
            {
                anyhow::bail!("malformed or duplicate Z3 pin entry: {key}");
            }
        }
        let pin = Self {
            values,
            digest: sha256_hex(text.as_bytes()),
        };
        let version = pin.value("Z3_VERSION")?;
        if version.split('.').count() != 3
            || !version
                .split('.')
                .all(|part| !part.is_empty() && part.bytes().all(|b| b.is_ascii_digit()))
            || pin.value("Z3_RELEASE_URL")?
                != format!("https://github.com/Z3Prover/z3/releases/download/z3-{version}")
        {
            anyhow::bail!("invalid Z3 release identity in ci/z3.pin");
        }
        let rows = pin.value("Z3_ROWS")?.split(',').collect::<BTreeSet<_>>();
        if rows.len() != pin.value("Z3_ROWS")?.split(',').count()
            || !rows.contains(pin.value("Z3_REFERENCE_ROW")?)
            || rows
                != BTreeSet::from([
                    "darwin_arm64",
                    "darwin_x86_64",
                    "linux_x86_64",
                    "linux_aarch64",
                ])
        {
            anyhow::bail!("invalid Z3 pin rows");
        }
        let mut keys = [
            "Z3_VERSION",
            "Z3_RELEASE_URL",
            "Z3_REFERENCE_ROW",
            "Z3_ROWS",
        ]
        .into_iter()
        .map(str::to_owned)
        .collect::<BTreeSet<_>>();
        for row in rows {
            if row.is_empty() || !row.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_') {
                anyhow::bail!("invalid Z3 pin row");
            }
            for prefix in [
                "Z3_ASSET_",
                "Z3_ASSET_SIZE_",
                "Z3_ASSET_SHA256_",
                "Z3_BIN_SHA256_",
            ] {
                let key = format!("{prefix}{row}");
                let value = pin.value(&key)?;
                match prefix {
                    "Z3_ASSET_"
                        if !value.starts_with(&format!("z3-{version}-"))
                            || Path::new(value)
                                .extension()
                                .is_none_or(|extension| extension != "zip")
                            || !value.bytes().all(|b| {
                                b.is_ascii_alphanumeric() || matches!(b, b'.' | b'-' | b'_')
                            }) =>
                    {
                        anyhow::bail!("invalid Z3 asset name")
                    }
                    "Z3_ASSET_SIZE_" if value.parse::<u64>().ok().is_none_or(|n| n == 0) => {
                        anyhow::bail!("invalid Z3 asset size")
                    }
                    "Z3_ASSET_SHA256_" | "Z3_BIN_SHA256_"
                        if value.len() != 64
                            || !value
                                .bytes()
                                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)) =>
                    {
                        anyhow::bail!("invalid Z3 pin digest")
                    }
                    _ => {}
                }
                keys.insert(key);
            }
        }
        if pin.values.keys().cloned().collect::<BTreeSet<_>>() != keys {
            anyhow::bail!("unknown or orphan Z3 pin key");
        }
        Ok(pin)
    }

    fn value(&self, key: &str) -> Result<&str> {
        self.values
            .get(key)
            .map(String::as_str)
            .with_context(|| format!("missing Z3 pin key {key}"))
    }

    pub(crate) fn host_release(&self) -> Result<Release> {
        let row = host_row(env::consts::OS, env::consts::ARCH)?;
        self.identity(row)?;
        Ok(Release {
            asset: self.value(&format!("Z3_ASSET_{row}"))?.to_owned(),
            archive_sha256: self.value(&format!("Z3_ASSET_SHA256_{row}"))?.to_owned(),
            executable_sha256: self.value(&format!("Z3_BIN_SHA256_{row}"))?.to_owned(),
        })
    }

    pub(super) fn identity(&self, row: &str) -> Result<Identity> {
        if !self
            .value("Z3_ROWS")?
            .split(',')
            .any(|candidate| candidate == row)
        {
            anyhow::bail!("unknown Z3 reference row {row}");
        }
        Ok(Identity {
            version: self.value("Z3_VERSION")?.to_owned(),
            row: row.to_owned(),
            pin_sha256: self.digest.clone(),
            executable_sha256: self.value(&format!("Z3_BIN_SHA256_{row}"))?.to_owned(),
        })
    }

    fn executable_identity(&self, path: &Path) -> Result<Identity> {
        let digest = sha256_file(path)?;
        let row = self
            .value("Z3_ROWS")?
            .split(',')
            .find(|row| self.value(&format!("Z3_BIN_SHA256_{row}")).ok() == Some(digest.as_str()))
            .context("Z3 executable bytes are not in current ci/z3.pin")?;
        self.identity(row)
    }

    pub(super) fn validate_cache(&self, value: &Value, banner: &str) -> Result<()> {
        let identity: Identity = serde_json::from_value(value.clone())
            .context("reference cache lacks current pinned identity; regenerate it")?;
        if identity != self.identity(&identity.row)? || !banner_matches(banner, &identity.version) {
            anyhow::bail!("reference cache does not match current ci/z3.pin; regenerate it");
        }
        Ok(())
    }
}

fn host_row(os: &str, arch: &str) -> Result<&'static str> {
    match (os, arch) {
        ("macos", "aarch64") => Ok("darwin_arm64"),
        ("macos", "x86_64") => Ok("darwin_x86_64"),
        ("linux", "x86_64") => Ok("linux_x86_64"),
        ("linux", "aarch64") => Ok("linux_aarch64"),
        _ => anyhow::bail!("ci/z3.pin has no Z3 release for {os}/{arch}"),
    }
}

/// Immutable projection of the ONE pin owner, not another registry identity.
pub(crate) struct Release {
    pub(crate) asset: String,
    pub(crate) archive_sha256: String,
    pub(crate) executable_sha256: String,
}

impl Release {
    pub(crate) fn stem(&self) -> &str {
        self.asset.strip_suffix(".zip").unwrap_or(&self.asset)
    }
    pub(crate) fn cache_root() -> Result<PathBuf> {
        let base = env::var_os("XDG_CACHE_HOME")
            .filter(|value| !value.is_empty())
            .map(PathBuf::from)
            .or_else(|| env::var_os("HOME").map(|home| PathBuf::from(home).join(".cache")))
            .context("Z3 cache needs XDG_CACHE_HOME or HOME")?;
        Ok(base.join("ay-z3"))
    }
    pub(crate) fn entry(&self, cache: &Path) -> PathBuf {
        cache.join(&self.archive_sha256)
    }
    pub(crate) fn binary(&self, cache: &Path) -> PathBuf {
        self.entry(cache).join(self.stem()).join("bin/z3")
    }
    pub(crate) fn verify_cached(&self, cache: &Path) -> Result<PathBuf> {
        let entry = self.entry(cache);
        for directory in [
            &entry,
            &entry.join(self.stem()),
            &entry.join(self.stem()).join("bin"),
        ] {
            let metadata = fs::symlink_metadata(directory).with_context(|| {
                format!(
                    "Z3 reference absent; run `ay tool install z3-reference`: {}",
                    directory.display()
                )
            })?;
            if !metadata.file_type().is_dir() {
                anyhow::bail!(
                    "Z3 cache directory is not an original directory: {}",
                    directory.display()
                );
            }
        }
        let binary = self.binary(cache);
        let metadata = fs::symlink_metadata(&binary)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if metadata.permissions().mode() & 0o111 == 0 {
                anyhow::bail!("pinned Z3 cache binary is not executable");
            }
        }
        if !metadata.file_type().is_file() || sha256_file(&binary)? != self.executable_sha256 {
            anyhow::bail!("Z3 cache executable bytes disagree with ci/z3.pin; immutable entry {} was not replaced", entry.display());
        }
        Ok(binary)
    }
}

/// The copied image is checked before execution and retained for all probes.
pub(super) struct Snapshot {
    _directory: tempfile::TempDir,
    oracle: ay_sys::z3_oracle::Z3Oracle,
    pub(super) identity: Identity,
}

impl Snapshot {
    pub(super) fn capture(root: &Path, spelling: &str) -> Result<Self> {
        let pin = Pin::load(root)?;
        let source = if spelling == "z3" {
            pin.host_release()?.verify_cached(&Release::cache_root()?)?
        } else {
            let path = PathBuf::from(spelling);
            if path.components().count() > 1 || path.is_absolute() {
                path
            } else {
                crate::cmd_tool::path_lookup(spelling)
                    .context("requested Z3 executable was not found")?
            }
        };
        // Authenticate before executing even a version probe. The private
        // copied image is rehashed below before any actual oracle command.
        let identity = pin.executable_identity(&source)?;
        let directory = tempfile::Builder::new()
            .prefix("ay-z3-reference-")
            .tempdir()?;
        let path = directory
            .path()
            .join(if cfg!(windows) { "z3.exe" } else { "z3" });
        fs::copy(&source, &path)?;
        if sha256_file(&path)? != identity.executable_sha256 {
            anyhow::bail!("Z3 executable changed while capturing pinned reference");
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            fs::set_permissions(&path, fs::Permissions::from_mode(0o500))?;
        }
        let oracle = ay_sys::z3_oracle::resolve_z3_spelling(path.as_os_str())
            .map_err(|reason| anyhow::anyhow!("pinned Z3 snapshot refused: {reason}"))?;
        if !banner_matches(oracle.banner(), pin.version()) {
            anyhow::bail!("pinned executable banner disagrees with ci/z3.pin");
        }
        Ok(Self {
            _directory: directory,
            oracle,
            identity,
        })
    }

    pub(super) fn path(&self) -> &Path {
        self.oracle.path()
    }
    pub(super) fn banner(&self) -> &str {
        self.oracle.banner()
    }
}

#[cfg(test)]
#[path = "reference_tests.rs"]
mod tests;
