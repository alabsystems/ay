// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded JSON observations shared by read-only qualification inspectors.

use super::*;
use std::io::Read as _;

pub(super) fn same_observed_regular_file(before: &fs::Metadata, after: &fs::Metadata) -> bool {
    if !after.is_file() || before.len() != after.len() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        before.dev() == after.dev()
            && before.ino() == after.ino()
            && before.mtime() == after.mtime()
            && before.mtime_nsec() == after.mtime_nsec()
            && before.ctime() == after.ctime()
            && before.ctime_nsec() == after.ctime_nsec()
    }
    #[cfg(not(unix))]
    {
        before
            .modified()
            .is_ok_and(|time| after.modified().ok() == Some(time))
    }
}

/// Deserialize and hash one bounded regular-file stream. The digest includes
/// trailing whitespace and covers the bytes actually delivered to the parser.
pub(super) fn read_hashed_json<T: serde::de::DeserializeOwned>(
    path: &Path,
    limit: u64,
    label: &str,
) -> Result<(String, T), String> {
    struct HashingReader {
        file: fs::File,
        digest: Sha256,
        bytes: u64,
        limit: u64,
    }
    impl std::io::Read for HashingReader {
        fn read(&mut self, output: &mut [u8]) -> std::io::Result<usize> {
            let read = self.file.read(output)?;
            self.bytes = self.bytes.saturating_add(read as u64);
            if self.bytes > self.limit {
                return Err(std::io::Error::other("JSON input exceeds its byte bound"));
            }
            self.digest.update(&output[..read]);
            Ok(read)
        }
    }

    let before = fs::symlink_metadata(path).map_err(|error| format!("inspect {label}: {error}"))?;
    if !before.is_file() || before.len() > limit {
        return Err(format!(
            "{label} must be a bounded non-symlink regular file: {}",
            path.display()
        ));
    }
    let mut options = fs::OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
    }
    let file = options
        .open(path)
        .map_err(|error| format!("open {label}: {error}"))?;
    let opened = file
        .metadata()
        .map_err(|error| format!("inspect opened {label}: {error}"))?;
    if !same_observed_regular_file(&before, &opened) {
        return Err(format!(
            "{label} changed before decoding: {}",
            path.display()
        ));
    }
    // serde_json reads individual bytes. Keep the buffer outside the hashing
    // layer so the hash consumes chunks and no full JSON buffer is retained.
    let mut reader = std::io::BufReader::new(HashingReader {
        file,
        digest: Sha256::new(),
        bytes: 0,
        limit,
    });
    let value = serde_json::from_reader(&mut reader)
        .map_err(|error| format!("invalid {label} {}: {error}", path.display()))?;
    let reader = reader.into_inner();
    let after = reader
        .file
        .metadata()
        .map_err(|error| format!("inspect read {label}: {error}"))?;
    let named =
        fs::symlink_metadata(path).map_err(|error| format!("reinspect {label}: {error}"))?;
    if reader.bytes != before.len()
        || !same_observed_regular_file(&before, &after)
        || !same_observed_regular_file(&before, &named)
    {
        return Err(format!(
            "{label} changed during decoding: {}",
            path.display()
        ));
    }
    Ok((format!("{:x}", reader.digest.finalize()), value))
}
