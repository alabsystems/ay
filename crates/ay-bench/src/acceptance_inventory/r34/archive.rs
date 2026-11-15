// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{capture, Inventory, R34Archive};
use crate::{BenchError, Result};
use flate2::read::GzDecoder;
use std::collections::BTreeMap;
use std::io::Read as _;
use std::path::{Component, Path};

// The exact compressed container is 234769 bytes. Bounds apply before formula
// admission, including unselected archive contents; no files are extracted.
const MAX_ARCHIVE: u64 = 1024 * 1024;
const MAX_EXPANDED: u64 = 32 * 1024 * 1024;
const MAX_ENTRIES: usize = 512;

#[cfg(test)]
mod open_tests;

pub(super) fn load(inventory: &Path, path: &Path) -> Result<R34Archive> {
    // Validate the actual raw document, not a reserialization which could
    // insert absent optional null fields or trust a caller-edited public struct.
    let inventory = Inventory::load(inventory)?;
    if inventory.document.schema != super::super::INVENTORY_SCHEMA_V8 {
        return Err(BenchError::msg(
            "R34 execution requires the frozen v8 inventory",
        ));
    }
    let capture = capture::load()?;
    let archived = inventory
        .document
        .stored_inputs
        .iter()
        .filter(|input| {
            input.path == capture.archive.path && input.request_ids.iter().any(|id| id == "R34")
        })
        .count();
    if archived == 0 {
        return Err(BenchError::msg(
            "R34 original archive is not bound by the inventory",
        ));
    }
    let bytes = read_opened(open_archive(path)?, &capture.archive)?;
    let files = members(&bytes, &capture)?;
    Ok(R34Archive {
        capture,
        files,
        inventory_sha256: inventory.sha256.clone(),
    })
}

fn open_archive(path: &Path) -> Result<std::fs::File> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        // One open chooses the object. Never check a pathname and then reopen
        // it: replacement could follow a symlink or wait for a FIFO writer.
        Ok(std::fs::OpenOptions::new()
            .read(true)
            .custom_flags(nix::libc::O_NOFOLLOW | nix::libc::O_NONBLOCK)
            .open(path)?)
    }
    #[cfg(not(unix))]
    {
        let _ = path;
        Err(BenchError::msg(
            "R34 archive requires a no-follow, nonblocking open",
        ))
    }
}

fn read_opened(file: std::fs::File, identity: &capture::ArchiveIdentity) -> Result<Vec<u8>> {
    let meta = file.metadata()?;
    if !meta.file_type().is_file() || meta.len() != identity.bytes || meta.len() > MAX_ARCHIVE {
        return Err(BenchError::msg(
            "R34 archive must be the exact regular file",
        ));
    }
    let mut bytes = Vec::new();
    file.take(MAX_ARCHIVE + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 != identity.bytes || bytes.len() as u64 > MAX_ARCHIVE {
        return Err(BenchError::msg(
            "R34 archive changed or exceeded its byte bound",
        ));
    }
    capture::require_hash(&capture::digest(&bytes), &identity.sha256, "archive")?;
    Ok(bytes)
}

pub(super) fn members(
    bytes: &[u8],
    capture: &capture::Capture,
) -> Result<BTreeMap<String, Vec<u8>>> {
    let decoder = GzDecoder::new(bytes).take(MAX_EXPANDED + 1);
    let mut archive = tar::Archive::new(decoder);
    let mut files = BTreeMap::new();
    let mut expanded = 0u64;
    for (index, entry) in archive.entries()?.enumerate() {
        if index >= MAX_ENTRIES {
            return Err(BenchError::msg("R34 archive entry cap"));
        }
        let mut entry = entry?;
        let path = entry.path()?.into_owned();
        if path
            .components()
            .any(|part| !matches!(part, Component::Normal(_)))
        {
            return Err(BenchError::msg(
                "R34 archive contains a non-relative member",
            ));
        }
        let Some(name) = path.to_str() else {
            return Err(BenchError::msg("R34 archive member is not UTF-8"));
        };
        if entry.header().entry_type().is_dir() {
            continue;
        }
        if !entry.header().entry_type().is_file() {
            return Err(BenchError::msg("R34 archive has a non-regular data member"));
        }
        expanded = expanded
            .checked_add(entry.size())
            .ok_or_else(|| BenchError::msg("R34 expanded byte overflow"))?;
        if expanded > MAX_EXPANDED {
            return Err(BenchError::msg("R34 expanded byte cap"));
        }
        let Some(identity) = capture.files.get(name) else {
            continue;
        };
        if entry.size() != identity.bytes || files.contains_key(name) {
            return Err(BenchError::msg(
                "R34 duplicate or wrong-sized selected member",
            ));
        }
        let mut data = Vec::new();
        entry.read_to_end(&mut data)?;
        capture::require_hash(&capture::digest(&data), &identity.sha256, name)?;
        files.insert(name.to_owned(), data);
    }
    if files.len() != capture.files.len() {
        return Err(BenchError::msg(
            "R34 archive lacks a required captured member",
        ));
    }
    Ok(files)
}
