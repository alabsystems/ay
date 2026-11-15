// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::selection::invalid;
use crate::Result;
use sha2::{Digest, Sha256};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::path::Path;
use std::time::{Duration, Instant};

pub(super) fn hash(bytes: &[u8]) -> String {
    format!("sha256:{:x}", Sha256::digest(bytes))
}
pub(super) fn remaining(deadline: Instant) -> Result<Duration> {
    deadline
        .checked_duration_since(Instant::now())
        .filter(|duration| !duration.is_zero())
        .ok_or_else(|| invalid("original SMT acceptance deadline expired"))
}

/// Fixed-size streaming copy, no parsing/rewriting or compression expansion.
pub(super) fn copy(
    source: &Path,
    destination: &Path,
    expected: &str,
    size: u64,
    deadline: Instant,
) -> Result<()> {
    remaining(deadline)?;
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(nix::libc::O_NOFOLLOW | nix::libc::O_NONBLOCK);
    }
    let mut input = options.open(source)?;
    let before = input.metadata()?;
    if !before.is_file() || before.len() != size {
        return Err(invalid("input snapshot size/type mismatch"));
    }
    let mut output = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(destination)?;
    let mut digest = Sha256::new();
    let mut used = 0_u64;
    let mut block = [0_u8; 8192];
    loop {
        remaining(deadline)?;
        let count = input.read(&mut block)?;
        if count == 0 {
            break;
        }
        used = used
            .checked_add(count as u64)
            .ok_or_else(|| invalid("input size overflow"))?;
        if used > size {
            return Err(invalid("input grew during snapshot"));
        }
        digest.update(&block[..count]);
        output.write_all(&block[..count])?;
    }
    let after = input.metadata()?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        if (
            before.dev(),
            before.ino(),
            before.mtime(),
            before.mtime_nsec(),
            before.ctime(),
            before.ctime_nsec(),
        ) != (
            after.dev(),
            after.ino(),
            after.mtime(),
            after.mtime_nsec(),
            after.ctime(),
            after.ctime_nsec(),
        ) {
            return Err(invalid("input identity changed during snapshot"));
        }
    }
    if used != size || after.len() != size || format!("sha256:{:x}", digest.finalize()) != expected
    {
        return Err(invalid("input snapshot digest mismatch"));
    }
    output.sync_all()?;
    drop(output);
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(destination, fs::Permissions::from_mode(0o400))?;
    }
    remaining(deadline)?;
    Ok(())
}

/// Fixed report admission: no unbounded serde Vec or uninterruptible large
/// write. The inventory is <=1MiB and copied case identity strings are bounded.
struct JsonWriter {
    file: File,
    remaining_bytes: usize,
    deadline: Option<Instant>,
}
impl Write for JsonWriter {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        if self
            .deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
        {
            return Err(std::io::Error::new(
                std::io::ErrorKind::TimedOut,
                "original report deadline",
            ));
        }
        if bytes.len() > self.remaining_bytes {
            return Err(std::io::Error::other("SMT report exceeds8MiB"));
        }
        let count = bytes.len().min(8192);
        let written = self.file.write(&bytes[..count])?;
        self.remaining_bytes -= written;
        Ok(written)
    }
    fn flush(&mut self) -> std::io::Result<()> {
        self.file.flush()
    }
}

pub(super) fn write_json(
    path: &Path,
    value: &impl serde::Serialize,
    deadline: Instant,
) -> Result<()> {
    remaining(deadline)?;
    write_json_inner(path, value, Some(deadline))
}

/// Bounded terminal failure evidence after owned child cleanup. This is not a
/// new work grant: the caller must force all acceptance/closure bits false.
pub(super) fn write_failure_json(path: &Path, value: &impl serde::Serialize) -> Result<()> {
    write_json_inner(path, value, None)
}
fn write_json_inner(
    path: &Path,
    value: &impl serde::Serialize,
    deadline: Option<Instant>,
) -> Result<()> {
    let file = OpenOptions::new().write(true).create_new(true).open(path)?;
    let mut writer = JsonWriter {
        file,
        remaining_bytes: 8 * 1024 * 1024,
        deadline,
    };
    let result = (|| {
        serde_json::to_writer_pretty(&mut writer, value)?;
        writer.flush()?;
        writer.file.sync_all()?;
        if let Some(deadline) = deadline {
            remaining(deadline)?;
        }
        Ok(())
    })();
    drop(writer);
    if result.is_err() {
        fs::remove_file(path)?;
    }
    result
}

pub(super) fn write_bytes(path: &Path, bytes: &[u8], deadline: Instant) -> Result<()> {
    remaining(deadline)?;
    let mut file = File::options().write(true).create_new(true).open(path)?;
    file.write_all(bytes)?;
    file.sync_all()?;
    drop(file);
    remaining(deadline)?;
    Ok(())
}

/// Retain already bounded terminal bytes; no parsing, child work or acceptance.
pub(super) fn write_terminal_bytes(path: &Path, bytes: &[u8]) -> Result<()> {
    if bytes.len() > 3 * 64 * 1024 {
        return Err(invalid("terminal output exceeds capture bound"));
    }
    let mut file = File::options().write(true).create_new(true).open(path)?;
    file.write_all(bytes)?;
    file.sync_all()?;
    Ok(())
}
