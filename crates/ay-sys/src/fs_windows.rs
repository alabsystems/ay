// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Windows counterparts of the audited filesystem syscall wrappers in `fs.rs`.
//!
//! Exposed under the same `ay_sys::fs` path as the unix implementation so
//! callers need no target-specific branching.

use std::io;
use std::path::Path;

/// Atomically renames `source` to `target` without replacing an existing target.
///
/// On Windows this is `MoveFileExW` without `MOVEFILE_REPLACE_EXISTING`, the
/// exact counterpart of Linux `renameat2(RENAME_NOREPLACE)` and macOS
/// `renamex_np(RENAME_EXCL)`: it either moves `source` without replacing
/// `target`, or leaves both names intact and fails
/// ([`io::ErrorKind::AlreadyExists`] when `target` already exists).
pub fn rename_noreplace(source: &Path, target: &Path) -> io::Result<()> {
    crate::windows_fs::rename_noreplace(source, target)
}
