// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The git metadata a release-profile stamp watches, so that it is retaken
//! whenever HEAD moves (`provenance.rs`, `StampMode::FollowsHead`).
//!
//! Two rules from main's earlier provenance repairs hold here:
//!
//! - A watched path always exists (6cf32079c7, 216175710a). Cargo reruns a
//!   build script on every build while a `rerun-if-changed` path is missing,
//!   and that is the rebuild storm this code exists to end. A loose-ref
//!   repository normally has no `packed-refs`; a `git archive` export has no
//!   metadata at all.
//! - A packed branch ref still restamps when it becomes loose (216175710a).
//!   While the checked-out branch's ref lives only in `packed-refs`, its
//!   loose file is absent, so its nearest existing parent directory is
//!   watched instead: the next commit creates the loose file there.

use std::path::{Path, PathBuf};

/// The existing files among `metadata`, then `branch_ref` if it exists, or
/// else its nearest existing ancestor. Never a path that does not exist.
pub(crate) fn head_movement_watches(
    metadata: &[PathBuf],
    branch_ref: Option<&Path>,
) -> Vec<PathBuf> {
    let mut watches: Vec<PathBuf> = metadata
        .iter()
        .filter(|path| path.is_file())
        .cloned()
        .collect();
    let existing = branch_ref.and_then(|path| path.ancestors().find(|path| path.exists()));
    if let Some(existing) = existing {
        if !watches.iter().any(|watch| watch == existing) {
            watches.push(existing.to_path_buf());
        }
    }
    watches
}
