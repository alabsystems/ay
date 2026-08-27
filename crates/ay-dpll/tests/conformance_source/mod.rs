// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Logical-module source reader for the source-text conformance guards.
//!
//! # Why this exists
//!
//! The chokepoint conformance suites are SOURCE-TEXT guards: they read a file,
//! `find` an anchor, and assert facts about the text around it. They were
//! written against a one-file-per-module tree. `7d448bb9c3 refactor: repair
//! post-pull quality regressions` split several of those files into a parent
//! plus a submodule directory, and every guard whose anchor moved into the
//! directory started reporting "must exist" — a guard that cannot find what it
//! guards, which reads as coverage while checking nothing.
//!
//! The fix is not three new paths. A guard must address a LOGICAL MODULE — the
//! parent file PLUS its submodule directory — so the next split cannot re-blind
//! it.
//!
//! # Region semantics, which is the part that can go wrong
//!
//! Several assertions are REGION-BOUNDED: find anchor A, find anchor B after
//! it, assert facts about (or an ordering within) the text between them. A
//! reader that CONCATENATED the files of a logical module would let such a
//! region silently span a file boundary, and the assertion would then be
//! meaningless or accidentally satisfied. So this reader never concatenates:
//!
//! * [`LogicalModule::locate`] searches every file of the module and requires
//!   the anchor to resolve EXACTLY ONCE. Zero is the stale-path failure this
//!   module exists to fix; more than one is just as dangerous, because the
//!   guard would silently bind to whichever site happened to sort first.
//!   `begin_public_solve` already exists twice in this crate (the lifecycle
//!   entrypoint and an unrelated array-cache method in `executor/theories`),
//!   so this is a live hazard, not a hypothetical one.
//! * [`LogicalModule::region`] requires BOTH endpoints to resolve into the SAME
//!   file and panics otherwise. A region is therefore always a contiguous slice
//!   of ONE file — byte-for-byte the same kind of value the guards asserted
//!   over before this module existed. A future split that separates a region's
//!   two endpoints fails LOUD instead of silently widening the region.
//! * [`LogicalModule::region_to_item_end`] bounds a region by the closing brace
//!   of the enclosing column-0 item (the `impl`/`struct`/`fn` block) rather
//!   than by a following anchor. It is for the case where the anchor that used
//!   to terminate a region left the file: it keeps the region inside one file
//!   and is at least as TIGHT as a following-declaration bound.
//!
//! Existence checks (`contains`/`count`) do search the whole logical module,
//! because "this statement exists in this module" is exactly what they mean and
//! a submodule split must not silently make one false.

#![allow(dead_code)]

use std::path::{Path, PathBuf};

/// One file of a logical module.
pub(crate) struct SourceFile {
    rel: String,
    text: String,
}

/// A parent source file plus every `.rs` file in its submodule directory.
pub(crate) struct LogicalModule {
    root: String,
    files: Vec<SourceFile>,
}

/// A contiguous slice of exactly one file of a logical module.
pub(crate) struct Region<'a> {
    module: &'a str,
    file: &'a str,
    label: String,
    text: &'a str,
}

fn crate_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn collect(dir: &Path, base: &Path, out: &mut Vec<SourceFile>) {
    let mut entries = std::fs::read_dir(dir)
        .unwrap_or_else(|error| panic!("cannot list {}: {error}", dir.display()))
        .map(|entry| {
            entry
                .unwrap_or_else(|error| panic!("cannot read entry in {}: {error}", dir.display()))
                .path()
        })
        .collect::<Vec<_>>();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            collect(&path, base, out);
        } else if path.extension().and_then(|ext| ext.to_str()) == Some("rs") {
            let rel = path
                .strip_prefix(base)
                .unwrap_or(&path)
                .to_string_lossy()
                .replace('\\', "/");
            let text = std::fs::read_to_string(&path)
                .unwrap_or_else(|error| panic!("cannot read {}: {error}", path.display()));
            out.push(SourceFile { rel, text });
        }
    }
}

impl LogicalModule {
    /// Load the logical module rooted at `root_rel` (crate-relative), i.e. that
    /// file plus every `.rs` file beneath its submodule directory.
    pub(crate) fn load(root_rel: &str) -> Self {
        let base = crate_root();
        let parent = base.join(root_rel);
        let text = std::fs::read_to_string(&parent)
            .unwrap_or_else(|error| panic!("cannot read {}: {error}", parent.display()));
        let mut files = vec![SourceFile {
            rel: root_rel.to_string(),
            text,
        }];
        let dir = parent.with_extension("");
        if dir.is_dir() {
            collect(&dir, &base, &mut files);
        }
        Self {
            root: root_rel.to_string(),
            files,
        }
    }

    pub(crate) fn root(&self) -> &str {
        &self.root
    }

    pub(crate) fn file_count(&self) -> usize {
        self.files.len()
    }

    /// Crate-relative paths of every file in this logical module.
    pub(crate) fn file_names(&self) -> Vec<&str> {
        self.files.iter().map(|file| file.rel.as_str()).collect()
    }

    fn sites(&self, anchor: &str) -> Vec<(usize, usize)> {
        let mut sites = Vec::new();
        for (index, file) in self.files.iter().enumerate() {
            let mut from = 0;
            while let Some(offset) = file.text[from..].find(anchor) {
                let at = from + offset;
                sites.push((index, at));
                from = at + 1;
            }
        }
        sites
    }

    /// Resolve `anchor` to its single site in this logical module.
    ///
    /// THE META-GUARD. Panics on zero sites (the stale-path drift) and on more
    /// than one (a duplicate anchor, which would silently bind the guard to an
    /// arbitrary site).
    pub(crate) fn locate(&self, anchor: &str) -> (usize, usize) {
        let sites = self.sites(anchor);
        match sites.len() {
            1 => sites[0],
            0 => panic!(
                "conformance anchor {anchor:?} resolves NOWHERE in the logical module {} \
                 ({} file(s): {:?}). Either the guarded code was removed, or it moved and this \
                 guard has been blind since it did.",
                self.root,
                self.files.len(),
                self.file_names()
            ),
            n => panic!(
                "conformance anchor {anchor:?} resolves {n} times in the logical module {} \
                 (at {:?}). A duplicate anchor is as dangerous as a missing one: the guard \
                 would bind to whichever site sorted first. Disambiguate the anchor.",
                self.root,
                sites
                    .iter()
                    .map(|&(index, offset)| format!("{}@{offset}", self.files[index].rel))
                    .collect::<Vec<_>>()
            ),
        }
    }

    /// The text between two uniquely-resolved anchors of the SAME file.
    ///
    /// Panics if the endpoints land in different files: the region would not be
    /// a well-defined stretch of source, and every ordering/containment
    /// assertion taken over it would be fiction.
    pub(crate) fn region(&self, start: &str, end: &str) -> Region<'_> {
        let (start_file, start_at) = self.locate(start);
        let (end_file, end_at) = self.locate(end);
        assert_eq!(
            start_file, end_file,
            "region anchors straddle a module split: {start:?} is in {} but {end:?} is in {}. \
             A region spanning a file boundary is not a well-defined stretch of source — \
             re-bound the region inside one file (see `region_to_item_end`) rather than \
             concatenating the module.",
            self.files[start_file].rel, self.files[end_file].rel
        );
        assert!(
            start_at < end_at,
            "region anchors are inverted in {}: {start:?} at {start_at} must precede {end:?} \
             at {end_at}",
            self.files[start_file].rel
        );
        Region {
            module: &self.root,
            file: &self.files[start_file].rel,
            label: format!("{start:?}..{end:?}"),
            text: &self.files[start_file].text[start_at..end_at],
        }
    }

    /// The text from a uniquely-resolved anchor to the closing brace of the
    /// enclosing column-0 item.
    ///
    /// For a method anchor that is the end of its `impl` block; for a column-0
    /// `struct`/`fn` anchor it is that item's own closing brace. Use this where
    /// the anchor that used to terminate a region has left the file — it keeps
    /// the region inside one file and never runs past the item.
    pub(crate) fn region_to_item_end(&self, start: &str) -> Region<'_> {
        let (file, start_at) = self.locate(start);
        let text = &self.files[file].text;
        let end_at = text[start_at..]
            .find("\n}\n")
            .map(|offset| start_at + offset + 2)
            .unwrap_or(text.len());
        Region {
            module: &self.root,
            file: &self.files[file].rel,
            label: format!("{start:?}..end-of-item"),
            text: &text[start_at..end_at],
        }
    }

    /// Every occurrence of `prefix` across the logical module, each paired with
    /// the text running from it to the NEXT occurrence in the SAME file (or to
    /// that file's end).
    ///
    /// For a family of sibling declarations sharing a prefix. Windows never
    /// span a file boundary, so splitting the family across submodules narrows
    /// each window rather than silently merging two members into one.
    pub(crate) fn windows(&self, prefix: &str) -> Vec<Region<'_>> {
        let mut regions = Vec::new();
        for file in &self.files {
            let starts = file
                .text
                .match_indices(prefix)
                .map(|(offset, _)| offset)
                .collect::<Vec<_>>();
            for (index, &start) in starts.iter().enumerate() {
                let end = starts.get(index + 1).copied().unwrap_or(file.text.len());
                regions.push(Region {
                    module: &self.root,
                    file: &file.rel,
                    label: format!("{prefix:?} window {index}"),
                    text: &file.text[start..end],
                });
            }
        }
        regions
    }

    /// Whether any file of the logical module contains `needle`.
    pub(crate) fn contains(&self, needle: &str) -> bool {
        self.files.iter().any(|file| file.text.contains(needle))
    }

    /// How many times `needle` occurs across the logical module.
    pub(crate) fn count(&self, needle: &str) -> usize {
        self.files
            .iter()
            .map(|file| file.text.matches(needle).count())
            .sum()
    }

    /// Whitespace-normalized containment, evaluated per file.
    ///
    /// Deliberately NOT a normalized concatenation: joining the module first
    /// would let a needle be satisfied by text that straddles two files.
    pub(crate) fn normalized_contains(&self, needle: &str) -> bool {
        self.files.iter().any(|file| {
            file.text
                .split_whitespace()
                .collect::<Vec<_>>()
                .join(" ")
                .contains(needle)
        })
    }

    /// Assert every listed anchor resolves exactly once across this module.
    pub(crate) fn assert_anchors_resolve_uniquely(&self, anchors: &[&str]) {
        for anchor in anchors {
            let _ = self.locate(anchor);
        }
    }
}

impl Region<'_> {
    pub(crate) fn text(&self) -> &str {
        self.text
    }

    pub(crate) fn file(&self) -> &str {
        self.file
    }

    pub(crate) fn contains(&self, needle: &str) -> bool {
        self.text.contains(needle)
    }

    pub(crate) fn count(&self, needle: &str) -> usize {
        self.text.matches(needle).count()
    }

    /// Offset of the first occurrence of `needle` inside the region, for the
    /// ordering assertions. Panics with the region's identity when absent.
    pub(crate) fn offset_of(&self, needle: &str, what: &str) -> usize {
        self.text.find(needle).unwrap_or_else(|| {
            panic!(
                "{what}: {needle:?} is absent from the region {} of {} (module {})",
                self.label, self.file, self.module
            )
        })
    }

    /// Offset of the LAST occurrence of `needle` inside the region.
    pub(crate) fn last_offset_of(&self, needle: &str, what: &str) -> usize {
        self.text.rfind(needle).unwrap_or_else(|| {
            panic!(
                "{what}: {needle:?} is absent from the region {} of {} (module {})",
                self.label, self.file, self.module
            )
        })
    }
}

pub(crate) mod inventory;
