// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! In-process composition of completed checks with inert documentation changes.
//! This is not a persistent cache or a claim that a new binary was built.

use super::{Runner, ValidatedHead};
use crate::cmd_gate::land::{plan, scope};
use anyhow::{Context, Result};
use serde::Serialize;
use std::path::{Path, PathBuf};

#[derive(Clone, Serialize)]
pub(super) struct Composition {
    from_head: String,
    from_tree: String,
    to_head: String,
    to_tree: String,
    changes: Vec<Change>,
}

#[derive(Clone, Serialize)]
struct Change {
    path: PathBuf,
    status: String,
    old_blob: String,
    new_blob: String,
}

impl Runner {
    pub(in crate::cmd_gate::land) fn compose_documentation(
        &mut self,
        previous: &ValidatedHead,
        head: &str,
    ) -> Result<Option<ValidatedHead>> {
        let Some(changes) = self.documentation_delta(previous, head)? else {
            return Ok(None);
        };
        let metadata = self.metadata()?;
        self.compose_documentation_checked(previous, head, changes, &metadata)
    }

    fn documentation_delta(
        &mut self,
        previous: &ValidatedHead,
        head: &str,
    ) -> Result<Option<Vec<Change>>> {
        self.exact_clean(head)?;
        if !self.git_status(&["merge-base", "--is-ancestor", &previous.head, head])? {
            return Ok(None);
        }
        // Compare the actual composed tree with the sealed tree. Looking only
        // at incoming commits could miss a merge resolution or another edit.
        let raw = self.git_bytes(&[
            "diff",
            "--raw",
            "-z",
            "--no-renames",
            "--no-abbrev",
            "--no-ext-diff",
            "--no-textconv",
            &previous.head,
            head,
            "--",
        ])?;
        let Some(changes) = documentation_changes(&raw)? else {
            return Ok(None);
        };
        let paths = changes
            .iter()
            .map(|change| change.path.clone())
            .collect::<Vec<_>>();
        let Some(changed) = canonical_changes(&self.root, &paths) else {
            return Ok(None);
        };
        // Unchanged aliases can turn Markdown into compiler/policy input.
        let tree = self.git_bytes(&["ls-tree", "-r", "-z", head])?;
        for entry in tree
            .split(|byte| *byte == 0)
            .filter(|entry| !entry.is_empty())
        {
            let Some(separator) = entry.iter().position(|byte| *byte == b'\t') else {
                return Ok(None);
            };
            let mode = entry[..separator].split(|byte| *byte == b' ').next();
            if mode == Some(b"160000".as_slice()) {
                return Ok(None);
            }
            if mode == Some(b"120000".as_slice()) {
                let Ok(path) = std::str::from_utf8(&entry[separator + 1..]) else {
                    return Ok(None);
                };
                if !input_unaffected(&self.root.join(path), &changed) {
                    return Ok(None);
                }
            }
        }
        Ok(Some(changes))
    }

    fn compose_documentation_checked(
        &mut self,
        previous: &ValidatedHead,
        head: &str,
        changes: Vec<Change>,
        metadata: &plan::Metadata,
    ) -> Result<Option<ValidatedHead>> {
        let paths = changes
            .iter()
            .map(|change| change.path.clone())
            .collect::<Vec<_>>();
        if !provenance_unaffected(&self.root, metadata, &paths) {
            return Ok(None);
        }
        let scope = scope::RustScope::read(self, &previous.head, &paths)?;
        let delta = plan::select(&self.root, metadata, paths, None, &scope)?;
        if delta.broad_compile || !delta.steps.is_empty() {
            return Ok(None);
        }
        let from_tree = self.git(&["rev-parse", &format!("{}^{{tree}}", previous.head)])?;
        let to_tree = self.git(&["rev-parse", &format!("{head}^{{tree}}")])?;
        self.exact_clean(head)?;
        let composition = Composition {
            from_head: previous.head.clone(),
            from_tree: from_tree.trim().into(),
            to_head: head.into(),
            to_tree: to_tree.trim().into(),
            changes,
        };
        println!(
            "{}",
            serde_json::to_string(&serde_json::json!({
                "event": "documentation_composition",
                "checked_head": previous.checked_head,
                "checked_tree": previous.checked_tree,
                "original_checks": previous.checks,
                "composition": composition,
                "new_binary_built": false,
                "checks_reexecuted": false,
                "formal_verification_claim": false,
            }))?
        );
        let mut documentation = previous.documentation.clone();
        documentation.push(composition);
        Ok(Some(ValidatedHead {
            head: head.into(),
            checked_head: previous.checked_head.clone(),
            checked_tree: previous.checked_tree.clone(),
            checks: previous.checks.clone(),
            documentation,
        }))
    }
}

fn documentation_changes(raw: &[u8]) -> Result<Option<Vec<Change>>> {
    if raw.is_empty() {
        return Ok(Some(Vec::new()));
    }
    if raw.last() != Some(&0) {
        return Ok(None);
    }
    let fields = raw[..raw.len() - 1]
        .split(|byte| *byte == 0)
        .collect::<Vec<_>>();
    if fields.len() % 2 != 0 {
        return Ok(None);
    }
    let mut changes = Vec::new();
    for pair in fields.chunks_exact(2) {
        let header = std::str::from_utf8(pair[0]).context("Git delta header is not UTF-8")?;
        let columns = header.split_ascii_whitespace().collect::<Vec<_>>();
        if columns.len() != 5 {
            return Ok(None);
        }
        let regular = match columns[4] {
            "M" => columns[0] == ":100644" && columns[1] == "100644",
            "A" => columns[0] == ":000000" && columns[1] == "100644",
            "D" => columns[0] == ":100644" && columns[1] == "000000",
            _ => false,
        };
        let path =
            PathBuf::from(std::str::from_utf8(pair[1]).context("Git delta path is not UTF-8")?);
        // Do not assume that everything under docs/ is inert: fixtures, Rust
        // source, executables, symlinks and unknown data require a fresh plan.
        if !regular
            || !path
                .extension()
                .is_some_and(|extension| matches!(extension.to_str(), Some("md" | "rst")))
        {
            return Ok(None);
        }
        changes.push(Change {
            path,
            status: columns[4].into(),
            old_blob: columns[2].into(),
            new_blob: columns[3].into(),
        });
    }
    Ok(Some(changes))
}

fn provenance_unaffected(root: &Path, metadata: &plan::Metadata, paths: &[PathBuf]) -> bool {
    let Some(changed) = canonical_changes(root, paths) else {
        return false;
    };
    for package in &metadata.packages {
        // Cargo manifests and targets are inputs without an extra annotation.
        if !input_unaffected(&package.manifest_path, &changed)
            || package
                .targets
                .iter()
                .any(|target| !input_unaffected(&target.src_path, &changed))
        {
            return false;
        }
        let Some(provenance) = package.metadata.get("ay-provenance") else {
            continue;
        };
        let Some(inputs) = provenance
            .get("inputs")
            .and_then(serde_json::Value::as_array)
        else {
            return false;
        };
        let Some(directory) = package.manifest_path.parent() else {
            return false;
        };
        for input in inputs {
            let Some(input) = input.as_str() else {
                return false;
            };
            // Missing/dangling inputs cannot establish non-overlap, including
            // a deleted target reached through an unchanged symlink alias.
            if !input_unaffected(&directory.join(input), &changed) {
                return false;
            }
        }
    }
    true
}

fn canonical_changes(root: &Path, paths: &[PathBuf]) -> Option<Vec<PathBuf>> {
    let root = root.canonicalize().ok()?;
    Some(
        paths
            .iter()
            .map(|path| {
                let absolute = root.join(path);
                absolute.canonicalize().unwrap_or(absolute)
            })
            .collect(),
    )
}

fn input_unaffected(path: &Path, changed: &[PathBuf]) -> bool {
    let Ok(input) = path.canonicalize() else {
        return false;
    };
    !changed
        .iter()
        .any(|path| path == &input || (input.is_dir() && path.starts_with(&input)))
}

#[cfg(test)]
#[path = "land_documentation_tests.rs"]
mod tests;
