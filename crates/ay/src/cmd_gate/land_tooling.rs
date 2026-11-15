// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native ownership evidence for retiring unconsumed internal script leaves.

use super::{plan, Runner};
use crate::cmd_scripts::retirement::{exclusion_removal, removed_leaves, Leaf};
use anyhow::Result;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

const INDEX: &str = "scripts/index-internal.toml";
const MANIFEST: &str = "publish/manifest.txt";

pub(super) fn owned_removals(
    runner: &mut Runner,
    base: &str,
    paths: &[PathBuf],
    metadata: &plan::Metadata,
) -> Result<BTreeSet<PathBuf>> {
    let empty = BTreeSet::new();
    if !paths.iter().any(|path| path == Path::new(INDEX))
        || !runner.git_status(&["cat-file", "-e", &format!("{base}:{INDEX}")])?
    {
        return Ok(empty);
    }
    let old = runner.git(&["show", &format!("{base}:{INDEX}")])?;
    let Ok(new) = std::fs::read_to_string(runner.root.join(INDEX)) else {
        return Ok(empty);
    };
    let Some(leaves) = removed_leaves(&old, &new) else {
        return Ok(empty);
    };
    let deleted = runner.git_bytes(&[
        "diff",
        "--no-renames",
        "--diff-filter=D",
        "--name-only",
        "-z",
        base,
        "HEAD",
        "--",
    ])?;
    let deleted = deleted.split(|byte| *byte == 0).collect::<BTreeSet<_>>();
    let mut owned = BTreeSet::from([PathBuf::from(INDEX)]);
    for leaf in &leaves {
        if !deleted.contains(leaf.path.as_bytes()) {
            return Ok(empty);
        }
        let entry = runner.git(&["ls-tree", base, "--", &leaf.path])?;
        if !entry.starts_with("100644 blob ") && !entry.starts_with("100755 blob ") {
            return Ok(empty);
        }
        owned.insert(PathBuf::from(&leaf.path));
    }
    if paths.iter().any(|path| path == Path::new(MANIFEST)) {
        let old = runner.git(&["show", &format!("{base}:{MANIFEST}")])?;
        let Ok(new) = std::fs::read_to_string(runner.root.join(MANIFEST)) else {
            return Ok(empty);
        };
        if !exclusion_removal(&old, &new, &leaves) {
            return Ok(empty);
        }
        owned.insert(PathBuf::from(MANIFEST));
    }
    // An explicit build/runtime input or Cargo target remains its package's
    // responsibility even when a catalog happens to call it an internal tool.
    let mut inputs = Vec::new();
    for package in &metadata.packages {
        if let Some(value) = package
            .metadata
            .get("ay-provenance")
            .and_then(|value| value.get("inputs"))
        {
            if !value
                .as_array()
                .is_some_and(|values| values.iter().all(|value| value.is_string()))
            {
                return Ok(empty);
            }
        }
        inputs.push(package.manifest_path.clone());
        inputs.extend(package.targets.iter().map(|target| target.src_path.clone()));
        inputs.extend(plan::provenance_inputs(package));
    }
    if owned.iter().any(|path| {
        let path = runner.root.join(path);
        inputs
            .iter()
            .any(|input| path == *input || path.starts_with(input))
    }) || !unaliased(runner, &leaves)?
        || !unconsumed(runner, &leaves, &owned, &inputs)?
    {
        return Ok(empty);
    }
    Ok(owned)
}

fn unaliased(runner: &mut Runner, leaves: &[Leaf]) -> Result<bool> {
    let tree = runner.git_bytes(&["ls-tree", "-r", "-z", "HEAD"])?;
    for entry in tree
        .split(|byte| *byte == 0)
        .filter(|entry| !entry.is_empty())
    {
        let Some(separator) = entry.iter().position(|byte| *byte == b'\t') else {
            return Ok(false);
        };
        if entry.starts_with(b"160000 ") {
            return Ok(false);
        }
        if !entry.starts_with(b"120000 ") {
            continue;
        }
        let Ok(path) = std::str::from_utf8(&entry[separator + 1..]) else {
            return Ok(false);
        };
        let Ok(target) = runner.root.join(path).canonicalize() else {
            return Ok(false);
        };
        for leaf in leaves {
            let path = runner.root.join(&leaf.path);
            let Some(parent) = path.parent().and_then(|parent| parent.canonicalize().ok()) else {
                return Ok(false);
            };
            let Some(name) = path.file_name() else {
                return Ok(false);
            };
            if parent.join(name).starts_with(&target) {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

fn unconsumed(
    runner: &mut Runner,
    leaves: &[Leaf],
    owned: &BTreeSet<PathBuf>,
    inputs: &[PathBuf],
) -> Result<bool> {
    let mut tokens = BTreeSet::new();
    for leaf in leaves {
        tokens.insert(leaf.path.clone());
        tokens.insert(leaf.name.clone());
        let Some(name) = Path::new(&leaf.path)
            .file_name()
            .and_then(|name| name.to_str())
        else {
            return Ok(false);
        };
        tokens.insert(name.to_owned());
        // Python imports and script loaders commonly omit the extension, and
        // the module stem need not equal the catalog's hyphenated CLI name.
        let Some(stem) = Path::new(&leaf.path)
            .file_stem()
            .and_then(|name| name.to_str())
        else {
            return Ok(false);
        };
        tokens.insert(stem.to_owned());
    }
    let mut args = vec!["grep", "-a", "-l", "-z", "-F"];
    for token in &tokens {
        args.extend(["-e", token.as_str()]);
    }
    // The committed tree, not a working-tree ignore rule or an index-only
    // census. Git status 1 is the sole accepted 'no matches' result.
    args.extend(["HEAD", "--", "."]);
    let matches = runner.git_search(&args)?;
    for path in matches
        .split(|byte| *byte == 0)
        .filter(|path| !path.is_empty())
    {
        let Ok(path) = std::str::from_utf8(path) else {
            return Ok(false);
        };
        let Some(path) = path.strip_prefix("HEAD:") else {
            return Ok(false);
        };
        let path = Path::new(path);
        if owned.contains(path) {
            continue;
        }
        let absolute = runner.root.join(path);
        if !plan::documentation(path)
            || inputs
                .iter()
                .any(|input| absolute == *input || absolute.starts_with(input))
        {
            return Ok(false);
        }
    }
    Ok(true)
}

#[cfg(test)]
#[path = "land_tooling_tests.rs"]
mod tests;
