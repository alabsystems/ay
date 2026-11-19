// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Cargo-resolved in-tree packages, including independently owned workspaces.
use super::{normalize, Metadata, Package};
use anyhow::{Context, Result};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

pub(super) struct Graph<'a> {
    root: PathBuf,
    metadata: &'a Metadata,
    pub(super) packages: Vec<&'a Package>,
    parents: BTreeMap<&'a str, BTreeSet<&'a str>>,
}

impl<'a> Graph<'a> {
    fn manifest(package: &Package) -> PathBuf {
        package
            .manifest_path
            .canonicalize()
            .or_else(|error| {
                // Workspace metadata can describe a deleted manifest. Keep its
                // existing parent in the same physical namespace as sources.
                let parent = package.manifest_path.parent().ok_or(error)?;
                let parent = parent.canonicalize()?;
                Ok::<_, std::io::Error>(
                    parent.join(package.manifest_path.file_name().unwrap_or_default()),
                )
            })
            .unwrap_or_else(|_| normalize(&package.manifest_path))
    }
    pub(super) fn read(root: &Path, metadata: &'a Metadata) -> Result<Self> {
        let root = root.canonicalize().unwrap_or_else(|_| normalize(root));
        let packages = metadata
            .packages
            .iter()
            .filter(|package| {
                let contained = if metadata.workspace_members.contains(&package.id) {
                    // Cargo's selected workspace identity remains authoritative
                    // (including explicit out-of-tree members). Only foreign
                    // packages need the additional in-tree source proof.
                    true
                } else {
                    match package.manifest_path.canonicalize() {
                        Ok(manifest) => manifest.starts_with(&root),
                        // An unavailable foreign path never acquires in-tree
                        // identity from its spelling alone.
                        Err(_) => false,
                    }
                };
                package.source.is_none() && contained
            })
            .collect();
        let mut parents: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
        if let Some(resolve) = &metadata.resolve {
            for package in &resolve.nodes {
                for dependency in package.dependencies.iter().flatten() {
                    parents.entry(dependency).or_default().insert(&package.id);
                }
            }
        }
        Ok(Self {
            root,
            metadata,
            packages,
            parents,
        })
    }

    pub(super) fn physical_owner(&self, path: &Path) -> Option<&'a Package> {
        let path = path.canonicalize().unwrap_or_else(|_| normalize(path));
        self.packages
            .iter()
            .copied()
            .filter(|package| {
                Self::manifest(package)
                    .parent()
                    .is_some_and(|directory| path.starts_with(directory))
            })
            .max_by_key(|package| package.manifest_path.components().count())
    }

    pub(super) fn owners(&self, path: &Path, provenance: &[&&Package]) -> Vec<&'a Package> {
        let physical = self.physical_owner(path);
        self.packages
            .iter()
            .copied()
            .filter(|package| {
                physical.is_some_and(|owner| owner.id == package.id)
                    || provenance.iter().any(|owner| owner.id == package.id)
            })
            .collect()
    }

    #[cfg(test)]
    fn foreign_owner(&self, path: &Path, provenance: &[&&Package]) -> Option<&'a Package> {
        self.owners(path, provenance)
            .into_iter()
            .find(|package| !self.metadata.workspace_members.contains(&package.id))
    }

    /// Stop at the first importing workspace package on each resolved path.
    /// CLI compilation checks downstream integration without rerunning every
    /// solver suite merely because a small native dependency changed.
    pub(super) fn consumers(&self, id: &str) -> Vec<&'a Package> {
        let mut pending = vec![id];
        let mut visited = BTreeSet::new();
        let mut selected = BTreeSet::new();
        while let Some(id) = pending.pop() {
            if !visited.insert(id) {
                continue;
            }
            for parent in self.parents.get(id).into_iter().flatten() {
                if self
                    .metadata
                    .workspace_members
                    .iter()
                    .any(|member| member.as_str() == *parent)
                {
                    selected.insert(*parent);
                } else {
                    pending.push(*parent);
                }
            }
        }
        self.packages
            .iter()
            .copied()
            .filter(|package| selected.contains(package.id.as_str()))
            .collect()
    }

    /// Whether the CLI's resolved dependency closure includes this owner.
    /// Unlike `consumers`, traverse through workspace importers as well.
    /// Only metadata resolving the actual CLI features may exclude a build;
    /// unavailable, ambiguous or incomplete graph input stays conservative.
    pub(super) fn cli_depends_on(&self, id: &str) -> bool {
        let mut candidates = self.metadata.packages.iter().filter(|package| {
            package.name == "ay" && self.metadata.workspace_members.contains(&package.id)
        });
        let Some(cli) = candidates.next() else {
            return true;
        };
        if candidates.next().is_some() {
            return true;
        }
        if !cli
            .targets
            .iter()
            .any(|target| target.name == "ay" && target.kind.iter().any(|kind| kind == "bin"))
        {
            return true;
        }
        let Some(resolve) = &self.metadata.resolve else {
            return true;
        };
        let nodes: BTreeMap<_, _> = resolve
            .nodes
            .iter()
            .map(|node| (node.id.as_str(), node))
            .collect();
        if nodes.len() != resolve.nodes.len() || !nodes.contains_key(id) {
            return true;
        }
        let Some(cli_node) = nodes.get(cli.id.as_str()) else {
            return true;
        };
        if !super::CLI_FEATURES
            .split(',')
            .all(|feature| cli_node.features.iter().any(|enabled| enabled == feature))
        {
            return true;
        }
        let mut pending = vec![cli.id.as_str()];
        let mut visited = BTreeSet::new();
        while let Some(current) = pending.pop() {
            if current == id {
                return true;
            }
            if !visited.insert(current) {
                continue;
            }
            let Some(node) = nodes.get(current) else {
                return true;
            };
            let Some(dependencies) = &node.dependencies else {
                return true;
            };
            pending.extend(dependencies.iter().map(String::as_str));
        }
        false
    }

    /// Narrow only exclusion additions for known independent workspaces. All
    /// other manifest settings and explicit member selection must be equal;
    /// globs, escaping paths, removals and overlapping members stay broad.
    pub(super) fn only_adds_independent_exclusions(
        &self,
        before: Option<&str>,
        base_paths: Option<&BTreeSet<PathBuf>>,
    ) -> Result<bool> {
        let Some(before) = before else {
            return Ok(false);
        };
        let Some(base_paths) = base_paths else {
            return Ok(false);
        };
        let mut before: toml::Value =
            toml::from_str(before).context("parse base workspace manifest")?;
        let mut after: toml::Value =
            toml::from_str(&std::fs::read_to_string(self.root.join("Cargo.toml"))?)?;
        fn exclusions(value: &mut toml::Value) -> Option<BTreeSet<String>> {
            let workspace = value.get_mut("workspace")?.as_table_mut()?;
            let values = workspace
                .remove("exclude")
                .unwrap_or_else(|| toml::Value::Array(Vec::new()));
            values
                .as_array()?
                .iter()
                .map(|value| value.as_str().map(str::to_owned))
                .collect()
        }
        let Some(old) = exclusions(&mut before) else {
            return Ok(false);
        };
        let Some(new) = exclusions(&mut after) else {
            return Ok(false);
        };
        if before != after || old == new || !old.is_subset(&new) {
            return Ok(false);
        }
        let Some(members) = after
            .get("workspace")
            .and_then(|v| v.get("members"))
            .and_then(toml::Value::as_array)
        else {
            return Ok(false);
        };
        for exclusion in new.difference(&old) {
            let path = Path::new(exclusion);
            if path.is_absolute()
                || path
                    .components()
                    .any(|part| !matches!(part, std::path::Component::Normal(_)))
                || exclusion.contains(['*', '?', '[', ']'])
            {
                return Ok(false);
            }
            // A new exclusion cannot hide any previously tracked package or
            // source. Existing directories require ordinary broad validation;
            // source ownership is never guessed from a new manifest alone.
            if base_paths.iter().any(|old| old.starts_with(path)) {
                return Ok(false);
            }
            for member in members {
                let Some(member) = member.as_str() else {
                    return Ok(false);
                };
                if member.contains(['*', '?', '[', ']'])
                    || Path::new(member).starts_with(path)
                    || path.starts_with(member)
                {
                    return Ok(false);
                }
            }
            let directory = self.root.join(path);
            let Some(package) = self
                .packages
                .iter()
                .find(|package| Self::manifest(package).parent() == Some(directory.as_path()))
            else {
                return Ok(false);
            };
            if self.metadata.workspace_members.contains(&package.id) {
                return Ok(false);
            }
            let manifest: toml::Value =
                toml::from_str(&std::fs::read_to_string(&package.manifest_path)?)?;
            if manifest.get("workspace").is_none() {
                return Ok(false);
            }
        }
        // Every currently selected member must already exist in the base.
        // New/deleted/renamed members cannot use this configuration shortcut.
        for member in self
            .packages
            .iter()
            .filter(|package| self.metadata.workspace_members.contains(&package.id))
        {
            let manifest = Self::manifest(member);
            let relative = manifest.strip_prefix(&self.root)?;
            if !base_paths.contains(relative) {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

#[cfg(test)]
#[path = "land_local_paths_tests.rs"]
mod tests;
