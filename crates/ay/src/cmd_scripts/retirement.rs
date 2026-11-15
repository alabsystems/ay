// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Semantic ownership of an internal catalog leaf's removal. This does not
//! approve removing a tool: it identifies the native checks for that change.

use std::collections::BTreeSet;
use std::path::{Component, Path};

#[derive(Debug)]
pub(crate) struct Leaf {
    pub(crate) name: String,
    pub(crate) path: String,
}

pub(crate) fn removed_leaves(old: &str, new: &str) -> Option<Vec<Leaf>> {
    let mut old: toml::Value = old.parse().ok()?;
    let new: toml::Value = new.parse().ok()?;
    let retained = new.get("script")?.as_array()?;
    let entries = old.get_mut("script")?.as_array_mut()?;
    let mut leaves = Vec::new();
    let mut names = BTreeSet::new();
    let mut paths = BTreeSet::new();
    for entry in entries.iter() {
        let name = entry.get("name")?.as_str()?;
        let path = entry.get("path")?.as_str()?;
        if !names.insert(name.to_owned()) || !paths.insert(path.to_owned()) {
            return None;
        }
        if retained.contains(entry) {
            continue;
        }
        if name.is_empty()
            || entry.get("publish")?.as_str()? != "internal"
            || entry
                .get("cli")
                .is_some_and(|value| value.as_str() != Some(""))
            || Path::new(path)
                .components()
                .any(|part| !matches!(part, Component::Normal(_)))
            || !Path::new(path).starts_with("scripts")
        {
            return None;
        }
        leaves.push(Leaf {
            name: name.into(),
            path: path.into(),
        });
    }
    if leaves.is_empty() {
        return None;
    }
    entries.retain(|entry| retained.contains(entry));
    // Equality includes unknown fields, policy, order and all retained entries.
    // Adding/modifying a tool is deliberately outside this ownership proof.
    if old != new {
        return None;
    }
    for entry in retained {
        if let Some(requires) = entry.get("requires") {
            for dependency in requires.as_array()? {
                if leaves
                    .iter()
                    .any(|leaf| Some(leaf.name.as_str()) == dependency.as_str())
                {
                    return None;
                }
            }
        }
    }
    Some(leaves)
}

pub(crate) fn exclusion_removal(old: &str, new: &str, leaves: &[Leaf]) -> bool {
    let removed = leaves
        .iter()
        .map(|leaf| format!("!{}", leaf.path))
        .collect::<BTreeSet<_>>();
    old.lines()
        .filter(|line| !removed.contains(*line))
        .eq(new.lines())
}

#[cfg(test)]
mod tests {
    use super::*;

    const RETAINED: &str = "schema_version = 1\n[[script]]\nname='retained'\npath='scripts/retained.sh'\npublish='internal'\n";
    fn original() -> String {
        format!(
            "{RETAINED}[[script]]\nname='retired'\npath='scripts/retired.sh'\npublish='internal'\n"
        )
    }

    #[test]
    fn identifies_only_exact_internal_leaf_removal() {
        let leaves = removed_leaves(&original(), RETAINED).expect("leaf removal");
        assert_eq!(leaves.len(), 1);
        assert!(exclusion_removal(
            "scripts\n!scripts/retired.sh\n!scripts/other.sh\n",
            "scripts\n!scripts/other.sh\n",
            &leaves
        ));
        assert!(!exclusion_removal(
            "scripts\n!scripts/retired.sh\n!scripts/other.sh\n",
            "scripts\n",
            &leaves
        ));
    }

    #[test]
    fn refuses_dependency_public_modified_fronted_and_policy_changes() {
        let old = original();
        assert!(removed_leaves(
            &old.replace("name='retained'", "requires=['retired']\nname='retained'"),
            &RETAINED.replace("name='retained'", "requires=['retired']\nname='retained'")
        )
        .is_none());
        assert!(removed_leaves(
            &old.replace(
                "path='scripts/retired.sh'\npublish='internal'",
                "path='scripts/retired.sh'\npublish='public'"
            ),
            RETAINED
        )
        .is_none());
        assert!(removed_leaves(&old, &RETAINED.replace("retained.sh", "other.sh")).is_none());
        assert!(removed_leaves(&format!("{old}cli='solve'\n"), RETAINED).is_none());
        assert!(removed_leaves(
            &old,
            &RETAINED.replace("schema_version = 1", "schema_version = 2")
        )
        .is_none());
    }
}
