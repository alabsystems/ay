// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The complete retained signature, including sorts outside the scalar arena.

use super::control::{Failure, Scope};
use super::{ChcSort, ChcVar};
use ay_core::kani_compat::DetHashMap;

pub(super) struct Formals<'a> {
    names: DetHashMap<&'a str, &'a ChcVar>,
}

impl<'a> Formals<'a> {
    pub(super) fn new(keep: &'a [ChcVar], scope: &mut Scope<'_>) -> Result<Self, Failure> {
        let mut names = DetHashMap::default();
        for var in keep {
            scope.work(var.name.len().saturating_add(1))?;
            admit_sort(&var.sort, 0, scope)?;
            if names.contains_key(var.name.as_str()) {
                return Err(Failure::Declined);
            }
            scope.grow::<(&str, &ChcVar)>(2)?;
            names.insert(var.name.as_str(), var);
        }
        Ok(Self { names })
    }

    /// Same-name/different-sort occurrences must not become fresh existentials.
    pub(super) fn contains(&self, var: &ChcVar, scope: &mut Scope<'_>) -> Result<bool, Failure> {
        scope.work(var.name.len().saturating_add(1))?;
        let Some(kept) = self.names.get(var.name.as_str()) else {
            return Ok(false);
        };
        admit_sort(&var.sort, 0, scope)?;
        admit_sort(&kept.sort, 0, scope)?;
        if var.sort != kept.sort {
            return Err(Failure::Declined);
        }
        Ok(true)
    }
}

/// Unused formals need no scalar representation. Bound their full sort spine
/// and names nevertheless. Datatype constructors have O(1) identity and are
/// neither traversed nor interpreted by this exact scalar/array fragment.
fn admit_sort(sort: &ChcSort, depth: usize, scope: &mut Scope<'_>) -> Result<(), Failure> {
    scope.depth(depth)?;
    match sort {
        ChcSort::BitVec(0) => Err(Failure::Declined),
        ChcSort::Array(key, value) => {
            admit_sort(key, depth + 1, scope)?;
            admit_sort(value, depth + 1, scope)
        }
        ChcSort::Uninterpreted(name) | ChcSort::Datatype { name, .. } => scope.work(name.len()),
        _ => Ok(()),
    }
}

/// Precharge all recursive comparisons/copies of the conservative closed
/// fragment. Its arrays are flat (scalar key and element), as the arena's:
/// nested and opaque array sorts remain unsupported (5eb47055a).
pub(super) fn charge_sort(
    sort: &ChcSort,
    depth: usize,
    scope: &mut Scope<'_>,
) -> Result<(), Failure> {
    scope.depth(depth)?;
    scope.grow::<ChcSort>(1)?;
    match sort {
        ChcSort::Bool | ChcSort::BitVec(1..=128) => Ok(()),
        ChcSort::Array(key, value)
            if !matches!(**key, ChcSort::Array(..)) && !matches!(**value, ChcSort::Array(..)) =>
        {
            charge_sort(key, depth + 1, scope)?;
            charge_sort(value, depth + 1, scope)
        }
        _ => Err(Failure::Declined),
    }
}
