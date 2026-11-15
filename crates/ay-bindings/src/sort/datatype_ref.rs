// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Scope resolution for [`SortInner::DatatypeRef`].
//!
//! A datatype reference is meaningful only inside a declaration of the
//! datatype it names. This module finds references that are not, so that a
//! program declaration and the native lowering can refuse them instead of
//! turning them into a bare sort name.

use std::collections::{HashMap, HashSet};

use super::{DatatypeSort, Sort, SortInner};

/// One enclosing datatype declaration on the path to a sort position.
struct Scope<'a> {
    name: &'a str,
    parent: Option<usize>,
}

impl Sort {
    /// First datatype reference in this sort that no enclosing datatype
    /// declaration (inside this sort) names. `None` means every reference is
    /// enclosed by a declaration of its name: the sort is closed.
    #[must_use]
    pub(crate) fn dangling_datatype_ref(&self) -> Option<&str> {
        dangling_ref(self, None)
    }
}

/// The dangling-reference check for the field sorts of one declaration: a
/// field may refer to `dt` itself, or to a datatype declared around the
/// reference inside the field sort.
pub(crate) fn dangling_datatype_ref_in_declaration(dt: &DatatypeSort) -> Option<&str> {
    dt.constructors
        .iter()
        .flat_map(|ctor| &ctor.fields)
        .find_map(|field| dangling_ref(&field.sort, Some(&dt.name)))
}

fn dangling_ref<'a>(sort: &'a Sort, enclosing: Option<&'a str>) -> Option<&'a str> {
    // Scope ids are interned by (declaration node, parent scope), so a shared
    // sub-DAG reached again under the same enclosing declarations is walked
    // once: every node is visited at most once per distinct scope chain.
    let mut scopes: Vec<Scope<'a>> = Vec::new();
    let mut interned: HashMap<(*const SortInner, Option<usize>), usize> = HashMap::new();
    let mut seen: HashSet<(*const SortInner, Option<usize>)> = HashSet::new();
    let start = enclosing.map(|name| {
        scopes.push(Scope { name, parent: None });
        0
    });
    let mut pending = vec![(sort, start)];
    while let Some((sort, scope)) = pending.pop() {
        let inner = sort.inner();
        if !seen.insert((std::ptr::from_ref(inner), scope)) {
            continue;
        }
        match inner {
            SortInner::DatatypeRef(name) => {
                let mut cursor = scope;
                while let Some(id) = cursor {
                    if scopes[id].name == name {
                        break;
                    }
                    cursor = scopes[id].parent;
                }
                if cursor.is_none() {
                    return Some(name);
                }
            }
            SortInner::Datatype(dt) => {
                let id = *interned
                    .entry((std::ptr::from_ref(inner), scope))
                    .or_insert_with(|| {
                        scopes.push(Scope {
                            name: &dt.name,
                            parent: scope,
                        });
                        scopes.len() - 1
                    });
                for field in dt.constructors.iter().flat_map(|ctor| &ctor.fields) {
                    pending.push((&field.sort, Some(id)));
                }
            }
            SortInner::Array(array) => {
                pending.push((&array.element_sort, scope));
                pending.push((&array.index_sort, scope));
            }
            SortInner::Seq(element) => pending.push((element, scope)),
            _ => {}
        }
    }
    None
}
