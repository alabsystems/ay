// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Resolve placeholders without copying unchanged datatype metadata.
//!
//! Existing datatype values retain their own definitions, even when a registry
//! entry has the same name. Only an uninterpreted placeholder consults that
//! registry. Recursive references keep the parser's finite-snapshot cycle cut;
//! this is not name-based interning.
//!
//! # Cost: the distinct lists, not the tree expansion
//!
//! Resolution walks a sort structurally, and a nested datatype DAG such as
//! `Dk = { a: D(k-1), b: D(k-1) }` has `2^k` paths for `O(k)` type text. The
//! parser's [`ResolutionMemo`] keeps the walk proportional to the distinct
//! constructor lists, across every declaration of one parse:
//!
//! - A definition that reaches no declared placeholder is returned unchanged
//!   without being walked. Lists that mention no `Uninterpreted` sort answer
//!   in `O(1)` from their interned flag; the rest are decided once per list.
//! - The cycle cut fires on a datatype value whose name is already on the
//!   path. With a *regular* registry, which maps every name to a datatype of
//!   that name as every parser insertion does, a placeholder never leads the
//!   walk below its declaration (the declaration is cut at once), so a cut
//!   value and the value that put its name on the path are both reached by
//!   structural descent: the inner one nested in the outer. A finite DAG
//!   cannot nest a value inside an equal value, so the two carry different
//!   constructor lists: only a name seen with two or more lists (a *snapshot
//!   name*) can ever be cut. While no snapshot name is on the path, resolving
//!   `(name, list)` is independent of the path, and its result is memoized.
//! - What the memo learns about lists (their structure, snapshot names) never
//!   goes stale. What it learns from the registry (whether a placeholder is
//!   declared, what it resolves to) is stamped with a generation, which moves
//!   only when an entry changes for a name that some memoized fact mentioned.
//! - Re-resolving the registry after a `declare-datatypes` skips entries that
//!   mention no `Uninterpreted` sort, which resolution cannot change, and
//!   entries that already resolved to themselves.
//!
//! What remains: while a snapshot name is on the path the result memo is
//! off, so a DAG in which every level is itself recursive (each `Dk` has a
//! field of sort `Dk` as well as two of sort `D(k-1)`) is still walked as a
//! tree, as it always was. Memoizing there needs a key that names the path's
//! snapshot names occurring inside the list.
//!
//! The memo keys lists by their content address alone, so it assumes, as the
//! normalized identity does, that SHA-256 does not collide.
//!
//! Reaching a registry entry that is not a datatype of its own name (the
//! parser never makes one) turns the result memo off for the rest of the
//! parse, and the walk is then exactly the unmemoized one.

use super::{ChcDtConstructor, ChcSort, FxHashSet};
use crate::ChcDtId;
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::borrow::Cow;
use std::collections::BTreeSet;

/// The parser's datatype registry: name -> declared datatype sort.
pub(in crate::parser) type Registry = FxHashMap<String, ChcSort>;

/// What sort resolution keeps between the declarations of one parse.
#[derive(Default)]
pub(in crate::parser) struct ResolutionMemo {
    /// Lists whose structure has been scanned for snapshot names.
    scanned: FxHashSet<ChcDtId>,
    /// The first list seen under each datatype name.
    first_list: FxHashMap<String, ChcDtId>,
    /// Names seen with two or more lists: the only names the cut can fire on.
    snapshot_names: FxHashSet<String>,
    /// Stamp of every registry-derived fact below.
    generation: u64,
    /// Per list: does it reach a declared placeholder?
    reaches: FxHashMap<ChcDtId, (u64, bool)>,
    /// Path-independent results per list, by datatype name.
    resolved: FxHashMap<ChcDtId, Vec<Resolved>>,
    /// Uninterpreted names a registry-derived fact was read from.
    mentioned: FxHashSet<String>,
    /// Registry names whose entry mentions an `Uninterpreted` sort.
    open: BTreeSet<String>,
    /// The open names whose entry has not resolved to itself at the current
    /// generation.
    unsettled: BTreeSet<String>,
    /// A placeholder led to an entry that is not a datatype of its name.
    irregular_registry: bool,
    /// A placeholder named a sort the registry did not declare. Parser input
    /// never does: every placeholder names a datatype of its own command.
    undeclared_placeholder: bool,
    /// Lists and sorts visited, for the linearity tests.
    #[cfg(test)]
    work: usize,
}

struct Resolved {
    name: String,
    generation: u64,
    /// `None` when resolution leaves the value unchanged.
    result: Option<ChcSort>,
}

impl ResolutionMemo {
    /// Call before the registry entry for `name` becomes `entry`.
    pub(in crate::parser) fn registry_changed(&mut self, name: &str, entry: &ChcSort) {
        if self.mentioned.contains(name) {
            self.generation += 1;
            // An entry settles (resolves to itself) only when every
            // placeholder it reaches is cut, which depends on its structure
            // alone, or undeclared, which a declaration can change. Without
            // undeclared placeholders a settled entry stays settled.
            if self.undeclared_placeholder {
                #[cfg(test)]
                {
                    self.work += self.open.len();
                }
                self.unsettled.clone_from(&self.open);
            }
        }
        if mentions_uninterpreted(entry) {
            self.open.insert(name.to_owned());
            self.unsettled.insert(name.to_owned());
        } else {
            self.open.remove(name);
            self.unsettled.remove(name);
        }
    }

    #[cfg(test)]
    pub(in crate::parser) fn work(&self) -> usize {
        self.work
    }
}

/// Set the registry entry for `name`, telling the memo first.
pub(in crate::parser) fn set_entry(
    registry: &mut Registry,
    memo: &mut ResolutionMemo,
    name: String,
    sort: ChcSort,
) {
    memo.registry_changed(&name, &sort);
    registry.insert(name, sort);
}

/// Resolve the registry after a `declare-datatypes` inserted `block`.
///
/// The parser used to resolve every entry against the registry as it stood
/// and store every result. That is what this does, except that it skips the
/// entries outside `block` that cannot change: those that mention no
/// `Uninterpreted` sort, and those that already resolved to themselves at the
/// current generation.
pub(in crate::parser) fn resolve_registry(
    registry: &mut Registry,
    memo: &mut ResolutionMemo,
    block: &[String],
) {
    let roots: BTreeSet<String> = block.iter().chain(&memo.unsettled).cloned().collect();
    #[cfg(test)]
    {
        memo.work += roots.len();
    }
    let mut changed: Vec<(String, ChcSort)> = Vec::new();
    let mut unchanged: Vec<&String> = Vec::new();
    {
        let registry: &Registry = registry;
        let mut resolver = Resolver::new(registry, memo);
        for name in &roots {
            let Some(sort) = registry.get(name) else {
                continue;
            };
            match resolver.resolve(sort) {
                Cow::Owned(resolved) => changed.push((name.clone(), resolved)),
                Cow::Borrowed(_) => unchanged.push(name),
            }
        }
    }
    // Settled before any store: a store that moves the generation unsettles
    // them again.
    for name in unchanged {
        memo.unsettled.remove(name);
    }
    for (name, resolved) in changed {
        set_entry(registry, memo, name, resolved);
    }
}

/// Whether an `Uninterpreted` sort occurs anywhere in `sort`.
fn mentions_uninterpreted(sort: &ChcSort) -> bool {
    match sort {
        ChcSort::Uninterpreted(_) => true,
        ChcSort::Array(key, value) => mentions_uninterpreted(key) || mentions_uninterpreted(value),
        ChcSort::Datatype { constructors, .. } => constructors.mentions_uninterpreted(),
        ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::BitVec(_) => false,
    }
}

pub(in crate::parser) struct Resolver<'p> {
    registry: &'p Registry,
    memo: &'p mut ResolutionMemo,
    /// Datatype names on the current path (the finite-snapshot cycle cut).
    seen: FxHashSet<String>,
    /// How many names in `seen` are snapshot names.
    snapshot_names_on_path: usize,
}

impl<'p> Resolver<'p> {
    /// A resolver over `registry`, which must not change while it lives.
    pub(in crate::parser) fn new(registry: &'p Registry, memo: &'p mut ResolutionMemo) -> Self {
        Self {
            registry,
            memo,
            seen: FxHashSet::default(),
            snapshot_names_on_path: 0,
        }
    }

    /// Resolve `sort`: `Borrowed` exactly when nothing in it changes.
    pub(in crate::parser) fn resolve<'a>(&mut self, sort: &'a ChcSort) -> Cow<'a, ChcSort> {
        if !self.reaches_placeholder(sort) {
            return Cow::Borrowed(sort);
        }
        self.scan(sort);
        self.resolve_sort(sort)
    }

    fn resolve_sort<'a>(&mut self, sort: &'a ChcSort) -> Cow<'a, ChcSort> {
        #[cfg(test)]
        {
            self.memo.work += 1;
        }
        match sort {
            ChcSort::Uninterpreted(name) => {
                self.mention(name);
                let registry = self.registry;
                let Some(datatype) = registry.get(name) else {
                    return Cow::Borrowed(sort);
                };
                if !matches!(datatype, ChcSort::Datatype { name: declared, .. } if declared == name)
                {
                    self.memo.irregular_registry = true;
                }
                if !self.enter(name) {
                    return Cow::Owned(datatype.clone());
                }
                let resolved = self.resolve_sort(datatype).into_owned();
                self.leave(name);
                Cow::Owned(resolved)
            }
            ChcSort::Array(key, value) => {
                let key = self.resolve_sort(key);
                let value = self.resolve_sort(value);
                if matches!((&key, &value), (Cow::Borrowed(_), Cow::Borrowed(_))) {
                    Cow::Borrowed(sort)
                } else {
                    Cow::Owned(ChcSort::Array(
                        Box::new(key.into_owned()),
                        Box::new(value.into_owned()),
                    ))
                }
            }
            ChcSort::Datatype { name, constructors } => {
                // A definition that reaches no placeholder is unchanged on
                // every path, whatever the cut holds.
                if !self.reaches_placeholder(sort) || self.seen.contains(name) {
                    return Cow::Borrowed(sort);
                }
                let memoized = self.snapshot_names_on_path == 0 && !self.memo.irregular_registry;
                if memoized {
                    if let Some(done) = self.lookup(name, constructors.id()) {
                        return done.map_or(Cow::Borrowed(sort), Cow::Owned);
                    }
                }
                self.enter(name);
                let changed = self.resolve_constructors(constructors);
                self.leave(name);
                let result = changed.map(|constructors| ChcSort::Datatype {
                    name: name.clone(),
                    constructors: crate::ChcDtConstructors::new(constructors),
                });
                // The walk may have met an irregular entry below.
                if memoized && !self.memo.irregular_registry {
                    self.store(name, constructors.id(), result.clone());
                }
                result.map_or(Cow::Borrowed(sort), Cow::Owned)
            }
            ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::BitVec(_) => {
                Cow::Borrowed(sort)
            }
        }
    }

    fn resolve_constructors(
        &mut self,
        constructors: &[ChcDtConstructor],
    ) -> Option<Vec<ChcDtConstructor>> {
        let mut changed: Option<Vec<ChcDtConstructor>> = None;
        for (constructor_index, constructor) in constructors.iter().enumerate() {
            for (selector_index, selector) in constructor.selectors.iter().enumerate() {
                if let Cow::Owned(sort) = self.resolve_sort(&selector.sort) {
                    // Clone once, only after an actual placeholder/child change.
                    // No recursive structural comparison is needed to discover it.
                    let updated = changed.get_or_insert_with(|| constructors.to_vec());
                    updated[constructor_index].selectors[selector_index].sort = sort;
                }
            }
        }
        changed
    }

    fn lookup(&self, name: &str, id: ChcDtId) -> Option<Option<ChcSort>> {
        self.memo
            .resolved
            .get(&id)?
            .iter()
            .find(|done| done.name == name && done.generation == self.memo.generation)
            .map(|done| done.result.clone())
    }

    fn store(&mut self, name: &str, id: ChcDtId, result: Option<ChcSort>) {
        let generation = self.memo.generation;
        let entries = self.memo.resolved.entry(id).or_default();
        match entries.iter_mut().find(|done| done.name == name) {
            Some(done) => {
                done.generation = generation;
                done.result = result;
            }
            None => entries.push(Resolved {
                name: name.to_owned(),
                generation,
                result,
            }),
        }
    }

    /// Put `name` on the path; `false` if it already is (the cut).
    fn enter(&mut self, name: &str) -> bool {
        if !self.seen.insert(name.to_owned()) {
            return false;
        }
        if self.memo.snapshot_names.contains(name) {
            self.snapshot_names_on_path += 1;
        }
        true
    }

    fn leave(&mut self, name: &str) {
        self.seen.remove(name);
        if self.memo.snapshot_names.contains(name) {
            self.snapshot_names_on_path -= 1;
        }
    }

    /// Record that a registry-derived fact was read for `name`.
    fn mention(&mut self, name: &str) {
        if !self.memo.mentioned.contains(name) {
            self.memo.mentioned.insert(name.to_owned());
        }
        if !self.registry.contains_key(name) {
            self.memo.undeclared_placeholder = true;
        }
    }

    /// Whether `sort` contains an uninterpreted name the registry declares as
    /// a datatype, which resolution would replace. Each list is answered once
    /// per generation.
    fn reaches_placeholder(&mut self, sort: &ChcSort) -> bool {
        match sort {
            ChcSort::Uninterpreted(name) => {
                self.mention(name);
                self.registry.contains_key(name)
            }
            ChcSort::Array(key, value) => {
                self.reaches_placeholder(key) || self.reaches_placeholder(value)
            }
            ChcSort::Datatype { constructors, .. } => {
                if !constructors.mentions_uninterpreted() {
                    return false;
                }
                let id = constructors.id();
                if let Some(&(generation, known)) = self.memo.reaches.get(&id) {
                    if generation == self.memo.generation {
                        return known;
                    }
                }
                #[cfg(test)]
                {
                    self.memo.work += 1;
                }
                // A `true` answer may stop early: names are never removed
                // from the registry, so it can never become false.
                let reaches = constructors
                    .iter()
                    .flat_map(|constructor| &constructor.selectors)
                    .any(|selector| self.reaches_placeholder(&selector.sort));
                self.memo
                    .reaches
                    .insert(id, (self.memo.generation, reaches));
                reaches
            }
            ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::BitVec(_) => false,
        }
    }

    /// Record the `(name, list)` of every datatype value structural descent
    /// from `root` reaches, descending into each list once per parse, and
    /// every name that occurs with two lists.
    fn scan(&mut self, root: &ChcSort) {
        let mut pending = vec![root];
        while let Some(sort) = pending.pop() {
            match sort {
                ChcSort::Array(key, value) => {
                    pending.push(key);
                    pending.push(value);
                }
                ChcSort::Datatype { name, constructors } => {
                    let id = constructors.id();
                    match self.memo.first_list.get(name) {
                        Some(first) if *first != id => {
                            if !self.memo.snapshot_names.contains(name) {
                                self.memo.snapshot_names.insert(name.clone());
                            }
                        }
                        Some(_) => {}
                        None => {
                            self.memo.first_list.insert(name.clone(), id);
                        }
                    }
                    if self.memo.scanned.insert(id) {
                        #[cfg(test)]
                        {
                            self.memo.work += 1;
                        }
                        pending.extend(
                            constructors
                                .iter()
                                .flat_map(|constructor| &constructor.selectors)
                                .map(|selector| &selector.sort),
                        );
                    }
                }
                ChcSort::Uninterpreted(_)
                | ChcSort::Bool
                | ChcSort::Int
                | ChcSort::Real
                | ChcSort::BitVec(_) => {}
            }
        }
    }

    /// Start from a path that already holds `names`, as a resolution nested
    /// inside them would. Memoization stays off while they are on the path.
    #[cfg(test)]
    fn on_path(registry: &'p Registry, memo: &'p mut ResolutionMemo, names: &[&str]) -> Self {
        let mut resolver = Self::new(registry, memo);
        resolver.seen = names.iter().map(|name| (*name).to_owned()).collect();
        resolver.snapshot_names_on_path = names.len();
        resolver
    }
}

#[cfg(test)]
mod tests;
