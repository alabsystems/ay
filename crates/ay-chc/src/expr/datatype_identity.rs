// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Datatype sorts by reference: hash-consed, content-addressed constructor lists.
//!
//! A [`ChcSort::Datatype`] carries its constructors, and every selector carries
//! its own sort, so a nested datatype embeds the definitions of the datatypes it
//! contains. The struct family `D0 = (_ BitVec 32)`, `Dk = { a: D(k-1), b: D(k-1) }`
//! is `O(k)` lines of type text, but as a tree it has `2^k` leaves. The value was
//! always a DAG in memory (children share one `Arc`); identity, hashing,
//! comparison and printing walked it as a tree.
//!
//! [`ChcDtConstructors`] makes the DAG the identity:
//!
//! - **Content address.** Every constructor list has a [`ChcDtId`]: SHA-256 of
//!   an injective, length-prefixed encoding of its constructors and selectors,
//!   in which a nested datatype appears as its name and its own `ChcDtId`, never
//!   inline. Equal lists get the same id in every process; distinct lists get
//!   distinct ids unless SHA-256 collides. Computing an id costs the list's own
//!   text, because every child id is already known.
//! - **Hash-consing.** [`ChcDtConstructors::new`] interns through one global
//!   (sharded) table of weak references. While a list is alive, every structurally equal
//!   list built anywhere in the process is the same allocation, so `Eq` is a
//!   pointer comparison and is exact (a colliding id never merges two lists:
//!   interning compares contents, and children compare by pointer). `Hash`
//!   feeds the id; `Ord` orders by id and breaks an id tie (a collision) by
//!   contents. All three cost `O(1)` in the size of the definition.
//! - **Memory.** The table holds weak references and a dying list removes its
//!   own entry, so the table never keeps a definition alive and holds one entry
//!   per live distinct list.
//!
//! `Eq` keeps its meaning: two datatype sorts are equal exactly when their
//! names and their whole definitions are structurally equal, as with the
//! derived implementation it replaces. Parser snapshots of mutually recursive
//! datatypes that differ structurally remain unequal.

use super::types::{ChcDtConstructor, ChcSort};
use sha2::{Digest, Sha256};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::sync::{Arc, Mutex, MutexGuard, OnceLock, PoisonError, Weak};

/// Domain separator of the identity encoding. Changing the encoding changes
/// every datatype identity, and therefore every normalized CHC identity that
/// references one: bump this and the normalized-input schema together.
const DATATYPE_IDENTITY_DOMAIN: &[u8] = b"ay.chc.datatype-constructors/v1\0";

/// Content address of one hash-consed datatype constructor list.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ChcDtId([u8; 32]);

impl ChcDtId {
    /// The SHA-256 digest bytes.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
}

impl fmt::Display for ChcDtId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in self.0 {
            write!(f, "{byte:02x}")?;
        }
        Ok(())
    }
}

impl fmt::Debug for ChcDtId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "@{self}")
    }
}

/// The constructors of one datatype, hash-consed and identified by content.
///
/// Build one with [`ChcDtConstructors::new`] (or `From<Vec<_>>` /
/// `FromIterator`); read it through `Deref<Target = Vec<ChcDtConstructor>>`.
/// It is immutable: to change a definition, build a new list.
#[derive(Clone)]
pub struct ChcDtConstructors(Arc<Node>);

struct Node {
    id: ChcDtId,
    /// Sort kinds occurring anywhere in this list's definition, nested
    /// datatypes included: content properties, decided once at interning
    /// from the children's own summaries.
    content: Content,
    constructors: Vec<ChcDtConstructor>,
}

/// What occurs anywhere in a definition. Each answer would otherwise walk the
/// definition as a tree: `2^k` paths for a `k`-level struct DAG.
#[derive(Clone, Copy, Default)]
struct Content {
    uninterpreted: bool,
    bitvec: bool,
}

type Table = HashMap<ChcDtId, Vec<Weak<Node>>>;

/// Lock shards, selected by the id's first byte (ids are uniform).
const SHARDS: usize = 64;

/// Lock the intern table shard that holds `id`.
///
/// No critical section below can panic part-way through an update, so a
/// poisoned lock still guards a consistent table and is recovered.
///
/// DEADLOCK RULE: nothing may drop a `ChcDtConstructors`, a `ChcSort` or an
/// `Arc<Node>` while a shard guard is held, because a dying [`Node`] takes
/// its shard's lock in `Drop`. Only `Weak` handles are dropped under a lock.
fn table(id: &ChcDtId) -> MutexGuard<'static, Table> {
    static TABLE: OnceLock<[Mutex<Table>; SHARDS]> = OnceLock::new();
    TABLE.get_or_init(|| std::array::from_fn(|_| Mutex::new(Table::new())))
        [usize::from(id.0[0]) % SHARDS]
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
}

impl Drop for Node {
    fn drop(&mut self) {
        // The guard is released before this node's constructors (and with
        // them any child lists) are dropped, which take a lock in turn.
        let mut table = table(&self.id);
        if let Some(bucket) = table.get_mut(&self.id) {
            bucket.retain(|weak| weak.strong_count() > 0);
            if bucket.is_empty() {
                table.remove(&self.id);
            }
        }
    }
}

impl ChcDtConstructors {
    /// Intern a constructor list.
    ///
    /// Returns the live list structurally equal to `constructors` if there is
    /// one, and otherwise records and returns a new one. Costs the list's own
    /// text (names, selectors, array sorts) plus one table probe; nested
    /// datatypes cost their name and their precomputed id.
    pub fn new(constructors: Vec<ChcDtConstructor>) -> Self {
        let id = identity_of(&constructors);
        let content = content_of(&constructors);
        // Strong handles upgraded under the lock that did not match. Dropping
        // one could run `Node::drop`, which takes the lock, so they are
        // released only after the guard.
        let mut unmatched = Vec::new();
        let node = {
            let mut table = table(&id);
            let bucket = table.entry(id).or_default();
            bucket.retain(|weak| weak.strong_count() > 0);
            let mut found = None;
            for weak in bucket.iter() {
                if let Some(node) = weak.upgrade() {
                    if node.constructors == constructors {
                        found = Some(node);
                        break;
                    }
                    unmatched.push(node);
                }
            }
            match found {
                Some(node) => node,
                None => {
                    let node = Arc::new(Node {
                        id,
                        content,
                        constructors,
                    });
                    bucket.push(Arc::downgrade(&node));
                    node
                }
            }
            // The guard is released here.
        };
        drop(unmatched);
        // When an equal list was found, `constructors` was not moved and is
        // dropped on return, after the guard: its child lists may die and
        // take the lock.
        Self(node)
    }

    /// The content address of this list.
    pub fn id(&self) -> ChcDtId {
        self.0.id
    }

    /// Whether an `Uninterpreted` sort occurs anywhere in this definition,
    /// nested datatypes included. `O(1)`: decided once at interning.
    pub(crate) fn mentions_uninterpreted(&self) -> bool {
        self.0.content.uninterpreted
    }

    /// Whether a `BitVec` sort occurs anywhere in this definition, nested
    /// datatypes included. `O(1)`: decided once at interning.
    pub(crate) fn contains_bitvec(&self) -> bool {
        self.0.content.bitvec
    }

    /// Whether two handles are the same interned list. For live lists this is
    /// exactly structural equality.
    pub fn ptr_eq(left: &Self, right: &Self) -> bool {
        Arc::ptr_eq(&left.0, &right.0)
    }

    /// Address of the interned list's node (not of its constructor buffer,
    /// which `Vec::as_ptr` through `Deref` would give). While both lists are
    /// alive, two addresses are equal exactly when the lists are structurally
    /// equal, so a traversal that borrows its sorts may key a visited set by it.
    pub fn node_addr(&self) -> *const () {
        Arc::as_ptr(&self.0).cast()
    }
}

impl Deref for ChcDtConstructors {
    type Target = Vec<ChcDtConstructor>;

    fn deref(&self) -> &Self::Target {
        &self.0.constructors
    }
}

impl From<Vec<ChcDtConstructor>> for ChcDtConstructors {
    fn from(constructors: Vec<ChcDtConstructor>) -> Self {
        Self::new(constructors)
    }
}

impl FromIterator<ChcDtConstructor> for ChcDtConstructors {
    fn from_iter<I: IntoIterator<Item = ChcDtConstructor>>(constructors: I) -> Self {
        Self::new(constructors.into_iter().collect())
    }
}

impl<'a> IntoIterator for &'a ChcDtConstructors {
    type Item = &'a ChcDtConstructor;
    type IntoIter = std::slice::Iter<'a, ChcDtConstructor>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.constructors.iter()
    }
}

/// Exact structural equality, by pointer: while a list is alive the intern
/// table makes it the only live list with its contents.
impl PartialEq for ChcDtConstructors {
    fn eq(&self, other: &Self) -> bool {
        Self::ptr_eq(self, other)
    }
}

impl Eq for ChcDtConstructors {}

impl Hash for ChcDtConstructors {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.id.hash(state);
    }
}

impl PartialOrd for ChcDtConstructors {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Orders by content address, so the order is the same in every process.
/// Two distinct live lists share an id only under a SHA-256 collision; their
/// contents then decide, which keeps `cmp == Equal` exactly `==`.
impl Ord for ChcDtConstructors {
    fn cmp(&self, other: &Self) -> Ordering {
        if Self::ptr_eq(self, other) {
            return Ordering::Equal;
        }
        self.0
            .id
            .cmp(&other.0.id)
            .then_with(|| self.0.constructors.cmp(&other.0.constructors))
    }
}

/// Prints the reference, never the definition: a nested datatype printed
/// inline costs its tree size.
impl fmt::Debug for ChcDtConstructors {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ChcDtConstructors({:?})", self.0.id)
    }
}

/// SHA-256 over the injective encoding of one constructor list.
///
/// Every variable-length field is length-prefixed and every sort starts with
/// its own tag, so distinct lists have distinct encodings. A nested datatype
/// is encoded as its name and its id, which already commits to its contents.
fn identity_of(constructors: &[ChcDtConstructor]) -> ChcDtId {
    let mut digest = Sha256::new();
    digest.update(DATATYPE_IDENTITY_DOMAIN);
    update_len(&mut digest, constructors.len());
    for constructor in constructors {
        update_text(&mut digest, &constructor.name);
        update_len(&mut digest, constructor.selectors.len());
        for selector in &constructor.selectors {
            update_text(&mut digest, &selector.name);
            update_sort(&mut digest, &selector.sort);
        }
    }
    ChcDtId(digest.finalize().into())
}

fn update_len(digest: &mut Sha256, len: usize) {
    digest.update((len as u64).to_le_bytes());
}

fn update_text(digest: &mut Sha256, text: &str) {
    update_len(digest, text.len());
    digest.update(text.as_bytes());
}

/// Pre-order, with an explicit stack: array sorts are trees of their own.
fn update_sort(digest: &mut Sha256, sort: &ChcSort) {
    let mut pending = vec![sort];
    while let Some(sort) = pending.pop() {
        match sort {
            ChcSort::Bool => digest.update([0]),
            ChcSort::Int => digest.update([1]),
            ChcSort::Real => digest.update([2]),
            ChcSort::BitVec(width) => {
                digest.update([3]);
                digest.update(width.to_le_bytes());
            }
            ChcSort::Array(key, value) => {
                digest.update([4]);
                pending.push(value);
                pending.push(key);
            }
            ChcSort::Uninterpreted(name) => {
                digest.update([5]);
                update_text(digest, name);
            }
            ChcSort::Datatype { name, constructors } => {
                digest.update([6]);
                update_text(digest, name);
                digest.update(constructors.id().as_bytes());
            }
        }
    }
}

/// What occurs in `constructors`: their own array sorts are walked, nested
/// datatypes answer from their interned summary.
fn content_of(constructors: &[ChcDtConstructor]) -> Content {
    let mut content = Content::default();
    let mut pending: Vec<&ChcSort> = constructors
        .iter()
        .flat_map(|constructor| &constructor.selectors)
        .map(|selector| &selector.sort)
        .collect();
    while let Some(sort) = pending.pop() {
        match sort {
            ChcSort::Uninterpreted(_) => content.uninterpreted = true,
            ChcSort::BitVec(_) => content.bitvec = true,
            ChcSort::Datatype { constructors, .. } => {
                content.uninterpreted |= constructors.mentions_uninterpreted();
                content.bitvec |= constructors.contains_bitvec();
            }
            ChcSort::Array(key, value) => {
                pending.push(key);
                pending.push(value);
            }
            ChcSort::Bool | ChcSort::Int | ChcSort::Real => {}
        }
    }
    content
}

/// Table entries (live or not) recorded under `id`. Test only: the table is
/// process-wide, so tests observe their own ids rather than global counts.
#[cfg(test)]
pub(crate) fn table_entries_for(id: ChcDtId) -> usize {
    table(&id).get(&id).map_or(0, Vec::len)
}

#[cfg(test)]
#[path = "tests/datatype_identity.rs"]
mod tests;
