// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Merkle digests of a session's problem: its header, its live declarations
//! and its live assertions (#session-scope-digest).
//!
//! # What a digest names
//!
//! The live-scope digest names the PROBLEM a check decided, so it covers
//! everything the verdict depends on: the header (logic and options), every
//! live declaration and definition (sorts, parameters, `define-fun` bodies,
//! datatype declarations), and the live assertions in order. Two sessions
//! that differ only in a definition body — `(define-fun f ((y Int)) Int (+ y
//! 1))` against `(- y 1)` beside the same assertion — have different digests.
//!
//! It is `H(live, declarations, assertions)`, two chains kept as one link per
//! live item: `declarations` starts at the header digest and links each live
//! declaration, `assertions` starts at zero and links each live assertion's
//! node digest. `pop` truncates both to their length at the matching `push`.
//! A caller holding its own record of a row's assertions recomputes the
//! assertion chain and combines it with the session's declarations digest
//! ([`ScopeDigests::live_digest_of`]).
//!
//! # Linear in the DAG
//!
//! A node's digest is `H(node, sort digest, payload, child count, child
//! digests)`, computed once per distinct node (identity-keyed, `memo.rs`). The
//! payload is a canonical encoding of the node's own fields (`payload.rs`):
//! the variant's name, its scalars, and the digests of the sorts it carries,
//! never a child's sort (a child's digest already covers it) and never a
//! `Debug` rendering. A sort's digest is a Merkle hash over the sort DAG,
//! computed once per distinct sort allocation. So the cost of a digest is the
//! size of the term DAG plus the size of the sort DAG: a nested record sort
//! whose fields share one sort costs its DAG, not its unfolded tree, and a
//! 1000-field record is hashed once, not once per node of its sort.

use std::collections::HashMap;

use sha2::{Digest, Sha256};

use super::memo::{node_key, sort_key, NodeKey, ScopedTable};
use super::payload::{node_payload, Payload};
use crate::constraint::Constraint;
use crate::expr::Expr;
use crate::sort::{Sort, SortInner};

const NODE_DOMAIN: &[u8] = b"ay-bindings.expr-node@2";
const SORT_DOMAIN: &[u8] = b"ay-bindings.sort@1";
const HEADER_DOMAIN: &[u8] = b"ay-bindings.session-header@1";
const DECLARATION_DOMAIN: &[u8] = b"ay-bindings.session-declaration@1";
const ASSERTION_DOMAIN: &[u8] = b"ay-bindings.session-scope@1";
const LIVE_DOMAIN: &[u8] = b"ay-bindings.session-live@1";

/// Digests computed by one call before they are committed: lookups see the
/// committed tables first, inserts land here. `assertion_digest` discards it,
/// so asking for a digest never grows the session's tables.
struct Overlay<'a> {
    nodes: &'a ScopedTable<NodeKey, Expr, [u8; 32]>,
    sorts: &'a ScopedTable<usize, Sort, [u8; 32]>,
    new_nodes: HashMap<NodeKey, (Expr, [u8; 32])>,
    new_sorts: HashMap<usize, (Sort, [u8; 32])>,
}

impl Overlay<'_> {
    fn node(&self, key: &NodeKey) -> Option<[u8; 32]> {
        self.nodes
            .get(key)
            .or_else(|| self.new_nodes.get(key).map(|(_, digest)| *digest))
    }

    fn sort(&self, key: usize) -> Option<[u8; 32]> {
        self.sorts
            .get(&key)
            .or_else(|| self.new_sorts.get(&key).map(|(_, digest)| *digest))
    }

    /// Merkle digest of `sort`, each distinct sort allocation once. Iterative
    /// post-order, so a deep sort cannot exhaust the native stack.
    fn sort_digest(&mut self, sort: &Sort) -> [u8; 32] {
        let mut stack = vec![sort.clone()];
        while let Some(current) = stack.last().cloned() {
            if self.sort(sort_key(&current)).is_some() {
                stack.pop();
                continue;
            }
            let children = sort_children(&current);
            let missing: Vec<Sort> = children
                .iter()
                .filter(|child| self.sort(sort_key(child)).is_none())
                .cloned()
                .collect();
            if !missing.is_empty() {
                stack.extend(missing);
                continue;
            }
            stack.pop();
            let digest = sort_shell_digest(&current, |child| self.sort(sort_key(child)));
            self.new_sorts
                .insert(sort_key(&current), (current.clone(), digest));
        }
        self.sort(sort_key(sort))
            .unwrap_or_else(|| sort_shell_digest(sort, |_| None))
    }

    /// Merkle digest of `expr`, each distinct node once. Iterative
    /// post-order: a node is hashed only once every child digest is known.
    fn node_digest(&mut self, expr: &Expr) -> [u8; 32] {
        let mut stack: Vec<Expr> = vec![expr.clone()];
        while let Some(current) = stack.last().cloned() {
            if self.node(&node_key(&current)).is_some() {
                stack.pop();
                continue;
            }
            let mut children = Vec::new();
            let mut missing = false;
            for child in current.children() {
                match self.node(&node_key(child)) {
                    Some(digest) => children.push(digest),
                    None => {
                        missing = true;
                        stack.push(child.clone());
                    }
                }
            }
            if missing {
                continue;
            }
            stack.pop();
            let digest = self.shell_digest(&current, &children);
            self.new_nodes
                .insert(node_key(&current), (current.clone(), digest));
        }
        match self.node(&node_key(expr)) {
            Some(digest) => digest,
            None => {
                let children: Vec<[u8; 32]> = expr
                    .children()
                    .map(|child| self.node_digest(child))
                    .collect();
                self.shell_digest(expr, &children)
            }
        }
    }

    fn shell_digest(&mut self, expr: &Expr, children: &[[u8; 32]]) -> [u8; 32] {
        let sort = self.sort_digest(expr.sort());
        let mut hasher = Sha256::new();
        hasher.update(NODE_DOMAIN);
        hasher.update(sort);
        {
            let mut sort_digest = |sort: &Sort| self.sort_digest(sort);
            let mut payload = Payload::new(&mut hasher, &mut sort_digest);
            node_payload(expr.value(), &mut payload);
        }
        hasher.update(length(children.len()));
        for child in children {
            hasher.update(child);
        }
        hasher.finalize().into()
    }
}

fn sort_children(sort: &Sort) -> Vec<Sort> {
    match sort.inner() {
        SortInner::Array(array) => vec![array.index_sort.clone(), array.element_sort.clone()],
        SortInner::Datatype(datatype) => datatype
            .constructors
            .iter()
            .flat_map(|constructor| constructor.fields.iter().map(|field| field.sort.clone()))
            .collect(),
        SortInner::Seq(element) => vec![(**element).clone()],
        _ => Vec::new(),
    }
}

/// A sort's own fields and its children's digests. `child` returns `None`
/// only for a child the caller has not digested, which the iterative walk
/// never asks for; the fallback hashes a fixed marker rather than panic.
fn sort_shell_digest(sort: &Sort, child: impl Fn(&Sort) -> Option<[u8; 32]>) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(SORT_DOMAIN);
    let mut child_digest = |sort: &Sort| hasher_input(child(sort));
    let mut fields: Vec<Vec<u8>> = Vec::new();
    let tag: &str = match sort.inner() {
        SortInner::Bool => "Bool",
        SortInner::Int => "Int",
        SortInner::Real => "Real",
        SortInner::String => "String",
        SortInner::RegLan => "RegLan",
        SortInner::BitVec(bitvec) => {
            fields.push(bitvec.width.to_le_bytes().to_vec());
            "BitVec"
        }
        SortInner::FloatingPoint(exponent, significand) => {
            fields.push(exponent.to_le_bytes().to_vec());
            fields.push(significand.to_le_bytes().to_vec());
            "FloatingPoint"
        }
        SortInner::Uninterpreted(name) => {
            fields.push(text(name));
            "Uninterpreted"
        }
        SortInner::DatatypeRef(name) => {
            fields.push(text(name));
            "DatatypeRef"
        }
        SortInner::Array(array) => {
            fields.push(child_digest(&array.index_sort));
            fields.push(child_digest(&array.element_sort));
            "Array"
        }
        SortInner::Seq(element) => {
            fields.push(child_digest(element));
            "Seq"
        }
        SortInner::Datatype(datatype) => {
            fields.push(text(&datatype.name));
            fields.push(length(datatype.constructors.len()).to_vec());
            for constructor in &datatype.constructors {
                fields.push(text(&constructor.name));
                fields.push(length(constructor.fields.len()).to_vec());
                for field in &constructor.fields {
                    fields.push(text(&field.name));
                    fields.push(child_digest(&field.sort));
                }
            }
            "Datatype"
        }
    };
    hasher.update(text(tag));
    for field in fields {
        hasher.update(field);
    }
    hasher.finalize().into()
}

fn hasher_input(digest: Option<[u8; 32]>) -> Vec<u8> {
    digest.map_or_else(|| b"undigested".to_vec(), |digest| digest.to_vec())
}

/// A length-prefixed byte string: injective over sequences of strings.
fn text(value: &str) -> Vec<u8> {
    let mut out = length(value.len()).to_vec();
    out.extend_from_slice(value.as_bytes());
    out
}

pub(super) fn length(count: usize) -> [u8; 8] {
    u64::try_from(count).unwrap_or(u64::MAX).to_le_bytes()
}

/// The digests of a session's live problem.
#[derive(Debug)]
pub(super) struct ScopeDigests {
    nodes: ScopedTable<NodeKey, Expr, [u8; 32]>,
    sorts: ScopedTable<usize, Sort, [u8; 32]>,
    header: [u8; 32],
    /// Declaration chain head after each live declaration, in order.
    declarations: Vec<[u8; 32]>,
    /// Assertion chain head after each live assertion, in order.
    assertions: Vec<[u8; 32]>,
    /// The two chains' lengths at each open scope's `push`.
    marks: Vec<(usize, usize)>,
}

impl ScopeDigests {
    /// Digests of a session opened with `logic` and `options`.
    pub(super) fn new(logic: &str, options: &[(String, String)]) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(HEADER_DOMAIN);
        hasher.update(text(logic));
        hasher.update(length(options.len()));
        for (name, value) in options {
            hasher.update(text(name));
            hasher.update(text(value));
        }
        Self {
            nodes: ScopedTable::new(),
            sorts: ScopedTable::new(),
            header: hasher.finalize().into(),
            declarations: Vec::new(),
            assertions: Vec::new(),
            marks: Vec::new(),
        }
    }

    fn overlay(&self) -> Overlay<'_> {
        Overlay {
            nodes: &self.nodes,
            sorts: &self.sorts,
            new_nodes: HashMap::new(),
            new_sorts: HashMap::new(),
        }
    }

    /// Run `compute` over an overlay and commit what it digested.
    fn committed<T>(&mut self, compute: impl FnOnce(&mut Overlay<'_>) -> T) -> T {
        let mut overlay = self.overlay();
        let result = compute(&mut overlay);
        let (new_nodes, new_sorts) = (overlay.new_nodes, overlay.new_sorts);
        for (key, (keep, digest)) in new_nodes {
            self.nodes.insert(key, keep, digest);
        }
        for (key, (keep, digest)) in new_sorts {
            self.sorts.insert(key, keep, digest);
        }
        result
    }

    /// Record one live declaration, definition, option or logic.
    pub(super) fn declare(&mut self, command: &Constraint) {
        let digest = self.committed(|overlay| declaration_digest(overlay, command));
        let link = link(DECLARATION_DOMAIN, self.declarations_head(), digest);
        self.declarations.push(link);
    }

    /// Record one live assertion and return its node digest.
    pub(super) fn assert(&mut self, expr: &Expr) -> [u8; 32] {
        let node = self.committed(|overlay| overlay.node_digest(expr));
        let link = link(ASSERTION_DOMAIN, self.assertions_head(), node);
        self.assertions.push(link);
        node
    }

    /// Node digest of `expr` as [`Self::assert`] would chain it, computed
    /// without growing the session's tables.
    pub(super) fn node(&self, expr: &Expr) -> [u8; 32] {
        self.overlay().node_digest(expr)
    }

    pub(super) fn push(&mut self) {
        self.nodes.push();
        self.sorts.push();
        self.marks
            .push((self.declarations.len(), self.assertions.len()));
    }

    pub(super) fn pop(&mut self) {
        self.nodes.pop();
        self.sorts.pop();
        if let Some((declarations, assertions)) = self.marks.pop() {
            self.declarations.truncate(declarations);
            self.assertions.truncate(assertions);
        }
    }

    fn declarations_head(&self) -> [u8; 32] {
        self.declarations.last().copied().unwrap_or(self.header)
    }

    fn assertions_head(&self) -> [u8; 32] {
        self.assertions.last().copied().unwrap_or([0; 32])
    }

    /// Digest of the live problem: header, declarations, assertions.
    pub(super) fn scope(&self) -> [u8; 32] {
        live(self.declarations_head(), self.assertions_head())
    }

    /// The live digest a stack with the session's live declarations and
    /// these assertion node digests, in order, would have.
    pub(super) fn live_digest_of(&self, assertions: &[[u8; 32]]) -> [u8; 32] {
        let chain = assertions.iter().fold([0; 32], |prefix, &node| {
            link(ASSERTION_DOMAIN, prefix, node)
        });
        live(self.declarations_head(), chain)
    }

    /// Number of live assertions.
    pub(super) fn live(&self) -> usize {
        self.assertions.len()
    }

    /// Number of open scopes.
    pub(super) fn depth(&self) -> usize {
        self.marks.len()
    }
}

fn link(domain: &[u8], prefix: [u8; 32], item: [u8; 32]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(prefix);
    hasher.update(item);
    hasher.finalize().into()
}

fn live(declarations: [u8; 32], assertions: [u8; 32]) -> [u8; 32] {
    link(LIVE_DOMAIN, declarations, assertions)
}

/// The digest of one declaration-class command; every field the solver
/// reads, `define-fun` bodies through their node digests.
fn declaration_digest(overlay: &mut Overlay<'_>, command: &Constraint) -> [u8; 32] {
    let mut hasher = Sha256::new();
    match command {
        Constraint::SetLogic(logic) => {
            hasher.update(text("set-logic"));
            hasher.update(text(logic));
        }
        Constraint::SetOption { name, value } => {
            hasher.update(text("set-option"));
            hasher.update(text(name));
            hasher.update(text(value));
        }
        Constraint::DeclareConst {
            name,
            sort: declared,
        } => {
            hasher.update(text("declare-const"));
            hasher.update(text(name));
            hasher.update(overlay.sort_digest(declared));
        }
        Constraint::DeclareVar {
            name,
            sort: declared,
        } => {
            hasher.update(text("declare-var"));
            hasher.update(text(name));
            hasher.update(overlay.sort_digest(declared));
        }
        Constraint::DeclareFun {
            name,
            arg_sorts,
            return_sort,
        } => {
            hasher.update(text("declare-fun"));
            hasher.update(text(name));
            hasher.update(length(arg_sorts.len()));
            for argument in arg_sorts {
                hasher.update(overlay.sort_digest(argument));
            }
            hasher.update(overlay.sort_digest(return_sort));
        }
        Constraint::DeclareDatatype(datatype) => {
            hasher.update(text("declare-datatype"));
            hasher.update(
                overlay.sort_digest(&Sort::from_inner(SortInner::Datatype(datatype.clone()))),
            );
        }
        Constraint::DefineFun {
            name,
            params,
            return_sort,
            body,
        } => {
            hasher.update(text("define-fun"));
            hasher.update(text(name));
            hasher.update(length(params.len()));
            for (parameter, parameter_sort) in params {
                hasher.update(text(parameter));
                hasher.update(overlay.sort_digest(parameter_sort));
            }
            hasher.update(overlay.sort_digest(return_sort));
            hasher.update(overlay.node_digest(body));
        }
        other => {
            // Session `declare` refuses every other command before it is
            // recorded; a digest of its rendering keeps this total anyway.
            hasher.update(text("other"));
            hasher.update(text(&other.to_string()));
        }
    }
    hasher.finalize().into()
}

#[cfg(test)]
impl ScopeDigests {
    /// Distinct sort allocations whose digest the session holds.
    pub(super) fn digested_sorts(&self) -> usize {
        self.sorts.len()
    }

    /// Distinct expression nodes whose digest the session holds.
    pub(super) fn digested_nodes(&self) -> usize {
        self.nodes.len()
    }
}

#[cfg(test)]
#[path = "digest_tests.rs"]
mod tests;
