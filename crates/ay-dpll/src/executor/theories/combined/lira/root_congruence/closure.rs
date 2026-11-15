// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Congruence closure over the ground terms of an assertion window.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};

/// The head of an interior node, as congruence sees it.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Head {
    App(Symbol, Sort),
    Not,
    Ite(Sort),
}

/// The ground terms of a window as nodes, and the classes a set of
/// equalities between them generates under congruence.
///
/// Quantified and `let` terms are leaves: their bodies are not nodes.
pub(super) struct Closure {
    node_of: HashMap<TermId, u32>,
    term_of: Vec<TermId>,
    children: Vec<Vec<u32>>,
    size: Vec<u64>,
    parent: Vec<u32>,
    class_size: Vec<u32>,
    /// Per class root: the interior nodes with a child in the class.
    uses: Vec<Vec<u32>>,
    /// Per class root: the value constant the class holds, if any.
    value: Vec<Option<TermId>>,
    heads: Vec<Option<u32>>,
    head_ids: HashMap<Head, u32>,
    signatures: HashMap<(u32, Vec<u32>), u32>,
    pending: Vec<(u32, u32)>,
}

impl Closure {
    /// The closure of no equality over the terms of `roots`.
    pub(super) fn new(terms: &TermStore, roots: &[TermId]) -> Self {
        let mut closure = Self {
            node_of: HashMap::default(),
            term_of: Vec::new(),
            children: Vec::new(),
            size: Vec::new(),
            parent: Vec::new(),
            class_size: Vec::new(),
            uses: Vec::new(),
            value: Vec::new(),
            heads: Vec::new(),
            head_ids: HashMap::default(),
            signatures: HashMap::default(),
            pending: Vec::new(),
        };
        for &root in roots {
            closure.add_term(terms, root);
        }
        closure.enter_signatures();
        closure
    }

    pub(super) fn len(&self) -> usize {
        self.term_of.len()
    }

    /// The node of a term of the window.
    pub(super) fn node(&self, term: TermId) -> u32 {
        self.node_of[&term]
    }

    pub(super) fn term(&self, node: u32) -> TermId {
        self.term_of[node as usize]
    }

    pub(super) fn children(&self, node: u32) -> &[u32] {
        &self.children[node as usize]
    }

    /// Tree size of the node's term, saturating.
    pub(super) fn size(&self, node: u32) -> u64 {
        self.size[node as usize]
    }

    /// Number of nodes in the class `root` stands for.
    pub(super) fn class_size(&self, root: u32) -> u32 {
        self.class_size[root as usize]
    }

    /// The node that stands for `node`'s class.
    pub(super) fn find(&mut self, mut node: u32) -> u32 {
        let mut root = node;
        while self.parent[root as usize] != root {
            root = self.parent[root as usize];
        }
        while self.parent[node as usize] != root {
            let next = self.parent[node as usize];
            self.parent[node as usize] = root;
            node = next;
        }
        root
    }

    /// Join the classes of `a` and `b` and everything congruence joins with
    /// them. `false` when they were one class already, or when the two
    /// classes hold different value constants: the equality that asks for
    /// that join is false, and the caller leaves it for the solver to refute.
    pub(super) fn assert_equal(&mut self, a: u32, b: u32) -> bool {
        let joined = self.merge(a, b);
        while let Some((x, y)) = self.pending.pop() {
            self.merge(x, y);
        }
        joined
    }

    /// Add `root` and its ground subterms as nodes, children first.
    fn add_term(&mut self, terms: &TermStore, root: TermId) {
        let mut stack: Vec<(TermId, bool)> = vec![(root, false)];
        while let Some((term, children_done)) = stack.pop() {
            if self.node_of.contains_key(&term) {
                continue;
            }
            let (head, kids): (Option<Head>, Vec<TermId>) = match terms.get(term) {
                TermData::App(sym, args) => (
                    Some(Head::App(sym.clone(), terms.sort(term).clone())),
                    args.clone(),
                ),
                TermData::Not(inner) => (Some(Head::Not), vec![*inner]),
                TermData::Ite(c, t, e) => {
                    (Some(Head::Ite(terms.sort(term).clone())), vec![*c, *t, *e])
                }
                // Constants, free symbols, and the quantified or `let` terms
                // the closure does not look into.
                _ => (None, Vec::new()),
            };
            if !children_done && kids.iter().any(|kid| !self.node_of.contains_key(kid)) {
                stack.push((term, true));
                for &kid in kids.iter().rev() {
                    if !self.node_of.contains_key(&kid) {
                        stack.push((kid, false));
                    }
                }
                continue;
            }
            let node = self.term_of.len() as u32;
            let kid_nodes: Vec<u32> = kids.iter().map(|kid| self.node_of[kid]).collect();
            let size = kid_nodes.iter().fold(1u64, |acc, &kid| {
                acc.saturating_add(self.size[kid as usize])
            });
            let head_id = head.map(|head| {
                let next = self.head_ids.len() as u32;
                *self.head_ids.entry(head).or_insert(next)
            });
            self.node_of.insert(term, node);
            self.term_of.push(term);
            self.children.push(kid_nodes);
            self.size.push(size);
            self.parent.push(node);
            self.class_size.push(1);
            self.uses.push(Vec::new());
            self.value
                .push(matches!(terms.get(term), TermData::Const(_)).then_some(term));
            self.heads.push(head_id);
        }
    }

    fn signature(&mut self, node: u32) -> Option<(u32, Vec<u32>)> {
        let head = self.heads[node as usize]?;
        let kids = self.children[node as usize].clone();
        Some((head, kids.into_iter().map(|kid| self.find(kid)).collect()))
    }

    /// Enter every interior node into the signature table and its children's
    /// use lists. Hash consing makes two nodes with one signature impossible
    /// here; the table is what `merge` reads afterwards.
    fn enter_signatures(&mut self) {
        for node in 0..self.term_of.len() as u32 {
            let Some(signature) = self.signature(node) else {
                continue;
            };
            for &class in &signature.1 {
                let uses = &mut self.uses[class as usize];
                if uses.last() != Some(&node) {
                    uses.push(node);
                }
            }
            if let Some(&other) = self.signatures.get(&signature) {
                self.pending.push((node, other));
            } else {
                self.signatures.insert(signature, node);
            }
        }
        while let Some((x, y)) = self.pending.pop() {
            self.merge(x, y);
        }
    }

    fn merge(&mut self, a: u32, b: u32) -> bool {
        let (mut into, mut from) = (self.find(a), self.find(b));
        if into == from {
            return false;
        }
        if let (Some(x), Some(y)) = (self.value[into as usize], self.value[from as usize]) {
            if x != y {
                return false;
            }
        }
        if self.class_size[into as usize] < self.class_size[from as usize] {
            std::mem::swap(&mut into, &mut from);
        }
        self.parent[from as usize] = into;
        self.class_size[into as usize] += self.class_size[from as usize];
        if self.value[into as usize].is_none() {
            self.value[into as usize] = self.value[from as usize];
        }
        // A user of the absorbed class has a new signature; one that now
        // collides with another node is congruent to it.
        let moved = std::mem::take(&mut self.uses[from as usize]);
        for &user in &moved {
            if let Some(signature) = self.signature(user) {
                match self.signatures.get(&signature) {
                    Some(&other) if other != user => self.pending.push((user, other)),
                    Some(_) => {}
                    None => {
                        self.signatures.insert(signature, user);
                    }
                }
            }
        }
        self.uses[into as usize].extend(moved);
        true
    }
}

#[cfg(test)]
#[path = "closure_tests.rs"]
mod tests;
