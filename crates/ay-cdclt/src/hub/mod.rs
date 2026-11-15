// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The hub: one e-graph per engine check, the kernel's term hub (design H1).
//!
//! Every term two theories share, every uninterpreted application and every
//! equality between such terms is a node. The hub keeps
//! - congruence closure, with a congruence table keyed by function and
//!   argument classes;
//! - a proof forest (`target` / `just`) from which [`Hub::explain`] derives
//!   the literals behind any equality, including congruence steps;
//! - interpreted values (`true`, `false`, numerals): a class that holds two
//!   different values is a conflict;
//! - theory variables on nodes (`th_vars`), one per plug-in and class: when
//!   two classes that both carry a variable of plug-in T merge, the hub
//!   raises `new_eq` for T (design §4.1 events).
//!
//! Everything is undone by a trail, one scope per SAT decision level. Nodes
//! are never deleted: a node created inside a scope is detached when that
//! scope is popped and attached again at the lower level (its SAT variable,
//! like every minted variable, lives for the whole check).
//!
//! The reserved enode fields of the multi-engine design §3.3 (generation,
//! relevancy bit, MAM label sets, parent lists per (symbol, argument)) are
//! present and maintained; `reserved.rs` says what each holds.
//!
//! The enode mode is fixed per check (KC24): [`EnodeMode::Sparse`] is
//! implemented; [`EnodeMode::Full`] (every ground subterm of a relevant
//! assertion, for E-matching) is refused until the quantifier plug-in
//! exists.

mod explain;
mod merge;
mod reserved;
mod transitivity;

use std::collections::VecDeque;

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Sort, TermId};
use num_rational::BigRational;

pub(crate) use crate::engine::EnodeMode;
use crate::plugin::{GiveUp, ThId, ThVar};
pub(crate) use merge::{HubConflict, HubEvent};
use reserved::label_bit;
use transitivity::Transitivity;

/// Index of a node in the hub.
pub(crate) type NodeId = u32;

/// An interpreted value: two classes carrying different values never merge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum HubValue {
    /// `true` or `false`.
    Bool(bool),
    /// A numeral, compared exactly across Int and Real spellings.
    Num(BigRational),
}

/// Why a proof-forest edge `n -> target` holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Just {
    /// No edge: the node is the root of its proof tree.
    Root,
    /// An assigned literal, by the Boolean node it assigns (its term is the
    /// literal's): an equality atom (its arguments merged) or a Boolean node
    /// merged with `true`/`false`.
    Lit(NodeId, bool),
    /// `n` and `target` are congruent applications; for two equalities,
    /// `crossed` says their sides matched crosswise (`(= a b)` with
    /// `(= d c)`). Fixed when the congruence is found: explaining it later by
    /// the current classes could pick a pairing that only holds through
    /// newer merges, and a lazy reason must use only literals assigned before
    /// the literal it explains.
    Congruence { crossed: bool },
    /// The equality node merged with `true` because its arguments are equal.
    EqTrue(NodeId),
}

/// A parent entry: the application and the argument position at which a
/// member of this class occurs in it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Parent {
    node: NodeId,
    arg: u32,
}

#[derive(Debug)]
struct Node {
    term: TermId,
    /// Congruence function id; 0 for nodes outside the congruence table.
    func: u32,
    args: Box<[NodeId]>,
    /// An equality `(= a b)` with `args == [a, b]`.
    is_eq: bool,
    is_bool: bool,
    /// An argument of an application in the congruence table: a shared term
    /// in the sense of model-based combination (design §4.3).
    shared_arg: bool,
    /// Part of the congruence table and its arguments' parent lists.
    attached: bool,
    root: NodeId,
    /// Circular list of the class.
    next: NodeId,
    /// Class size (meaningful at a root).
    size: u32,
    /// At a root: the applications with an argument in the class, each with
    /// the argument position (one entry per position).
    parents: Vec<Parent>,
    /// Instantiation generation (reserved, §3.3): 0 for input terms.
    generation: u32,
    /// Relevant to the current assignment (KC21), set by the kernel.
    relevant: bool,
    /// At a root: approximate set of the class members' function ids.
    lbls: u64,
    /// At a root: approximate set of the class parents' function ids.
    plbls: u64,
    target: Option<NodeId>,
    just: Just,
    /// The node's own interpreted value. Valued nodes stay roots, so a class
    /// is valued iff its root is.
    value: Option<HubValue>,
    /// At a root: one theory variable per plug-in, with the member carrying it.
    th_vars: Vec<(ThId, ThVar, NodeId)>,
}

/// One undo step.
#[derive(Debug, Clone, Copy)]
enum Undo {
    /// `r1` was absorbed into `r2` through the edge `n1 -> n2`.
    Union {
        r1: NodeId,
        r2: NodeId,
        n1: NodeId,
        r2_parents: usize,
        r2_th_vars: usize,
        r2_lbls: u64,
        r2_plbls: u64,
    },
    /// The node became the table entry for its signature.
    TableInsert(NodeId),
    /// The node stopped being the table entry for its signature.
    TableRemove(NodeId),
    /// A parent was pushed on this root's parent list; its old `plbls`.
    ParentPush(NodeId, u64),
    /// The node became relevant.
    Relevant(NodeId),
    /// The node was created or attached.
    Attached(NodeId),
}

/// A merge waiting to be applied.
#[derive(Debug, Clone, Copy)]
struct Pending {
    a: NodeId,
    b: NodeId,
    just: Just,
}

/// The e-graph (see the module docs).
#[derive(Debug)]
pub(crate) struct Hub {
    nodes: Vec<Node>,
    by_term: HashMap<TermId, NodeId>,
    funcs: HashMap<(String, usize, Sort), u32>,
    table: HashMap<Box<[u32]>, NodeId>,
    sig_scratch: Vec<u32>,
    trail: Vec<Undo>,
    scopes: Vec<usize>,
    queue: VecDeque<Pending>,
    detached: Vec<NodeId>,
    true_node: NodeId,
    false_node: NodeId,
    events: Vec<HubEvent>,
    /// `(node, value node)`: a Boolean node joined a valued class.
    props: Vec<(NodeId, NodeId)>,
    conflict: Option<HubConflict>,
    /// Arithmetic-sorted shared arguments (candidates for combination).
    shared: Vec<NodeId>,
    mode: EnodeMode,
    /// Dynamic transitivity counters (`transitivity.rs`).
    dack: Transitivity,
    explain_epoch: u32,
    lca_epoch: u32,
    edge_mark: Vec<u32>,
    lca_mark: Vec<u32>,
    visit_epoch: u32,
    visit_mark: Vec<u32>,
    pub(crate) merges: u64,
}

impl Hub {
    /// A hub with the two Boolean value nodes, in enode mode `mode` (KC24).
    /// `Full` is refused: it needs lazy, relevancy-driven node creation for
    /// every ground subterm (KC23), which only the quantifier plug-in will
    /// use, and no such plug-in exists.
    pub(crate) fn new(
        true_term: TermId,
        false_term: TermId,
        mode: EnodeMode,
    ) -> Result<Self, GiveUp> {
        if mode == EnodeMode::Full {
            return Err(GiveUp::new(
                "hub enode mode Full is reserved for the quantifier plug-in (KC24)",
            ));
        }
        Ok(Self::sparse(true_term, false_term))
    }

    /// A Sparse hub (design H1): nodes only where the kernel asks for them.
    pub(crate) fn sparse(true_term: TermId, false_term: TermId) -> Self {
        let mut hub = Self {
            nodes: Vec::new(),
            by_term: HashMap::default(),
            funcs: HashMap::default(),
            table: HashMap::default(),
            sig_scratch: Vec::new(),
            trail: Vec::new(),
            scopes: Vec::new(),
            queue: VecDeque::new(),
            detached: Vec::new(),
            true_node: 0,
            false_node: 0,
            events: Vec::new(),
            props: Vec::new(),
            conflict: None,
            shared: Vec::new(),
            explain_epoch: 0,
            lca_epoch: 0,
            edge_mark: Vec::new(),
            lca_mark: Vec::new(),
            visit_epoch: 0,
            visit_mark: Vec::new(),
            mode: EnodeMode::Sparse,
            dack: Transitivity::default(),
            merges: 0,
        };
        hub.true_node = hub.push_node(true_term, 0, Box::new([]), false, true);
        hub.nodes[0].value = Some(HubValue::Bool(true));
        hub.false_node = hub.push_node(false_term, 0, Box::new([]), false, true);
        hub.nodes[1].value = Some(HubValue::Bool(false));
        hub
    }

    fn idx(n: NodeId) -> usize {
        n as usize
    }

    fn node(&self, n: NodeId) -> &Node {
        &self.nodes[Self::idx(n)]
    }

    fn node_mut(&mut self, n: NodeId) -> &mut Node {
        &mut self.nodes[Self::idx(n)]
    }

    /// The node of a term, if it has one.
    pub(crate) fn node_of(&self, term: TermId) -> Option<NodeId> {
        self.by_term.get(&term).copied()
    }

    /// The term of a node.
    pub(crate) fn term(&self, n: NodeId) -> TermId {
        self.node(n).term
    }

    /// The representative of a node's class.
    pub(crate) fn root(&self, n: NodeId) -> NodeId {
        self.node(n).root
    }

    /// The Boolean value a node carries itself (`true` / `false` nodes).
    pub(crate) fn bool_value(&self, n: NodeId) -> Option<bool> {
        match self.node(n).value {
            Some(HubValue::Bool(b)) => Some(b),
            _ => None,
        }
    }

    /// The arguments of an equality node.
    pub(crate) fn eq_args(&self, n: NodeId) -> Option<(NodeId, NodeId)> {
        let node = self.node(n);
        node.is_eq.then(|| (node.args[0], node.args[1]))
    }

    /// Arithmetic-sorted arguments of applications (combination candidates).
    pub(crate) fn shared_nodes(&self) -> &[NodeId] {
        &self.shared
    }

    /// Number of nodes.
    pub(crate) fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether merges, or their output (events, propagations, a conflict),
    /// are waiting for the next closure.
    pub(crate) fn has_pending(&self) -> bool {
        !self.queue.is_empty()
            || !self.events.is_empty()
            || !self.props.is_empty()
            || self.conflict.is_some()
    }

    fn push_node(
        &mut self,
        term: TermId,
        func: u32,
        args: Box<[NodeId]>,
        is_eq: bool,
        is_bool: bool,
    ) -> NodeId {
        let id = NodeId::try_from(self.nodes.len()).unwrap_or(NodeId::MAX);
        self.nodes.push(Node {
            term,
            func,
            args,
            is_eq,
            is_bool,
            shared_arg: false,
            attached: false,
            root: id,
            next: id,
            size: 1,
            parents: Vec::new(),
            generation: 0,
            relevant: false,
            lbls: label_bit(func),
            plbls: 0,
            target: None,
            just: Just::Root,
            value: None,
            th_vars: Vec::new(),
        });
        self.edge_mark.push(0);
        self.lca_mark.push(0);
        self.visit_mark.push(0);
        self.by_term.insert(term, id);
        id
    }

    /// The congruence id of a function symbol of a given arity and result
    /// sort (an overloaded name is two functions).
    pub(crate) fn func_id(&mut self, name: &str, arity: usize, sort: &Sort) -> u32 {
        let next = u32::try_from(self.funcs.len() + 1).unwrap_or(u32::MAX);
        *self
            .funcs
            .entry((name.to_string(), arity, sort.clone()))
            .or_insert(next)
    }

    /// Add a leaf (a variable, a numeral, an opaque theory term). Returns the
    /// existing node when the term has one.
    pub(crate) fn add_leaf(
        &mut self,
        term: TermId,
        is_bool: bool,
        value: Option<HubValue>,
    ) -> NodeId {
        if let Some(n) = self.node_of(term) {
            return n;
        }
        let n = self.push_node(term, 0, Box::new([]), false, is_bool);
        self.node_mut(n).value = value;
        self.attach(n);
        n
    }

    /// Add an uninterpreted application over existing argument nodes.
    pub(crate) fn add_app(
        &mut self,
        term: TermId,
        func: u32,
        args: Vec<NodeId>,
        is_bool: bool,
    ) -> NodeId {
        if let Some(n) = self.node_of(term) {
            return n;
        }
        let n = self.push_node(term, func, args.into_boxed_slice(), false, is_bool);
        self.attach(n);
        n
    }

    /// Add an equality node `(= a b)` over existing nodes.
    pub(crate) fn add_eq(&mut self, term: TermId, a: NodeId, b: NodeId) -> NodeId {
        if let Some(n) = self.node_of(term) {
            return n;
        }
        // Equalities are congruent like applications, up to the order of
        // their sides: `a ~ c ∧ b ~ d` puts `(= a b)` and `(= c d)` (or
        // `(= d c)`) in one class, so a false equality falsifies every
        // equality between the same two classes (disequality propagation).
        let func = self.func_id("=", 2, &Sort::Bool);
        let n = self.push_node(term, func, Box::new([a, b]), true, true);
        self.attach(n);
        n
    }

    /// Mark a node as a shared argument; arithmetic ones become combination
    /// candidates.
    pub(crate) fn mark_shared(&mut self, n: NodeId, arithmetic: bool) {
        let node = self.node_mut(n);
        if node.shared_arg {
            return;
        }
        node.shared_arg = true;
        if arithmetic {
            self.shared.push(n);
        }
    }

    /// Attach plug-in `th`'s variable `v` to node `n`. Called right after the
    /// node is created, while it is still a singleton root, so the entry is
    /// the node's own and survives every pop.
    pub(crate) fn attach_var(&mut self, n: NodeId, th: ThId, v: ThVar) {
        debug_assert_eq!(self.root(n), n, "attach_var on a merged node");
        if self.node(n).th_vars.iter().any(|&(t, _, _)| t == th) {
            return;
        }
        self.node_mut(n).th_vars.push((th, v, n));
    }

    /// Enter a node into the congruence table and its arguments' parent
    /// lists (at creation, or again after the scope that created it popped).
    fn attach(&mut self, n: NodeId) {
        self.node_mut(n).attached = true;
        self.record(Undo::Attached(n));
        let args = self.node(n).args.clone();
        let label = label_bit(self.node(n).func);
        for (i, &a) in args.iter().enumerate() {
            let r = self.root(a);
            let arg = u32::try_from(i).unwrap_or(u32::MAX);
            let old = self.node(r).plbls;
            let root = self.node_mut(r);
            root.parents.push(Parent { node: n, arg });
            root.plbls |= label;
            self.record(Undo::ParentPush(r, old));
        }
        if self.node(n).func != 0 {
            self.insert_or_merge(n);
        }
        if let Some((a, b)) = self.eq_args(n) {
            if self.root(a) == self.root(b) {
                let t = self.true_node;
                self.queue.push_back(Pending {
                    a: n,
                    b: t,
                    just: Just::EqTrue(n),
                });
            }
        }
    }

    fn record(&mut self, undo: Undo) {
        if !self.scopes.is_empty() {
            self.trail.push(undo);
        }
    }
}

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_random;
