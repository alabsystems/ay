// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Assignments, merges and their undo (design H1): congruence closure with
//! a trail, the proof forest, values and theory-variable events.

use super::{Hub, HubValue, Just, NodeId, Parent, Pending, Undo};
use crate::plugin::{ThId, ThVar};

/// A theory event raised by a merge or a disequality (design §4.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum HubEvent {
    /// Classes carrying `a` and `b` of plug-in `th` merged; `na`, `nb` are
    /// the members carrying them (the explanation's endpoints).
    NewEq {
        th: ThId,
        a: ThVar,
        b: ThVar,
        na: NodeId,
        nb: NodeId,
    },
    /// An equality between classes carrying `a` and `b` (on members `na`,
    /// `nb`) became false.
    NewDiseq {
        th: ThId,
        a: ThVar,
        b: ThVar,
        eq: NodeId,
        na: NodeId,
        nb: NodeId,
    },
}

/// Two nodes holding different values ended in one class.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct HubConflict {
    pub(crate) a: NodeId,
    pub(crate) b: NodeId,
}

impl Hub {
    /// An assigned literal on a Boolean node: a true equality merges its
    /// arguments; every Boolean node joins `true` or `false`.
    pub(crate) fn assign(&mut self, n: NodeId, value: bool) {
        let just = Just::Lit(n, value);
        if value {
            if let Some((a, b)) = self.eq_args(n) {
                self.queue.push_back(Pending { a, b, just });
            }
        } else if let Some((a, b)) = self.eq_args(n) {
            self.diseq_events(n, a, b);
        }
        let target = if value {
            self.true_node
        } else {
            self.false_node
        };
        self.queue.push_back(Pending {
            a: n,
            b: target,
            just,
        });
    }

    fn diseq_events(&mut self, eq: NodeId, a: NodeId, b: NodeId) {
        let (ra, rb) = (self.root(a), self.root(b));
        let vars_a = self.node(ra).th_vars.clone();
        let vars_b = self.node(rb).th_vars.clone();
        for &(th, va, na) in &vars_a {
            if let Some(&(_, vb, nb)) = vars_b.iter().find(|&&(t, _, _)| t == th) {
                self.events.push(HubEvent::NewDiseq {
                    th,
                    a: va,
                    b: vb,
                    eq,
                    na,
                    nb,
                });
            }
        }
    }

    /// Apply queued merges until the queue is empty or a class holds two
    /// different values.
    pub(crate) fn propagate(&mut self) {
        while self.conflict.is_none() {
            let Some(p) = self.queue.pop_front() else {
                break;
            };
            self.merge(p.a, p.b, p.just);
        }
    }

    /// Take the events, propagations and conflict produced so far.
    pub(crate) fn take_events(&mut self) -> Vec<HubEvent> {
        std::mem::take(&mut self.events)
    }

    pub(crate) fn take_props(&mut self) -> Vec<(NodeId, NodeId)> {
        std::mem::take(&mut self.props)
    }

    pub(crate) fn take_conflict(&mut self) -> Option<HubConflict> {
        self.conflict.take()
    }

    fn valued(&self, r: NodeId) -> bool {
        self.node(r).value.is_some()
    }

    fn merge(&mut self, a: NodeId, b: NodeId, just: Just) {
        let (mut r1, mut r2) = (self.root(a), self.root(b));
        if r1 == r2 {
            return;
        }
        let (mut n1, mut n2) = (a, b);
        // r1 is absorbed into r2: a valued root survives, else the larger one.
        let swap = match (self.valued(r1), self.valued(r2)) {
            (true, false) => true,
            (false, true) => false,
            _ => self.node(r1).size > self.node(r2).size,
        };
        if swap {
            std::mem::swap(&mut r1, &mut r2);
            std::mem::swap(&mut n1, &mut n2);
        }
        self.merges += 1;
        let parents = self.node(r1).parents.clone();
        for p in &parents {
            if self.node(p.node).func != 0 && self.node(p.node).attached {
                self.remove_if_entry(p.node);
            }
        }
        self.merge_justification(n1, n2, just);
        let r2_parents = self.node(r2).parents.len();
        let r2_th_vars = self.node(r2).th_vars.len();
        let (r2_lbls, r2_plbls) = (self.node(r2).lbls, self.node(r2).plbls);
        self.record(Undo::Union {
            r1,
            r2,
            n1,
            r2_parents,
            r2_th_vars,
            r2_lbls,
            r2_plbls,
        });
        let (lbls, plbls) = (self.node(r1).lbls, self.node(r1).plbls);
        let root = self.node_mut(r2);
        root.lbls |= lbls;
        root.plbls |= plbls;
        self.union_classes(r1, r2);
        self.merge_th_vars(r1, r2);
        self.reinsert_parents(&parents, r2);
        // Values: a clash is a conflict (a Boolean value reached r1's members
        // in `union_classes`).
        if let (Some(v1), Some(v2)) = (&self.node(r1).value, &self.node(r2).value) {
            if v1 != v2 {
                self.conflict = Some(HubConflict { a: r1, b: r2 });
            }
        }
    }

    /// Point r1's members at r2 and splice the class lists. A member of
    /// Boolean sort joining a `true`/`false` class is a propagation.
    fn union_classes(&mut self, r1: NodeId, r2: NodeId) {
        let bool_value = !self.valued(r1) && matches!(self.node(r2).value, Some(HubValue::Bool(_)));
        let mut c = r1;
        loop {
            self.node_mut(c).root = r2;
            if bool_value && self.node(c).is_bool {
                self.props.push((c, r2));
            }
            c = self.node(c).next;
            if c == r1 {
                break;
            }
        }
        let (next1, next2) = (self.node(r1).next, self.node(r2).next);
        self.node_mut(r1).next = next2;
        self.node_mut(r2).next = next1;
        let size1 = self.node(r1).size;
        self.node_mut(r2).size += size1;
    }

    /// One theory variable per plug-in and class: a second one is `new_eq`.
    fn merge_th_vars(&mut self, r1: NodeId, r2: NodeId) {
        let vars1 = self.node(r1).th_vars.clone();
        for (th, v, m) in vars1 {
            let existing = self
                .node(r2)
                .th_vars
                .iter()
                .find(|&&(t, _, _)| t == th)
                .copied();
            match existing {
                Some((_, w, mw)) => self.events.push(HubEvent::NewEq {
                    th,
                    a: w,
                    b: v,
                    na: mw,
                    nb: m,
                }),
                None => self.node_mut(r2).th_vars.push((th, v, m)),
            }
        }
    }

    /// The signatures of r1's parents changed: re-enter them in the table,
    /// finding congruences, and hand them to r2.
    fn reinsert_parents(&mut self, parents: &[Parent], r2: NodeId) {
        self.visit_epoch = self.visit_epoch.wrapping_add(1).max(1);
        for &entry in parents {
            let p = entry.node;
            if !self.node(p).attached {
                continue;
            }
            // Every (parent, position) entry moves to r2; each parent's
            // signature is re-entered once.
            self.node_mut(r2).parents.push(entry);
            if self.visit_mark[Self::idx(p)] == self.visit_epoch {
                continue;
            }
            self.visit_mark[Self::idx(p)] = self.visit_epoch;
            if let Some((x, y)) = self.eq_args(p) {
                if self.root(x) == self.root(y) {
                    let t = self.true_node;
                    self.queue.push_back(Pending {
                        a: p,
                        b: t,
                        just: Just::EqTrue(p),
                    });
                }
            }
            if self.node(p).func != 0 {
                self.insert_or_merge(p);
            }
        }
    }

    /// Re-root `n`'s proof tree at `n`.
    fn reverse_justification(&mut self, n: NodeId) {
        let mut prev = n;
        let mut curr = self.node_mut(n).target.take();
        let mut js = std::mem::replace(&mut self.node_mut(n).just, Just::Root);
        while let Some(c) = curr {
            let next = self.node(c).target;
            let next_js = self.node(c).just;
            let node = self.node_mut(c);
            node.target = Some(prev);
            node.just = js;
            prev = c;
            js = next_js;
            curr = next;
        }
    }

    fn merge_justification(&mut self, n1: NodeId, n2: NodeId, just: Just) {
        self.reverse_justification(n1);
        let node = self.node_mut(n1);
        node.target = Some(n2);
        node.just = just;
    }

    /// Open a scope (one per SAT decision level).
    pub(crate) fn push_scope(&mut self) {
        self.scopes.push(self.trail.len());
    }

    /// Close `n` scopes: undo every merge, table and parent-list change made
    /// in them, then attach again the nodes created in them.
    pub(crate) fn pop_scopes(&mut self, n: usize) {
        if n == 0 {
            return;
        }
        let keep = self.scopes.len().saturating_sub(n);
        let Some(&mark) = self.scopes.get(keep) else {
            return;
        };
        self.scopes.truncate(keep);
        while self.trail.len() > mark {
            let Some(undo) = self.trail.pop() else {
                break;
            };
            self.undo(undo);
        }
        self.queue.clear();
        self.events.clear();
        self.props.clear();
        self.conflict = None;
        let mut detached = std::mem::take(&mut self.detached);
        detached.reverse();
        for n in detached {
            self.attach(n);
        }
        // Congruences and `EqTrue` merges the re-attachment found hold at
        // this level: apply them now, or a deeper scope would own them and
        // lose them on its pop. Their output waits for the next closure.
        self.propagate();
    }

    fn undo(&mut self, undo: Undo) {
        match undo {
            Undo::Union {
                r1,
                r2,
                n1,
                r2_parents,
                r2_th_vars,
                r2_lbls,
                r2_plbls,
            } => {
                let root = self.node_mut(r2);
                root.parents.truncate(r2_parents);
                root.th_vars.truncate(r2_th_vars);
                root.lbls = r2_lbls;
                root.plbls = r2_plbls;
                let size1 = self.node(r1).size;
                self.node_mut(r2).size -= size1;
                let (next1, next2) = (self.node(r1).next, self.node(r2).next);
                self.node_mut(r1).next = next2;
                self.node_mut(r2).next = next1;
                let mut c = r1;
                loop {
                    self.node_mut(c).root = r1;
                    c = self.node(c).next;
                    if c == r1 {
                        break;
                    }
                }
                let node = self.node_mut(n1);
                node.target = None;
                node.just = Just::Root;
                self.reverse_justification(r1);
            }
            Undo::TableInsert(n) => {
                self.signature(n);
                self.table.remove(self.sig_scratch.as_slice());
            }
            Undo::TableRemove(n) => {
                self.signature(n);
                let key: Box<[u32]> = self.sig_scratch.as_slice().into();
                self.table.insert(key, n);
            }
            Undo::ParentPush(r, plbls) => {
                let root = self.node_mut(r);
                root.parents.pop();
                root.plbls = plbls;
            }
            Undo::Relevant(n) => {
                self.node_mut(n).relevant = false;
            }
            Undo::Attached(n) => {
                self.node_mut(n).attached = false;
                self.detached.push(n);
            }
        }
    }

    /// The signature of an application under the current roots.
    pub(super) fn signature(&mut self, n: NodeId) {
        self.sig_scratch.clear();
        let node = &self.nodes[Self::idx(n)];
        self.sig_scratch.push(node.func);
        for &a in node.args.iter() {
            self.sig_scratch.push(self.nodes[Self::idx(a)].root);
        }
        if node.is_eq {
            // `=` is commutative: its two side classes, ordered.
            if let (Some(&x), Some(&y)) = (self.sig_scratch.get(1), self.sig_scratch.get(2)) {
                if x > y {
                    self.sig_scratch.swap(1, 2);
                }
            }
        }
    }

    /// Whether two congruent equalities match their sides crosswise now.
    fn crossed(&self, n: NodeId, q: NodeId) -> bool {
        let (xs, ys) = (&self.node(n).args, &self.node(q).args);
        self.node(n).is_eq
            && match (xs.first(), ys.first()) {
                (Some(&x), Some(&y)) => self.root(x) != self.root(y),
                _ => false,
            }
    }

    /// Put `n` in the table, or queue its congruence with the entry there.
    pub(super) fn insert_or_merge(&mut self, n: NodeId) {
        self.signature(n);
        match self.table.get(self.sig_scratch.as_slice()).copied() {
            Some(q) if q == n => {}
            Some(q) => {
                let crossed = self.crossed(n, q);
                self.queue.push_back(Pending {
                    a: n,
                    b: q,
                    just: Just::Congruence { crossed },
                });
            }
            None => {
                let key: Box<[u32]> = self.sig_scratch.as_slice().into();
                self.table.insert(key, n);
                self.record(Undo::TableInsert(n));
            }
        }
    }

    /// Remove `n` from the table if it is the entry for its signature.
    pub(super) fn remove_if_entry(&mut self, n: NodeId) {
        self.signature(n);
        if self.table.get(self.sig_scratch.as_slice()) == Some(&n) {
            self.table.remove(self.sig_scratch.as_slice());
            self.record(Undo::TableRemove(n));
        }
    }
}
