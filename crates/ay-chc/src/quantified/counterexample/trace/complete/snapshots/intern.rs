// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact private syntax keys, not public or extensional array equality.

use super::*;
use ay_model_check::SnapshotNode;

enum Kind {
    Finite(String),
    Store(usize, String, String),
    Range(usize, usize, u64, u64, u64),
}

struct Key {
    sort: String,
    kind: Kind,
}

impl Key {
    fn same_syntax(&self, other: &Self) -> bool {
        if self.sort != other.sort {
            return false;
        }
        match (&self.kind, &other.kind) {
            (Kind::Finite(left), Kind::Finite(right)) => left == right,
            (Kind::Store(a, i, v), Kind::Store(b, j, w)) => a == b && i == j && v == w,
            (Kind::Range(d, s, l, h, o), Kind::Range(e, t, m, k, p)) => {
                d == e && s == t && l == m && h == k && o == p
            }
            _ => false,
        }
    }

    fn bytes(&self) -> Option<usize> {
        let bytes = match &self.kind {
            Kind::Finite(body) => body.len(),
            Kind::Store(_, index, value) => index.len().checked_add(value.len())?,
            Kind::Range(..) => 64,
        };
        self.sort.len().checked_add(bytes)?.checked_add(64)
    }
}

pub(in crate::quantified::counterexample::trace::complete) struct Definition {
    key: Key,
    pub(in crate::quantified::counterexample::trace::complete) name: String,
    pub(in crate::quantified::counterexample::trace::complete) body: String,
}

pub(in crate::quantified::counterexample::trace::complete) struct Environment {
    pub(in crate::quantified::counterexample::trace::complete) definitions: Vec<Definition>,
    pub(in crate::quantified::counterexample::trace::complete) bindings: Vec<Option<usize>>,
    names: Vec<String>,
}

impl Environment {
    pub(in crate::quantified::counterexample::trace::complete) fn new(
        names: Vec<String>,
        count: usize,
        control: &SourceControl<'_>,
    ) -> Option<Self> {
        control.bytes(count.checked_mul(std::mem::size_of::<Definition>())?)?;
        let mut definitions = Vec::new();
        definitions.try_reserve_exact(count).ok()?;
        Some(Self {
            definitions,
            bindings: Vec::new(),
            names,
        })
    }

    pub(in crate::quantified::counterexample::trace::complete) fn name(
        &self,
        index: usize,
    ) -> Option<&str> {
        Some(&self.definitions.get(index)?.name)
    }

    pub(in crate::quantified::counterexample::trace::complete) fn import(
        &mut self,
        topology: &SnapshotTopology<'_>,
        control: &SourceControl<'_>,
    ) -> Option<usize> {
        let nodes = topology.nodes();
        control.bytes(nodes.len().checked_mul(std::mem::size_of::<usize>())?)?;
        let mut local = Vec::new();
        local.try_reserve_exact(nodes.len()).ok()?;
        // Process EVERY node before selecting the root; no unreachable/empty
        // capture is allowed to escape typed admission through root selection.
        for node in nodes {
            let key = key(*node, &local, control)?;
            local.push(self.intern(key, control)?);
        }
        control.poll()?;
        local.get(topology.root()).copied()
    }

    fn intern(&mut self, key: Key, control: &SourceControl<'_>) -> Option<usize> {
        for (index, prior) in self.definitions.iter().enumerate() {
            // Prepay complete byte comparisons; this linear memo introduces
            // no unchecked hash/semantic-equality or source-provenance claim.
            control.debit(key.bytes()?.checked_add(prior.key.bytes()?)?, 0)?;
            if prior.key.same_syntax(&key) {
                return Some(index);
            }
        }
        let index = self.definitions.len();
        if index >= MAX_NODES {
            control.stop();
            return None;
        }
        let name = self.names.get(index.checked_mul(2)?)?;
        let binder = self.names.get(index.checked_mul(2)?.checked_add(1)?)?;
        let body = self.body(&key, binder, control)?;
        control.bytes(name.len())?;
        self.definitions.push(Definition {
            key,
            name: name.clone(),
            body,
        });
        Some(index)
    }

    fn body(&self, key: &Key, binder: &str, control: &SourceControl<'_>) -> Option<String> {
        let mut body = String::new();
        match &key.kind {
            Kind::Finite(value) => literal::append(&mut body, value, control)?,
            Kind::Store(base, index, value) => {
                for piece in ["(store ", self.name(*base)?, " ", index, " ", value, ")"] {
                    literal::append(&mut body, piece, control)?;
                }
            }
            Kind::Range(destination, source, lo, hi, source_lo) => {
                control.debit(512, 1024)?;
                let destination = self.name(*destination)?;
                let source = self.name(*source)?;
                let value = format!("(lambda (({binder} (_ BitVec 64))) (ite (and (bvule (_ bv{lo} 64) {binder}) (bvult {binder} (_ bv{hi} 64))) (select {source} (bvadd (bvsub {binder} (_ bv{lo} 64)) (_ bv{source_lo} 64))) (select {destination} {binder})))");
                literal::append(&mut body, &value, control)?;
            }
        }
        Some(body)
    }
}

fn key(node: SnapshotNode<'_>, prior: &[usize], control: &SourceControl<'_>) -> Option<Key> {
    control.charge(1)?;
    let sort = literal::sort(node.sort, control)?;
    let get = |index| prior.get(index).copied();
    let kind = match node.kind {
        SnapshotKind::Finite(value) => Kind::Finite(literal::finite(value, node.sort, control)?),
        SnapshotKind::Store { base, index, value } => {
            let ay_core::Sort::Array(array) = node.sort else {
                return None;
            };
            Kind::Store(
                get(base)?,
                scalar(index, &array.index_sort, control)?,
                scalar(value, &array.element_sort, control)?,
            )
        }
        SnapshotKind::Range {
            destination,
            source,
            lo,
            hi,
            source_lo,
        } => Kind::Range(
            get(destination)?,
            get(source)?,
            unsigned(lo, control)?,
            unsigned(hi, control)?,
            unsigned(source_lo, control)?,
        ),
        _ => return None,
    };
    Some(Key { sort, kind })
}
