// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! AC circuit reuse for bit-vector addition, multiplication, AND and OR.
//! Reference: Z3 5.3.3 src/ast/rewriter/maximize_ac_sharing.cpp.
//! Shared subcircuits are region boundaries; an unshared AC region is flattened
//! once, existing binary circuits are reused, and remaining leaves are balanced.

use super::{Symbol, TermData, TermId, TermStore};
use crate::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use crate::Sort;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Op {
    Add,
    Mul,
    And,
    Or,
}
impl Op {
    fn name(self) -> &'static str {
        match self {
            Self::Add => "bvadd",
            Self::Mul => "bvmul",
            Self::And => "bvand",
            Self::Or => "bvor",
        }
    }
}
type Circuit = (Op, u32, TermId, TermId);

fn operation(terms: &TermStore, term: TermId) -> Option<(Op, u32)> {
    let Sort::BitVec(bits) = terms.sort(term) else {
        return None;
    };
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    if terms.is_declared_function(name)
        || args.len() < 2
        || args.iter().any(|arg| terms.sort(*arg) != terms.sort(term))
    {
        return None;
    }
    let op = match name.as_str() {
        "bvadd" => Op::Add,
        "bvmul" => Op::Mul,
        "bvand" => Op::And,
        "bvor" => Op::Or,
        _ => return None,
    };
    Some((op, bits.width))
}

fn key(op: Op, width: u32, a: TermId, b: TermId) -> Circuit {
    if a <= b {
        (op, width, a, b)
    } else {
        (op, width, b, a)
    }
}

fn graph(
    terms: &TermStore,
    roots: &[TermId],
) -> (Vec<TermId>, HashMap<TermId, usize>, HashSet<TermId>) {
    let mut order = Vec::new();
    let mut uses = HashMap::default();
    let mut boundary: HashSet<_> = roots.iter().copied().collect();
    let mut seen = HashSet::default();
    let mut operations = HashMap::default();
    let mut pending = Vec::new();
    for root in roots.iter().rev() {
        *uses.entry(*root).or_insert(0) += 1;
        pending.push((*root, false));
    }
    while let Some((term, finish)) = pending.pop() {
        if finish {
            order.push(term);
            continue;
        }
        if !seen.insert(term) {
            continue;
        }
        pending.push((term, true));
        let parent_op = *operations
            .entry(term)
            .or_insert_with(|| operation(terms, term));
        for child in terms.children(term).into_iter().rev() {
            *uses.entry(child).or_insert(0) += 1;
            let child_op = *operations
                .entry(child)
                .or_insert_with(|| operation(terms, child));
            if parent_op != child_op {
                boundary.insert(child);
            }
            pending.push((child, false));
        }
    }
    (order, uses, boundary)
}

fn rebuild(terms: &mut TermStore, term: TermId, memo: &HashMap<TermId, TermId>) -> TermId {
    let map = |id: TermId| memo.get(&id).copied().unwrap_or(id);
    let data = match terms.get(term).clone() {
        TermData::App(op, args) => TermData::App(op, args.into_iter().map(map).collect()),
        TermData::Not(inner) => TermData::Not(map(inner)),
        TermData::Ite(c, t, e) => TermData::Ite(map(c), map(t), map(e)),
        TermData::Let(bindings, body) => TermData::Let(
            bindings
                .into_iter()
                .map(|(name, value)| (name, map(value)))
                .collect(),
            map(body),
        ),
        TermData::Forall(vars, body, triggers) => TermData::Forall(vars, map(body), triggers),
        TermData::Exists(vars, body, triggers) => TermData::Exists(vars, map(body), triggers),
        _ => return term,
    };
    let result = terms.intern(data, terms.sort(term).clone());
    if result != term && terms.is_quantifier(term) {
        terms.copy_quantifier_metadata(term, result);
    }
    result
}

#[derive(Default)]
struct Circuits {
    known: HashMap<Circuit, TermId>,
    shared: HashSet<TermId>,
}

impl Circuits {
    fn binary(
        &mut self,
        terms: &mut TermStore,
        op: Op,
        width: u32,
        a: TermId,
        b: TermId,
    ) -> TermId {
        let k = key(op, width, a, b);
        if let Some(result) = self.known.get(&k) {
            return *result;
        }
        let result = terms.mk_app(Symbol::named(op.name()), [k.2, k.3], Sort::bitvec(width));
        self.known.insert(k, result);
        result
    }

    fn region(&mut self, terms: &mut TermStore, term: TermId, op: Op, width: u32) -> TermId {
        let mut pending = terms.children(term);
        pending.reverse();
        let mut args = Vec::new();
        while let Some(child) = pending.pop() {
            if !self.shared.contains(&child) && operation(terms, child) == Some((op, width)) {
                pending.extend(terms.children(child).into_iter().rev());
            } else {
                args.push(child);
            }
        }
        // Z3 uses the same bounded pair search. Above this size balancing is
        // still equivalent, without a quadratic reuse search over wide sums.
        if args.len() < 128 {
            while let Some((i, j, reused)) = self.reusable_pair(op, width, &args) {
                args[i] = reused;
                let _ = args.remove(j);
            }
        }
        while args.len() > 1 {
            let mut next = Vec::with_capacity(args.len().div_ceil(2));
            for pair in args.chunks(2) {
                match pair {
                    [a, b] => next.push(self.binary(terms, op, width, *a, *b)),
                    [a] => next.push(*a),
                    _ => {}
                }
            }
            args = next;
        }
        args.first().copied().unwrap_or(term)
    }

    fn reusable_pair(&self, op: Op, width: u32, args: &[TermId]) -> Option<(usize, usize, TermId)> {
        for (i, a) in args.iter().enumerate() {
            for (j, b) in args.iter().enumerate().skip(i + 1) {
                if let Some(result) = self.known.get(&key(op, width, *a, *b)) {
                    return Some((i, j, *result));
                }
            }
        }
        None
    }
}

impl TermStore {
    /// Reassociate builtin BV addition, multiplication, AND and OR to reuse circuits.
    /// The result is equivalent, with identical variables and no model converter.
    /// Reuse state belongs to this call, so assertion scopes cannot leak.
    pub fn maximize_bv_sharing(&mut self, roots: &mut [TermId]) -> bool {
        let (order, uses, boundary) = graph(self, roots);
        let mut memo = HashMap::default();
        let mut circuits = Circuits::default();
        for original in order {
            let mut rewritten = rebuild(self, original, &memo);
            if let Some((op, width)) = operation(self, rewritten) {
                if let TermData::App(_, args) = self.get(rewritten) {
                    if let [a, b] = args.as_slice() {
                        circuits
                            .known
                            .entry(key(op, width, *a, *b))
                            .or_insert(rewritten);
                    }
                }
                if boundary.contains(&original) || uses.get(&original).copied().unwrap_or(0) > 1 {
                    rewritten = circuits.region(self, rewritten, op, width);
                }
            }
            if uses.get(&original).copied().unwrap_or(0) > 1 {
                circuits.shared.insert(rewritten);
            }
            memo.insert(original, rewritten);
        }
        let mut changed = false;
        for root in roots {
            if let Some(rewritten) = memo.get(root) {
                changed |= *root != *rewritten;
                *root = *rewritten;
            }
        }
        changed
    }
}

#[cfg(test)]
mod tests;
