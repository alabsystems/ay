// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The two compaction analyses: O1 (asserted constant aliasing, schema 8) and
//! O2 (guarded selectors, Lemma 4). Both are purely syntactic passes over the
//! exact assertion roots.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::TermId;

use super::scan::{FieldSort, Node, Scan, SelKind, SortShape};

/// Visit budget of the guard analysis; on overflow every selector keeps the
/// general (unguarded) encoding, which is always sound.
const MAX_GUARD_VISITS: usize = 4_000_000;

/// O1: union-find over asserted top-level equalities between two declared
/// datatype constants. Returns `constant -> representative` for every
/// constant that is not its own representative.
pub(super) fn alias_map(scan: &Scan) -> HashMap<TermId, TermId> {
    let mut parent: HashMap<TermId, TermId> = HashMap::default();
    fn find(parent: &HashMap<TermId, TermId>, mut x: TermId) -> TermId {
        while let Some(&p) = parent.get(&x) {
            if p == x {
                break;
            }
            x = p;
        }
        x
    }
    let mut stack: Vec<TermId> = scan.roots.clone();
    let mut seen: HashSet<TermId> = HashSet::default();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match scan.node(t) {
            Some(Node::And(args)) => stack.extend(args.iter().copied()),
            Some(Node::Eq(args)) if args.len() == 2 => {
                let (a, b) = (args[0], args[1]);
                let consts = matches!(scan.node(a), Some(Node::Const))
                    && matches!(scan.node(b), Some(Node::Const));
                let dt = matches!(scan.sort_of(a), Some(FieldSort::Dt(_)));
                if consts && dt {
                    let (ra, rb) = (find(&parent, a), find(&parent, b));
                    if ra != rb {
                        let (lo, hi) = if ra.0 < rb.0 { (ra, rb) } else { (rb, ra) };
                        parent.insert(hi, lo);
                    }
                }
            }
            _ => {}
        }
    }
    let keys: Vec<TermId> = parent.keys().copied().collect();
    keys.into_iter()
        .map(|k| (k, find(&parent, k)))
        .filter(|(k, r)| k != r)
        .collect()
}

/// The arguments `x` of every `((_ is cons) x)` — or `(not ((_ is nil) x))`,
/// equivalent for a two-constructor list sort — that is a top-level conjunct
/// of `t` (through nested `and` only).
fn cons_guards(scan: &Scan, t: TermId, memo: &mut HashMap<TermId, Vec<TermId>>) -> Vec<TermId> {
    if let Some(g) = memo.get(&t) {
        return g.clone();
    }
    let mut out: Vec<TermId> = Vec::new();
    let mut stack = vec![t];
    let mut seen: HashSet<TermId> = HashSet::default();
    while let Some(u) = stack.pop() {
        if !seen.insert(u) {
            continue;
        }
        match scan.node(u) {
            Some(Node::And(args)) => stack.extend(args.iter().copied()),
            Some(Node::Tester { ctor, arg }) => {
                if is_cons_ctor(scan, *arg, *ctor) == Some(true) {
                    out.push(*arg);
                }
            }
            Some(Node::Not(inner)) => {
                if let Some(Node::Tester { ctor, arg }) = scan.node(*inner) {
                    if is_cons_ctor(scan, *arg, *ctor) == Some(false) {
                        out.push(*arg);
                    }
                }
            }
            _ => {}
        }
    }
    out.sort_unstable();
    out.dedup();
    memo.insert(t, out.clone());
    out
}

/// For a tester on a list sort: whether it tests the cons (`None` when the
/// argument is not list-sorted).
fn is_cons_ctor(scan: &Scan, arg: TermId, ctor: usize) -> Option<bool> {
    match scan.sort_of(arg) {
        Some(FieldSort::Dt(s)) => match scan.sorts[s as usize].shape {
            SortShape::List { cons_idx, .. } => Some(cons_idx == ctor),
            _ => None,
        },
        _ => None,
    }
}

/// The guards `cons_guards` of `t`'s negation when `t` is `(not G)`.
fn negated_guards(scan: &Scan, t: TermId, memo: &mut HashMap<TermId, Vec<TermId>>) -> Vec<TermId> {
    match scan.node(t) {
        Some(Node::Not(inner)) => cons_guards(scan, *inner, memo),
        _ => Vec::new(),
    }
}

/// For each argument, the union of the other arguments' guard sets.
fn sibling_extras(per: &[Vec<TermId>]) -> Vec<Vec<TermId>> {
    let mut count: HashMap<TermId, u32> = HashMap::default();
    for p in per {
        for &x in p {
            *count.entry(x).or_insert(0) += 1;
        }
    }
    per.iter()
        .map(|own| {
            count
                .iter()
                .filter(|(x, n)| **n > u32::from(own.contains(x)))
                .map(|(x, _)| *x)
                .collect()
        })
        .collect()
}

/// Interning of guard sets (sorted vectors of guarded list terms).
#[derive(Default)]
struct GuardSets {
    sets: Vec<Vec<TermId>>,
    ids: HashMap<Vec<TermId>, u32>,
}

impl GuardSets {
    fn intern(&mut self, mut set: Vec<TermId>) -> u32 {
        set.sort_unstable();
        set.dedup();
        if let Some(&id) = self.ids.get(&set) {
            return id;
        }
        let id = self.sets.len() as u32;
        self.sets.push(set.clone());
        self.ids.insert(set, id);
        id
    }

    fn extend(&mut self, g: u32, extra: &[TermId]) -> u32 {
        if extra.is_empty() {
            return g;
        }
        let mut set = self.sets[g as usize].clone();
        set.extend_from_slice(extra);
        self.intern(set)
    }
}

/// O2 (Lemma 4): the list selector applications EVERY occurrence of which
/// lies under its own cons tester — in the then-branch of an `ite` whose
/// condition has `((_ is cons) x)` as a top-level conjunct, in an `and`
/// argument a sibling of which has it, in an `or` argument a sibling of which
/// is the negation of such a formula, or in the conclusion of an implication
/// a premise of which has it. Any unguarded path disqualifies.
/// Also returns the list selector applications that stay unguarded.
pub(super) fn guarded_selectors(scan: &Scan) -> (HashSet<TermId>, Vec<TermId>) {
    let mut sets = GuardSets::default();
    let empty = sets.intern(Vec::new());
    let mut memo: HashMap<TermId, Vec<TermId>> = HashMap::default();
    let mut ok: HashMap<TermId, bool> = HashMap::default();
    let mut seen: HashSet<(TermId, u32)> = HashSet::default();
    let mut stack: Vec<(TermId, u32)> = scan.encode_roots.iter().map(|&r| (r, empty)).collect();
    while let Some((t, g)) = stack.pop() {
        if !seen.insert((t, g)) {
            continue;
        }
        if seen.len() > MAX_GUARD_VISITS {
            return (HashSet::default(), Vec::new());
        }
        let Some(node) = scan.node(t) else {
            return (HashSet::default(), Vec::new());
        };
        match node {
            Node::Sel {
                kind: SelKind::ListRest { .. } | SelKind::ListField { .. },
                arg,
            } => {
                let here = sets.sets[g as usize].binary_search(arg).is_ok();
                let entry = ok.entry(t).or_insert(true);
                *entry = *entry && here;
                stack.push((*arg, g));
            }
            Node::Ite(c, a, b) => {
                let extra = cons_guards(scan, *c, &mut memo);
                let ga = sets.extend(g, &extra);
                stack.extend([(*c, g), (*a, ga), (*b, g)]);
            }
            Node::And(args) | Node::Or(args) => {
                let per: Vec<Vec<TermId>> = args
                    .iter()
                    .map(|&a| match node {
                        Node::And(_) => cons_guards(scan, a, &mut memo),
                        _ => negated_guards(scan, a, &mut memo),
                    })
                    .collect();
                for (&a, extra) in args.iter().zip(sibling_extras(&per)) {
                    let ga = sets.extend(g, &extra);
                    stack.push((a, ga));
                }
            }
            Node::Implies(args) => {
                let Some((&last, premises)) = args.split_last() else {
                    continue;
                };
                let mut extra = Vec::new();
                for &p in premises {
                    extra.extend(cons_guards(scan, p, &mut memo));
                    stack.push((p, g));
                }
                let gl = sets.extend(g, &extra);
                stack.push((last, gl));
            }
            other => stack.extend(other.children().into_iter().map(|c| (c, g))),
        }
    }
    let unguarded = ok.iter().filter(|(_, v)| !**v).map(|(t, _)| *t).collect();
    let guarded = ok.into_iter().filter(|(_, v)| *v).map(|(t, _)| t).collect();
    (guarded, unguarded)
}
