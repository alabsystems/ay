// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A small incremental CDCL SAT solver with assumptions and final-conflict
//! cores, for the clausal-abstraction QBF engine.
//!
//! The abstraction engine asks each quantifier level thousands to millions
//! of tiny questions under assumptions, adding a clause between most of
//! them. `ay_sat::Solver` is built for large one-shot and IC3 queries: on
//! that workload its per-call setup dominated (about 4 ms per call on a
//! 24-variable formula, measured 2026-11-18), so this crate keeps a
//! textbook MiniSat core instead (Eén & Sörensson, "An Extensible
//! SAT-solver", SAT 2003): two watched literals, VSIDS with phase saving,
//! first-UIP learning with local minimization, Luby restarts, activity-based
//! learned-clause reduction, and `analyzeFinal` for the assumption core.
//!
//! Literals are `ay_sat::Literal` (index `2v` positive, `2v + 1` negative).

use ay_sat::{Literal, Variable};

const NO_REASON: u32 = u32::MAX;
const UNDEF: i8 = 0;
const TRUE: i8 = 1;
const FALSE: i8 = -1;

/// Answer to one query.
pub(crate) enum CdclResult {
    /// A model, indexed by variable.
    Sat(Vec<bool>),
    /// A subset of the assumptions that the clauses refute (empty when the
    /// clauses alone are unsatisfiable).
    Unsat(Vec<Literal>),
    /// Stopped by the caller.
    Unknown,
}

struct Clause {
    lits: Vec<Literal>,
    learnt: bool,
    activity: f64,
}

#[derive(Clone, Copy)]
struct Watch {
    clause: u32,
    blocker: Literal,
}

/// Binary max-heap of variables ordered by activity.
#[derive(Default)]
struct Heap {
    heap: Vec<u32>,
    index: Vec<u32>,
}

impl Heap {
    const ABSENT: u32 = u32::MAX;

    fn contains(&self, v: u32) -> bool {
        self.index[v as usize] != Self::ABSENT
    }

    fn grow(&mut self) {
        self.index.push(Self::ABSENT);
    }

    fn up(&mut self, mut pos: usize, act: &[f64]) {
        let v = self.heap[pos];
        while pos > 0 {
            let parent = (pos - 1) / 2;
            let p = self.heap[parent];
            if act[p as usize] >= act[v as usize] {
                break;
            }
            self.heap[pos] = p;
            self.index[p as usize] = pos as u32;
            pos = parent;
        }
        self.heap[pos] = v;
        self.index[v as usize] = pos as u32;
    }

    fn down(&mut self, mut pos: usize, act: &[f64]) {
        let v = self.heap[pos];
        let len = self.heap.len();
        loop {
            let left = 2 * pos + 1;
            if left >= len {
                break;
            }
            let right = left + 1;
            let child =
                if right < len && act[self.heap[right] as usize] > act[self.heap[left] as usize] {
                    right
                } else {
                    left
                };
            let c = self.heap[child];
            if act[c as usize] <= act[v as usize] {
                break;
            }
            self.heap[pos] = c;
            self.index[c as usize] = pos as u32;
            pos = child;
        }
        self.heap[pos] = v;
        self.index[v as usize] = pos as u32;
    }

    fn insert(&mut self, v: u32, act: &[f64]) {
        if self.contains(v) {
            return;
        }
        self.heap.push(v);
        let pos = self.heap.len() - 1;
        self.index[v as usize] = pos as u32;
        self.up(pos, act);
    }

    fn increased(&mut self, v: u32, act: &[f64]) {
        if self.contains(v) {
            self.up(self.index[v as usize] as usize, act);
        }
    }

    fn pop(&mut self, act: &[f64]) -> Option<u32> {
        let top = *self.heap.first()?;
        let last = self.heap.pop()?;
        self.index[top as usize] = Self::ABSENT;
        if !self.heap.is_empty() {
            self.heap[0] = last;
            self.index[last as usize] = 0;
            self.down(0, act);
        }
        Some(top)
    }
}

/// Incremental CDCL solver.
pub(crate) struct Cdcl {
    clauses: Vec<Clause>,
    free_slots: Vec<u32>,
    watches: Vec<Vec<Watch>>,
    assigns: Vec<i8>,
    level: Vec<u32>,
    reason: Vec<u32>,
    polarity: Vec<bool>,
    activity: Vec<f64>,
    seen: Vec<bool>,
    heap: Heap,
    trail: Vec<Literal>,
    trail_lim: Vec<usize>,
    qhead: usize,
    var_inc: f64,
    cla_inc: f64,
    num_learnts: usize,
    num_originals: usize,
    max_learnts: f64,
    conflicts: u64,
    /// False once the clauses alone are refuted.
    ok: bool,
}

fn luby(y: f64, mut x: u64) -> f64 {
    let mut size = 1u64;
    let mut seq = 0i32;
    while size < x + 1 {
        seq += 1;
        size = 2 * size + 1;
    }
    while size - 1 != x {
        size = (size - 1) >> 1;
        seq -= 1;
        x %= size;
    }
    y.powi(seq)
}

impl Cdcl {
    pub(crate) fn new() -> Self {
        Self {
            clauses: Vec::new(),
            free_slots: Vec::new(),
            watches: Vec::new(),
            assigns: Vec::new(),
            level: Vec::new(),
            reason: Vec::new(),
            polarity: Vec::new(),
            activity: Vec::new(),
            seen: Vec::new(),
            heap: Heap::default(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
            qhead: 0,
            var_inc: 1.0,
            cla_inc: 1.0,
            num_learnts: 0,
            num_originals: 0,
            max_learnts: 0.0,
            conflicts: 0,
            ok: true,
        }
    }

    pub(crate) fn new_var(&mut self) -> Variable {
        let v = self.assigns.len() as u32;
        self.assigns.push(UNDEF);
        self.level.push(0);
        self.reason.push(NO_REASON);
        // Default phase false, as MiniSat.
        self.polarity.push(false);
        self.activity.push(0.0);
        self.seen.push(false);
        self.watches.push(Vec::new());
        self.watches.push(Vec::new());
        self.heap.grow();
        self.heap.insert(v, &self.activity);
        Variable::new(v)
    }

    #[inline]
    fn value(&self, lit: Literal) -> i8 {
        let a = self.assigns[lit.variable().index()];
        if lit.is_positive() {
            a
        } else {
            -a
        }
    }

    fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    fn enqueue(&mut self, lit: Literal, reason: u32) {
        let v = lit.variable().index();
        self.assigns[v] = if lit.is_positive() { TRUE } else { FALSE };
        self.level[v] = self.decision_level() as u32;
        self.reason[v] = reason;
        self.trail.push(lit);
    }

    /// Add a clause; only valid between queries (at level 0).
    pub(crate) fn add_clause(&mut self, mut lits: Vec<Literal>) {
        if !self.ok {
            return;
        }
        lits.sort_unstable();
        lits.dedup();
        let mut kept = Vec::with_capacity(lits.len());
        for (i, &l) in lits.iter().enumerate() {
            if i + 1 < lits.len() && lits[i + 1] == l.negated() {
                return; // tautology (negation sorts right after)
            }
            match self.value(l) {
                TRUE => return,
                FALSE => {}
                _ => kept.push(l),
            }
        }
        match kept.len() {
            0 => self.ok = false,
            1 => {
                self.enqueue(kept[0], NO_REASON);
                if self.propagate() != NO_REASON {
                    self.ok = false;
                }
            }
            _ => {
                self.num_originals += 1;
                self.attach(kept, false);
            }
        }
    }

    fn attach(&mut self, lits: Vec<Literal>, learnt: bool) -> u32 {
        let (a, b) = (lits[0], lits[1]);
        let clause = Clause {
            lits,
            learnt,
            activity: 0.0,
        };
        let index = match self.free_slots.pop() {
            Some(slot) => {
                self.clauses[slot as usize] = clause;
                slot
            }
            None => {
                self.clauses.push(clause);
                (self.clauses.len() - 1) as u32
            }
        };
        self.watches[a.index()].push(Watch {
            clause: index,
            blocker: b,
        });
        self.watches[b.index()].push(Watch {
            clause: index,
            blocker: a,
        });
        index
    }

    /// Unit propagation; returns the conflicting clause or `NO_REASON`.
    fn propagate(&mut self) -> u32 {
        let mut conflict = NO_REASON;
        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            let false_lit = p.negated();
            let mut ws = std::mem::take(&mut self.watches[false_lit.index()]);
            let mut i = 0;
            let mut j = 0;
            while i < ws.len() {
                let w = ws[i];
                i += 1;
                if self.value(w.blocker) == TRUE {
                    ws[j] = w;
                    j += 1;
                    continue;
                }
                let cref = w.clause as usize;
                {
                    let lits = &mut self.clauses[cref].lits;
                    if lits[0] == false_lit {
                        lits.swap(0, 1);
                    }
                }
                let first = self.clauses[cref].lits[0];
                if first != w.blocker && self.value(first) == TRUE {
                    ws[j] = Watch {
                        clause: w.clause,
                        blocker: first,
                    };
                    j += 1;
                    continue;
                }
                let len = self.clauses[cref].lits.len();
                let mut moved = false;
                for k in 2..len {
                    let l = self.clauses[cref].lits[k];
                    if self.value(l) != FALSE {
                        self.clauses[cref].lits.swap(1, k);
                        self.watches[l.index()].push(Watch {
                            clause: w.clause,
                            blocker: first,
                        });
                        moved = true;
                        break;
                    }
                }
                if moved {
                    continue;
                }
                ws[j] = Watch {
                    clause: w.clause,
                    blocker: first,
                };
                j += 1;
                if self.value(first) == FALSE {
                    conflict = w.clause;
                    self.qhead = self.trail.len();
                    while i < ws.len() {
                        ws[j] = ws[i];
                        j += 1;
                        i += 1;
                    }
                } else {
                    self.enqueue(first, w.clause);
                }
            }
            ws.truncate(j);
            self.watches[false_lit.index()] = ws;
            if conflict != NO_REASON {
                break;
            }
        }
        conflict
    }

    fn bump_var(&mut self, v: usize) {
        self.activity[v] += self.var_inc;
        if self.activity[v] > 1e100 {
            for a in &mut self.activity {
                *a *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }
        self.heap.increased(v as u32, &self.activity);
    }

    fn bump_clause(&mut self, cref: usize) {
        let clause = &mut self.clauses[cref];
        if !clause.learnt {
            return;
        }
        clause.activity += self.cla_inc;
        if clause.activity > 1e20 {
            for c in &mut self.clauses {
                c.activity *= 1e-20;
            }
            self.cla_inc *= 1e-20;
        }
    }

    /// First-UIP conflict analysis: the learnt clause (asserting literal
    /// first, a literal of the backjump level second) and the backjump level.
    fn analyze(&mut self, mut conflict: u32) -> (Vec<Literal>, usize) {
        let current = self.decision_level() as u32;
        let mut learnt = vec![Literal::positive(Variable::new(0))];
        let mut path = 0usize;
        let mut index = self.trail.len();
        let mut asserting: Option<Literal> = None;
        loop {
            let cref = conflict as usize;
            self.bump_clause(cref);
            let start = usize::from(asserting.is_some());
            for k in start..self.clauses[cref].lits.len() {
                let q = self.clauses[cref].lits[k];
                let v = q.variable().index();
                if !self.seen[v] && self.level[v] > 0 {
                    self.seen[v] = true;
                    self.bump_var(v);
                    if self.level[v] >= current {
                        path += 1;
                    } else {
                        learnt.push(q);
                    }
                }
            }
            loop {
                index -= 1;
                if self.seen[self.trail[index].variable().index()] {
                    break;
                }
            }
            let p = self.trail[index];
            let v = p.variable().index();
            self.seen[v] = false;
            path -= 1;
            asserting = Some(p);
            if path == 0 {
                break;
            }
            conflict = self.reason[v];
        }
        learnt[0] = asserting.map_or(learnt[0], Literal::negated);

        // Local minimization: drop a literal implied by others in the clause.
        let marked: Vec<Literal> = learnt[1..].to_vec();
        let mut kept = 1;
        for k in 1..learnt.len() {
            let v = learnt[k].variable().index();
            let r = self.reason[v];
            let redundant = r != NO_REASON
                && self.clauses[r as usize].lits[1..].iter().all(|q| {
                    let u = q.variable().index();
                    self.seen[u] || self.level[u] == 0
                });
            if !redundant {
                learnt[kept] = learnt[k];
                kept += 1;
            }
        }
        learnt.truncate(kept);
        for l in &marked {
            self.seen[l.variable().index()] = false;
        }

        let mut backjump = 0;
        if learnt.len() > 1 {
            let mut best = 1;
            for k in 2..learnt.len() {
                if self.level[learnt[k].variable().index()]
                    > self.level[learnt[best].variable().index()]
                {
                    best = k;
                }
            }
            learnt.swap(1, best);
            backjump = self.level[learnt[1].variable().index()] as usize;
        }
        (learnt, backjump)
    }

    /// The assumptions responsible for `failed` (an assumption that is
    /// false under the current trail), MiniSat's `analyzeFinal`.
    fn analyze_final(&mut self, failed: Literal) -> Vec<Literal> {
        let mut core = vec![failed];
        if self.decision_level() == 0 {
            return core;
        }
        let fv = failed.variable().index();
        self.seen[fv] = true;
        for i in (self.trail_lim[0]..self.trail.len()).rev() {
            let x = self.trail[i].variable().index();
            if !self.seen[x] {
                continue;
            }
            let r = self.reason[x];
            if r == NO_REASON {
                // A decision above level 0 while assumptions are being
                // placed is an assumption (possibly the complement of
                // `failed` itself).
                core.push(self.trail[i]);
            } else {
                for k in 1..self.clauses[r as usize].lits.len() {
                    let u = self.clauses[r as usize].lits[k].variable().index();
                    if self.level[u] > 0 {
                        self.seen[u] = true;
                    }
                }
            }
            self.seen[x] = false;
        }
        self.seen[fv] = false;
        core
    }

    fn cancel_until(&mut self, level: usize) {
        if self.decision_level() <= level {
            return;
        }
        let bound = self.trail_lim[level];
        for i in (bound..self.trail.len()).rev() {
            let l = self.trail[i];
            let v = l.variable().index();
            self.assigns[v] = UNDEF;
            self.reason[v] = NO_REASON;
            self.polarity[v] = l.is_positive();
            self.heap.insert(v as u32, &self.activity);
        }
        self.trail.truncate(bound);
        self.qhead = bound;
        self.trail_lim.truncate(level);
    }

    fn locked(&self, cref: usize) -> bool {
        let first = self.clauses[cref].lits[0];
        let v = first.variable().index();
        self.reason[v] == cref as u32 && self.value(first) == TRUE
    }

    /// Delete about half of the learnt clauses, least active first; binary
    /// and reason clauses stay.
    fn reduce_db(&mut self) {
        let mut candidates: Vec<usize> = (0..self.clauses.len())
            .filter(|&c| {
                let clause = &self.clauses[c];
                clause.learnt && clause.lits.len() > 2 && !self.locked(c)
            })
            .collect();
        candidates.sort_by(|&a, &b| {
            self.clauses[a]
                .activity
                .total_cmp(&self.clauses[b].activity)
        });
        let remove = candidates.len() / 2;
        let mut deleted = vec![false; self.clauses.len()];
        for &c in &candidates[..remove] {
            deleted[c] = true;
            self.clauses[c].lits = Vec::new();
            self.clauses[c].learnt = false;
            self.free_slots.push(c as u32);
            self.num_learnts -= 1;
        }
        if remove > 0 {
            for ws in &mut self.watches {
                ws.retain(|w| !deleted[w.clause as usize]);
            }
        }
    }

    fn pick_branch(&mut self) -> Option<Literal> {
        while let Some(v) = self.heap.pop(&self.activity) {
            if self.assigns[v as usize] == UNDEF {
                let var = Variable::new(v);
                return Some(if self.polarity[v as usize] {
                    Literal::positive(var)
                } else {
                    Literal::negative(var)
                });
            }
        }
        None
    }

    /// Decide the clauses under `assumptions`. `stop` is polled every 256
    /// conflicts and every 4096 decisions.
    pub(crate) fn solve(&mut self, assumptions: &[Literal], stop: &dyn Fn() -> bool) -> CdclResult {
        if !self.ok {
            return CdclResult::Unsat(Vec::new());
        }
        if self.max_learnts == 0.0 {
            self.max_learnts = (self.num_originals as f64 / 3.0).max(5000.0);
        }
        let mut restart = 0u64;
        let mut decisions = 0u64;
        loop {
            let budget = (luby(2.0, restart) * 100.0) as u64;
            restart += 1;
            let mut local = 0u64;
            loop {
                let conflict = self.propagate();
                if conflict != NO_REASON {
                    self.conflicts += 1;
                    local += 1;
                    if self.decision_level() == 0 {
                        self.ok = false;
                        return CdclResult::Unsat(Vec::new());
                    }
                    let (learnt, backjump) = self.analyze(conflict);
                    self.cancel_until(backjump);
                    if learnt.len() == 1 {
                        self.enqueue(learnt[0], NO_REASON);
                    } else {
                        let asserting = learnt[0];
                        let cref = self.attach(learnt, true);
                        self.num_learnts += 1;
                        self.bump_clause(cref as usize);
                        self.enqueue(asserting, cref);
                    }
                    self.var_inc /= 0.95;
                    self.cla_inc /= 0.999;
                    if self.conflicts % 256 == 0 && stop() {
                        self.cancel_until(0);
                        return CdclResult::Unknown;
                    }
                    continue;
                }
                if local >= budget {
                    self.cancel_until(0);
                    break;
                }
                if self.num_learnts as f64 >= self.max_learnts + self.trail.len() as f64 {
                    self.reduce_db();
                    self.max_learnts *= 1.1;
                }
                let mut next = None;
                while self.decision_level() < assumptions.len() {
                    let p = assumptions[self.decision_level()];
                    match self.value(p) {
                        TRUE => self.trail_lim.push(self.trail.len()),
                        FALSE => {
                            let core = self.analyze_final(p);
                            self.cancel_until(0);
                            return CdclResult::Unsat(core);
                        }
                        _ => {
                            next = Some(p);
                            break;
                        }
                    }
                }
                let next = match next {
                    Some(p) => p,
                    None => match self.pick_branch() {
                        Some(p) => p,
                        None => {
                            let model = self.assigns.iter().map(|&a| a == TRUE).collect();
                            self.cancel_until(0);
                            return CdclResult::Sat(model);
                        }
                    },
                };
                decisions += 1;
                if decisions % 4096 == 0 && stop() {
                    self.cancel_until(0);
                    return CdclResult::Unknown;
                }
                self.trail_lim.push(self.trail.len());
                self.enqueue(next, NO_REASON);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Lcg(u64);
    impl Lcg {
        fn below(&mut self, n: u64) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (self.0 >> 33) % n
        }
    }

    fn satisfiable(clauses: &[Vec<Literal>], fixed: &[Literal], n: usize) -> bool {
        (0u32..1 << n).any(|bits| {
            let val = |l: Literal| ((bits >> l.variable().index()) & 1 == 1) == l.is_positive();
            fixed.iter().all(|&l| val(l)) && clauses.iter().all(|c| c.iter().any(|&l| val(l)))
        })
    }

    /// Random incremental sessions: every answer is checked by brute force,
    /// every model against all clauses and assumptions, and every core is
    /// a subset of the assumptions that is itself refuted.
    #[test]
    fn cdcl_matches_brute_force_incrementally() {
        let mut rng = Lcg(0xcdc1_2026);
        let mut seen = [0usize; 2];
        for _ in 0..400 {
            let n = 1 + rng.below(12) as usize;
            let mut solver = Cdcl::new();
            let vars: Vec<Variable> = (0..n).map(|_| solver.new_var()).collect();
            let mut clauses: Vec<Vec<Literal>> = Vec::new();
            let lit = |rng: &mut Lcg| {
                let v = vars[rng.below(n as u64) as usize];
                if rng.below(2) == 0 {
                    Literal::positive(v)
                } else {
                    Literal::negative(v)
                }
            };
            for _ in 0..12 {
                for _ in 0..rng.below(n as u64 / 2 + 2) {
                    let len = 1 + rng.below(4) as usize;
                    let clause: Vec<Literal> = (0..len).map(|_| lit(&mut rng)).collect();
                    solver.add_clause(clause.clone());
                    clauses.push(clause);
                }
                let assumptions: Vec<Literal> = (0..rng.below(n as u64 + 1))
                    .map(|_| lit(&mut rng))
                    .collect();
                let expected = satisfiable(&clauses, &assumptions, n);
                match solver.solve(&assumptions, &|| false) {
                    CdclResult::Sat(model) => {
                        assert!(expected, "SAT on an unsatisfiable query");
                        let val = |l: Literal| model[l.variable().index()] == l.is_positive();
                        assert!(assumptions.iter().all(|&l| val(l)));
                        assert!(clauses.iter().all(|c| c.iter().any(|&l| val(l))));
                        seen[0] += 1;
                    }
                    CdclResult::Unsat(core) => {
                        assert!(!expected, "UNSAT on a satisfiable query");
                        assert!(core.iter().all(|l| assumptions.contains(l)));
                        assert!(!satisfiable(&clauses, &core, n), "core is not refuted");
                        seen[1] += 1;
                    }
                    CdclResult::Unknown => panic!("no stop was requested"),
                }
            }
        }
        assert!(seen[0] > 400 && seen[1] > 400, "{seen:?}");
    }

    #[test]
    fn cdcl_refutes_pigeonhole_and_stops_on_request() {
        // PHP(6, 5) is unsatisfiable.
        let holes = 5u32;
        let mut solver = Cdcl::new();
        let vars: Vec<Variable> = (0..(holes + 1) * holes).map(|_| solver.new_var()).collect();
        let x = |p: u32, h: u32| vars[(p * holes + h) as usize];
        for p in 0..=holes {
            solver.add_clause((0..holes).map(|h| Literal::positive(x(p, h))).collect());
        }
        for h in 0..holes {
            for p in 0..=holes {
                for q in p + 1..=holes {
                    solver.add_clause(vec![Literal::negative(x(p, h)), Literal::negative(x(q, h))]);
                }
            }
        }
        assert!(matches!(solver.solve(&[], &|| false), CdclResult::Unsat(c) if c.is_empty()));
        let mut big = Cdcl::new();
        let holes = 11u32;
        let vars: Vec<Variable> = (0..(holes + 1) * holes).map(|_| big.new_var()).collect();
        let x = |p: u32, h: u32| vars[(p * holes + h) as usize];
        for p in 0..=holes {
            big.add_clause((0..holes).map(|h| Literal::positive(x(p, h))).collect());
        }
        for h in 0..holes {
            for p in 0..=holes {
                for q in p + 1..=holes {
                    big.add_clause(vec![Literal::negative(x(p, h)), Literal::negative(x(q, h))]);
                }
            }
        }
        assert!(matches!(big.solve(&[], &|| true), CdclResult::Unknown));
    }
}
