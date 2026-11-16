// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The bit-serial invariant prover. A linear bit-level fact over ripple
//! structures (adders, comparators) is proved one bit position at a time:
//! the exact set of reachable joint carry states at each boundary is computed
//! by projected enumeration, written as clauses, and each boundary's clauses
//! are derived from the previous boundary's and that position's gates.

use super::super::emission_progress::EmissionProgress;
use super::localsat::{self, Clause};
use super::proof::{Prem, Proof, S};
use super::term::{Op, T};
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};

/// Gates between `t` and the stop/cut sets, and the leaf atoms reached.
pub(crate) fn cone(
    p: &Proof<'_>,
    t: T,
    stop: &HashSet<T>,
    cut: &HashSet<T>,
    leafcut: &HashSet<T>,
) -> (Vec<T>, Vec<T>) {
    let (mut gates, mut leaves) = (Vec::new(), Vec::new());
    if leafcut.contains(&t) {
        return (gates, vec![t]);
    }
    let mut seen = HashSet::default();
    let mut stack = vec![t];
    while let Some(u) = stack.pop() {
        if !seen.insert(u) {
            continue;
        }
        if matches!(p.t.op(u), Op::True | Op::False) {
            gates.push(u);
            continue;
        }
        if u != t && (stop.contains(&u) || cut.contains(&u) || leafcut.contains(&u)) {
            leaves.push(u);
            continue;
        }
        if p.t.is_gate(u) {
            gates.push(u);
            stack.extend(p.t.args(u));
        } else if matches!(p.t.op(u), Op::Not) {
            stack.extend(p.t.args(u));
        } else {
            leaves.push(u);
        }
    }
    (gates, leaves)
}

#[derive(Default)]
pub(crate) struct Chain {
    pub(crate) bounds: Vec<Vec<T>>,
    pub(crate) outputs: HashMap<usize, Vec<Vec<T>>>,
    pub(crate) finals: Vec<Vec<T>>,
    pub(crate) params: Vec<(T, S)>,
    pub(crate) hyps: HashMap<usize, Vec<S>>,
    pub(crate) final_hyps: Vec<S>,
    pub(crate) cut: HashSet<T>,
    pub(crate) leafcut: HashSet<T>,
}

pub(crate) struct ChainResult {
    pub(crate) outputs: HashMap<usize, Vec<S>>,
    pub(crate) finals: Vec<S>,
}

const MAX_STATE: usize = 18;

struct Run {
    env: HashMap<T, bool>,
    param_steps: Vec<S>,
    budget: u64,
}

impl Chain {
    fn state_atoms(&self, p: &Proof<'_>, run: &Run, i: usize) -> Vec<T> {
        let mut out = Vec::new();
        let mut seen = HashSet::default();
        for &t in &self.bounds[i] {
            let a = p.t.lit_of(t).0;
            if matches!(p.t.op(a), Op::True | Op::False)
                || run.env.contains_key(&a)
                || !seen.insert(a)
            {
                continue;
            }
            out.push(a);
        }
        out
    }

    /// Boundary 0 also carries the leaf inputs its terms depend on.
    fn widen_boundary0(&mut self, p: &Proof<'_>, run: &Run) {
        let stop: HashSet<T> = run.env.keys().copied().collect();
        let mut seen: HashSet<T> = self.bounds[0].iter().map(|&t| p.t.lit_of(t).0).collect();
        let mut extra = Vec::new();
        for &t in &self.bounds[0] {
            let a = p.t.lit_of(t).0;
            if matches!(p.t.op(a), Op::True | Op::False) || run.env.contains_key(&a) {
                continue;
            }
            let (_, leaves) = cone(p, a, &stop, &self.cut, &self.leafcut);
            for x in leaves {
                let y = p.t.lit_of(x).0;
                if !matches!(p.t.op(y), Op::True | Op::False)
                    && !run.env.contains_key(&y)
                    && seen.insert(y)
                {
                    extra.push(y);
                }
            }
        }
        self.bounds[0].extend(extra);
    }

    fn local_clauses(p: &mut Proof<'_>, gates: &[T]) -> Vec<Clause> {
        let mut out = Vec::new();
        for &g in gates {
            for d in p.gate_defs(g) {
                out.push(d.lits().iter().map(|&l| p.t.lit_of(l)).collect());
            }
        }
        out
    }

    /// Projections onto `proj` of the models of `db` that extend `fixed`.
    fn project(
        db: &[Clause],
        fixed: &HashMap<T, bool>,
        proj: &[T],
        budget: &mut u64,
        progress: &EmissionProgress<'_>,
    ) -> Option<HashSet<Vec<bool>>> {
        progress.poll().then_some(())?;
        if proj.len() > MAX_STATE {
            return None;
        }
        localsat::project(db, fixed, proj, budget, progress)
    }

    pub(crate) fn run(mut self, p: &mut Proof<'_>) -> Option<ChainResult> {
        p.observe()?;
        let mut run = Run {
            env: HashMap::default(),
            param_steps: Vec::new(),
            budget: 2_000_000_000,
        };
        for &(l, s) in &self.params {
            p.observe()?;
            let (a, v) = p.t.lit_of(l);
            run.env.insert(a, v);
            run.param_steps.push(s);
        }
        self.widen_boundary0(p, &run);
        p.observe()?;
        let (mut reach, mut inv) = self.boundary0(p, &mut run)?;
        let mut outputs = HashMap::default();
        let len = self.bounds.len() - 1;
        for i in 0..len {
            p.observe()?;
            let (r2, inv2, outs) = self.position(p, &mut run, i, &reach, &inv)?;
            reach = r2;
            inv = inv2;
            outputs.insert(i, outs);
        }
        let finals = self.finish(p, &run, len, &inv)?;
        p.observe()?;
        Some(ChainResult { outputs, finals })
    }

    fn boundary0(&self, p: &mut Proof<'_>, run: &mut Run) -> Option<(HashSet<Vec<bool>>, Vec<S>)> {
        p.observe()?;
        let s0 = self.state_atoms(p, run, 0);
        let stop: HashSet<T> = run.env.keys().copied().collect();
        let mut gates = Vec::new();
        for &a in &s0 {
            gates.extend(cone(p, a, &stop, &self.cut, &self.leafcut).0);
        }
        let db = Self::local_clauses(p, &gates);
        let reach = Self::project(&db, &run.env.clone(), &s0, &mut run.budget, p.progress())?;
        let mut prem: Vec<Prem> = run.param_steps.iter().map(|&s| Prem::Step(s)).collect();
        for &g in &gates {
            prem.extend(p.gate(g));
        }
        let inv = invariant(p, &s0, &reach, &prem, &s0)?;
        Some((reach, inv))
    }
}

fn valid_clause(p: &Proof<'_>, reach: &[&Vec<bool>], c: &[(usize, bool)]) -> Option<bool> {
    for s in reach {
        p.observe()?;
        if !c.iter().any(|&(j, v)| s[j] == v) {
            return Some(false);
        }
    }
    Some(true)
}

fn covered_state(
    p: &Proof<'_>,
    reach: &HashSet<Vec<bool>>,
    chosen: &[Vec<(usize, bool)>],
    s: &[bool],
) -> Option<bool> {
    p.observe()?;
    if s.len() > MAX_STATE {
        return None;
    }
    // The exact set is already owned by the projection. Do not rescan its
    // ordered view for every valuation; that view still determines all clauses.
    let reachable = reach.contains(s);
    p.observe()?;
    if reachable {
        return Some(true);
    }
    for c in chosen {
        p.observe()?;
        if c.iter().all(|&(j, v)| s[j] != v) {
            return Some(true);
        }
    }
    Some(false)
}

/// Clauses over `atoms` exactly characterizing `reach`, each derived from `prem`.
fn invariant(
    p: &mut Proof<'_>,
    atoms: &[T],
    reach: &HashSet<Vec<bool>>,
    prem: &[Prem],
    decide: &[T],
) -> Option<Vec<S>> {
    p.observe()?;
    let k = atoms.len();
    if k > MAX_STATE {
        return None;
    }
    let ordered_reach: Vec<&Vec<bool>> = reach.iter().collect();

    let mut chosen: Vec<Vec<(usize, bool)>> = Vec::new();
    for size in 1..=2usize {
        for c in small_clauses(k, size) {
            p.observe()?;
            if chosen.iter().any(|x| x.iter().all(|l| c.contains(l))) {
                continue;
            }
            if valid_clause(p, &ordered_reach, &c)? {
                chosen.push(c);
            }
        }
    }
    for st in 0u64..(1u64 << k) {
        let s: Vec<bool> = (0..k).map(|j| (st >> j) & 1 == 1).collect();
        p.observe()?;
        if covered_state(p, reach, &chosen, &s)? {
            continue;
        }
        let mut c: Vec<(usize, bool)> = (0..k).map(|j| (j, !s[j])).collect();
        let mut shrunk = true;
        while shrunk {
            p.observe()?;
            shrunk = false;
            for x in 0..c.len() {
                p.observe()?;
                let mut c2 = c.clone();
                c2.remove(x);
                if !c2.is_empty() && valid_clause(p, &ordered_reach, &c2)? {
                    c = c2;
                    shrunk = true;
                    break;
                }
            }
        }
        chosen.push(c);
    }
    let mut out = Vec::new();
    for c in chosen {
        p.observe()?;
        let lits: Vec<T> = c
            .iter()
            .map(|&(j, v)| if v { atoms[j] } else { p.t.not(atoms[j]) })
            .collect();
        out.push(p.derive(&lits, prem, decide)?);
    }
    Some(out)
}

#[cfg(test)]
mod tests;

fn small_clauses(k: usize, size: usize) -> Vec<Vec<(usize, bool)>> {
    let mut out = Vec::new();
    if size == 1 {
        for j in 0..k {
            for v in [false, true] {
                out.push(vec![(j, v)]);
            }
        }
    } else {
        for a in 0..k {
            for b in a + 1..k {
                for (va, vb) in [(false, false), (false, true), (true, false), (true, true)] {
                    out.push(vec![(a, va), (b, vb)]);
                }
            }
        }
    }
    out
}

/// The states reachable after one position, its invariant steps and its
/// output steps.
type Advance = (HashSet<Vec<bool>>, Vec<S>, Vec<S>);

impl Chain {
    fn position(
        &self,
        p: &mut Proof<'_>,
        run: &mut Run,
        i: usize,
        reach: &HashSet<Vec<bool>>,
        inv: &[S],
    ) -> Option<Advance> {
        p.observe()?;
        let si = self.state_atoms(p, run, i);
        let sn = self.state_atoms(p, run, i + 1);
        let mut stop: HashSet<T> = si.iter().copied().collect();
        stop.extend(run.env.keys().copied());
        let mut targets: Vec<T> = self.bounds[i + 1].clone();
        let outs = self.outputs.get(&i).cloned().unwrap_or_default();
        for cl in &outs {
            targets.extend(cl);
        }
        let hyps = self.hyps.get(&i).cloned().unwrap_or_default();
        for &h in &hyps {
            targets.extend(p.clause(h).to_vec());
        }
        let (gates, inputs) = self.position_cone(p, &targets, &stop);
        let mut db = Self::local_clauses(p, &gates);
        for &h in &hyps {
            db.push(p.clause(h).iter().map(|&l| p.t.lit_of(l)).collect());
        }
        let mut newreach = HashSet::default();
        for s in reach {
            p.observe()?;
            let mut fixed = run.env.clone();
            for (&a, &v) in si.iter().zip(s) {
                fixed.insert(a, v);
            }
            newreach.extend(Self::project(
                &db,
                &fixed,
                &sn,
                &mut run.budget,
                p.progress(),
            )?);
            for cl in &outs {
                let mut neg = fixed.clone();
                for &l in cl {
                    let (a, v) = p.t.lit_of(l);
                    neg.insert(a, !v);
                }
                if localsat::solve(&db, &neg, &mut run.budget, p.progress())?.is_some() {
                    return None;
                }
            }
        }
        let mut prem: Vec<Prem> = Vec::new();
        for &g in &gates {
            prem.extend(p.gate(g));
        }
        prem.extend(inv.iter().map(|&s| Prem::Step(s)));
        prem.extend(hyps.iter().map(|&s| Prem::Step(s)));
        prem.extend(run.param_steps.iter().map(|&s| Prem::Step(s)));
        let mut decide = si.clone();
        decide.extend(&inputs);
        let mut out_steps = Vec::new();
        for cl in &outs {
            out_steps.push(p.derive(cl, &prem, &decide)?);
        }
        let inv2 = invariant(p, &sn, &newreach, &prem, &decide)?;
        Some((newreach, inv2, out_steps))
    }

    fn position_cone(&self, p: &Proof<'_>, targets: &[T], stop: &HashSet<T>) -> (Vec<T>, Vec<T>) {
        let mut gates = Vec::new();
        let mut gseen = HashSet::default();
        let mut inputs = Vec::new();
        let mut iseen = HashSet::default();
        for &t in targets {
            let (g, leaves) = cone(p, t, stop, &self.cut, &self.leafcut);
            for x in g {
                if gseen.insert(x) {
                    gates.push(x);
                }
            }
            for x in leaves {
                let a = p.t.lit_of(x).0;
                if !stop.contains(&a)
                    && !matches!(p.t.op(a), Op::True | Op::False)
                    && iseen.insert(a)
                {
                    inputs.push(a);
                }
            }
        }
        (gates, inputs)
    }

    fn finish(&self, p: &mut Proof<'_>, run: &Run, len: usize, inv: &[S]) -> Option<Vec<S>> {
        p.observe()?;
        let sl = self.state_atoms(p, run, len);
        let mut stop: HashSet<T> = sl.iter().copied().collect();
        stop.extend(run.env.keys().copied());
        let mut out = Vec::new();
        for cl in &self.finals {
            p.observe()?;
            let mut prem: Vec<Prem> = inv.iter().map(|&s| Prem::Step(s)).collect();
            prem.extend(self.final_hyps.iter().map(|&s| Prem::Step(s)));
            for &l in cl {
                let (g, _) = cone(p, l, &stop, &self.cut, &self.leafcut);
                for x in g {
                    prem.extend(p.gate(x));
                }
            }
            prem.extend(run.param_steps.iter().map(|&s| Prem::Step(s)));
            out.push(p.derive(cl, &prem, &sl)?);
        }
        Some(out)
    }
}
