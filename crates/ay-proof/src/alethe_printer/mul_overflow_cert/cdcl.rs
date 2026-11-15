// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A small CDCL refuter for local Boolean steps. Learned clauses are reverse
//! unit propagation consequences of the clauses before them, so a `drup` step
//! that lists them (each extended by the target literals) is checkable.

use super::super::emission_progress::EmissionProgress;
use super::propagation::{charge, Occurrences};
use super::term::T;
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};

pub(crate) struct Refutation {
    pub(crate) learned: Vec<Vec<(T, bool)>>,
    pub(crate) used: Vec<usize>,
}

struct State {
    db: Vec<Vec<(T, bool)>>,
    occurrences: Occurrences,
    /// atom -> (value, level, reason clause)
    assign: HashMap<T, (bool, u32, Option<usize>)>,
    trail: Vec<T>,
    level: u32,
    used: HashSet<usize>,
}

impl State {
    fn value(&self, a: T, p: bool) -> Option<bool> {
        self.assign.get(&a).map(|&(v, _, _)| v == p)
    }

    /// Unit propagation; returns a falsified clause.
    fn propagate(
        &mut self,
        budget: &mut u64,
        progress: &EmissionProgress<'_>,
    ) -> Option<Option<usize>> {
        let mut sweep = self.occurrences.sweep(budget, progress)?;
        while let Some(k) = sweep.next(budget, progress)? {
            progress.poll().then_some(())?;
            charge(budget, self.db[k].len().checked_add(1)?, progress)?;
            let mut open = None;
            let mut nopen = 0;
            let mut sat = false;
            for &(a, p) in &self.db[k] {
                progress.poll().then_some(())?;
                match self.value(a, p) {
                    None => {
                        nopen += 1;
                        open = Some((a, p));
                        if nopen > 1 {
                            break;
                        }
                    }
                    Some(true) => {
                        sat = true;
                        break;
                    }
                    Some(false) => {}
                }
            }
            if sat || nopen > 1 {
                continue;
            }
            match open {
                None => {
                    progress.poll().then_some(())?;
                    return Some(Some(k));
                }
                Some((a, p)) => {
                    self.assign.insert(a, (p, self.level, Some(k)));
                    self.trail.push(a);
                    sweep.assigned(&self.occurrences, a, budget, progress)?;
                }
            }
        }
        progress.poll().then_some(())?;
        Some(None)
    }

    fn mark_cone(&mut self, k: usize, progress: &EmissionProgress<'_>) -> Option<()> {
        progress.poll().then_some(())?;
        let mut stack = vec![k];
        let mut seen = HashSet::default();
        while let Some(c) = stack.pop() {
            progress.poll().then_some(())?;
            if !seen.insert(c) {
                continue;
            }
            self.used.insert(c);
            for &(a, _) in &self.db[c] {
                progress.poll().then_some(())?;
                if let Some(&(_, _, Some(r))) = self.assign.get(&a) {
                    if r != c {
                        stack.push(r);
                    }
                }
            }
        }
        progress.poll().then_some(())
    }

    /// First-UIP clause and backjump level for a conflict at `level > 0`.
    fn analyze(&self, k: usize, progress: &EmissionProgress<'_>) -> Option<(Vec<(T, bool)>, u32)> {
        progress.poll().then_some(())?;
        let mut seen = HashSet::default();
        let mut learnt = Vec::new();
        let mut counter = 0usize;
        let mut clause = self.db[k].clone();
        let mut idx = self.trail.len();
        let mut skip: Option<T> = None;
        let mut bt = 0;
        loop {
            progress.poll().then_some(())?;
            for &(a, p) in &clause {
                progress.poll().then_some(())?;
                if Some(a) == skip || !seen.insert(a) {
                    continue;
                }
                let &(_, lvl, _) = self.assign.get(&a)?;
                if lvl == self.level {
                    counter += 1;
                } else if lvl > 0 {
                    learnt.push((a, p));
                    bt = bt.max(lvl);
                }
            }
            loop {
                progress.poll().then_some(())?;
                idx = idx.checked_sub(1)?;
                if seen.contains(&self.trail[idx]) {
                    break;
                }
            }
            let a = self.trail[idx];
            counter = counter.checked_sub(1)?;
            let &(v, _, reason) = self.assign.get(&a)?;
            if counter == 0 {
                learnt.push((a, !v));
                progress.poll().then_some(())?;
                return Some((learnt, bt));
            }
            skip = Some(a);
            clause = self.db[reason?].clone();
        }
    }

    fn decide(&self, decide: &[T], progress: &EmissionProgress<'_>) -> Option<T> {
        for &v in decide {
            progress.poll().then_some(())?;
            if !self.assign.contains_key(&v) {
                return Some(v);
            }
        }
        for cl in &self.db {
            progress.poll().then_some(())?;
            let mut sat = false;
            let mut open = None;
            for &(a, p) in cl {
                progress.poll().then_some(())?;
                if self.value(a, p) == Some(true) {
                    sat = true;
                    break;
                }
                if open.is_none() && !self.assign.contains_key(&a) {
                    open = Some(a);
                }
            }
            if !sat && open.is_some() {
                return open;
            }
        }
        None
    }
}

/// Refute `db` together with the negation of `target`.
pub(crate) fn refute(
    db: &[Vec<(T, bool)>],
    target: &[(T, bool)],
    decide: &[T],
    budget: &mut u64,
    progress: &EmissionProgress<'_>,
) -> Option<Refutation> {
    progress.poll().then_some(())?;
    let occurrences = Occurrences::new(db, budget, progress)?;
    let mut st = State {
        db: db.to_vec(),
        occurrences,
        assign: HashMap::default(),
        trail: Vec::new(),
        level: 0,
        used: HashSet::default(),
    };
    for &(a, p) in target {
        progress.poll().then_some(())?;
        st.assign.insert(a, (!p, 0, None));
        st.trail.push(a);
    }
    let base = db.len();
    let mut learned = Vec::new();
    loop {
        progress.poll().then_some(())?;
        match st.propagate(budget, progress)? {
            Some(k) => {
                st.mark_cone(k, progress)?;
                if st.level == 0 {
                    let mut used: Vec<usize> =
                        st.used.iter().copied().filter(|&u| u < base).collect();
                    used.sort_unstable();
                    progress.poll().then_some(())?;
                    return Some(Refutation { learned, used });
                }
                let (clause, bt) = st.analyze(k, progress)?;
                progress.poll().then_some(())?;
                learned.push(clause.clone());
                st.occurrences.append(&clause, budget, progress)?;
                st.db.push(clause);
                while let Some(&a) = st.trail.last() {
                    progress.poll().then_some(())?;
                    if st.assign.get(&a).map_or(0, |x| x.1) <= bt {
                        break;
                    }
                    st.assign.remove(&a);
                    st.trail.pop();
                }
                st.level = bt;
            }
            None => {
                let v = st.decide(decide, progress)?;
                progress.poll().then_some(())?;
                st.level += 1;
                st.assign.insert(v, (true, st.level, None));
                st.trail.push(v);
            }
        }
    }
}
