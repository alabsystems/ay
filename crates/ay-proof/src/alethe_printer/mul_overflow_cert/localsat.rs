// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A tiny DPLL over a few hundred local clauses, used to enumerate the
//! reachable states of a bit-serial circuit (never as a proof).
//!
//! Every fresh solve starts with a full ordered propagation. Only a completed
//! parent fixed point can seed a child from one newly decided atom: unchanged
//! rows retain their parent result until a propagated assignment notifies them.
//! No fixed point or assignment survives a solve or a projection database append.

use super::super::emission_progress::EmissionProgress;
use super::propagation::{charge, exhausted, reserve, Occurrences};
use super::term::T;
use ay_core::kani_compat::DetHashMap as HashMap;

pub(crate) type Clause = Vec<(T, bool)>;

mod projected;
pub(super) use projected::project;

#[cfg(test)]
mod seeded_tests;

/// Only successful propagation below constructs this state. Its immutable
/// index borrow cannot outlive the current solve or survive a database append.
struct FixedPoint<'index> {
    assignment: HashMap<T, bool>,
    index: &'index Occurrences,
}

enum Pending<'index> {
    Fresh(HashMap<T, bool>),
    Ready(FixedPoint<'index>),
    Child {
        parent: FixedPoint<'index>,
        decision: (T, bool),
    },
}

/// Private-field capability issued only when extending a proved fixed point
/// by one previously unassigned atom. No arbitrary input can request a seed.
pub(super) struct ChildSeed<'index> {
    index: &'index Occurrences,
    atom: T,
}

impl ChildSeed<'_> {
    pub(super) fn atom_for(&self, index: &Occurrences) -> Option<T> {
        std::ptr::eq(self.index, index).then_some(self.atom)
    }
}

fn propagate<'index>(
    db: &[Clause],
    index: &'index Occurrences,
    pending: Pending<'index>,
    budget: &mut u64,
    progress: &EmissionProgress<'_>,
) -> Option<Option<FixedPoint<'index>>> {
    let (mut asg, mut sweep) = match pending {
        Pending::Fresh(asg) => (asg, index.sweep(budget, progress)?),
        Pending::Ready(parent) => {
            progress.poll().then_some(())?;
            if !std::ptr::eq(parent.index, index) {
                return exhausted(budget);
            }
            return Some(Some(parent));
        }
        Pending::Child {
            mut parent,
            decision: (atom, value),
        } => {
            charge(budget, 1, progress)?;
            if parent.assignment.contains_key(&atom) {
                return exhausted(budget);
            }
            let seed = ChildSeed {
                index: parent.index,
                atom,
            };
            let sweep = index.sweep_after_decision(&seed, budget, progress)?;
            parent.assignment.insert(atom, value);
            (parent.assignment, sweep)
        }
    };
    while let Some(k) = sweep.next(budget, progress)? {
        progress.poll().then_some(())?;
        let cl = &db[k];
        charge(budget, cl.len().checked_add(1)?, progress)?;
        let mut open = None;
        let mut nopen = 0;
        let mut sat = false;
        for &(a, p) in cl {
            progress.poll().then_some(())?;
            match asg.get(&a) {
                None => {
                    nopen += 1;
                    open = Some((a, p));
                    if nopen > 1 {
                        break;
                    }
                }
                Some(&v) if v == p => {
                    sat = true;
                    break;
                }
                Some(_) => {}
            }
        }
        if sat || nopen > 1 {
            continue;
        }
        match open {
            None => {
                progress.poll().then_some(())?;
                return Some(None);
            }
            Some((a, p)) => {
                asg.insert(a, p);
                sweep.assigned(index, a, budget, progress)?;
            }
        }
    }
    progress.poll().then_some(())?;
    Some(Some(FixedPoint {
        assignment: asg,
        index,
    }))
}

// Outer None is refusal; inner None is genuine satisfying completion.
fn branch_var(
    db: &[Clause],
    asg: &HashMap<T, bool>,
    progress: &EmissionProgress<'_>,
) -> Option<Option<(T, bool)>> {
    for cl in db {
        progress.poll().then_some(())?;
        let mut sat = false;
        let mut open = None;
        for &(a, p) in cl {
            progress.poll().then_some(())?;
            if asg.get(&a) == Some(&p) {
                sat = true;
                break;
            }
            if open.is_none() && !asg.contains_key(&a) {
                open = Some((a, p));
            }
        }
        if !sat {
            if let Some(choice) = open {
                return Some(Some(choice));
            }
        }
    }
    progress.poll().then_some(())?;
    Some(None)
}

/// A satisfying assignment extending `fixed`, `Some(None)` when unsatisfiable,
/// `None` when the budget is exhausted or the original owner refuses.
pub(crate) fn solve(
    db: &[Clause],
    fixed: &HashMap<T, bool>,
    budget: &mut u64,
    progress: &EmissionProgress<'_>,
) -> Option<Option<HashMap<T, bool>>> {
    progress.poll().then_some(())?;
    let index = Occurrences::new(db, budget, progress)?;
    solve_indexed(db, &index, fixed, budget, progress)
}

fn solve_indexed(
    db: &[Clause],
    index: &Occurrences,
    fixed: &HashMap<T, bool>,
    budget: &mut u64,
    progress: &EmissionProgress<'_>,
) -> Option<Option<HashMap<T, bool>>> {
    solve_pending(db, index, Pending::Fresh(fixed.clone()), budget, progress)
}

fn solve_pending<'index>(
    db: &[Clause],
    index: &'index Occurrences,
    pending: Pending<'index>,
    budget: &mut u64,
    progress: &EmissionProgress<'_>,
) -> Option<Option<HashMap<T, bool>>> {
    let mut stack = vec![pending];
    while let Some(pending) = stack.pop() {
        progress.poll().then_some(())?;
        let Some(parent) = propagate(db, index, pending, budget, progress)? else {
            continue;
        };
        match branch_var(db, &parent.assignment, progress)? {
            None => {
                progress.poll().then_some(())?;
                return Some(Some(parent.assignment));
            }
            Some((a, p)) => {
                let other = FixedPoint {
                    assignment: parent.assignment.clone(),
                    index: parent.index,
                };
                stack.push(Pending::Child {
                    parent: other,
                    decision: (a, !p),
                });
                stack.push(Pending::Child {
                    parent,
                    decision: (a, p),
                });
            }
        }
    }
    progress.poll().then_some(())?;
    Some(None)
}

/// Previous restart/blocking enumeration retained as a test-only oracle.
/// Its index remains tied to its exact clause database.
/// The exclusive borrow prevents changing old clauses or pairing this index
/// with another database. Appends extend the same index in original order; no
/// assignments or SAT results survive a solve. The fixed assignment, remaining
/// allowance and original owner also cannot change during the enumeration.
#[cfg(test)]
pub(super) struct Projection<'a, 'caller> {
    db: &'a mut Vec<Clause>,
    base: usize,
    index: Occurrences,
    fixed: &'a HashMap<T, bool>,
    budget: &'a mut u64,
    progress: &'a EmissionProgress<'caller>,
    active: bool,
}

#[cfg(test)]
impl<'a, 'caller> Projection<'a, 'caller> {
    pub(super) fn new(
        db: &'a mut Vec<Clause>,
        fixed: &'a HashMap<T, bool>,
        budget: &'a mut u64,
        progress: &'a EmissionProgress<'caller>,
    ) -> Option<Self> {
        let index = Occurrences::new(db, budget, progress)?;
        Some(Self {
            base: db.len(),
            db,
            index,
            fixed,
            budget,
            progress,
            active: true,
        })
    }

    /// Admit every added literal, possible relocation and occurrence before
    /// use. A partially extended index is never usable after any refusal.
    pub(super) fn append(&mut self, literals: impl Iterator<Item = (T, bool)>) -> Option<()> {
        if !self.active {
            return None;
        }
        self.active = false;
        self.progress.poll().then_some(())?;
        let mut clause = Vec::new();
        for literal in literals {
            reserve(&mut clause, 1, self.budget, self.progress)?;
            clause.push(literal);
        }
        reserve(self.db, 1, self.budget, self.progress)?;
        self.index.append(&clause, self.budget, self.progress)?;
        self.db.push(clause);
        self.progress.poll().then_some(())?;
        self.active = true;
        Some(())
    }

    pub(super) fn solve(&mut self) -> Option<Option<HashMap<T, bool>>> {
        if !self.active {
            return None;
        }
        self.active = false;
        self.progress.poll().then_some(())?;
        let answer = solve_indexed(self.db, &self.index, self.fixed, self.budget, self.progress);
        self.active = answer.is_some();
        answer
    }
}

#[cfg(test)]
impl Drop for Projection<'_, '_> {
    fn drop(&mut self) {
        // Also restore the caller's exact clauses on refusal or observer unwind.
        // Only appended scratch rows are removed; no work receives new credit.
        self.db.truncate(self.base);
    }
}
