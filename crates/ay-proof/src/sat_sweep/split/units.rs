// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The values a leaf's or a conflict's derivation rests on, each RECORDED
//! as its own widened step or INLINED as its derivation, whichever prints
//! less (`worth_recording`).
//!
//! ## Why not one step per value
//!
//! A value the leaf needs is the end of a propagation chain from the path:
//! an `xnor` forced true because its word equality was, because a guard was
//! false. Recorded one step per propagated value, proof_gate_strict row
//! 1257's printed document spent 18 MB on 74,000 such steps, most of them
//! single-use wires; inlined, a wire costs its consumer one more hint.

use super::super::*;
use super::node::{lit_value, Propagated};
use super::pool::Pool;

/// What a leaf has derived so far.
pub(super) struct Derived<'l> {
    pub(super) pool: &'l Pool,
    pub(super) prop: &'l Propagated,
    /// `¬p` for every path literal `p`.
    pub(super) widen: Vec<Literal>,
    /// The hints that derive each assigned variable's value.
    pub(super) units: DetHashMap<usize, Vec<u64>>,
    /// The representative of each rewritten literal.
    pub(super) rep: DetHashMap<Literal, Literal>,
    /// The next literal toward a literal's representative, and the pool
    /// clause of that implication.
    pub(super) toward: DetHashMap<Literal, (Literal, usize)>,
    pub(super) shortcuts: DetHashMap<Literal, u64>,
}

impl<'l> Derived<'l> {
    pub(super) fn new(pool: &'l Pool, prop: &'l Propagated, path: &[Literal]) -> Self {
        Self {
            pool,
            prop,
            widen: path.iter().map(|lit| lit.negated()).collect(),
            units: DetHashMap::default(),
            rep: DetHashMap::default(),
            toward: DetHashMap::default(),
            shortcuts: DetHashMap::default(),
        }
    }
}

impl Sweep<'_, '_> {
    /// The clause refuting `path` when propagation under it falsified pool
    /// clause `conflict`: the conflict and the values of its literals, each
    /// recorded or inlined as a leaf's are (`leaf_units`).
    pub(super) fn refute_by_propagation(
        &mut self,
        pool: &Pool,
        state: &Propagated,
        path: &[Literal],
        conflict: usize,
    ) -> Option<u64> {
        let mut derived = Derived::new(pool, state, path);
        let demand: Vec<usize> = pool.clauses[conflict]
            .iter()
            .map(|lit| lit.variable().index())
            .collect();
        self.leaf_units(&mut derived, &demand)?;
        let mut hints: Vec<u64> = Vec::new();
        for &var in &demand {
            hints.extend(derived.units.get(&var)?.iter().copied());
        }
        hints.push(pool.ids[conflict]);
        let widen = derived.widen.clone();
        self.record_chain(&widen, &hints)
    }

    /// The hints that derive `var`'s value under the path (`leaf_units`
    /// has made them).
    pub(super) fn unit_hints(&mut self, derived: &mut Derived<'_>, var: usize) -> Option<Vec<u64>> {
        derived.units.get(&var).cloned()
    }

    /// Make the hints for every value in `demand` and every value those rest
    /// on: nothing for a path literal; otherwise the hints of its reason's
    /// other values and the reason. A value is RECORDED as its own step when
    /// the steps that need it would repeat its derivation at more cost than
    /// the step (`worth_recording`), and inlined otherwise.
    pub(super) fn leaf_units(&mut self, derived: &mut Derived<'_>, demand: &[usize]) -> Option<()> {
        let pool = derived.pool;
        let prop = derived.prop;
        // Every value needed, reasons before what they imply, and how many
        // times each is referred to.
        let mut order: Vec<usize> = Vec::new();
        let mut uses: DetHashMap<usize, usize> = DetHashMap::default();
        let mut expanded: DetHashSet<usize> = DetHashSet::default();
        let mut stack: Vec<(usize, bool)> = Vec::new();
        for &var in demand {
            *uses.entry(var).or_insert(0) += 1;
            stack.push((var, false));
        }
        while let Some((at, done)) = stack.pop() {
            if done {
                order.push(at);
                continue;
            }
            if derived.units.contains_key(&at) || !expanded.insert(at) {
                continue;
            }
            stack.push((at, true));
            if let Some(reason) = prop.reason_of[at] {
                for lit in &pool.clauses[reason] {
                    let other = lit.variable().index();
                    if other != at {
                        *uses.entry(other).or_insert(0) += 1;
                        stack.push((other, false));
                    }
                }
            }
        }
        for at in order {
            let Some(reason) = prop.reason_of[at] else {
                derived.units.insert(at, Vec::new());
                continue;
            };
            let mut hints: Vec<u64> = Vec::new();
            for lit in &pool.clauses[reason] {
                let other = lit.variable().index();
                if other != at {
                    hints.extend(derived.units.get(&other)?.iter().copied());
                }
            }
            hints.push(pool.ids[reason]);
            let clause_literals = 1 + derived.widen.len().min(8);
            // A reason that repeats a variable prints a gate twice, which the
            // transport can only resolve in binary steps: kept in its own
            // step, it never turns a long chain binary.
            let repeats = repeats_variable(&pool.clauses[reason]);
            if repeats
                || worth_recording(
                    uses.get(&at).copied().unwrap_or(1),
                    hints.len(),
                    clause_literals,
                )
            {
                let implied = literal(at, !prop.value[at]?);
                debug_assert_eq!(lit_value(&prop.value, implied), Some(true));
                let mut target = vec![implied];
                target.extend(derived.widen.iter().copied());
                hints = vec![self.record_chain(&target, &hints)?];
            }
            derived.units.insert(at, hints);
        }
        Some(())
    }
}

fn repeats_variable(clause: &[Literal]) -> bool {
    clause.iter().enumerate().any(|(at, lit)| {
        clause[..at]
            .iter()
            .any(|other| other.variable() == lit.variable())
    })
}

/// Whether a value `uses` steps need, derived by `hints` hints, costs less
/// recorded once (a step of about `literals` literals, then one hint per
/// use) than repeated inline in each. A printed hint costs about as much as
/// a clause literal and a third of a step's own overhead.
fn worth_recording(uses: usize, hints: usize, literals: usize) -> bool {
    const INLINE_CAP: usize = 48;
    hints > INLINE_CAP || uses.saturating_mul(hints.saturating_sub(1)) > 3 + hints + literals / 2
}
