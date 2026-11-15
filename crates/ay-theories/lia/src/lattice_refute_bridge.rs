// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LIA bridge for the lattice-closure refutation engine ([`crate::lattice_refute`]).
//!
//! Branch-and-bound diverges on an integer-infeasible system whose relaxation
//! stays feasible along an unbounded direction; the executor's oscillation
//! detector then gives up with `unknown`. Before the solver hands out a split on
//! an UNBOUNDED variable, [`LiaSolver::lattice_refutation_before_split`] runs the
//! closure over the asserted linear atoms and, on a refutation, returns a
//! conflict made only of asserted literals (deletion-minimised when small).
//!
//! Gates keep the cost off the hot path: only splits on a variable missing an
//! LRA bound can diverge; only small systems are collected; and a deterministic
//! work budget (`BUDGET_BASE` plus `BUDGET_PER_SPLIT` per split
//! opportunity, carried in [`crate::DiophState`] across the split loop's
//! per-round solver rebuilds) bounds the amortised cost per split.

use super::*;
use crate::lattice_refute::{refute_system, IntRow, Limits, Refutation, SourceSet, System};

/// Largest number of distinct asserted linear atoms the closure collects.
const MAX_ROWS: usize = 96;
/// Largest number of distinct integer terms the closure collects.
const MAX_VARS: usize = 32;
/// Cores up to this size are deletion-minimised.
const MAX_MINIMIZE: usize = 16;
/// Work units always available to the closure.
const BUDGET_BASE: u64 = 10_000;
/// Work units added to the budget per split opportunity.
const BUDGET_PER_SPLIT: u64 = 250;

impl LiaSolver<'_> {
    /// [`Self::lattice_refutation_before_split`] at most once per `check()`
    /// (`tried` is the caller's per-check flag), as a ready `Unsat` result.
    pub(crate) fn lattice_once(
        &mut self,
        tried: &mut bool,
        split_var: TermId,
    ) -> Option<TheoryResult> {
        if !self.lattice_closure || std::mem::replace(tried, true) {
            return None;
        }
        self.lattice_refutation_before_split(split_var)
            .map(TheoryResult::Unsat)
    }

    /// Refute the current assertions by lattice closure before a split on
    /// `split_var` is issued. `Some(conflict)` is a set of asserted literals
    /// with no integer solution; `None` claims nothing.
    pub(crate) fn lattice_refutation_before_split(
        &mut self,
        split_var: TermId,
    ) -> Option<Vec<TheoryLit>> {
        let bounded = matches!(self.lra.get_bounds_ref(split_var), Some((Some(_), Some(_))));
        if bounded {
            return None;
        }
        let (spent, seen) = &mut self.lattice_budget;
        *seen += 1;
        if *spent > BUDGET_BASE + BUDGET_PER_SPLIT * *seen {
            instrument::bump(&instrument::LATTICE_REFUTE_SKIPS);
            return None;
        }
        instrument::bump(&instrument::LATTICE_REFUTE_RUNS);
        let (conflict, work) = self.try_lattice_refutation();
        self.lattice_budget.0 += work as u64;
        if conflict.is_some() {
            instrument::bump(&instrument::LATTICE_REFUTE_HITS);
        }
        conflict
    }

    /// The refutation (if any) and the work units spent on it.
    fn try_lattice_refutation(&self) -> (Option<Vec<TheoryLit>>, usize) {
        let Some((lits, system)) = self.collect_lattice_rows() else {
            return (None, 0);
        };
        let limits = Limits::default();
        let (outcome, mut work) = refute_system(system.clone(), &limits);
        let Refutation::Refuted(mut core) = outcome else {
            return (None, work);
        };
        if core.len() <= MAX_MINIMIZE {
            let (minimal, extra) = minimize_core(core, &system, &limits);
            core = minimal;
            work += extra;
        }
        (Some(core.iter().map(|i| lits[i]).collect()), work)
    }

    /// Asserted Int-sorted equalities, disequalities and inequalities as
    /// integer rows. Each row's source is its index in the returned literal
    /// list. `None` when the system is empty or exceeds the size gate.
    fn collect_lattice_rows(&self) -> Option<(Vec<TheoryLit>, System)> {
        let mut var_index: HashMap<TermId, usize> = HashMap::default();
        let mut seen: HashSet<(TermId, bool)> = HashSet::default();
        let (mut lits, mut system) = (Vec::new(), System::default());
        for &(atom, value) in &self.asserted {
            if lits.len() > MAX_ROWS || var_index.len() > MAX_VARS {
                return None;
            }
            if !seen.insert((atom, value)) {
                continue;
            }
            let TermData::App(Symbol::Named(name), args) = self.terms().get(atom) else {
                continue;
            };
            let op = name.as_str();
            if args.len() != 2 || !matches!(op, "=" | "<=" | "<" | ">=" | ">") {
                continue;
            }
            if *self.terms().sort(args[0]) != Sort::Int || *self.terms().sort(args[1]) != Sort::Int
            {
                continue;
            }
            let Some((coeffs, k)) =
                self.integer_linear_difference(args[0], args[1], &mut var_index)
            else {
                continue;
            };
            let sources = SourceSet::single(lits.len());
            lits.push(TheoryLit::new(atom, value));
            let negated = || coeffs.iter().map(|(v, c)| (*v, -c)).collect::<Vec<_>>();
            // The atom reads `Σ coeffs·x + k  op  0`.
            let row = match (op, value) {
                ("=", true) => {
                    system.eqs.push(IntRow::new(coeffs.clone(), -&k, sources));
                    continue;
                }
                ("=", false) => {
                    system
                        .diseqs
                        .push(IntRow::new(coeffs.clone(), -&k, sources));
                    continue;
                }
                ("<=", true) | (">", false) => IntRow::new(coeffs.clone(), -&k, sources),
                ("<", true) | (">=", false) => {
                    IntRow::new(coeffs.clone(), -&k - BigInt::one(), sources)
                }
                (">=", true) | ("<", false) => IntRow::new(negated(), k, sources),
                _ => IntRow::new(negated(), k - BigInt::one(), sources), // (">", true) | ("<=", false)
            };
            system.ineqs.push(row);
        }
        if lits.len() > MAX_ROWS || var_index.len() > MAX_VARS || lits.is_empty() {
            return None;
        }
        Some((lits, system))
    }

    /// `lhs - rhs` as integer coefficients over Int-sorted terms plus an
    /// integer constant, scaled by the common denominator. `None` when a
    /// non-Int term occurs.
    fn integer_linear_difference(
        &self,
        lhs: TermId,
        rhs: TermId,
        var_index: &mut HashMap<TermId, usize>,
    ) -> Option<(Vec<(usize, BigInt)>, BigInt)> {
        let left = self.term_to_linear_coeffs(lhs);
        let right = self.term_to_linear_coeffs(rhs);
        let mut diff: Vec<(TermId, BigRational)> = left.vars.into_iter().collect();
        diff.extend(right.vars.into_iter().map(|(t, c)| (t, -c)));
        let constant = left.constant - right.constant;
        let mut denom = constant.denom().clone();
        for (term, c) in &diff {
            if *self.terms().sort(*term) != Sort::Int {
                return None;
            }
            denom = denom.lcm(c.denom());
        }
        let scale = BigRational::from(denom);
        let mut coeffs = Vec::with_capacity(diff.len());
        diff.sort_by_key(|(t, _)| t.0);
        for (term, c) in diff {
            let next = var_index.len();
            let idx = *var_index.entry(term).or_insert(next);
            coeffs.push((idx, (c * &scale).to_integer()));
        }
        Some((coeffs, (constant * scale).to_integer()))
    }
}

/// Deletion-based minimisation: drop each member whose removal keeps the
/// remaining rows refutable. The result is a subset of `core` that is still
/// refuted by the engine (each accepted step re-derives the contradiction).
/// Also returns the work units spent.
fn minimize_core(core: SourceSet, system: &System, limits: &Limits) -> (SourceSet, usize) {
    let members: Vec<usize> = core.iter().collect();
    let mut current = core;
    let mut work = 0;
    for candidate in members {
        let keep: Vec<usize> = current.iter().filter(|&s| s != candidate).collect();
        if keep.len() == current.len() {
            continue;
        }
        let pick = |rows: &[IntRow]| -> Vec<IntRow> {
            rows.iter()
                .filter(|r| r.sources.iter().all(|s| keep.binary_search(&s).is_ok()))
                .cloned()
                .collect()
        };
        let subsystem = System {
            eqs: pick(&system.eqs),
            ineqs: pick(&system.ineqs),
            diseqs: pick(&system.diseqs),
        };
        let (outcome, spent) = refute_system(subsystem, limits);
        work += spent;
        if let Refutation::Refuted(smaller) = outcome {
            current = smaller;
        }
    }
    (current, work)
}
