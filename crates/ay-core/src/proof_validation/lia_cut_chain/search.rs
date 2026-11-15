// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The search that PROPOSES a cut chain. Untrusted: its output is re-checked
//! by [`super::validate_cut_chain`].
//!
//! Two classical presolve steps, both of which only ever derive Chvátal–Gomory
//! cuts (Savelsbergh, "Preprocessing and probing techniques for mixed integer
//! programming problems", ORSA J. Computing 6(4), 1994; Achterberg,
//! "Constraint Integer Programming", 2007, §10.1):
//!
//! 1. **Exact equality elimination.** An equality row with a `±1` coefficient
//!    determines that atom as an integer combination of the others; it is
//!    substituted into every other row (the same pivot order as the
//!    guarded-split rule), so each remaining row is an integer combination of
//!    clause rows.
//! 2. **Rounded bound propagation over coefficient classes.** Every remaining
//!    row is `Σ a_x·x ≥ r`. For a kept part `K` of it — one class of equal
//!    `|a_x|`, the classes whose coefficient is a multiple of one class's,
//!    or a single atom — the relaxed rest is bounded above by facts already
//!    derived (per atom, or for a whole class on its own primitive form), so
//!    `K ≥ r − U`. Dividing by the content `g` of `K` and rounding up gives a
//!    bound on the primitive form `K/g`; it is a cut when `g ∤ r − U`, and an
//!    exact combination otherwise. A form whose derived lower bound exceeds
//!    its derived upper bound closes the chain.
//!
//! The search computes bounds only; each fact records WHICH row and facts it
//! came from, and multipliers are reconstructed for the facts the final
//! contradiction reaches, and nothing else.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use super::{ChainCut, ChainRow, Coeffs, MAX_CHAIN_CUTS};
use crate::TermId;

/// Propagation passes over every row.
const MAX_ROUNDS: usize = 24;

/// Derived facts, cut or not, before the search gives up.
const MAX_FACTS: usize = 768;

/// Atom visits across the equality elimination and all relaxations before the
/// search gives up, so the strict checker and the funnel pay a bounded,
/// deterministic cost on any clause shape.
const MAX_WORK: usize = 1 << 15;

/// A proposed chain, in [`super::LiaCutChainWitness`]'s layout.
pub(super) struct Chain {
    pub(super) cuts: Vec<ChainCut>,
    pub(super) final_rows: Vec<BigRational>,
    pub(super) final_cuts: Vec<BigRational>,
}

/// A `≥`-row of the eliminated system and its integer multipliers over the
/// clause rows.
#[derive(Clone)]
struct BaseRow {
    form: Coeffs,
    bound: BigInt,
    multipliers: BTreeMap<usize, BigInt>,
}

impl BaseRow {
    /// `self + scale·other`.
    fn add_scaled(&mut self, other: &BaseRow, scale: &BigInt) {
        add_scaled(&mut self.form, &other.form, scale);
        self.bound += &other.bound * scale;
        add_scaled(&mut self.multipliers, &other.multipliers, scale);
    }

    fn negated(&self) -> BaseRow {
        let minus = -BigInt::one();
        let mut out = BaseRow {
            form: Coeffs::new(),
            bound: BigInt::zero(),
            multipliers: BTreeMap::new(),
        };
        out.add_scaled(self, &minus);
        out
    }
}

/// One derived bound `orientation·form ≥ bound` on a primitive form whose
/// first coefficient is positive: `form ≥ bound`, or `−form ≥ bound` when
/// `upper`.
struct Fact {
    form: Coeffs,
    upper: bool,
    bound: BigInt,
    /// `(base row + Σ multiplier·part) / divisor` reads the orientation form
    /// `≥ bound` exactly, or `≥` something `bound` rounds up (`cut`).
    row: usize,
    parts: Vec<(usize, BigInt)>,
    divisor: BigInt,
    cut: bool,
}

/// Propose a cut chain refuting `rows`, or `None`.
pub(super) fn find_chain(rows: &[ChainRow]) -> Option<Chain> {
    let mut work = 0;
    let base = match eliminate(rows, &mut work)? {
        Eliminated::Refuted(multipliers) => {
            return Some(Chain {
                cuts: Vec::new(),
                final_rows: dense(rows.len(), &to_rational(&multipliers)),
                final_cuts: Vec::new(),
            });
        }
        Eliminated::Rows(base) => base,
    };
    let candidates: Vec<Vec<Vec<TermId>>> = base.iter().map(|row| kept_parts(&row.form)).collect();
    let mut search = Search {
        base: &base,
        facts: Vec::new(),
        store: BTreeMap::new(),
        work,
    };
    for (index, row) in base.iter().enumerate() {
        if let Offer::Contradiction(lower, upper) =
            search.offer(row.form.clone(), row.bound.clone(), index, Vec::new())
        {
            return search.chain(rows.len(), lower, upper);
        }
    }
    for _ in 0..MAX_ROUNDS {
        let mut changed = false;
        for (index, kept_sets) in candidates.iter().enumerate() {
            for kept in kept_sets {
                match search.relax(index, kept) {
                    Offer::Contradiction(lower, upper) => {
                        return search.chain(rows.len(), lower, upper);
                    }
                    Offer::Improved => changed = true,
                    Offer::Stale => {}
                }
                if search.facts.len() >= MAX_FACTS || search.work > MAX_WORK {
                    return None;
                }
            }
        }
        if !changed {
            break;
        }
    }
    None
}

enum Eliminated {
    Rows(Vec<BaseRow>),
    /// Integer multipliers of a ground refutation `0 ≥ b > 0`.
    Refuted(BTreeMap<usize, BigInt>),
}

/// Substitute away every equality with a `±1` pivot, then read the rest as
/// `≥`-rows (a residual equality in both directions).
///
/// The substitutions are charged to `work` against [`MAX_WORK`], and `None`
/// declines once they cost more: every pivot scan visits the equality atoms
/// it reads and every remaining row once, and every substitution visits the
/// pivot row's atoms and multipliers. Uncharged, a wide clause of dense
/// unit-pivot equalities paid tens of milliseconds here before the search's
/// own budget was ever consulted.
fn eliminate(rows: &[ChainRow], work: &mut usize) -> Option<Eliminated> {
    let mut eqs = Vec::new();
    let mut ges = Vec::new();
    for (index, row) in rows.iter().enumerate() {
        let base = BaseRow {
            form: row.form.clone(),
            bound: row.bound.clone(),
            multipliers: BTreeMap::from([(index, BigInt::one())]),
        };
        if row.equality {
            eqs.push(base);
        } else {
            ges.push(base);
        }
    }
    for _ in 0..eqs.len() {
        let mut scanned = 0usize;
        let found = eqs.iter().enumerate().find_map(|(index, eq)| {
            eq.form
                .iter()
                .find(|(_, coeff)| {
                    scanned += 1;
                    coeff.abs().is_one()
                })
                .map(|(atom, coeff)| (index, *atom, coeff.clone()))
        });
        *work = work.saturating_add(scanned);
        let Some((index, pivot, k)) = found else {
            break;
        };
        let pivot_row = eqs.swap_remove(index);
        let substitution = pivot_row.form.len() + pivot_row.multipliers.len();
        for row in eqs.iter_mut().chain(ges.iter_mut()) {
            *work = work.saturating_add(1);
            // `row − (m/k)·pivot_row` removes the pivot; exact, `k = ±1`.
            if let Some(m) = row.form.get(&pivot).cloned() {
                *work = work.saturating_add(substitution);
                if *work > MAX_WORK {
                    return None;
                }
                row.add_scaled(&pivot_row, &-(m * &k));
            }
        }
        if *work > MAX_WORK {
            return None;
        }
    }
    let mut base = Vec::new();
    for eq in eqs {
        if eq.form.is_empty() {
            if eq.bound.is_positive() {
                return Some(Eliminated::Refuted(eq.multipliers));
            }
            if eq.bound.is_negative() {
                return Some(Eliminated::Refuted(eq.negated().multipliers));
            }
            continue;
        }
        base.push(eq.negated());
        base.push(eq);
    }
    for ge in ges {
        if ge.form.is_empty() {
            if ge.bound.is_positive() {
                return Some(Eliminated::Refuted(ge.multipliers));
            }
            continue;
        }
        base.push(ge);
    }
    Some(Eliminated::Rows(base))
}

/// The kept parts propagation tries on one row: each class of equal `|a|`,
/// the classes whose coefficient is a multiple of one class's, and each
/// single atom — never the whole row (that is the row's own fact).
fn kept_parts(form: &Coeffs) -> Vec<Vec<TermId>> {
    let classes = classes(form);
    let mut out: Vec<Vec<TermId>> = Vec::new();
    let mut push = |kept: Vec<TermId>| {
        if !kept.is_empty() && kept.len() < form.len() && !out.contains(&kept) {
            out.push(kept);
        }
    };
    for (magnitude, atoms) in &classes {
        push(atoms.clone());
        let multiples = form
            .iter()
            .filter(|(_, coeff)| coeff.abs().is_multiple_of(magnitude))
            .map(|(atom, _)| *atom)
            .collect();
        push(multiples);
    }
    for atom in form.keys() {
        push(vec![*atom]);
    }
    out
}

/// Atoms grouped by `|coefficient|`, each group in form order.
fn classes(form: &Coeffs) -> BTreeMap<BigInt, Vec<TermId>> {
    let mut classes: BTreeMap<BigInt, Vec<TermId>> = BTreeMap::new();
    for (atom, coeff) in form {
        classes.entry(coeff.abs()).or_default().push(*atom);
    }
    classes
}

enum Offer {
    Stale,
    Improved,
    /// Fact indices of a lower and an upper bound that cross.
    Contradiction(usize, usize),
}

struct Search<'a> {
    base: &'a [BaseRow],
    facts: Vec<Fact>,
    /// Primitive form → `[lower, upper]` fact.
    store: BTreeMap<Coeffs, [Option<usize>; 2]>,
    /// Atoms visited so far, against [`MAX_WORK`].
    work: usize,
}

/// `target += scale·source`, dropping entries that cancel.
fn add_scaled<K, V>(target: &mut BTreeMap<K, V>, source: &BTreeMap<K, V>, scale: &V)
where
    K: Ord + Copy,
    V: Clone + Zero + std::ops::AddAssign + for<'a> std::ops::Mul<&'a V, Output = V>,
{
    if scale.is_zero() {
        return;
    }
    for (key, value) in source {
        let entry = target.entry(*key).or_insert_with(V::zero);
        *entry += value.clone() * scale;
        if entry.is_zero() {
            let _ = target.remove(key);
        }
    }
}

/// A sparse multiplier map as a dense vector of `len` entries.
fn dense(len: usize, sparse: &BTreeMap<usize, BigRational>) -> Vec<BigRational> {
    let mut out = vec![BigRational::zero(); len];
    for (index, value) in sparse {
        if let Some(slot) = out.get_mut(*index) {
            *slot = value.clone();
        }
    }
    out
}

fn to_rational(sparse: &BTreeMap<usize, BigInt>) -> BTreeMap<usize, BigRational> {
    sparse
        .iter()
        .map(|(index, value)| (*index, BigRational::from_integer(value.clone())))
        .collect()
}

mod facts;

#[cfg(test)]
mod budget_tests;
