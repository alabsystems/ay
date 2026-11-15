// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integer refutation by lattice closure (an "Omega-lite" procedure).
//!
//! Branch-and-bound cannot refute an integer-infeasible system whose rational
//! relaxation is feasible along an UNBOUNDED direction: every split moves the
//! fractional vertex one unit further out and the loop diverges (the executor's
//! oscillation detector then answers `unknown`). The canonical shape comes from
//! `mod`/`div` elimination: `B = A + C`, `C <= A < C + 1`, `B = 2q + r`, `r = 1`.
//! Over the rationals `A - C` ranges over `[0, 1)`, so the relaxation is
//! feasible for every `C`; over the integers the strict bound tightens to
//! `A - C <= 0`, the pair of bounds forces the implied EQUALITY `A = C`, and the
//! equality lattice `2C = 2q + 1` is empty.
//!
//! [`refute_system`] decides such systems by alternating four integer-exact steps
//! until a contradiction or a fixpoint:
//!
//! 1. **Equality elimination** (exact). Each equality is GCD-checked, divided by
//!    its GCD and eliminated by substituting a unit-coefficient variable. When no
//!    coefficient is a unit, a unimodular change of variables
//!    (`x_k = y - Σ q_i x_i`, the Euclid/"mod-hat" step of the Omega test) shrinks
//!    the smallest coefficient until one is.
//! 2. **Chvátal-Gomory normalisation** of every inequality `a·x <= c`:
//!    `(a/g)·x <= floor(c/g)` with `g = gcd(a)`.
//! 3. **Tight-pair detection**: inequalities on the same primitive linear form
//!    `p·x <= u` and `p·x >= l` refute when `l > u` and yield the implied equality
//!    `p·x = u` when `l == u`, which re-enters step 1. A disequality `p·x != v`
//!    first moves a bound sitting exactly on `v` one step inwards.
//! 4. **Fourier-Motzkin real shadow** on the variable with the cheapest
//!    elimination (exact Omega-test eliminations preferred). Its rows are
//!    nonnegative combinations, so they stay valid for every integer solution.
//!
//! Every derived row carries the set of input rows it depends on; a refutation
//! returns the union for the conflict clause. Each step is implied by the
//! integer semantics of its inputs, so a refutation is SOUND. The procedure is
//! a refutation engine only: an [`Refutation::Open`] answer claims nothing (the
//! real shadow may lose integer information when an elimination is inexact).
//! Resource caps ([`Limits`]) turn blow-up into `Open`, never into a verdict.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};

mod rows;

use rows::{lin_comb, round_div, too_big};
pub(crate) use rows::{IntRow, SourceSet};

/// Resource caps. Hitting any of them yields [`Refutation::Open`].
#[derive(Clone, Debug)]
pub(crate) struct Limits {
    /// Maximum number of inequality rows alive at once (Fourier-Motzkin blow-up).
    pub(crate) max_ineqs: usize,
    /// Maximum bit length of any coefficient or constant.
    pub(crate) max_bits: u64,
    /// Maximum number of row operations over the whole run.
    pub(crate) max_work: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            max_ineqs: 128,
            max_bits: 256,
            max_work: 5_000,
        }
    }
}

/// Outcome of [`refute_system`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Refutation {
    /// The conjunction of the listed input rows has no integer solution.
    Refuted(SourceSet),
    /// No contradiction derived (NOT a satisfiability claim).
    Open,
}

enum Stop {
    Refuted(SourceSet),
    Open,
}

/// The input of [`refute_system`]: equalities `Σ a·x = c`, inequalities
/// `Σ a·x <= c` and disequalities `Σ a·x != c`.
#[derive(Clone, Debug, Default)]
pub(crate) struct System {
    pub(crate) eqs: Vec<IntRow>,
    pub(crate) ineqs: Vec<IntRow>,
    pub(crate) diseqs: Vec<IntRow>,
}

/// Try to refute `eqs ∧ ineqs` over the integers (test convenience).
#[cfg(test)]
pub(crate) fn refute(eqs: Vec<IntRow>, ineqs: Vec<IntRow>, limits: &Limits) -> Refutation {
    let system = System {
        eqs,
        ineqs,
        diseqs: Vec::new(),
    };
    refute_system(system, limits).0
}

/// Try to refute a [`System`]; also returns the work units spent (at most
/// `limits.max_work` plus one step).
pub(crate) fn refute_system(system: System, limits: &Limits) -> (Refutation, usize) {
    let mut closure = Closure {
        eqs: system.eqs,
        ineqs: system.ineqs,
        diseqs: system.diseqs,
        limits,
        work: 0,
    };
    let outcome = match closure.run() {
        Stop::Refuted(sources) => Refutation::Refuted(sources),
        Stop::Open => Refutation::Open,
    };
    (outcome, closure.work)
}

struct Closure<'l> {
    eqs: Vec<IntRow>,
    ineqs: Vec<IntRow>,
    diseqs: Vec<IntRow>,
    limits: &'l Limits,
    work: usize,
}

impl Closure<'_> {
    fn run(&mut self) -> Stop {
        loop {
            if let Err(stop) = self.eliminate_equalities() {
                return stop;
            }
            match self.normalize_inequalities() {
                Err(stop) => return stop,
                Ok(true) => continue,
                Ok(false) => {}
            }
            if self.ineqs.is_empty() {
                return Stop::Open;
            }
            if let Err(stop) = self.fourier_motzkin_step() {
                return stop;
            }
        }
    }

    fn tick(&mut self, ops: usize) -> Result<(), Stop> {
        self.work += ops;
        if self.work > self.limits.max_work {
            return Err(Stop::Open);
        }
        Ok(())
    }

    fn eliminate_equalities(&mut self) -> Result<(), Stop> {
        while let Some(mut eq) = self.eqs.pop() {
            loop {
                self.tick(1 + self.eqs.len() + self.ineqs.len())?;
                if eq.coeffs.is_empty() {
                    if !eq.constant.is_zero() {
                        return Err(Stop::Refuted(eq.sources));
                    }
                    break;
                }
                let g = eq.gcd();
                if !(&eq.constant % &g).is_zero() {
                    return Err(Stop::Refuted(eq.sources));
                }
                if !g.is_one() {
                    for (_, c) in &mut eq.coeffs {
                        *c /= &g;
                    }
                    eq.constant /= &g;
                }
                if let Some(&(var, ref unit)) = eq.coeffs.iter().find(|(_, c)| c.abs().is_one()) {
                    let unit = unit.clone();
                    self.substitute_unit(&eq, var, &unit)?;
                    break;
                }
                self.euclid_reduce(&mut eq)?;
            }
        }
        Ok(())
    }

    /// Eliminate `var` (coefficient `unit = ±1` in `eq`) from every other row:
    /// `R := R - (c·unit)·eq`, which zeroes `var` in `R`.
    fn substitute_unit(&mut self, eq: &IntRow, var: usize, unit: &BigInt) -> Result<(), Stop> {
        let max_bits = self.limits.max_bits;
        let mut overflow = false;
        let rows = self.eqs.iter_mut().chain(self.ineqs.iter_mut());
        for row in rows.chain(self.diseqs.iter_mut()) {
            let Some(c) = row.coeff_of(var) else {
                continue;
            };
            let t = c * unit;
            row.coeffs = lin_comb(&BigInt::one(), &row.coeffs, &-&t, &eq.coeffs);
            row.constant -= &t * &eq.constant;
            row.sources.union_with(&eq.sources);
            overflow |= too_big(row, max_bits);
        }
        if overflow {
            return Err(Stop::Open);
        }
        Ok(())
    }

    /// One Euclid step on an equality without unit coefficients: with `m` the
    /// smallest coefficient (on `x_k`), substitute `x_k = y - Σ q_i x_i`
    /// (`q_i = round(a_i / m)`, `y` reusing index `k`) in EVERY row. The map is
    /// unimodular (a bijection of the integer lattice), so it needs no sources;
    /// afterwards `eq`'s other coefficients are the remainders `|a_i - q_i m| <= |m|/2`.
    fn euclid_reduce(&mut self, eq: &mut IntRow) -> Result<(), Stop> {
        let Some((k, m)) = eq
            .coeffs
            .iter()
            .min_by(|(va, a), (vb, b)| a.abs().cmp(&b.abs()).then(va.cmp(vb)))
            .map(|(v, c)| (*v, c.clone()))
        else {
            return Ok(());
        };
        let quotients: Vec<(usize, BigInt)> = eq
            .coeffs
            .iter()
            .filter(|(v, _)| *v != k)
            .map(|(v, c)| (*v, round_div(c, &m)))
            .filter(|(_, q)| !q.is_zero())
            .collect();
        let apply = |row: &mut IntRow| {
            if let Some(c) = row.coeff_of(k).cloned() {
                row.coeffs = lin_comb(&BigInt::one(), &row.coeffs, &-c, &quotients);
            }
        };
        let max_bits = self.limits.max_bits;
        apply(&mut *eq);
        let mut overflow = too_big(eq, max_bits);
        let rows = self.eqs.iter_mut().chain(self.ineqs.iter_mut());
        for row in rows.chain(self.diseqs.iter_mut()) {
            apply(row);
            overflow |= too_big(row, max_bits);
        }
        if overflow {
            return Err(Stop::Open);
        }
        Ok(())
    }

    /// Normalise every inequality, keep only the tightest bound per primitive
    /// form and direction, and turn tight pairs into equalities.
    /// Returns `Ok(true)` when new equalities were queued.
    fn normalize_inequalities(&mut self) -> Result<bool, Stop> {
        // Primitive form `p` (first coefficient positive) -> the tightest
        // `p·x <= c` (slot 0) and the tightest `-p·x <= c` (slot 1).
        type Tightest = Option<(BigInt, SourceSet)>;
        let mut table: BTreeMap<Vec<(usize, BigInt)>, [Tightest; 2]> = BTreeMap::new();
        let holes = self.normalize_disequalities()?;
        let rows = std::mem::take(&mut self.ineqs);
        self.tick(rows.len())?;
        for row in rows {
            if row.coeffs.is_empty() {
                if row.constant.is_negative() {
                    return Err(Stop::Refuted(row.sources));
                }
                continue;
            }
            let g = row.gcd();
            let side = usize::from(row.coeffs[0].1.is_negative());
            let divisor = if side == 1 { -&g } else { g.clone() };
            let key = row.coeffs.iter().map(|(v, c)| (*v, c / &divisor)).collect();
            let bound = row.constant.div_floor(&g);
            let slot = &mut table.entry(key).or_default()[side];
            let tighter = slot.as_ref().is_none_or(|(cur, src)| {
                bound < *cur || (bound == *cur && row.sources.len() < src.len())
            });
            if tighter {
                *slot = Some((bound, row.sources));
            }
        }
        let mut found_eq = false;
        for (key, [mut upper, mut lower]) in table {
            if let Some(holes) = holes.get(&key) {
                step_off_holes(&mut upper, &mut lower, holes);
            }
            if let (Some((u, su)), Some((l, sl))) = (&upper, &lower) {
                // p·x <= u and p·x >= -l.
                let slack = u + l;
                if slack.is_negative() {
                    return Err(Stop::Refuted(su.joined(sl)));
                }
                if slack.is_zero() {
                    self.eqs.push(IntRow {
                        coeffs: key,
                        constant: u.clone(),
                        sources: su.joined(sl),
                    });
                    found_eq = true;
                    continue;
                }
            }
            if let Some((l, sl)) = lower {
                let coeffs = key.iter().map(|(v, c)| (*v, -c)).collect();
                self.ineqs.push(IntRow {
                    coeffs,
                    constant: l,
                    sources: sl,
                });
            }
            if let Some((u, su)) = upper {
                self.ineqs.push(IntRow {
                    coeffs: key,
                    constant: u,
                    sources: su,
                });
            }
        }
        Ok(found_eq)
    }

    /// Normalise every disequality to `p·x != v` over a primitive form `p`
    /// (first coefficient positive). A disequality whose GCD does not divide
    /// its constant always holds and is dropped; `0 != 0` refutes.
    fn normalize_disequalities(&mut self) -> Result<Holes, Stop> {
        let mut holes = Holes::new();
        let rows = std::mem::take(&mut self.diseqs);
        self.tick(rows.len())?;
        for row in rows {
            if row.coeffs.is_empty() {
                if row.constant.is_zero() {
                    return Err(Stop::Refuted(row.sources));
                }
                continue;
            }
            let g = row.gcd();
            if !(&row.constant % &g).is_zero() {
                continue;
            }
            let divisor = if row.coeffs[0].1.is_negative() { -g } else { g };
            let coeffs: Vec<(usize, BigInt)> =
                row.coeffs.iter().map(|(v, c)| (*v, c / &divisor)).collect();
            let value = &row.constant / &divisor;
            self.diseqs.push(IntRow {
                coeffs: coeffs.clone(),
                constant: value.clone(),
                sources: row.sources.clone(),
            });
            holes.entry(coeffs).or_default().push((value, row.sources));
        }
        Ok(holes)
    }

    /// Eliminate one variable from the inequalities (real shadow).
    fn fourier_motzkin_step(&mut self) -> Result<(), Stop> {
        // var -> (#positive, #negative, all positive are +1, all negative are -1)
        let mut stats: BTreeMap<usize, (usize, usize, bool, bool)> = BTreeMap::new();
        for row in &self.ineqs {
            for (v, c) in &row.coeffs {
                let s = stats.entry(*v).or_insert((0, 0, true, true));
                if c.is_positive() {
                    s.0 += 1;
                    s.2 &= c.is_one();
                } else {
                    s.1 += 1;
                    s.3 &= (-c).is_one();
                }
            }
        }
        // A variable bounded on one side only projects away exactly.
        if let Some((&var, _)) = stats.iter().find(|(_, s)| s.0 == 0 || s.1 == 0) {
            self.ineqs.retain(|row| row.coeff_of(var).is_none());
            self.diseqs.retain(|row| row.coeff_of(var).is_none());
            return Ok(());
        }
        let (&var, _) = stats
            .iter()
            .min_by_key(|(v, s)| (!(s.2 || s.3), s.0 * s.1, **v))
            .ok_or(Stop::Open)?;
        let (mut pos, mut neg, mut rest) = (Vec::new(), Vec::new(), Vec::new());
        for row in std::mem::take(&mut self.ineqs) {
            let direction = row.coeff_of(var).map(Signed::is_positive);
            match direction {
                Some(true) => pos.push(row),
                Some(false) => neg.push(row),
                None => rest.push(row),
            }
        }
        if rest.len() + pos.len() * neg.len() > self.limits.max_ineqs {
            return Err(Stop::Open);
        }
        self.diseqs.retain(|row| row.coeff_of(var).is_none());
        self.tick(pos.len() * neg.len())?;
        for p in &pos {
            let a = p.coeff_of(var).cloned().unwrap_or_default();
            for n in &neg {
                let b = -n.coeff_of(var).cloned().unwrap_or_default();
                let g = a.gcd(&b);
                let (mp, mn) = (&b / &g, &a / &g);
                let row = IntRow {
                    coeffs: lin_comb(&mp, &p.coeffs, &mn, &n.coeffs),
                    constant: &mp * &p.constant + &mn * &n.constant,
                    sources: p.sources.joined(&n.sources),
                };
                if too_big(&row, self.limits.max_bits) {
                    return Err(Stop::Open);
                }
                rest.push(row);
            }
        }
        self.ineqs = rest;
        Ok(())
    }
}

/// Primitive form -> excluded values (with sources) from disequalities.
type Holes = BTreeMap<Vec<(usize, BigInt)>, Vec<(BigInt, SourceSet)>>;

/// Tighten `p·x <= u` (`upper`) and `-p·x <= c` (`lower`, i.e. `p·x >= -c`)
/// past excluded values: `p·x <= u ∧ p·x != u` gives `p·x <= u - 1` (and
/// symmetrically), each step joining the disequality's sources.
fn step_off_holes(
    upper: &mut Option<(BigInt, SourceSet)>,
    lower: &mut Option<(BigInt, SourceSet)>,
    holes: &[(BigInt, SourceSet)],
) {
    loop {
        let mut moved = false;
        if let Some((u, su)) = upper.as_mut() {
            if let Some((_, hole_src)) = holes.iter().find(|(v, _)| *v == *u) {
                *u -= BigInt::one();
                su.union_with(hole_src);
                moved = true;
            }
        }
        if let Some((c, sc)) = lower.as_mut() {
            if let Some((_, hole_src)) = holes.iter().find(|(v, _)| *v == -&*c) {
                *c -= BigInt::one();
                sc.union_with(hole_src);
                moved = true;
            }
        }
        if !moved {
            return;
        }
    }
}

#[cfg(test)]
#[path = "lattice_refute_tests.rs"]
mod tests;
