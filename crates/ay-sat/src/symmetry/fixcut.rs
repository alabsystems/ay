// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Fix-and-cut over the Schreier–Sims chain (symmetry fixing, step 3).
//!
//! Satsuma's `fix_and_cut` (symmetries.h) over the signed automorphisms ay's
//! IR finder verifies: permutations of the literals that commute with
//! negation. The walk keeps a base of literals; at each step it takes the
//! orbits of the pointwise stabilizer of the base and either
//!
//! - **fixes** on a clause: some clause lies inside one literal orbit —
//!   every model satisfies one of its literals, and a stabilizer element
//!   carries that literal onto the clause's literal `v`, so WLOG `v` is
//!   true (a unit; when the clause's literals are pairwise exclusive the
//!   others are false as well);
//! - **fixes** on a negation: `¬v` lies in the orbit of `v`, so WLOG `v` is
//!   true (Satsuma's negation fixing, the source of every unit it derives
//!   on xor_op); or
//! - **cuts**: neither — WLOG `v` is at least every `w` in its orbit (the
//!   binaries `v ∨ ¬w`), the lex-leader constraint of the transversal
//!   element carrying `v` to `w` under an order that puts the base first;
//!
//! then extends the base by `v` and continues in the stabilizer (which also
//! fixes `¬v`, the permutations commuting with negation). Every
//! constraint is a lex-leader consequence under the single order "base in
//! walk order, then the rest", so the set is satisfiability-preserving as a
//! whole. Fixings are RUP from the cut binaries and the clause; the proof
//! (step 4) will write each binary as a dominance step with the transversal
//! element as its witness, which is why `ops` and the chain are kept.
//!
//! Soundness rests on the generators being verified automorphisms of the
//! formula the walk sees (root, irredundant, unit-free), and on the chain's
//! level orbits being orbits of real group elements: an incomplete chain
//! only makes an orbit smaller, never wrong. Points are literal indices
//! (`Literal::index`), so the domain has twice the variables.

use std::collections::{BTreeMap, HashSet};

use super::schreier::{Orbits, Perm, SchreierSims};
use crate::{Literal, Variable};

/// Clauses longer than this are never checked for pairwise exclusion.
const AMO_MAX_LITERALS: usize = 12;
/// How many applicable clauses to look past the first one for an exclusive
/// (at-most-one) clause, which fixes a whole orbit at once.
const AMO_LOOKAHEAD: u32 = 64;

/// What the walk did at one base point.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LevelOp {
    /// WLOG the clause's literal on the base variable is true.
    Fix { clause: usize, amo: bool },
    /// `¬base` is in the base literal's orbit: WLOG it is true.
    NegationFix,
    /// A flip of `support` variables carries `¬base` to `base`: WLOG true.
    FlipFix { support: u32 },
    /// The orbit binaries `base ∨ ¬w`.
    Cut,
    /// The base point was taken but the chain's transversal missed a literal
    /// of the clause, so nothing was emitted for it.
    Skip,
}

/// One derived clause with its certificate: an SR step whose witness is the
/// automorphism that justifies it (the DSR token layout: the pivot twice,
/// then `literal, image` pairs), or a RUP step when `witness` is empty.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Step {
    pub(crate) clause: Vec<Literal>,
    pub(crate) witness: Vec<Literal>,
}

impl Step {
    fn rup(clause: Vec<Literal>) -> Self {
        Self {
            clause,
            witness: Vec::new(),
        }
    }

    /// An SR step justified by the literal permutation `pairs` (point index
    /// to image index).
    fn sr(clause: Vec<Literal>, pairs: impl IntoIterator<Item = (u32, u32)>) -> Self {
        let pivot = clause[0];
        let mut witness = vec![pivot, pivot];
        for (x, y) in pairs {
            witness.push(Literal::from_index(x as usize));
            witness.push(Literal::from_index(y as usize));
        }
        Self { clause, witness }
    }
}

/// The walk's output.
#[derive(Clone, Debug, Default)]
pub(crate) struct FixAndCut {
    /// Every derived clause in derivation order, each with its certificate.
    pub(crate) steps: Vec<Step>,
    /// WLOG units (fixings and their at-most-one consequences).
    pub(crate) units: Vec<Literal>,
    /// Orbit binaries `[v, ¬w]`.
    pub(crate) binaries: Vec<[Literal; 2]>,
    /// The base literals (indices), in walk order: the head of the
    /// lex-leader order.
    pub(crate) base: Vec<u32>,
    /// One entry per base point.
    pub(crate) ops: Vec<LevelOp>,
    pub(crate) fixings: u64,
    pub(crate) cuts: u64,
    pub(crate) work: u64,
    pub(crate) budget_hit: bool,
    /// Detection rounds run (1 unless a round derived units).
    pub(crate) rounds: u32,
}

impl FixAndCut {
    /// Append a later round's output (its steps follow ours in derivation
    /// order, which is what the proof needs).
    pub(crate) fn absorb(&mut self, later: FixAndCut) {
        self.steps.extend(later.steps);
        self.units.extend(later.units);
        self.binaries.extend(later.binaries);
        self.base.extend(later.base);
        self.ops.extend(later.ops);
        self.fixings += later.fixings;
        self.cuts += later.cuts;
        self.work += later.work;
        self.budget_hit |= later.budget_hit;
        self.rounds += later.rounds.max(1);
    }
}

/// The residual formula after asserting `units` and propagating: satisfied
/// clauses dropped, false literals removed, new unit clauses asserted in
/// turn. `None` when propagation reaches a conflict (the solver's own
/// propagation will find it; nothing to detect on).
pub(crate) fn simplify_by_units(
    clauses: &[Vec<Literal>],
    units: &[Literal],
    num_vars: u32,
) -> Option<Vec<Vec<Literal>>> {
    let mut value = vec![0i8; num_vars as usize];
    let assign = |l: Literal, value: &mut Vec<i8>| -> bool {
        let v = l.variable().index();
        let want = if l.is_positive() { 1 } else { -1 };
        match value.get(v) {
            Some(0) => {
                value[v] = want;
                true
            }
            Some(&cur) => cur == want,
            None => false,
        }
    };
    for &u in units {
        if !assign(u, &mut value) {
            return None;
        }
    }
    let mut current: Vec<Vec<Literal>> = clauses.to_vec();
    loop {
        let mut next: Vec<Vec<Literal>> = Vec::with_capacity(current.len());
        let mut new_units = 0usize;
        for clause in &current {
            let mut reduced: Vec<Literal> = Vec::with_capacity(clause.len());
            let mut satisfied = false;
            for &l in clause {
                match value.get(l.variable().index()).copied().unwrap_or(0) {
                    0 => reduced.push(l),
                    v if (v > 0) == l.is_positive() => {
                        satisfied = true;
                        break;
                    }
                    _ => {}
                }
            }
            if satisfied {
                continue;
            }
            match reduced.len() {
                0 => return None,
                1 => {
                    if !assign(reduced[0], &mut value) {
                        return None;
                    }
                    new_units += 1;
                }
                _ => next.push(reduced),
            }
        }
        current = next;
        if new_units == 0 {
            return Some(current);
        }
    }
}

#[cfg(test)]
/// Run the walk over signed `generators` (sparse literal maps, closed under
/// negation) on a formula over `num_vars` variables. Returns the
/// constraints and the chain (for step 4's witnesses).
pub(crate) fn fix_and_cut(
    clauses: &[Vec<Literal>],
    generators: &[BTreeMap<Literal, Literal>],
    num_vars: u32,
    seed: u64,
    budget: u64,
) -> (FixAndCut, SchreierSims) {
    fix_and_cut_with_flips(
        clauses,
        generators,
        super::flips::FlipGroup::default(),
        num_vars,
        seed,
        budget,
    )
}

/// As `fix_and_cut`, then the flip group's negation fixings: the chain walk
/// first (few generators, short base), then the flips that fix the chain's
/// base variables — they preserve every constraint derived so far — give
/// one unit per remaining rank. The order is the chain's base, then the
/// flip-fixed variables.
pub(crate) fn fix_and_cut_with_flips(
    clauses: &[Vec<Literal>],
    generators: &[BTreeMap<Literal, Literal>],
    mut flips: super::flips::FlipGroup,
    num_vars: u32,
    seed: u64,
    budget: u64,
) -> (FixAndCut, SchreierSims) {
    let mut chain = SchreierSims::new(seed);
    for g in generators {
        let map: BTreeMap<u32, u32> = g
            .iter()
            .map(|(a, b)| (a.index() as u32, b.index() as u32))
            .collect();
        chain.add_generator(Perm::from_map(&map));
    }
    chain.settle();
    let mut walk = Walk::new(clauses, num_vars, budget);
    walk.run(&mut chain);
    let mut out = walk.finish();
    if flips.rank() > 0 {
        let base_vars: Vec<u32> = out
            .base
            .iter()
            .map(|&l| Literal::from_index(l as usize).variable().index() as u32)
            .collect();
        flips.restrict_to_fixing(&base_vars, &mut out.work);
        for (unit, witness) in flips.fixings(&mut out.work) {
            out.steps.push(Step::sr(
                vec![unit],
                witness.iter().map(|&x| {
                    let var = Variable(x);
                    (
                        Literal::positive(var).index() as u32,
                        Literal::negative(var).index() as u32,
                    )
                }),
            ));
            out.units.push(unit);
            out.fixings += 1;
            out.base.push(unit.index() as u32);
            out.ops.push(LevelOp::FlipFix {
                support: witness.len() as u32,
            });
        }
    }
    (out, chain)
}

#[cfg(test)]
/// Lift sign-preserving variable permutations to literal maps.
pub(crate) fn lift_variable_generators(
    generators: &[BTreeMap<Variable, Variable>],
) -> Vec<BTreeMap<Literal, Literal>> {
    generators
        .iter()
        .map(|g| {
            g.iter()
                .flat_map(|(&a, &b)| {
                    [
                        (Literal::positive(a), Literal::positive(b)),
                        (Literal::negative(a), Literal::negative(b)),
                    ]
                })
                .collect()
        })
        .collect()
}

struct Walk<'a> {
    clauses: &'a [Vec<Literal>],
    num_vars: u32,
    /// Variable -> clauses containing it.
    occ: Vec<Vec<u32>>,
    /// Binary clauses as sorted raw literal pairs, for at-most-one checks.
    binaries: HashSet<(u32, u32)>,
    /// +1 true, -1 false, 0 open.
    fixed: Vec<i8>,
    /// Locality score: clauses shared with base variables so far.
    score: Vec<u32>,
    marked: Vec<bool>,
    first_clause: usize,
    budget: u64,
    out: FixAndCut,
}

impl<'a> Walk<'a> {
    fn new(clauses: &'a [Vec<Literal>], num_vars: u32, budget: u64) -> Self {
        let n = num_vars as usize;
        let mut occ: Vec<Vec<u32>> = vec![Vec::new(); n];
        let mut binaries = HashSet::new();
        for (ci, c) in clauses.iter().enumerate() {
            for l in c {
                if let Some(o) = occ.get_mut(l.variable().index()) {
                    o.push(ci as u32);
                }
            }
            if let [a, b] = c.as_slice() {
                binaries.insert(sorted_pair(*a, *b));
            }
        }
        Self {
            clauses,
            num_vars,
            occ,
            binaries,
            fixed: vec![0; n],
            score: vec![0; n],
            marked: vec![false; clauses.len()],
            first_clause: 0,
            budget,
            out: FixAndCut::default(),
        }
    }

    fn finish(self) -> FixAndCut {
        self.out
    }

    fn run(&mut self, chain: &mut SchreierSims) {
        let mut steps = 0u32;
        loop {
            if self.out.work + chain.work() > self.budget {
                self.out.budget_hit = true;
                break;
            }
            if steps >= self.num_vars {
                break;
            }
            steps += 1;
            let level = chain.chosen();
            let mut orbits = chain.stabilizer_orbits(level, self.num_vars * 2);
            self.out.work += u64::from(orbits.unions()) + 1;
            if !orbits.nontrivial() {
                break;
            }
            let Some((v, applicable)) = self.pick(&mut orbits) else {
                break;
            };
            chain.extend_base(v);
            if chain.chosen() != level + 1 {
                break;
            }
            let lit = Literal::from_index(v as usize);
            let op = match applicable {
                Some((clause, amo)) => {
                    if self.fix_check(chain, level, clause, lit) {
                        self.fix(chain, level, clause, lit, amo);
                        LevelOp::Fix { clause, amo }
                    } else {
                        LevelOp::Skip
                    }
                }
                None if chain.in_level_orbit(level, lit.negated().index() as u32) => {
                    self.negation_fix(chain, level, lit);
                    LevelOp::NegationFix
                }
                None => {
                    self.cut(chain, level, lit);
                    LevelOp::Cut
                }
            };
            self.out.base.push(v);
            self.out.ops.push(op);
            self.mark_clauses_of(lit.variable().index() as u32);
        }
        self.out.work += chain.work();
    }

    /// The next base literal (index) and, when a clause fixes it, that
    /// clause and whether it is pairwise exclusive.
    fn pick(&mut self, orbits: &mut Orbits) -> Option<(u32, Option<(usize, bool)>)> {
        if let Some(found) = self.pick_clause(orbits) {
            return Some(found);
        }
        // Cut (or negation-fix) on the positive literal of the open variable
        // with the most clauses in common with the base.
        let mut best: Option<(u32, u32)> = None;
        for x in 0..self.num_vars {
            self.out.work += 1;
            let l = Literal::positive(Variable(x)).index() as u32;
            if self.fixed[x as usize] != 0 || orbits.orbit_size(l) < 2 {
                continue;
            }
            let s = self.score[x as usize];
            if best.is_none_or(|(_, bs)| s > bs) {
                best = Some((l, s));
            }
        }
        best.map(|(l, _)| (l, None))
    }

    /// The first applicable clause (looking past it only for an exclusive
    /// one), as Satsuma does; the clause's first open literal is the base.
    fn pick_clause(&mut self, orbits: &mut Orbits) -> Option<(u32, Option<(usize, bool)>)> {
        let has_binaries = !self.binaries.is_empty();
        let mut best: Option<(usize, u32, u32, bool)> = None;
        let mut seen = 0u32;
        for c in self.first_clause..self.clauses.len() {
            if self.clauses[c].len() < 2 {
                continue;
            }
            self.out.work += 1;
            let Some((var, size)) = self.applicable(c, orbits) else {
                continue;
            };
            if best.is_none() {
                self.first_clause = c;
            }
            seen += 1;
            let amo = has_binaries && self.is_amo(c);
            let better = match best {
                None => true,
                Some((_, _, bsize, bamo)) => (amo && !bamo) || (!bamo && size < bsize),
            };
            if better {
                best = Some((c, var, size, amo));
            }
            if amo || !has_binaries || seen >= AMO_LOOKAHEAD {
                break;
            }
        }
        best.map(|(c, var, _, amo)| (var, Some((c, amo))))
    }

    /// `Some((first open literal, orbit size))` when every open literal of
    /// clause `c` lies in one non-trivial literal orbit and at least two are
    /// open; `None` when a literal is already true or they straddle orbits.
    fn applicable(&mut self, c: usize, orbits: &mut Orbits) -> Option<(u32, u32)> {
        let mut first: Option<u32> = None;
        let mut open = 0u32;
        for l in &self.clauses[c] {
            let f = self.fixed[l.variable().index()];
            if f != 0 {
                if (f > 0) == l.is_positive() {
                    return None;
                }
                continue;
            }
            let li = l.index() as u32;
            match first {
                None => {
                    if orbits.orbit_size(li) < 2 {
                        return None;
                    }
                    first = Some(li);
                }
                Some(fl) => {
                    if !orbits.same_orbit(fl, li) {
                        return None;
                    }
                }
            }
            open += 1;
        }
        let fl = first?;
        (open >= 2).then(|| (fl, orbits.orbit_size(fl)))
    }

    /// Whether the clause's literals are pairwise exclusive in the formula.
    fn is_amo(&mut self, c: usize) -> bool {
        let lits = &self.clauses[c];
        if lits.len() > AMO_MAX_LITERALS {
            return false;
        }
        for (i, a) in lits.iter().enumerate() {
            for b in &lits[i + 1..] {
                self.out.work += 1;
                if !self
                    .binaries
                    .contains(&sorted_pair(a.negated(), b.negated()))
                {
                    return false;
                }
            }
        }
        true
    }

    /// Every open literal of the clause other than `v` must be in the
    /// chain's orbit at `level`, so a transversal element carries it to `v`.
    fn fix_check(&mut self, chain: &SchreierSims, level: usize, c: usize, v: Literal) -> bool {
        self.clauses[c].iter().all(|&l| {
            self.out.work += 1;
            l == v
                || self.fixed[l.variable().index()] != 0
                || chain.in_level_orbit(level, l.index() as u32)
        })
    }

    /// Record a unit as true (its step is pushed by the caller).
    fn set_true(&mut self, l: Literal) {
        self.out.units.push(l);
        self.out.fixings += 1;
        self.fixed[l.variable().index()] = if l.is_positive() { 1 } else { -1 };
    }

    /// The SR witness for a step that derives `v ∨ ¬to` (or, for `to = ¬v`,
    /// the unit `v`): the transversal element of the level's group carrying
    /// the base literal `v` to `to`.
    ///
    /// Direction matters. A witness `x -> y` substitutes `y` for `x`, and
    /// VeriPB's redundance rule needs every constraint, the earlier cuts
    /// included, to hold after the substitution under `¬(v ∨ ¬to)`, where `v`
    /// is false and `to` is true: mapping `v` to `to` makes every earlier cut
    /// `v ∨ ¬z` true. The inverse (carrying `to` to `v`) is the same element
    /// only for an involution; for a longer cycle it breaks an earlier cut
    /// (0be1e12a, 2026-09-24: `x9 ∨ ¬x522` with the 4-cycle the wrong way
    /// round failed on the earlier cut `x9 ∨ ¬x10`).
    fn witness_to(chain: &SchreierSims, level: usize, to: Literal) -> Option<Perm> {
        chain.transversal(level, to.index() as u32)
    }

    /// Clause fixing: `v ∨ ¬l` by SR with the element carrying `v` to `l` for each
    /// other open literal, then the unit by RUP (and, for an exclusive
    /// clause, the other literals' negations by RUP).
    fn fix(&mut self, chain: &SchreierSims, level: usize, c: usize, v: Literal, amo: bool) {
        let others: Vec<Literal> = self.clauses[c]
            .iter()
            .copied()
            .filter(|&l| l != v && self.fixed[l.variable().index()] == 0)
            .collect();
        for &l in &others {
            let Some(sigma) = Self::witness_to(chain, level, l) else {
                continue;
            };
            self.out.work += sigma.support_len() as u64;
            self.out.steps.push(Step::sr(
                vec![v, l.negated()],
                sigma.pairs().iter().copied(),
            ));
        }
        self.out.steps.push(Step::rup(vec![v]));
        self.set_true(v);
        if !amo {
            return;
        }
        for l in others {
            self.out.steps.push(Step::rup(vec![l.negated()]));
            self.set_true(l.negated());
        }
    }

    /// Negation fixing: the unit `v` by SR with the element carrying `v` to
    /// `¬v` (so the unit's image holds under `¬v`).
    fn negation_fix(&mut self, chain: &SchreierSims, level: usize, v: Literal) {
        if let Some(sigma) = Self::witness_to(chain, level, v.negated()) {
            self.out.work += sigma.support_len() as u64;
            self.out
                .steps
                .push(Step::sr(vec![v], sigma.pairs().iter().copied()));
        }
        self.set_true(v);
    }

    /// Orbit cut: `v ∨ ¬w` by SR with the element carrying `v` to `w`.
    fn cut(&mut self, chain: &SchreierSims, level: usize, v: Literal) {
        for &w in chain.level_orbit(level) {
            let wl = Literal::from_index(w as usize);
            if wl == v {
                continue;
            }
            self.out.work += 1;
            if let Some(sigma) = Self::witness_to(chain, level, wl) {
                self.out.work += sigma.support_len() as u64;
                self.out.steps.push(Step::sr(
                    vec![v, wl.negated()],
                    sigma.pairs().iter().copied(),
                ));
            }
            self.out.binaries.push([v, wl.negated()]);
            self.out.cuts += 1;
        }
    }

    fn mark_clauses_of(&mut self, v: u32) {
        let Some(list) = self.occ.get(v as usize) else {
            return;
        };
        for &ci in list {
            let c = ci as usize;
            if self.marked[c] {
                continue;
            }
            self.marked[c] = true;
            for l in &self.clauses[c] {
                self.out.work += 1;
                if let Some(s) = self.score.get_mut(l.variable().index()) {
                    *s += 1;
                }
            }
        }
    }
}

fn sorted_pair(a: Literal, b: Literal) -> (u32, u32) {
    let (x, y) = (a.raw(), b.raw());
    if x <= y {
        (x, y)
    } else {
        (y, x)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(x: i32) -> Literal {
        let v = Variable((x.unsigned_abs() - 1) as u32);
        if x > 0 {
            Literal::positive(v)
        } else {
            Literal::negative(v)
        }
    }

    fn cnf(cls: &[&[i32]]) -> Vec<Vec<Literal>> {
        cls.iter()
            .map(|c| c.iter().map(|&x| lit(x)).collect())
            .collect()
    }

    /// A signed generator from DIMACS pairs: `a -> b` and `-a -> -b`.
    fn perm(pairs: &[(i32, i32)]) -> BTreeMap<Literal, Literal> {
        pairs
            .iter()
            .flat_map(|&(a, b)| [(lit(a), lit(b)), (lit(-a), lit(-b))])
            .collect()
    }

    /// Brute-force satisfiability of a formula over `n` variables.
    fn satisfiable(clauses: &[Vec<Literal>], n: u32) -> bool {
        (0u32..1 << n).any(|m| {
            clauses.iter().all(|c| {
                c.iter().any(|l| {
                    let bit = (m >> l.variable().index()) & 1 == 1;
                    bit == l.is_positive()
                })
            })
        })
    }

    fn with_constraints(clauses: &[Vec<Literal>], fc: &FixAndCut) -> Vec<Vec<Literal>> {
        let mut all = clauses.to_vec();
        all.extend(fc.units.iter().map(|&u| vec![u]));
        all.extend(fc.binaries.iter().map(|b| b.to_vec()));
        all
    }

    /// Pigeonhole 3 into 2: pigeons and holes interchangeable.
    fn php32() -> (Vec<Vec<Literal>>, Vec<BTreeMap<Literal, Literal>>) {
        // p(i,h) = 2i + h + 1 for i in 0..3, h in 0..2.
        let clauses = cnf(&[
            &[1, 2],
            &[3, 4],
            &[5, 6],
            &[-1, -3],
            &[-1, -5],
            &[-3, -5],
            &[-2, -4],
            &[-2, -6],
            &[-4, -6],
        ]);
        let gens = vec![
            perm(&[(1, 3), (3, 1), (2, 4), (4, 2)]),
            perm(&[(3, 5), (5, 3), (4, 6), (6, 4)]),
            perm(&[(1, 2), (2, 1), (3, 4), (4, 3), (5, 6), (6, 5)]),
        ];
        (clauses, gens)
    }

    #[test]
    fn pigeonhole_fixes_a_pigeon_and_its_hole() {
        let (clauses, gens) = php32();
        let (fc, _) = fix_and_cut(&clauses, &gens, 6, 1, 1 << 30);
        assert!(fc.fixings >= 1, "{fc:?}");
        assert!(
            fc.units.contains(&lit(1)),
            "the first clause fixes p(0,0): {fc:?}"
        );
        // In the stabilizer of p(0,0) pigeons 1 and 2 still swap, so the hole
        // clause ¬p(1,0) ∨ ¬p(2,0) fixes ¬p(1,0); then the group is trivial.
        assert!(fc.units.contains(&lit(-3)), "{fc:?}");
        assert_eq!(
            fc.base,
            vec![lit(1).index() as u32, lit(-3).index() as u32],
            "{fc:?}"
        );
        assert!(!fc.budget_hit);
        assert_eq!(fc.base.len(), fc.ops.len());
        assert!(!satisfiable(&with_constraints(&clauses, &fc), 6));
    }

    #[test]
    fn an_exclusive_clause_fixes_its_whole_orbit() {
        // Exactly-one over three interchangeable variables.
        let clauses = cnf(&[
            &[1, 2, 3],
            &[-1, -2],
            &[-1, -3],
            &[-2, -3],
            &[1, 4],
            &[2, 4],
            &[3, 4],
        ]);
        let gens = vec![perm(&[(1, 2), (2, 1)]), perm(&[(2, 3), (3, 2)])];
        let (fc, _) = fix_and_cut(&clauses, &gens, 4, 9, 1 << 30);
        assert_eq!(
            fc.ops.first(),
            Some(&LevelOp::Fix {
                clause: 0,
                amo: true
            }),
            "{fc:?}"
        );
        assert!(
            fc.units.contains(&lit(1))
                && fc.units.contains(&lit(-2))
                && fc.units.contains(&lit(-3)),
            "{fc:?}"
        );
        assert!(satisfiable(&with_constraints(&clauses, &fc), 4));
    }

    #[test]
    fn a_satisfiable_symmetric_formula_stays_satisfiable() {
        // One at-least-one clause over three interchangeable variables and a
        // mixed clause that cannot fix.
        let clauses = cnf(&[&[1, 2, 3], &[-1, -2, 4], &[-2, -3, 4], &[-1, -3, 4]]);
        let gens = vec![perm(&[(1, 2), (2, 1)]), perm(&[(2, 3), (3, 2)])];
        let (fc, _) = fix_and_cut(&clauses, &gens, 4, 3, 1 << 30);
        assert_eq!(fc.units, vec![lit(1)], "{fc:?}");
        assert!(satisfiable(&with_constraints(&clauses, &fc), 4));
    }

    #[test]
    fn without_a_fixing_clause_the_walk_cuts_the_orbit() {
        // x1, x2, x3 interchangeable, no clause inside the orbit.
        let clauses = cnf(&[&[1, -4], &[2, -4], &[3, -4], &[-1, 5], &[-2, 5], &[-3, 5]]);
        let gens = vec![perm(&[(1, 2), (2, 1)]), perm(&[(2, 3), (3, 2)])];
        let (fc, _) = fix_and_cut(&clauses, &gens, 5, 5, 1 << 30);
        assert_eq!(fc.fixings, 0, "{fc:?}");
        assert!(fc.cuts >= 2, "{fc:?}");
        assert!(fc.ops.contains(&LevelOp::Cut));
        // Every cut is v ∨ ¬w with v the base point of its level.
        for b in &fc.binaries {
            assert!(b[0].is_positive() && !b[1].is_positive());
            assert!(fc.base.contains(&(b[0].index() as u32)));
        }
        assert!(satisfiable(&with_constraints(&clauses, &fc), 5));
    }

    /// Apply a step's witness substitution to a literal.
    fn image(step: &Step, l: Literal) -> Literal {
        let pairs = &step.witness[2..];
        pairs.chunks(2).find(|p| p[0] == l).map_or(l, |p| p[1])
    }

    #[test]
    fn a_negation_symmetry_fixes_a_literal() {
        // x1 xor x2, symmetric under flipping both: WLOG x1 is true.
        let clauses = cnf(&[&[1, 2], &[-1, -2], &[1, 3], &[2, 3]]);
        let gens = vec![perm(&[(1, -1), (2, -2)])];
        let (fc, _) = fix_and_cut(&clauses, &gens, 3, 11, 1 << 30);
        assert_eq!(fc.units, vec![lit(1)], "{fc:?}");
        assert_eq!(fc.ops, vec![LevelOp::NegationFix], "{fc:?}");
        assert!(fc.binaries.is_empty());
        assert!(satisfiable(&with_constraints(&clauses, &fc), 3));
        // The step: unit x1 with a witness carrying ¬x1 to x1.
        assert_eq!(fc.steps.len(), 1);
        let step = &fc.steps[0];
        assert_eq!(step.clause, vec![lit(1)]);
        assert_eq!(&step.witness[..2], &[lit(1), lit(1)]);
        assert_eq!(image(step, lit(-1)), lit(1));
        assert_eq!(image(step, lit(1)), lit(-1));
    }

    #[test]
    fn every_sr_step_witness_carries_the_base_onto_the_cut_literal() {
        let clauses = cnf(&[&[1, -4], &[2, -4], &[3, -4], &[-1, 5], &[-2, 5], &[-3, 5]]);
        let gens = vec![perm(&[(1, 2), (2, 1)]), perm(&[(2, 3), (3, 2)])];
        let (fc, _) = fix_and_cut(&clauses, &gens, 5, 5, 1 << 30);
        let sr: Vec<&Step> = fc.steps.iter().filter(|s| !s.witness.is_empty()).collect();
        assert_eq!(sr.len() as u64, fc.cuts, "{fc:?}");
        for step in sr {
            let [v, not_w] = step.clause[..] else {
                panic!("cut steps are binary: {step:?}");
            };
            assert_eq!(
                image(step, v),
                not_w.negated(),
                "witness must carry v to w: {step:?}"
            );
        }
    }

    /// Unit propagation from `assumed` over `db`: `None` on a conflict, else
    /// the assignment reached.
    fn propagate(db: &[Vec<Literal>], assumed: &[Literal]) -> Option<HashSet<Literal>> {
        let mut val: HashSet<Literal> = HashSet::new();
        for &l in assumed {
            if val.contains(&l.negated()) {
                return None;
            }
            val.insert(l);
        }
        loop {
            let mut changed = false;
            for c in db {
                if c.iter().any(|l| val.contains(l)) {
                    continue;
                }
                let open: Vec<Literal> = c
                    .iter()
                    .copied()
                    .filter(|l| !val.contains(&l.negated()))
                    .collect();
                match open.len() {
                    0 => return None,
                    1 => {
                        val.insert(open[0]);
                        changed = true;
                    }
                    _ => {}
                }
            }
            if !changed {
                return Some(val);
            }
        }
    }

    /// VeriPB's redundance condition for every SR step, checked by RUP: with
    /// the step's clause falsified, each constraint so far (formula and earlier
    /// steps) and the clause itself must hold after the witness substitution.
    fn assert_every_sr_step_is_redundant(clauses: &[Vec<Literal>], fc: &FixAndCut) {
        let mut db: Vec<Vec<Literal>> = clauses.to_vec();
        for step in &fc.steps {
            if !step.witness.is_empty() {
                let not_c: Vec<Literal> = step.clause.iter().map(|l| l.negated()).collect();
                let mut goals = db.clone();
                goals.push(step.clause.clone());
                for d in &goals {
                    let image: Vec<Literal> = d.iter().map(|&l| image(step, l)).collect();
                    let mut assumed = not_c.clone();
                    assumed.extend(image.iter().map(|l| l.negated()));
                    assert!(
                        propagate(&db, &assumed).is_none(),
                        "{d:?} under the witness of {step:?} is not implied"
                    );
                }
            }
            db.push(step.clause.clone());
        }
    }

    #[test]
    fn a_cycle_symmetry_gets_witnesses_that_keep_earlier_cuts() {
        // Only a 3-cycle generates the group, so two of its transversal
        // elements are 3-cycles, not involutions: the witness must carry the
        // base to the cut literal, not back (0be1e12a).
        let clauses = cnf(&[&[1, 2, 3], &[-1, -2, -3]]);
        let gens = vec![perm(&[(1, 2), (2, 3), (3, 1)])];
        let (fc, _) = fix_and_cut(&clauses, &gens, 3, 5, 1 << 30);
        let sr_steps = fc.steps.iter().filter(|s| !s.witness.is_empty()).count();
        assert!(sr_steps >= 2, "{fc:?}");
        assert_every_sr_step_is_redundant(&clauses, &fc);
    }

    #[test]
    fn every_sr_step_of_a_pigeonhole_is_redundant() {
        let (clauses, gens) = php32();
        let (fc, _) = fix_and_cut(&clauses, &gens, 6, 5, 1 << 30);
        assert_every_sr_step_is_redundant(&clauses, &fc);
    }

    #[test]
    fn a_clause_fixing_derives_binaries_then_the_unit_by_rup() {
        let (clauses, gens) = php32();
        let (fc, _) = fix_and_cut(&clauses, &gens, 6, 1, 1 << 30);
        // First level: clause (p00 ∨ p01) fixes p00: one SR binary p00 ∨ ¬p01
        // whose witness carries p01 to p00, then the RUP unit.
        assert_eq!(fc.steps[0].clause, vec![lit(1), lit(-2)]);
        assert_eq!(image(&fc.steps[0], lit(2)), lit(1));
        assert_eq!(fc.steps[1], Step::rup(vec![lit(1)]));
    }

    #[test]
    fn lifting_variable_generators_keeps_both_polarities() {
        let g: BTreeMap<Variable, Variable> =
            [(Variable(0), Variable(1)), (Variable(1), Variable(0))]
                .into_iter()
                .collect();
        let lifted = lift_variable_generators(&[g]);
        assert_eq!(lifted[0].get(&lit(1)), Some(&lit(2)));
        assert_eq!(lifted[0].get(&lit(-2)), Some(&lit(-1)));
    }

    #[test]
    fn simplification_propagates_units_and_reports_conflicts() {
        let clauses = cnf(&[&[1, 2], &[-1, 3], &[-3, 4, 5], &[-2, -4], &[6, 7]]);
        // x1 true: (x1 ∨ x2) satisfied, (¬x1 ∨ x3) gives x3, then (x4 ∨ x5)
        // stays; (¬x2 ∨ ¬x4) stays; (x6 ∨ x7) untouched.
        let residual = simplify_by_units(&clauses, &[lit(1)], 7).expect("consistent");
        assert_eq!(
            residual,
            cnf(&[&[4, 5], &[-2, -4], &[6, 7]]),
            "{residual:?}"
        );
        // x1 and x2 true: x3, then ¬x4 from (¬x2 ∨ ¬x4), then x5.
        let residual = simplify_by_units(&clauses, &[lit(1), lit(2)], 7).expect("consistent");
        assert_eq!(residual, cnf(&[&[6, 7]]), "{residual:?}");
        // Contradictory units, or a falsified clause, is a conflict.
        assert!(simplify_by_units(&clauses, &[lit(1), lit(-1)], 7).is_none());
        assert!(simplify_by_units(&clauses, &[lit(-6), lit(-7)], 7).is_none());
    }

    #[test]
    fn the_budget_stops_the_walk() {
        let (clauses, gens) = php32();
        let (fc, _) = fix_and_cut(&clauses, &gens, 6, 1, 1);
        assert!(fc.budget_hit);
        assert!(fc.units.is_empty() && fc.binaries.is_empty());
    }

    #[test]
    fn no_generators_no_constraints() {
        let (clauses, _) = php32();
        let (fc, chain) = fix_and_cut(&clauses, &[], 6, 1, 1 << 30);
        assert!(fc.units.is_empty() && fc.binaries.is_empty() && fc.base.is_empty());
        assert_eq!(chain.depth(), 0);
    }
}

#[cfg(test)]
mod probe {
    //! `AY_FIXCUT_PROBE=<dimacs>` runs the signed search and the walk on a
    //! file, printing phase timings, generator counts and results; ignored
    //! by default (a measurement aid, not a test).
    use super::*;

    fn read_dimacs(path: &str) -> (Vec<Vec<Literal>>, u32) {
        let text = std::fs::read_to_string(path).unwrap_or_default();
        let mut clauses = Vec::new();
        let mut num_vars = 0u32;
        for line in text.lines() {
            if line.starts_with('c') {
                continue;
            }
            if let Some(rest) = line.strip_prefix("p cnf") {
                num_vars = rest
                    .split_whitespace()
                    .next()
                    .and_then(|v| v.parse().ok())
                    .unwrap_or(0);
                continue;
            }
            let lits: Vec<Literal> = line
                .split_whitespace()
                .filter_map(|t| t.parse::<i32>().ok())
                .take_while(|&x| x != 0)
                .map(|x| {
                    let v = Variable(x.unsigned_abs() - 1);
                    if x > 0 {
                        Literal::positive(v)
                    } else {
                        Literal::negative(v)
                    }
                })
                .collect();
            if !lits.is_empty() {
                clauses.push(lits);
            }
        }
        (clauses, num_vars)
    }

    /// Measurement aid: set `AY_FIXCUT_PROBE` to a DIMACS path to make this
    /// probe do work. Without it the test returns immediately, which is why it
    /// carries no `#[ignore]`: the environment already selects it, and
    /// `ay-quality-gate`'s ban on test-disabling attributes is absolute (see
    /// `crates/ay-core/tests/serde_bignum_parity.rs` for the same shape, and
    /// `crates/ay-milp/src/dualfix.rs` for the `examples/` conversion used when
    /// a harness really does work unconditionally).
    #[test]
    fn probe_file() {
        let Ok(path) = std::env::var("AY_FIXCUT_PROBE") else {
            return;
        };
        let (clauses, num_vars) = read_dimacs(&path);
        let t0 = std::time::Instant::now();
        let counts = super::super::build_formula_counts(&clauses);
        let (flips, flip_stats) =
            super::super::flips::find_flip_symmetries(&clauses, num_vars, &counts);
        let mean_support = flips
            .basis
            .iter()
            .map(|r| r.iter().map(|w| w.count_ones() as usize).sum::<usize>())
            .sum::<usize>()
            .checked_div(flips.rank())
            .unwrap_or(0);
        eprintln!(
            "probe: flips={} mean support={mean_support} {flip_stats:?} in {:?}",
            flips.rank(),
            t0.elapsed()
        );
        let t0 = std::time::Instant::now();
        let gens = super::super::ir::find_signed_automorphisms_budgeted(
            &clauses,
            &counts,
            super::super::FIX_AND_CUT_IR_NODE_BUDGET,
            super::super::FIX_AND_CUT_IR_MAX_GENERATORS,
            super::super::FIX_AND_CUT_IR_WORK_BUDGET,
        );
        let support: usize = gens.iter().map(|g| g.len()).sum();
        eprintln!(
            "probe: vars={num_vars} clauses={} signed generators={} total support={support} in {:?}",
            clauses.len(),
            gens.len(),
            t0.elapsed()
        );
        let t1 = std::time::Instant::now();
        let detector = super::super::detector::SymmetryDetector::new(1 << 20, 1 << 20);
        let (fc, chain) = detector.detect_fix_and_cut(&clauses, num_vars);
        eprintln!(
            "probe: rounds={} levels={} fixings={} cuts={} work={} budget_hit={} chain generators={} chain work={} in {:?}",
            fc.rounds,
            fc.base.len(),
            fc.fixings,
            fc.cuts,
            fc.work,
            fc.budget_hit,
            chain.generators,
            chain.work,
            t1.elapsed()
        );
    }
}
