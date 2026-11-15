// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Sign-flip symmetries by linear algebra over GF(2).
//!
//! A set `S` of variables is a *flip symmetry* when negating every literal
//! of `S` maps the clause multiset onto itself. Flip symmetries are closed
//! under symmetric difference, so they form a subspace of GF(2)^n, and the
//! subspace is cut out by local conditions: group the clauses by variable
//! set `W`; the sign patterns `P_W` on `W` (as bit masks) must be carried
//! onto themselves by `S|W`, so `S|W` lies in the period lattice
//! `Stab(P_W) = { s : P_W ⊕ s = P_W }`, itself a subspace, and its
//! annihilator gives linear equations on the variables of `W`. Gaussian
//! elimination over all equations yields a basis of the flip group.
//!
//! This is what the individualization–refinement search cannot afford on
//! xor-heavy formulas: their flip groups have rank in the hundreds (xor_op
//! 605), so the IR tree needs thousands of deep leaves, while here the
//! whole group costs one elimination. Satsuma's units on such formulas are
//! negation fixings of exactly these symmetries.
//!
//! Every basis vector is returned as a literal map and gate-checked against
//! the formula (`literal_permutation_preserves_formula`), so an error here
//! can only lose symmetries, never invent one.

use std::collections::{BTreeMap, HashMap};

use crate::{Literal, Variable};

/// Formulas with more *free* variables than this skip the finder (dense
/// rows over the free variables). A variable is pinned before the
/// elimination when it occurs in no clause, in a clause over more than
/// `FLIP_MAX_CLAUSE_VARS` variables, or in a group with a single sign
/// pattern (its lattice is trivial); on structured formulas most variables
/// are, so a million-variable formula usually leaves a few thousand.
pub(crate) const FLIP_MAX_VARS: usize = 32_000;

/// The set bits of a dense row, as column indices.
fn support_columns(row: &[u64]) -> Vec<u32> {
    let mut out = Vec::new();
    for (i, &w) in row.iter().enumerate() {
        let mut m = w;
        while m != 0 {
            out.push((i * 64) as u32 + m.trailing_zeros());
            m &= m - 1;
        }
    }
    out
}
/// Clauses over more distinct variables than this pin their variables (a
/// sound under-approximation: no flip touches them).
const FLIP_MAX_CLAUSE_VARS: usize = 64;

/// The flip group as a GF(2) basis over the *free* variables (dense rows in
/// a compact index; `vars` maps a column back to its variable).
#[derive(Clone, Debug, Default)]
pub(crate) struct FlipGroup {
    words: usize,
    /// Basis vectors, each a flip set as a bit row over the free variables.
    pub(crate) basis: Vec<Vec<u64>>,
    /// Column -> variable index.
    vars: Vec<u32>,
    /// Variable index -> column, `u32::MAX` when pinned.
    column: Vec<u32>,
}

impl FlipGroup {
    pub(crate) fn rank(&self) -> usize {
        self.basis.len()
    }

    fn col_bit(row: &[u64], c: u32) -> bool {
        row[c as usize / 64] >> (c % 64) & 1 == 1
    }

    /// The variables a row flips.
    pub(crate) fn support(&self, row: &[u64]) -> Vec<u32> {
        support_columns(row)
            .into_iter()
            .map(|c| self.vars[c as usize])
            .collect()
    }

    #[cfg(test)]
    /// The literal map of a flip row (both polarities of every flipped
    /// variable).
    pub(crate) fn as_generator(&self, row: &[u64]) -> BTreeMap<Literal, Literal> {
        self.support(row)
            .into_iter()
            .flat_map(|v| {
                let var = Variable(v);
                [
                    (Literal::positive(var), Literal::negative(var)),
                    (Literal::negative(var), Literal::positive(var)),
                ]
            })
            .collect()
    }

    /// Greedy weight reduction: replace a basis vector by its sum with
    /// another whenever that is lighter, until a pass changes nothing (at
    /// most `passes`). A sparse basis keeps the gate check, which touches
    /// every clause on a flipped variable, cheap.
    pub(crate) fn sparsify(&mut self, passes: usize, work: &mut u64) {
        let k = self.basis.len();
        let mut weight: Vec<u32> = self
            .basis
            .iter()
            .map(|r| r.iter().map(|w| w.count_ones()).sum())
            .collect();
        for _ in 0..passes {
            let mut changed = false;
            for i in 0..k {
                for j in 0..k {
                    if i == j {
                        continue;
                    }
                    *work += self.words as u64;
                    let combined: u32 = self.basis[i]
                        .iter()
                        .zip(&self.basis[j])
                        .map(|(a, b)| (a ^ b).count_ones())
                        .sum();
                    if combined < weight[i] {
                        let (bi, bj) = if i < j {
                            let (l, r) = self.basis.split_at_mut(j);
                            (&mut l[i], &r[0])
                        } else {
                            let (l, r) = self.basis.split_at_mut(i);
                            (&mut r[0], &l[j])
                        };
                        for (a, b) in bi.iter_mut().zip(bj) {
                            *a ^= *b;
                        }
                        weight[i] = combined;
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
    }

    /// Drop every flip touching a variable of `pinned`, keeping a basis of
    /// the subgroup that fixes them: the flips left are in the stabilizer
    /// of the pinned literals, so they respect any constraint derived under
    /// the pinned points as base.
    pub(crate) fn restrict_to_fixing(&mut self, pinned: &[u32], work: &mut u64) {
        for &v in pinned {
            let Some(&c) = self.column.get(v as usize) else {
                continue;
            };
            if c == u32::MAX {
                continue;
            }
            let Some(k) = self.basis.iter().position(|r| Self::col_bit(r, c)) else {
                continue;
            };
            let b = self.basis.swap_remove(k);
            for r in self.basis.iter_mut() {
                if Self::col_bit(r, c) {
                    *work += self.words as u64;
                    for (a, x) in r.iter_mut().zip(&b) {
                        *a ^= *x;
                    }
                }
            }
        }
    }

    /// Negation fixings over the whole group: while a flip remains, take the
    /// lightest basis vector `b` and its lowest variable `v`; WLOG `v` is
    /// true (the model with `v` false maps under `b` to one with `v` true,
    /// and `b` fixes every variable fixed before); then continue in the
    /// stabilizer of `v`, which is the group with `b` eliminated. One unit
    /// per rank, each with its witness flip set.
    pub(crate) fn fixings(mut self, work: &mut u64) -> Vec<(Literal, Vec<u32>)> {
        let mut out = Vec::new();
        while !self.basis.is_empty() {
            let (k, _) = self
                .basis
                .iter()
                .enumerate()
                .map(|(i, r)| (i, r.iter().map(|w| w.count_ones()).sum::<u32>()))
                .min_by_key(|&(_, w)| w)
                .unwrap_or((0, 0));
            let b = self.basis.swap_remove(k);
            let support = self.support(&b);
            let Some(&v) = support.first() else {
                continue;
            };
            let c = self.column[v as usize];
            for r in self.basis.iter_mut() {
                if Self::col_bit(r, c) {
                    *work += self.words as u64;
                    for (a, x) in r.iter_mut().zip(&b) {
                        *a ^= *x;
                    }
                }
            }
            out.push((Literal::positive(Variable(v)), support));
        }
        out
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct FlipStats {
    /// Distinct variable sets seen.
    pub(crate) groups: u64,
    /// Equations inserted into the elimination.
    pub(crate) equations: u64,
    /// Rank of the equation system.
    pub(crate) rank: u64,
    /// Dimension of the flip group (generators returned before the gate).
    pub(crate) dimension: u64,
    /// Generators the gate rejected (must be zero; counted, never trusted).
    pub(crate) rejected: u64,
    /// Variables pinned before the elimination (absent, over-long clause,
    /// single-pattern group).
    pub(crate) pinned: u64,
    /// 1 when the free variables exceeded `FLIP_MAX_VARS` (finder skipped).
    pub(crate) too_many_free: u64,
    pub(crate) work: u64,
}

/// Dense GF(2) rows with an echelon basis keyed by pivot (lowest set bit).
struct Elimination {
    words: usize,
    pivots: Vec<Option<Vec<u64>>>,
    rank: u64,
    work: u64,
}

impl Elimination {
    fn new(num_vars: usize) -> Self {
        Self {
            words: num_vars.div_ceil(64).max(1),
            pivots: vec![None; num_vars],
            rank: 0,
            work: 0,
        }
    }

    fn lowest_bit(row: &[u64]) -> Option<usize> {
        row.iter()
            .enumerate()
            .find(|(_, &w)| w != 0)
            .map(|(i, &w)| i * 64 + w.trailing_zeros() as usize)
    }

    /// Insert a sparse equation (variable indices); returns whether it was
    /// independent of the rows so far.
    fn insert(&mut self, vars: &[u32]) -> bool {
        let mut row = vec![0u64; self.words];
        for &v in vars {
            row[v as usize / 64] ^= 1u64 << (v % 64);
        }
        self.reduce_and_store(row)
    }

    fn reduce_and_store(&mut self, mut row: Vec<u64>) -> bool {
        loop {
            let Some(p) = Self::lowest_bit(&row) else {
                return false;
            };
            match &self.pivots[p] {
                Some(pivot) => {
                    let from = p / 64;
                    for (r, q) in row[from..].iter_mut().zip(&pivot[from..]) {
                        *r ^= *q;
                    }
                    self.work += (self.words - from) as u64;
                }
                None => {
                    self.pivots[p] = Some(row);
                    self.rank += 1;
                    return true;
                }
            }
        }
    }

    /// A basis of the null space: one vector per free variable, by back
    /// substitution over the echelon rows (each row's lowest bit is its
    /// pivot, so the pivot's value is the parity of the rest).
    fn null_space(&mut self) -> Vec<Vec<u64>> {
        let n = self.pivots.len();
        let pivot_order: Vec<usize> = (0..n).filter(|&p| self.pivots[p].is_some()).collect();
        let mut out = Vec::new();
        for f in 0..n {
            if self.pivots[f].is_some() {
                continue;
            }
            let mut x = vec![0u64; self.words];
            x[f / 64] |= 1u64 << (f % 64);
            for &p in pivot_order.iter().rev() {
                let Some(row) = &self.pivots[p] else {
                    continue;
                };
                let parity = row
                    .iter()
                    .zip(&x)
                    .fold(0u32, |acc, (&r, &xv)| acc ^ (r & xv).count_ones());
                self.work += self.words as u64;
                if parity & 1 == 1 {
                    x[p / 64] ^= 1u64 << (p % 64);
                }
            }
            out.push(x);
        }
        out
    }
}

/// Reduced row-echelon basis of a set of 64-bit vectors.
fn rref64(vectors: &[u64]) -> Vec<u64> {
    let mut basis: Vec<u64> = Vec::new();
    for &v in vectors {
        let mut r = v;
        for &b in &basis {
            if r & (1u64 << b.trailing_zeros()) != 0 {
                r ^= b;
            }
        }
        if r != 0 {
            // Keep rows reduced against the new pivot as well.
            let pivot = 1u64 << r.trailing_zeros();
            for b in basis.iter_mut() {
                if *b & pivot != 0 {
                    *b ^= r;
                }
            }
            basis.push(r);
            basis.sort_unstable_by_key(|b| b.trailing_zeros());
        }
    }
    basis
}

/// Equations (as masks over the group's width) cutting out the subspace
/// spanned by `basis` (RREF, pivots = lowest bits): one per free column.
fn annihilator(basis: &[u64], width: usize) -> Vec<u64> {
    let pivot_bits: u64 = basis
        .iter()
        .fold(0, |acc, b| acc | (1u64 << b.trailing_zeros()));
    let mut out = Vec::new();
    for f in 0..width {
        if pivot_bits >> f & 1 == 1 {
            continue;
        }
        let mut a = 1u64 << f;
        for b in basis {
            if b >> f & 1 == 1 {
                a |= 1u64 << b.trailing_zeros();
            }
        }
        out.push(a);
    }
    out
}

/// Sign patterns of the clauses on one variable set: mask -> multiplicity.
type Patterns = HashMap<u64, u32>;

/// The period lattice of a pattern multiset: every shift carrying it onto
/// itself, as a list (closed under xor, so a subspace; `0` included).
fn period_lattice(patterns: &Patterns, work: &mut u64) -> Vec<u64> {
    let Some(&p0) = patterns.keys().min() else {
        return vec![0];
    };
    let mut lattice = Vec::new();
    for &q in patterns.keys() {
        let s = p0 ^ q;
        *work += patterns.len() as u64;
        let valid = patterns
            .iter()
            .all(|(&r, &c)| patterns.get(&(r ^ s)) == Some(&c));
        if valid {
            lattice.push(s);
        }
    }
    lattice
}

/// Greedy sparsification passes over the basis before the gate.
const SPARSIFY_PASSES: usize = 3;

/// The flip group's basis, sparsified and gate-checked vector by vector
/// (a vector the gate rejects is dropped and counted).
pub(crate) fn find_flip_symmetries(
    clauses: &[Vec<Literal>],
    num_vars: u32,
    formula_counts: &BTreeMap<Vec<u32>, u32>,
) -> (FlipGroup, FlipStats) {
    let n = num_vars as usize;
    let mut stats = FlipStats::default();
    if n == 0 || clauses.is_empty() {
        return (FlipGroup::default(), stats);
    }
    let mut groups: HashMap<Vec<u32>, Patterns> = HashMap::new();
    let mut pinned = vec![false; n];
    let mut occurs = vec![false; n];
    for clause in clauses {
        let mut vars: Vec<(u32, bool)> = clause
            .iter()
            .map(|l| (l.variable().index() as u32, l.is_positive()))
            .collect();
        vars.sort_unstable();
        vars.dedup();
        stats.work += vars.len() as u64;
        for &(v, _) in &vars {
            if let Some(o) = occurs.get_mut(v as usize) {
                *o = true;
            }
        }
        let distinct = vars.windows(2).all(|w| w[0].0 != w[1].0);
        if !distinct {
            continue; // a tautology constrains nothing
        }
        if vars.len() > FLIP_MAX_CLAUSE_VARS {
            for &(v, _) in &vars {
                pinned[v as usize] = true;
            }
            continue;
        }
        let key: Vec<u32> = vars.iter().map(|&(v, _)| v).collect();
        let mask: u64 = vars
            .iter()
            .enumerate()
            .filter(|(_, &(_, pos))| !pos)
            .fold(0u64, |m, (i, _)| m | (1u64 << i));
        *groups.entry(key).or_default().entry(mask).or_insert(0) += 1;
    }
    // A variable in no clause of this formula is not free to flip: it may
    // be assigned at the root, eliminated with a reconstruction dependency,
    // or simply unused, and none of those is a symmetry of the solver's
    // formula. Unpinned, it became a one-variable "flip group" whose walk
    // fixed it true — 26 false UNSAT answers on the 2026-09-22 screen.
    for v in 0..n {
        if !occurs[v] {
            pinned[v] = true;
        }
    }
    stats.groups = groups.len() as u64;
    // Groups with one sign pattern pin all their variables; the rest yield
    // equations over the free variables.
    let mut lattices: Vec<(&Vec<u32>, Vec<u64>)> = Vec::new();
    for (key, patterns) in &groups {
        let lattice = period_lattice(patterns, &mut stats.work);
        let basis = rref64(&lattice);
        if basis.is_empty() {
            for &v in key {
                pinned[v as usize] = true;
            }
        } else {
            lattices.push((key, basis));
        }
    }
    let vars: Vec<u32> = (0..n as u32).filter(|&v| !pinned[v as usize]).collect();
    stats.pinned = (n - vars.len()) as u64;
    if vars.is_empty() || vars.len() > FLIP_MAX_VARS {
        stats.too_many_free = u64::from(vars.len() > FLIP_MAX_VARS);
        return (FlipGroup::default(), stats);
    }
    let mut column = vec![u32::MAX; n];
    for (c, &v) in vars.iter().enumerate() {
        column[v as usize] = c as u32;
    }
    let mut elim = Elimination::new(vars.len());
    for (key, basis) in lattices {
        for a in annihilator(&basis, key.len()) {
            let cols: Vec<u32> = key
                .iter()
                .enumerate()
                .filter(|(i, _)| a >> i & 1 == 1)
                .map(|(_, &v)| column[v as usize])
                .filter(|&c| c != u32::MAX)
                .collect();
            if cols.is_empty() {
                continue;
            }
            stats.equations += 1;
            elim.insert(&cols);
        }
    }
    stats.rank = elim.rank;
    let mut group = FlipGroup {
        words: elim.words,
        basis: elim.null_space(),
        vars,
        column,
    };
    stats.dimension = group.basis.len() as u64;
    stats.work += elim.work;
    group.sparsify(SPARSIFY_PASSES, &mut stats.work);
    // The gate, on the clauses a flip touches (occurrence lists).
    let mut occ: Vec<Vec<u32>> = vec![Vec::new(); n];
    for (ci, c) in clauses.iter().enumerate() {
        for l in c {
            if let Some(o) = occ.get_mut(l.variable().index()) {
                o.push(ci as u32);
            }
        }
    }
    let mut kept = Vec::new();
    let basis = std::mem::take(&mut group.basis);
    for row in basis {
        let support = group.support(&row);
        if flip_preserves_formula(clauses, formula_counts, &occ, &support, &mut stats.work) {
            kept.push(row);
        } else {
            stats.rejected += 1;
        }
    }
    group.basis = kept;
    (group, stats)
}

/// Whether flipping `support` maps every clause it touches onto a clause of
/// the same multiplicity (clauses it does not touch map to themselves).
fn flip_preserves_formula(
    clauses: &[Vec<Literal>],
    formula_counts: &BTreeMap<Vec<u32>, u32>,
    occ: &[Vec<u32>],
    support: &[u32],
    work: &mut u64,
) -> bool {
    let mut flipped = vec![false; occ.len()];
    for &v in support {
        flipped[v as usize] = true;
    }
    let mut touched: Vec<u32> = support
        .iter()
        .flat_map(|&v| occ[v as usize].iter().copied())
        .collect();
    touched.sort_unstable();
    touched.dedup();
    for ci in touched {
        let clause = &clauses[ci as usize];
        *work += clause.len() as u64;
        let image: Vec<Literal> = clause
            .iter()
            .map(|&l| {
                if flipped[l.variable().index()] {
                    l.negated()
                } else {
                    l
                }
            })
            .collect();
        let before = formula_counts.get(&super::canonical_clause_key(clause));
        let after = formula_counts.get(&super::canonical_clause_key(&image));
        if before != after {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(x: i32) -> Literal {
        let v = Variable(x.unsigned_abs() - 1);
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

    /// Clauses of `x_a ⊕ x_b ⊕ x_c = parity`.
    fn xor3(a: i32, b: i32, c: i32, parity: bool) -> Vec<Vec<i32>> {
        let mut out = Vec::new();
        for bits in 0..8u32 {
            let assignment = [bits & 1 == 1, bits >> 1 & 1 == 1, bits >> 2 & 1 == 1];
            let p = assignment.iter().filter(|&&x| x).count() % 2 == 1;
            if p != parity {
                // Forbid this assignment.
                out.push(
                    [a, b, c]
                        .iter()
                        .zip(assignment)
                        .map(|(&v, t)| if t { -v } else { v })
                        .collect(),
                );
            }
        }
        out
    }

    fn run(clauses: &[Vec<Literal>], n: u32) -> (Vec<BTreeMap<Literal, Literal>>, FlipStats) {
        let counts = super::super::build_formula_counts(clauses);
        let (group, stats) = find_flip_symmetries(clauses, n, &counts);
        let gens = group.basis.iter().map(|r| group.as_generator(r)).collect();
        (gens, stats)
    }

    #[test]
    fn fixings_take_one_unit_per_rank_and_stay_satisfiable() {
        let mut cls: Vec<Vec<i32>> = xor3(1, 2, 3, false);
        cls.extend(xor3(3, 4, 5, true));
        let refs: Vec<&[i32]> = cls.iter().map(|c| c.as_slice()).collect();
        let clauses = cnf(&refs);
        let counts = super::super::build_formula_counts(&clauses);
        let (group, _) = find_flip_symmetries(&clauses, 5, &counts);
        let mut work = 0;
        let units = group.clone().fixings(&mut work);
        assert_eq!(units.len(), 3, "{units:?}");
        let mut all = clauses.clone();
        all.extend(units.iter().map(|(u, _)| vec![*u]));
        // Brute force: the fixed formula must still have a model.
        assert!((0u32..32).any(|m| all.iter().all(|c| c.iter().any(|l| ((m
            >> l.variable().index())
            & 1
            == 1)
            == l.is_positive()))));
        // Restricting to flips fixing variable 3 leaves rank 1 (x1x2 only... and x4x5).
        let mut g = group;
        g.restrict_to_fixing(&[2], &mut work);
        assert_eq!(g.rank(), 2, "flips avoiding x3: {{1,2}} and {{4,5}}");
    }

    #[test]
    fn two_xors_sharing_a_variable_have_rank_three() {
        let mut cls: Vec<Vec<i32>> = xor3(1, 2, 3, false);
        cls.extend(xor3(3, 4, 5, true));
        let refs: Vec<&[i32]> = cls.iter().map(|c| c.as_slice()).collect();
        let clauses = cnf(&refs);
        let (gens, stats) = run(&clauses, 5);
        assert_eq!(stats.rejected, 0, "{stats:?}");
        assert_eq!(gens.len(), 3, "{stats:?}");
        for g in &gens {
            // Even on {1,2,3} and even on {3,4,5}.
            let flipped = |x: i32| g.contains_key(&lit(x));
            assert_eq!([1, 2, 3].iter().filter(|&&x| flipped(x)).count() % 2, 0);
            assert_eq!([3, 4, 5].iter().filter(|&&x| flipped(x)).count() % 2, 0);
        }
    }

    #[test]
    fn a_variable_in_no_clause_is_never_a_flip() {
        // Variable 4 is declared but absent (root-assigned or eliminated in
        // practice): it must not become a flip group of its own.
        let clauses = cnf(&[&[1, 2], &[-1, -2], &[3, 5], &[-3, 5]]);
        // Two genuine flips: {x1, x2} and {x3} (x3's two clauses differ only
        // in its sign); never x4.
        let (gens, stats) = run(&clauses, 5);
        assert_eq!(gens.len(), 2, "{stats:?}");
        assert!(gens.iter().all(|g| !g.contains_key(&lit(4))), "{gens:?}");
        let counts = super::super::build_formula_counts(&clauses);
        let (group, _) = find_flip_symmetries(&clauses, 5, &counts);
        let mut work = 0;
        let units = group.fixings(&mut work);
        assert!(
            units.iter().all(|(u, _)| u.variable().index() != 3),
            "{units:?}"
        );
    }

    #[test]
    fn a_lone_clause_pins_its_variables() {
        let clauses = cnf(&[&[1, 2], &[1, -2, 3]]);
        let (gens, stats) = run(&clauses, 3);
        assert!(gens.is_empty(), "{stats:?}");
        // Single-pattern groups pin their variables before any elimination.
        assert_eq!(stats.pinned, 3, "{stats:?}");
        assert_eq!(stats.equations, 0, "{stats:?}");
    }

    #[test]
    fn a_complementary_pair_flips_together() {
        let clauses = cnf(&[&[1, 2], &[-1, -2], &[3, 4]]);
        let (gens, stats) = run(&clauses, 4);
        assert_eq!(gens.len(), 1, "{stats:?}");
        assert!(gens[0].contains_key(&lit(1)) && gens[0].contains_key(&lit(2)));
        assert!(!gens[0].contains_key(&lit(3)));
    }

    #[test]
    fn multiplicities_are_respected() {
        // Twice (1 2), once (-1 -2): no flip maps the multiset to itself.
        let clauses = cnf(&[&[1, 2], &[1, 2], &[-1, -2]]);
        let (gens, stats) = run(&clauses, 2);
        assert!(gens.is_empty(), "{stats:?}");
    }

    #[test]
    fn pigeonhole_has_no_flips() {
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
        let (gens, _) = run(&clauses, 6);
        assert!(gens.is_empty());
    }

    #[test]
    fn elimination_null_space_is_orthogonal_to_every_row() {
        let mut e = Elimination::new(70);
        let rows: Vec<Vec<u32>> = vec![
            vec![0, 1, 2],
            vec![2, 3, 65],
            vec![1, 65, 69],
            vec![0, 3, 69],
        ];
        for r in &rows {
            e.insert(r);
        }
        assert_eq!(e.rank, 3, "the fourth row is the sum of the others");
        for x in e.null_space() {
            let support = support_columns(&x);
            for r in &rows {
                let parity = r.iter().filter(|v| support.contains(v)).count() % 2;
                assert_eq!(parity, 0, "null vector {x:?} vs row {r:?}");
            }
        }
    }
}
