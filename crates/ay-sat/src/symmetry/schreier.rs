// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Random Schreier–Sims over sparse permutations of variables.
//!
//! Step 2 of `competition/proof-posture-parity/PLAN-symmetry-fixing.md`: the
//! stabilizer chain that Satsuma's fix-and-cut walks (`dejavu::groups::
//! random_schreier`). A permutation is stored by its support; the chain keeps
//! one Schreier vector per base point, so a coset representative is
//! reconstructed by walking the vector rather than stored per orbit element.
//!
//! The chain is *random* Schreier–Sims: after the given generators are
//! sifted in, random products of the strong generators are sifted until
//! `RANDOM_SIFTS_TO_SETTLE` consecutive random elements sift to the identity.
//! The result is complete with high probability; fix-and-cut only needs
//! orbits of the pointwise stabilizers, and a missing strong generator can
//! only make an orbit *smaller* — a fix or cut derived from it stays sound
//! because every symmetry it uses is a real group element.
//!
//! Nothing here touches the formula; soundness of what is derived from the
//! chain rests on the generators being verified formula automorphisms, which
//! `detector::permutation_preserves_formula` guarantees upstream.

use std::collections::{hash_map::Entry, BTreeMap, HashMap};

/// A permutation of `u32` points given by its support: sorted `(x, image)`
/// pairs for every moved point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Perm {
    map: Vec<(u32, u32)>,
}

impl Perm {
    pub(crate) fn identity() -> Self {
        Self { map: Vec::new() }
    }

    /// Build from a sparse variable map (the detector's generator form).
    /// Fixed points and identity entries are dropped.
    pub(crate) fn from_map(map: &BTreeMap<u32, u32>) -> Self {
        let mut v: Vec<(u32, u32)> = map
            .iter()
            .map(|(&a, &b)| (a, b))
            .filter(|(a, b)| a != b)
            .collect();
        v.sort_unstable();
        Self { map: v }
    }

    #[inline]
    /// The moved points and their images, sorted by point.
    pub(crate) fn pairs(&self) -> &[(u32, u32)] {
        &self.map
    }

    pub(crate) fn is_identity(&self) -> bool {
        self.map.is_empty()
    }

    #[inline]
    pub(crate) fn support_len(&self) -> usize {
        self.map.len()
    }

    #[inline]
    pub(crate) fn support(&self) -> impl Iterator<Item = u32> + '_ {
        self.map.iter().map(|&(x, _)| x)
    }

    #[inline]
    pub(crate) fn apply(&self, x: u32) -> u32 {
        match self.map.binary_search_by_key(&x, |&(a, _)| a) {
            Ok(i) => self.map[i].1,
            Err(_) => x,
        }
    }

    pub(crate) fn inverse(&self) -> Self {
        let mut v: Vec<(u32, u32)> = self.map.iter().map(|&(a, b)| (b, a)).collect();
        v.sort_unstable();
        Self { map: v }
    }

    /// `self` then `other`: `x -> other(self(x))`.
    pub(crate) fn then(&self, other: &Self) -> Self {
        let mut points: Vec<u32> = self.support().chain(other.support()).collect();
        points.sort_unstable();
        points.dedup();
        let mut v = Vec::with_capacity(points.len());
        for x in points {
            let y = other.apply(self.apply(x));
            if y != x {
                v.push((x, y));
            }
        }
        Self { map: v }
    }
}

/// One level of the chain: the base point, the strong generators that fix
/// every earlier base point, the orbit of the base point under them, and the
/// Schreier vector giving, for each orbit element, the generator and the
/// element it was reached from.
#[derive(Clone, Debug)]
struct Level {
    point: u32,
    /// Strong generators of this level's group, as indices into the chain's
    /// pool: a generator fixing base[..i] belongs to every level up to the
    /// one whose point it moves, and is stored once.
    generators: Vec<usize>,
    /// orbit element -> (pool index of the generator, predecessor element);
    /// the base point maps to itself with `usize::MAX`.
    schreier: HashMap<u32, (usize, u32)>,
    orbit: Vec<u32>,
}

impl Level {
    fn new(point: u32) -> Self {
        let mut schreier = HashMap::new();
        schreier.insert(point, (usize::MAX, point));
        Self {
            point,
            generators: Vec::new(),
            schreier,
            orbit: vec![point],
        }
    }

    /// Extend the orbit with a new generator (and re-close under all).
    fn add_generator(&mut self, gi: usize, pool: &[Perm]) {
        self.generators.push(gi);
        self.reclose(pool);
    }

    fn reclose(&mut self, pool: &[Perm]) {
        let mut i = 0;
        while i < self.orbit.len() {
            let x = self.orbit[i];
            for &gi in &self.generators {
                let y = pool[gi].apply(x);
                if let Entry::Vacant(entry) = self.schreier.entry(y) {
                    entry.insert((gi, x));
                    self.orbit.push(y);
                }
            }
            i += 1;
        }
    }

    /// A coset representative `u` with `u(point) = y`, or `None` if `y` is
    /// not in the orbit.
    fn representative(&self, y: u32, pool: &[Perm]) -> Option<Perm> {
        if !self.schreier.contains_key(&y) {
            return None;
        }
        let mut path: Vec<usize> = Vec::new();
        let mut cur = y;
        while cur != self.point {
            let (gi, prev) = self.schreier[&cur];
            path.push(gi);
            cur = prev;
        }
        let mut u = Perm::identity();
        for &gi in path.iter().rev() {
            u = u.then(&pool[gi]);
        }
        Some(u)
    }
}

/// Consecutive random elements that must sift to the identity before the
/// chain is taken as complete.
const RANDOM_SIFTS_TO_SETTLE: u32 = 12;

/// The stabilizer chain.
#[derive(Clone, Debug)]
pub(crate) struct SchreierSims {
    /// Every strong generator, stored once; levels refer to it by index.
    pool: Vec<Perm>,
    levels: Vec<Level>,
    /// Base points chosen by the caller (`extend_base`) come first.
    chosen: usize,
    /// Every generator ever added, for random products.
    all_generators: Vec<Perm>,
    rng: u64,
    /// Work counter: support elements touched, for budgets.
    work: u64,
}

impl SchreierSims {
    pub(crate) fn new(seed: u64) -> Self {
        Self {
            pool: Vec::new(),
            levels: Vec::new(),
            chosen: 0,
            all_generators: Vec::new(),
            rng: seed | 1,
            work: 0,
        }
    }

    pub(crate) fn work(&self) -> u64 {
        self.work
    }

    #[cfg(test)]
    pub(crate) fn base(&self) -> Vec<u32> {
        self.levels.iter().map(|l| l.point).collect()
    }

    pub(crate) fn depth(&self) -> usize {
        self.levels.len()
    }

    fn next_random(&mut self) -> u64 {
        // xorshift64*
        let mut x = self.rng;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.rng = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    /// Sift `g` through the chain from `from_level`. Returns the residue and
    /// the level at which sifting stopped (`levels.len()` if it passed every
    /// level); a residue that is the identity means `g` is in the group
    /// generated so far.
    fn sift_from(&mut self, mut g: Perm, from_level: usize) -> (Perm, usize) {
        let mut level = from_level;
        while level < self.levels.len() {
            let point = self.levels[level].point;
            let y = g.apply(point);
            self.work += g.support_len() as u64;
            if y == point {
                level += 1;
                continue;
            }
            match self.levels[level].representative(y, &self.pool) {
                Some(u) => {
                    g = g.then(&u.inverse());
                    level += 1;
                }
                None => return (g, level),
            }
        }
        (g, level)
    }

    /// Add a residue as a strong generator at `level`, creating levels as
    /// needed (the base is extended by a point the residue moves).
    fn install(&mut self, g: Perm, mut level: usize) {
        if g.is_identity() {
            return;
        }
        let gi = self.pool.len();
        self.pool.push(g);
        loop {
            if level == self.levels.len() {
                let Some(point) = self.pool[gi].support().next() else {
                    return;
                };
                self.levels.push(Level::new(point));
            }
            let point = self.levels[level].point;
            let moves = self.pool[gi].apply(point) != point;
            // The generator fixes base[..level], so it is a strong generator
            // of this level's group (it may still move points of the orbit
            // even when it fixes the base point); it stops at the first
            // level whose base point it moves.
            let (levels, pool) = (&mut self.levels, &self.pool);
            levels[level].add_generator(gi, pool);
            if moves {
                return;
            }
            level += 1;
        }
    }

    /// Add a group generator and settle the chain (random Schreier–Sims).
    pub(crate) fn add_generator(&mut self, g: Perm) {
        if g.is_identity() {
            return;
        }
        self.all_generators.push(g.clone());
        let (residue, level) = self.sift_from(g, 0);
        if !residue.is_identity() {
            self.install(residue, level);
        }
    }

    /// A random element of the group generated so far: a product of a few
    /// random generators (product replacement would mix better; this is
    /// enough for the acceptance tests and is cheap).
    fn random_element(&mut self) -> Perm {
        let n = self.all_generators.len();
        let mut g = Perm::identity();
        if n == 0 {
            return g;
        }
        let k = 2 + (self.next_random() % 4) as usize;
        for _ in 0..k {
            let i = (self.next_random() % n as u64) as usize;
            let h = self.all_generators[i].clone();
            g = if self.next_random() & 1 == 0 {
                g.then(&h)
            } else {
                g.then(&h.inverse())
            };
        }
        g
    }

    /// Random sifts until the chain looks complete; call once after the
    /// generators are added (`add_generator` does not settle: with a
    /// thousand generators a settle per add is quadratic).
    pub(crate) fn settle(&mut self) {
        let mut clean = 0;
        while clean < RANDOM_SIFTS_TO_SETTLE {
            let g = self.random_element();
            let (residue, level) = self.sift_from(g, 0);
            if residue.is_identity() {
                clean += 1;
            } else {
                self.install(residue, level);
                clean = 0;
            }
        }
    }

    /// Make `point` the next *chosen* base point (fix-and-cut fixes a
    /// variable and continues in its stabilizer): it is inserted after the
    /// base points chosen so far, and the levels the search had appended on
    /// its own are rebuilt behind it, so `stabilizer_orbits(chosen)` is the
    /// stabilizer of exactly the chosen points.
    pub(crate) fn extend_base(&mut self, point: u32) {
        if self.levels[..self.chosen].iter().any(|l| l.point == point) {
            return;
        }
        let tail: Vec<Level> = self.levels.drain(self.chosen..).collect();
        self.levels.push(Level::new(point));
        self.chosen += 1;
        // Re-sift every generator the drained levels held (each once).
        let mut seen: Vec<usize> = tail
            .iter()
            .flat_map(|l| l.generators.iter().copied())
            .collect();
        seen.sort_unstable();
        seen.dedup();
        let gens: Vec<Perm> = seen.into_iter().map(|gi| self.pool[gi].clone()).collect();
        for g in gens {
            let (residue, level) = self.sift_from(g, self.chosen - 1);
            if !residue.is_identity() {
                self.install(residue, level);
            }
        }
        self.settle();
    }

    /// How many base points were chosen through `extend_base`.
    pub(crate) fn chosen(&self) -> usize {
        self.chosen
    }

    /// Orbits of the pointwise stabilizer of the first `level` base points,
    /// as a union-find parent array over `domain` points (only moved points
    /// are non-trivial). `level == 0` is the whole group.
    pub(crate) fn stabilizer_orbits(&self, level: usize, domain: u32) -> Orbits {
        let mut uf = Orbits::new(domain);
        // The stabilizer of base[..level] is generated by the strong
        // generators that fix those points: every generator stored at a
        // level >= `level` fixes base[..level] by construction; generators at
        // earlier levels may also fix them, and are included when they do.
        // A generator sits in several levels; apply each once.
        let mut applied = vec![false; self.pool.len()];
        for (li, l) in self.levels.iter().enumerate() {
            for &gi in &l.generators {
                if applied[gi] {
                    continue;
                }
                let g = &self.pool[gi];
                let fixes_prefix = li >= level
                    || self.levels[..level]
                        .iter()
                        .all(|b| g.apply(b.point) == b.point);
                if fixes_prefix {
                    applied[gi] = true;
                    for x in g.support() {
                        uf.union(x, g.apply(x));
                    }
                }
            }
        }
        uf
    }

    /// The orbit of base[`level`] under the level's group (the points a
    /// transversal element reaches); empty for a level the chain lacks.
    pub(crate) fn level_orbit(&self, level: usize) -> &[u32] {
        self.levels.get(level).map_or(&[], |l| l.orbit.as_slice())
    }

    /// A group element carrying base[`level`] to `y` (a product of the
    /// level's strong generators, so it fixes base[..level]), or `None` when
    /// `y` is outside the level's orbit.
    pub(crate) fn transversal(&self, level: usize, y: u32) -> Option<Perm> {
        self.levels
            .get(level)
            .and_then(|l| l.representative(y, &self.pool))
    }

    /// Whether `y` is in the orbit of base[`level`] under the level's group.
    pub(crate) fn in_level_orbit(&self, level: usize, y: u32) -> bool {
        self.levels
            .get(level)
            .is_some_and(|l| l.schreier.contains_key(&y))
    }
}

/// What the chain says about a generator set, for the stats.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct ChainSummary {
    pub(crate) generators: u64,
    pub(crate) base_len: u64,
    /// Orbits of size at least two under the whole group.
    pub(crate) orbits: u64,
    pub(crate) work: u64,
}

/// Build the chain over sparse variable maps and summarise it.
pub(crate) fn summarise_generators(
    generators: &[BTreeMap<u32, u32>],
    domain: u32,
    seed: u64,
) -> ChainSummary {
    let mut chain = SchreierSims::new(seed);
    for g in generators {
        chain.add_generator(Perm::from_map(g));
    }
    chain.settle();
    let mut orbits = chain.stabilizer_orbits(0, domain);
    let mut counted = std::collections::HashSet::new();
    let mut nontrivial = 0u64;
    for g in generators {
        for &x in g.keys() {
            let r = orbits.find(x);
            if counted.insert(r) && orbits.orbit_size(x) >= 2 {
                nontrivial += 1;
            }
        }
    }
    ChainSummary {
        generators: generators.len() as u64,
        base_len: chain.depth() as u64,
        orbits: nontrivial,
        work: chain.work(),
    }
}

/// Union-find over `u32` points.
#[derive(Clone, Debug)]
pub(crate) struct Orbits {
    parent: Vec<u32>,
    size: Vec<u32>,
    /// Successful unions: zero means every orbit is a singleton.
    unions: u32,
}

impl Orbits {
    pub(crate) fn new(domain: u32) -> Self {
        Self {
            parent: (0..domain).collect(),
            size: vec![1; domain as usize],
            unions: 0,
        }
    }

    pub(crate) fn unions(&self) -> u32 {
        self.unions
    }

    /// Whether any orbit has at least two points.
    pub(crate) fn nontrivial(&self) -> bool {
        self.unions > 0
    }

    pub(crate) fn find(&mut self, mut x: u32) -> u32 {
        while self.parent[x as usize] != x {
            let p = self.parent[x as usize];
            self.parent[x as usize] = self.parent[p as usize];
            x = p;
        }
        x
    }

    pub(crate) fn union(&mut self, a: u32, b: u32) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return;
        }
        let (big, small) = if self.size[ra as usize] >= self.size[rb as usize] {
            (ra, rb)
        } else {
            (rb, ra)
        };
        self.parent[small as usize] = big;
        self.size[big as usize] += self.size[small as usize];
        self.unions += 1;
    }

    pub(crate) fn orbit_size(&mut self, x: u32) -> u32 {
        let r = self.find(x);
        self.size[r as usize]
    }

    pub(crate) fn same_orbit(&mut self, a: u32, b: u32) -> bool {
        self.find(a) == self.find(b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn perm(pairs: &[(u32, u32)]) -> Perm {
        let mut m = BTreeMap::new();
        for &(a, b) in pairs {
            m.insert(a, b);
        }
        Perm::from_map(&m)
    }

    fn cycle(points: &[u32]) -> Perm {
        let mut pairs = Vec::new();
        for i in 0..points.len() {
            pairs.push((points[i], points[(i + 1) % points.len()]));
        }
        perm(&pairs)
    }

    #[test]
    fn perm_composition_and_inverse() {
        let a = cycle(&[0, 1, 2]);
        let b = perm(&[(0, 1), (1, 0)]);
        let ab = a.then(&b);
        assert_eq!(ab.apply(0), b.apply(a.apply(0)));
        assert_eq!(ab.apply(2), b.apply(a.apply(2)));
        assert!(a.then(&a.inverse()).is_identity());
        assert!(perm(&[]).is_identity());
    }

    #[test]
    fn symmetric_group_orbits_and_stabilizers() {
        // S4 on {0,1,2,3} from a transposition and a 4-cycle.
        let mut ss = SchreierSims::new(7);
        ss.add_generator(perm(&[(0, 1), (1, 0)]));
        ss.add_generator(cycle(&[0, 1, 2, 3]));
        ss.settle();
        let mut whole = ss.stabilizer_orbits(0, 4);
        assert_eq!(whole.orbit_size(0), 4);
        assert!(whole.same_orbit(0, 3));
        // Fixing base[0] leaves S3 on the other three points.
        let b0 = ss.base()[0];
        let mut stab = ss.stabilizer_orbits(1, 4);
        assert_eq!(stab.orbit_size(b0), 1, "the first base point is fixed");
        let others: Vec<u32> = (0..4).filter(|&x| x != b0).collect();
        assert_eq!(
            stab.orbit_size(others[0]),
            3,
            "S3 is transitive on the rest"
        );
        assert!(ss.depth() >= 2, "S4 needs a base of length at least 3");
    }

    #[test]
    fn extending_the_base_fixes_the_point() {
        let mut ss = SchreierSims::new(11);
        ss.add_generator(cycle(&[0, 1, 2, 3, 4]));
        ss.add_generator(perm(&[(0, 1), (1, 0)]));
        ss.settle();
        let mut whole = ss.stabilizer_orbits(0, 5);
        assert_eq!(whole.orbit_size(2), 5);
        ss.extend_base(2);
        assert_eq!(ss.base()[0], 2, "the chosen point leads the base");
        assert_eq!(ss.chosen(), 1);
        let mut stab = ss.stabilizer_orbits(1, 5);
        assert_eq!(stab.orbit_size(2), 1);
        assert_eq!(
            stab.orbit_size(0),
            4,
            "S5's point stabilizer is S4 on the rest"
        );
        // A second chosen point: the stabilizer of both is S3 on the rest.
        ss.extend_base(0);
        assert_eq!(&ss.base()[..2], &[2, 0]);
        let mut stab2 = ss.stabilizer_orbits(2, 5);
        assert_eq!(stab2.orbit_size(0), 1);
        assert_eq!(stab2.orbit_size(1), 3);
    }

    #[test]
    fn a_product_of_disjoint_cycles_has_separate_orbits() {
        let mut ss = SchreierSims::new(3);
        ss.add_generator(cycle(&[0, 1, 2]).then(&cycle(&[5, 6])));
        ss.settle();
        let mut o = ss.stabilizer_orbits(0, 8);
        assert_eq!(o.orbit_size(0), 3);
        assert_eq!(o.orbit_size(5), 2);
        assert_eq!(o.orbit_size(3), 1);
        assert!(!o.same_orbit(0, 5));
    }

    #[test]
    fn sifting_a_group_element_leaves_no_residue() {
        let mut ss = SchreierSims::new(5);
        let a = cycle(&[0, 1, 2, 3, 4, 5]);
        let b = perm(&[(0, 1), (1, 0)]);
        ss.add_generator(a.clone());
        ss.add_generator(b.clone());
        ss.settle();
        let g = a.then(&b).then(&a).then(&b.inverse());
        let (residue, _) = ss.sift_from(g, 0);
        assert!(residue.is_identity());
        let outside = perm(&[(6, 7), (7, 6)]);
        let (residue, _) = ss.sift_from(outside, 0);
        assert!(!residue.is_identity());
    }
}
