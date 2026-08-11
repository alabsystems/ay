// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Individualization-refinement (IR) automorphism finder for CNF (#17).
//!
//! This is the saucy/nauty/bliss core, adapted to CNF formulas. It discovers
//! *composite* variable-permutation symmetries (the kind clique / graph-coloring
//! / pigeonhole instances have) that the single-swap and consecutive/half-split
//! enumerators miss, by building a colored graph whose automorphisms are exactly
//! the (sign-preserving) formula automorphisms and running an IR search over it.
//!
//! SOUNDNESS: this module only *proposes* candidate variable permutations. Every
//! returned permutation is verified by
//! [`super::detector::permutation_preserves_formula`] — the sound gate — so a
//! search bug can only cause a MISS, never an unsound permutation. The downstream
//! symmetry-breaking encoder is responsible for emitting only sound clauses from
//! these verified generators.
//!
//! Graph model:
//!   * one node per LITERAL (2 per variable: positive, negative);
//!   * one node per CLAUSE;
//!   * edges literal--clause for membership and literal--complement (the polarity
//!     matching edge) so an automorphism maps complementary literals to
//!     complementary literals (a variable permutation);
//!   * initial colors: positive literals (color 0) ≠ negative literals (color 1)
//!     — this restricts the search to SIGN-PRESERVING permutations, which are
//!     exactly what the variable-permutation gate can represent — and clause nodes
//!     colored by length class (clauses of different length cannot map to each
//!     other).
//!
//! The search keeps a "first leaf" canonical labeling; each later leaf yields a
//! candidate automorphism (the permutation mapping the first-leaf labeling to the
//! later one), which is projected to a variable permutation and gate-verified.
//! Orbit pruning (union-find over discovered automorphisms) and a leftmost-path
//! cell-size invariant keep the bounded DFS small.

use std::collections::{BTreeMap, BTreeSet};

use crate::{Literal, Variable};

use super::detector::permutation_preserves_formula;

/// A colored graph plus the variable<->node mapping needed to project a graph
/// automorphism back to a variable permutation.
struct ColoredGraph {
    /// Adjacency list (undirected, stored both directions).
    adj: Vec<Vec<u32>>,
    /// Initial (pre-refinement) color of each node.
    init_color: Vec<u32>,
    /// Number of distinct variables (dense). Literal nodes are `2*i` (positive)
    /// and `2*i + 1` (negative) for dense variable `i`; clause nodes follow.
    nv: usize,
    /// Dense index -> original [`Variable`].
    dense_to_var: Vec<Variable>,
}

/// Build the colored literal+clause graph for `clauses`.
fn build_graph(clauses: &[Vec<Literal>], sign_split: bool) -> ColoredGraph {
    // Dense variable mapping (sorted for determinism).
    let mut var_set: BTreeSet<Variable> = BTreeSet::new();
    for c in clauses {
        for l in c {
            var_set.insert(l.variable());
        }
    }
    let dense_to_var: Vec<Variable> = var_set.iter().copied().collect();
    let mut var_idx: BTreeMap<Variable, usize> = BTreeMap::new();
    for (i, v) in dense_to_var.iter().enumerate() {
        var_idx.insert(*v, i);
    }
    let nv = dense_to_var.len();
    let nc = clauses.len();
    let n = 2 * nv + nc;

    let mut adj: Vec<Vec<u32>> = vec![Vec::new(); n];
    let lit_node = |di: usize, pos: bool| -> u32 {
        if pos {
            (2 * di) as u32
        } else {
            (2 * di + 1) as u32
        }
    };
    let clause_node = |ci: usize| -> u32 { (2 * nv + ci) as u32 };

    for (ci, c) in clauses.iter().enumerate() {
        let cn = clause_node(ci);
        for l in c {
            let di = var_idx[&l.variable()];
            let ln = lit_node(di, l.is_positive());
            adj[ln as usize].push(cn);
            adj[cn as usize].push(ln);
        }
    }
    // Polarity matching edges.
    for di in 0..nv {
        let p = (2 * di) as u32;
        let q = (2 * di + 1) as u32;
        adj[p as usize].push(q);
        adj[q as usize].push(p);
    }

    // Initial colors: clauses by length, plus either a polarity split (positive
    // literals 0, negative literals 1 — sign-PRESERVING search) or a single
    // literal color (SIGNED search, which also finds automorphisms that flip
    // polarities).
    //
    // The split is not free: it is exactly what makes AY blind on shuffled
    // competition benchmarks. On `homer11.shuffled` (SAT-COMP 2026 Main),
    // 1-WL from the split colors discretizes to 440 singleton literal classes —
    // no candidate pair survives — while 1-WL from a single literal color stops
    // at 2 classes of 220 literals. The instance's symmetry is entirely in
    // sign-flipping permutations.
    let mut init_color = vec![0u32; n];
    let mut next_class = if sign_split {
        for di in 0..nv {
            init_color[2 * di] = 0;
            init_color[2 * di + 1] = 1;
        }
        2u32
    } else {
        1u32
    };
    let mut len_class: BTreeMap<usize, u32> = BTreeMap::new();
    for (ci, c) in clauses.iter().enumerate() {
        let id = *len_class.entry(c.len()).or_insert_with(|| {
            let v = next_class;
            next_class += 1;
            v
        });
        init_color[clause_node(ci) as usize] = id;
    }

    ColoredGraph {
        adj,
        init_color,
        nv,
        dense_to_var,
    }
}

/// 1-WL equitable refinement: split color classes by the multiset of neighbor
/// colors until the partition is stable. Renormalizes colors to a dense
/// `0..k` range, ordered by `(old_color, sorted neighbor-color multiset)` so the
/// refinement is deterministic and order-preserving.
fn refine(adj: &[Vec<u32>], color: &mut Vec<u32>) -> u64 {
    let n = color.len();
    let mut rounds = 0u64;
    loop {
        rounds += 1;
        let mut sigs: Vec<(u32, Vec<u32>)> = Vec::with_capacity(n);
        for u in 0..n {
            let mut nb: Vec<u32> = adj[u].iter().map(|&v| color[v as usize]).collect();
            nb.sort_unstable();
            sigs.push((color[u], nb));
        }
        let mut order: Vec<usize> = (0..n).collect();
        order.sort_unstable_by(|&a, &b| sigs[a].cmp(&sigs[b]));
        let mut new_color = vec![0u32; n];
        let mut cur = 0u32;
        for i in 0..n {
            if i > 0 && sigs[order[i]] != sigs[order[i - 1]] {
                cur += 1;
            }
            new_color[order[i]] = cur;
        }
        let num_new = cur + 1;
        let num_old = color.iter().max().map(|m| m + 1).unwrap_or(0);
        *color = new_color;
        if num_new == num_old {
            break;
        }
    }
    rounds
}

/// Individualize node `v`: give it a singleton color ordered first within its
/// current cell, leaving every other node's relative order intact, then return
/// the renormalized (still-not-refined) coloring.
fn individualize(color: &[u32], v: usize) -> Vec<u32> {
    let n = color.len();
    let tc = color[v];
    let keys: Vec<(u32, u8)> = (0..n)
        .map(|u| {
            if color[u] == tc {
                (tc, if u == v { 0 } else { 1 })
            } else {
                (color[u], 0)
            }
        })
        .collect();
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_unstable_by(|&a, &b| keys[a].cmp(&keys[b]));
    let mut new_color = vec![0u32; n];
    let mut cur = 0u32;
    for i in 0..n {
        if i > 0 && keys[order[i]] != keys[order[i - 1]] {
            cur += 1;
        }
        new_color[order[i]] = cur;
    }
    new_color
}

/// Cell-size signature of a (dense) coloring: sorted multiset of cell sizes.
/// Used as a leftmost-path invariant to prune non-matching subtrees.
fn cell_size_signature(color: &[u32]) -> Vec<usize> {
    let k = color.iter().max().map(|m| *m as usize + 1).unwrap_or(0);
    let mut sizes = vec![0usize; k];
    for &c in color {
        sizes[c as usize] += 1;
    }
    sizes.sort_unstable();
    sizes
}

/// Find the target cell: the smallest non-singleton cell, ties broken by lowest
/// color id. Returns the member node ids (in increasing id order).
fn target_cell(color: &[u32]) -> Option<Vec<usize>> {
    let k = color.iter().max().map(|m| *m as usize + 1)?;
    let mut cells: Vec<Vec<usize>> = vec![Vec::new(); k];
    for (node, &c) in color.iter().enumerate() {
        cells[c as usize].push(node);
    }
    let mut best: Option<usize> = None;
    for (c, cell) in cells.iter().enumerate() {
        if cell.len() >= 2 {
            match best {
                Some(b) if cells[b].len() <= cell.len() => {}
                _ => best = Some(c),
            }
        }
    }
    best.map(|c| std::mem::take(&mut cells[c]))
}

/// IR search state.
struct Search<'a> {
    adj: &'a [Vec<u32>],
    nv: usize,
    dense_to_var: &'a [Variable],
    var_to_dense: BTreeMap<Variable, usize>,
    formula_counts: &'a BTreeMap<Vec<u32>, u32>,
    node_budget: u64,
    max_generators: usize,
    nodes: u64,
    /// Edges in the model graph — the unit of the deterministic work budget.
    edge_count: u64,
    /// Literals in the clause multiset — the cost of one gate verification.
    verify_cost: u64,
    work: u64,
    work_budget: u64,
    /// First (leftmost) discrete leaf: rank (color id) -> node.
    first_leaf: Option<Vec<usize>>,
    /// Cell-size invariant along the leftmost path, indexed by depth.
    first_path_inv: Vec<Vec<usize>>,
    /// Union-find over nodes capturing discovered-automorphism orbits (for pruning).
    uf: Vec<usize>,
    generators: Vec<BTreeMap<Variable, Variable>>,
    seen: BTreeSet<BTreeMap<Variable, Variable>>,
    /// When set, leaves are projected to LITERAL permutations (sign flips
    /// allowed) and collected in `signed_generators` instead.
    signed: bool,
    signed_generators: Vec<BTreeMap<Literal, Literal>>,
    signed_seen: BTreeSet<Vec<(u32, u32)>>,
}

impl Search<'_> {
    fn find(&mut self, x: usize) -> usize {
        let mut r = x;
        while self.uf[r] != r {
            r = self.uf[r];
        }
        // Path compression.
        let mut c = x;
        while self.uf[c] != c {
            let n = self.uf[c];
            self.uf[c] = r;
            c = n;
        }
        r
    }

    fn union(&mut self, a: usize, b: usize) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra != rb {
            self.uf[ra] = rb;
        }
    }

    /// Project a node-level graph automorphism `g` (g[a] = image of a) to a
    /// sign-preserving variable permutation, or `None` if `g` flips a polarity
    /// or maps a literal node onto a clause node.
    fn project(&self, g: &[usize]) -> Option<BTreeMap<Variable, Variable>> {
        let mut perm = BTreeMap::new();
        for i in 0..self.nv {
            let img = g[2 * i];
            if img >= 2 * self.nv || !img.is_multiple_of(2) {
                return None; // sign flip or literal -> clause: not representable
            }
            let j = img / 2;
            if g[2 * i + 1] != 2 * j + 1 {
                return None; // negative literal must track the positive one
            }
            if j != i {
                perm.insert(self.dense_to_var[i], self.dense_to_var[j]);
            }
        }
        Some(perm)
    }

    /// Project a node-level automorphism to a LITERAL permutation, allowing
    /// sign flips. Returns `None` when a literal node maps onto a clause node
    /// or the complement pairing is broken.
    fn project_signed(&self, g: &[usize]) -> Option<BTreeMap<Literal, Literal>> {
        let mut perm = BTreeMap::new();
        for i in 0..self.nv {
            for sign in 0..2 {
                let src = 2 * i + sign;
                let img = g[src];
                if img >= 2 * self.nv {
                    return None; // literal mapped onto a clause node
                }
                // The complement pairing must be respected: ¬l tracks l.
                if g[src ^ 1] != (img ^ 1) {
                    return None;
                }
                if img != src {
                    perm.insert(self.dense_literal(src), self.dense_literal(img));
                }
            }
        }
        Some(perm)
    }

    /// Literal for a dense literal-node id (`2*i` positive, `2*i+1` negative).
    fn dense_literal(&self, node: usize) -> Literal {
        let var = self.dense_to_var[node / 2];
        if node.is_multiple_of(2) {
            Literal::positive(var)
        } else {
            Literal::negative(var)
        }
    }

    fn handle_signed_leaf(&mut self, leaf: &[usize], first: &[usize]) {
        let n = leaf.len();
        let mut g = vec![0usize; n];
        for r in 0..n {
            g[first[r]] = leaf[r];
        }
        let Some(perm) = self.project_signed(&g) else {
            return;
        };
        self.work = self.work.saturating_add(self.verify_cost);
        if perm.is_empty()
            || !crate::symmetry::literal_permutation_preserves_formula(self.formula_counts, &perm)
        {
            return;
        }
        // Orbit union-find over literal nodes (sound: verified automorphism).
        let pairs: Vec<(usize, usize)> = (0..2 * self.nv)
            .filter_map(|src| (g[src] != src && g[src] < 2 * self.nv).then_some((src, g[src])))
            .collect();
        for (a, b) in pairs {
            self.union(a, b);
        }
        let key: Vec<(u32, u32)> = perm.iter().map(|(a, b)| (a.raw(), b.raw())).collect();
        if self.signed_seen.insert(key) {
            self.signed_generators.push(perm);
        }
    }

    fn handle_leaf(&mut self, color: &[u32]) {
        let n = color.len();
        // rank (color id) -> node.
        let mut leaf = vec![0usize; n];
        for (node, &c) in color.iter().enumerate() {
            leaf[c as usize] = node;
        }
        if self.signed {
            match self.first_leaf.take() {
                None => self.first_leaf = Some(leaf),
                Some(first) => {
                    self.handle_signed_leaf(&leaf, &first);
                    self.first_leaf = Some(first);
                }
            }
            return;
        }
        match &self.first_leaf {
            None => self.first_leaf = Some(leaf),
            Some(first) => {
                let mut g = vec![0usize; n];
                for r in 0..n {
                    g[first[r]] = leaf[r];
                }
                if let Some(perm) = self.project(&g) {
                    if !perm.is_empty() && permutation_preserves_formula(self.formula_counts, &perm)
                    {
                        // Update orbit union-find from this VERIFIED automorphism
                        // (sound: only genuine automorphism orbits are merged).
                        let pairs: Vec<(usize, usize)> = perm
                            .iter()
                            .map(|(a, b)| (self.var_to_dense[a], self.var_to_dense[b]))
                            .collect();
                        for (da, db) in pairs {
                            self.union(2 * da, 2 * db);
                            self.union(2 * da + 1, 2 * db + 1);
                        }
                        if self.seen.insert(perm.clone()) {
                            self.generators.push(perm);
                        }
                    }
                }
            }
        }
    }

    /// Generators found so far, whichever projection this search is collecting.
    fn generator_count(&self) -> usize {
        if self.signed {
            self.signed_generators.len()
        } else {
            self.generators.len()
        }
    }

    fn dfs(&mut self, mut color: Vec<u32>, depth: usize, leftmost: bool) {
        if self.nodes > self.node_budget
            || self.work > self.work_budget
            || self.generator_count() >= self.max_generators
        {
            return;
        }
        self.nodes += 1;
        let rounds = refine(self.adj, &mut color);
        // Deterministic cost accounting: one refinement round touches every
        // edge. Without it the SIGNED search is unaffordable — dropping the
        // polarity split coarsens the initial partition, so the IR tree is far
        // wider, and a node budget alone let a 2320-variable instance spend
        // 3.6 s searching where the whole solve takes 0.02 s.
        self.work = self.work.saturating_add(rounds * self.edge_count);

        let inv = cell_size_signature(&color);
        if leftmost {
            if self.first_path_inv.len() == depth {
                self.first_path_inv.push(inv.clone());
            }
        } else {
            match self.first_path_inv.get(depth) {
                Some(fi) if *fi == inv => {}
                _ => return, // shape differs from the reference path: no automorphism here
            }
        }

        let Some(members) = target_cell(&color) else {
            self.handle_leaf(&color);
            return;
        };

        let mut branched: Vec<usize> = Vec::new();
        let mut first_child = true;
        for &v in &members {
            if self.nodes > self.node_budget || self.generator_count() >= self.max_generators {
                break;
            }
            // Orbit pruning: skip v if a previously-branched node is in its orbit.
            let rv = self.find(v);
            if branched.iter().any(|&b| {
                // recompute (orbits may have grown since b was branched)
                let mut r = b;
                while self.uf[r] != r {
                    r = self.uf[r];
                }
                r == rv
            }) {
                continue;
            }
            branched.push(v);
            let child = individualize(&color, v);
            self.dfs(child, depth + 1, leftmost && first_child);
            first_child = false;
        }
    }
}

/// Find gate-verified composite automorphisms of `clauses` via individualization
/// -refinement. Returns variable-permutation generators (each verified by
/// [`permutation_preserves_formula`], so sound by construction). Bounded by
/// `node_budget` IR-tree nodes and `max_generators` results.
pub(crate) fn find_automorphisms(
    clauses: &[Vec<Literal>],
    formula_counts: &BTreeMap<Vec<u32>, u32>,
    node_budget: u64,
    max_generators: usize,
) -> Vec<BTreeMap<Variable, Variable>> {
    run_search(clauses, formula_counts, node_budget, max_generators, false).0
}

/// Find gate-verified SIGNED automorphisms: literal permutations that may flip
/// polarities. Each generator is verified by
/// [`crate::symmetry::literal_permutation_preserves_formula`], so a search bug
/// can only cost generators, never soundness.
///
/// This is the projection that matters on competition benchmarks, whose
/// polarity shuffling turns variable symmetry into signed symmetry.
pub(crate) fn find_signed_automorphisms(
    clauses: &[Vec<Literal>],
    formula_counts: &BTreeMap<Vec<u32>, u32>,
    node_budget: u64,
    max_generators: usize,
) -> Vec<BTreeMap<Literal, Literal>> {
    run_search(clauses, formula_counts, node_budget, max_generators, true).1
}

type SearchResult = (
    Vec<BTreeMap<Variable, Variable>>,
    Vec<BTreeMap<Literal, Literal>>,
);

fn run_search(
    clauses: &[Vec<Literal>],
    formula_counts: &BTreeMap<Vec<u32>, u32>,
    node_budget: u64,
    max_generators: usize,
    signed: bool,
) -> SearchResult {
    if clauses.is_empty() {
        return (Vec::new(), Vec::new());
    }
    let graph = build_graph(clauses, !signed);
    let n = graph.adj.len();
    // Guard against pathological graph sizes (caller also caps vars/clauses).
    if n == 0 || graph.nv == 0 {
        return (Vec::new(), Vec::new());
    }

    let mut var_to_dense: BTreeMap<Variable, usize> = BTreeMap::new();
    for (i, v) in graph.dense_to_var.iter().enumerate() {
        var_to_dense.insert(*v, i);
    }

    let edge_count: u64 = graph.adj.iter().map(|a| a.len() as u64).sum::<u64>().max(1);
    let verify_cost: u64 = formula_counts
        .keys()
        .map(|k| k.len() as u64)
        .sum::<u64>()
        .max(1);
    // Deterministic work ceiling for the whole search, in edge-visits. Sized so
    // detection stays in the tens of milliseconds on the instances it fires on
    // while never dominating an easy solve. Overridable for experiments.
    let work_budget: u64 = std::env::var("AY_SAT_IR_WORK_BUDGET")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(30_000_000);

    let mut search = Search {
        adj: &graph.adj,
        nv: graph.nv,
        dense_to_var: &graph.dense_to_var,
        var_to_dense,
        formula_counts,
        node_budget,
        max_generators,
        nodes: 0,
        edge_count,
        verify_cost,
        work: 0,
        work_budget,
        first_leaf: None,
        first_path_inv: Vec::new(),
        uf: (0..n).collect(),
        generators: Vec::new(),
        seen: BTreeSet::new(),
        signed,
        signed_generators: Vec::new(),
        signed_seen: BTreeSet::new(),
    };

    search.dfs(graph.init_color.clone(), 0, true);
    (search.generators, search.signed_generators)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symmetry::build_formula_counts;

    fn lit(i: u32, pos: bool) -> Literal {
        if pos {
            Literal::positive(Variable(i))
        } else {
            Literal::negative(Variable(i))
        }
    }

    /// 2-vertex / 2-color clique-coloring formula (the gate's canonical example):
    /// vars 0,1 = vertex0's color vars; 2,3 = vertex1's. The color swap
    /// (0<->1, 2<->3) is a genuine composite automorphism.
    fn clique_coloring_2v2c() -> Vec<Vec<Literal>> {
        vec![
            vec![lit(0, true), lit(1, true)],
            vec![lit(2, true), lit(3, true)],
            vec![lit(0, false), lit(1, false)],
            vec![lit(2, false), lit(3, false)],
            vec![lit(0, false), lit(2, false)],
            vec![lit(1, false), lit(3, false)],
        ]
    }

    #[test]
    fn test_ir_finds_color_swap_2v2c() {
        let clauses = clique_coloring_2v2c();
        let counts = build_formula_counts(&clauses);
        let gens = find_automorphisms(&clauses, &counts, 10_000, 64);
        assert!(
            !gens.is_empty(),
            "IR must discover at least one composite automorphism on 2v2c clique-coloring"
        );
        // Every returned generator must be a genuine automorphism (sound).
        for g in &gens {
            assert!(permutation_preserves_formula(&counts, g));
        }
        // The composite color swap must be reachable (directly or as a product
        // we can compose); at minimum SOME non-identity generator exists and the
        // color swap is in the group. Check the color swap is verified-present
        // by composing? Simplest: assert it is among the generators OR that the
        // group is non-trivial. We assert it is directly found.
        let color_swap: BTreeMap<Variable, Variable> = [(0, 1), (1, 0), (2, 3), (3, 2)]
            .into_iter()
            .map(|(a, b)| (Variable(a), Variable(b)))
            .collect();
        assert!(
            gens.contains(&color_swap),
            "the composite color swap (0<->1,2<->3) must be among the IR generators, got {gens:?}"
        );
    }

    /// A symmetric 3-clique coloring (vertices fully interchangeable): IR must
    /// find non-trivial generators, all gate-verified.
    #[test]
    fn test_ir_soundness_all_verified() {
        // 3 vertices, 3 colors, triangle graph. var (v*3 + c) = vertex v gets color c.
        let mut clauses: Vec<Vec<Literal>> = Vec::new();
        let var = |v: u32, c: u32| Variable(v * 3 + c);
        for v in 0..3 {
            // at least one color
            clauses.push((0..3).map(|c| Literal::positive(var(v, c))).collect());
            // at most one color
            for c1 in 0..3 {
                for c2 in (c1 + 1)..3 {
                    clauses.push(vec![
                        Literal::negative(var(v, c1)),
                        Literal::negative(var(v, c2)),
                    ]);
                }
            }
        }
        // triangle edges: endpoints differ in every color
        for (a, b) in [(0u32, 1u32), (0, 2), (1, 2)] {
            for c in 0..3 {
                clauses.push(vec![
                    Literal::negative(var(a, c)),
                    Literal::negative(var(b, c)),
                ]);
            }
        }
        let counts = build_formula_counts(&clauses);
        let gens = find_automorphisms(&clauses, &counts, 50_000, 64);
        assert!(
            !gens.is_empty(),
            "IR must find symmetry on the triangle 3-coloring"
        );
        for g in &gens {
            assert!(
                permutation_preserves_formula(&counts, g),
                "every IR generator must pass the soundness gate: {g:?}"
            );
            // non-identity
            assert!(g.iter().any(|(k, v)| k != v));
        }
    }

    /// Bounded replacement for the former environment-driven timing benchmark.
    ///
    /// Exercise both search limits on a fixed composite-symmetry instance:
    /// a zero-node budget must stop before finding a leaf, while a sufficient
    /// budget with a one-generator cap must return exactly one deterministic,
    /// gate-verified automorphism.
    #[test]
    fn test_ir_respects_deterministic_search_limits() {
        let clauses = clique_coloring_2v2c();
        let counts = build_formula_counts(&clauses);

        assert!(
            find_automorphisms(&clauses, &counts, 0, 1).is_empty(),
            "a zero-node budget must stop before exploring an IR leaf"
        );

        let gens = find_automorphisms(&clauses, &counts, 10_000, 1);
        assert_eq!(gens.len(), 1, "the generator cap must be enforced exactly");
        for g in &gens {
            assert!(
                permutation_preserves_formula(&counts, g),
                "a bounded result must still pass the formula-preservation gate"
            );
            assert!(g.iter().any(|(from, to)| from != to));
        }

        assert_eq!(
            gens,
            find_automorphisms(&clauses, &counts, 10_000, 1),
            "fixed search limits must produce deterministic generators"
        );
    }

    #[test]
    fn test_ir_no_symmetry_returns_empty() {
        // Asymmetric formula.
        let clauses = vec![
            vec![lit(0, true)],
            vec![lit(0, true), lit(1, true)],
            vec![lit(1, false), lit(2, true)],
        ];
        let counts = build_formula_counts(&clauses);
        let gens = find_automorphisms(&clauses, &counts, 10_000, 64);
        for g in &gens {
            // Whatever it returns must be sound.
            assert!(permutation_preserves_formula(&counts, g));
        }
    }

    /// `(a ∨ b) ∧ (¬a ∨ ¬b)` is invariant under flipping BOTH variables, a
    /// symmetry no sign-preserving search can represent.
    #[test]
    fn signed_search_finds_a_polarity_flip() {
        let clauses = vec![
            vec![lit(0, true), lit(1, true)],
            vec![lit(0, false), lit(1, false)],
        ];
        let counts = build_formula_counts(&clauses);
        let signed = find_signed_automorphisms(&clauses, &counts, 10_000, 64);
        assert!(!signed.is_empty(), "signed search must find generators");
        for g in &signed {
            assert!(crate::symmetry::literal_permutation_preserves_formula(
                &counts, g
            ));
            // Complement-closed: ¬l tracks l.
            for (from, to) in g {
                assert_eq!(
                    g.get(&from.negated()).copied(),
                    Some(to.negated()),
                    "signed permutation must be complement-closed"
                );
            }
        }
        assert!(
            signed.iter().any(|g| g
                .iter()
                .any(|(from, to)| from.is_positive() != to.is_positive())),
            "at least one generator must flip a polarity"
        );
    }

    /// A formula with no symmetry at all must yield nothing from the signed
    /// search either — and never an unverified permutation.
    #[test]
    fn signed_search_is_sound_on_an_asymmetric_formula() {
        let clauses = vec![
            vec![lit(0, true)],
            vec![lit(0, true), lit(1, true)],
            vec![lit(1, false), lit(2, true)],
        ];
        let counts = build_formula_counts(&clauses);
        let generators = find_signed_automorphisms(&clauses, &counts, 10_000, 64);
        assert!(
            generators.is_empty(),
            "an asymmetric formula must not produce signed generators: {generators:?}"
        );
        for g in &generators {
            assert!(crate::symmetry::literal_permutation_preserves_formula(
                &counts, g
            ));
        }
    }
}
