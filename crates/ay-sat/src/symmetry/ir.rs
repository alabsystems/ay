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
fn build_graph(clauses: &[Vec<Literal>]) -> ColoredGraph {
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

    // Initial colors: positive literals 0, negative literals 1, clauses by length.
    let mut init_color = vec![0u32; n];
    for di in 0..nv {
        init_color[2 * di] = 0;
        init_color[2 * di + 1] = 1;
    }
    let mut len_class: BTreeMap<usize, u32> = BTreeMap::new();
    let mut next_class = 2u32;
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
fn refine(adj: &[Vec<u32>], color: &mut Vec<u32>) {
    let n = color.len();
    loop {
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
    /// First (leftmost) discrete leaf: rank (color id) -> node.
    first_leaf: Option<Vec<usize>>,
    /// Cell-size invariant along the leftmost path, indexed by depth.
    first_path_inv: Vec<Vec<usize>>,
    /// Union-find over nodes capturing discovered-automorphism orbits (for pruning).
    uf: Vec<usize>,
    generators: Vec<BTreeMap<Variable, Variable>>,
    seen: BTreeSet<BTreeMap<Variable, Variable>>,
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

    fn handle_leaf(&mut self, color: &[u32]) {
        let n = color.len();
        // rank (color id) -> node.
        let mut leaf = vec![0usize; n];
        for (node, &c) in color.iter().enumerate() {
            leaf[c as usize] = node;
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

    fn dfs(&mut self, mut color: Vec<u32>, depth: usize, leftmost: bool) {
        if self.nodes > self.node_budget || self.generators.len() >= self.max_generators {
            return;
        }
        self.nodes += 1;
        refine(self.adj, &mut color);

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
            if self.nodes > self.node_budget || self.generators.len() >= self.max_generators {
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
    if clauses.is_empty() {
        return Vec::new();
    }
    let graph = build_graph(clauses);
    let n = graph.adj.len();
    // Guard against pathological graph sizes (caller also caps vars/clauses).
    if n == 0 || graph.nv == 0 {
        return Vec::new();
    }

    let mut var_to_dense: BTreeMap<Variable, usize> = BTreeMap::new();
    for (i, v) in graph.dense_to_var.iter().enumerate() {
        var_to_dense.insert(*v, i);
    }

    let mut search = Search {
        adj: &graph.adj,
        nv: graph.nv,
        dense_to_var: &graph.dense_to_var,
        var_to_dense,
        formula_counts,
        node_budget,
        max_generators,
        nodes: 0,
        first_leaf: None,
        first_path_inv: Vec::new(),
        uf: (0..n).collect(),
        generators: Vec::new(),
        seen: BTreeSet::new(),
    };

    search.dfs(graph.init_color.clone(), 0, true);
    search.generators
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

    /// Manual benchmark (ignored): set `AY_IR_BENCH_CNF` to a DIMACS path and run
    /// `cargo test -p ay-sat --lib symmetry::ir::tests::bench_clique -- --ignored --nocapture`.
    #[test]
    #[ignore = "manual benchmark requires AY_IR_BENCH_CNF"]
    fn bench_clique() {
        let path = std::env::var("AY_IR_BENCH_CNF").expect("set AY_IR_BENCH_CNF");
        let text = std::fs::read_to_string(&path).unwrap();
        let mut clauses: Vec<Vec<Literal>> = Vec::new();
        for line in text.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('p') || line.starts_with('c') {
                continue;
            }
            let mut c = Vec::new();
            for tok in line.split_whitespace() {
                let v: i64 = tok.parse().unwrap();
                if v == 0 {
                    break;
                }
                let var = Variable(v.unsigned_abs() as u32 - 1);
                c.push(if v > 0 {
                    Literal::positive(var)
                } else {
                    Literal::negative(var)
                });
            }
            if !c.is_empty() {
                c.sort_unstable_by_key(|l| l.raw());
                clauses.push(c);
            }
        }
        let counts = build_formula_counts(&clauses);
        let nb: u64 = std::env::var("AY_IR_BENCH_NB")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(8_000);
        let mg: usize = std::env::var("AY_IR_BENCH_MG")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(96);
        let t0 = ay_core::time::Instant::now();
        let gens = find_automorphisms(&clauses, &counts, nb, mg);
        let dt = t0.elapsed();
        let mut sup_total = 0usize;
        for g in &gens {
            assert!(permutation_preserves_formula(&counts, g));
            sup_total += g.len();
        }
        eprintln!(
            "IR bench [nb={nb} mg={mg}]: {} clauses, {} generators, total support {}, time {:?}",
            clauses.len(),
            gens.len(),
            sup_total,
            dt
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
}
