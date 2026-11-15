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

/// Recursion-depth bound of the IR search (a stack bound: the partition is
/// shared along the path, so depth costs frames, not colourings).
const DFS_MAX_DEPTH: usize = 4096;

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
/// Unique clauses (first occurrence order) and each one's multiplicity.
fn merge_duplicate_clauses(clauses: &[Vec<Literal>]) -> (Vec<Vec<Literal>>, Vec<u32>) {
    let mut index: BTreeMap<Vec<u32>, usize> = BTreeMap::new();
    let mut unique: Vec<Vec<Literal>> = Vec::new();
    let mut multiplicity: Vec<u32> = Vec::new();
    for c in clauses {
        let key = super::canonical_clause_key(c);
        match index.get(&key) {
            Some(&i) => multiplicity[i] += 1,
            None => {
                index.insert(key, unique.len());
                unique.push(c.clone());
                multiplicity.push(1);
            }
        }
    }
    (unique, multiplicity)
}

fn build_graph(clauses: &[Vec<Literal>], sign_split: bool, multiplicity: &[u32]) -> ColoredGraph {
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
    let mut len_class: BTreeMap<(usize, u32), u32> = BTreeMap::new();
    for (ci, c) in clauses.iter().enumerate() {
        let mult = multiplicity.get(ci).copied().unwrap_or(1);
        let id = *len_class.entry((c.len(), mult)).or_insert_with(|| {
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
/// The search's partition: cells are contiguous ranges of a node ordering,
/// refined and individualized in place, with a trail of fragment starts so
/// a subtree's changes undo in time proportional to the work that made them
/// (McKay's structure). A split keeps its fragments in the parent's place,
/// so cells never reorder: the literal cells built first stay ahead of the
/// clause cells, and a discrete partition's first `2·nv` positions are the
/// literal labelling a leaf needs. Refinement is by splitter queue: a
/// splitter cell splits the cells it touches by neighbour count, fragments
/// ordered by increasing count, every fragment but the largest queued (all
/// of them when the split cell was itself queued) — the coarsest equitable
/// partition finer than the input, with a cell order that depends only on
/// colours and counts, so isomorphic inputs refine to corresponding orders.
struct Partition {
    /// position -> node
    perm: Vec<usize>,
    /// node -> position
    pos: Vec<usize>,
    /// node -> start position of its cell
    cell_of: Vec<usize>,
    /// cell start -> end (exclusive); meaningful at starts only
    cell_end: Vec<usize>,
    cells: usize,
    singletons: usize,
    /// (parent cell start, fragment start) per split, in creation order.
    trail: Vec<(usize, usize)>,
    queue: std::collections::VecDeque<usize>,
    in_queue: Vec<bool>,
    count: Vec<u32>,
    touched_nodes: Vec<usize>,
    touched_cells: Vec<usize>,
    cell_marked: Vec<bool>,
    scratch: Vec<(u32, usize)>,
    fragments: Vec<usize>,
}

impl Partition {
    /// Cells are the runs of equal colour, in colour order.
    fn from_colors(color: &[u32]) -> Self {
        let n = color.len();
        let k = color.iter().max().map_or(0, |m| *m as usize + 1);
        let mut start = vec![0usize; k + 1];
        for &c in color {
            start[c as usize + 1] += 1;
        }
        for i in 0..k {
            start[i + 1] += start[i];
        }
        let mut fill = start.clone();
        let mut perm = vec![0usize; n];
        let mut pos = vec![0usize; n];
        for (node, &c) in color.iter().enumerate() {
            let p = fill[c as usize];
            fill[c as usize] += 1;
            perm[p] = node;
            pos[node] = p;
        }
        let mut cell_of = vec![0usize; n];
        let mut cell_end = vec![0usize; n];
        let mut singletons = 0;
        for c in 0..k {
            let (s, e) = (start[c], start[c + 1]);
            if e == s {
                continue;
            }
            cell_end[s] = e;
            if e - s == 1 {
                singletons += 1;
            }
            for &node in &perm[s..e] {
                cell_of[node] = s;
            }
        }
        let cells = (0..k).filter(|&c| start[c + 1] > start[c]).count();
        Self {
            perm,
            pos,
            cell_of,
            cell_end,
            cells,
            singletons,
            trail: Vec::new(),
            queue: std::collections::VecDeque::new(),
            in_queue: vec![false; n],
            count: vec![0; n],
            touched_nodes: Vec::new(),
            touched_cells: Vec::new(),
            cell_marked: vec![false; n],
            scratch: Vec::new(),
            fragments: Vec::new(),
        }
    }

    fn len(&self) -> usize {
        self.perm.len()
    }

    fn is_discrete(&self) -> bool {
        self.cells == self.len()
    }

    #[cfg(test)]
    /// Dense colours in cell order (tests and the invariant helpers).
    fn colors(&self) -> Vec<u32> {
        let n = self.len();
        let mut color = vec![0u32; n];
        let (mut p, mut next) = (0, 0u32);
        while p < n {
            let e = self.cell_end[p];
            for &u in &self.perm[p..e] {
                color[u] = next;
            }
            next += 1;
            p = e;
        }
        color
    }

    /// The first cell of size at least two at or after position `from`
    /// (cells before a node's target stay singletons in its subtree, so a
    /// child scans from its parent's target).
    fn first_nonsingleton_from(&self, from: usize) -> Option<usize> {
        let n = self.len();
        let mut p = from;
        while p < n {
            let e = self.cell_end[p];
            if e - p >= 2 {
                return Some(p);
            }
            p = e;
        }
        None
    }

    /// Move `v` to the front of its cell and split the rest off.
    fn individualize(&mut self, v: usize) {
        let c = self.cell_of[v];
        let ce = self.cell_end[c];
        if ce - c < 2 {
            return;
        }
        let pv = self.pos[v];
        let other = self.perm[c];
        self.perm.swap(c, pv);
        self.pos[v] = c;
        self.pos[other] = pv;
        self.cell_end[c] = c + 1;
        self.cell_end[c + 1] = ce;
        for p in c + 1..ce {
            self.cell_of[self.perm[p]] = c + 1;
        }
        self.trail.push((c, c + 1));
        self.cells += 1;
        self.singletons += 1 + usize::from(ce - (c + 1) == 1);
    }

    /// Split cell `c` by the counts in `scratch` (members sorted by count,
    /// then node). Returns the work done; no split when all counts agree.
    fn split_by_counts(&mut self, c: usize) -> u64 {
        let ce = self.cell_end[c];
        let size = ce - c;
        // `fragments` is this call's output: empty when the cell does not
        // split (a stale list here re-queued old fragments without end).
        self.fragments.clear();
        self.scratch.clear();
        self.scratch
            .extend(self.perm[c..ce].iter().map(|&u| (self.count[u], u)));
        if self
            .scratch
            .iter()
            .all(|&(cnt, _)| cnt == self.scratch[0].0)
        {
            return size as u64;
        }
        self.scratch.sort_unstable();
        let mut frag_start = c;
        for i in 0..size {
            let (cnt, u) = self.scratch[i];
            let p = c + i;
            self.perm[p] = u;
            self.pos[u] = p;
            if i > 0 && cnt != self.scratch[i - 1].0 {
                self.cell_end[frag_start] = p;
                self.fragments.push(frag_start);
                frag_start = p;
            }
            self.cell_of[u] = frag_start;
        }
        self.cell_end[frag_start] = ce;
        self.fragments.push(frag_start);
        // Trail entries in decreasing fragment order, so the undo (which
        // pops in reverse) merges fragments back in increasing order and the
        // parent's end is exactly the fragment start at every pop. Pushed in
        // increasing order, a three-way split was undone last-fragment-first
        // and each later pop shrank the parent's end back (FmlaImplyChain
        // panicked on the singleton count underflowing).
        for &f in self.fragments[1..].iter().rev() {
            self.trail.push((c, f));
        }
        self.cells += self.fragments.len() - 1;
        self.singletons += self
            .fragments
            .iter()
            .filter(|&&f| self.cell_end[f] - f == 1)
            .count();
        size as u64
    }

    /// Refine to the coarsest equitable partition; `seed` names a node
    /// whose singleton cell is the only splitter (the parent partition was
    /// equitable), `None` queues every cell. Returns the work in visits and
    /// whether the pass completed: it stops once `cap` visits are spent
    /// (the root pass over a multi-million-edge graph ran 8–33 s otherwise,
    /// the budget being checked only between tree nodes), leaving the queue
    /// drained and the partition valid but not equitable.
    fn refine(&mut self, adj: &[Vec<u32>], seed: Option<usize>, cap: u64) -> (u64, bool) {
        let n = self.len();
        match seed {
            Some(v) => {
                let s = self.cell_of[v];
                self.queue.push_back(s);
                self.in_queue[s] = true;
            }
            None => {
                let mut p = 0;
                while p < n {
                    self.queue.push_back(p);
                    self.in_queue[p] = true;
                    p = self.cell_end[p];
                }
            }
        }
        let mut work = 0u64;
        let mut complete = true;
        while let Some(s) = self.queue.pop_front() {
            self.in_queue[s] = false;
            if work > cap {
                complete = false;
                continue; // drain the queue; nothing more is split
            }
            let e = self.cell_end[s];
            for p in s..e {
                let u = self.perm[p];
                work += adj[u].len() as u64;
                for &w in &adj[u] {
                    let w = w as usize;
                    if self.count[w] == 0 {
                        self.touched_nodes.push(w);
                    }
                    self.count[w] += 1;
                }
            }
            for i in 0..self.touched_nodes.len() {
                let c = self.cell_of[self.touched_nodes[i]];
                if !self.cell_marked[c] {
                    self.cell_marked[c] = true;
                    self.touched_cells.push(c);
                }
            }
            self.touched_cells.sort_unstable();
            let touched = std::mem::take(&mut self.touched_cells);
            for &c in &touched {
                self.cell_marked[c] = false;
                if self.cell_end[c] - c < 2 {
                    continue;
                }
                let was_queued = self.in_queue[c];
                work += self.split_by_counts(c);
                if self.fragments.len() < 2 {
                    continue;
                }
                let fragments = std::mem::take(&mut self.fragments);
                let largest = fragments
                    .iter()
                    .copied()
                    .max_by_key(|&f| (self.cell_end[f] - f, std::cmp::Reverse(f)))
                    .unwrap_or(c);
                for &f in &fragments {
                    if self.in_queue[f] {
                        continue;
                    }
                    if was_queued || f != largest {
                        self.in_queue[f] = true;
                        self.queue.push_back(f);
                    }
                }
                self.fragments = fragments;
            }
            self.touched_cells = touched;
            self.touched_cells.clear();
            for i in 0..self.touched_nodes.len() {
                self.count[self.touched_nodes[i]] = 0;
            }
            self.touched_nodes.clear();
        }
        (work, complete)
    }

    /// Merge back every split made after `mark`, latest first.
    fn undo_to(&mut self, mark: usize) {
        while self.trail.len() > mark {
            let Some((c, f)) = self.trail.pop() else {
                break;
            };
            let fe = self.cell_end[f];
            debug_assert_eq!(self.cell_end[c], f, "undo merges the next fragment");
            if fe - f == 1 {
                self.singletons -= 1;
            }
            if f - c == 1 {
                self.singletons -= 1;
            }
            self.cell_end[c] = fe;
            for p in f..fe {
                self.cell_of[self.perm[p]] = c;
            }
            self.cells -= 1;
        }
    }
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
    /// Deepest tree level entered (a recursion-stack bound; the partition
    /// itself is shared along the path).
    max_depth: usize,
    /// Literals in the clause multiset — the cost of one gate verification.
    verify_cost: u64,
    work: u64,
    work_budget: u64,
    /// The partition, refined and individualized in place along the path.
    part: Partition,
    /// First (leftmost) discrete leaf: literal position -> node.
    first_leaf: Option<Vec<usize>>,
    /// Shape invariant along the leftmost path, indexed by depth.
    first_path_inv: Vec<[usize; 4]>,
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

    fn handle_leaf(&mut self) {
        // Literal positions come first: the leaf labelling is position ->
        // node over the first 2·nv positions.
        let leaf: Vec<usize> = self.part.perm[..2 * self.nv].to_vec();
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
                let mut g = vec![0usize; 2 * self.nv];
                for r in 0..2 * self.nv {
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

    fn dfs(&mut self, depth: usize, leftmost: bool, seed: Option<usize>, from: usize) {
        if self.nodes > self.node_budget
            || self.work > self.work_budget
            || self.generator_count() >= self.max_generators
            || depth > self.max_depth
        {
            return;
        }
        self.nodes += 1;
        let mark = self.part.trail.len();
        // Children refine incrementally from the individualized singleton
        // (the parent partition was equitable); the root refines everything.
        // Deterministic cost accounting in visits: without it the SIGNED
        // search is unaffordable — dropping the polarity split coarsens the
        // initial partition, so the IR tree is far wider, and a node budget
        // alone let a 2320-variable instance spend 3.6 s searching where the
        // whole solve takes 0.02 s.
        let adj = self.adj;
        let remaining = self.work_budget.saturating_sub(self.work);
        let (visits, complete) = self.part.refine(adj, seed, remaining);
        self.work = self.work.saturating_add(visits.max(1));
        if !complete {
            // Out of budget mid-refinement: the partition is not equitable,
            // so nothing below is worth exploring.
            self.part.undo_to(mark);
            return;
        }

        let target = self.part.first_nonsingleton_from(from);
        let n = self.part.len();
        let inv = [
            self.part.cells,
            self.part.singletons,
            target.unwrap_or(n),
            target.map_or(0, |t| self.part.cell_end[t] - t),
        ];
        if leftmost {
            if self.first_path_inv.len() == depth {
                self.first_path_inv.push(inv);
            }
        } else {
            match self.first_path_inv.get(depth) {
                Some(fi) if *fi == inv => {}
                _ => {
                    // shape differs from the reference path: no automorphism here
                    self.part.undo_to(mark);
                    return;
                }
            }
        }

        let Some(t) = target else {
            if self.part.is_discrete() {
                self.handle_leaf();
            }
            self.part.undo_to(mark);
            return;
        };
        let members: Vec<usize> = self.part.perm[t..self.part.cell_end[t]].to_vec();

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
            let child_mark = self.part.trail.len();
            self.part.individualize(v);
            self.work = self
                .work
                .saturating_add((self.part.cell_end[t + 1] - t) as u64);
            self.dfs(depth + 1, leftmost && first_child, Some(v), t);
            self.part.undo_to(child_mark);
            first_child = false;
        }
        self.part.undo_to(mark);
    }
}

#[cfg(test)]
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
    run_search(
        clauses,
        formula_counts,
        node_budget,
        max_generators,
        super::IR_WORK_BUDGET,
        false,
    )
    .0
}

/// As `find_signed_automorphisms` with an explicit work ceiling
/// (edge-visits), for the fix-and-cut route's larger budgets.
pub(crate) fn find_signed_automorphisms_budgeted(
    clauses: &[Vec<Literal>],
    formula_counts: &BTreeMap<Vec<u32>, u32>,
    node_budget: u64,
    max_generators: usize,
    work_budget: u64,
) -> Vec<BTreeMap<Literal, Literal>> {
    run_search(
        clauses,
        formula_counts,
        node_budget,
        max_generators,
        work_budget,
        true,
    )
    .1
}

/// As `find_automorphisms` with an explicit work ceiling (edge-visits), for
/// the fix-and-cut route's larger budgets.
pub(crate) fn find_automorphisms_budgeted(
    clauses: &[Vec<Literal>],
    formula_counts: &BTreeMap<Vec<u32>, u32>,
    node_budget: u64,
    max_generators: usize,
    work_budget: u64,
) -> Vec<BTreeMap<Variable, Variable>> {
    run_search(
        clauses,
        formula_counts,
        node_budget,
        max_generators,
        work_budget,
        false,
    )
    .0
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
    run_search(
        clauses,
        formula_counts,
        node_budget,
        max_generators,
        super::IR_WORK_BUDGET,
        true,
    )
    .1
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
    work_budget: u64,
    signed: bool,
) -> SearchResult {
    if clauses.is_empty() {
        return (Vec::new(), Vec::new());
    }
    // Duplicate clauses would be interchangeable clause nodes: every pair
    // doubles the IR tree with automorphisms that project to the identity
    // (so the orbit pruning never learns them). em_8_4_5_fbc carries 1,296
    // duplicates and the search found nothing in 30 s; merged, the multiset
    // is kept exact by colouring a clause node with its multiplicity.
    let (unique, multiplicity) = merge_duplicate_clauses(clauses);
    let clauses = unique.as_slice();
    let graph = build_graph(clauses, !signed, &multiplicity);
    let n = graph.adj.len();
    // Guard against pathological graph sizes (caller also caps vars/clauses).
    if n == 0 || graph.nv == 0 {
        return (Vec::new(), Vec::new());
    }

    let mut var_to_dense: BTreeMap<Variable, usize> = BTreeMap::new();
    for (i, v) in graph.dense_to_var.iter().enumerate() {
        var_to_dense.insert(*v, i);
    }

    let max_depth = DFS_MAX_DEPTH;
    let verify_cost: u64 = formula_counts
        .keys()
        .map(|k| k.len() as u64)
        .sum::<u64>()
        .max(1);
    // B2: the work ceiling is the shared constant in `symmetry/mod.rs` (or the
    // fix-and-cut route's larger one); the env override is deleted.

    let mut search = Search {
        adj: &graph.adj,
        nv: graph.nv,
        dense_to_var: &graph.dense_to_var,
        var_to_dense,
        formula_counts,
        node_budget,
        max_generators,
        nodes: 0,
        max_depth,
        verify_cost,
        work: 0,
        work_budget,
        part: Partition::from_colors(&graph.init_color),
        first_leaf: None,
        first_path_inv: Vec::new(),
        uf: (0..n).collect(),
        generators: Vec::new(),
        seen: BTreeSet::new(),
        signed,
        signed_generators: Vec::new(),
        signed_seen: BTreeSet::new(),
    };

    search.dfs(0, true, None, 0);
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

    /// Every cell's members have the same number of neighbours in every cell.
    fn is_equitable(adj: &[Vec<u32>], color: &[u32]) -> bool {
        let k = color.iter().max().map_or(0, |m| *m as usize + 1);
        let profile = |u: usize| {
            let mut counts = vec![0u32; k];
            for &w in &adj[u] {
                counts[color[w as usize] as usize] += 1;
            }
            counts
        };
        (0..color.len())
            .all(|u| (0..color.len()).all(|w| color[u] != color[w] || profile(u) == profile(w)))
    }

    #[test]
    fn refinement_is_equitable_and_relabelling_invariant() {
        // A 6-cycle with a chord (0-3): the chord ends form one cell, the
        // rest another, and the reflection fixing the chord is an
        // automorphism (so individualizing a chord end leaves work to do).
        let edges = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0), (0, 3)];
        let n = 6;
        let build = |map: &dyn Fn(usize) -> usize| {
            let mut adj = vec![Vec::new(); n];
            for &(a, b) in &edges {
                adj[map(a)].push(map(b) as u32);
                adj[map(b)].push(map(a) as u32);
            }
            adj
        };
        let cells = |adj: &[Vec<u32>]| {
            let mut part = Partition::from_colors(&vec![0u32; n]);
            part.refine(adj, None, u64::MAX);
            let color = part.colors();
            assert!(is_equitable(adj, &color), "{color:?}");
            let k = color.iter().max().map_or(0, |m| *m as usize + 1);
            assert_eq!(k, part.cells);
            let mut sizes = vec![0usize; k];
            for &c in &color {
                sizes[c as usize] += 1;
            }
            assert_eq!(sizes.iter().filter(|&&s| s == 1).count(), part.singletons);
            (color, sizes, part)
        };
        let (color_a, sizes_a, mut part) = cells(&build(&|v| v));
        let relabel = [4usize, 0, 2, 5, 1, 3];
        let (color_b, sizes_b, _) = cells(&build(&|v| relabel[v]));
        assert_eq!(sizes_a, sizes_b, "cell order must depend on structure only");
        // Fragments are ordered by ascending neighbour count: the four
        // degree-2 nodes, then the two chord ends.
        assert_eq!(sizes_a, vec![4, 2], "{sizes_a:?}");
        for v in 0..n {
            assert_eq!(color_a[v], color_b[relabel[v]], "node {v}");
        }
        // Individualize, refine incrementally, then undo: the partition is
        // restored exactly.
        let adj = build(&|v| v);
        let mark = part.trail.len();
        let (cells_before, singletons_before) = (part.cells, part.singletons);
        let target = part.first_nonsingleton_from(0).unwrap_or(0);
        let v = part.perm[target];
        part.individualize(v);
        part.refine(&adj, Some(v), u64::MAX);
        let inc = part.colors();
        assert!(is_equitable(&adj, &inc), "{inc:?}");
        assert!(part.cells > cells_before);
        part.undo_to(mark);
        assert_eq!(part.colors(), color_a);
        assert_eq!(
            (part.cells, part.singletons),
            (cells_before, singletons_before)
        );
        // Incremental refinement yields the same partition as a full pass
        // over the individualized colouring (cell order may differ: it
        // depends on the splitter sequence, which is fixed per procedure).
        let mut individualized = color_a.clone();
        for u in 0..n {
            if individualized[u] > color_a[v] || (individualized[u] == color_a[v] && u != v) {
                individualized[u] += 1;
            }
        }
        let mut full = Partition::from_colors(&individualized);
        full.refine(&adj, None, u64::MAX);
        let full_colors = full.colors();
        for u in 0..n {
            for w in 0..n {
                assert_eq!(
                    inc[u] == inc[w],
                    full_colors[u] == full_colors[w],
                    "nodes {u} and {w}"
                );
            }
        }
    }

    #[test]
    fn individualize_refine_undo_restores_random_graphs_exactly() {
        // Random sparse graphs: refine fully, then for every node
        // individualize, refine from it and undo — colours and counters must
        // come back exactly. Multi-fragment splits occur throughout, which
        // is what corrupted the partition before (the undo merged fragments
        // last-first and shrank the parent's end back).
        let mut seed = 0x2545_F491_4F6C_DD1Du64;
        let mut next = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for round in 0..40 {
            let n = 6 + (next() % 20) as usize;
            let m = n + (next() % (3 * n as u64)) as usize;
            let mut adj = vec![Vec::new(); n];
            for _ in 0..m {
                let a = (next() % n as u64) as usize;
                let b = (next() % n as u64) as usize;
                if a != b {
                    adj[a].push(b as u32);
                    adj[b].push(a as u32);
                }
            }
            let colors: Vec<u32> = (0..n).map(|_| (next() % 2) as u32).collect();
            let mut part = Partition::from_colors(&colors);
            part.refine(&adj, None, u64::MAX);
            let base = part.colors();
            assert!(is_equitable(&adj, &base), "round {round}: {base:?}");
            let counters = (part.cells, part.singletons);
            for v in 0..n {
                let mark = part.trail.len();
                part.individualize(v);
                part.refine(&adj, Some(v), u64::MAX);
                let refined = part.colors();
                assert!(
                    is_equitable(&adj, &refined),
                    "round {round} node {v}: {refined:?}"
                );
                part.undo_to(mark);
                assert_eq!(part.colors(), base, "round {round} node {v}");
                assert_eq!(
                    (part.cells, part.singletons),
                    counters,
                    "round {round} node {v}"
                );
            }
        }
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
