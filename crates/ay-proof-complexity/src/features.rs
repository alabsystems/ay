// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Structural (proof-complexity) features computed over a CNF formula.
//!
//! These features characterise how hard a CNF instance is *structurally*,
//! independent of solver runtime. They give downstream tools (benchmarks,
//! regressions, diffs, correlation studies) a fixed-width signal that
//! can be attached to every benchmark row.
//!
//! The current feature vector is intentionally cheap to compute on the
//! order of O(clauses * average_width): we walk the clause database once,
//! aggregate per-clause statistics, and derive a handful of densities.
//! Nothing here requires solving the formula.
//!
//! ## Features
//!
//! - `num_vars`, `num_clauses`: raw size.
//! - `clause_width_max`, `clause_width_mean`: width distribution.
//! - `xor_density`: fraction of clauses that look like they participate in
//!   an XOR constraint. We use a width-3 heuristic: exactly-3 literal
//!   clauses with the same variable set and opposite polarities occur in
//!   4-clause groups that encode a 3-XOR, so we approximate by counting
//!   length-3 clauses whose polarity pattern is one of the 4 odd-parity
//!   patterns. The density is `(matched / total_clauses)`. This correlates
//!   with Tseitin-style inputs without pulling in a full XOR extractor.
//!   See `cnf.rs::add_xor_equals_clauses` for the construction we are
//!   detecting.
//! - `cardinality_density`: fraction of clauses that are "at-most-one"
//!   shaped, i.e. width-2 clauses with both literals negative. These are
//!   characteristic of pigeonhole-style encodings (see `hard_formulas::pigeonhole`).
//! - `modularity`: a cheap proxy for community structure, computed as
//!   `1 - (edges_across_partitions / total_edges)` on the variable
//!   incidence graph with variables partitioned by `var_id % k` for
//!   `k = sqrt(num_vars).ceil().max(2)`. Higher = more community
//!   structure. This is *not* the Newman-Girvan modularity; it is a
//!   deterministic, O(clauses * width) approximation. See
//!   `research/BENCHMARKS_AND_TECHNIQUES.md` for the full notion.
//! - `vig_density`: density of the variable-interaction graph (VIG),
//!   defined as `2 * |E| / (V * (V-1))` where `V = num_vars` and `E` is
//!   the number of distinct unordered pairs `{u, v}` that co-occur in at
//!   least one clause. `0.0` when `num_vars < 2`.
//! - `treewidth_approx`: cheap upper bound on the VIG treewidth computed
//!   by the minimum-degree elimination heuristic (Bodlaender, "A Tourist
//!   Guide Through Treewidth", 1993; Bodlaender & Koster, "Treewidth
//!   Computations I. Upper Bounds", 2010). We iteratively eliminate a
//!   lowest-degree vertex, record its degree, and connect its neighbours
//!   (making them a clique in the fill-in graph). The maximum recorded
//!   elimination degree is an upper bound on `tw(G)`. `None` when the
//!   VIG is empty. For inputs with > 1024 variables we sample a
//!   deterministic subgraph to keep extraction linear-ish.
//! - `pigeonhole_score`: an O(clauses) pigeonhole-structure detector in
//!   `[0, 1]`. We scan for width-2 all-negative clauses (the canonical
//!   at-most-one shape), group them by their two variables' membership
//!   in a hypothetical "hole" via shared-variable counts, and report the
//!   fraction of variables that participate in at least one AMO pair
//!   scaled by the AMO-to-ALO balance. Formulas produced by
//!   `hard_formulas::pigeonhole(n)` land at `> 0.8`. Random k-CNF stays
//!   near zero.
//!
//! ## References
//!
//! - Ansotegui, Bonet, Levy (2012), "The Community Structure of SAT
//!   Formulas" — notion of formula community structure.
//! - Biere, Heule, van Maaren, Walsh (2021), "Handbook of Satisfiability",
//!   chapter on instance features.
//! - Bodlaender (1993), "A Tourist Guide Through Treewidth", *Acta
//!   Cybernetica* — min-degree elimination heuristic for treewidth
//!   upper bounds.
//! - Bodlaender & Koster (2010), "Treewidth Computations I. Upper
//!   Bounds", *Information and Computation* — survey of practical
//!   treewidth heuristics.
//! - Haken (1985), "The Intractability of Resolution" — pigeonhole
//!   encoding structure we detect.

use std::collections::HashSet;

use crate::cnf::Cnf;

/// A fixed-width vector of structural features derived from a CNF.
///
/// Every field is finite and non-negative. `f64` fields may be `NaN` only
/// when the formula has zero clauses (then `clause_width_mean` is 0.0 by
/// convention — we normalise away division-by-zero).
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct ProofComplexityFeatures {
    /// Number of propositional variables (as declared by the formula).
    pub num_vars: u32,
    /// Number of clauses.
    pub num_clauses: u32,
    /// Maximum clause width observed.
    pub clause_width_max: u32,
    /// Mean clause width (0.0 when `num_clauses == 0`).
    pub clause_width_mean: f64,
    /// Fraction of clauses that match an XOR-encoding signature (0..=1).
    pub xor_density: f64,
    /// Fraction of clauses that match an at-most-one / cardinality
    /// signature (width-2, both literals negative) (0..=1).
    pub cardinality_density: f64,
    /// Community-structure proxy (0..=1). Higher means more modular.
    pub modularity: f64,
    /// Variable-interaction graph (VIG) density `2*|E| / (V*(V-1))`.
    /// `0.0` when `num_vars < 2`.
    pub vig_density: f64,
    /// Treewidth upper bound from the min-degree elimination heuristic
    /// on the VIG. `None` when the VIG is empty. For large formulas
    /// (> 1024 vars) this is computed on a deterministic subsample.
    pub treewidth_approx: Option<f64>,
    /// Pigeonhole-structure score in `[0, 1]`. Width-2 all-negative
    /// clauses (at-most-one encodings) combined with width-n positive
    /// "at-least-one" clauses are the canonical signature; see
    /// `hard_formulas::pigeonhole`.
    pub pigeonhole_score: f64,
}

impl ProofComplexityFeatures {
    /// Compute features for a `Cnf` value in one pass.
    #[must_use]
    pub fn from_cnf(cnf: &Cnf) -> Self {
        let num_vars = cnf.num_vars() as u32;
        let num_clauses = cnf.num_clauses() as u32;

        let mut total_width: u64 = 0;
        let mut max_width: u32 = 0;
        let mut amo_like: u64 = 0;

        // Count width-3 clauses by positive-literal parity so we can pick
        // the dominant XOR sign at the end.
        let mut xor_even_parity: u64 = 0; // positives in {0, 2}
        let mut xor_odd_parity: u64 = 0; // positives in {1, 3}
        for clause in cnf.clauses() {
            let w = clause.len() as u32;
            total_width += u64::from(w);
            if w > max_width {
                max_width = w;
            }
            if w == 3 {
                let positives = clause.iter().filter(|l| l.is_positive()).count();
                if positives % 2 == 0 {
                    xor_even_parity += 1;
                } else {
                    xor_odd_parity += 1;
                }
            }
            if w == 2 && clause.iter().all(|l| !l.is_positive()) {
                amo_like += 1;
            }
        }
        // Whichever parity dominates is the "XOR signal". A parity-true 3-XOR
        // produces 4 odd-positive clauses; a parity-false 3-XOR produces 4
        // even-positive clauses. Random 3-CNF gives ~50/50 and the density
        // stays below 0.5.
        let xor_like: u64 = xor_even_parity.max(xor_odd_parity);

        let mean = if num_clauses == 0 {
            0.0
        } else {
            total_width as f64 / f64::from(num_clauses)
        };
        let xor_density = density(xor_like, num_clauses);
        let cardinality_density = density(amo_like, num_clauses);
        let modularity = compute_modularity_proxy(cnf);

        // Build the variable-interaction graph once; reuse it for VIG
        // density and the min-degree treewidth heuristic.
        let vig = VariableInteractionGraph::from_cnf(cnf);
        let vig_density = vig.density();
        let treewidth_approx = vig.min_degree_treewidth_upper_bound();
        let pigeonhole_score = compute_pigeonhole_score(cnf);

        Self {
            num_vars,
            num_clauses,
            clause_width_max: max_width,
            clause_width_mean: mean,
            xor_density,
            cardinality_density,
            modularity,
            vig_density,
            treewidth_approx,
            pigeonhole_score,
        }
    }
}

fn density(count: u64, total: u32) -> f64 {
    if total == 0 {
        0.0
    } else {
        count as f64 / f64::from(total)
    }
}

/// Deterministic, O(clauses * width) community-structure proxy.
///
/// Bucket every variable into `k = max(2, ceil(sqrt(num_vars)))` groups by
/// `var_id % k`. For each clause, count the number of distinct buckets
/// it touches: width-1 clauses touch 1 bucket; spread-out clauses touch
/// many. A high fraction of single-bucket (or low-bucket-count) clauses
/// indicates community structure. Return
/// `1 - (spread_weight / total_weight)` so larger = more modular.
fn compute_modularity_proxy(cnf: &Cnf) -> f64 {
    let n_vars = cnf.num_vars().max(1);
    let k = (n_vars as f64).sqrt().ceil() as u32;
    let k = k.max(2);

    let mut total_weight: u64 = 0;
    let mut spread_weight: u64 = 0;

    // Reuse a small scratch buffer for "distinct buckets in this clause".
    // Clauses are typically short, so a linear search in a Vec is cheap.
    let mut buckets: Vec<u32> = Vec::with_capacity(16);

    for clause in cnf.clauses() {
        if clause.is_empty() {
            continue;
        }
        buckets.clear();
        for lit in clause {
            let b = lit.variable().index() as u32 % k;
            if !buckets.contains(&b) {
                buckets.push(b);
            }
        }
        // Normalise by clause width so that a 10-literal clause touching
        // 10 buckets doesn't swamp a dozen unit clauses.
        let w = clause.len() as u64;
        total_weight += w;
        // Each distinct bucket beyond the first contributes "spread".
        let distinct = buckets.len() as u64;
        if distinct > 1 {
            spread_weight += distinct - 1;
        }
    }

    if total_weight == 0 {
        0.0
    } else {
        let ratio = spread_weight as f64 / total_weight as f64;
        (1.0 - ratio).clamp(0.0, 1.0)
    }
}

/// Maximum number of variables to include in the full VIG / treewidth
/// computation. Larger formulas are deterministically subsampled to
/// `VIG_SAMPLE_LIMIT` variables (chosen by `var_id % stride`). This keeps
/// feature extraction bounded to a few hundred microseconds even for
/// industrial-scale instances.
const VIG_SAMPLE_LIMIT: usize = 1024;

/// Variable-interaction graph built from a CNF.
///
/// Vertices are variables. An edge `{u, v}` exists when some clause
/// contains both `u` (positive or negative) and `v` (positive or
/// negative). Self-loops are excluded; edges are undirected and stored
/// only once per pair.
///
/// Representation: adjacency-lists over the subsampled variable set.
/// The subsampling stride is `max(1, ceil(num_vars / VIG_SAMPLE_LIMIT))`
/// so for `num_vars <= VIG_SAMPLE_LIMIT` every variable is kept.
struct VariableInteractionGraph {
    /// Local index -> variable id (only used for diagnostics; kept for
    /// completeness of the deterministic sampling rule).
    _local_to_var: Vec<u32>,
    /// Adjacency lists (local indices). Sorted and deduplicated so
    /// degree lookups are `O(len)` without repeated work.
    adj: Vec<Vec<u32>>,
    /// Number of variables originally declared by the CNF (unsampled).
    num_vars_full: usize,
}

impl VariableInteractionGraph {
    fn from_cnf(cnf: &Cnf) -> Self {
        let num_vars_full = cnf.num_vars();
        let stride = num_vars_full
            .max(1)
            .div_ceil(VIG_SAMPLE_LIMIT.max(1))
            .max(1);

        // Deterministic sampling: keep variables whose id is a multiple
        // of `stride`. This preserves structural patterns such as the
        // `var_id % holes` layout used by `pigeonhole(n)`.
        // Do not allocate a header-sized reverse map here. DIMACS permits
        // over-declared variable counts, so a tiny formula can legitimately
        // carry a multi-billion-variable header. The arithmetic sampling rule
        // gives the local index directly for every retained variable.
        let local_to_var: Vec<u32> = (0..num_vars_full)
            .step_by(stride)
            .map(|v| v as u32)
            .collect();

        let n_local = local_to_var.len();
        let mut adj: Vec<Vec<u32>> = vec![Vec::new(); n_local];

        // For each clause, enumerate every pair of kept variables.
        // Clauses are short on average; for very wide clauses the
        // quadratic pair enumeration is still bounded by width^2 and
        // we deduplicate adjacency entries below.
        let mut sampled: Vec<u32> = Vec::with_capacity(16);
        for clause in cnf.clauses() {
            sampled.clear();
            for lit in clause {
                let v = lit.variable().index();
                if v >= num_vars_full {
                    continue;
                }
                if v % stride == 0 {
                    let lv = (v / stride) as u32;
                    if !sampled.contains(&lv) {
                        sampled.push(lv);
                    }
                }
            }
            if sampled.len() < 2 {
                continue;
            }
            for i in 0..sampled.len() {
                for j in (i + 1)..sampled.len() {
                    let a = sampled[i];
                    let b = sampled[j];
                    adj[a as usize].push(b);
                    adj[b as usize].push(a);
                }
            }
        }

        // Sort + dedup adjacency so degree() is the true neighbour count.
        for list in &mut adj {
            list.sort_unstable();
            list.dedup();
        }

        Self {
            _local_to_var: local_to_var,
            adj,
            num_vars_full,
        }
    }

    fn num_vertices(&self) -> usize {
        self.adj.len()
    }

    fn num_edges(&self) -> usize {
        self.adj.iter().map(Vec::len).sum::<usize>() / 2
    }

    /// VIG density `2*E / (V*(V-1))` on the ORIGINAL (unsampled) variable
    /// count. We scale the sampled edge count by `stride^2` to estimate
    /// the full-graph density; when `stride == 1` (no sampling) this is
    /// exact.
    fn density(&self) -> f64 {
        let v_full = self.num_vars_full;
        if v_full < 2 {
            return 0.0;
        }
        let v_local = self.num_vertices().max(1);
        let stride = v_full.div_ceil(v_local);
        let stride = stride.max(1);
        let e_local = self.num_edges() as f64;
        let e_estimated = e_local * (stride * stride) as f64;
        let max_edges = (v_full as f64) * ((v_full as f64) - 1.0) / 2.0;
        if max_edges <= 0.0 {
            0.0
        } else {
            (e_estimated / max_edges).clamp(0.0, 1.0)
        }
    }

    /// Minimum-degree elimination heuristic: upper bound on `tw(G)`.
    ///
    /// Repeatedly pick a vertex of minimum degree, record its current
    /// degree, remove it from the graph, and add fill-in edges to make
    /// its former neighbours a clique. The largest recorded degree is
    /// an upper bound on treewidth (Bodlaender 1993).
    ///
    /// Runs in O(V * (V + E)) worst-case; on SAT-like VIGs (low average
    /// degree) it's effectively linear. Returns `None` if the graph
    /// has zero vertices.
    fn min_degree_treewidth_upper_bound(&self) -> Option<f64> {
        let n = self.num_vertices();
        if n == 0 {
            return None;
        }

        // Working adjacency using sorted Vecs. For each elimination step
        // we find the min-degree vertex, record its degree, and clique
        // its neighbours.
        let mut adj: Vec<Vec<u32>> = self.adj.clone();
        let mut alive: Vec<bool> = vec![true; n];
        let mut remaining = n;
        let mut max_elim_degree: u32 = 0;

        while remaining > 0 {
            // Find min-degree alive vertex.
            let mut best: Option<usize> = None;
            let mut best_deg: usize = usize::MAX;
            for (v, list) in adj.iter().enumerate() {
                if !alive[v] {
                    continue;
                }
                let deg = list.len();
                if deg < best_deg {
                    best_deg = deg;
                    best = Some(v);
                    if deg == 0 {
                        break;
                    }
                }
            }
            let v = match best {
                Some(v) => v,
                None => break,
            };

            max_elim_degree = max_elim_degree.max(best_deg as u32);

            // Snapshot neighbours (they will become a clique).
            let nbrs: Vec<u32> = adj[v].clone();

            // Remove v from the graph.
            alive[v] = false;
            remaining -= 1;
            for &u in &nbrs {
                let list = &mut adj[u as usize];
                if let Ok(pos) = list.binary_search(&(v as u32)) {
                    list.remove(pos);
                }
            }
            adj[v].clear();

            // Add fill-in edges so surviving neighbours form a clique.
            for i in 0..nbrs.len() {
                for j in (i + 1)..nbrs.len() {
                    let a = nbrs[i] as usize;
                    let b = nbrs[j] as usize;
                    if !alive[a] || !alive[b] {
                        continue;
                    }
                    let a_list = &mut adj[a];
                    if a_list.binary_search(&(b as u32)).is_err() {
                        let pos = a_list.partition_point(|&x| x < b as u32);
                        a_list.insert(pos, b as u32);
                    }
                    let b_list = &mut adj[b];
                    if b_list.binary_search(&(a as u32)).is_err() {
                        let pos = b_list.partition_point(|&x| x < a as u32);
                        b_list.insert(pos, a as u32);
                    }
                }
            }
        }

        Some(f64::from(max_elim_degree))
    }
}

/// Pigeonhole-structure score.
///
/// Detects PHP-like encodings by looking for the canonical two-level
/// structure: at-least-one (ALO) clauses and at-most-one (AMO)
/// pairwise-negative clauses. In `pigeonhole(n)` every pigeon has an
/// ALO clause of width `n` over its hole variables, and every pair of
/// pigeons sharing a hole contributes an AMO clause of width 2 with
/// both literals negative over that hole.
///
/// The heuristic, in `[0, 1]`:
///
/// 1. `amo_pair_count`: number of width-2 all-negative clauses.
/// 2. `alo_wide_count`: number of all-positive clauses of width `>= 2`
///    (the ALO signature).
/// 3. `participating_vars`: variables appearing in at least one AMO
///    pair.
/// 4. Score = `(participating_vars / num_vars) *
///    min(1, amo_pair_count / max(1, alo_wide_count))`.
///
/// This lands above 0.8 for `pigeonhole(n)` with `n >= 2`, at 0.0 for
/// pure XOR/parity formulas, and near 0.0 for random 3-CNF. It is a
/// fingerprint, not a decision procedure — callers should treat it as
/// a proxy for "this looks PHP-ish".
fn compute_pigeonhole_score(cnf: &Cnf) -> f64 {
    let n_vars = cnf.num_vars();
    if n_vars == 0 || cnf.num_clauses() == 0 {
        return 0.0;
    }

    let mut amo_pair_count: u64 = 0;
    let mut alo_wide_count: u64 = 0;
    // Keep this proportional to the input, not the declared variable range.
    // Over-declared DIMACS headers are common enough that a dense bitmap here
    // can otherwise turn a tiny benchmark into a multi-gigabyte allocation.
    let mut participating: HashSet<usize> = HashSet::new();

    for clause in cnf.clauses() {
        let w = clause.len();
        if w == 2 && clause.iter().all(|l| !l.is_positive()) {
            amo_pair_count += 1;
            for lit in clause {
                let v = lit.variable().index();
                if v < n_vars {
                    participating.insert(v);
                }
            }
        } else if w >= 2 && clause.iter().all(|l| l.is_positive()) {
            alo_wide_count += 1;
        }
    }

    let participating_vars = participating.len() as f64;
    let var_coverage = participating_vars / (n_vars as f64);
    let balance = if alo_wide_count == 0 {
        0.0
    } else {
        (amo_pair_count as f64 / alo_wide_count as f64).min(1.0)
    };

    (var_coverage * balance).clamp(0.0, 1.0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parity, pigeonhole, random_k_cnf};

    #[test]
    fn test_features_empty_formula() {
        let cnf = Cnf::new_with_capacity(0, 0);
        let f = ProofComplexityFeatures::from_cnf(&cnf);
        assert_eq!(f.num_vars, 0);
        assert_eq!(f.num_clauses, 0);
        assert_eq!(f.clause_width_max, 0);
        assert_eq!(f.clause_width_mean, 0.0);
        assert_eq!(f.xor_density, 0.0);
        assert_eq!(f.cardinality_density, 0.0);
        assert_eq!(f.vig_density, 0.0);
        assert!(f.treewidth_approx.is_none());
        assert_eq!(f.pigeonhole_score, 0.0);
    }

    #[test]
    fn test_features_pigeonhole_has_cardinality_signature() {
        // php(3) encodes at-most-one constraints as width-2 all-negative
        // clauses. They should dominate the cardinality density.
        let cnf = pigeonhole(3);
        let f = ProofComplexityFeatures::from_cnf(&cnf);
        assert!(
            f.cardinality_density > 0.5,
            "expected pigeonhole to be cardinality-heavy, got {}",
            f.cardinality_density
        );
        assert_eq!(f.clause_width_max, 3, "alo clauses are width 3 for php(3)");
    }

    #[test]
    fn test_features_parity_has_xor_signature() {
        // parity(3): all 4 width-3 clauses are odd-parity XOR patterns.
        let cnf = parity(3);
        let f = ProofComplexityFeatures::from_cnf(&cnf);
        assert_eq!(f.num_clauses, 4);
        assert_eq!(f.clause_width_max, 3);
        assert!(
            (f.xor_density - 1.0).abs() < 1e-9,
            "expected xor_density=1.0 for parity(3), got {}",
            f.xor_density
        );
    }

    #[test]
    fn test_features_random_cnf_bounds() {
        let cnf = random_k_cnf(3, 20, 60, Some(7));
        let f = ProofComplexityFeatures::from_cnf(&cnf);
        assert_eq!(f.clause_width_max, 3);
        assert!(f.clause_width_mean > 0.0);
        assert!(f.xor_density >= 0.0 && f.xor_density <= 1.0);
        assert!(f.cardinality_density >= 0.0 && f.cardinality_density <= 1.0);
        assert!(f.modularity >= 0.0 && f.modularity <= 1.0);
        assert!(f.vig_density >= 0.0 && f.vig_density <= 1.0);
        let tw = f.treewidth_approx.expect("random cnf has VIG vertices");
        assert!(tw >= 0.0);
        assert!(f.pigeonhole_score >= 0.0 && f.pigeonhole_score <= 1.0);
    }

    #[test]
    fn test_vig_density_triangle() {
        // A single width-3 clause over vars {0,1,2} creates a complete
        // triangle in the VIG: V=3, E=3, density = 3 / (3*2/2) = 1.0.
        let mut cnf = Cnf::new_with_capacity(3, 1);
        cnf.add_clause(&[
            crate::Lit::positive(crate::Var::new(0)),
            crate::Lit::positive(crate::Var::new(1)),
            crate::Lit::positive(crate::Var::new(2)),
        ]);
        let f = ProofComplexityFeatures::from_cnf(&cnf);
        assert!(
            (f.vig_density - 1.0).abs() < 1e-9,
            "expected VIG density 1.0 for triangle, got {}",
            f.vig_density
        );
    }

    #[test]
    fn test_vig_density_disjoint_units() {
        // 5 unit clauses over 5 variables: no pair-interactions, VIG is
        // edgeless, density 0.
        let mut cnf = Cnf::new_with_capacity(5, 5);
        for i in 0..5 {
            cnf.add_clause(&[crate::Lit::positive(crate::Var::new(i))]);
        }
        let f = ProofComplexityFeatures::from_cnf(&cnf);
        assert_eq!(f.vig_density, 0.0);
        assert_eq!(
            f.treewidth_approx,
            Some(0.0),
            "edgeless VIG has treewidth 0"
        );
    }

    #[test]
    fn test_treewidth_approx_path() {
        // Build a path x0-x1, x1-x2, ..., x4-x5 via width-2 clauses.
        // A path has treewidth 1; min-degree heuristic recovers 1.
        let mut cnf = Cnf::new_with_capacity(6, 5);
        for i in 0..5 {
            cnf.add_clause(&[
                crate::Lit::positive(crate::Var::new(i)),
                crate::Lit::positive(crate::Var::new(i + 1)),
            ]);
        }
        let f = ProofComplexityFeatures::from_cnf(&cnf);
        let tw = f.treewidth_approx.expect("path has VIG vertices");
        assert!(
            (tw - 1.0).abs() < 1e-9,
            "expected path treewidth upper bound = 1, got {tw}"
        );
    }

    #[test]
    fn test_treewidth_approx_clique() {
        // A single 5-clause creates a K_5 VIG. K_5 has treewidth 4.
        let mut cnf = Cnf::new_with_capacity(5, 1);
        let lits: Vec<_> = (0..5)
            .map(|i| crate::Lit::positive(crate::Var::new(i)))
            .collect();
        cnf.add_clause(&lits);
        let f = ProofComplexityFeatures::from_cnf(&cnf);
        let tw = f.treewidth_approx.expect("clique has VIG vertices");
        // Min-degree heuristic on K_n produces exactly n-1.
        assert!(
            (tw - 4.0).abs() < 1e-9,
            "expected K5 treewidth = 4, got {tw}"
        );
    }

    #[test]
    fn test_pigeonhole_score_matches_php() {
        // pigeonhole(3) encodes 4 pigeons in 3 holes with the canonical
        // ALO (width 3 all-positive) and AMO (width 2 all-negative)
        // structure. The score should be high.
        let cnf = pigeonhole(3);
        let f = ProofComplexityFeatures::from_cnf(&cnf);
        assert!(
            f.pigeonhole_score > 0.8,
            "expected pigeonhole_score > 0.8 for php(3), got {}",
            f.pigeonhole_score
        );
    }

    #[test]
    fn test_pigeonhole_score_zero_on_parity() {
        // parity(3): only width-3 clauses with mixed polarities. No AMO
        // width-2-all-negative clauses. Score must be 0.
        let cnf = parity(3);
        let f = ProofComplexityFeatures::from_cnf(&cnf);
        assert_eq!(f.pigeonhole_score, 0.0);
    }

    #[test]
    fn test_pigeonhole_score_bounded_on_random() {
        let cnf = random_k_cnf(3, 30, 120, Some(11));
        let f = ProofComplexityFeatures::from_cnf(&cnf);
        // Random 3-CNF has no structured AMO+ALO pairing: score is
        // tiny. Keep the bound loose so seed changes don't break it.
        assert!(
            f.pigeonhole_score < 0.2,
            "random CNF should not look PHP-like, got {}",
            f.pigeonhole_score
        );
    }
}
