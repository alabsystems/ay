// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Named unsat-core extraction for finite-enum pigeonhole refutations
//! (#uc-qfdt).
//!
//! The finite-enum pigeonhole pass (`add_finite_enum_pigeonhole_conflict`)
//! proves UNSAT whenever the assertions force `> k` pairwise-distinct values
//! of a `k`-inhabitant all-nullary (enum) datatype sort. Under
//! `produce-unsat-cores` with named assertions (the SMT-COMP Unsat-Core track
//! shape: every assert named), plain `check-sat` is redirected through the
//! generic assumption engine, which never reaches that pass — so
//! coloring-style instances (SMT-LIB 20210312-Bouvier, up to 512k asserts)
//! time out in named mode even though the unnamed instance is decided in
//! seconds.
//!
//! This module runs the pigeonhole refutation BEFORE the named→assumptions
//! redirect and extracts a small, validator-friendly named core:
//!
//! - Every clique edge `a != b` is mapped to the top-level SOURCE
//!   ASSERTION(S) that entail it (`:named` ids equal the bare inner assertion
//!   TermIds, see `ay-frontend/src/elaborate/term.rs`
//!   `process_term_annotations`). The core takes the EDGE CLOSURE over the
//!   clique vertex set: every original assertion entailing a within-clique
//!   edge is included, not just the first-recorded source per pair (a
//!   superset only strengthens an unsat core).
//! - The clique search is SEED-BIASED: it prefers vertices whose finite-enum
//!   domain is narrowed by a MEMBERSHIP assertion (`(or (= x c1) .. (= x cm))`
//!   / `(= x c)`); those membership assertions join the core. A pure
//!   `(k+1)`-clique core is logically UNSAT but practically unvalidatable —
//!   its refutation embeds a pigeonhole proof, exponential for resolution —
//!   while the membership chains give validating solvers a short
//!   domain-narrowing proof (measured: vlsat3_b98 k=81 seed core of 3,401 of
//!   512,764 asserts validates in minutes; the pure-clique core does not).
//! - Validator hardness scales with the RESIDUAL (clique members WITHOUT a
//!   membership chain): each residual vertex is unconstrained over all `k`
//!   constructors, so the validator's endgame is a pigeonhole over the
//!   residual instead of cheap domain propagation. Measured on vlsat3_b98
//!   (k=81): the residual-3 selection validates in 165.6 s while a
//!   same-size, same-membership residual-4 selection does not validate at
//!   1250 s. The drop-1 completion below therefore reconsiders EVERY clique
//!   member (most-unlocking drop first), not just the last few greedy picks —
//!   on b98 the single blocking seed (p19) is an EARLY greedy pick.
//!
//! FAIL-CLOSED: a core is returned ONLY after in-process re-verification that
//! the core assertions ALONE re-derive every clique edge over the same sort
//! with the same (declaration-derived) cardinality, and only when every core
//! assertion is named. Any mismatch falls back to the generic redirect path
//! (whose worst case is the all-named core: reduction 0, error-free). The
//! invariant is 0 invalidated cores — never emit a core that is not
//! self-verified.

use super::super::super::Executor;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, TermData, TermId};

/// Size-gated core ENRICHMENT (giant-clique validator hardness, #uc-qfdt):
/// for cliques over sorts with `k >= AY_UC_ENRICH_K` (default 43) the core
/// additionally includes edge assertions with EXACTLY ONE endpoint in the
/// clique whose other endpoint is a clique-adjacent high-coverage vertex,
/// plus the edges among those vertices (see `enrich_pigeonhole_core`).
/// This mimics the measured shape of cvc5's 2025 cores on vlsat3_b79/b89
/// (the two giant instances whose pure-clique AY cores exceed the 1200 s
/// validation budget while cvc5's validate in 1-3 s): cvc5's b79 core is the
/// same 82 membership asserts + a near-clique whose 7 extra vertices each
/// connect to ~80 of the 84 clique members (560 one-endpoint edges); its b89
/// core adds 17 such vertices (~1.3k edges). The extra vertices are, first,
/// the sort's membership SUBJECTS that fell outside the clique (their domain
/// chains are already in the core; wiring them to the clique lets the
/// validator propagate through them instead of leaving them floating), then
/// the highest-coverage non-subject neighbours.
///
/// THRESHOLD CHOICE (measured, deliberate): default 43. Every k >= 43 probe
/// instance was DUAL-VALIDATED (cvc5 + SMTInterpol, 1200 s budget) in its
/// enriched shape before this default was adopted, and enrichment made all
/// of them FASTER to validate, including the one that already validated
/// un-enriched:
///   b98 k=81: un-enriched 194 s/38.6 s -> enriched 0.1 s/2.6 s (red 507,956)
///   b79 k=83: dual timeout (>1205 s)   -> enriched 0.2 s/3.4 s (red 260,953)
///   b89 k=86: dual timeout (>1205 s)   -> enriched 0.3 s/3.5 s (red 260,662)
///   e97 k=43: dual timeout (>1205 s)   -> enriched 15.9 s/24.4 s (red 147,381)
/// 43 is the smallest k with a measured win; every validated below-threshold
/// probe instance (all k <= 24, incl. e91) emits a BYTE-IDENTICAL core.
/// Enrichment is SUPERSET-only over the re-verified clique core, so it is
/// trivially sound; the fail-closed in-process re-verification still covers
/// the clique subset, and the name cost is O(k) per core (b98: 1,407 of a
/// 509,363 reduction) against the difference between a validated and an
/// unvalidated (0-point) core.
const UC_ENRICH_K_DEFAULT: usize = 43;
/// Max enrichment vertices per core (cvc5's measured shapes use 7 and 17).
const UC_ENRICH_VERTEX_CAP: usize = 16;

/// Disequality edges over one provably-finite datatype sort, with per-edge
/// source-assertion provenance. `edges` maps the ordered term pair to the
/// FIRST top-level assertion that entails the disequality (any single source
/// suffices for core soundness; first-recorded keeps assembly deterministic).
/// `extra_sources` keeps every FURTHER distinct assertion entailing an
/// already-recorded pair, so core assembly can take the full edge closure
/// over the clique vertex set (validator-friendly superset; empty — zero
/// overhead — when no assertion duplicates another's edge, the common case).
pub(in crate::executor) struct EnumDiseqEdges {
    /// Exact cardinality of the sort (from the datatype declaration).
    pub(in crate::executor) k: usize,
    /// Ordered disequality pair -> first source assertion TermId.
    pub(in crate::executor) edges: HashMap<(TermId, TermId), TermId>,
    /// Ordered disequality pair -> additional source assertions (dedup'd,
    /// in first-recorded order).
    pub(in crate::executor) extra_sources: HashMap<(TermId, TermId), Vec<TermId>>,
}

impl EnumDiseqEdges {
    pub(in crate::executor) fn new(k: usize) -> Self {
        EnumDiseqEdges {
            k,
            edges: HashMap::default(),
            extra_sources: HashMap::default(),
        }
    }

    /// Record `source` as entailing the disequality `pair`. The first source
    /// per pair defines the graph; later DISTINCT sources are kept aside for
    /// the edge-closure core assembly.
    pub(in crate::executor) fn record(&mut self, pair: (TermId, TermId), source: TermId) {
        match self.edges.get(&pair) {
            None => {
                self.edges.insert(pair, source);
            }
            Some(&first) if first != source => {
                let extras = self.extra_sources.entry(pair).or_default();
                if !extras.contains(&source) {
                    extras.push(source);
                }
            }
            Some(_) => {}
        }
    }
}

/// A membership (domain-narrowing) assertion for one enum-sorted term:
/// `(= x c)` or `(or (= x c1) ... (= x cm))` with every `ci` a constructor
/// constant of `x`'s sort. `domain` is the number of distinct constructor
/// constants mentioned (narrower = better validation seed).
pub(in crate::executor) struct EnumMembership {
    pub(in crate::executor) assertion: TermId,
    pub(in crate::executor) domain: usize,
}

/// Bitset-adjacency clique graph over the distinct enum-sorted terms of one
/// sort's disequality edges. Nodes are sorted by TermId for determinism.
struct CliqueGraph {
    nodes: Vec<TermId>,
    index: HashMap<TermId, usize>,
    words: usize,
    adj: Vec<u64>,
}

impl CliqueGraph {
    fn from_edges(edges: &HashMap<(TermId, TermId), TermId>, max_nodes: usize) -> Option<Self> {
        let mut nodes: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        for &(a, b) in edges.keys() {
            if seen.insert(a) {
                nodes.push(a);
            }
            if seen.insert(b) {
                nodes.push(b);
            }
        }
        if nodes.len() > max_nodes {
            return None; // too large: sound skip
        }
        // Deterministic node numbering regardless of hash iteration order.
        nodes.sort_by_key(|t| t.0);
        let n = nodes.len();
        let index: HashMap<TermId, usize> =
            nodes.iter().enumerate().map(|(i, &t)| (t, i)).collect();
        let words = n.div_ceil(64);
        let mut adj = vec![0u64; n * words];
        for &(a, b) in edges.keys() {
            let (ia, ib) = (index[&a], index[&b]);
            if ia != ib {
                adj[ia * words + ib / 64] |= 1u64 << (ib % 64);
                adj[ib * words + ia / 64] |= 1u64 << (ia % 64);
            }
        }
        Some(CliqueGraph {
            nodes,
            index,
            words,
            adj,
        })
    }

    fn n(&self) -> usize {
        self.nodes.len()
    }

    fn to_terms(&self, clique: &[usize]) -> Vec<TermId> {
        clique.iter().map(|&v| self.nodes[v]).collect()
    }

    /// Set bit positions of a bitset, ascending.
    fn ones(bits: &[u64]) -> Vec<usize> {
        let mut out = Vec::new();
        for (w, &word) in bits.iter().enumerate() {
            let mut b = word;
            while b != 0 {
                out.push(w * 64 + b.trailing_zeros() as usize);
                b &= b - 1;
            }
        }
        out
    }

    fn popcount(bits: &[u64]) -> usize {
        bits.iter().map(|w| w.count_ones() as usize).sum()
    }

    /// Greedy completion of `clique` (kept as node indices, `cand` = nodes
    /// adjacent to every member): repeatedly add the candidate with the
    /// largest common neighbourhood inside `cand`, preferring seeds and
    /// narrower domains on ties, until the clique reaches `target` or the
    /// candidate set empties. Every grown set stays a genuine clique by
    /// construction. Returns `true` on reaching `target`.
    ///
    /// `exhaust`: grow to candidate exhaustion even when `target` is provably
    /// unreachable (skip the reachability prune). The seed-subgraph phase
    /// NEEDS this: with fewer seeds than `target` (vlsat3_b98: 80 membership
    /// seeds < target 82) the prune would abandon the phase at the START
    /// vertex, and the arbitrary-vertex completion then greedily wanders off
    /// the membership staircase — the exact residual-4, validator-hard b98
    /// selection. Growing the seed clique to exhaustion first keeps every
    /// reachable membership vertex in the clique.
    fn complete_greedy(
        &self,
        clique: &mut Vec<usize>,
        cand: &mut [u64],
        target: usize,
        seed_domain: &[Option<usize>],
        budget: &mut u64,
        exhaust: bool,
    ) -> bool {
        let words = self.words;
        loop {
            if clique.len() >= target {
                return true;
            }
            // Prune: cannot reach target even taking every candidate.
            if !exhaust && clique.len() + Self::popcount(cand) < target {
                return false;
            }
            let mut best: Option<(usize, usize, bool, usize)> = None; // (v, common, seed, domain)
            for u in Self::ones(cand) {
                if *budget < words as u64 {
                    return false; // budget exhausted: sound skip
                }
                *budget -= words as u64;
                let common: usize = (0..words)
                    .map(|i| (self.adj[u * words + i] & cand[i]).count_ones() as usize)
                    .sum();
                let seed = seed_domain[u].is_some();
                let domain = seed_domain[u].unwrap_or(usize::MAX);
                let better = match best {
                    None => true,
                    Some((_, bc, bs, bd)) => {
                        common > bc
                            || (common == bc && seed && !bs)
                            || (common == bc && seed == bs && domain < bd)
                    }
                };
                if better {
                    best = Some((u, common, seed, domain));
                }
            }
            let Some((u, ..)) = best else {
                return false;
            };
            clique.push(u);
            for (i, candidate) in cand.iter_mut().enumerate() {
                *candidate &= self.adj[u * words + i];
            }
        }
    }

    /// Seed-first clique search: from each of the highest-seed-degree seed
    /// vertices, (1) grow greedily INSIDE the seed subgraph, (2) complete
    /// with arbitrary vertices, (3) on a near miss retry after dropping one
    /// member ("drop-1 completion"), trying EVERY member as the drop in
    /// most-promising order (largest unlocked candidate pool first). Returns
    /// a clique of size `> k` as node indices, or `None` (sound skip — caller
    /// falls back to the general search).
    fn seed_first_clique(
        &self,
        k: usize,
        seed_domain: &[Option<usize>],
        restarts: usize,
        budget: &mut u64,
    ) -> Option<Vec<usize>> {
        let n = self.n();
        let words = self.words;
        let target = k + 1;
        let mut seed_mask = vec![0u64; words];
        for v in 0..n {
            if seed_domain[v].is_some() {
                seed_mask[v / 64] |= 1u64 << (v % 64);
            }
        }
        if Self::popcount(&seed_mask) == 0 {
            return None;
        }
        // Restart seeds: highest degree within the seed subgraph first.
        let mut starts: Vec<(usize, usize)> = (0..n)
            .filter(|&v| seed_domain[v].is_some())
            .map(|v| {
                let deg: usize = (0..words)
                    .map(|i| (self.adj[v * words + i] & seed_mask[i]).count_ones() as usize)
                    .sum();
                (v, deg)
            })
            .collect();
        *budget = budget.saturating_sub((n * words) as u64);
        starts.sort_by_key(|&(v, deg)| (std::cmp::Reverse(deg), self.nodes[v].0));
        starts.truncate(restarts);

        for &(start, _) in &starts {
            if *budget == 0 {
                return None;
            }
            // Phase 1: grow inside the seed subgraph, to EXHAUSTION — even
            // when the seeds alone cannot reach the target (vlsat3_b98:
            // 80 seeds < target 82) the maximal seed clique is the right
            // base for completion; see `complete_greedy` on `exhaust`.
            let mut clique = vec![start];
            let mut cand: Vec<u64> = (0..words)
                .map(|i| self.adj[start * words + i] & seed_mask[i])
                .collect();
            if self.complete_greedy(&mut clique, &mut cand, target, seed_domain, budget, true) {
                return Some(clique); // an all-seed (k+1)-clique: residual 0
            }
            if std::env::var_os("AY_DEBUG_PIGEONHOLE").is_some() {
                eprintln!(
                    "c sfc-debug start={} phase1_len={} budget={}",
                    self.nodes[start].0,
                    clique.len(),
                    budget
                );
            }
            // Phase 2: complete the seed clique with arbitrary vertices.
            let mut cand_full = self.common_neighbours(&clique);
            if self.complete_greedy(
                &mut clique,
                &mut cand_full,
                target,
                seed_domain,
                budget,
                false,
            ) {
                return Some(clique);
            }
            // Phase 3: drop-1 completion — try dropping EACH clique member
            // and re-completing, most-promising drop first (largest unlocked
            // common-neighbour pool; deterministic node-id tie-break). The
            // blocking member is often an EARLY greedy pick — on vlsat3_b98
            // the seed p19 is the ONLY member of the maximal 80-seed clique
            // whose removal unlocks a completion (pool 15 vs <=1 for every
            // other drop), and it is added 20th of 80; a last-added-first
            // order never reconsiders it. Dropping it yields the residual-3
            // clique (79 membership seeds + 3 free vertices) whose reduced
            // benchmark is, up to renaming of the free constants, EXACTLY
            // the probe-validated b98 seed core (165.6 s at k=81).
            const DROP1_COMPLETION_ATTEMPTS: usize = 16;
            let mut drops: Vec<(usize, usize)> = Vec::with_capacity(clique.len());
            for i in 0..clique.len() {
                let per_drop_cost = (clique.len() * words) as u64;
                if *budget < per_drop_cost {
                    return None; // budget exhausted: sound skip
                }
                *budget -= per_drop_cost;
                let c2: Vec<usize> = clique
                    .iter()
                    .enumerate()
                    .filter(|&(j, _)| j != i)
                    .map(|(_, &v)| v)
                    .collect();
                let pool = Self::popcount(&self.common_neighbours(&c2));
                drops.push((i, pool));
            }
            drops.sort_by_key(|&(i, pool)| (std::cmp::Reverse(pool), self.nodes[clique[i]].0));
            for &(drop, pool) in drops.iter().take(DROP1_COMPLETION_ATTEMPTS) {
                if *budget == 0 {
                    return None;
                }
                // Even taking the whole pool cannot reach the target: skip.
                if clique.len() - 1 + pool < target {
                    continue;
                }
                let mut c2: Vec<usize> = clique
                    .iter()
                    .enumerate()
                    .filter(|&(i, _)| i != drop)
                    .map(|(_, &v)| v)
                    .collect();
                let mut cand2 = self.common_neighbours(&c2);
                if self.complete_greedy(&mut c2, &mut cand2, target, seed_domain, budget, false) {
                    return Some(c2);
                }
            }
        }
        None
    }

    /// Bitset of nodes adjacent to EVERY member of `clique` (members
    /// themselves excluded automatically: no self-loops).
    fn common_neighbours(&self, clique: &[usize]) -> Vec<u64> {
        let words = self.words;
        let mut cand = vec![u64::MAX; words];
        // Mask off bits beyond n.
        let n = self.n();
        if !n.is_multiple_of(64) {
            cand[words - 1] = (1u64 << (n % 64)) - 1;
        }
        for &m in clique {
            for (i, candidate) in cand.iter_mut().enumerate() {
                *candidate &= self.adj[m * words + i];
            }
        }
        cand
    }

    /// Swap-improvement toward seeds: replace a non-seed clique member with a
    /// seed vertex adjacent to all OTHER members (narrowest domain first).
    /// Every swap strictly increases the seed count, so the loop terminates.
    /// The result is re-verified edge-by-edge by the caller regardless.
    fn swap_improve(
        &self,
        mut clique: Vec<usize>,
        seed_domain: &[Option<usize>],
        budget: &mut u64,
    ) -> Vec<usize> {
        let n = self.n();
        let words = self.words;
        let mut in_clique = vec![false; n];
        for &m in &clique {
            in_clique[m] = true;
        }
        let mut seeds: Vec<usize> = (0..n).filter(|&v| seed_domain[v].is_some()).collect();
        seeds.sort_by_key(|&v| (seed_domain[v].unwrap_or(usize::MAX), self.nodes[v].0));
        loop {
            let mut swapped = false;
            for i in 0..clique.len() {
                if seed_domain[clique[i]].is_some() {
                    continue; // already a seed
                }
                // Members-except-i mask.
                let mut need = vec![0u64; words];
                for (j, &m) in clique.iter().enumerate() {
                    if j != i {
                        need[m / 64] |= 1u64 << (m % 64);
                    }
                }
                for &s in &seeds {
                    if in_clique[s] {
                        continue;
                    }
                    if *budget < words as u64 {
                        return clique; // budget exhausted: keep what we have
                    }
                    *budget -= words as u64;
                    let ok = (0..words).all(|w| self.adj[s * words + w] & need[w] == need[w]);
                    if ok {
                        in_clique[clique[i]] = false;
                        in_clique[s] = true;
                        clique[i] = s;
                        swapped = true;
                        break;
                    }
                }
            }
            if !swapped {
                return clique;
            }
        }
    }
}

impl Executor {
    /// Attempt the finite-enum pigeonhole NAMED-CORE fast path. Returns the
    /// core assertion TermIds (clique-edge source assertions + the clique
    /// members' membership assertions) iff a re-verified `> k` disequality
    /// clique exists over some `k`-inhabitant enum sort AND every core
    /// assertion is named. On ANY doubt returns `None` (sound skip: the
    /// caller proceeds with the generic named→assumptions redirect).
    pub(in crate::executor) fn try_enum_pigeonhole_named_core(
        &mut self,
        named: &HashMap<TermId, String>,
    ) -> Option<Vec<TermId>> {
        let debug = std::env::var_os("AY_DEBUG_PIGEONHOLE").is_some();
        // Cheap gate: the pass only ever fires over declared datatypes.
        if self.ctx.datatype_iter().next().is_none() {
            if debug {
                eprintln!("c pigeonhole-core-debug decline=no-datatypes");
            }
            return None;
        }
        let assertions = self.ctx.assertions.clone();
        let mut by_sort: HashMap<Sort, EnumDiseqEdges> = HashMap::default();
        for &assertion in &assertions {
            self.collect_finite_enum_diseq_edges(assertion, assertion, &mut by_sort);
        }
        for &assertion in &assertions {
            self.collect_guarded_ite_diseq_edges(assertion, assertion, &mut by_sort);
        }
        if by_sort.is_empty() {
            if debug {
                eprintln!("c pigeonhole-core-debug decline=no-edges");
            }
            return None;
        }
        let membership = self.collect_enum_membership_assertions(&assertions);

        // Deterministic sort order: densest edge set first (the conflict, if
        // any, almost always lives there), stable across runs.
        let mut sorted: Vec<(Sort, EnumDiseqEdges)> = by_sort.into_iter().collect();
        sorted.sort_by_key(|(_, info)| (std::cmp::Reverse(info.edges.len()), info.k));

        for (sort, info) in &sorted {
            if info.edges.is_empty() {
                continue;
            }
            let mem = membership.get(sort);
            if debug {
                eprintln!(
                    "c pigeonhole-core-debug sort={:?} k={} edges={} seeds={}",
                    sort,
                    info.k,
                    info.edges.len(),
                    mem.map_or(0, |m| m.len())
                );
            }
            let Some(clique) = self.seed_biased_pigeonhole_clique(info, mem) else {
                if debug {
                    eprintln!("c pigeonhole-core-debug decline=no-clique");
                }
                continue;
            };
            if debug {
                let residual = clique
                    .iter()
                    .filter(|&&t| mem.is_none_or(|m| !m.contains_key(&t)))
                    .count();
                eprintln!(
                    "c pigeonhole-core-debug clique={} residual={}",
                    clique.len(),
                    residual
                );
            }
            let Some(core) = Self::assemble_pigeonhole_core(
                info,
                mem,
                &clique,
                named,
                Self::uc_enrich_k_threshold(),
            ) else {
                if debug {
                    eprintln!("c pigeonhole-core-debug decline=assemble-failed");
                }
                continue;
            };
            // FAIL-CLOSED gate 1: every core assertion must be named, or the
            // emitted name set would under-cover the refutation when the
            // consumer keeps only core-named assertions (competition
            // validation semantics). Mixed named/unnamed inputs fall back.
            if !core.iter().all(|a| named.contains_key(a)) {
                if debug {
                    eprintln!("c pigeonhole-core-debug decline=unnamed-core-assertion");
                }
                continue;
            }
            // FAIL-CLOSED gate 2: the core assertions ALONE must re-derive
            // the full clique (re-run the pigeonhole collectors restricted to
            // the core). A failed re-verification is a sound skip.
            // A failed re-verification is a SOUND skip (fall through to the
            // generic redirect) — deliberately no debug_assert here: the
            // fail-closed branch must stay a silent skip in every build
            // profile, never a debug-build panic (U4 review finding F3).
            if !self.verify_pigeonhole_core_entails_clique(&core, sort, info.k, &clique) {
                if debug {
                    eprintln!("c pigeonhole-core-debug decline=verify-failed");
                }
                continue;
            }
            if debug {
                eprintln!("c pigeonhole-core-debug core={}", core.len());
            }
            return Some(core);
        }
        None
    }

    /// Seed-biased `> k` clique selection over one sort's disequality graph.
    /// Prefers membership-narrowed vertices (they admit short domain-chain
    /// validation proofs); falls back to the general budgeted clique search
    /// with a swap-improvement pass toward seeds.
    fn seed_biased_pigeonhole_clique(
        &self,
        info: &EnumDiseqEdges,
        membership: Option<&HashMap<TermId, EnumMembership>>,
    ) -> Option<Vec<TermId>> {
        let k = info.k;
        let graph = CliqueGraph::from_edges(&info.edges, Self::FINITE_ENUM_PIGEONHOLE_MAX_NODES)?;
        if graph.n() <= k {
            return None;
        }
        let seed_domain: Vec<Option<usize>> = graph
            .nodes
            .iter()
            .map(|t| membership.and_then(|m| m.get(t)).map(|e| e.domain))
            .collect();
        let mut budget = Self::FINITE_ENUM_PIGEONHOLE_WORK_BUDGET;

        if membership.is_some() {
            if let Some(clique) = graph.seed_first_clique(
                k,
                &seed_domain,
                Self::FINITE_ENUM_PIGEONHOLE_GREEDY_RESTARTS,
                &mut budget,
            ) {
                let improved = graph.swap_improve(clique, &seed_domain, &mut budget);
                return Some(graph.to_terms(&improved));
            }
        }
        // Fallback: the general (greedy + exact Bron–Kerbosch) search used by
        // the plain-path pigeonhole pass, then swap toward seeds.
        let edge_set: HashSet<(TermId, TermId)> = info.edges.keys().copied().collect();
        let clique = self.disequality_graph_clique_exceeding(&edge_set, k)?;
        if membership.is_some() {
            let idxs: Vec<usize> = clique.iter().map(|t| graph.index[t]).collect();
            let improved = graph.swap_improve(idxs, &seed_domain, &mut budget);
            return Some(graph.to_terms(&improved));
        }
        Some(clique)
    }

    /// Effective enrichment gate: sorts with `k >=` this threshold get the
    /// neighbourhood-edge enrichment (see `UC_ENRICH_K_DEFAULT` for the
    /// measured rationale). Env-tunable via `AY_UC_ENRICH_K` for probing a
    /// different cutoff (each probe instance was validated through exactly
    /// this override before the default moved).
    fn uc_enrich_k_threshold() -> usize {
        std::env::var("AY_UC_ENRICH_K")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(UC_ENRICH_K_DEFAULT)
    }

    /// Core assembly: the EDGE CLOSURE over the clique vertex set — every
    /// original assertion entailing a within-clique edge (the first-recorded
    /// source per pair plus all extra sources) — plus, for `k >=
    /// enrich_k_threshold` only, the one-endpoint ENRICHMENT edges (see
    /// `UC_ENRICH_K_DEFAULT`) — plus ALL of the clique sort's membership
    /// assertions. The membership chains are what make the core VALIDATABLE:
    /// a bare `(k+1)`-clique core embeds a pigeonhole proof (exponential for
    /// resolution — measured unvalidatable at k>=16), while the domain
    /// chains admit a short narrowing refutation (the shape of the
    /// cvc5-validated vlsat3_b98 seed core: 3,321 clique edges + all 80
    /// membership chains). Extra membership/duplicate-edge/enrichment
    /// assertions only strengthen the (already unsat) core — never a
    /// soundness risk — and cost O(k) names against reductions of O(N).
    /// Returns `None` if ANY clique pair lacks a recorded source — fail
    /// closed, never guess.
    ///
    /// BYTE-IDENTITY INVARIANT: for `info.k < enrich_k_threshold` this
    /// function is exactly the pre-enrichment assembly — the enrichment
    /// block is guarded first thing and never runs, so below-threshold
    /// emissions cannot move (probe-verified byte-identical on
    /// b10/b94/b29/b42/e53/e60/e91).
    fn assemble_pigeonhole_core(
        info: &EnumDiseqEdges,
        membership: Option<&HashMap<TermId, EnumMembership>>,
        clique: &[TermId],
        named: &HashMap<TermId, String>,
        enrich_k_threshold: usize,
    ) -> Option<Vec<TermId>> {
        let mut core: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        for i in 0..clique.len() {
            for j in (i + 1)..clique.len() {
                let pair = Self::ordered_term_pair(clique[i], clique[j]);
                let &src = info.edges.get(&pair)?;
                if seen.insert(src) {
                    core.push(src);
                }
                // Edge closure: include EVERY other assertion entailing this
                // within-clique edge (superset composition, trivially sound).
                if let Some(extras) = info.extra_sources.get(&pair) {
                    for &extra in extras {
                        if seen.insert(extra) {
                            core.push(extra);
                        }
                    }
                }
            }
        }
        if info.k >= enrich_k_threshold {
            Self::enrich_pigeonhole_core(info, membership, clique, named, &mut core, &mut seen);
        }
        if let Some(mem) = membership {
            // Deterministic order: sort by assertion TermId.
            let mut mem_asserts: Vec<TermId> = mem.values().map(|e| e.assertion).collect();
            mem_asserts.sort_by_key(|t| t.0);
            for assertion in mem_asserts {
                if seen.insert(assertion) {
                    core.push(assertion);
                }
            }
        }
        Some(core)
    }

    /// Neighbourhood-edge ENRICHMENT for `k >= AY_UC_ENRICH_K` cliques (the
    /// measured cvc5 giant-core shape; see `UC_ENRICH_K_DEFAULT`). Appends
    /// to `core` the source assertions of (a) edges with EXACTLY ONE
    /// endpoint in the clique whose outside endpoint is clique-adjacent at
    /// high coverage (>= 3/4 of the clique; cvc5's measured enrichment
    /// vertices sit at 85-100 %), then (b) the edges AMONG the selected
    /// outside vertices (the closure cvc5's cores carry: 15 such edges on
    /// b79, 124 on b89). Candidate vertices are ranked membership-SUBJECTS
    /// first (their domain chains are already in the core — wiring them in
    /// gives the validator narrow pigeons to propagate through), then by
    /// coverage descending, then TermId ascending (deterministic). Bounded
    /// by `UC_ENRICH_VERTEX_CAP` vertices AND a total extra-edge budget of
    /// 2x the clique-edge count, taken as a rank-order prefix.
    ///
    /// The within-selected closure (b) is what makes the b89 shape
    /// validator-friendly: with it, the wired outside subjects can REPLACE
    /// unconstrained clique members in the validator's own pigeonhole,
    /// shrinking the effective residual (b89's clique has residual 11 — 11
    /// members without a domain chain — vs b79's 3). Measured: the
    /// (a)-only b89 reduced core times z3 out at 60 s and holds cvc5 past
    /// 11 minutes, while appending the 104 available within-selected edges
    /// makes z3 answer unsat in 0.33 s — cvc5's own b89 core, which carries
    /// them, validates in 1-3 s.
    ///
    /// SUPERSET-only and OPTIONAL by construction: every added assertion is
    /// verified `:named` here (unnamed sources are skipped silently), so
    /// enrichment can never flip an emittable core into the caller's
    /// all-named fail-closed decline, and the in-process clique
    /// re-verification is unaffected (it only requires clique edges, which
    /// enrichment never removes).
    fn enrich_pigeonhole_core(
        info: &EnumDiseqEdges,
        membership: Option<&HashMap<TermId, EnumMembership>>,
        clique: &[TermId],
        named: &HashMap<TermId, String>,
        core: &mut Vec<TermId>,
        seen: &mut HashSet<TermId>,
    ) {
        let n = clique.len();
        if n < 2 {
            return;
        }
        let clique_set: HashSet<TermId> = clique.iter().copied().collect();
        // Outside vertex -> its one-endpoint pairs (only pairs whose primary
        // source is named participate; enrichment is optional, never guess).
        let mut incident: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::default();
        for (&(a, b), src) in &info.edges {
            let (a_in, b_in) = (clique_set.contains(&a), clique_set.contains(&b));
            if a_in == b_in || !named.contains_key(src) {
                continue; // within-clique, fully-outside, or unnamed source
            }
            let outside = if a_in { b } else { a };
            incident.entry(outside).or_default().push((a, b));
        }
        // Coverage bar: adjacent to >= 3/4 of the clique.
        let mut candidates: Vec<(bool, usize, TermId)> = incident
            .iter()
            .filter(|(_, pairs)| pairs.len() * 4 >= n * 3)
            .map(|(&outside, pairs)| {
                let subject = membership.is_some_and(|m| m.contains_key(&outside));
                (subject, pairs.len(), outside)
            })
            .collect();
        candidates
            .sort_by_key(|&(subject, coverage, t)| (!subject, std::cmp::Reverse(coverage), t.0));
        // Extra-edge budget: 2x the clique-edge count n*(n-1)/2.
        let mut edge_budget = n * (n - 1);
        let push_pair_sources =
            |pair: (TermId, TermId), core: &mut Vec<TermId>, seen: &mut HashSet<TermId>| {
                let &src = info.edges.get(&pair).expect("pair from info.edges");
                if seen.insert(src) {
                    core.push(src);
                }
                if let Some(extras) = info.extra_sources.get(&pair) {
                    for &extra in extras {
                        if named.contains_key(&extra) && seen.insert(extra) {
                            core.push(extra);
                        }
                    }
                }
            };
        let mut selected: Vec<TermId> = Vec::new();
        for &(_, coverage, outside) in candidates.iter().take(UC_ENRICH_VERTEX_CAP) {
            if coverage > edge_budget {
                break; // rank-order prefix: stop, don't skip (deterministic)
            }
            edge_budget -= coverage;
            selected.push(outside);
            let mut pairs = std::mem::take(incident.get_mut(&outside).expect("candidate"));
            // Deterministic edge order within a vertex: by ordered pair.
            pairs.sort_by_key(|&(a, b)| (a.0, b.0));
            for pair in pairs {
                push_pair_sources(pair, core, seen);
            }
        }
        // (b) within-selected closure: named edges among the selected
        // outside vertices, in ordered-pair order (deterministic), each
        // counted against the remaining budget.
        selected.sort_by_key(|t| t.0);
        for i in 0..selected.len() {
            for j in (i + 1)..selected.len() {
                let pair = Self::ordered_term_pair(selected[i], selected[j]);
                let Some(src) = info.edges.get(&pair) else {
                    continue; // no such edge in the input
                };
                if !named.contains_key(src) {
                    continue;
                }
                if edge_budget == 0 {
                    return;
                }
                edge_budget -= 1;
                push_pair_sources(pair, core, seen);
            }
        }
    }

    /// In-process fail-closed re-verification: re-run the pigeonhole edge
    /// collectors over ONLY the core assertions and check that (a) the sort's
    /// cardinality re-derives to exactly `k` (both from the declaration and
    /// from the restricted collection), (b) the clique exceeds `k`, and
    /// (c) EVERY clique pair is re-derived as a disequality edge. `k + 1`
    /// pairwise-distinct members of a `k`-inhabitant sort is UNSAT by
    /// pigeonhole, so a `true` here certifies the core.
    pub(in crate::executor) fn verify_pigeonhole_core_entails_clique(
        &mut self,
        core: &[TermId],
        sort: &Sort,
        k: usize,
        clique: &[TermId],
    ) -> bool {
        if clique.len() <= k {
            return false;
        }
        // Independent cardinality re-derivation from the datatype declaration
        // (does not trust the collection pass that produced the candidate).
        if self.pigeonhole_datatype_cardinality(sort) != Some(k) {
            return false;
        }
        let mut by_sort: HashMap<Sort, EnumDiseqEdges> = HashMap::default();
        for &assertion in core {
            self.collect_finite_enum_diseq_edges(assertion, assertion, &mut by_sort);
        }
        for &assertion in core {
            self.collect_guarded_ite_diseq_edges(assertion, assertion, &mut by_sort);
        }
        let Some(info) = by_sort.get(sort) else {
            return false;
        };
        if info.k != k {
            return false;
        }
        for i in 0..clique.len() {
            for j in (i + 1)..clique.len() {
                let pair = Self::ordered_term_pair(clique[i], clique[j]);
                if !info.edges.contains_key(&pair) {
                    return false;
                }
            }
        }
        true
    }

    /// Collect membership (domain-narrowing) assertions per enum sort:
    /// top-level `(= x c)` / `(or (= x c1) ... (= x cm))` conjuncts where
    /// every `ci` is a constructor constant of `x`'s all-nullary datatype
    /// sort and `x` is any non-constructor term of that sort. Keeps the
    /// NARROWEST assertion per term.
    pub(in crate::executor) fn collect_enum_membership_assertions(
        &self,
        assertions: &[TermId],
    ) -> HashMap<Sort, HashMap<TermId, EnumMembership>> {
        let mut out: HashMap<Sort, HashMap<TermId, EnumMembership>> = HashMap::default();
        let mut ctor_cache: HashMap<Sort, Option<HashSet<String>>> = HashMap::default();
        for &assertion in assertions {
            self.collect_enum_membership_in(assertion, assertion, &mut out, &mut ctor_cache);
        }
        out
    }

    fn collect_enum_membership_in(
        &self,
        term: TermId,
        source: TermId,
        out: &mut HashMap<Sort, HashMap<TermId, EnumMembership>>,
        ctor_cache: &mut HashMap<Sort, Option<HashSet<String>>>,
    ) {
        match self.ctx.terms.get(term) {
            TermData::App(sym, args) if sym.name() == "and" => {
                let args = args.clone();
                for arg in args {
                    self.collect_enum_membership_in(arg, source, out, ctor_cache);
                }
            }
            TermData::App(sym, args) if sym.name() == "or" && !args.is_empty() => {
                let args = args.clone();
                let mut subject: Option<TermId> = None;
                let mut ctors: HashSet<TermId> = HashSet::default();
                for &disjunct in &args {
                    let Some((x, c)) = self.enum_membership_literal(disjunct, ctor_cache) else {
                        return;
                    };
                    match subject {
                        None => subject = Some(x),
                        Some(s) if s == x => {}
                        _ => return, // mixed subjects: not a membership chain
                    }
                    ctors.insert(c);
                }
                if let Some(x) = subject {
                    let sort = self.ctx.terms.sort(x).clone();
                    Self::record_membership(out, sort, x, source, ctors.len());
                }
            }
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                if let Some((x, _c)) = self.enum_membership_literal(term, ctor_cache) {
                    let sort = self.ctx.terms.sort(x).clone();
                    Self::record_membership(out, sort, x, source, 1);
                }
            }
            _ => {}
        }
    }

    /// `(= x c)` (either operand order) with `c` a constructor constant of an
    /// all-nullary datatype sort and `x` NOT one → `Some((x, c))`.
    fn enum_membership_literal(
        &self,
        term: TermId,
        ctor_cache: &mut HashMap<Sort, Option<HashSet<String>>>,
    ) -> Option<(TermId, TermId)> {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }
        let (a, b) = (args[0], args[1]);
        let sort = self.ctx.terms.sort(a).clone();
        if !ctor_cache.contains_key(&sort) {
            let names = self.enum_datatype_ctor_names(&sort);
            ctor_cache.insert(sort.clone(), names);
        }
        let ctors = ctor_cache.get(&sort).and_then(|o| o.as_ref())?;
        let is_ctor = |t: TermId| matches!(self.ctx.terms.get(t), TermData::Var(name, _) if ctors.contains(name.as_str()));
        match (is_ctor(a), is_ctor(b)) {
            (false, true) => Some((a, b)),
            (true, false) => Some((b, a)),
            _ => None,
        }
    }

    /// Constructor-constant names of an ALL-NULLARY (enum) datatype sort,
    /// with NO cap on the constructor count (unlike
    /// `finite_enum_datatype_ctors`, whose 16-ctor cap serves array index
    /// enumeration; Bouvier enum sorts reach 205 constructors).
    fn enum_datatype_ctor_names(&self, sort: &Sort) -> Option<HashSet<String>> {
        match sort {
            Sort::Datatype(dt) => {
                if dt.constructors.is_empty()
                    || !dt.constructors.iter().all(|c| c.fields.is_empty())
                {
                    return None;
                }
                Some(dt.constructors.iter().map(|c| c.name.clone()).collect())
            }
            Sort::Uninterpreted(name) => {
                let ctors: Vec<String> = self
                    .ctx
                    .datatype_iter()
                    .find(|(dt_name, _)| dt_name == name)
                    .map(|(_, cs)| cs.iter().map(String::clone).collect())
                    .unwrap_or_default();
                if ctors.is_empty() {
                    return None;
                }
                let all_nullary = ctors.iter().all(|c| {
                    self.ctx
                        .constructor_selector_info(c)
                        .map_or(true, |f| f.is_empty())
                });
                if all_nullary {
                    Some(ctors.into_iter().collect())
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn record_membership(
        out: &mut HashMap<Sort, HashMap<TermId, EnumMembership>>,
        sort: Sort,
        subject: TermId,
        source: TermId,
        domain: usize,
    ) {
        let per_sort = out.entry(sort).or_default();
        match per_sort.get(&subject) {
            Some(existing) if existing.domain <= domain => {}
            _ => {
                per_sort.insert(
                    subject,
                    EnumMembership {
                        assertion: source,
                        domain,
                    },
                );
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Executor;
    use ay_frontend::parse;

    /// Execute declarations + asserts (no check-sat) and return the executor.
    fn exec_setup(input: &str) -> Executor {
        let commands = parse(input).unwrap();
        let mut exec = Executor::new();
        exec.execute_all(&commands).unwrap();
        exec
    }

    const K4_INSTANCE: &str = r#"
        (set-logic QF_DT)
        (declare-datatype E ((e0) (e1) (e2)))
        (declare-const v1 E)
        (declare-const v2 E)
        (declare-const v3 E)
        (declare-const v4 E)
        (declare-const v5 E)
        (assert (= v1 e0))
        (assert (or (= v2 e0) (= v2 e1)))
        (assert (or (= v3 e0) (= v3 e1) (= v3 e2)))
        (assert (or (= v4 e0) (= v4 e1) (= v4 e2)))
        (assert (or (= v5 e0) (= v5 e1) (= v5 e2)))
        (assert (distinct v1 v2))
        (assert (distinct v1 v3))
        (assert (distinct v1 v4))
        (assert (distinct v2 v3))
        (assert (distinct v2 v4))
        (assert (distinct v3 v4))
        (assert (distinct v1 v5))
    "#;

    /// PROVENANCE: every collected disequality edge maps to the exact
    /// top-level assertion that entails it, and an n-ary `distinct` maps all
    /// its pairs to the same source assertion.
    #[test]
    fn test_diseq_edge_provenance_maps_to_source_assertions() {
        let mut exec = exec_setup(
            r#"
            (set-logic QF_DT)
            (declare-datatype E ((e0) (e1)))
            (declare-const a E)
            (declare-const b E)
            (declare-const c E)
            (assert (distinct a b))
            (assert (not (= b c)))
            (assert (distinct a b c))
        "#,
        );
        let assertions = exec.ctx.assertions.clone();
        assert_eq!(assertions.len(), 3);
        let mut by_sort: HashMap<Sort, EnumDiseqEdges> = HashMap::default();
        for &a in &assertions {
            exec.collect_finite_enum_diseq_edges(a, a, &mut by_sort);
        }
        for &a in &assertions {
            exec.collect_guarded_ite_diseq_edges(a, a, &mut by_sort);
        }
        assert_eq!(by_sort.len(), 1, "one enum sort expected");
        let info = by_sort.values().next().unwrap();
        assert_eq!(info.k, 2);
        // Three distinct pairs: (a,b) from assertion 0, (b,c) from assertion 1,
        // (a,c) first recorded by assertion 2 (the n-ary distinct re-derives
        // (a,b)/(b,c) but first-wins keeps the earlier sources).
        assert_eq!(info.edges.len(), 3);
        let sources: Vec<TermId> = info.edges.values().copied().collect();
        assert!(sources.contains(&assertions[0]));
        assert!(sources.contains(&assertions[1]));
        assert!(sources.contains(&assertions[2]));
        // Every source must be one of the top-level assertions.
        for src in info.edges.values() {
            assert!(assertions.contains(src), "source must be a real assertion");
        }
    }

    /// MEMBERSHIP: `(= x c)` and `(or (= x c1) (= x c2))` chains are
    /// collected with the right source assertion and domain size; a
    /// disequality assert is NOT membership.
    #[test]
    fn test_membership_collection_sources_and_domains() {
        let exec = exec_setup(
            r#"
            (set-logic QF_DT)
            (declare-datatype E ((e0) (e1) (e2)))
            (declare-const a E)
            (declare-const b E)
            (assert (= a e0))
            (assert (or (= b e0) (= b e1)))
            (assert (distinct a b))
        "#,
        );
        let assertions = exec.ctx.assertions.clone();
        let membership = exec.collect_enum_membership_assertions(&assertions);
        assert_eq!(membership.len(), 1, "one enum sort expected");
        let per_sort = membership.values().next().unwrap();
        assert_eq!(per_sort.len(), 2, "membership for a and b only");
        let mut domains: Vec<usize> = per_sort.values().map(|e| e.domain).collect();
        domains.sort_unstable();
        assert_eq!(domains, vec![1, 2]);
        let sources: HashSet<TermId> = per_sort.values().map(|e| e.assertion).collect();
        assert!(sources.contains(&assertions[0]));
        assert!(sources.contains(&assertions[1]));
        assert!(!sources.contains(&assertions[2]));
    }

    /// FAIL-CLOSED: a core with ONE edge assertion removed must fail the
    /// in-process re-verification (no core smaller than sound is ever
    /// certified), while the full core passes it.
    #[test]
    fn test_verify_rejects_incomplete_core() {
        let mut exec = exec_setup(K4_INSTANCE);
        let assertions = exec.ctx.assertions.clone();
        // All assertions named (identity map suffices for the gate).
        let named: HashMap<TermId, String> = assertions
            .iter()
            .enumerate()
            .map(|(i, &t)| (t, format!("n{i}")))
            .collect();
        let core = exec
            .try_enum_pigeonhole_named_core(&named)
            .expect("K4 over 3-ctor enum must produce a pigeonhole core");
        // Recover sort/k/clique via a fresh collection to drive verify directly.
        let mut by_sort: HashMap<Sort, EnumDiseqEdges> = HashMap::default();
        for &a in &assertions {
            exec.collect_finite_enum_diseq_edges(a, a, &mut by_sort);
        }
        let (sort, info) = by_sort.iter().next().unwrap();
        let sort = sort.clone();
        let k = info.k;
        let membership = exec.collect_enum_membership_assertions(&assertions);
        let clique = exec
            .seed_biased_pigeonhole_clique(by_sort.get(&sort).unwrap(), membership.get(&sort))
            .expect("clique must be found");
        assert_eq!(clique.len(), k + 1);
        assert!(
            exec.verify_pigeonhole_core_entails_clique(&core, &sort, k, &clique),
            "full core must re-verify"
        );
        // Drop one EDGE assertion (a source of some collected edge) from the core.
        let edge_sources: HashSet<TermId> = by_sort
            .get(&sort)
            .unwrap()
            .edges
            .values()
            .copied()
            .collect();
        let victim = *core
            .iter()
            .find(|&&a| edge_sources.contains(&a))
            .expect("core contains edge assertions");
        let corrupted: Vec<TermId> = core.iter().copied().filter(|&a| a != victim).collect();
        assert!(
            !exec.verify_pigeonhole_core_entails_clique(&corrupted, &sort, k, &clique),
            "core missing an edge assertion must FAIL re-verification"
        );
    }

    /// FAIL-CLOSED: when any core assertion is UNNAMED, the fast path must
    /// decline (the emitted name set would under-cover the refutation under
    /// keep-only-core-named validation semantics).
    #[test]
    fn test_unnamed_core_assertion_blocks_fast_path() {
        let mut exec = exec_setup(K4_INSTANCE);
        let assertions = exec.ctx.assertions.clone();
        // Name everything EXCEPT one clique edge assert ((distinct v1 v2),
        // assertion index 5).
        let named: HashMap<TermId, String> = assertions
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != 5)
            .map(|(i, &t)| (t, format!("n{i}")))
            .collect();
        assert!(
            exec.try_enum_pigeonhole_named_core(&named).is_none(),
            "fast path must decline when a core assertion is unnamed"
        );
        // Sanity: with everything named it fires.
        let all_named: HashMap<TermId, String> = assertions
            .iter()
            .enumerate()
            .map(|(i, &t)| (t, format!("n{i}")))
            .collect();
        assert!(exec.try_enum_pigeonhole_named_core(&all_named).is_some());
    }

    /// EDGE CLOSURE: a second, distinct assertion entailing an edge whose
    /// BOTH endpoints lie in the clique vertex set must join the core
    /// (superset composition), while assertions contributing ONLY
    /// clique-external edges stay out. (A syntactic duplicate like
    /// `(not (= v1 v2))` hash-conses to the SAME TermId as
    /// `(distinct v1 v2)`, so the duplicate source here is an n-ary
    /// `distinct` that overlaps the clique edge but also mentions the
    /// non-clique vertex v5.)
    #[test]
    fn test_closure_includes_duplicate_edge_sources() {
        let input = format!("{K4_INSTANCE}\n(assert (distinct v1 v2 v5))");
        let mut exec = exec_setup(&input);
        let assertions = exec.ctx.assertions.clone();
        assert_eq!(assertions.len(), 13);
        let named: HashMap<TermId, String> = assertions
            .iter()
            .enumerate()
            .map(|(i, &t)| (t, format!("n{i}")))
            .collect();
        let core = exec
            .try_enum_pigeonhole_named_core(&named)
            .expect("core expected");
        let core_set: HashSet<TermId> = core.iter().copied().collect();
        // Both sources of the within-clique (v1,v2) edge are in the closure:
        // the original `(distinct v1 v2)` (index 5) AND the overlapping
        // `(distinct v1 v2 v5)` (index 12).
        assert!(core_set.contains(&assertions[5]), "primary edge source");
        assert!(
            core_set.contains(&assertions[12]),
            "duplicate edge source must join the closure core"
        );
        // The purely clique-external edge (v1,v5) still stays out.
        assert!(!core_set.contains(&assertions[11]));
        assert_eq!(core.len(), 12, "11 original core asserts + 1 duplicate");
    }

    /// SEED-FIRST EXHAUSTION: when the seed subgraph cannot reach the target
    /// on its own, the search must still grow the seed clique to exhaustion
    /// before completing with arbitrary vertices — NOT abandon the seed
    /// phase and greedily wander into a high-connectivity non-seed region.
    /// Graph: seeds s0..s5 form K6 with a1, a2 adjacent to all of them (the
    /// residual-2 target clique), plus a DECOY K21 of non-seeds d0..d19+s0
    /// (each d adjacent to s0 and to every other d, to nothing else). With
    /// k = 7 (target 8) both cliques qualify; the greedy-from-singleton path
    /// (the pre-lever behaviour once the reachability prune abandoned phase
    /// 1) dives into the decoy — residual 7, validator-hostile — while the
    /// exhaustive seed phase keeps all 6 membership seeds (residual 2).
    #[test]
    fn test_seed_phase_grows_to_exhaustion_not_into_decoy() {
        let s: Vec<TermId> = (0..6).map(TermId).collect();
        let a1 = TermId(6);
        let a2 = TermId(7);
        let d: Vec<TermId> = (8..28).map(TermId).collect();
        let src = TermId(99);
        let mut edges: HashMap<(TermId, TermId), TermId> = HashMap::default();
        let add = |a: TermId, b: TermId, edges: &mut HashMap<(TermId, TermId), TermId>| {
            let pair = if a.0 < b.0 { (a, b) } else { (b, a) };
            edges.insert(pair, src);
        };
        for i in 0..6 {
            for j in (i + 1)..6 {
                add(s[i], s[j], &mut edges); // K6 over the seeds
            }
            add(s[i], a1, &mut edges);
            add(s[i], a2, &mut edges);
        }
        add(a1, a2, &mut edges);
        for i in 0..20 {
            add(s[0], d[i], &mut edges); // decoy hangs off the start seed
            for j in (i + 1)..20 {
                add(d[i], d[j], &mut edges);
            }
        }
        let graph = CliqueGraph::from_edges(&edges, 4096).unwrap();
        let seed_domain: Vec<Option<usize>> = graph
            .nodes
            .iter()
            .map(|t| (t.0 < 6).then_some(t.0 as usize + 1))
            .collect();
        let k = 7;
        let mut budget = 1_000_000u64;
        let clique = graph
            .seed_first_clique(k, &seed_domain, 50, &mut budget)
            .expect("an (k+1)-clique exists");
        assert_eq!(clique.len(), k + 1);
        let members: HashSet<TermId> = graph.to_terms(&clique).into_iter().collect();
        for m in &s {
            assert!(
                members.contains(m),
                "all 6 membership seeds must stay in the clique (residual 2, \
                 not the residual-7 decoy)"
            );
        }
        assert!(members.contains(&a1) && members.contains(&a2));
    }

    /// DROP-1 ORDER: the drop-1 completion must reconsider EVERY clique
    /// member, most-unlocking drop first — not only the last few greedy
    /// picks. Graph: seeds s0..s11 form K12 (staircase domains, so the
    /// greedy adds s1 SECOND); x is adjacent to all 12 seeds; y and z are
    /// adjacent to every seed EXCEPT s1, to x, and to each other. With
    /// k = 13 (target 14) the ONLY (k+1)-clique drops s1 — an early greedy
    /// pick that a last-added-first drop order (the pre-lever behaviour,
    /// which reached only the 8 most recent members) never reconsiders.
    /// This is the vlsat3_b98 blocker shape in miniature (there the blocking
    /// seed p19 is added 20th of 80 and its drop unlocks the residual-3,
    /// validator-friendly clique).
    #[test]
    fn test_drop1_reconsiders_early_greedy_picks() {
        let s: Vec<TermId> = (0..12).map(TermId).collect(); // seeds
        let x = TermId(12);
        let y = TermId(13);
        let z = TermId(14);
        let src = TermId(99); // provenance is irrelevant at graph level
        let mut edges: HashMap<(TermId, TermId), TermId> = HashMap::default();
        let add = |a: TermId, b: TermId, edges: &mut HashMap<(TermId, TermId), TermId>| {
            let pair = if a.0 < b.0 { (a, b) } else { (b, a) };
            edges.insert(pair, src);
        };
        for i in 0..12 {
            for j in (i + 1)..12 {
                add(s[i], s[j], &mut edges); // K12 over the seeds
            }
            add(s[i], x, &mut edges); // x adjacent to every seed
            if i != 1 {
                add(s[i], y, &mut edges); // y, z skip s1
                add(s[i], z, &mut edges);
            }
        }
        add(x, y, &mut edges);
        add(x, z, &mut edges);
        add(y, z, &mut edges);
        let graph = CliqueGraph::from_edges(&edges, 4096).unwrap();
        // Staircase seed domains (narrow first) as in the Bouvier chains.
        let seed_domain: Vec<Option<usize>> = graph
            .nodes
            .iter()
            .map(|t| (t.0 < 12).then_some(t.0 as usize + 1))
            .collect();
        let k = 13;
        let mut budget = 1_000_000u64;
        let clique = graph
            .seed_first_clique(k, &seed_domain, 50, &mut budget)
            .expect("the s1-dropping 14-clique must be found");
        assert_eq!(clique.len(), k + 1);
        let members: HashSet<TermId> = graph.to_terms(&clique).into_iter().collect();
        assert!(
            !members.contains(&s[1]),
            "the blocking early greedy pick s1 must be dropped"
        );
        for &m in [x, y, z].iter().chain(s.iter().filter(|t| t.0 != 1)) {
            assert!(members.contains(&m), "member {m:?} expected");
        }
    }

    // ---- Enrichment policy (size-gated one-endpoint edges) ----

    /// Build an `EnumDiseqEdges` from `(a, b, source)` triples (ids).
    fn mk_info(k: usize, edges: &[(u32, u32, u32)]) -> EnumDiseqEdges {
        let mut info = EnumDiseqEdges::new(k);
        for &(a, b, src) in edges {
            let pair = Executor::ordered_term_pair(TermId(a), TermId(b));
            info.record(pair, TermId(src));
        }
        info
    }

    fn names_for(ids: &[u32]) -> HashMap<TermId, String> {
        ids.iter().map(|&i| (TermId(i), format!("n{i}"))).collect()
    }

    /// K4 clique (k=3) with sources 100..=105, two high-coverage outside
    /// vertices: 4 (subject, cov 3: sources 200..=202) and 6 (non-subject,
    /// cov 3: 230..=232) with a within-selected edge (4,6) (240); one
    /// low-coverage outside vertex 5 (cov 2: 210..=211) with an edge to the
    /// UNSELECTED side of the closure (220); memberships for clique member 0
    /// (300) and outside subject 4 (301).
    fn enrich_fixture() -> (EnumDiseqEdges, HashMap<TermId, EnumMembership>) {
        let info = mk_info(
            3,
            &[
                (0, 1, 100),
                (0, 2, 101),
                (0, 3, 102),
                (1, 2, 103),
                (1, 3, 104),
                (2, 3, 105),
                (0, 4, 200),
                (1, 4, 201),
                (2, 4, 202),
                (0, 5, 210),
                (1, 5, 211),
                (4, 5, 220),
                (0, 6, 230),
                (1, 6, 231),
                (2, 6, 232),
                (4, 6, 240),
            ],
        );
        let mut mem: HashMap<TermId, EnumMembership> = HashMap::default();
        mem.insert(
            TermId(0),
            EnumMembership {
                assertion: TermId(300),
                domain: 1,
            },
        );
        mem.insert(
            TermId(4),
            EnumMembership {
                assertion: TermId(301),
                domain: 2,
            },
        );
        (info, mem)
    }

    /// THRESHOLD GATING: below the threshold the assembled core is EXACTLY
    /// the pre-enrichment core (byte-identity invariant); at/above it the
    /// high-coverage one-endpoint edges AND the within-selected closure
    /// join — and ONLY those (the low-coverage vertex 5 and its edges,
    /// including the (4,5) edge into the selected set, stay out).
    #[test]
    fn test_enrichment_gated_by_threshold_and_composition() {
        let (info, mem) = enrich_fixture();
        let clique: Vec<TermId> = (0..4).map(TermId).collect();
        let named = names_for(&[
            100, 101, 102, 103, 104, 105, 200, 201, 202, 210, 211, 220, 230, 231, 232, 240, 300,
            301,
        ]);
        let base = Executor::assemble_pigeonhole_core(&info, Some(&mem), &clique, &named, 82)
            .expect("core");
        let expect_base: Vec<TermId> = [100, 101, 102, 103, 104, 105, 300, 301]
            .map(TermId)
            .to_vec();
        assert_eq!(
            base, expect_base,
            "k=3 < 82: pre-enrichment core, unchanged"
        );
        let enriched = Executor::assemble_pigeonhole_core(&info, Some(&mem), &clique, &named, 3)
            .expect("core");
        // Order: clique edges, subject vertex 4's one-endpoint edges,
        // non-subject vertex 6's, the within-selected (4,6) closure edge,
        // then memberships. Vertex 5 (cov 2 < 3/4*4) contributes NOTHING —
        // not even its (4,5) edge into the selected set.
        let expect_enriched: Vec<TermId> = [
            100, 101, 102, 103, 104, 105, 200, 201, 202, 230, 231, 232, 240, 300, 301,
        ]
        .map(TermId)
        .to_vec();
        assert_eq!(enriched, expect_enriched);
    }

    /// CLOSURE NAMEDNESS: an unnamed within-selected closure edge is
    /// skipped silently; the rest of the enrichment is unaffected.
    #[test]
    fn test_enrichment_closure_skips_unnamed_edge() {
        let (info, mem) = enrich_fixture();
        let clique: Vec<TermId> = (0..4).map(TermId).collect();
        // Everything named EXCEPT the (4,6) closure edge source 240.
        let named = names_for(&[
            100, 101, 102, 103, 104, 105, 200, 201, 202, 210, 211, 220, 230, 231, 232, 300, 301,
        ]);
        let core = Executor::assemble_pigeonhole_core(&info, Some(&mem), &clique, &named, 3)
            .expect("core");
        assert!(!core.contains(&TermId(240)), "unnamed closure edge skipped");
        assert!(core.contains(&TermId(230)) && core.contains(&TermId(202)));
        assert!(core.iter().all(|t| named.contains_key(t)));
    }

    /// UNNAMED enrichment sources are skipped silently — enrichment must
    /// never introduce an unnamed assertion (which would flip the caller's
    /// all-named fail-closed gate from emit to decline).
    #[test]
    fn test_enrichment_skips_unnamed_sources() {
        let (mut info, mem) = enrich_fixture();
        // Vertex 4 adjacent to the whole clique (add the 4th edge)…
        info.record((TermId(3), TermId(4)), TermId(203));
        let clique: Vec<TermId> = (0..4).map(TermId).collect();
        // …but source 201 is NOT named: named coverage 3 still >= 3/4 * 4.
        let named = names_for(&[100, 101, 102, 103, 104, 105, 200, 202, 203, 300, 301]);
        let core = Executor::assemble_pigeonhole_core(&info, Some(&mem), &clique, &named, 3)
            .expect("core");
        assert!(core.contains(&TermId(200)) && core.contains(&TermId(202)));
        assert!(core.contains(&TermId(203)));
        assert!(
            !core.contains(&TermId(201)),
            "unnamed enrichment source must be skipped"
        );
        assert!(
            core.iter().all(|t| named.contains_key(t)),
            "enrichment must never add an unnamed assertion"
        );
    }

    /// EDGE BUDGET: extra edges are capped at 2x the clique-edge count,
    /// taken as a deterministic rank-order prefix (TermId ascending on
    /// coverage ties). n=4: budget 12; five full-coverage outside vertices
    /// (4 edges each) -> exactly the first three (12 edges) join.
    #[test]
    fn test_enrichment_edge_budget_prefix() {
        let mut triples: Vec<(u32, u32, u32)> = vec![
            (0, 1, 100),
            (0, 2, 101),
            (0, 3, 102),
            (1, 2, 103),
            (1, 3, 104),
            (2, 3, 105),
        ];
        let mut src = 200;
        for o in 10..15 {
            for c in 0..4 {
                triples.push((c, o, src));
                src += 1;
            }
        }
        let info = mk_info(3, &triples);
        let clique: Vec<TermId> = (0..4).map(TermId).collect();
        let all_ids: Vec<u32> = triples.iter().map(|t| t.2).collect();
        let named = names_for(&all_ids);
        let core =
            Executor::assemble_pigeonhole_core(&info, None, &clique, &named, 3).expect("core");
        // 6 clique edges + 3 vertices x 4 enrichment edges.
        assert_eq!(core.len(), 6 + 12);
        for id in 200..212 {
            assert!(core.contains(&TermId(id)), "vertex 10-12 edge {id}");
        }
        for id in 212..220 {
            assert!(
                !core.contains(&TermId(id)),
                "vertex 13-14 edge {id} over budget"
            );
        }
    }

    /// SUBJECT-FIRST RANKING: an outside MEMBERSHIP SUBJECT outranks a
    /// higher-coverage non-subject (its edges appear first in the core) —
    /// the cvc5-measured shape wires the floating membership subjects in.
    #[test]
    fn test_enrichment_ranks_membership_subjects_first() {
        let triples: Vec<(u32, u32, u32)> = vec![
            (0, 1, 100),
            (0, 2, 101),
            (0, 3, 102),
            (1, 2, 103),
            (1, 3, 104),
            (2, 3, 105),
            // Non-subject vertex 10: full coverage (4 edges).
            (0, 10, 200),
            (1, 10, 201),
            (2, 10, 202),
            (3, 10, 203),
            // Subject vertex 20: coverage 3.
            (0, 20, 210),
            (1, 20, 211),
            (2, 20, 212),
        ];
        let info = mk_info(3, &triples);
        let mut mem: HashMap<TermId, EnumMembership> = HashMap::default();
        mem.insert(
            TermId(20),
            EnumMembership {
                assertion: TermId(300),
                domain: 2,
            },
        );
        let clique: Vec<TermId> = (0..4).map(TermId).collect();
        let named = names_for(&[
            100, 101, 102, 103, 104, 105, 200, 201, 202, 203, 210, 211, 212, 300,
        ]);
        let core = Executor::assemble_pigeonhole_core(&info, Some(&mem), &clique, &named, 3)
            .expect("core");
        let pos = |id: u32| core.iter().position(|&t| t == TermId(id)).unwrap();
        for s in [210, 211, 212] {
            for ns in [200, 201, 202, 203] {
                assert!(
                    pos(s) < pos(ns),
                    "subject vertex edges must precede non-subject edges"
                );
            }
        }
    }

    /// VERTEX CAP: at most `UC_ENRICH_VERTEX_CAP` (16) enrichment vertices
    /// even when the edge budget allows more. n=20 clique, 18 candidates at
    /// coverage 15 (bar: 15 >= 3/4 * 20): budget 380 admits all 18, the cap
    /// keeps the first 16 (TermId ascending).
    #[test]
    fn test_enrichment_vertex_cap() {
        let mut triples: Vec<(u32, u32, u32)> = Vec::new();
        let mut src = 1000;
        for i in 0..20u32 {
            for j in (i + 1)..20 {
                triples.push((i, j, src));
                src += 1;
            }
        }
        let mut by_vertex: Vec<(u32, Vec<u32>)> = Vec::new();
        for o in 0..18u32 {
            let mut ids = Vec::new();
            for c in 0..15u32 {
                triples.push((c, 100 + o, src));
                ids.push(src);
                src += 1;
            }
            by_vertex.push((100 + o, ids));
        }
        let info = mk_info(19, &triples);
        let clique: Vec<TermId> = (0..20).map(TermId).collect();
        let all_ids: Vec<u32> = triples.iter().map(|t| t.2).collect();
        let named = names_for(&all_ids);
        let core =
            Executor::assemble_pigeonhole_core(&info, None, &clique, &named, 19).expect("core");
        assert_eq!(core.len(), 190 + 16 * 15, "16 vertices x 15 edges enrich");
        for (o, ids) in &by_vertex {
            let included = ids.iter().all(|&i| core.contains(&TermId(i)));
            let excluded = ids.iter().all(|&i| !core.contains(&TermId(i)));
            if *o < 116 {
                assert!(included, "vertex {o} within the cap");
            } else {
                assert!(excluded, "vertex {o} beyond the 16-vertex cap");
            }
        }
    }

    /// DEFAULT THRESHOLD: 43 without the env override — exactly the
    /// dual-validated enrichment set: e97 (k=43), b98 (k=81), b79 (k=83)
    /// and b89 (k=86) enrich; e91 (k=24) and every smaller validated probe
    /// instance (k <= 20) stay byte-identical on the un-enriched path.
    #[test]
    fn test_default_enrich_threshold_covers_validated_set() {
        if std::env::var_os("AY_UC_ENRICH_K").is_none() {
            let t = Executor::uc_enrich_k_threshold();
            assert_eq!(t, 43);
            for k in [43, 81, 83, 86] {
                assert!(k >= t, "validated-enriched instance k={k} must enrich");
            }
            for k in [12, 16, 19, 20, 24] {
                assert!(
                    k < t,
                    "below-threshold instance k={k} must stay un-enriched"
                );
            }
        }
    }

    /// END-TO-END at competition scale: a k=82 enum sort with an 83-clique
    /// and one outside vertex at 90 % coverage emits, through the full named
    /// fast path (collect -> clique -> assemble -> named gate -> re-verify),
    /// the clique core PLUS the outside vertex's one-endpoint edges (default
    /// threshold 82 <= k, no env needed).
    #[test]
    fn test_end_to_end_enriched_core_at_default_threshold() {
        let k = 82;
        let mut s = String::from("(set-logic QF_DT)\n(declare-datatype E (");
        for i in 0..k {
            s.push_str(&format!("(e{i}) "));
        }
        s.push_str("))\n");
        for i in 0..=k {
            s.push_str(&format!("(declare-const v{i} E)\n"));
        }
        s.push_str("(declare-const w E)\n");
        for i in 0..=k {
            for j in (i + 1)..=k {
                s.push_str(&format!("(assert (distinct v{i} v{j}))\n"));
            }
        }
        // w adjacent to 75 of the 83 clique vertices (90 % >= 3/4).
        for i in 0..75 {
            s.push_str(&format!("(assert (distinct v{i} w))\n"));
        }
        let mut exec = exec_setup(&s);
        let assertions = exec.ctx.assertions.clone();
        let n_clique_edges = (k + 1) * k / 2;
        assert_eq!(assertions.len(), n_clique_edges + 75);
        let named: HashMap<TermId, String> = assertions
            .iter()
            .enumerate()
            .map(|(i, &t)| (t, format!("smtcomp{}", i + 1)))
            .collect();
        let core = exec
            .try_enum_pigeonhole_named_core(&named)
            .expect("pigeonhole core at k=82");
        assert_eq!(
            core.len(),
            n_clique_edges + 75,
            "core = full clique closure + all 75 enrichment edges"
        );
    }

    /// SEED BIAS: the K4 core consists of exactly the 6 clique-edge asserts
    /// plus the sort's membership asserts (the validator-friendly domain
    /// chains, all of them — the cvc5-validated b98 seed-core shape). The
    /// irrelevant edge (v1,v5) stays out.
    #[test]
    fn test_core_is_clique_edges_plus_membership() {
        let mut exec = exec_setup(K4_INSTANCE);
        let assertions = exec.ctx.assertions.clone();
        let named: HashMap<TermId, String> = assertions
            .iter()
            .enumerate()
            .map(|(i, &t)| (t, format!("n{i}")))
            .collect();
        let core = exec
            .try_enum_pigeonhole_named_core(&named)
            .expect("core expected");
        let core_set: HashSet<TermId> = core.iter().copied().collect();
        // Assertions 0..=4 are memberships of v1..v5; 5..=10 the K4 edges;
        // 11 the irrelevant (v1,v5) edge.
        for idx in [0usize, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] {
            assert!(
                core_set.contains(&assertions[idx]),
                "core must contain assertion {idx}"
            );
        }
        assert!(
            !core_set.contains(&assertions[11]),
            "core must NOT contain the irrelevant clique-external edge"
        );
        assert_eq!(core.len(), 11);
    }
}
