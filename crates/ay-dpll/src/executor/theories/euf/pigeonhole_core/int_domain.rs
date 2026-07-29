// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Named unsat-core extraction for INT FINITE-DOMAIN pigeonhole refutations
//! (#uc-qfidl).
//!
//! Sibling of the parent module's datatype pass. Graph-coloring instances are
//! shipped in two dialects: the QF_DT dialect (an all-nullary datatype sort
//! supplies the palette, handled by `try_enum_pigeonhole_named_core`) and the
//! QF_IDL dialect (SMT-LIB 20210312-Bouvier `vlsat3_c*`), where the variables
//! are plain `Int`s and the palette is spelled out per variable as
//!   `(assert (or (= u7 0) (= u7 1) ... (= u7 12)))`
//! with the coloring constraints as `(assert (distinct u32 u54))`. The
//! datatype pass is gated on `pigeonhole_datatype_cardinality`, so it never
//! fires there and AY times out on the whole family (100 of the 1069
//! Unsat-Core QF_LinearIntArith selections; most of the 2025 field times out
//! on them too).
//!
//! The refutation is the same pigeonhole: if a set `S` of variables is
//! pairwise distinct by ASSERTED constraints and `|S|` exceeds the size of
//! the UNION of their asserted domains, no injection exists and the
//! assertions are UNSAT. The core is then `C(|S|,2)` disequality source
//! assertions plus the `|S|` domain assertions — 105 of 1463 asserts on
//! `vlsat3_c00`.
//!
//! CANDIDATE-`D` RESTRICTION (what makes the parent's `CliqueGraph` reusable
//! unchanged): the datatype architecture keys ONE cardinality `k` per sort,
//! but the Int bound `|U_{v in S} D(v)|` is per-clique, and the parent's
//! clique completion is free to pick vertices with no domain at all (for Int
//! that is an INFINITE domain, which would void the certificate). Both
//! problems dissolve by fixing a candidate value set `D` first and building
//! the graph over `V(D) = { v : D(v) subset-of D }` only: then every graph
//! vertex is domain-constrained, the residual is structurally 0, and ANY
//! clique of size `> |D|` is an exact pigeonhole certificate with `k = |D|`.
//! Candidates are the deduplicated per-variable domains plus their union,
//! tried in ASCENDING size (smallest `k` => smallest core => best reduction).
//! This is heuristically, not logically, complete — incompleteness only costs
//! points, never correctness.
//!
//! FAIL-CLOSED: a core is returned ONLY after in-process re-verification that
//! the core assertions ALONE re-derive (a) a domain assertion for every
//! clique member, (b) a strictly-too-small union of those domains, and (c)
//! every within-clique disequality edge. Nothing the clique heuristic
//! computed is carried into the verdict. Any mismatch falls back to the
//! generic redirect path. The pass can only ever turn unknown/timeout into
//! unsat: it never returns SAT, takes `&self` so it cannot perturb the
//! fall-through state, and runs only under `produce-unsat-cores` with named
//! assertions.

use super::super::super::super::Executor;
use super::{CliqueGraph, EnumDiseqEdges, EnumMembership};
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Constant, Sort, TermData, TermId};
use num_bigint::BigInt;
use std::collections::BTreeSet;

/// SAT-side twin (#sq-qfufidl-sat). A CHILD module, not a `pigeonhole_core`
/// sibling: `int_domain_literal` and `INT_DOMAIN_MAX_VALUES` are private items
/// of this module, and Rust scopes those to it AND its descendants — a sibling
/// would force widening each of them to `pub(super)`. Nothing else here
/// changes; the coloring pass calls this module's primitives and edits none of
/// its unsat-load-bearing collectors.
mod coloring;

/// Largest accepted `(or ...)` arity / domain size. A domain assertion is
/// self-limiting (its size is the disjunction's arity), so this only bounds
/// pathological machine-generated input.
const INT_DOMAIN_MAX_VALUES: usize = 4096;

/// Term-visit budget shared by the two collectors of one attempt. Guards deep
/// `and` trees; exhaustion is a sound skip (a truncated collection can only
/// MISS domains/edges, never fabricate them, and the fail-closed
/// re-verification runs on its own fresh budget anyway).
/// Below this many assertions the pass stands down entirely.
///
/// Set by measurement. The pass pre-empts the generic minimizer, and on SMALL
/// instances the generic minimizer wins: on a randomized corpus of small unsat
/// instances carrying both domain chains and cliques, unconditional adoption
/// made 21 cores worse against 4 better (aggregate +11.6%) — one shrank to 2
/// assertions generically against 6 here. Every one of those was 11-17
/// assertions, decided fast by both arms.
///
/// The wins are the opposite regime: 599-19,420 assertions, where AY times out
/// and the generic core does not exist at all. A size floor separates the two
/// cleanly where a ratio does not — an 8x ratio also declined 10 real wins
/// worth 7,429 reduction in the 14-29% band (e.g. vlsat3_c56, a verified
/// 190/1026 core, where BOTH arms otherwise return unknown).
const MIN_ASSERTS_FOR_PIGEONHOLE: usize = 256;

/// A core larger than this fraction of the assertion set is not worth adopting
/// even on a big instance: it cannot beat the generic path by enough to matter,
/// and the degenerate cliques (k in the hundreds, core = C(k,2)) reduce nothing.
const WORTH_IT_CORE_RATIO: usize = 2;

const INT_DOMAIN_SCAN_NODE_BUDGET: u64 = 2_000_000;

/// Maximum number of candidate value sets `D` examined.
const INT_PIGEONHOLE_MAX_LEVELS: usize = 4096;

/// Maximum number of FULL clique searches run across all candidates. Infeasible
/// candidates are rejected by the O(V+E) peel below and are not counted, so
/// this bounds the only super-linear work.
const INT_PIGEONHOLE_MAX_SEARCHES: usize = 8;

/// The asserted finite domain of one `Int` term: the assertion that entails it
/// and the exact set of integers it admits.
struct IntDomain {
    assertion: TermId,
    values: BTreeSet<BigInt>,
}

impl Executor {
    /// Attempt the Int finite-domain pigeonhole NAMED-CORE fast path. Returns
    /// the core assertion TermIds (clique-edge source assertions + the clique
    /// members' domain assertions) iff a re-verified pigeonhole certificate
    /// exists AND every core assertion is named. On ANY doubt returns `None`
    /// (sound skip: the caller proceeds with the generic named->assumptions
    /// redirect).
    pub(in crate::executor) fn try_int_domain_pigeonhole_named_core(
        &self,
        named: &HashMap<TermId, String>,
    ) -> Option<Vec<TermId>> {
        self.try_int_domain_pigeonhole_named_core_gated(named, true)
    }

    /// PLAIN-PATH twin: does an Int finite-domain pigeonhole certificate prove
    /// this conjunction UNSAT?
    ///
    /// The named-core entry above runs only under `produce-unsat-cores`, so
    /// outside that mode the very same certificate was unreachable and AY timed
    /// out on instances it can settle in milliseconds (measured on
    /// vlsat3_c00: plain `timeout` at 30s, UC-prepped `unsat` in 0.01s, same
    /// binary). This is the sibling of `add_finite_enum_pigeonhole_conflict`,
    /// which does exactly this for DATATYPE enums.
    ///
    /// Both WORTH-IT gates are deliberately OFF here: they exist to protect the
    /// generic minimizer's smaller CORES, and on this path there is no core to
    /// score — a certificate is an ANSWER where there was a timeout, which is
    /// never a loss. Gate 2 still runs, so soundness is unchanged.
    pub(in crate::executor) fn int_domain_pigeonhole_proves_unsat(&self) -> bool {
        self.int_domain_pigeonhole_core_inner(None, false).is_some()
    }

    /// Seam for unit tests. The two WORTH-IT gates (size floor, core ratio) are
    /// SCORING heuristics, not part of the certificate, and no hand-written
    /// fixture can clear them — so tests that exercise the certificate
    /// machinery itself pass `apply_worth_gates = false`. A parameter rather
    /// than an env override keeps the knob out of the shipped path and avoids
    /// cross-test races on process-global state. Soundness does not depend on
    /// it: gate 2 runs either way.
    pub(in crate::executor) fn try_int_domain_pigeonhole_named_core_gated(
        &self,
        named: &HashMap<TermId, String>,
        apply_worth_gates: bool,
    ) -> Option<Vec<TermId>> {
        self.int_domain_pigeonhole_core_inner(Some(named), apply_worth_gates)
    }

    /// `named = None` means the caller only wants the VERDICT, not a core, so
    /// the naming gate does not apply (there is no core to print).
    fn int_domain_pigeonhole_core_inner(
        &self,
        named: Option<&HashMap<TermId, String>>,
        apply_worth_gates: bool,
    ) -> Option<Vec<TermId>> {
        // AY convention: default ON, `=0` opts out (a flag-gated-off fast
        // path is not a fix; the escape hatch is for A/B measurement).
        if std::env::var_os("AY_INT_PIGEONHOLE").is_some_and(|v| v == "0") {
            return None;
        }
        let debug = std::env::var_os("AY_DEBUG_PIGEONHOLE").is_some();
        if named.is_some_and(|n| n.is_empty()) {
            return None;
        }
        // SIZE FLOOR: stand down on small instances, where the generic
        // minimizer reliably returns a SMALLER core than a clique certificate
        // and adopting ours is a measured net loss. See the constant.
        if apply_worth_gates && self.ctx.assertions.len() < MIN_ASSERTS_FOR_PIGEONHOLE {
            if debug {
                eprintln!(
                    "c int-pigeonhole-debug decline=too-small asserts={}",
                    self.ctx.assertions.len()
                );
            }
            return None;
        }

        let mut scan_budget = INT_DOMAIN_SCAN_NODE_BUDGET;
        let assertions = self.ctx.assertions.clone();
        let dom = self.collect_int_domains(&assertions, &mut scan_budget);
        // Cheap bail: a non-coloring instance pays one linear top-level scan
        // (the `or` arm aborts on the FIRST non-domain disjunct) and stops here.
        if dom.len() < 2 {
            if debug {
                eprintln!("c int-pigeonhole-debug decline=no-domains");
            }
            return None;
        }
        // Edges are recorded ONLY between two domain-constrained endpoints:
        // that single filter is what guarantees every graph vertex carries a
        // finite domain, hence that every clique is a valid certificate.
        let info = self.collect_int_diseq_edges(&assertions, &dom, &mut scan_budget);
        if info.edges.is_empty() {
            if debug {
                eprintln!("c int-pigeonhole-debug decline=no-edges");
            }
            return None;
        }
        if scan_budget == 0 {
            if debug {
                eprintln!("c int-pigeonhole-debug decline=budget-exhausted");
            }
            return None;
        }

        // Deterministic vertex order (hash iteration order must never move a
        // core), then compact u32 value ids: the candidate subset test and the
        // peel run millions of times and a BigInt comparison per (vertex,
        // candidate) pair would dominate the whole pass.
        let mut vertices: Vec<TermId> = dom.keys().copied().collect();
        vertices.sort_by_key(|t| t.0);
        let mut value_id: HashMap<BigInt, u32> = HashMap::default();
        let mut dom_ids: Vec<Vec<u32>> = Vec::with_capacity(vertices.len());
        for v in &vertices {
            let d = &dom[v];
            let mut ids: Vec<u32> = Vec::with_capacity(d.values.len());
            for value in &d.values {
                let next = u32::try_from(value_id.len()).ok()?;
                ids.push(*value_id.entry(value.clone()).or_insert(next));
            }
            ids.sort_unstable();
            dom_ids.push(ids);
        }
        let n_values = value_id.len();
        let vindex: HashMap<TermId, usize> =
            vertices.iter().enumerate().map(|(i, &t)| (t, i)).collect();
        let mut adj: Vec<Vec<u32>> = vec![Vec::new(); vertices.len()];
        for &(a, b) in info.edges.keys() {
            // Both endpoints are `dom` keys by construction of the collector.
            let (ia, ib) = (vindex[&a], vindex[&b]);
            adj[ia].push(u32::try_from(ib).ok()?);
            adj[ib].push(u32::try_from(ia).ok()?);
        }

        // Candidate value sets: every distinct per-variable domain, plus the
        // union of all of them (= the whole id universe, by construction of
        // `value_id`). Ascending by size, lexicographic tie-break: the first
        // success is the smallest `k` we can certify, i.e. the smallest core.
        let mut candidates: Vec<Vec<u32>> = Vec::new();
        let mut seen_candidates: HashSet<Vec<u32>> = HashSet::default();
        for ids in &dom_ids {
            if seen_candidates.insert(ids.clone()) {
                candidates.push(ids.clone());
            }
        }
        let universe: Vec<u32> = (0..u32::try_from(n_values).ok()?).collect();
        if seen_candidates.insert(universe.clone()) {
            candidates.push(universe);
        }
        candidates.sort_by(|a, b| a.len().cmp(&b.len()).then_with(|| a.cmp(b)));
        candidates.truncate(INT_PIGEONHOLE_MAX_LEVELS);
        if debug {
            eprintln!(
                "c int-pigeonhole-debug vars={} edges={} values={} candidates={}",
                vertices.len(),
                info.edges.len(),
                n_values,
                candidates.len()
            );
        }

        // ONE work budget threaded across every candidate, so the total cost is
        // bounded regardless of how many candidates there are.
        let mut work_budget = Self::FINITE_ENUM_PIGEONHOLE_WORK_BUDGET;
        let mut searches = 0usize;
        let mut in_candidate = vec![false; n_values];
        for candidate in &candidates {
            if searches >= INT_PIGEONHOLE_MAX_SEARCHES || work_budget == 0 {
                break;
            }
            if self.solve_deadline.expired() {
                if debug {
                    eprintln!("c int-pigeonhole-debug decline=deadline");
                }
                return None;
            }
            let k = candidate.len();
            in_candidate.iter_mut().for_each(|b| *b = false);
            for &id in candidate {
                in_candidate[id as usize] = true;
            }
            // V(D): the vertices whose whole domain fits inside the candidate.
            let mut alive: Vec<bool> = dom_ids
                .iter()
                .map(|ids| ids.iter().all(|&i| in_candidate[i as usize]))
                .collect();
            let mut n_alive = alive.iter().filter(|&&a| a).count();
            work_budget = work_budget.saturating_sub(vertices.len() as u64);
            if n_alive <= k {
                continue;
            }
            // k-core peel: every member of a `(k+1)`-clique has `k` neighbours
            // INSIDE it, so a vertex of induced degree `< k` cannot belong to
            // one. Dropping it is EXACT (removes no certificate) and makes an
            // infeasible candidate cost O(V+E) instead of a clique search.
            work_budget =
                work_budget.saturating_sub((vertices.len() + 2 * info.edges.len()) as u64);
            let mut degree: Vec<usize> = vec![0; vertices.len()];
            let mut queue: Vec<usize> = Vec::new();
            for i in 0..vertices.len() {
                if !alive[i] {
                    continue;
                }
                degree[i] = adj[i].iter().filter(|&&j| alive[j as usize]).count();
                if degree[i] < k {
                    queue.push(i);
                }
            }
            while let Some(i) = queue.pop() {
                if !alive[i] {
                    continue; // already peeled (a vertex can be queued twice)
                }
                alive[i] = false;
                n_alive -= 1;
                for &j in &adj[i] {
                    let j = j as usize;
                    if alive[j] {
                        degree[j] -= 1;
                        if degree[j] < k {
                            queue.push(j);
                        }
                    }
                }
            }
            if n_alive <= k {
                continue;
            }

            searches += 1;
            // Restrict the edge set to the surviving vertices and give the
            // parent's clique machinery the per-candidate cardinality `k = |D|`.
            let mut edges_d: HashMap<(TermId, TermId), TermId> = HashMap::default();
            for (&(a, b), &src) in &info.edges {
                if alive[vindex[&a]] && alive[vindex[&b]] {
                    edges_d.insert((a, b), src);
                }
            }
            let mut extras_d: HashMap<(TermId, TermId), Vec<TermId>> = HashMap::default();
            for (&(a, b), extras) in &info.extra_sources {
                if alive[vindex[&a]] && alive[vindex[&b]] {
                    extras_d.insert((a, b), extras.clone());
                }
            }
            work_budget = work_budget.saturating_sub(info.edges.len() as u64);
            let info_d = EnumDiseqEdges {
                k,
                edges: edges_d,
                extra_sources: extras_d,
            };
            let Some(graph) =
                CliqueGraph::from_edges(&info_d.edges, Self::FINITE_ENUM_PIGEONHOLE_MAX_NODES)
            else {
                continue; // above the node cap: sound skip
            };
            if graph.n() <= k {
                continue;
            }
            // EVERY vertex is a seed (its domain is a subset of the candidate),
            // so the parent's residual-minimising phases can only ever pick
            // domain-constrained vertices. The narrower-domain tie-break in
            // `complete_greedy` reproduces the measured-good "smallest domain,
            // then highest degree" coloring heuristic for free.
            let seed_domain: Vec<Option<usize>> = graph
                .nodes
                .iter()
                .map(|t| Some(dom[t].values.len()))
                .collect();
            let Some(found) = graph.seed_first_clique(
                k,
                &seed_domain,
                Self::FINITE_ENUM_PIGEONHOLE_GREEDY_RESTARTS,
                &mut work_budget,
            ) else {
                if debug {
                    eprintln!("c int-pigeonhole-debug k={k} nodes={} no-clique", graph.n());
                }
                continue;
            };
            let improved = graph.swap_improve(found, &seed_domain, &mut work_budget);
            let clique = graph.to_terms(&improved);

            // Domain assertions of the CLIQUE only. Every other `V(D)` member's
            // domain assertion would be sound (a superset core stays unsat) but
            // is pure score loss: 105 names instead of 147 on vlsat3_c00.
            let mem_clique: HashMap<TermId, EnumMembership> = clique
                .iter()
                .map(|&v| {
                    (
                        v,
                        EnumMembership {
                            assertion: dom[&v].assertion,
                            domain: dom[&v].values.len(),
                        },
                    )
                })
                .collect();
            // `enrich_pigeonhole_core` is the only consumer of `named`, and it
            // skips unnamed sources silently, so the verdict-only caller passes
            // an empty map and simply gets no enrichment.
            let no_names: HashMap<TermId, String> = HashMap::default();
            let Some(core) = Self::assemble_pigeonhole_core(
                &info_d,
                Some(&mem_clique),
                &clique,
                named.unwrap_or(&no_names),
                Self::int_pigeonhole_enrich_k_threshold(),
            ) else {
                if debug {
                    eprintln!("c int-pigeonhole-debug decline=assemble-failed");
                }
                continue;
            };
            // FAIL-CLOSED gate 1: every core assertion must be named. Not mere
            // conservatism — the consumer keeps only core-NAMED assertions when
            // it rebuilds the reduced benchmark, so an unnamed core member would
            // silently vanish and the reduced file would not be unsat.
            if named.is_some_and(|n| !core.iter().all(|a| n.contains_key(a))) {
                if debug {
                    eprintln!("c int-pigeonhole-debug decline=unnamed-core-assertion");
                }
                continue;
            }
            // FAIL-CLOSED gate 2: the core assertions ALONE must re-derive the
            // whole certificate. This is the ONLY certificate — the fast path
            // bypasses the generic assumption-core certification — so it is
            // deliberately stronger than the datatype twin's. A failed
            // re-verification is a SOUND skip; deliberately no debug_assert
            // here, the fail-closed branch must stay a silent skip in every
            // build profile (U4 review finding F3).
            if !self.verify_int_pigeonhole_core(&core, &clique) {
                if debug {
                    eprintln!("c int-pigeonhole-debug decline=verify-failed");
                }
                continue;
            }
            // WORTH-IT gate: a valid certificate is not automatically a WIN.
            // This fast path pre-empts the generic minimizer, which on
            // instances AY already decides quickly often returns a SMALLER
            // core than the clique does — and UnsatCore scores
            // `asserts - core_size`, so adopting a bigger valid core is a
            // measurable LOSS. Measured on a 200-instance randomized corpus of
            // small unsat instances carrying both domain chains and cliques:
            // unconditional adoption made 39 cores worse against 6 better,
            // aggregate core +21% (362 -> 437). One case shrank to a 2-assert
            // core generically and a 10-assert core here.
            //
            // So only pre-empt when the certificate is a LANDSLIDE. The target
            // family clears this by an order of magnitude (vlsat3_c00 is
            // 105/1463 = 7%), while the mixed shapes that motivated the gate
            // (10 of 12) correctly decline and keep today's behaviour. This
            // also keeps the pass off QF_Datatypes instances where the
            // datatype twin declined: a big Int core there can no longer
            // displace the generic one on a BANKED division.
            if apply_worth_gates
                && core.len().saturating_mul(WORTH_IT_CORE_RATIO) > assertions.len()
            {
                if debug {
                    eprintln!(
                        "c int-pigeonhole-debug decline=not-worth-it core={} of {}",
                        core.len(),
                        assertions.len()
                    );
                }
                continue;
            }
            if debug {
                eprintln!(
                    "c int-pigeonhole-debug k={k} clique={} core={} of {}",
                    clique.len(),
                    core.len(),
                    assertions.len()
                );
            }
            return Some(core);
        }
        if debug {
            eprintln!("c int-pigeonhole-debug decline=no-candidate searches={searches}");
        }
        None
    }

    /// Effective enrichment gate for Int cliques. DEFAULT OFF (`usize::MAX`):
    /// `info_d.k = |D|` routinely exceeds the datatype default of 43 on this
    /// family, so leaving it implicit would silently enable an UNMEASURED core
    /// shape. The override exists so a threshold can later be measured through
    /// exactly this knob (the methodology that set the datatype default). If it
    /// is ever turned on, the Int version must ALSO core the domain assertions
    /// of the enrichment-selected outside vertices, or those vertices reach the
    /// reduced benchmark as unbounded Ints.
    fn int_pigeonhole_enrich_k_threshold() -> usize {
        std::env::var("AY_INT_PIGEONHOLE_ENRICH_K")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(usize::MAX)
    }

    /// FAIL-CLOSED certificate check. Re-derives domains and disequality edges
    /// from the CORE ASSERTIONS ALONE (never from the search state) and checks
    /// the three facts the pigeonhole argument needs:
    ///   (i)   every clique member has a domain assertion inside the core,
    ///   (ii)  the union of those re-derived domains is strictly smaller than
    ///         the clique, and
    ///   (iii) every within-clique pair re-derives as an asserted disequality.
    /// Under (i)-(iii) any model of the core would inject `|S|` variables into
    /// `< |S|` values, so the core is unsatisfiable — and an unsatisfiable
    /// subset makes the whole assertion set unsatisfiable, whatever else it
    /// contains. Every heuristic above could be arbitrarily buggy and the worst
    /// outcome here is `false`.
    fn verify_int_pigeonhole_core(&self, core: &[TermId], clique: &[TermId]) -> bool {
        if clique.len() < 2 {
            return false;
        }
        let mut seen: HashSet<TermId> = HashSet::default();
        for &v in clique {
            if !seen.insert(v) {
                return false; // a repeated vertex would fake the cardinality
            }
        }
        let mut budget = INT_DOMAIN_SCAN_NODE_BUDGET;
        let dom2 = self.collect_int_domains(core, &mut budget);
        let edges2 = self.collect_int_diseq_edges(core, &dom2, &mut budget);
        if budget == 0 {
            return false; // truncated re-derivation: fail closed
        }
        let core_set: HashSet<TermId> = core.iter().copied().collect();
        let mut union: BTreeSet<BigInt> = BTreeSet::new();
        for &v in clique {
            let Some(d) = dom2.get(&v) else {
                return false;
            };
            // Belt and braces: `dom2` was collected from `core`, so this holds
            // by construction — but the certificate must not depend on that.
            if !core_set.contains(&d.assertion) {
                return false;
            }
            union.extend(d.values.iter().cloned());
            // The union only grows, so failing here is final; it also bounds
            // the set to `< |S|` elements.
            if union.len() >= clique.len() {
                return false;
            }
        }
        for i in 0..clique.len() {
            for j in (i + 1)..clique.len() {
                let pair = Self::ordered_term_pair(clique[i], clique[j]);
                if !edges2.edges.contains_key(&pair) {
                    return false;
                }
            }
        }
        true
    }

    /// Collect the asserted finite `Int` domains, keeping the NARROWEST
    /// assertion per subject term.
    fn collect_int_domains(
        &self,
        assertions: &[TermId],
        budget: &mut u64,
    ) -> HashMap<TermId, IntDomain> {
        let mut out: HashMap<TermId, IntDomain> = HashMap::default();
        for &assertion in assertions {
            self.collect_int_domains_in(assertion, assertion, &mut out, budget);
        }
        out
    }

    /// Walk `term` collecting UNCONDITIONAL finite-domain constraints on `Int`
    /// terms. Recurses only through top-level `and` conjuncts: a domain
    /// constraint buried under `or`/`ite`/`=>`/`not` is not unconditional and
    /// using it would over-narrow a domain, i.e. fabricate a pigeonhole =>
    /// wrong-unsat. `source` is the TOP-LEVEL assertion, carried as provenance
    /// so the core can name it.
    fn collect_int_domains_in(
        &self,
        term: TermId,
        source: TermId,
        out: &mut HashMap<TermId, IntDomain>,
        budget: &mut u64,
    ) {
        if *budget == 0 {
            return; // sound skip: a missing domain only weakens the search
        }
        *budget -= 1;
        match self.ctx.terms.get(term) {
            TermData::App(sym, args) if sym.name() == "and" => {
                let args = args.clone();
                for arg in args {
                    self.collect_int_domains_in(arg, source, out, budget);
                }
            }
            // `(or (= x c1) ... (= x cm))`: the domain staircase. EVERY
            // disjunct must be a bare `(= x const)` literal over the SAME
            // subject — a nested `or`, a second subject or any other shape
            // aborts the whole assertion (it then contributes nothing, the
            // conservative direction).
            TermData::App(sym, args)
                if sym.name() == "or"
                    && !args.is_empty()
                    && args.len() <= INT_DOMAIN_MAX_VALUES =>
            {
                let args = args.clone();
                let mut subject: Option<TermId> = None;
                let mut values: BTreeSet<BigInt> = BTreeSet::new();
                for &disjunct in &args {
                    let Some((x, c)) = self.int_domain_literal(disjunct) else {
                        return;
                    };
                    match subject {
                        None => subject = Some(x),
                        Some(s) if s == x => {}
                        _ => return, // mixed subjects: not a domain chain
                    }
                    values.insert(c);
                }
                if let Some(x) = subject {
                    Self::record_int_domain(out, x, source, values);
                }
            }
            // `(= x c)`: a singleton domain.
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                if let Some((x, c)) = self.int_domain_literal(term) {
                    let mut values = BTreeSet::new();
                    values.insert(c);
                    Self::record_int_domain(out, x, source, values);
                }
            }
            // Unrecognised assertions are IGNORED, never a bail: one stray
            // assert must not disable the pass for the whole file (they simply
            // never enter the core, and extra assertions can only remove
            // models, never rescue an already-contradictory subset).
            _ => {}
        }
    }

    /// `(= x c)` (either operand order — `mk_eq` does not normalise argument
    /// order) with `c` an integer constant and `x` a non-constant `Int` term.
    ///
    /// The `Sort::Int` check is load-bearing: the same syntax over `Real` (or a
    /// mixed arithmetic term) does NOT denote a finite domain.
    fn int_domain_literal(&self, term: TermId) -> Option<(TermId, BigInt)> {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }
        let (a, b) = (args[0], args[1]);
        let int_const = |t: TermId| match self.ctx.terms.get(t) {
            TermData::Const(Constant::Int(n)) => Some(n.clone()),
            _ => None,
        };
        let (x, c) = match (int_const(a), int_const(b)) {
            (None, Some(c)) => (a, c),
            (Some(c), None) => (b, c),
            _ => return None, // both or neither constant: no subject
        };
        if matches!(self.ctx.terms.get(x), TermData::Const(_)) {
            return None;
        }
        if *self.ctx.terms.sort(x) != Sort::Int {
            return None;
        }
        Some((x, c))
    }

    /// Keep the entry with STRICTLY FEWER values; ties keep the first in
    /// assertion order (deterministic). Whichever assertion is kept is by
    /// itself a valid unconditional upper bound on the subject's value set, so
    /// a wider choice is only an OVER-approximation — and a pigeonhole over
    /// over-approximated domains implies the same pigeonhole over the true
    /// ones. Narrowest is a score optimisation, never a correctness
    /// requirement.
    fn record_int_domain(
        out: &mut HashMap<TermId, IntDomain>,
        subject: TermId,
        source: TermId,
        values: BTreeSet<BigInt>,
    ) {
        match out.get(&subject) {
            Some(existing) if existing.values.len() <= values.len() => {}
            _ => {
                out.insert(
                    subject,
                    IntDomain {
                        assertion: source,
                        values,
                    },
                );
            }
        }
    }

    /// Collect UNCONDITIONAL disequality edges between two DOMAIN-CONSTRAINED
    /// `Int` terms, with per-edge source-assertion provenance. The
    /// both-endpoints-in-`dom` filter is the soundness keystone of the pass:
    /// it makes every graph vertex finite-domained, so a clique can never
    /// include a vertex whose (infinite) domain would void the certificate.
    ///
    /// `k` is a per-CANDIDATE quantity here, unlike the datatype twin's
    /// per-sort cardinality, so the collector stores a placeholder 0 and each
    /// candidate rebuilds its own `EnumDiseqEdges` with `k = |D|`.
    fn collect_int_diseq_edges(
        &self,
        assertions: &[TermId],
        dom: &HashMap<TermId, IntDomain>,
        budget: &mut u64,
    ) -> EnumDiseqEdges {
        let mut out = EnumDiseqEdges::new(0);
        for &assertion in assertions {
            self.collect_int_diseq_edges_in(assertion, assertion, dom, &mut out, budget);
        }
        out
    }

    /// Recurses only through top-level `and` conjuncts — a disequality under
    /// `or`/`ite`/`=>`/`not` is not unconditional and would fabricate a false
    /// clique (the governing rule of the datatype collector).
    fn collect_int_diseq_edges_in(
        &self,
        term: TermId,
        source: TermId,
        dom: &HashMap<TermId, IntDomain>,
        out: &mut EnumDiseqEdges,
        budget: &mut u64,
    ) {
        if *budget == 0 {
            return; // sound skip: a missing edge only weakens the search
        }
        *budget -= 1;
        match self.ctx.terms.get(term) {
            // Also the n-ary-`distinct` arm in practice: `mk_distinct` expands
            // `(distinct a b c ...)` into an `and` of pairwise `(not (= _ _))`.
            TermData::App(sym, args) if sym.name() == "and" => {
                let args = args.clone();
                for arg in args {
                    self.collect_int_diseq_edges_in(arg, source, dom, out, budget);
                }
            }
            // Kept for robustness (an internally built n-ary distinct could
            // still reach here); on this family every edge arrives as `Not(=)`
            // because `mk_distinct` normalises the BINARY case to `Not(Eq)`.
            TermData::App(sym, args) if sym.name() == "distinct" && args.len() >= 2 => {
                let args = args.clone();
                for i in 0..args.len() {
                    for j in (i + 1)..args.len() {
                        if args[i] != args[j]
                            && dom.contains_key(&args[i])
                            && dom.contains_key(&args[j])
                        {
                            out.record(Self::ordered_term_pair(args[i], args[j]), source);
                        }
                    }
                }
            }
            // `(not (= a b))`: a single edge. This arm carries the whole
            // Bouvier family (1407 edges on vlsat3_c00).
            TermData::Not(inner) => {
                let TermData::App(sym, args) = self.ctx.terms.get(*inner) else {
                    return;
                };
                if sym.name() == "=" && args.len() == 2 && args[0] != args[1] {
                    let (lhs, rhs) = (args[0], args[1]);
                    if dom.contains_key(&lhs) && dom.contains_key(&rhs) {
                        out.record(Self::ordered_term_pair(lhs, rhs), source);
                    }
                }
                // `(not (distinct ...))` is a positive constraint, not a
                // disequality — nothing to collect.
            }
            _ => {}
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

    /// All assertions named (an identity-ish map suffices for gate 1).
    fn name_all(exec: &Executor) -> HashMap<TermId, String> {
        exec.ctx
            .assertions
            .iter()
            .enumerate()
            .map(|(i, &t)| (t, format!("n{i}")))
            .collect()
    }

    /// K4 over a 3-value Int domain plus an unrelated junk assert: the core is
    /// exactly the 6 disequalities + the 4 domain chains, and the junk assert
    /// is NOT cored (unrecognised assertions are ignored, not collected).
    const K4_INT: &str = r#"
        (set-logic QF_IDL)
        (declare-fun x0 () Int)
        (declare-fun x1 () Int)
        (declare-fun x2 () Int)
        (declare-fun x3 () Int)
        (declare-fun y () Int)
        (assert (or (= x0 0) (= x0 1) (= x0 2)))
        (assert (or (= x1 0) (= x1 1) (= x1 2)))
        (assert (or (= x2 0) (= x2 1) (= x2 2)))
        (assert (or (= x3 0) (= x3 1) (= x3 2)))
        (assert (distinct x0 x1))
        (assert (distinct x0 x2))
        (assert (distinct x0 x3))
        (assert (distinct x1 x2))
        (assert (distinct x1 x3))
        (assert (distinct x2 x3))
        (assert (> y 100))
    "#;

    #[test]
    fn test_int_pigeonhole_core_is_edges_plus_domains_without_junk() {
        let exec = exec_setup(K4_INT);
        let named = name_all(&exec);
        let core = exec
            .try_int_domain_pigeonhole_named_core_gated(&named, false)
            .expect("K4 over a 3-value Int domain must produce a pigeonhole core");
        let assertions = exec.ctx.assertions.clone();
        assert_eq!(core.len(), 10, "6 disequalities + 4 domain chains");
        let core_set: HashSet<TermId> = core.iter().copied().collect();
        for a in &assertions[0..10] {
            assert!(core_set.contains(a), "every domain/edge assert is cored");
        }
        assert!(
            !core_set.contains(&assertions[10]),
            "the unrelated `(> y 100)` assert must NOT be cored"
        );
    }

    /// 0-WRONG GUARD: the near miss. 3 pairwise-distinct variables over a
    /// 3-value domain is SAT — `|S| == |U|`, not `>` — and the pass must
    /// decline rather than emit a certificate.
    #[test]
    fn test_int_pigeonhole_declines_on_satisfiable_near_miss() {
        let exec = exec_setup(
            r#"
            (set-logic QF_IDL)
            (declare-fun x0 () Int)
            (declare-fun x1 () Int)
            (declare-fun x2 () Int)
            (assert (or (= x0 0) (= x0 1) (= x0 2)))
            (assert (or (= x1 0) (= x1 1) (= x1 2)))
            (assert (or (= x2 0) (= x2 1) (= x2 2)))
            (assert (distinct x0 x1 x2))
        "#,
        );
        let named = name_all(&exec);
        assert!(
            exec.try_int_domain_pigeonhole_named_core_gated(&named, false)
                .is_none(),
            "a SATISFIABLE 3-clique over 3 values must never be certified"
        );
    }

    /// A disequality buried under `or` is NOT unconditional: collecting it
    /// would fabricate the fourth edge of a K4 and produce a WRONG unsat on a
    /// satisfiable instance.
    #[test]
    fn test_int_pigeonhole_ignores_disequalities_under_or() {
        let exec = exec_setup(
            r#"
            (set-logic QF_IDL)
            (declare-fun x0 () Int)
            (declare-fun x1 () Int)
            (declare-fun x2 () Int)
            (declare-fun x3 () Int)
            (assert (or (= x0 0) (= x0 1) (= x0 2)))
            (assert (or (= x1 0) (= x1 1) (= x1 2)))
            (assert (or (= x2 0) (= x2 1) (= x2 2)))
            (assert (or (= x3 0) (= x3 1) (= x3 2)))
            (assert (distinct x0 x1))
            (assert (distinct x0 x2))
            (assert (distinct x1 x2))
            (assert (or (distinct x0 x3) (= x0 x3)))
            (assert (or (distinct x1 x3) (= x1 x3)))
            (assert (or (distinct x2 x3) (= x2 x3)))
        "#,
        );
        let named = name_all(&exec);
        assert!(
            exec.try_int_domain_pigeonhole_named_core_gated(&named, false)
                .is_none(),
            "disequalities under `or` must never enter the clique"
        );
    }

    /// Two domain assertions for one variable: the NARROWEST is kept, and it
    /// is the one that lands in the core (the wider one is an
    /// over-approximation and would still be sound, but costs reduction).
    #[test]
    fn test_int_pigeonhole_keeps_narrowest_domain_assertion() {
        let exec = exec_setup(
            r#"
            (set-logic QF_IDL)
            (declare-fun x0 () Int)
            (declare-fun x1 () Int)
            (declare-fun x2 () Int)
            (declare-fun x3 () Int)
            (assert (or (= x0 1) (= x0 2) (= x0 3) (= x0 4)))
            (assert (or (= x0 0) (= x0 1) (= x0 2)))
            (assert (or (= x1 0) (= x1 1) (= x1 2)))
            (assert (or (= x2 0) (= x2 1) (= x2 2)))
            (assert (or (= x3 0) (= x3 1) (= x3 2)))
            (assert (distinct x0 x1))
            (assert (distinct x0 x2))
            (assert (distinct x0 x3))
            (assert (distinct x1 x2))
            (assert (distinct x1 x3))
            (assert (distinct x2 x3))
        "#,
        );
        let named = name_all(&exec);
        let core = exec
            .try_int_domain_pigeonhole_named_core_gated(&named, false)
            .expect("K4 over 3 values must still certify");
        let assertions = exec.ctx.assertions.clone();
        let core_set: HashSet<TermId> = core.iter().copied().collect();
        assert!(
            core_set.contains(&assertions[1]),
            "the narrow 3-value chain for x0 is the one cored"
        );
        assert!(
            !core_set.contains(&assertions[0]),
            "the wider 4-value chain for x0 must not be cored"
        );
        assert_eq!(core.len(), 10);
    }

    /// FAIL-CLOSED gate 1: an UNNAMED core assertion makes the pass decline
    /// (the emitted name set would under-cover the refutation).
    #[test]
    fn test_int_pigeonhole_declines_on_unnamed_core_assertion() {
        let exec = exec_setup(K4_INT);
        let mut named = name_all(&exec);
        let victim = exec.ctx.assertions[4]; // one of the disequalities
        named.remove(&victim);
        assert!(
            exec.try_int_domain_pigeonhole_named_core_gated(&named, false)
                .is_none(),
            "an unnamed core assertion must force a decline"
        );
    }

    /// FAIL-CLOSED gate 2: a core missing one edge assertion must fail
    /// re-verification, while the full core passes it.
    #[test]
    fn test_verify_rejects_incomplete_int_core() {
        let exec = exec_setup(K4_INT);
        let named = name_all(&exec);
        let core = exec
            .try_int_domain_pigeonhole_named_core_gated(&named, false)
            .unwrap();
        let assertions = exec.ctx.assertions.clone();
        // Re-derive the clique: the 4 domain-constrained variables.
        let mut budget = INT_DOMAIN_SCAN_NODE_BUDGET;
        let dom = exec.collect_int_domains(&assertions, &mut budget);
        let mut clique: Vec<TermId> = dom.keys().copied().collect();
        clique.sort_by_key(|t| t.0);
        assert_eq!(clique.len(), 4);
        assert!(
            exec.verify_int_pigeonhole_core(&core, &clique),
            "the full core must re-verify"
        );
        for victim in &assertions[0..10] {
            let corrupted: Vec<TermId> = core.iter().copied().filter(|a| a != victim).collect();
            assert!(
                !exec.verify_int_pigeonhole_core(&corrupted, &clique),
                "a core missing any certificate assertion must FAIL re-verification"
            );
        }
    }

    /// DEFAULT-ON: the pass fires with no env var set at all (the
    /// `AY_INT_PIGEONHOLE=0` opt-out is exercised end-to-end through the
    /// binary — `std::env::set_var` is unavailable here, the crate is
    /// `#![forbid(unsafe_code)]`).
    #[test]
    fn test_int_pigeonhole_is_default_on() {
        assert!(
            std::env::var_os("AY_INT_PIGEONHOLE").is_none(),
            "test env must not pin the knob"
        );
        let exec = exec_setup(K4_INT);
        let named = name_all(&exec);
        assert!(
            exec.try_int_domain_pigeonhole_named_core_gated(&named, false)
                .is_some(),
            "the pass is DEFAULT-ON with no env set"
        );
    }

    /// Real-sorted variables with the same syntax do NOT have a finite domain
    /// (`(or (= r 0.0) ...)` is not an Int chain) — the pass must not fire.
    #[test]
    fn test_int_pigeonhole_ignores_non_int_sorts() {
        let exec = exec_setup(
            r#"
            (set-logic QF_LRA)
            (declare-fun r0 () Real)
            (declare-fun r1 () Real)
            (declare-fun r2 () Real)
            (declare-fun r3 () Real)
            (assert (or (= r0 0.0) (= r0 1.0) (= r0 2.0)))
            (assert (or (= r1 0.0) (= r1 1.0) (= r1 2.0)))
            (assert (or (= r2 0.0) (= r2 1.0) (= r2 2.0)))
            (assert (or (= r3 0.0) (= r3 1.0) (= r3 2.0)))
            (assert (distinct r0 r1))
            (assert (distinct r0 r2))
            (assert (distinct r0 r3))
            (assert (distinct r1 r2))
            (assert (distinct r1 r3))
            (assert (distinct r2 r3))
        "#,
        );
        let named = name_all(&exec);
        assert!(
            exec.try_int_domain_pigeonhole_named_core_gated(&named, false)
                .is_none(),
            "Real-sorted chains must never be treated as finite domains"
        );
    }
}
