// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT-side twin of the parent module's Int finite-domain pigeonhole
//! certificate: a DSATUR graph-COLOURING model finder (#sq-qfufidl-sat).
//!
//! The parent proves the refutation half of the SMT-LIB 20210312-Bouvier
//! `vlsat*` family (a clique bigger than the union of its asserted domains has
//! no injection). The satisfiable half of the same family is not refutable at
//! all — it needs a WITNESS, and AY had none: on the 114 vlsat instances of
//! SingleQuery/QF_Equality_LinearArith the certificate alone took AY from 7 to
//! 68 solved, and every one of the 42 remaining unknowns is `sat` in the
//! official field. Those 42 are ordinary graph colourings restricted to the
//! per-variable asserted domains — plain fail-first greedy DSATUR colours all
//! 42, the largest (`vlsat3_l02`: 200 subjects, 19,425 edges, 97.6% density,
//! 117 palette values) in a fraction of a second.
//!
//! # What this pass is NOT
//!
//! It is not a decision procedure and it never decides anything. It PROPOSES a
//! candidate model; acceptance is the strictest gate AY has (the
//! `partition_rescue` contract: full `finalize_sat_model_validation` +
//! `ConfirmedSat` from the independent compositional model checker, both
//! against the whole pre-dispatch conjunction), followed a second time by the
//! usual `emit_sat_verdict` funnel against the RESTORED user assertion set.
//! An assertion the colouring never inspected therefore has exactly two
//! fates: it evaluates true under the model (the model really does satisfy
//! it), or acceptance is blocked and the pass is a no-op. There is no third
//! outcome, and no new evaluator is written here.
//!
//! # Why the parent's collectors are not reused wholesale
//!
//! Three of their invariants are correct for refutation and INVERTED for model
//! finding, and they are unsat-load-bearing, so they are left untouched:
//!
//! 1. [`Executor::record_int_domain`] keeps the NARROWEST domain assertion
//!    per subject, arguing (correctly, for unsat) that a wider domain is an
//!    over-approximation. A model must satisfy EVERY asserted domain, so the
//!    model side needs the INTERSECTION. The parent's own shipped test
//!    `test_int_pigeonhole_keeps_narrowest_domain_assertion` is the
//!    counterexample: it keeps `{0,1,2}` over `{1,2,3,4}`, and a colouring
//!    picking `x0 = 0` falsifies the discarded assertion.
//! 2. `collect_int_diseq_edges` DROPS an edge whose endpoint carries no
//!    domain. That filter is the unsat keystone (every clique vertex must be
//!    finite-domained); for a model it silently deletes a constraint.
//! 3. "Unrecognised assertions are ignored, never a bail" is right for unsat
//!    (extra assertions only remove models) and exactly wrong for sat.
//!
//! Budget exhaustion is the same story: a truncated collection is a sound skip
//! for unsat and a MISSING CONSTRAINT for sat, so every truncation here is a
//! decline on its own fresh counter.
//!
//! Reused directly: [`Executor::int_domain_literal`] (the genuinely general
//! `(= x c)` primitive, whose `Sort::Int` check is load-bearing),
//! [`Executor::ordered_term_pair`], [`INT_DOMAIN_MAX_VALUES`], the `and`-only
//! recursion rule, and the `AY_DEBUG_PIGEONHOLE` trace flag.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Constant, TermData, TermId};
use num_bigint::BigInt;
use std::cmp::Reverse;
use std::collections::{BTreeSet, BinaryHeap};

use super::INT_DOMAIN_MAX_VALUES;
use crate::executor::model::Model;
use crate::executor::Executor;
use crate::executor_types::{SolveResult, UnknownReason};

/// Term-visit budget for the fused shape walk. The largest real instance in
/// the family (`vlsat3_l98`) carries 321,602 assertions, so this leaves ample
/// headroom while still bounding a pathological `and` tree.
const COLOR_SCAN_NODE_BUDGET: u64 = 2_000_000;

/// One counter for graph construction plus the whole DSATUR loop: adjacency
/// steps, heap pushes/pops and bitset words are all charged against it.
const COLOR_WORK_BUDGET: u64 = 50_000_000;

/// Structural caps. A shaped-but-huge input must not be able to turn a
/// heuristic into the thing that burns the deadline.
const COLOR_MAX_SUBJECTS: usize = 1_000_000;
const COLOR_MAX_EDGES: usize = 4_000_000;

/// Palette cap, shared with the domain-assertion arity cap so the two halves
/// accept exactly the same domain shapes.
const COLOR_MAX_PALETTE: usize = INT_DOMAIN_MAX_VALUES;

/// Cap on emitted function-table rows. `format_function_body` renders a table
/// as a nested `ite` chain one level per row, and a 50k-deep s-expression can
/// stack-overflow a recursive-descent model validator — an invalid model is
/// worse than an honest `unknown` in the Model Validation division. The family
/// needs <= ~2,000; raise only after measuring a validator.
const COLOR_MAX_TABLE_ROWS: usize = 50_000;

/// Deadline poll cadence, in charged work units (the parent polls per
/// candidate; this loop has no comparably coarse unit).
const COLOR_DEADLINE_MASK: u64 = 0xFFFF;

/// Result of the fused shape walk over the assertion set.
///
/// One walk collects everything: `and`-only recursion, per-subject domain
/// INTERSECTION, raw disequality pairs, and the coverage bit. `covered` going
/// false aborts the walk immediately — that is what makes a non-matching
/// instance cost one term-node visit.
struct ShapeScan {
    /// Running intersection of every asserted finite domain, per subject.
    dom: HashMap<TermId, BTreeSet<BigInt>>,
    /// Raw ordered disequality pairs, before the domain-membership check.
    pairs: Vec<(TermId, TermId)>,
    /// Every visited node was a recognised shape. Not a soundness device (the
    /// gates are) — it is what lets the pass decline early instead of building
    /// a model the gates would throw away.
    covered: bool,
    /// Some subject's domain intersection went empty. That genuinely means the
    /// instance is unsatisfiable, but this pass never claims unsat: it
    /// declines and the normal solver decides.
    dead: bool,
}

/// How a subject term is published in the emitted model.
enum SubjectKind {
    /// A declared nullary constant: the LIA pin alone is the interpretation
    /// (`output.rs` prints Int nullary symbols LIA-first).
    Leaf,
    /// A UF application with all-constant arguments: needs a function-table
    /// row too, because `output.rs` sources an arity>0 interpretation ONLY
    /// from `euf_model.function_tables` and model completion explicitly
    /// refuses to fabricate a table for a name occurring in an assertion.
    /// Pinning only LIA would validate perfectly and then print no
    /// interpretation for the symbol at all — a partial model.
    App { table: String, key: Vec<String> },
}

/// Snapshot of the verdict-shaping state the proposal mutates, restored
/// verbatim on every decline so a rejected proposal is byte-identical to a run
/// with `AY_INT_COLORING=0` (the `partition_rescue::RescueStateGuard`
/// contract).
struct ColoringStateGuard {
    last_model: Option<Model>,
    last_result: Option<SolveResult>,
    last_unknown_reason: Option<UnknownReason>,
    last_model_validated: bool,
    skip_model_eval: bool,
    defer_model_validation: bool,
    qfax_refinement_clause: Option<Vec<(TermId, bool)>>,
    last_assumption_core: Option<Vec<TermId>>,
}

impl Executor {
    /// Propose a finite-domain COLOURING model for the pre-dispatch
    /// conjunction.
    ///
    /// Returns `true` only when a colouring was built AND accepted by the full
    /// strict validation pipeline plus the independent model-check gate, with
    /// the accepted model installed in `last_model`. Returns `false` otherwise,
    /// with every mutated field restored, so `route_to_solver` runs exactly as
    /// if the pass did not exist.
    ///
    /// It cannot produce `unsat` or `unknown`: those are not among its return
    /// values, and it runs strictly BEFORE any verdict exists.
    pub(in crate::executor) fn int_domain_coloring_proposes_sat(
        &mut self,
        pre_dispatch_assertions: &[TermId],
    ) -> bool {
        // AY convention: default ON, `=0` opts out. FIRST statement, so the
        // off path is byte-identical to a binary without the pass — which is
        // what makes the same-binary A/B a measurement rather than a
        // comparison of two solvers. Deliberately a separate name from
        // `AY_INT_PIGEONHOLE` so the two halves stay independently A/B-able.
        if std::env::var_os("AY_INT_COLORING").is_some_and(|v| v == "0") {
            return false;
        }
        let debug = std::env::var_os("AY_DEBUG_PIGEONHOLE").is_some();

        let Some(plan) = self.int_domain_coloring_plan(pre_dispatch_assertions, debug) else {
            return false;
        };
        self.install_and_gate_coloring_model(plan, debug)
    }

    /// Everything up to and including the colouring: shape walk, graph build,
    /// DSATUR, and the per-subject publication plan. Pure read over `self`
    /// (`&self`), so no state can be perturbed by a decline anywhere in here.
    fn int_domain_coloring_plan(
        &self,
        assertions: &[TermId],
        debug: bool,
    ) -> Option<Vec<(TermId, SubjectKind, BigInt)>> {
        let mut scan_budget = COLOR_SCAN_NODE_BUDGET;
        let mut scan = ShapeScan {
            dom: HashMap::default(),
            pairs: Vec::new(),
            covered: true,
            dead: false,
        };
        for &assertion in assertions {
            self.coloring_scan_in(assertion, &mut scan, &mut scan_budget);
            if !scan.covered || scan.dead {
                break;
            }
        }
        // Every one of these is a silent decline. In particular `dead` (an
        // empty domain intersection) is NOT reported as unsat: proving unsat
        // is the parent module's job and it re-verifies its own certificate.
        if scan.dead {
            if debug {
                eprintln!("c int-coloring-debug decline=empty-domain-intersection");
            }
            return None;
        }
        if !scan.covered {
            if debug {
                eprintln!("c int-coloring-debug decline=uncovered-assertion");
            }
            return None;
        }
        if scan_budget == 0 {
            // A truncated walk is a MISSING CONSTRAINT on this side, never a
            // sound skip (contrast the parent's collectors).
            if debug {
                eprintln!("c int-coloring-debug decline=scan-budget");
            }
            return None;
        }
        if scan.dom.len() < 2 || scan.pairs.is_empty() {
            if debug {
                eprintln!(
                    "c int-coloring-debug decline=not-a-coloring vars={} pairs={}",
                    scan.dom.len(),
                    scan.pairs.len()
                );
            }
            return None;
        }
        if scan.dom.len() > COLOR_MAX_SUBJECTS || scan.pairs.len() > COLOR_MAX_EDGES {
            if debug {
                eprintln!("c int-coloring-debug decline=too-large");
            }
            return None;
        }
        // A pair with a domain-free endpoint is a constraint this pass cannot
        // honour (the parent DROPS it, which is sound only for unsat).
        if scan
            .pairs
            .iter()
            .any(|(a, b)| !scan.dom.contains_key(a) || !scan.dom.contains_key(b))
        {
            if debug {
                eprintln!("c int-coloring-debug decline=edge-endpoint-without-domain");
            }
            return None;
        }

        let mut work_budget = COLOR_WORK_BUDGET;
        let graph = self.build_coloring_graph(&scan, &mut work_budget, debug)?;
        let assignment = self.run_dsatur(&graph, &mut work_budget, debug)?;
        self.coloring_publication_plan(&graph, &assignment, debug)
    }

    /// Fused shape walk. `and`-only recursion, the same rule the parent's
    /// collectors use: a domain or disequality under `or`/`ite`/`=>`/`not` is
    /// not unconditional, so it may not be treated as a constraint on the
    /// model — and, unlike the parent, an unrecognised node is a hard
    /// `covered = false` rather than a skip.
    fn coloring_scan_in(&self, term: TermId, scan: &mut ShapeScan, budget: &mut u64) {
        if !scan.covered || scan.dead {
            return;
        }
        if *budget == 0 {
            return; // caller declines on an exhausted budget
        }
        *budget -= 1;
        match self.ctx.terms.get(term) {
            TermData::App(sym, args) if sym.name() == "and" => {
                let args = args.clone();
                for arg in args {
                    self.coloring_scan_in(arg, scan, budget);
                    if !scan.covered || scan.dead {
                        return;
                    }
                }
            }
            // `(or (= x c1) ... (= x cm))`: the domain staircase. Every
            // disjunct must be a bare `(= x const)` over the SAME subject.
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
                        scan.covered = false;
                        return;
                    };
                    match subject {
                        None => subject = Some(x),
                        Some(s) if s == x => {}
                        _ => {
                            scan.covered = false;
                            return;
                        }
                    }
                    values.insert(c);
                }
                if let Some(x) = subject {
                    Self::intersect_domain(scan, x, values);
                }
            }
            // `(= x c)`: a singleton domain. Any other equality is a
            // constraint this pass does not model.
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                match self.int_domain_literal(term) {
                    Some((x, c)) => {
                        let mut values = BTreeSet::new();
                        values.insert(c);
                        Self::intersect_domain(scan, x, values);
                    }
                    None => scan.covered = false,
                }
            }
            // Kept for robustness: `mk_distinct` normalises the binary case to
            // `Not(Eq)`, but an internally built n-ary distinct can reach here.
            TermData::App(sym, args) if sym.name() == "distinct" && args.len() >= 2 => {
                let args = args.clone();
                for i in 0..args.len() {
                    for j in (i + 1)..args.len() {
                        if args[i] == args[j] {
                            // `(distinct x x)` is `false`. The parent drops the
                            // self-pair (sound: it only weakens the clique
                            // search); here a colouring would cheerfully claim
                            // sat on an unsatisfiable assertion.
                            scan.covered = false;
                            return;
                        }
                        if *budget == 0 {
                            return;
                        }
                        *budget -= 1;
                        scan.pairs.push(Self::ordered_term_pair(args[i], args[j]));
                    }
                }
            }
            // `(not (= a b))`: the edge shape the whole family arrives in.
            TermData::Not(inner) => {
                let TermData::App(sym, args) = self.ctx.terms.get(*inner) else {
                    scan.covered = false;
                    return;
                };
                if sym.name() != "=" || args.len() != 2 {
                    scan.covered = false;
                    return;
                }
                if args[0] == args[1] {
                    scan.covered = false; // `(not (= x x))` is `false`
                    return;
                }
                scan.pairs.push(Self::ordered_term_pair(args[0], args[1]));
            }
            // An asserted `true` constrains nothing; coverage is preserved.
            TermData::Const(Constant::Bool(true)) => {}
            _ => scan.covered = false,
        }
    }

    /// Intersect a newly seen asserted domain into the running one. EVERY
    /// asserted domain must hold in a model, so intersection — not the
    /// parent's min-cardinality choice — is the model-side rule. An empty
    /// intersection sets `dead` (a decline), never an unsat claim.
    fn intersect_domain(scan: &mut ShapeScan, subject: TermId, values: BTreeSet<BigInt>) {
        match scan.dom.get_mut(&subject) {
            None => {
                scan.dom.insert(subject, values);
            }
            Some(existing) => {
                let inter: BTreeSet<BigInt> = existing.intersection(&values).cloned().collect();
                if inter.is_empty() {
                    scan.dead = true;
                }
                *existing = inter;
            }
        }
    }

    /// Compact the scan into the colouring graph: deterministic vertex order,
    /// a GLOBAL ascending palette (so colour-id order is integer order and
    /// "smallest legal value" is "lowest clear bit"), per-subject colour ids
    /// and a deduplicated undirected adjacency.
    fn build_coloring_graph(
        &self,
        scan: &ShapeScan,
        work: &mut u64,
        debug: bool,
    ) -> Option<ColoringGraph> {
        let mut subjects: Vec<TermId> = scan.dom.keys().copied().collect();
        subjects.sort_by_key(|t| t.0);
        let index: HashMap<TermId, u32> = subjects
            .iter()
            .enumerate()
            .map(|(i, &t)| (t, i as u32))
            .collect();

        let mut palette_set: BTreeSet<BigInt> = BTreeSet::new();
        for v in &subjects {
            palette_set.extend(scan.dom[v].iter().cloned());
        }
        if palette_set.len() > COLOR_MAX_PALETTE {
            if debug {
                eprintln!(
                    "c int-coloring-debug decline=palette-too-large values={}",
                    palette_set.len()
                );
            }
            return None;
        }
        let palette: Vec<BigInt> = palette_set.into_iter().collect();
        let value_id: HashMap<BigInt, u32> = palette
            .iter()
            .enumerate()
            .map(|(i, v)| (v.clone(), i as u32))
            .collect();

        let mut dom: Vec<Vec<u32>> = Vec::with_capacity(subjects.len());
        for v in &subjects {
            let mut ids: Vec<u32> = scan.dom[v].iter().map(|c| value_id[c]).collect();
            // The BTreeSet is already ascending and the palette is globally
            // ascending, so this is a no-op — asserted for the invariant the
            // "first clear bit == smallest legal value" step relies on.
            ids.sort_unstable();
            dom.push(ids);
        }

        let mut adj: Vec<Vec<u32>> = vec![Vec::new(); subjects.len()];
        let mut seen: HashSet<(u32, u32)> = HashSet::default();
        for (a, b) in &scan.pairs {
            if !self.charge(work, 1) {
                return None;
            }
            let (va, vb) = (index[a], index[b]);
            if !seen.insert((va, vb)) {
                continue;
            }
            adj[va as usize].push(vb);
            adj[vb as usize].push(va);
        }

        if debug {
            eprintln!(
                "c int-coloring-debug vars={} edges={} values={}",
                subjects.len(),
                seen.len(),
                palette.len()
            );
        }
        Some(ColoringGraph {
            subjects,
            palette,
            dom,
            adj,
        })
    }

    /// Fail-first greedy DSATUR restricted to the asserted domains.
    ///
    /// Priority is (fewest remaining legal values, highest degree, lowest
    /// vertex index): fail-first, with a fully deterministic tie-break. There
    /// is NO backtracking — a vertex with no legal value left is a hard
    /// decline. That is a measurement, not taste: plain greedy solves all 42
    /// of the family's open instances, and chronological backtracking on a
    /// 97.6%-dense graph has no usable bound, i.e. it is precisely the way to
    /// burn the deadline this pass exists to save.
    fn run_dsatur(&self, g: &ColoringGraph, work: &mut u64, debug: bool) -> Option<Vec<u32>> {
        let n = g.subjects.len();
        // Blocking state is one flat bit array sized to sum(|dom[v]|), NOT
        // subjects x palette: the latter is 51 MB at 100k subjects x 4096
        // colours.
        let mut blk_off: Vec<u32> = Vec::with_capacity(n);
        let mut words_total = 0usize;
        for d in &g.dom {
            blk_off.push(words_total as u32);
            words_total += d.len().div_ceil(64);
        }
        let mut blocked: Vec<u64> = vec![0; words_total];
        let mut remaining: Vec<u32> = g.dom.iter().map(|d| d.len() as u32).collect();
        let degree: Vec<u32> = g.adj.iter().map(|a| a.len() as u32).collect();
        let mut assigned: Vec<Option<u32>> = vec![None; n];

        let key = |remaining: u32, v: usize, degree: &[u32]| {
            Reverse((remaining, u32::MAX - degree[v], v as u32))
        };
        let mut heap: BinaryHeap<Reverse<(u32, u32, u32)>> = BinaryHeap::with_capacity(n);
        for (v, &count) in remaining.iter().enumerate() {
            heap.push(key(count, v, &degree));
        }

        let mut done = 0usize;
        while done < n {
            // Lazy deletion: an entry is stale once its vertex is assigned or
            // its recorded saturation is out of date.
            let v = loop {
                if !self.charge(work, 1) {
                    return None;
                }
                let Some(Reverse((k, _, v))) = heap.pop() else {
                    // Unassigned vertices with an empty heap is an internal
                    // invariant break; decline rather than guess.
                    if debug {
                        eprintln!("c int-coloring-debug decline=heap-underflow");
                    }
                    return None;
                };
                let v = v as usize;
                if assigned[v].is_none() && k == remaining[v] {
                    break v;
                }
            };
            if remaining[v] == 0 {
                if debug {
                    eprintln!("c int-coloring-debug decline=no-legal-value");
                }
                return None;
            }
            // Smallest legal value: the first CLEAR bit, since `dom[v]` and the
            // global palette are both ascending.
            let words = g.dom[v].len().div_ceil(64);
            let mut pick: Option<usize> = None;
            for w in 0..words {
                if !self.charge(work, 1) {
                    return None;
                }
                let free = !blocked[blk_off[v] as usize + w];
                if free != 0 {
                    let bit = free.trailing_zeros() as usize;
                    let p = w * 64 + bit;
                    if p < g.dom[v].len() {
                        pick = Some(p);
                        break;
                    }
                }
            }
            let Some(p) = pick else {
                // `remaining[v] > 0` with no clear bit is an internal
                // invariant break, not a colouring failure.
                if debug {
                    eprintln!("c int-coloring-debug decline=bitset-invariant");
                }
                return None;
            };
            let c = g.dom[v][p];
            assigned[v] = Some(c);
            done += 1;

            for &w in &g.adj[v] {
                if !self.charge(work, 1) {
                    return None;
                }
                let w = w as usize;
                if assigned[w].is_some() {
                    continue;
                }
                let Ok(q) = g.dom[w].binary_search(&c) else {
                    continue;
                };
                let word = blk_off[w] as usize + q / 64;
                let mask = 1u64 << (q % 64);
                if blocked[word] & mask == 0 {
                    blocked[word] |= mask;
                    remaining[w] -= 1;
                    heap.push(key(remaining[w], w, &degree));
                }
            }
        }
        // Total by construction: the loop exits only at `done == n`.
        assigned.into_iter().collect()
    }

    /// Charge `amount` against the shared work budget, polling the solve
    /// deadline on a coarse cadence. `false` means "stop and decline" — either
    /// the budget ran out or the deadline did. This is the single place both
    /// limits are enforced, so no loop in the pass can outrun them.
    fn charge(&self, work: &mut u64, amount: u64) -> bool {
        if *work < amount {
            *work = 0;
            return false;
        }
        *work -= amount;
        // `work` decreases monotonically, so masking it gives a poll roughly
        // every COLOR_DEADLINE_MASK+1 charged units without a second counter.
        if *work & COLOR_DEADLINE_MASK == 0 && self.solve_deadline.expired() {
            *work = 0;
            return false;
        }
        true
    }

    /// Turn the colouring into a per-subject publication plan, declining on any
    /// subject shape that cannot be rendered FAITHFULLY in an emitted model.
    ///
    /// Accepted: a declared nullary constant (LIA pin alone) and a UF
    /// application with all-constant arguments over a declared, non-defined,
    /// non-internal symbol (LIA pin plus a function-table row). Everything else
    /// (an arithmetic composite, an `ite`, a defined-fun application) declines:
    /// pinning a value for a term whose interpretation is COMPUTED from its
    /// leaves would be a model the printer and the evaluators disagree about.
    fn coloring_publication_plan(
        &self,
        g: &ColoringGraph,
        assignment: &[u32],
        debug: bool,
    ) -> Option<Vec<(TermId, SubjectKind, BigInt)>> {
        let mut plan: Vec<(TermId, SubjectKind, BigInt)> = Vec::with_capacity(g.subjects.len());
        let mut rows_per_table: HashMap<String, usize> = HashMap::default();
        for (i, &t) in g.subjects.iter().enumerate() {
            let value = g.palette[assignment[i] as usize].clone();
            let kind = match self.ctx.terms.get(t) {
                TermData::Var(_, _) => SubjectKind::Leaf,
                TermData::App(sym, args) if !args.is_empty() => {
                    let name = sym.name().to_string();
                    // Terms key symbols by IDENTITY; `symbol_info_by_identity`
                    // returns `Some` only for a real identity, so this both
                    // validates the table key and gets the signature.
                    let Some(info) = self.ctx.symbol_info_by_identity(&name) else {
                        if debug {
                            eprintln!("c int-coloring-debug decline=unknown-symbol sym={name}");
                        }
                        return None;
                    };
                    if info.arg_sorts.len() != args.len() {
                        return None;
                    }
                    // A defined-fun / solver-internal symbol is SKIPPED by the
                    // model printer, so a table for it would validate and then
                    // print nothing — a partial model.
                    if self.ctx.is_defined_fun(&name) || self.ctx.is_internal_symbol(&name) {
                        if debug {
                            eprintln!("c int-coloring-debug decline=unprintable-symbol sym={name}");
                        }
                        return None;
                    }
                    let mut key = Vec::with_capacity(args.len());
                    for &a in args {
                        match self.ctx.terms.get(a) {
                            TermData::Const(Constant::Int(n)) => key.push(n.to_string()),
                            TermData::Const(Constant::Bool(b)) => key.push(b.to_string()),
                            _ => {
                                if debug {
                                    eprintln!("c int-coloring-debug decline=non-constant-argument");
                                }
                                return None;
                            }
                        }
                    }
                    let rows = rows_per_table.entry(name.clone()).or_insert(0);
                    *rows += 1;
                    if *rows > COLOR_MAX_TABLE_ROWS {
                        if debug {
                            eprintln!("c int-coloring-debug decline=table-too-deep sym={name}");
                        }
                        return None;
                    }
                    SubjectKind::App { table: name, key }
                }
                _ => {
                    if debug {
                        eprintln!("c int-coloring-debug decline=unpublishable-subject");
                    }
                    return None;
                }
            };
            plan.push((t, kind, value));
        }
        Some(plan)
    }

    /// Install the proposed model and submit it to the strict acceptance gates.
    ///
    /// `last_model_validated` is deliberately left `false`: `emit_sat_verdict`
    /// branches on it, and setting it by hand would forge evidence. It may only
    /// become `true` as a SIDE EFFECT of `finalize_sat_model_validation`
    /// succeeding (the `diff_logic` / `strings_w4` contract).
    fn install_and_gate_coloring_model(
        &mut self,
        plan: Vec<(TermId, SubjectKind, BigInt)>,
        debug: bool,
    ) -> bool {
        let mut lia_values: HashMap<TermId, BigInt> = HashMap::default();
        // `function_tables` and `function_table_terms` are POSITIONALLY
        // aligned by contract (`combiner_models` zips them), so rows and their
        // source applications are built together.
        let mut tables: HashMap<String, Vec<(Vec<String>, String)>> = HashMap::default();
        let mut table_terms: HashMap<String, Vec<TermId>> = HashMap::default();
        for (term, kind, value) in &plan {
            lia_values.insert(*term, value.clone());
            if let SubjectKind::App { table, key } = kind {
                tables
                    .entry(table.clone())
                    .or_default()
                    .push((key.clone(), value.to_string()));
                table_terms.entry(table.clone()).or_default().push(*term);
            }
        }
        // Deterministic row order, keeping the two aligned vectors in step. A
        // duplicate argument key with a different result is structurally
        // impossible (hash-consing makes congruent applications ONE TermId,
        // hence one subject), but a first-match `ite` chain that contradicted
        // the validated interpretation is exactly the wrong-printed-model
        // class, so it is checked rather than assumed.
        for (name, rows) in tables.iter_mut() {
            let terms = table_terms.get_mut(name).expect("aligned by construction");
            let mut zipped: Vec<((Vec<String>, String), TermId)> =
                rows.drain(..).zip(terms.drain(..)).collect();
            zipped.sort_by(|a, b| a.0 .0.cmp(&b.0 .0));
            let mut seen: HashMap<Vec<String>, String> = HashMap::default();
            for ((key, result), _) in &zipped {
                if seen
                    .insert(key.clone(), result.clone())
                    .is_some_and(|p| p != *result)
                {
                    if debug {
                        eprintln!("c int-coloring-debug decline=conflicting-table-row sym={name}");
                    }
                    return false;
                }
            }
            for (row, term) in zipped {
                rows.push(row);
                terms.push(term);
            }
        }

        let guard = ColoringStateGuard {
            last_model: self.last_model.clone(),
            last_result: self.last_result.clone(),
            last_unknown_reason: self.last_unknown_reason,
            last_model_validated: self.last_model_validated,
            skip_model_eval: self.skip_model_eval,
            defer_model_validation: self.defer_model_validation,
            qfax_refinement_clause: self.qfax_refinement_clause.clone(),
            last_assumption_core: self.last_assumption_core.clone(),
        };

        let mut model = Model::empty();
        model.lia_model = Some(ay_lia::LiaModel { values: lia_values });
        if !tables.is_empty() {
            let euf = ay_euf::EufModel {
                function_tables: tables,
                function_table_terms: table_terms,
                ..ay_euf::EufModel::default()
            };
            model.euf_model = Some(euf);
        }
        self.last_model = Some(model);
        // `validate_model_attempt` reads the (last_result, last_model) PAIR and
        // refuses to validate anything that is not already a Sat candidate, so
        // the proposal must be staged as one. Restored verbatim on decline.
        self.last_result = Some(SolveResult::Sat);
        self.last_model_validated = false;
        self.last_unknown_reason = None;
        // Forced OFF so `finalize_sat_model_validation` cannot take its
        // fail-OPEN defer/skip early return (which returns Ok(Sat) without
        // having validated anything).
        self.defer_model_validation = false;
        self.skip_model_eval = false;

        let finalize = self.finalize_sat_model_validation();
        let finalize_ok = matches!(finalize, Ok(SolveResult::Sat)) && self.last_model_validated;
        if !finalize_ok {
            if debug {
                eprintln!("c int-coloring-debug decline=finalize-rejected result={finalize:?}");
            }
            self.restore_after_coloring(guard);
            return false;
        }
        // The strict POSITIVE kernel: every assertion must be PROVABLY true
        // under a separate compositional evaluator. Not the fail-open
        // `Ok(Sat)`/`CannotConfirm` path — "cannot evaluate" rejects here.
        let verdict = self.confirm_sat_with_independent_gate();
        if !matches!(verdict, ay_model_check::GateVerdict::ConfirmedSat) {
            if debug {
                eprintln!("c int-coloring-debug decline=gate-rejected verdict={verdict:?}");
            }
            self.restore_after_coloring(guard);
            return false;
        }
        if debug {
            eprintln!("c int-coloring-debug accepted subjects={}", plan.len());
        }
        // ACCEPT path: keep the validated model/verdict, but RESTORE the two
        // flags this function forced OFF. They are not ours to consume.
        // `check_sat.rs:852` sets `defer_model_validation` whenever the input
        // contained any quantifier, and `quantifier_loop/result_mapping.rs:2159`
        // gates the ENTIRE quantified-SAT acceptance discipline on it (restore
        // original assertions, re-run finalize against them, apply
        // has_skipped_quantifiers / has_any_evidence / the MBQI quick-check).
        // Leaving it false here would silently skip that discipline downstream —
        // the decline paths already restore both, so the accept path leaking
        // them was the asymmetry.
        self.defer_model_validation = guard.defer_model_validation;
        self.skip_model_eval = guard.skip_model_eval;
        self.last_statistics.set_int("solver.int_coloring.fired", 1);
        true
    }

    /// Restore the snapshotted verdict-shaping state, reproducing a no-pass run
    /// byte-for-byte.
    fn restore_after_coloring(&mut self, guard: ColoringStateGuard) {
        self.last_model = guard.last_model;
        self.last_result = guard.last_result;
        self.last_unknown_reason = guard.last_unknown_reason;
        self.last_model_validated = guard.last_model_validated;
        self.skip_model_eval = guard.skip_model_eval;
        self.defer_model_validation = guard.defer_model_validation;
        self.qfax_refinement_clause = guard.qfax_refinement_clause;
        self.last_assumption_core = guard.last_assumption_core;
    }
}

/// The compact colouring graph. Vertices are `subjects` order (ascending
/// `TermId`); colours are indices into the globally ascending `palette`, so
/// colour-id order IS integer order.
struct ColoringGraph {
    subjects: Vec<TermId>,
    palette: Vec<BigInt>,
    dom: Vec<Vec<u32>>,
    adj: Vec<Vec<u32>>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_frontend::parse;

    /// Execute declarations + asserts (no check-sat) and return the executor.
    fn exec_setup(input: &str) -> Executor {
        let commands = parse(input).unwrap();
        let mut exec = Executor::new();
        exec.execute_all(&commands).unwrap();
        exec
    }

    /// Run the pass over the executor's own assertion set.
    fn propose(exec: &mut Executor) -> bool {
        let assertions = exec.ctx.assertions.clone();
        exec.int_domain_coloring_proposes_sat(&assertions)
    }

    /// The value the accepted model pins for a declared nullary Int constant.
    fn pinned(exec: &Executor, name: &str) -> Option<BigInt> {
        let term = exec.ctx.symbol_info(name).and_then(|i| i.term)?;
        exec.last_model
            .as_ref()?
            .lia_model
            .as_ref()?
            .values
            .get(&term)
            .cloned()
    }

    /// A colourable triangle over 3 values: the pass proposes, the gates
    /// accept, and every pinned value is inside its asserted domain and
    /// distinct from its neighbours'.
    #[test]
    fn test_int_coloring_colors_a_triangle() {
        let mut exec = exec_setup(
            r#"
            (set-logic QF_LIA)
            (declare-fun x0 () Int)
            (declare-fun x1 () Int)
            (declare-fun x2 () Int)
            (assert (or (= x0 0) (= x0 1) (= x0 2)))
            (assert (or (= x1 0) (= x1 1) (= x1 2)))
            (assert (or (= x2 0) (= x2 1) (= x2 2)))
            (assert (distinct x0 x1))
            (assert (distinct x0 x2))
            (assert (distinct x1 x2))
        "#,
        );
        assert!(propose(&mut exec), "a 3-clique over 3 values must colour");
        let vals: Vec<BigInt> = ["x0", "x1", "x2"]
            .iter()
            .map(|n| pinned(&exec, n).expect("every subject is pinned"))
            .collect();
        assert_eq!(
            vals.iter().collect::<BTreeSet<_>>().len(),
            3,
            "a proper colouring assigns three distinct values: {vals:?}"
        );
        for v in &vals {
            assert!(*v >= BigInt::from(0) && *v <= BigInt::from(2), "in domain");
        }
    }

    /// The exact case the parent's min-CARDINALITY domain choice gets wrong:
    /// `{0,1,2}` is kept over `{1,2,3,4}` there, and `{0,1,2}` is NOT a subset
    /// of `{1,2,3,4}`, so a colouring over the kept domain may pick `x0 = 0`
    /// and falsify the discarded assertion. The intersection is `{1,2}`.
    #[test]
    fn test_int_coloring_intersects_non_subset_domains() {
        let mut exec = exec_setup(
            r#"
            (set-logic QF_LIA)
            (declare-fun x0 () Int)
            (declare-fun x1 () Int)
            (assert (or (= x0 1) (= x0 2) (= x0 3) (= x0 4)))
            (assert (or (= x0 0) (= x0 1) (= x0 2)))
            (assert (or (= x1 0) (= x1 1) (= x1 2)))
            (assert (distinct x0 x1))
        "#,
        );
        assert!(propose(&mut exec), "still colourable over the intersection");
        let x0 = pinned(&exec, "x0").expect("x0 pinned");
        assert!(
            x0 == BigInt::from(1) || x0 == BigInt::from(2),
            "x0 must satisfy BOTH domain assertions, got {x0}"
        );
    }

    /// Contradictory domains intersect to the empty set. That genuinely means
    /// unsat, but this pass never claims a verdict of its own: it declines.
    #[test]
    fn test_int_coloring_declines_on_empty_intersection() {
        let mut exec = exec_setup(
            r#"
            (set-logic QF_LIA)
            (declare-fun x0 () Int)
            (declare-fun x1 () Int)
            (assert (= x0 0))
            (assert (or (= x0 1) (= x0 2)))
            (assert (or (= x1 0) (= x1 1)))
            (assert (distinct x0 x1))
        "#,
        );
        assert!(!propose(&mut exec), "an empty intersection must decline");
        assert!(exec.last_model.is_none(), "no model may be left installed");
    }

    /// Equal-cardinality DISJOINT domains: the parent keeps the first with no
    /// set comparison; the intersection is empty, so this declines.
    #[test]
    fn test_int_coloring_declines_on_disjoint_equal_size_domains() {
        let mut exec = exec_setup(
            r#"
            (set-logic QF_LIA)
            (declare-fun x0 () Int)
            (declare-fun x1 () Int)
            (assert (or (= x0 0) (= x0 1) (= x0 2)))
            (assert (or (= x0 3) (= x0 4) (= x0 5)))
            (assert (or (= x1 0) (= x1 1) (= x1 2)))
            (assert (distinct x0 x1))
        "#,
        );
        assert!(!propose(&mut exec), "disjoint domains must decline");
    }

    /// A colourable graph plus one assertion outside the recognised shapes.
    /// The colouring part is fine; the pass must still not answer on its own
    /// authority.
    #[test]
    fn test_int_coloring_declines_on_uncovered_assertion() {
        let mut exec = exec_setup(
            r#"
            (set-logic QF_LIA)
            (declare-fun x0 () Int)
            (declare-fun x1 () Int)
            (declare-fun y () Int)
            (assert (or (= x0 0) (= x0 1)))
            (assert (or (= x1 0) (= x1 1)))
            (assert (distinct x0 x1))
            (assert (> y 5))
        "#,
        );
        assert!(!propose(&mut exec), "an uncovered assertion must decline");
    }

    /// `(distinct x x)` is `false`. The parent drops the self-pair (sound for
    /// a clique search); a colouring would happily claim sat.
    #[test]
    fn test_int_coloring_declines_on_self_disequality() {
        let mut exec = exec_setup(
            r#"
            (set-logic QF_LIA)
            (declare-fun x0 () Int)
            (declare-fun x1 () Int)
            (assert (or (= x0 0) (= x0 1)))
            (assert (or (= x1 0) (= x1 1)))
            (assert (distinct x0 x1))
            (assert (distinct x0 x0))
        "#,
        );
        assert!(!propose(&mut exec), "a self-disequality must decline");
    }

    /// An edge whose endpoint carries no domain is a constraint this pass
    /// cannot honour (the parent DROPS it — sound only for unsat).
    #[test]
    fn test_int_coloring_declines_on_domain_free_endpoint() {
        let mut exec = exec_setup(
            r#"
            (set-logic QF_LIA)
            (declare-fun x0 () Int)
            (declare-fun x1 () Int)
            (declare-fun y () Int)
            (assert (or (= x0 0) (= x0 1)))
            (assert (or (= x1 0) (= x1 1)))
            (assert (distinct x0 x1))
            (assert (distinct x0 y))
        "#,
        );
        assert!(!propose(&mut exec), "a domain-free endpoint must decline");
    }

    /// A triangle over a 2-value palette exhausts some vertex's legal values.
    /// v1 has no backtracking, so it declines and the caller falls through to
    /// the normal solver.
    #[test]
    fn test_int_coloring_declines_when_no_legal_value_remains() {
        let mut exec = exec_setup(
            r#"
            (set-logic QF_LIA)
            (declare-fun x0 () Int)
            (declare-fun x1 () Int)
            (declare-fun x2 () Int)
            (assert (or (= x0 0) (= x0 1)))
            (assert (or (= x1 0) (= x1 1)))
            (assert (or (= x2 0) (= x2 1)))
            (assert (distinct x0 x1))
            (assert (distinct x0 x2))
            (assert (distinct x1 x2))
        "#,
        );
        assert!(!propose(&mut exec), "an uncolourable clique must decline");
        assert!(exec.last_model.is_none(), "no model may be left installed");
    }

    /// The same syntax over `Real` is not a finite domain (`int_domain_literal`
    /// rejects it), so nothing is collected and the pass declines.
    #[test]
    fn test_int_coloring_ignores_non_int_sorts() {
        let mut exec = exec_setup(
            r#"
            (set-logic QF_LRA)
            (declare-fun r0 () Real)
            (declare-fun r1 () Real)
            (assert (or (= r0 0.0) (= r0 1.0)))
            (assert (or (= r1 0.0) (= r1 1.0)))
            (assert (distinct r0 r1))
        "#,
        );
        assert!(!propose(&mut exec), "Real chains are not finite domains");
    }

    /// UF-application subjects (`(u N)`, the whole vlsat family) publish a
    /// FUNCTION TABLE as well as the LIA pins: `output.rs` sources an arity>0
    /// interpretation only from there, so pinning LIA alone would validate and
    /// then print no interpretation for `u` at all.
    #[test]
    fn test_int_coloring_publishes_a_function_table_for_uf_subjects() {
        let mut exec = exec_setup(
            r#"
            (set-logic QF_UFIDL)
            (declare-fun u (Int) Int)
            (assert (= (u 1) 0))
            (assert (or (= (u 2) 0) (= (u 2) 1)))
            (assert (or (= (u 3) 0) (= (u 3) 1) (= (u 3) 2)))
            (assert (distinct (u 1) (u 2)))
            (assert (distinct (u 1) (u 3)))
            (assert (distinct (u 2) (u 3)))
        "#,
        );
        assert!(propose(&mut exec), "the vlsat shape must colour");
        let model = exec.last_model.as_ref().expect("model installed");
        let euf = model.euf_model.as_ref().expect("euf model for the table");
        let table = euf.function_tables.get("u").expect("interpretation for u");
        assert_eq!(table.len(), 3, "one row per constrained application");
        // `(u 1)` is pinned to 0 by the singleton domain, so the other two must
        // take the remaining values.
        assert_eq!(
            table.iter().find(|(k, _)| k == &vec!["1".to_string()]),
            Some(&(vec!["1".to_string()], "0".to_string()))
        );
        let results: BTreeSet<&String> = table.iter().map(|(_, r)| r).collect();
        assert_eq!(results.len(), 3, "a proper colouring: {table:?}");
        assert_eq!(
            euf.function_table_terms.get("u").map(Vec::len),
            Some(3),
            "row/source vectors must stay positionally aligned"
        );
    }

    /// DETERMINISM: two runs over identical executor state produce identical
    /// pins and identical table rows.
    #[test]
    fn test_int_coloring_is_deterministic() {
        const SRC: &str = r#"
            (set-logic QF_UFIDL)
            (declare-fun u (Int) Int)
            (assert (or (= (u 1) 0) (= (u 1) 1) (= (u 1) 2)))
            (assert (or (= (u 2) 0) (= (u 2) 1) (= (u 2) 2)))
            (assert (or (= (u 3) 0) (= (u 3) 1) (= (u 3) 2)))
            (assert (or (= (u 4) 1) (= (u 4) 2)))
            (assert (distinct (u 1) (u 2)))
            (assert (distinct (u 1) (u 3)))
            (assert (distinct (u 2) (u 3)))
            (assert (distinct (u 2) (u 4)))
        "#;
        let mut a = exec_setup(SRC);
        let mut b = exec_setup(SRC);
        assert!(propose(&mut a));
        assert!(propose(&mut b));
        let table_a = a.last_model.as_ref().unwrap().euf_model.as_ref().unwrap();
        let table_b = b.last_model.as_ref().unwrap().euf_model.as_ref().unwrap();
        assert_eq!(table_a.function_tables, table_b.function_tables);
        let lia_a = &a.last_model.as_ref().unwrap().lia_model;
        let lia_b = &b.last_model.as_ref().unwrap().lia_model;
        assert_eq!(
            lia_a.as_ref().map(|m| {
                let mut v: Vec<_> = m.values.iter().map(|(k, x)| (k.0, x.clone())).collect();
                v.sort();
                v
            }),
            lia_b.as_ref().map(|m| {
                let mut v: Vec<_> = m.values.iter().map(|(k, x)| (k.0, x.clone())).collect();
                v.sort();
                v
            })
        );
    }

    /// DEFAULT-ON with no env set (the `AY_INT_COLORING=0` opt-out is
    /// exercised end-to-end through the binary: `std::env::set_var` is
    /// unavailable here, the crate is `#![forbid(unsafe_code)]`).
    #[test]
    fn test_int_coloring_is_default_on() {
        assert!(
            std::env::var_os("AY_INT_COLORING").is_none(),
            "test env must not pin the knob"
        );
        let mut exec = exec_setup(
            r#"
            (set-logic QF_LIA)
            (declare-fun x0 () Int)
            (declare-fun x1 () Int)
            (assert (or (= x0 0) (= x0 1)))
            (assert (or (= x1 0) (= x1 1)))
            (assert (distinct x0 x1))
        "#,
        );
        assert!(propose(&mut exec), "the pass is DEFAULT-ON with no env set");
    }
}
