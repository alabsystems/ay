// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The exact counting engine: exhaustive DPLL with dynamic connected-component
//! decomposition and component caching (the sharpSAT/GANAK architecture),
//! generic over an exact [`CountValue`] semiring and supporting projection.
//!
//! ## Soundness notes (load-bearing)
//!
//! * **Cache key.** A component is a connected closure: every unassigned
//!   variable of a member clause belongs to the component's variable set.
//!   Hence `(sorted vars, sorted clause ids)` uniquely determines the residual
//!   formula — the residual of clause `c` is exactly its literals over
//!   unassigned variables, all of which are in the component. Two states with
//!   equal keys therefore count the same residual. Projection status and
//!   weights are per-variable global constants, so they are functions of the
//!   key as well.
//! * **Decomposition.** Variable-disjoint components share no active clauses,
//!   so (weighted/projected) counts multiply.
//! * **Projection.** Only projection variables are branched or counted; a
//!   component with no projection variable contributes 1 iff its residual is
//!   satisfiable (existential check, delegated to `ay-sat`), else 0. Forced
//!   assignments from unit propagation are entailed, so applying them never
//!   changes the projected count.
//! * **Counter symmetry.** All per-clause counter updates happen at *assign*
//!   time (`assign`), never at propagation-dequeue time, so `backtrack`
//!   reverses exactly the updates every trail literal applied — including
//!   literals enqueued but not yet propagated when a conflict aborts.
//! * **No unsound preprocessing.** Only entailment-based simplification is
//!   used (unit propagation, failed literals). No pure literal elimination
//!   (not count-preserving).
//! * **Clause learning discipline** (see `learning-pollution-spec.md`):
//!   learned clauses participate in BCP and conflict analysis ONLY — never in
//!   component splitting or cache keys, which stay over original clauses.
//!   Learned-clause conflicts can be misattributed across components, so
//!   every zero branch purges all cache entries created inside its window
//!   (the watermark purge — provably the same purge set as sharpSAT's
//!   father/descendant pollution forest, because entry creation is
//!   DFS-contiguous). Caching a total that includes a conflict-driven zero
//!   branch is sound only jointly with that purge. Learned units are
//!   globally entailed (1UIP over F), re-asserted per branch with level-0
//!   semantics. Weighted mode attributes forced-literal weights by the
//!   variable's component membership, never by the forcing frame —
//!   cross-component propagations are integrated by their own component's
//!   count.

use crate::cache::{CompCache, CompKey};
use crate::value::{CountValue, WeightTable};

/// Internal literal: `var*2 + negated`, vars 0-based.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Lit(u32);

impl Lit {
    #[inline]
    fn new(var: u32, negated: bool) -> Self {
        Lit(var * 2 + u32::from(negated))
    }
    #[inline]
    fn from_dimacs(l: i32) -> Self {
        Lit::new(l.unsigned_abs() - 1, l < 0)
    }
    #[inline]
    fn var(self) -> usize {
        (self.0 >> 1) as usize
    }
    #[inline]
    fn negated(self) -> bool {
        self.0 & 1 == 1
    }
    #[inline]
    fn neg(self) -> Self {
        Lit(self.0 ^ 1)
    }
    #[inline]
    fn code(self) -> usize {
        self.0 as usize
    }
}

const UNASSIGNED: u8 = 0;
const VAL_TRUE: u8 = 1;
const VAL_FALSE: u8 = 2;

/// Antecedent of a trail literal, for 1UIP conflict analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Reason {
    /// Branching decision (or top-level assertion).
    Decision,
    /// Propagated by an original clause.
    Orig(u32),
    /// Propagated by a learned clause.
    Learned(u32),
}

/// The clause that produced a conflict.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConflictRef {
    Orig(u32),
    Learned(u32),
}

/// Stop learning past this many clauses (soundness-neutral: learning is an
/// optimization; the cap bounds memory since v3 has no DB reduction).
const MAX_LEARNED_CLAUSES: usize = 300_000;

/// Engine statistics for `c o` output lines.
#[derive(Debug, Default, Clone)]
pub struct Stats {
    /// Number of branching decisions.
    pub decisions: u64,
    /// Number of conflicts found by unit propagation.
    pub conflicts: u64,
    /// Component-cache hits.
    pub cache_hits: u64,
    /// Component-cache stores.
    pub cache_stores: u64,
    /// Entries dropped by cache eviction.
    pub cache_evictions: u64,
    /// SAT-oracle calls for projection-free components.
    pub sat_oracle_calls: u64,
    /// Components created by decomposition.
    pub components: u64,
    /// Top-level failed literals found by probing.
    pub failed_literals: u64,
    /// Learned clauses currently stored.
    pub learned_clauses: u64,
    /// Learned unit clauses (globally entailed literals found by analysis).
    pub learned_units: u64,
    /// Cache entries removed by pollution purges.
    pub cache_purged: u64,
    /// Learned clauses dropped by DB reduction.
    pub learned_reduced: u64,
    /// Maximum recursion depth reached.
    pub max_depth: u32,
}

/// Why counting failed (fail-closed surfaces).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CountAbort {
    /// The SAT oracle returned Unknown on an existential residual.
    OracleUnknown,
    /// The engine deadline expired (phase-1 budget).
    Deadline,
    /// The process memory limit was exceeded (see
    /// `ay_sys::process_memory_exceeded`; the limit is set once from
    /// `main()`). Terminal: an honest no-count beats an OOM kill — and on
    /// macOS an unbounded counter does not even get OOM-killed, it drives
    /// the machine into compressor exhaustion (2026-07-10 panic).
    Memory,
}

/// Engine configuration.
pub struct EngineConfig {
    /// Component-cache budget in bytes (approximate accounting).
    pub cache_budget_bytes: usize,
    /// Optional wall-clock deadline; the count aborts (fail-closed,
    /// `CountAbort::Deadline`) when exceeded. Used for phase-1 budgets.
    pub deadline: Option<std::time::Instant>,
}

impl Default for EngineConfig {
    fn default() -> Self {
        Self {
            // Competition memory limit is 32 GB; leave room for the formula,
            // trail, and oracle. Overridable by the CLI.
            cache_budget_bytes: 4 << 30,
            deadline: None,
        }
    }
}

/// A component: sorted unassigned variable ids + sorted active clause ids.
struct Comp {
    vars: Vec<u32>,
    /// ALL active clause ids (for the SAT oracle and sub-splitting).
    clauses: Vec<u32>,
    /// Only *shortened* long clauses (≥1 falsified literal, unsatisfied) —
    /// the cache key needs nothing else: post-BCP, an active binary has both
    /// literals free, and an untouched long clause is active iff all its
    /// variables are in the component, so both are functions of the variable
    /// set and the original formula.
    key_clauses: Vec<u32>,
    /// Occurrence counts in active clauses, parallel to `vars` (branching
    /// frequency score, computed as a byproduct of discovery).
    freq: Vec<u32>,
    /// Number of projection variables in `vars` (all of them when no
    /// projection is active).
    proj_count: u32,
}

/// Sentinel terminating analyzer index sections.
const IDX_END: u32 = u32::MAX;
/// Long-clause entries with this offset walk the arena instead of a private
/// literal copy (clauses longer than the copy cap).
const IDX_ARENA: u32 = u32::MAX - 1;
/// Cap on private literal copies per long-clause entry.
const IDX_COPY_CAP: usize = 64;

/// Per-variable occurrence index for component analysis (sharpsat-td layout):
/// one contiguous pool, per variable two sections, each `IDX_END`-terminated:
///
/// `[binary: other LITERAL codes...] IDX_END
///  [long: (clause_id, lits_ofs) pairs...] IDX_END`
///
/// where `lits_ofs` points into `lit_pool` at a copy of the clause's literal
/// codes with the variable itself omitted, `IDX_END`-terminated (or
/// `IDX_ARENA` for very long clauses, meaning "walk the arena").
/// Analysis therefore touches tight private memory and, for binaries,
/// exploits the post-BCP invariant (an active binary clause has both
/// literals unassigned) to avoid clause lookups entirely.
struct AnalyzerIndex {
    var_ofs: Vec<u32>,
    pool: Vec<u32>,
    lit_pool: Vec<u32>,
}

impl AnalyzerIndex {
    fn build(num_vars: usize, lits: &[Lit], start: &[u32]) -> Self {
        let n_clauses = start.len() - 1;
        // First pass: per-var section sizes.
        let mut bin_count = vec![0u32; num_vars];
        let mut long_count = vec![0u32; num_vars];
        for c in 0..n_clauses {
            let cl = &lits[start[c] as usize..start[c + 1] as usize];
            if cl.len() == 2 {
                bin_count[cl[0].var()] += 1;
                bin_count[cl[1].var()] += 1;
            } else if cl.len() > 2 {
                for l in cl {
                    long_count[l.var()] += 1;
                }
            }
        }
        let mut var_ofs = vec![0u32; num_vars + 1];
        let mut total = 0u64;
        for v in 0..num_vars {
            var_ofs[v] = total as u32;
            total += u64::from(bin_count[v]) + 1 + u64::from(long_count[v]) * 2 + 1;
        }
        var_ofs[num_vars] = total as u32;
        let mut pool = vec![IDX_END; total as usize];
        // Section fill cursors.
        let mut bin_fill: Vec<u32> = (0..num_vars).map(|v| var_ofs[v]).collect();
        let mut long_fill: Vec<u32> = (0..num_vars)
            .map(|v| var_ofs[v] + bin_count[v] + 1)
            .collect();
        let mut lit_pool: Vec<u32> = Vec::new();
        for c in 0..n_clauses {
            let cl = &lits[start[c] as usize..start[c + 1] as usize];
            if cl.len() == 2 {
                // Entry encodes the OTHER literal and this var's own
                // polarity: other_code << 1 | own_negated (so binary clauses
                // are reconstructible for the SAT oracle).
                pool[bin_fill[cl[0].var()] as usize] =
                    ((cl[1].code() as u32) << 1) | u32::from(cl[0].negated());
                bin_fill[cl[0].var()] += 1;
                pool[bin_fill[cl[1].var()] as usize] =
                    ((cl[0].code() as u32) << 1) | u32::from(cl[1].negated());
                bin_fill[cl[1].var()] += 1;
            } else if cl.len() > 2 {
                let copy = cl.len() <= IDX_COPY_CAP;
                for (i, l) in cl.iter().enumerate() {
                    let v = l.var();
                    let ofs = if copy {
                        let o = lit_pool.len() as u32;
                        for (j, m) in cl.iter().enumerate() {
                            if j != i {
                                lit_pool.push(m.code() as u32);
                            }
                        }
                        lit_pool.push(IDX_END);
                        o
                    } else {
                        IDX_ARENA
                    };
                    pool[long_fill[v] as usize] = c as u32;
                    pool[long_fill[v] as usize + 1] = ofs;
                    long_fill[v] += 2;
                }
            }
        }
        Self {
            var_ofs,
            pool,
            lit_pool,
        }
    }
}

/// The counting engine.
pub struct Engine<W: CountValue> {
    num_vars: usize,
    // Clause arena: literals flattened; clause c = lits[start[c]..start[c+1]].
    lits: Vec<Lit>,
    start: Vec<u32>,
    // Per-clause counters maintained under assignment.
    n_sat: Vec<u32>,
    n_unassigned: Vec<u32>,
    // Occurrence lists per literal code: clause ids containing that literal.
    occ_start: Vec<u32>,
    occ: Vec<u32>,
    // Assignment state.
    val: Vec<u8>,
    trail: Vec<Lit>,
    // Per-var assignment metadata (valid only while assigned).
    var_level: Vec<u32>,
    var_reason: Vec<Reason>,
    // Current decision level = recursion frame depth (0 = top level).
    cur_level: u32,
    // Learned clause arena (first two literals of each clause are watched).
    learned_lits: Vec<Lit>,
    learned_start: Vec<u32>,
    // Learned units, re-asserted at every branch.
    learned_units: Vec<Lit>,
    // Watch lists per literal code over learned clauses.
    watch: Vec<Vec<u32>>,
    // First conflicting clause seen by assign/propagation.
    conflict: Option<ConflictRef>,
    // 1UIP scratch (epoch-stamped seen flags).
    seen_stamp: Vec<u32>,
    seen_epoch: u32,
    // Projection: projected[v] is true when v is counted/branchable.
    projected: Vec<bool>,
    has_projection: bool,
    weights: WeightTable<W>,
    cache: CompCache<W>,
    // Branching activity (bumped on conflicts, decayed periodically).
    activity: Vec<f64>,
    conflicts_since_decay: u32,
    // Analyzer occurrence index (built once over original clauses).
    idx: AnalyzerIndex,
    // Component-discovery scratch (epoch-stamped, seed-tagged).
    var_epoch: Vec<u32>,
    var_seed: Vec<u32>,
    clause_epoch: Vec<u32>,
    clause_seed: Vec<u32>,
    // Per-clause discovery state within an epoch: 0 = in-comp all-active,
    // 1 = in-comp shortened, 2 = satisfied/skip.
    clause_state: Vec<u8>,
    epoch: u32,
    // Per-var frequency scratch for the current split.
    freq_scratch: Vec<u32>,
    // Tree-decomposition scores (optional branching bias; soundness-neutral).
    td_score: Vec<f64>,
    // Optional deadline, checked every DEADLINE_CHECK_MASK+1 count_comp calls.
    deadline: Option<std::time::Instant>,
    deadline_tick: u32,
    // Original formula contained an empty clause.
    has_empty_clause: bool,
    /// Statistics.
    pub stats: Stats,
}

impl<W: CountValue> Engine<W> {
    /// Build an engine from clauses (signed DIMACS literals), a weight table,
    /// and an optional projection set (1-based var ids).
    ///
    /// Tautological clauses are dropped (satisfied by every assignment);
    /// duplicate literals within a clause are deduplicated.
    pub fn new(
        num_vars: usize,
        clauses: &[Vec<i32>],
        weights: WeightTable<W>,
        show: Option<&[u32]>,
        config: EngineConfig,
    ) -> Self {
        let mut lits: Vec<Lit> = Vec::new();
        let mut start: Vec<u32> = vec![0];
        let mut seen: Vec<i32> = Vec::new();
        let mut has_empty_clause = false;
        for clause in clauses {
            seen.clear();
            let mut tautology = false;
            for &l in clause {
                if seen.contains(&-l) {
                    tautology = true;
                    break;
                }
                if !seen.contains(&l) {
                    seen.push(l);
                }
            }
            if tautology {
                continue;
            }
            if seen.is_empty() {
                has_empty_clause = true;
                continue;
            }
            for &l in &seen {
                lits.push(Lit::from_dimacs(l));
            }
            start.push(lits.len() as u32);
        }
        let n_clauses = start.len() - 1;

        // Occurrence lists (counting sort by literal code).
        let mut occ_start = vec![0u32; num_vars * 2 + 1];
        for l in &lits {
            occ_start[l.code() + 1] += 1;
        }
        for i in 1..occ_start.len() {
            occ_start[i] += occ_start[i - 1];
        }
        let mut occ = vec![0u32; lits.len()];
        let mut fill = occ_start.clone();
        for c in 0..n_clauses {
            for i in start[c] as usize..start[c + 1] as usize {
                let code = lits[i].code();
                occ[fill[code] as usize] = c as u32;
                fill[code] += 1;
            }
        }

        let n_unassigned: Vec<u32> = (0..n_clauses).map(|c| start[c + 1] - start[c]).collect();

        let (projected, has_projection) = match show {
            Some(vars) => {
                let mut p = vec![false; num_vars];
                for &v in vars {
                    p[v as usize - 1] = true;
                }
                let full = p.iter().all(|&x| x);
                (p, !full)
            }
            None => (vec![true; num_vars], false),
        };

        let idx = AnalyzerIndex::build(num_vars, &lits, &start);

        Self {
            num_vars,
            lits,
            start,
            n_sat: vec![0; n_clauses],
            n_unassigned,
            occ_start,
            occ,
            val: vec![UNASSIGNED; num_vars],
            trail: Vec::with_capacity(num_vars),
            var_level: vec![0; num_vars],
            var_reason: vec![Reason::Decision; num_vars],
            cur_level: 0,
            learned_lits: Vec::new(),
            learned_start: vec![0],
            learned_units: Vec::new(),
            watch: vec![Vec::new(); num_vars * 2],
            conflict: None,
            seen_stamp: vec![0; num_vars],
            seen_epoch: 0,
            projected,
            has_projection,
            weights,
            cache: CompCache::new(config.cache_budget_bytes),
            activity: vec![0.0; num_vars],
            conflicts_since_decay: 0,
            idx,
            var_epoch: vec![0; num_vars],
            var_seed: vec![0; num_vars],
            clause_epoch: vec![0; n_clauses],
            clause_seed: vec![0; n_clauses],
            clause_state: vec![0; n_clauses],
            epoch: 0,
            freq_scratch: vec![0; num_vars],
            td_score: Vec::new(),
            deadline: config.deadline,
            deadline_tick: 0,
            has_empty_clause,
            stats: Stats::default(),
        }
    }

    /// Install tree-decomposition branching scores (indexed by 0-based var).
    /// Purely a branching bias; cannot affect soundness.
    pub fn set_td_scores(&mut self, scores: Vec<f64>) {
        debug_assert_eq!(scores.len(), self.num_vars);
        self.td_score = scores;
    }

    #[inline]
    fn clause_lits(&self, c: u32) -> &[Lit] {
        &self.lits[self.start[c as usize] as usize..self.start[c as usize + 1] as usize]
    }

    #[inline]
    fn lit_is_true(&self, l: Lit) -> bool {
        self.val[l.var()] == if l.negated() { VAL_FALSE } else { VAL_TRUE }
    }

    /// Assign a literal: set value, push trail, apply ALL counter updates.
    ///
    /// Returns `false` when some original clause became empty (conflict; the
    /// clause is recorded in `self.conflict`). Counter updates are always
    /// fully applied regardless, keeping `backtrack` exactly symmetric for
    /// every trail literal.
    #[inline]
    fn assign(&mut self, l: Lit, reason: Reason) -> bool {
        debug_assert_eq!(self.val[l.var()], UNASSIGNED);
        self.val[l.var()] = if l.negated() { VAL_FALSE } else { VAL_TRUE };
        self.var_level[l.var()] = self.cur_level;
        self.var_reason[l.var()] = reason;
        self.trail.push(l);
        for i in self.occ_start[l.code()] as usize..self.occ_start[l.code() + 1] as usize {
            let c = self.occ[i] as usize;
            self.n_sat[c] += 1;
        }
        let neg = l.neg();
        let mut ok = true;
        for i in self.occ_start[neg.code()] as usize..self.occ_start[neg.code() + 1] as usize {
            let c = self.occ[i] as usize;
            self.n_unassigned[c] -= 1;
            if self.n_sat[c] == 0 && self.n_unassigned[c] == 0 && ok {
                ok = false;
                self.conflict = Some(ConflictRef::Orig(c as u32));
                self.bump_conflict(c as u32);
            }
        }
        ok
    }

    /// Propagate units from trail position `qhead` to fixpoint, over original
    /// clauses (occurrence counters) AND learned clauses (watched literals).
    ///
    /// Returns `Err(())` on conflict (recorded in `self.conflict`). Counters
    /// stay consistent either way.
    fn propagate_from(&mut self, mut qhead: usize) -> Result<(), ()> {
        // Process literals already on the trail from qhead (the caller
        // assigns the seed literal(s) before calling).
        while qhead < self.trail.len() {
            let lit = self.trail[qhead];
            qhead += 1;
            let neg = lit.neg();
            let occ_range =
                self.occ_start[neg.code()] as usize..self.occ_start[neg.code() + 1] as usize;
            for i in occ_range {
                let c = self.occ[i];
                if self.n_sat[c as usize] == 0 && self.n_unassigned[c as usize] == 1 {
                    let u = self
                        .clause_lits(c)
                        .iter()
                        .copied()
                        .find(|&x| self.val[x.var()] == UNASSIGNED)
                        .expect("clause with n_unassigned==1 has an unassigned literal");
                    if !self.assign(u, Reason::Orig(c)) {
                        self.stats.conflicts += 1;
                        return Err(());
                    }
                }
            }
            if !self.propagate_learned(lit) {
                self.stats.conflicts += 1;
                return Err(());
            }
        }
        Ok(())
    }

    /// Watched-literal propagation over learned clauses for a newly-true
    /// `lit`. Returns `false` on conflict (recorded in `self.conflict`).
    fn propagate_learned(&mut self, lit: Lit) -> bool {
        let neg = lit.neg();
        let mut i = 0;
        while i < self.watch[neg.code()].len() {
            let ci = self.watch[neg.code()][i] as usize;
            let s = self.learned_start[ci] as usize;
            let e = self.learned_start[ci + 1] as usize;
            // Normalize: the falsified watch sits at s+1.
            if self.learned_lits[s] == neg {
                self.learned_lits.swap(s, s + 1);
            }
            debug_assert_eq!(self.learned_lits[s + 1], neg);
            let first = self.learned_lits[s];
            if self.lit_is_true(first) {
                i += 1;
                continue;
            }
            // Find a non-false replacement watch.
            let mut moved = false;
            for j in s + 2..e {
                let cand = self.learned_lits[j];
                if !self.lit_is_true(cand.neg()) {
                    self.learned_lits.swap(s + 1, j);
                    let new_watch = self.learned_lits[s + 1];
                    self.watch[new_watch.code()].push(ci as u32);
                    self.watch[neg.code()].swap_remove(i);
                    moved = true;
                    break;
                }
            }
            if moved {
                continue;
            }
            // No replacement: `first` is unit or the clause conflicts.
            if self.lit_is_true(first.neg()) {
                self.conflict = Some(ConflictRef::Learned(ci as u32));
                return false;
            }
            if self.val[first.var()] == UNASSIGNED
                && !self.assign(first, Reason::Learned(ci as u32))
            {
                return false;
            }
            i += 1;
        }
        true
    }

    /// Undo the trail down to `mark`, reversing counter updates.
    fn backtrack(&mut self, mark: usize) {
        while self.trail.len() > mark {
            let lit = self.trail.pop().expect("trail is non-empty above mark");
            self.val[lit.var()] = UNASSIGNED;
            for i in self.occ_start[lit.code()] as usize..self.occ_start[lit.code() + 1] as usize {
                let c = self.occ[i] as usize;
                self.n_sat[c] -= 1;
            }
            let neg = lit.neg();
            for i in self.occ_start[neg.code()] as usize..self.occ_start[neg.code() + 1] as usize {
                let c = self.occ[i] as usize;
                self.n_unassigned[c] += 1;
            }
        }
    }

    fn conflict_ref_lits(&self, r: ConflictRef) -> Vec<Lit> {
        match r {
            ConflictRef::Orig(c) => self.clause_lits(c).to_vec(),
            ConflictRef::Learned(ci) => {
                let s = self.learned_start[ci as usize] as usize;
                let e = self.learned_start[ci as usize + 1] as usize;
                self.learned_lits[s..e].to_vec()
            }
        }
    }

    fn reason_lits(&self, r: Reason) -> Vec<Lit> {
        match r {
            Reason::Decision => Vec::new(),
            Reason::Orig(c) => self.clause_lits(c).to_vec(),
            Reason::Learned(ci) => {
                let s = self.learned_start[ci as usize] as usize;
                let e = self.learned_start[ci as usize + 1] as usize;
                self.learned_lits[s..e].to_vec()
            }
        }
    }

    /// Number of learned (non-unit) clauses stored.
    fn learned_count(&self) -> usize {
        self.learned_start.len() - 1
    }

    /// 1UIP conflict analysis over the trail; learns the asserting clause.
    ///
    /// No backjumping: the caller books the zero branch and flips in place
    /// (sharpSAT discipline). Learning is optional — bailing out at any point
    /// is sound — so all degenerate cases simply return.
    fn analyze_and_learn(&mut self) {
        let Some(cref) = self.conflict.take() else {
            return;
        };
        if self.learned_count() >= MAX_LEARNED_CLAUSES {
            return;
        }
        let conflict_level = self.cur_level;
        if conflict_level == 0 {
            return;
        }
        self.seen_epoch += 1;
        let epoch = self.seen_epoch;
        let mut counter: u32 = 0;
        let mut lower: Vec<Lit> = Vec::new();
        let mut cursor = self.trail.len();
        let mut clause = self.conflict_ref_lits(cref);
        let mut skip_var = usize::MAX;
        let uip: Lit = loop {
            for &l in &clause {
                let v = l.var();
                if v == skip_var || self.seen_stamp[v] == epoch {
                    continue;
                }
                debug_assert_ne!(self.val[v], UNASSIGNED);
                let lv = self.var_level[v];
                if lv == 0 {
                    // Top-level entailed (includes re-asserted learned
                    // units): dropping the literal strengthens the clause
                    // soundly.
                    continue;
                }
                self.seen_stamp[v] = epoch;
                self.activity[v] += 1.0;
                if lv == conflict_level {
                    counter += 1;
                } else {
                    lower.push(l);
                }
            }
            if counter == 0 {
                // All conflict literals were top-level or lower-level: no
                // current-level pivot to resolve on. Bail (sound).
                return;
            }
            loop {
                if cursor == 0 {
                    return;
                }
                cursor -= 1;
                let v = self.trail[cursor].var();
                if self.seen_stamp[v] == epoch && self.var_level[v] == conflict_level {
                    break;
                }
            }
            let v = self.trail[cursor].var();
            if counter == 1 {
                break self.trail[cursor].neg();
            }
            counter -= 1;
            let reason = self.var_reason[v];
            if reason == Reason::Decision {
                // Cannot resolve past a decision with pivots remaining;
                // degenerate (can arise from probing artifacts). Bail.
                return;
            }
            clause = self.reason_lits(reason);
            skip_var = v;
        };
        let mut new_clause = Vec::with_capacity(1 + lower.len());
        new_clause.push(uip);
        new_clause.extend(lower);
        self.attach_learned(new_clause);
    }

    /// Store a learned clause: units go to the re-assertion list; longer
    /// clauses join the watched arena (position 0 = asserting literal,
    /// position 1 = a deepest-level other literal).
    fn attach_learned(&mut self, mut clause: Vec<Lit>) {
        if clause.is_empty() {
            return;
        }
        if clause.len() == 1 {
            self.learned_units.push(clause[0]);
            self.stats.learned_units += 1;
            return;
        }
        let mut best = 1;
        for j in 2..clause.len() {
            if self.var_level[clause[j].var()] > self.var_level[clause[best].var()] {
                best = j;
            }
        }
        clause.swap(1, best);
        let ci = self.learned_count() as u32;
        self.learned_lits.extend_from_slice(&clause);
        self.learned_start.push(self.learned_lits.len() as u32);
        self.watch[clause[0].code()].push(ci);
        self.watch[clause[1].code()].push(ci);
        self.stats.learned_clauses += 1;
    }

    /// Reduce the learned-clause DB when it grows past the trigger: keep
    /// clauses that are current trail reasons (mandatory — 1UIP needs them),
    /// short clauses (<=3 literals), and the most recent half of the rest.
    /// Rebuilds the arena and watch lists and remaps trail reasons.
    ///
    /// Soundness-neutral: learned clauses are optional accelerators, and
    /// re-watching positions 0/1 after reduction only costs missed (lazily
    /// repaired) propagations, never wrong ones.
    fn reduce_learned_db(&mut self) {
        const REDUCE_TRIGGER: usize = 32_768;
        if self.learned_count() < REDUCE_TRIGGER || self.conflict.is_some() {
            return;
        }
        // Live reasons on the trail must survive.
        let mut is_reason = vec![false; self.learned_count()];
        for l in &self.trail {
            if let Reason::Learned(ci) = self.var_reason[l.var()] {
                if (ci as usize) < is_reason.len() {
                    is_reason[ci as usize] = true;
                }
            }
        }
        let n = self.learned_count();
        let recent_floor = n / 2;
        let mut keep: Vec<u32> = Vec::with_capacity(n / 2 + n / 8);
        for ci in 0..n {
            let len = (self.learned_start[ci + 1] - self.learned_start[ci]) as usize;
            if is_reason[ci] || len <= 3 || ci >= recent_floor {
                keep.push(ci as u32);
            }
        }
        // Rebuild arena + remap.
        let mut new_lits: Vec<Lit> = Vec::with_capacity(self.learned_lits.len() / 2);
        let mut new_start: Vec<u32> = Vec::with_capacity(keep.len() + 1);
        new_start.push(0);
        let mut remap: Vec<u32> = vec![u32::MAX; n];
        for (new_ci, &old_ci) in keep.iter().enumerate() {
            let s = self.learned_start[old_ci as usize] as usize;
            let e = self.learned_start[old_ci as usize + 1] as usize;
            new_lits.extend_from_slice(&self.learned_lits[s..e]);
            new_start.push(new_lits.len() as u32);
            remap[old_ci as usize] = new_ci as u32;
        }
        for i in 0..self.trail.len() {
            let v = self.trail[i].var();
            if let Reason::Learned(ci) = self.var_reason[v] {
                let new_ci = remap[ci as usize];
                debug_assert_ne!(new_ci, u32::MAX, "live reason must be kept");
                self.var_reason[v] = Reason::Learned(new_ci);
            }
        }
        for w in &mut self.watch {
            w.clear();
        }
        for ci in 0..new_start.len() - 1 {
            let s = new_start[ci] as usize;
            self.watch[new_lits[s].code()].push(ci as u32);
            self.watch[new_lits[s + 1].code()].push(ci as u32);
        }
        self.stats.learned_reduced += (n - keep.len()) as u64;
        self.learned_lits = new_lits;
        self.learned_start = new_start;
    }

    /// Re-assert all learned units at the current branch (level 0 semantics:
    /// they are globally entailed). Returns `false` on contradiction.
    fn assert_learned_units(&mut self) -> bool {
        let saved = self.cur_level;
        self.cur_level = 0;
        let mut ok = true;
        for i in 0..self.learned_units.len() {
            let u = self.learned_units[i];
            if self.lit_is_true(u) {
                continue;
            }
            if self.lit_is_true(u.neg()) {
                self.conflict = None;
                ok = false;
                break;
            }
            if !self.assign(u, Reason::Decision) {
                ok = false;
                break;
            }
        }
        self.cur_level = saved;
        ok
    }

    fn bump_conflict(&mut self, c: u32) {
        for i in self.start[c as usize] as usize..self.start[c as usize + 1] as usize {
            let v = self.lits[i].var();
            self.activity[v] += 1.0;
        }
        self.conflicts_since_decay += 1;
        if self.conflicts_since_decay >= 128 {
            self.conflicts_since_decay = 0;
            for a in &mut self.activity {
                *a *= 0.5;
            }
        }
    }

    /// Discover connected components among `candidate_vars` (unassigned only),
    /// via BFS over active (unsatisfied) clauses, using the analyzer index.
    ///
    /// `parent_clauses` must be the (sorted) active clause ids of the parent
    /// component — components are emitted by rescanning the parent's lists,
    /// so children inherit sorted order without sorting.
    ///
    /// Precondition: BCP fixpoint (the binary-clause shortcut relies on it).
    fn split_components(&mut self, candidate_vars: &[u32], parent_clauses: &[u32]) -> Vec<Comp> {
        self.epoch += 1;
        let epoch = self.epoch;
        let mut comps: Vec<Comp> = Vec::new();
        let mut stack: Vec<u32> = Vec::new();
        let mut buf: Vec<u32> = Vec::new(); // unassigned vars of the clause under scan
        for &seed in candidate_vars {
            let sv = seed as usize;
            if self.val[sv] != UNASSIGNED || self.var_epoch[sv] == epoch {
                continue;
            }
            let seed_tag = comps.len() as u32;
            self.var_epoch[sv] = epoch;
            self.var_seed[sv] = seed_tag;
            self.freq_scratch[sv] = 0;
            stack.clear();
            stack.push(seed);
            let mut n_vars = 1u32;
            let mut proj_count = u32::from(self.projected[sv]);
            while let Some(x) = stack.pop() {
                let xs = x as usize;
                let mut p = self.idx.var_ofs[xs] as usize;
                // Binary section: post-BCP, an active binary clause has both
                // literals unassigned; an assigned neighbor implies the
                // clause is satisfied (else it would have propagated).
                loop {
                    let entry = self.idx.pool[p];
                    if entry == IDX_END {
                        break;
                    }
                    p += 1;
                    let other = Lit(entry >> 1);
                    let y = other.var();
                    if self.val[y] != UNASSIGNED {
                        debug_assert!(
                            self.lit_is_true(other),
                            "active binary with a falsified literal escaped BCP"
                        );
                        continue;
                    }
                    self.freq_scratch[xs] += 1;
                    if self.var_epoch[y] != epoch {
                        self.var_epoch[y] = epoch;
                        self.var_seed[y] = seed_tag;
                        self.freq_scratch[y] = 0;
                        proj_count += u32::from(self.projected[y]);
                        n_vars += 1;
                        stack.push(y as u32);
                    }
                }
                p += 1;
                // Long section: (clause_id, lits_ofs) pairs over a private
                // copy of the clause's other literals.
                loop {
                    let c = self.idx.pool[p];
                    if c == IDX_END {
                        break;
                    }
                    let ofs = self.idx.pool[p + 1];
                    p += 2;
                    let cu = c as usize;
                    if self.clause_epoch[cu] == epoch {
                        continue;
                    }
                    self.clause_epoch[cu] = epoch;
                    // Scan the clause: satisfied => skip; else collect
                    // unassigned vars and detect falsified literals.
                    buf.clear();
                    let mut satisfied = false;
                    let mut shortened = false;
                    if ofs == IDX_ARENA {
                        for i in self.start[cu] as usize..self.start[cu + 1] as usize {
                            let l = self.lits[i];
                            if l.var() == xs {
                                continue;
                            }
                            match self.val[l.var()] {
                                UNASSIGNED => buf.push(l.var() as u32),
                                _ => {
                                    if self.lit_is_true(l) {
                                        satisfied = true;
                                        break;
                                    }
                                    shortened = true;
                                }
                            }
                        }
                    } else {
                        let mut q = ofs as usize;
                        loop {
                            let code = self.idx.lit_pool[q];
                            if code == IDX_END {
                                break;
                            }
                            q += 1;
                            let l = Lit(code);
                            match self.val[l.var()] {
                                UNASSIGNED => buf.push(l.var() as u32),
                                _ => {
                                    if self.lit_is_true(l) {
                                        satisfied = true;
                                        break;
                                    }
                                    shortened = true;
                                }
                            }
                        }
                    }
                    if satisfied {
                        self.clause_state[cu] = 2;
                        continue;
                    }
                    self.clause_state[cu] = u8::from(shortened);
                    self.clause_seed[cu] = seed_tag;
                    self.freq_scratch[xs] += 1;
                    for &y in &buf {
                        let yu = y as usize;
                        if self.var_epoch[yu] != epoch {
                            self.var_epoch[yu] = epoch;
                            self.var_seed[yu] = seed_tag;
                            self.freq_scratch[yu] = 1;
                            proj_count += u32::from(self.projected[yu]);
                            n_vars += 1;
                            stack.push(y);
                        } else {
                            self.freq_scratch[yu] += 1;
                        }
                    }
                }
            }
            self.stats.components += 1;
            comps.push(Comp {
                vars: Vec::with_capacity(n_vars as usize),
                clauses: Vec::new(),
                key_clauses: Vec::new(),
                freq: Vec::with_capacity(n_vars as usize),
                proj_count,
            });
        }
        if comps.is_empty() {
            return comps;
        }
        // Emit vars (and freq) in parent order — children stay sorted.
        for &v in candidate_vars {
            let vu = v as usize;
            if self.val[vu] == UNASSIGNED && self.var_epoch[vu] == epoch {
                let comp = &mut comps[self.var_seed[vu] as usize];
                comp.vars.push(v);
                comp.freq.push(self.freq_scratch[vu]);
            }
        }
        // Emit clauses in parent order.
        for &c in parent_clauses {
            let cu = c as usize;
            if self.clause_epoch[cu] == epoch && self.clause_state[cu] != 2 {
                let comp = &mut comps[self.clause_seed[cu] as usize];
                comp.clauses.push(c);
                if self.clause_state[cu] == 1 {
                    comp.key_clauses.push(c);
                }
            }
        }
        comps
    }

    /// Existential SAT check on a projection-free component via `ay-sat`.
    ///
    /// `comp.clauses` carries the active long clauses; active binary clauses
    /// are reconstructed from the analyzer index (post-BCP, an active binary
    /// has both literals unassigned, so it is active iff both vars are in the
    /// component).
    fn sat_oracle(&mut self, comp: &Comp) -> Result<bool, CountAbort> {
        self.stats.sat_oracle_calls += 1;
        let mut solver = ay_sat::Solver::new(comp.vars.len());
        let to_oracle_lit = |comp: &Comp, l: Lit| -> ay_sat::Literal {
            let idx = comp
                .vars
                .binary_search(&(l.var() as u32))
                .expect("component clause variable is in the component");
            let var = ay_sat::Variable::new(u32::try_from(idx).expect("fits u32"));
            if l.negated() {
                ay_sat::Literal::negative(var)
            } else {
                ay_sat::Literal::positive(var)
            }
        };
        // Long clauses.
        for &c in &comp.clauses {
            let mut clause: Vec<ay_sat::Literal> = Vec::new();
            for &l in self.clause_lits(c) {
                if self.val[l.var()] != UNASSIGNED {
                    // Falsified literal (an active clause has no true lits).
                    continue;
                }
                clause.push(to_oracle_lit(comp, l));
            }
            if !solver.add_clause(clause) {
                return Ok(false);
            }
        }
        // Binary clauses, emitted once from the lower-numbered side.
        for &v in &comp.vars {
            let vu = v as usize;
            let mut p = self.idx.var_ofs[vu] as usize;
            loop {
                let entry = self.idx.pool[p];
                if entry == IDX_END {
                    break;
                }
                p += 1;
                let other = Lit(entry >> 1);
                if other.var() <= vu || self.val[other.var()] != UNASSIGNED {
                    continue;
                }
                let own = Lit::new(v, entry & 1 == 1);
                let clause = vec![to_oracle_lit(comp, own), to_oracle_lit(comp, other)];
                if !solver.add_clause(clause) {
                    return Ok(false);
                }
            }
        }
        let result = solver.solve();
        match result.result() {
            ay_sat::SatResult::Sat(_) => Ok(true),
            ay_sat::SatResult::Unsat(_) => Ok(false),
            _ => Err(CountAbort::OracleUnknown),
        }
    }

    /// Pick the branching variable in a component: the projection variable
    /// with the highest VSADS-style score (activity + occurrence count in the
    /// component's active clauses).
    fn pick_var(&mut self, comp: &Comp) -> u32 {
        let mut best: Option<(f64, u32)> = None;
        for (&v, &freq) in comp.vars.iter().zip(&comp.freq) {
            let vu = v as usize;
            if self.val[vu] != UNASSIGNED || !self.projected[vu] {
                continue;
            }
            // VSADS + TD (sharpsat-td): freq + 10*activity + td_score.
            let td = self.td_score.get(vu).copied().unwrap_or(0.0);
            let score = 10.0 * self.activity[vu] + f64::from(freq) + td;
            if best.map(|(s, _)| score > s).unwrap_or(true) {
                best = Some((score, v));
            }
        }
        best.expect("component with projection variables has a branchable variable")
            .1
    }

    /// Count a component (recursive).
    fn count_comp(&mut self, comp: &Comp, depth: u32) -> Result<W, CountAbort> {
        if depth > self.stats.max_depth {
            self.stats.max_depth = depth;
        }
        self.deadline_tick = self.deadline_tick.wrapping_add(1);
        if self.deadline_tick & 0x3ff == 0 {
            if let Some(deadline) = self.deadline {
                if std::time::Instant::now() >= deadline {
                    return Err(CountAbort::Deadline);
                }
            }
            if ay_sys::process_memory_exceeded() {
                return Err(CountAbort::Memory);
            }
            self.reduce_learned_db();
        }
        // Base: a FREE variable is exactly a singleton component with no
        // clauses (comp.clauses excludes binaries, but a multi-var component
        // is connected by definition, so only singletons can be clause-free).
        if comp.vars.len() == 1 && comp.clauses.is_empty() {
            let v = comp.vars[0] as usize;
            return Ok(if self.projected[v] {
                self.weights.free_factor(v).clone()
            } else {
                W::one()
            });
        }
        let key = CompKey::encode(&comp.vars, &comp.key_clauses);
        if let Some(v) = self.cache.get(&key) {
            self.stats.cache_hits += 1;
            return Ok(v);
        }
        // Projection-free component: existential SAT check, in-engine (a
        // fresh external solver per leaf is ruinously expensive; the DPLL
        // below shares the trail, learned clauses, cache, and the watermark
        // purge discipline — TRUE results are model-witnessed and
        // context-free, FALSE results are purged with the enclosing zero
        // branch exactly like count values).
        let value = if self.has_projection && comp.proj_count == 0 {
            if self.sat_check_comp(comp, depth)? {
                W::one()
            } else {
                W::zero()
            }
        } else {
            // Branch on the best projection variable.
            let bv = self.pick_var(comp);
            self.stats.decisions += 1;
            let mut total = W::zero();
            for negated in [false, true] {
                let lit = Lit::new(bv, negated);
                let trail_mark = self.trail.len();
                // Watermark for the pollution purge: every cache entry
                // created inside a zero branch is deleted before the branch
                // exits (see learning-pollution-spec.md §4.4).
                let cache_mark = self.cache.stamp();
                self.cur_level = depth;
                self.conflict = None;
                let mut ok = self.assign(lit, Reason::Decision);
                if ok {
                    ok = self.assert_learned_units();
                }
                if ok {
                    ok = self.propagate_from(trail_mark).is_ok();
                }
                let mut branch = W::zero();
                if !ok {
                    self.stats.conflicts += 1;
                    self.analyze_and_learn();
                } else {
                    branch = W::one();
                    if self.weights.is_weighted() {
                        // Weight product of projected literals assigned in
                        // this step whose var belongs to THIS component
                        // (cross-component propagations via learned clauses
                        // are integrated by their own component's count —
                        // taking them here would double-count).
                        for i in trail_mark..self.trail.len() {
                            let l = self.trail[i];
                            let v = l.var();
                            if self.projected[v] && comp.vars.binary_search(&(v as u32)).is_ok() {
                                if let Some(w) = self.weights.lit_weight(l.code()) {
                                    branch.mul_assign(w);
                                }
                            }
                        }
                    }
                    if !branch.is_zero() {
                        let mut subs = self.split_components(&comp.vars, &comp.clauses);
                        // Smallest component first: fail fast on zeros and
                        // keep the recursion window tight. Consumed by value
                        // so each sibling's clause/var buffers are freed as
                        // soon as it is counted (the sibling Vecs sum to
                        // ~the parent component at EVERY recursion level).
                        subs.sort_by_key(|c| c.vars.len());
                        for sub in subs {
                            let c = self.count_comp(&sub, depth + 1)?;
                            if c.is_zero() {
                                branch = W::zero();
                                break;
                            }
                            branch.mul_assign(&c);
                        }
                        // Restore this frame's level after deeper frames.
                        self.cur_level = depth;
                    }
                }
                if branch.is_zero() {
                    // THE pollution purge: any zero branch (conflict, zero
                    // sub, genuine unsat) drops every entry it created.
                    self.cache.purge_since(cache_mark);
                }
                total.add_assign(&branch);
                self.backtrack(trail_mark);
            }
            total
        };
        self.stats.cache_stores += 1;
        self.cache.put(key, value.clone());
        Ok(value)
    }

    /// In-engine existential SAT check for a projection-free component:
    /// DPLL over the component's variables with the shared trail, BCP
    /// (originals + learned), component splitting, and cache. Returns as
    /// soon as one satisfying decomposition is found.
    fn sat_check_comp(&mut self, comp: &Comp, depth: u32) -> Result<bool, CountAbort> {
        self.deadline_tick = self.deadline_tick.wrapping_add(1);
        if self.deadline_tick & 0x3ff == 0 {
            if let Some(deadline) = self.deadline {
                if std::time::Instant::now() >= deadline {
                    return Err(CountAbort::Deadline);
                }
            }
            if ay_sys::process_memory_exceeded() {
                return Err(CountAbort::Memory);
            }
            // Same DB-reduction tick as count_comp: a run stuck in a
            // projection-free SAT subtree (the mode independent support
            // enables) otherwise grows the learned DB straight to the hard
            // cap with no reduction ever firing.
            self.reduce_learned_db();
        }
        if comp.clauses.is_empty() {
            // Only binaries/none among unassigned vars... a clause-free
            // component is satisfiable by definition (no constraints).
            return Ok(true);
        }
        let key = CompKey::encode(&comp.vars, &comp.key_clauses);
        if let Some(v) = self.cache.get(&key) {
            self.stats.cache_hits += 1;
            return Ok(!v.is_zero());
        }
        // Branch on any variable (VSADS + TD, mirroring pick_var; projection
        // is irrelevant inside a projection-free subtree). The TD term was
        // missing here, so projected-mode SAT leaves lost the decomposition
        // guidance the count path gets — order is soundness-neutral but
        // decides whether dense instances decompose in time.
        let mut best: Option<(f64, u32)> = None;
        for (&v, &freq) in comp.vars.iter().zip(&comp.freq) {
            let vu = v as usize;
            if self.val[vu] != UNASSIGNED {
                continue;
            }
            let td = self.td_score.get(vu).copied().unwrap_or(0.0);
            let score = 10.0 * self.activity[vu] + f64::from(freq) + td;
            if best.map(|(s, _)| score > s).unwrap_or(true) {
                best = Some((score, v));
            }
        }
        let Some((_, bv)) = best else {
            // Unreachable at BCP fixpoint: an active clause always has an
            // unassigned literal, and comp.vars come from the same split.
            debug_assert!(false, "sat_check_comp: no unassigned var");
            return Ok(true);
        };
        self.stats.decisions += 1;
        let mut sat = false;
        let cache_mark = self.cache.stamp();
        for negated in [false, true] {
            let lit = Lit::new(bv, negated);
            let trail_mark = self.trail.len();
            self.cur_level = depth;
            self.conflict = None;
            let mut ok = self.assign(lit, Reason::Decision);
            if ok {
                ok = self.assert_learned_units();
            }
            if ok {
                ok = self.propagate_from(trail_mark).is_ok();
            }
            if !ok {
                self.stats.conflicts += 1;
                self.analyze_and_learn();
            } else {
                let mut subs = self.split_components(&comp.vars, &comp.clauses);
                subs.sort_by_key(|c| c.vars.len());
                let mut all_sat = true;
                // By value: free each sibling's buffers as soon as checked.
                for sub in subs {
                    let sub_ok = if sub.clauses.is_empty() {
                        true
                    } else {
                        self.sat_check_comp(&sub, depth + 1)?
                    };
                    if !sub_ok {
                        all_sat = false;
                        break;
                    }
                }
                sat = all_sat;
            }
            self.backtrack(trail_mark);
            self.cur_level = depth;
            if sat {
                break;
            }
        }
        if !sat {
            // A FALSE verdict may be contamination-driven (learned-clause
            // conflicts): purge everything created inside this check, same
            // watermark discipline as count branches.
            self.cache.purge_since(cache_mark);
        }
        self.stats.cache_stores += 1;
        self.cache.put(key, if sat { W::one() } else { W::zero() });
        Ok(sat)
    }

    /// Count the whole formula. The result is exact; zero for weighted
    /// instances does not by itself imply unsatisfiability (zero weights).
    pub fn count(&mut self) -> Result<W, CountAbort> {
        // Top level: original units, BCP, and failed-literal probing (all
        // entailment-based, hence sound for every track).
        if !self.establish_top_level() {
            return Ok(W::zero());
        }

        // Weight product of top-level forced projected literals.
        let mut result = W::one();
        if self.weights.is_weighted() {
            for i in 0..self.trail.len() {
                let l = self.trail[i];
                if self.projected[l.var()] {
                    if let Some(w) = self.weights.lit_weight(l.code()) {
                        result.mul_assign(w);
                    }
                }
            }
            if result.is_zero() {
                return Ok(W::zero());
            }
        }

        // Decompose everything reachable from unassigned vars.
        let all_vars: Vec<u32> = (0..self.num_vars as u32).collect();
        let long_clauses: Vec<u32> = (0..self.n_sat.len() as u32)
            .filter(|&c| self.start[c as usize + 1] - self.start[c as usize] >= 3)
            .collect();
        let comps = self.split_components(&all_vars, &long_clauses);
        for comp in &comps {
            let c = self.count_comp(comp, 1)?;
            if c.is_zero() {
                self.sync_cache_stats();
                return Ok(W::zero());
            }
            result.mul_assign(&c);
        }
        self.sync_cache_stats();
        Ok(result)
    }

    /// Establish the top level: original units, BCP, failed-literal probing.
    /// Returns `false` when the formula is proved unsatisfiable. Idempotent.
    pub(crate) fn establish_top_level(&mut self) -> bool {
        if self.has_empty_clause {
            return false;
        }
        let mark = self.trail.len();
        for c in 0..self.n_sat.len() as u32 {
            if self.n_sat[c as usize] == 0 && self.n_unassigned[c as usize] == 1 {
                let u = self
                    .clause_lits(c)
                    .iter()
                    .copied()
                    .find(|&x| self.val[x.var()] == UNASSIGNED);
                if let Some(u) = u {
                    if !self.assign(u, Reason::Orig(c)) {
                        self.stats.conflicts += 1;
                        return false;
                    }
                }
            }
        }
        if self.propagate_from(mark).is_err() {
            return false;
        }
        self.probe_failed_literals()
    }

    /// Assume `lits` (in order) at the top level with propagation, report
    /// whether a conflict was reached, then restore the previous state.
    ///
    /// Returns `(conflict, first_implied)` where `first_implied` is the index
    /// of the first assumed literal found already TRUE under the propagation
    /// of the previous assumptions (for vivification), if any.
    pub(crate) fn probe_assume(&mut self, lits: &[Lit]) -> (bool, Option<usize>) {
        let mark = self.trail.len();
        let mut conflict = false;
        let mut first_implied = None;
        for (i, &l) in lits.iter().enumerate() {
            if self.lit_is_true(l.neg()) {
                // Assuming l is contradicted: conflict.
                conflict = true;
                break;
            }
            if self.lit_is_true(l) {
                // Already implied.
                if first_implied.is_none() {
                    first_implied = Some(i);
                }
                continue;
            }
            if !self.assign(l, Reason::Decision)
                || self.propagate_from(self.trail.len() - 1).is_err()
            {
                conflict = true;
                break;
            }
        }
        self.backtrack(mark);
        (conflict, first_implied)
    }

    /// Extract the residual formula at the current (top) level: fixed
    /// literals plus active clauses restricted to unassigned literals.
    pub(crate) fn extract_residual(&self) -> (Vec<i32>, Vec<Vec<i32>>) {
        let fixed: Vec<i32> = self
            .trail
            .iter()
            .map(|l| {
                let v = l.var() as i32 + 1;
                if l.negated() {
                    -v
                } else {
                    v
                }
            })
            .collect();
        let mut clauses = Vec::new();
        for c in 0..self.n_sat.len() as u32 {
            if self.n_sat[c as usize] > 0 {
                continue;
            }
            let residual: Vec<i32> = self
                .clause_lits(c)
                .iter()
                .filter(|l| self.val[l.var()] == UNASSIGNED)
                .map(|l| {
                    let v = l.var() as i32 + 1;
                    if l.negated() {
                        -v
                    } else {
                        v
                    }
                })
                .collect();
            debug_assert!(!residual.is_empty(), "empty active clause at top level");
            clauses.push(residual);
        }
        (fixed, clauses)
    }

    #[inline]
    pub(crate) fn lit_from_dimacs(l: i32) -> Lit {
        Lit::from_dimacs(l)
    }

    fn sync_cache_stats(&mut self) {
        self.stats.cache_evictions = self.cache.evictions;
        self.stats.cache_purged = self.cache.purged;
    }

    /// Failed-literal probing at the top level, to fixpoint (bounded).
    /// Returns `false` when the formula is proved unsatisfiable.
    fn probe_failed_literals(&mut self) -> bool {
        const MAX_ROUNDS: u32 = 5;
        for _ in 0..MAX_ROUNDS {
            let mut progressed = false;
            for v in 0..self.num_vars as u32 {
                if self.val[v as usize] != UNASSIGNED {
                    continue;
                }
                for negated in [false, true] {
                    if self.val[v as usize] != UNASSIGNED {
                        break;
                    }
                    let lit = Lit::new(v, negated);
                    let mark = self.trail.len();
                    let ok =
                        self.assign(lit, Reason::Decision) && self.propagate_from(mark).is_ok();
                    self.backtrack(mark);
                    if !ok {
                        // ¬lit is entailed: assert it permanently.
                        let ok2 = self.assign(lit.neg(), Reason::Decision)
                            && self.propagate_from(self.trail.len() - 1).is_ok();
                        if !ok2 {
                            return false;
                        }
                        self.stats.failed_literals += 1;
                        progressed = true;
                    }
                }
            }
            if !progressed {
                break;
            }
        }
        true
    }

    /// Plain satisfiability of the original formula (for the `s` line on
    /// weighted instances whose weighted count is zero). Must be called on a
    /// quiescent engine (top-level trail only).
    pub fn formula_is_sat(&mut self) -> Result<bool, CountAbort> {
        if self.has_empty_clause {
            return Ok(false);
        }
        let comp = Comp {
            vars: (0..self.num_vars as u32)
                .filter(|&v| self.val[v as usize] == UNASSIGNED)
                .collect(),
            // Long clauses only: the oracle reconstructs active binaries
            // from the analyzer index over the component's variables.
            clauses: (0..self.n_sat.len() as u32)
                .filter(|&c| {
                    self.n_sat[c as usize] == 0
                        && self.start[c as usize + 1] - self.start[c as usize] >= 3
                })
                .collect(),
            key_clauses: Vec::new(),
            freq: Vec::new(),
            proj_count: 0,
        };
        self.sat_oracle(&comp)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;

    fn count_mc(num_vars: usize, clauses: &[Vec<i32>]) -> BigUint {
        let mut engine: Engine<BigUint> = Engine::new(
            num_vars,
            clauses,
            WeightTable::unweighted(),
            None,
            EngineConfig::default(),
        );
        engine.count().expect("count succeeds")
    }

    /// Brute-force reference counter.
    fn brute_force(num_vars: usize, clauses: &[Vec<i32>], show: Option<&[u32]>) -> u64 {
        let mut count = 0u64;
        let mut seen_proj = std::collections::HashSet::new();
        for m in 0..(1u64 << num_vars) {
            let sat = clauses.iter().all(|cl| {
                cl.iter().any(|&l| {
                    let v = l.unsigned_abs() as usize - 1;
                    let bit = (m >> v) & 1 == 1;
                    if l > 0 {
                        bit
                    } else {
                        !bit
                    }
                })
            });
            if !sat {
                continue;
            }
            match show {
                None => count += 1,
                Some(vars) => {
                    let key: Vec<bool> = vars.iter().map(|&v| (m >> (v - 1)) & 1 == 1).collect();
                    if seen_proj.insert(key) {
                        count += 1;
                    }
                }
            }
        }
        count
    }

    #[test]
    fn counts_spec_example_1() {
        // {{-1,-2},{2,3,-4},{4,5},{4,6}} over 6 vars has 22 models.
        let clauses = vec![vec![-1, -2], vec![2, 3, -4], vec![4, 5], vec![4, 6]];
        assert_eq!(count_mc(6, &clauses), BigUint::from(22u32));
    }

    #[test]
    fn counts_empty_formula() {
        assert_eq!(count_mc(10, &[]), BigUint::from(1024u32));
    }

    #[test]
    fn counts_unsat() {
        let clauses = vec![vec![1], vec![-1]];
        assert_eq!(count_mc(1, &clauses), BigUint::from(0u32));
    }

    #[test]
    fn counts_single_clause() {
        // x1 ∨ x2 over 2 vars: 3 models.
        assert_eq!(count_mc(2, &[vec![1, 2]]), BigUint::from(3u32));
    }

    #[test]
    fn counts_disconnected_components() {
        // (x1∨x2) and (x3∨x4): 3*3 = 9.
        assert_eq!(count_mc(4, &[vec![1, 2], vec![3, 4]]), BigUint::from(9u32));
    }

    #[test]
    fn counts_projected_spec_example_4() {
        // Projection {1,2} of example 1's formula: 3 projected models.
        let clauses = vec![vec![-1, -2], vec![2, 3, -4], vec![4, 5], vec![4, 6]];
        let mut engine: Engine<BigUint> = Engine::new(
            6,
            &clauses,
            WeightTable::unweighted(),
            Some(&[1, 2]),
            EngineConfig::default(),
        );
        assert_eq!(engine.count().unwrap(), BigUint::from(3u32));
    }

    #[test]
    fn matches_brute_force_on_random_formulas() {
        // Deterministic pseudo-random formulas cross-checked against brute
        // force, unprojected and projected (includes unit clauses, duplicate
        // literals, and small tautologies by construction).
        let mut state = 0x9e3779b97f4a7c15u64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for trial in 0..60 {
            let num_vars = 3 + (next() % 10) as usize; // 3..12
            let num_clauses = 2 + (next() % 24) as usize;
            let mut clauses = Vec::new();
            for _ in 0..num_clauses {
                let len = 1 + (next() % 3) as usize;
                let mut cl = Vec::new();
                for _ in 0..len {
                    let v = 1 + (next() % num_vars as u64) as i32;
                    let sign = if next() % 2 == 0 { 1 } else { -1 };
                    cl.push(v * sign);
                }
                clauses.push(cl);
            }
            let expected = brute_force(num_vars, &clauses, None);
            let got = count_mc(num_vars, &clauses);
            assert_eq!(
                got,
                BigUint::from(expected),
                "trial {trial}: mc mismatch on {num_vars} vars {clauses:?}"
            );
            // Projected variant: first half of the variables.
            let show: Vec<u32> = (1..=(num_vars as u32).div_ceil(2)).collect();
            let expected_p = brute_force(num_vars, &clauses, Some(&show));
            let mut engine: Engine<BigUint> = Engine::new(
                num_vars,
                &clauses,
                WeightTable::unweighted(),
                Some(&show),
                EngineConfig::default(),
            );
            let got_p = engine.count().expect("projected count succeeds");
            assert_eq!(
                got_p,
                BigUint::from(expected_p),
                "trial {trial}: pmc mismatch on {num_vars} vars show {show:?} {clauses:?}"
            );
        }
    }

    #[test]
    fn weighted_count_matches_manual() {
        use num_rational::BigRational;
        // Formula: (x1) with w(x1)=0.4, w(-x1)=0.6 over 2 vars (x2 free,
        // weights 1 each → free factor 2). WMC = 0.4 * 2 = 0.8.
        let rat = |n: i64, d: i64| BigRational::new(n.into(), d.into());
        let weights = vec![rat(2, 5), rat(3, 5), rat(1, 1), rat(1, 1)];
        let mut engine: Engine<BigRational> = Engine::new(
            2,
            &[vec![1]],
            WeightTable::weighted(weights),
            None,
            EngineConfig::default(),
        );
        assert_eq!(engine.count().unwrap(), rat(4, 5));
    }

    #[test]
    fn weighted_negative_weights() {
        use num_rational::BigRational;
        // (x1 ∨ x2), w(x1)=-1/2, w(-x1)=3/2, x2 unweighted (1,1).
        // Models: (T,T)=-1/2, (T,F)=-1/2, (F,T)=3/2. Total = 1/2.
        let rat = |n: i64, d: i64| BigRational::new(n.into(), d.into());
        let weights = vec![rat(-1, 2), rat(3, 2), rat(1, 1), rat(1, 1)];
        let mut engine: Engine<BigRational> = Engine::new(
            2,
            &[vec![1, 2]],
            WeightTable::weighted(weights),
            None,
            EngineConfig::default(),
        );
        assert_eq!(engine.count().unwrap(), rat(1, 2));
    }

    #[test]
    fn tautologies_are_dropped() {
        // (x1 ∨ ¬x1) constrains nothing: 4 models over 2 vars.
        assert_eq!(count_mc(2, &[vec![1, -1]]), BigUint::from(4u32));
    }

    /// Conflict-heavy differential stress: denser formulas (more conflicts →
    /// clause learning + pollution purging exercised) with a TINY cache
    /// budget (evictions interleave with purges), verified against brute
    /// force. This is the in-crate guard for the learning/pollution
    /// discipline; the external harness runs the same check against ganak on
    /// larger instances.
    #[test]
    fn learning_and_pollution_stress_vs_brute_force() {
        let mut state = 0x0123456789abcdefu64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for trial in 0..80 {
            let num_vars = 8 + (next() % 13) as usize; // 8..20
                                                       // Density chosen to sit near the phase transition: lots of
                                                       // conflicts, still plenty of models on many trials.
            let num_clauses = (3 * num_vars) + (next() % (2 * num_vars as u64)) as usize;
            let mut clauses = Vec::new();
            for _ in 0..num_clauses {
                let len = 2 + (next() % 3) as usize;
                let mut cl = Vec::new();
                for _ in 0..len {
                    let v = 1 + (next() % num_vars as u64) as i32;
                    let sign = if next() % 2 == 0 { 1 } else { -1 };
                    cl.push(v * sign);
                }
                clauses.push(cl);
            }
            let expected = brute_force(num_vars, &clauses, None);
            let mut engine: Engine<BigUint> = Engine::new(
                num_vars,
                &clauses,
                WeightTable::unweighted(),
                None,
                EngineConfig {
                    // Tiny budget: force churn under purging.
                    cache_budget_bytes: 1 << 20,
                    deadline: None,
                },
            );
            let got = engine.count().expect("count succeeds");
            assert_eq!(
                got,
                BigUint::from(expected),
                "trial {trial}: learning-mode mismatch on {num_vars} vars \
                 ({} clauses, {} conflicts, {} learned, {} purged)",
                num_clauses,
                engine.stats.conflicts,
                engine.stats.learned_clauses,
                engine.stats.cache_purged,
            );
            // Projected variant too (SAT-oracle path under learning).
            let show: Vec<u32> = (1..=(num_vars as u32).div_ceil(2)).collect();
            let expected_p = brute_force(num_vars, &clauses, Some(&show));
            let mut engine_p: Engine<BigUint> = Engine::new(
                num_vars,
                &clauses,
                WeightTable::unweighted(),
                Some(&show),
                EngineConfig {
                    cache_budget_bytes: 1 << 20,
                    deadline: None,
                },
            );
            let got_p = engine_p.count().expect("projected count succeeds");
            assert_eq!(
                got_p,
                BigUint::from(expected_p),
                "trial {trial}: projected learning-mode mismatch"
            );
        }
    }

    #[test]
    fn empty_clause_is_unsat() {
        assert_eq!(count_mc(2, &[vec![]]), BigUint::from(0u32));
    }
}
