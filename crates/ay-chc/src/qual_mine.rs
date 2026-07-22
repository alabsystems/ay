// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Problem-derived candidate vocabulary for the Houdini/invariant lanes
//! (QUAL-MINE, CHC-COMP campaign item #11).
//!
//! Mines per-predicate qualifier candidates from the input clause system —
//! the cheap half of Eldarica/PCSat's predicate-abstraction advantage —
//! and hands them to the EXISTING Houdini drop-loop as extra pool entries.
//! Four candidate classes:
//!
//! (a) **Per-clause atom harvesting**: atomic comparisons from (negation- and
//!     strict-comparison-normalized) clause constraints whose free variables
//!     all occur as plain arguments of a predicate occurrence in the same
//!     clause, renamed onto that predicate's argument positions; then one
//!     PROPAGATION round between predicates sharing argument variables in a
//!     clause (rename via the shared-arg position mapping).
//! (b) **Difference terms** `t1 − t2` (Int) and `bvsub` both directions (BV)
//!     for same-sort argument pairs, compared `{=, ≤, ≥}` (Int) /
//!     `{=, bvule both ways}` (BV) against constants harvested from the
//!     problem. Plus mod-2 parity atoms for Int args.
//! (c) **BV wraparound-distance terms**: the conditional-abs shape
//!     `ite(d ≥s 0, d, bvneg d)` over `d = bvsub(aᵢ, aⱼ)` — the BV-exact
//!     rendering of Eldarica/CoAR's `ite(d ≥s 0, d, 2^w − (−d))` wraparound
//!     distance — bounded against harvested BV constants.
//! (d) **Loop templates** (relEqs2-style): from self-loop clauses
//!     `P(x̄) ∧ φ ⇒ P(t̄)`, unmodified-argument equalities `aᵢ = aⱼ`, scaled
//!     increment differences `cⱼ·aᵢ − cᵢ·aⱼ ⋈ k` (the `x′−x = c` invariant
//!     family), and `x±y` combinations for BV argument pairs.
//!
//! SOUNDNESS (G2): mined qualifiers are CANDIDATES ONLY. Every consumer runs
//! them through the existing Houdini model-based dropping + per-rule
//! certification (`validate_invariant_against_clauses` /
//! `verify_model_per_rule`); a wrong candidate is dropped or fails final
//! validation — it can never produce a wrong verdict. No new gate surface.
//!
//! Kill switch: `AY_CHC_DISABLE_QUAL_MINE=1` disables the pass entirely.

use crate::expr::intern::arc as mk_arc;
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseHead, HornClause, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet};

/// Total per-predicate candidate cap (after dedup; most-valuable-first).
const QUAL_MINE_MAX_PER_PRED: usize = 768;
/// Per-predicate cap when the mixed control∨data CNF class (g) is enabled:
/// the stock cap plus the mixed-class row budget, so the new rows never
/// displace the existing classes and vice versa (the vmt pc_sfifo/mem_slave
/// pools were measured SATURATED at 768 before class (g) existed).
const QUAL_MINE_MAX_PER_PRED_MIXED: usize = 1280;
/// Cap on harvested atoms per predicate (class a, pre-propagation).
const QUAL_MINE_MAX_ATOMS: usize = 192;
/// Cap on Int constants used in the difference/scaled-difference ladders.
const QUAL_MINE_MAX_INT_CONSTS: usize = 6;
/// Cap on BV constants (per width) used in the bound/difference ladders.
const QUAL_MINE_MAX_BV_CONSTS: usize = 6;
/// Cap on same-sort argument-position pairs per predicate for the
/// difference/wraparound/loop-template classes.
const QUAL_MINE_MAX_PAIRS: usize = 24;
/// All same-sort pairs are enumerated up to this arity; above it only pairs
/// CO-OCCURRING in a harvested atom are used (wide vmt predicates have
/// 30+ BV32 args — the full pair set would swamp the pool).
const QUAL_MINE_SMALL_ARITY: usize = 10;
/// Max |coefficient| admitted for scaled-difference loop templates.
const QUAL_MINE_MAX_COEFF: i128 = 16;
/// Max mined predicate arity (wider predicates are skipped entirely).
const QUAL_MINE_MAX_ARITY: usize = 128;
/// Max Bool argument positions enumerated for control-state clause
/// templates (pairs: 4 clauses each).
const QUAL_MINE_MAX_BOOLS: usize = 8;
/// Bool-arg count up to which 3-literal control clauses are enumerated
/// (8 clauses per triple; C(6,3)·8 = 160 worst case).
const QUAL_MINE_MAX_BOOLS_TRIPLE: usize = 6;
/// Node-count cap for a harvested atom (blow-up guard).
const QUAL_MINE_MAX_ATOM_NODES: usize = 40;

/// Whether the qualifier-mining pass is enabled.
/// Kill switch: `AY_CHC_DISABLE_QUAL_MINE=1` (read fresh — the pass runs once
/// per solve, and tests toggle the variable).
pub(crate) fn qual_mine_enabled() -> bool {
    std::env::var("AY_CHC_DISABLE_QUAL_MINE").ok().as_deref() != Some("1")
}

/// Whether the mixed control∨data CNF class (g) is enabled (fix #3
/// QUAL-MIX). Kill switch: `AY_CHC_DISABLE_QUAL_MIXED=1` restores the
/// previous behavior exactly — the 768-row per-predicate cap, no
/// multi-control-literal mixed rows, and the Int-only wide-arity gate of
/// the disjunctive init-cube splitter (`adaptive_houdini`).
pub(crate) fn qual_mixed_enabled() -> bool {
    std::env::var("AY_CHC_DISABLE_QUAL_MIXED").ok().as_deref() != Some("1")
}

/// Per-predicate mined qualifiers over positional placeholder variables.
///
/// Qualifiers are stored over placeholder vars `__qm{pred}_p{i}` (one per
/// argument position, with the predicate's argument sorts) and instantiated
/// onto arbitrary same-sorted target variables via [`Self::for_predicate`].
pub(crate) struct MinedQualifiers {
    per_pred: FxHashMap<PredicateId, Vec<ChcExpr>>,
    placeholders: FxHashMap<PredicateId, Vec<ChcVar>>,
}

impl MinedQualifiers {
    /// Mine qualifier candidates from every clause of `problem`.
    pub(crate) fn mine(problem: &ChcProblem) -> Self {
        let mut placeholders: FxHashMap<PredicateId, Vec<ChcVar>> = FxHashMap::default();
        for pred in problem.predicates() {
            let arity = pred.arity();
            if arity == 0 || arity > QUAL_MINE_MAX_ARITY {
                continue;
            }
            let vars: Vec<ChcVar> = pred
                .arg_sorts
                .iter()
                .enumerate()
                .map(|(i, sort)| ChcVar::new(format!("__qm{}_p{i}", pred.id.index()), sort.clone()))
                .collect();
            placeholders.insert(pred.id, vars);
        }

        let int_consts = harvest_int_constants(problem);
        let bv_consts = harvest_bv_constants(problem);

        let mixed = qual_mixed_enabled();
        let per_pred_cap = if mixed {
            QUAL_MINE_MAX_PER_PRED_MIXED
        } else {
            QUAL_MINE_MAX_PER_PRED
        };
        let mut miner = Miner {
            problem,
            placeholders,
            pools: FxHashMap::default(),
            seen: FxHashMap::default(),
            int_consts,
            bv_consts,
            per_pred_cap,
        };

        // Order matters twice over: `guarded_data_rows` snapshots the pools
        // while they contain ONLY the class-(a) harvested atoms, and the
        // per-predicate cap keeps earlier (more problem-specific) classes
        // when the ladders below would overflow it. The mixed class (g) runs
        // right after `guarded_data_rows` (it also reads the class-(a)
        // prefix) and BEFORE the generic ladders so its rows survive the cap.
        miner.harvest_clause_atoms();
        miner.guarded_data_rows();
        if mixed {
            miner.mixed_control_data_clauses();
        }
        miner.bool_control_clauses();
        miner.propagate_shared_args();
        miner.loop_templates();
        miner.difference_and_wraparound();

        // Final cap is PER PREDICATE: only predicates that actually carry a
        // Bool control argument (the mixed class-(g) target shape) get the
        // elevated budget; pure-Int / pure-data predicates keep the stock 768
        // cap so LIA/Int problems are not inflated with 512 extra rows (which
        // measurably starved the disjunctive fallback — the original QUAL-MINE
        // restricted extra rows to control-carrying shapes for exactly this
        // reason). The miner's internal `per_pred_cap` is the elevated value so
        // mixed rows survive intermediate mining; this truncate enforces the
        // real per-shape ceiling.
        let mut per_pred = miner.pools;
        for (pred_id, pool) in per_pred.iter_mut() {
            let has_bool_arg = problem
                .get_predicate(*pred_id)
                .map(|p| p.arg_sorts.iter().any(|s| matches!(s, ChcSort::Bool)))
                .unwrap_or(false);
            let cap = if mixed && has_bool_arg {
                QUAL_MINE_MAX_PER_PRED_MIXED
            } else {
                QUAL_MINE_MAX_PER_PRED
            };
            pool.truncate(cap);
        }
        Self {
            per_pred,
            placeholders: miner.placeholders,
        }
    }

    /// Instantiate the mined qualifiers for `pred` over `target_vars`
    /// (positional: `target_vars[i]` replaces argument position `i`).
    /// Returns an empty vec when arities/sorts do not line up (fail-safe:
    /// qualifiers are only ever candidates).
    pub(crate) fn for_predicate(&self, pred: PredicateId, target_vars: &[ChcVar]) -> Vec<ChcExpr> {
        let (Some(pool), Some(ph)) = (self.per_pred.get(&pred), self.placeholders.get(&pred))
        else {
            return Vec::new();
        };
        if target_vars.len() < ph.len()
            || ph
                .iter()
                .zip(target_vars.iter())
                .any(|(p, t)| p.sort != t.sort)
        {
            return Vec::new();
        }
        let subst: Vec<(ChcVar, ChcExpr)> = ph
            .iter()
            .zip(target_vars.iter())
            .map(|(p, t)| (p.clone(), ChcExpr::var(t.clone())))
            .collect();
        pool.iter().map(|q| q.substitute(&subst)).collect()
    }

    /// Total mined candidate count (diagnostics/tests).
    #[cfg(test)]
    pub(crate) fn total(&self) -> usize {
        self.per_pred.values().map(Vec::len).sum()
    }
}

/// One predicate occurrence in a clause whose arguments are all plain,
/// pairwise-distinct variables: maps variable name → argument position.
struct Occurrence {
    pred: PredicateId,
    var_to_pos: FxHashMap<String, usize>,
}

struct Miner<'a> {
    problem: &'a ChcProblem,
    placeholders: FxHashMap<PredicateId, Vec<ChcVar>>,
    pools: FxHashMap<PredicateId, Vec<ChcExpr>>,
    seen: FxHashMap<PredicateId, DetHashSet<ChcExpr>>,
    int_consts: Vec<i128>,
    bv_consts: FxHashMap<u32, Vec<u128>>,
    /// Per-predicate pool cap (stock, or widened when class (g) is on).
    per_pred_cap: usize,
}

impl Miner<'_> {
    fn push(&mut self, pred: PredicateId, qual: ChcExpr) {
        let pool = self.pools.entry(pred).or_default();
        if pool.len() >= self.per_pred_cap {
            return;
        }
        if self.seen.entry(pred).or_default().insert(qual.clone()) {
            pool.push(qual);
        }
    }

    /// Clean occurrences (head + body) of a clause.
    fn occurrences(&self, clause: &HornClause) -> Vec<Occurrence> {
        let mut out = Vec::new();
        let mut add = |pred: PredicateId, args: &[ChcExpr]| {
            if !self.placeholders.contains_key(&pred) {
                return;
            }
            let mut var_to_pos: FxHashMap<String, usize> = FxHashMap::default();
            for (i, a) in args.iter().enumerate() {
                let ChcExpr::Var(v) = a else {
                    return;
                };
                if var_to_pos.insert(v.name.clone(), i).is_some() {
                    return; // repeated variable: no clean position map
                }
            }
            out.push(Occurrence { pred, var_to_pos });
        };
        for (pid, args) in &clause.body.predicates {
            add(*pid, args);
        }
        if let ClauseHead::Predicate(pid, args) = &clause.head {
            add(*pid, args);
        }
        out
    }

    /// Class (a): harvest normalized constraint atoms into every occurrence
    /// whose arguments cover the atom's variables.
    fn harvest_clause_atoms(&mut self) {
        for clause in self.problem.clauses() {
            let Some(constraint) = clause.body.constraint.as_ref() else {
                continue;
            };
            let occurrences = self.occurrences(clause);
            if occurrences.is_empty() {
                continue;
            }
            // Light QE-normalization: push negations inward, normalize strict
            // Int comparisons, fold constants. (Clause-local variables are
            // handled by the vars ⊆ args filter below rather than full QE.)
            let normalized = constraint
                .normalize_negations()
                .normalize_strict_int_comparisons()
                .simplify_constants();
            let mut atoms: Vec<ChcExpr> = Vec::new();
            let mut atom_seen: DetHashSet<ChcExpr> = DetHashSet::default();
            collect_atoms(&normalized, &mut atoms, &mut atom_seen);
            for atom in atoms {
                let vars = atom.vars();
                if vars.is_empty() {
                    continue;
                }
                for occ in &occurrences {
                    if self
                        .pools
                        .get(&occ.pred)
                        .is_some_and(|p| p.len() >= QUAL_MINE_MAX_ATOMS)
                    {
                        continue;
                    }
                    if !vars.iter().all(|v| occ.var_to_pos.contains_key(&v.name)) {
                        continue;
                    }
                    let ph = &self.placeholders[&occ.pred];
                    let subst: Vec<(ChcVar, ChcExpr)> = vars
                        .iter()
                        .map(|v| {
                            let pos = occ.var_to_pos[&v.name];
                            (v.clone(), ChcExpr::var(ph[pos].clone()))
                        })
                        .collect();
                    let qual = atom.substitute(&subst);
                    self.push(occ.pred, qual);
                }
            }
        }
    }

    /// Propagation round: for clauses containing two clean occurrences P and
    /// Q sharing argument variables, rename P's qualifiers onto Q via the
    /// shared-arg position mapping (and vice versa — both ordered pairs are
    /// visited). One round, run after the harvesting pass.
    fn propagate_shared_args(&mut self) {
        for clause in self.problem.clauses() {
            let occurrences = self.occurrences(clause);
            for src in &occurrences {
                for dst in &occurrences {
                    if src.pred == dst.pred {
                        continue;
                    }
                    // Shared-arg mapping: src position → dst position via the
                    // shared clause variable.
                    let src_ph = self.placeholders[&src.pred].clone();
                    let dst_ph = self.placeholders[&dst.pred].clone();
                    let mut pos_map: FxHashMap<usize, usize> = FxHashMap::default();
                    for (name, &sp) in &src.var_to_pos {
                        if let Some(&dp) = dst.var_to_pos.get(name) {
                            if src_ph[sp].sort == dst_ph[dp].sort {
                                pos_map.insert(sp, dp);
                            }
                        }
                    }
                    if pos_map.is_empty() {
                        continue;
                    }
                    let subst: Vec<(ChcVar, ChcExpr)> = pos_map
                        .iter()
                        .map(|(&sp, &dp)| (src_ph[sp].clone(), ChcExpr::var(dst_ph[dp].clone())))
                        .collect();
                    let mapped_names: DetHashSet<String> =
                        pos_map.keys().map(|&sp| src_ph[sp].name.clone()).collect();
                    let src_pool: Vec<ChcExpr> =
                        self.pools.get(&src.pred).cloned().unwrap_or_default();
                    for qual in src_pool {
                        // Only qualifiers ranging entirely over SHARED positions
                        // translate; others would leave dangling placeholders.
                        if !qual.vars().iter().all(|v| mapped_names.contains(&v.name)) {
                            continue;
                        }
                        let translated = qual.substitute(&subst);
                        self.push(dst.pred, translated);
                    }
                }
            }
        }
    }

    /// Class (e): control-state clause templates over Bool argument
    /// positions — 2-literal clauses `±a ∨ ±b` for Bool pairs and 3-literal
    /// clauses for Bool triples (small counts only). The vmt/lustre control
    /// skeleton (which Bool combinations are reachable) is exactly this
    /// vocabulary; the data arguments are unconstrained at init, so control
    /// clauses are the only init-implied support lemmas available there.
    fn bool_control_clauses(&mut self) {
        let preds: Vec<PredicateId> = self.placeholders.keys().copied().collect();
        for pred in preds {
            let ph = self.placeholders[&pred].clone();
            let bools: Vec<&ChcVar> = ph
                .iter()
                .filter(|v| v.sort == ChcSort::Bool)
                .take(QUAL_MINE_MAX_BOOLS)
                .collect();
            for i in 0..bools.len() {
                for j in (i + 1)..bools.len() {
                    let a = ChcExpr::var(bools[i].clone());
                    let b = ChcExpr::var(bools[j].clone());
                    for pa in [a.clone(), ChcExpr::not(a.clone())] {
                        for pb in [b.clone(), ChcExpr::not(b.clone())] {
                            self.push(pred, ChcExpr::or(pa.clone(), pb));
                        }
                    }
                }
            }
            if bools.len() > QUAL_MINE_MAX_BOOLS_TRIPLE {
                continue;
            }
            for i in 0..bools.len() {
                for j in (i + 1)..bools.len() {
                    for k in (j + 1)..bools.len() {
                        let a = ChcExpr::var(bools[i].clone());
                        let b = ChcExpr::var(bools[j].clone());
                        let c = ChcExpr::var(bools[k].clone());
                        for pa in [a.clone(), ChcExpr::not(a.clone())] {
                            for pb in [b.clone(), ChcExpr::not(b.clone())] {
                                for pc in [c.clone(), ChcExpr::not(c.clone())] {
                                    self.push(
                                        pred,
                                        ChcExpr::or_all([pa.clone(), pb.clone(), pc.clone()]),
                                    );
                                }
                            }
                        }
                    }
                }
            }
            // 4-literal clauses characterize the full control-state set for
            // the typical 4-Bool vmt skeleton (the query flag itself is a
            // 4-literal clause there). Only for very small Bool counts.
            if bools.len() > 5 {
                continue;
            }
            for i in 0..bools.len() {
                for j in (i + 1)..bools.len() {
                    for k in (j + 1)..bools.len() {
                        for l in (k + 1)..bools.len() {
                            let lits = [
                                ChcExpr::var(bools[i].clone()),
                                ChcExpr::var(bools[j].clone()),
                                ChcExpr::var(bools[k].clone()),
                                ChcExpr::var(bools[l].clone()),
                            ];
                            for mask in 0u32..16 {
                                let clause: Vec<ChcExpr> = lits
                                    .iter()
                                    .enumerate()
                                    .map(|(idx, lit)| {
                                        if mask & (1 << idx) != 0 {
                                            ChcExpr::not(lit.clone())
                                        } else {
                                            lit.clone()
                                        }
                                    })
                                    .collect();
                                self.push(pred, ChcExpr::or_all(clause));
                            }
                        }
                    }
                }
            }
        }
    }

    /// Class (f): control-guarded data rows `±b ∨ (xᵢ ⋈ xⱼ)` — a Bool control
    /// literal disjoined with a same-sort data relation (equality/ordering)
    /// for co-occurring pairs. The vmt safety invariants correlate control
    /// state with data relations (e.g. "queue read ⇒ counters equal"), which
    /// neither the pure control clauses nor the unguarded data atoms express.
    fn guarded_data_rows(&mut self) {
        const MAX_GUARD_BOOLS: usize = 6;
        const MAX_GUARD_PAIRS: usize = 6;
        /// Harvested atoms (class a) admitted as guarded consequents.
        const MAX_GUARD_ATOMS: usize = 16;
        let preds: Vec<PredicateId> = self.placeholders.keys().copied().collect();
        for pred in preds {
            let ph = self.placeholders[&pred].clone();
            let bools: Vec<&ChcVar> = ph
                .iter()
                .filter(|v| v.sort == ChcSort::Bool)
                .take(MAX_GUARD_BOOLS)
                .collect();
            if bools.is_empty() {
                continue;
            }
            // `±b ∨ atom` / `±b ∨ ¬atom` over the harvested atoms — MUST run
            // while the pool holds only class-(a) atoms (see `mine`). This is
            // the dominant vmt invariant shape (e.g. fragtest_simple:
            // `¬running ∨ bvsle(cnt, limit+1)`).
            let atom_pool: Vec<ChcExpr> = self
                .pools
                .get(&pred)
                .map(|p| p.iter().take(MAX_GUARD_ATOMS).cloned().collect())
                .unwrap_or_default();
            for b in &bools {
                let bv = ChcExpr::var((*b).clone());
                for atom in &atom_pool {
                    if atom.sort() != ChcSort::Bool {
                        continue;
                    }
                    for consequent in [atom.clone(), ChcExpr::not(atom.clone())] {
                        self.push(pred, ChcExpr::or(bv.clone(), consequent.clone()));
                        self.push(pred, ChcExpr::or(ChcExpr::not(bv.clone()), consequent));
                    }
                }
            }
            let pairs: Vec<(usize, usize)> = self
                .same_sort_pairs(pred)
                .into_iter()
                .take(MAX_GUARD_PAIRS)
                .collect();
            for (i, j) in pairs {
                let (xi, xj) = (ChcExpr::var(ph[i].clone()), ChcExpr::var(ph[j].clone()));
                let atoms: Vec<ChcExpr> = match &ph[i].sort {
                    ChcSort::BitVec(_) => vec![
                        ChcExpr::eq(xi.clone(), xj.clone()),
                        ChcExpr::bv_ule(xi.clone(), xj.clone()),
                        ChcExpr::bv_ule(xj.clone(), xi.clone()),
                    ],
                    ChcSort::Int => vec![
                        ChcExpr::eq(xi.clone(), xj.clone()),
                        ChcExpr::le(xi.clone(), xj.clone()),
                        ChcExpr::le(xj.clone(), xi.clone()),
                    ],
                    _ => continue,
                };
                for b in &bools {
                    let bv = ChcExpr::var((*b).clone());
                    for atom in &atoms {
                        self.push(pred, ChcExpr::or(bv.clone(), atom.clone()));
                        self.push(pred, ChcExpr::or(ChcExpr::not(bv.clone()), atom.clone()));
                    }
                }
            }
        }
    }

    /// Class (g), fix #3 QUAL-MIX: mixed control∨data CNF clauses — 2-4
    /// Bool control literals (every sign combination) disjoined with ONE
    /// data atom: `±bᵢ ∨ ±bⱼ [∨ ±bₖ [∨ ±bₗ]] ∨ data`.
    ///
    /// The Spacer-oracle invariants for the vmt pc_sfifo/mem_slave family
    /// are exactly 5-6-literal clauses of this shape (a full 4-Bool control
    /// cube ∨ one BV sum/difference/argument equality); before this class
    /// existed NO pool carried any multi-control-literal mixed clause
    /// (`bool_control_clauses` is pure-Bool; `guarded_data_rows` allows
    /// exactly ONE guard). Data atoms, most-oracle-shaped first: harvested
    /// class-(a) comparison atoms over data variables, pair equalities and
    /// bvadd/bvsub-vs-constant equalities (the guarded rendering of the
    /// `loop_templates` BV sum vocabulary), then `arg = const` rows.
    ///
    /// Combinatorics discipline: control subsets come from the ≤8
    /// most-relevant Bool args (same selection as `bool_control_clauses`),
    /// data atoms are capped, and emission stops at `MAX_MIXED_ROWS` rows
    /// pre-dedup — priority order full-cube (bools == 4, the vmt skeleton),
    /// then pairs, then triples. Pure candidate content (G2-safe): every
    /// survivor still passes Houdini model-based dropping plus per-rule
    /// certification. Kill switch: `AY_CHC_DISABLE_QUAL_MIXED=1`.
    fn mixed_control_data_clauses(&mut self) {
        /// Per-predicate row budget for this class (pre-dedup).
        const MAX_MIXED_ROWS: usize = 512;
        /// Data atoms admitted as consequents (total).
        const MAX_MIXED_ATOMS: usize = 24;
        /// Harvested class-(a) atoms admitted (most problem-specific first).
        const MAX_MIXED_HARVESTED: usize = 8;
        /// Pair-derived atoms stop once the list reaches this size, leaving
        /// room for the `arg = const` consequents.
        const MAX_MIXED_PAIR_FILL: usize = 20;
        /// Constants per width/sort in the sum/difference/arg equalities.
        const MAX_MIXED_CONSTS: usize = 2;
        /// Argument positions admitted for `arg = const` consequents.
        const MAX_MIXED_ARGS: usize = 8;

        let preds: Vec<PredicateId> = self.placeholders.keys().copied().collect();
        for pred in preds {
            let ph = self.placeholders[&pred].clone();
            let bools: Vec<ChcVar> = ph
                .iter()
                .filter(|v| v.sort == ChcSort::Bool)
                .take(QUAL_MINE_MAX_BOOLS)
                .cloned()
                .collect();
            if bools.len() < 2 {
                continue;
            }

            // Data atoms, most-oracle-shaped first (the emission loop below
            // is budget-cut, so list order = priority).
            let mut atoms: Vec<ChcExpr> = Vec::new();
            let mut aseen: DetHashSet<ChcExpr> = DetHashSet::default();
            // (1) Harvested class-(a) comparison atoms over data (non-Bool)
            //     variables — the actual transition relations. The pool is
            //     append-only with class (a) first, so the pool prefix is
            //     still the harvested atoms even though `guarded_data_rows`
            //     already appended its Or-rooted rows (excluded here by the
            //     comparison-root filter).
            for cand in self.pools.get(&pred).cloned().unwrap_or_default() {
                if atoms.len() >= MAX_MIXED_HARVESTED {
                    break;
                }
                if !is_comparison_root(&cand) {
                    continue;
                }
                let vars = cand.vars();
                if vars.is_empty() || vars.iter().any(|v| v.sort == ChcSort::Bool) {
                    continue;
                }
                if aseen.insert(cand.clone()) {
                    atoms.push(cand);
                }
            }
            // (2) Pair equalities plus sum/difference-vs-constant equalities
            //     — the guarded variant of the `loop_templates` vocabulary.
            for (i, j) in self.same_sort_pairs(pred) {
                if atoms.len() >= MAX_MIXED_PAIR_FILL {
                    break;
                }
                let (xi, xj) = (ChcExpr::var(ph[i].clone()), ChcExpr::var(ph[j].clone()));
                let mut add = |atoms: &mut Vec<ChcExpr>, a: ChcExpr| {
                    if atoms.len() < MAX_MIXED_PAIR_FILL && aseen.insert(a.clone()) {
                        atoms.push(a);
                    }
                };
                match ph[i].sort.clone() {
                    ChcSort::BitVec(w) => {
                        add(&mut atoms, ChcExpr::eq(xi.clone(), xj.clone()));
                        let consts: Vec<u128> = self
                            .bv_consts
                            .get(&w)
                            .cloned()
                            .unwrap_or_default()
                            .into_iter()
                            .take(MAX_MIXED_CONSTS)
                            .collect();
                        for &c in &consts {
                            let cexp = ChcExpr::BitVec(c, w);
                            add(
                                &mut atoms,
                                ChcExpr::eq(
                                    bv_binop(ChcOp::BvAdd, xi.clone(), xj.clone()),
                                    cexp.clone(),
                                ),
                            );
                            if c != 0 {
                                // bvsub = 0 duplicates the plain equality.
                                add(
                                    &mut atoms,
                                    ChcExpr::eq(
                                        bv_binop(ChcOp::BvSub, xi.clone(), xj.clone()),
                                        cexp.clone(),
                                    ),
                                );
                                add(
                                    &mut atoms,
                                    ChcExpr::eq(
                                        bv_binop(ChcOp::BvSub, xj.clone(), xi.clone()),
                                        cexp,
                                    ),
                                );
                            }
                        }
                    }
                    ChcSort::Int => {
                        add(&mut atoms, ChcExpr::eq(xi.clone(), xj.clone()));
                        let consts: Vec<i128> = self
                            .int_consts
                            .iter()
                            .copied()
                            .take(MAX_MIXED_CONSTS)
                            .collect();
                        for &c in &consts {
                            add(
                                &mut atoms,
                                ChcExpr::eq(ChcExpr::add(xi.clone(), xj.clone()), ChcExpr::int(c)),
                            );
                            if c != 0 {
                                add(
                                    &mut atoms,
                                    ChcExpr::eq(
                                        ChcExpr::sub(xi.clone(), xj.clone()),
                                        ChcExpr::int(c),
                                    ),
                                );
                            }
                        }
                    }
                    _ => {}
                }
            }
            // (3) `arg = const` consequents fill the remainder.
            for v in ph
                .iter()
                .filter(|v| v.sort != ChcSort::Bool)
                .take(MAX_MIXED_ARGS)
            {
                if atoms.len() >= MAX_MIXED_ATOMS {
                    break;
                }
                let x = ChcExpr::var(v.clone());
                match &v.sort {
                    ChcSort::BitVec(w) => {
                        let consts: Vec<u128> = self
                            .bv_consts
                            .get(w)
                            .cloned()
                            .unwrap_or_default()
                            .into_iter()
                            .take(MAX_MIXED_CONSTS)
                            .collect();
                        for &c in &consts {
                            if atoms.len() >= MAX_MIXED_ATOMS {
                                break;
                            }
                            let a = ChcExpr::eq(x.clone(), ChcExpr::BitVec(c, *w));
                            if aseen.insert(a.clone()) {
                                atoms.push(a);
                            }
                        }
                    }
                    ChcSort::Int => {
                        let consts: Vec<i128> = self
                            .int_consts
                            .iter()
                            .copied()
                            .take(MAX_MIXED_CONSTS)
                            .collect();
                        for &c in &consts {
                            if atoms.len() >= MAX_MIXED_ATOMS {
                                break;
                            }
                            let a = ChcExpr::eq(x.clone(), ChcExpr::int(c));
                            if aseen.insert(a.clone()) {
                                atoms.push(a);
                            }
                        }
                    }
                    _ => {}
                }
            }
            atoms.truncate(MAX_MIXED_ATOMS);
            if atoms.is_empty() {
                continue;
            }

            // Control subsets in priority order under the row budget: the
            // full 4-Bool cube first when the predicate has exactly 4 Bools
            // (the vmt skeleton — 5-literal oracle rows), then pairs, then
            // triples (small Bool counts only, like `bool_control_clauses`).
            let n = bools.len();
            let mut subsets: Vec<Vec<usize>> = Vec::new();
            if n == 4 {
                subsets.push(vec![0, 1, 2, 3]);
            }
            for i in 0..n {
                for j in (i + 1)..n {
                    subsets.push(vec![i, j]);
                }
            }
            if n <= QUAL_MINE_MAX_BOOLS_TRIPLE {
                for i in 0..n {
                    for j in (i + 1)..n {
                        for k in (j + 1)..n {
                            subsets.push(vec![i, j, k]);
                        }
                    }
                }
            }
            let mut budget = MAX_MIXED_ROWS;
            'emit: for subset in &subsets {
                for atom in &atoms {
                    for mask in 0u32..(1u32 << subset.len()) {
                        if budget == 0 {
                            break 'emit;
                        }
                        budget -= 1;
                        let mut lits: Vec<ChcExpr> = subset
                            .iter()
                            .enumerate()
                            .map(|(idx, &b)| {
                                let v = ChcExpr::var(bools[b].clone());
                                if mask & (1 << idx) != 0 {
                                    ChcExpr::not(v)
                                } else {
                                    v
                                }
                            })
                            .collect();
                        lits.push(atom.clone());
                        self.push(pred, ChcExpr::or_all(lits));
                    }
                }
            }
        }
    }

    /// Same-sort argument-position pairs for `pred`: all pairs at small
    /// arity, else only pairs co-occurring in an already-mined qualifier.
    fn same_sort_pairs(&self, pred: PredicateId) -> Vec<(usize, usize)> {
        let ph = &self.placeholders[&pred];
        let mut pairs: Vec<(usize, usize)> = Vec::new();
        let mut seen: DetHashSet<(usize, usize)> = DetHashSet::default();
        if ph.len() <= QUAL_MINE_SMALL_ARITY {
            for i in 0..ph.len() {
                for j in (i + 1)..ph.len() {
                    if ph[i].sort == ph[j].sort
                        && ph[i].sort != ChcSort::Bool
                        && pairs.len() < QUAL_MINE_MAX_PAIRS
                    {
                        pairs.push((i, j));
                    }
                }
            }
            return pairs;
        }
        // Wide predicate: co-occurring positions in mined qualifiers only.
        let name_to_pos: FxHashMap<&str, usize> = ph
            .iter()
            .enumerate()
            .map(|(i, v)| (v.name.as_str(), i))
            .collect();
        let Some(pool) = self.pools.get(&pred) else {
            return pairs;
        };
        for qual in pool {
            if pairs.len() >= QUAL_MINE_MAX_PAIRS {
                break;
            }
            let vars = qual.vars();
            let positions: Vec<usize> = vars
                .iter()
                .filter_map(|v| name_to_pos.get(v.name.as_str()).copied())
                .collect();
            if !(2..=4).contains(&positions.len()) {
                continue;
            }
            for (ai, &a) in positions.iter().enumerate() {
                for &b in positions.iter().skip(ai + 1) {
                    let (lo, hi) = if a < b { (a, b) } else { (b, a) };
                    if ph[lo].sort == ph[hi].sort
                        && ph[lo].sort != ChcSort::Bool
                        && seen.insert((lo, hi))
                        && pairs.len() < QUAL_MINE_MAX_PAIRS
                    {
                        pairs.push((lo, hi));
                    }
                }
            }
        }
        pairs
    }

    /// Classes (b) + (c): difference terms against harvested constants, plus
    /// per-arg BV bounds, Int parity atoms, and BV wraparound distances.
    fn difference_and_wraparound(&mut self) {
        let preds: Vec<PredicateId> = self.placeholders.keys().copied().collect();
        for pred in preds {
            let ph = self.placeholders[&pred].clone();
            // Per-arg BV constant bounds (the vmt counter vocabulary; Int
            // var-const bounds are already covered by the Houdini pool).
            for v in &ph {
                let ChcSort::BitVec(w) = v.sort.clone() else {
                    continue;
                };
                let x = ChcExpr::var(v.clone());
                for &c in self.bv_consts.get(&w).cloned().unwrap_or_default().iter() {
                    let cexp = ChcExpr::BitVec(c, w);
                    self.push(pred, ChcExpr::bv_ule(x.clone(), cexp.clone()));
                    self.push(pred, ChcExpr::bv_ule(cexp.clone(), x.clone()));
                    self.push(pred, ChcExpr::eq(x.clone(), cexp));
                }
            }
            // Int parity atoms (mod-2 qualifiers from the PCSat brief).
            for v in &ph {
                if v.sort != ChcSort::Int {
                    continue;
                }
                let m = ChcExpr::mod_op(ChcExpr::var(v.clone()), ChcExpr::int(2));
                self.push(pred, ChcExpr::eq(m.clone(), ChcExpr::int(0)));
                self.push(pred, ChcExpr::eq(m, ChcExpr::int(1)));
            }
            for (i, j) in self.same_sort_pairs(pred) {
                let (vi, vj) = (&ph[i], &ph[j]);
                let (xi, xj) = (ChcExpr::var(vi.clone()), ChcExpr::var(vj.clone()));
                match vi.sort.clone() {
                    ChcSort::Int => {
                        let diff = ChcExpr::sub(xi.clone(), xj.clone());
                        for &c in &self.int_consts.clone() {
                            for k in [c, -c] {
                                self.push(pred, ChcExpr::eq(diff.clone(), ChcExpr::int(k)));
                                self.push(pred, ChcExpr::le(diff.clone(), ChcExpr::int(k)));
                                self.push(pred, ChcExpr::ge(diff.clone(), ChcExpr::int(k)));
                            }
                        }
                    }
                    ChcSort::BitVec(w) => {
                        let consts = self.bv_consts.get(&w).cloned().unwrap_or_default();
                        let d_ij = bv_binop(ChcOp::BvSub, xi.clone(), xj.clone());
                        let d_ji = bv_binop(ChcOp::BvSub, xj.clone(), xi.clone());
                        for d in [&d_ij, &d_ji] {
                            for &c in &consts {
                                let cexp = ChcExpr::BitVec(c, w);
                                self.push(pred, ChcExpr::eq(d.clone(), cexp.clone()));
                                self.push(pred, ChcExpr::bv_ule(d.clone(), cexp.clone()));
                                self.push(pred, ChcExpr::bv_ule(cexp, d.clone()));
                            }
                        }
                        // (c) wraparound distance: ite(d ≥s 0, d, bvneg d) —
                        // bvneg d = 2^w − d, i.e. the distance measured the
                        // other way around the ring.
                        let zero = ChcExpr::BitVec(0, w);
                        let wd = ChcExpr::ite(
                            bv_binop(ChcOp::BvSGe, d_ij.clone(), zero),
                            d_ij.clone(),
                            bv_unop(ChcOp::BvNeg, d_ij.clone()),
                        );
                        for &c in &consts {
                            let cexp = ChcExpr::BitVec(c, w);
                            self.push(pred, ChcExpr::bv_ule(wd.clone(), cexp.clone()));
                            self.push(pred, ChcExpr::eq(wd.clone(), cexp));
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    /// Class (d): relEqs2-style loop templates from self-loop clauses
    /// `P(x̄) ∧ φ ⇒ P(t̄)`.
    fn loop_templates(&mut self) {
        for clause in self.problem.clauses() {
            let ClauseHead::Predicate(hpred, hargs) = &clause.head else {
                continue;
            };
            let Some(ph) = self.placeholders.get(hpred).cloned() else {
                continue;
            };
            // Exactly one body occurrence of the SAME predicate with clean
            // variable args = a self-loop (transition) clause.
            let body_occ: Vec<&(PredicateId, Vec<ChcExpr>)> = clause
                .body
                .predicates
                .iter()
                .filter(|(pid, _)| pid == hpred)
                .collect();
            let [(_, bargs)] = body_occ.as_slice() else {
                continue;
            };
            if bargs.len() != hargs.len() || hargs.len() != ph.len() {
                continue;
            }
            let mut body_vars: Vec<&ChcVar> = Vec::with_capacity(bargs.len());
            let mut names: DetHashSet<&str> = DetHashSet::default();
            let mut clean = true;
            for a in bargs.iter() {
                match a {
                    ChcExpr::Var(v) if names.insert(v.name.as_str()) => body_vars.push(v),
                    _ => {
                        clean = false;
                        break;
                    }
                }
            }
            if !clean {
                continue;
            }

            // Per-position update classification.
            let mut unmodified: Vec<usize> = Vec::new();
            let mut increments: Vec<(usize, i128)> = Vec::new(); // Int: t_i = x_i + c, c ≠ 0
            for (i, t) in hargs.iter().enumerate() {
                match t {
                    ChcExpr::Var(v) if v.name == body_vars[i].name => unmodified.push(i),
                    _ => {
                        if let Some(c) = int_increment(t, body_vars[i]) {
                            if c != 0 && c.abs() <= QUAL_MINE_MAX_COEFF {
                                increments.push((i, c));
                            }
                        }
                    }
                }
            }

            // Unmodified-argument equalities (same sort).
            for (a, &i) in unmodified.iter().enumerate() {
                for &j in unmodified.iter().skip(a + 1) {
                    if ph[i].sort == ph[j].sort {
                        self.push(
                            *hpred,
                            ChcExpr::eq(ChcExpr::var(ph[i].clone()), ChcExpr::var(ph[j].clone())),
                        );
                    }
                }
            }

            // Scaled differences: for increments cᵢ, cⱼ the term
            // cⱼ·aᵢ − cᵢ·aⱼ is loop-invariant (x′−x = c family).
            let ladder: Vec<i128> = self.int_consts.clone();
            for (a, &(i, ci)) in increments.iter().enumerate() {
                for &(j, cj) in increments.iter().skip(a + 1) {
                    if ph[i].sort != ChcSort::Int || ph[j].sort != ChcSort::Int {
                        continue;
                    }
                    let term = ChcExpr::sub(
                        ChcExpr::mul(ChcExpr::int(cj), ChcExpr::var(ph[i].clone())),
                        ChcExpr::mul(ChcExpr::int(ci), ChcExpr::var(ph[j].clone())),
                    );
                    for &k in &ladder {
                        for kk in [k, -k] {
                            self.push(*hpred, ChcExpr::eq(term.clone(), ChcExpr::int(kk)));
                            self.push(*hpred, ChcExpr::le(term.clone(), ChcExpr::int(kk)));
                            self.push(*hpred, ChcExpr::ge(term.clone(), ChcExpr::int(kk)));
                        }
                    }
                }
            }

            // BV x±y combinations for same-width argument pairs.
            for (i, j) in self.same_sort_pairs(*hpred) {
                let ChcSort::BitVec(w) = ph[i].sort.clone() else {
                    continue;
                };
                let (xi, xj) = (ChcExpr::var(ph[i].clone()), ChcExpr::var(ph[j].clone()));
                let sum = bv_binop(ChcOp::BvAdd, xi.clone(), xj.clone());
                let consts = self.bv_consts.get(&w).cloned().unwrap_or_default();
                for &c in &consts {
                    let cexp = ChcExpr::BitVec(c, w);
                    self.push(*hpred, ChcExpr::eq(sum.clone(), cexp.clone()));
                    self.push(*hpred, ChcExpr::bv_ule(sum.clone(), cexp));
                }
                // Argument orderings (both directions; the wrong one drops).
                self.push(*hpred, ChcExpr::bv_ule(xi.clone(), xj.clone()));
                self.push(*hpred, ChcExpr::bv_ule(xj, xi));
            }
        }
    }
}

/// `t = x + c` / `t = c + x` / `t = x − c` (Int) → the increment `c`.
fn int_increment(t: &ChcExpr, x: &ChcVar) -> Option<i128> {
    match t {
        ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(v), ChcExpr::Int(c)) | (ChcExpr::Int(c), ChcExpr::Var(v))
                    if v.name == x.name =>
                {
                    Some(*c)
                }
                _ => None,
            }
        }
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(v), ChcExpr::Int(c)) if v.name == x.name => c.checked_neg(),
                _ => None,
            }
        }
        _ => None,
    }
}

fn bv_binop(op: ChcOp, a: ChcExpr, b: ChcExpr) -> ChcExpr {
    ChcExpr::Op(op, vec![mk_arc(a), mk_arc(b)])
}

fn bv_unop(op: ChcOp, a: ChcExpr) -> ChcExpr {
    ChcExpr::Op(op, vec![mk_arc(a)])
}

/// Whether the expression is a comparison-rooted atom — the class-(a)
/// harvested shape (`collect_atoms` output). Used to pick the harvested
/// atoms back out of a pool that later classes have appended to.
fn is_comparison_root(e: &ChcExpr) -> bool {
    matches!(
        e,
        ChcExpr::Op(
            ChcOp::Eq
                | ChcOp::Ne
                | ChcOp::Le
                | ChcOp::Lt
                | ChcOp::Ge
                | ChcOp::Gt
                | ChcOp::BvULe
                | ChcOp::BvULt
                | ChcOp::BvUGe
                | ChcOp::BvUGt
                | ChcOp::BvSLe
                | ChcOp::BvSLt
                | ChcOp::BvSGe
                | ChcOp::BvSGt,
            _
        )
    )
}

/// Atomic comparison collector: Int and BV comparison subterms (blow-up
/// guarded), walking through all boolean/ite structure.
fn collect_atoms(expr: &ChcExpr, out: &mut Vec<ChcExpr>, seen: &mut DetHashSet<ChcExpr>) {
    let mut stack: Vec<&ChcExpr> = vec![expr];
    while let Some(e) = stack.pop() {
        let ChcExpr::Op(op, args) = e else {
            continue;
        };
        stack.extend(args.iter().map(|a| a.as_ref()));
        if matches!(
            op,
            ChcOp::Eq
                | ChcOp::Ne
                | ChcOp::Le
                | ChcOp::Lt
                | ChcOp::Ge
                | ChcOp::Gt
                | ChcOp::BvULe
                | ChcOp::BvULt
                | ChcOp::BvUGe
                | ChcOp::BvUGt
                | ChcOp::BvSLe
                | ChcOp::BvSLt
                | ChcOp::BvSGe
                | ChcOp::BvSGt
        ) && node_count_capped(e, QUAL_MINE_MAX_ATOM_NODES) <= QUAL_MINE_MAX_ATOM_NODES
            && seen.insert(e.clone())
        {
            out.push(e.clone());
        }
    }
}

fn node_count_capped(expr: &ChcExpr, cap: usize) -> usize {
    let mut count = 0usize;
    let mut stack = vec![expr];
    while let Some(e) = stack.pop() {
        count += 1;
        if count > cap {
            return count;
        }
        match e {
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => stack.extend(args.iter().map(|a| a.as_ref())),
            ChcExpr::ConstArray(_, inner) => stack.push(inner.as_ref()),
            _ => {}
        }
    }
    count
}

/// Int constants from all clause constraints and predicate arguments,
/// smallest magnitude first, deduped and capped.
fn harvest_int_constants(problem: &ChcProblem) -> Vec<i128> {
    let mut seen: DetHashSet<i128> = DetHashSet::default();
    let mut out: Vec<i128> = Vec::new();
    visit_all_exprs(problem, &mut |e| {
        if let ChcExpr::Int(n) = e {
            if seen.insert(*n) {
                out.push(*n);
            }
        }
    });
    for c in [0i128, 1] {
        if seen.insert(c) {
            out.push(c);
        }
    }
    out.sort_by_key(|c| (c.unsigned_abs(), *c));
    out.truncate(QUAL_MINE_MAX_INT_CONSTS);
    out
}

/// BV constants per width, smallest first, deduped and capped; 0 and 1 are
/// always seeded (counter idioms).
fn harvest_bv_constants(problem: &ChcProblem) -> FxHashMap<u32, Vec<u128>> {
    let mut seen: FxHashMap<u32, DetHashSet<u128>> = FxHashMap::default();
    let mut widths: FxHashMap<u32, Vec<u128>> = FxHashMap::default();
    visit_all_exprs(problem, &mut |e| {
        if let ChcExpr::BitVec(v, w) = e {
            if seen.entry(*w).or_default().insert(*v) {
                widths.entry(*w).or_default().push(*v);
            }
        }
    });
    // Widths present as SORTS (not just literals): a predicate can carry a
    // BV arg whose width never appears as a constant literal.
    for pred in problem.predicates() {
        for sort in &pred.arg_sorts {
            if let ChcSort::BitVec(w) = sort {
                widths.entry(*w).or_default();
            }
        }
    }
    for (w, vals) in widths.iter_mut() {
        let s = seen.entry(*w).or_default();
        for c in [0u128, 1] {
            if s.insert(c) {
                vals.push(c);
            }
        }
        vals.sort_unstable();
        vals.truncate(QUAL_MINE_MAX_BV_CONSTS);
    }
    widths
}

/// Visit every expression in the problem (constraints, predicate args).
fn visit_all_exprs(problem: &ChcProblem, f: &mut impl FnMut(&ChcExpr)) {
    let visit = |root: &ChcExpr, f: &mut dyn FnMut(&ChcExpr)| {
        let mut stack: Vec<&ChcExpr> = vec![root];
        while let Some(e) = stack.pop() {
            f(e);
            match e {
                ChcExpr::Op(_, args)
                | ChcExpr::PredicateApp(_, _, args)
                | ChcExpr::FuncApp(_, _, args) => stack.extend(args.iter().map(|a| a.as_ref())),
                ChcExpr::ConstArray(_, inner) => stack.push(inner.as_ref()),
                _ => {}
            }
        }
    };
    for clause in problem.clauses() {
        if let Some(c) = &clause.body.constraint {
            visit(c, f);
        }
        for (_, args) in &clause.body.predicates {
            for a in args {
                visit(a, f);
            }
        }
        if let ClauseHead::Predicate(_, args) = &clause.head {
            for a in args {
                visit(a, f);
            }
        }
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ClauseBody, ClauseHead, HornClause};

    fn int_var(name: &str) -> ChcVar {
        ChcVar::new(name, ChcSort::Int)
    }

    fn bv_var(name: &str, w: u32) -> ChcVar {
        ChcVar::new(name, ChcSort::BitVec(w))
    }

    /// Two predicates sharing a variable in one clause: an atom over the
    /// shared variable must be mined into BOTH pools (propagation).
    #[test]
    fn atoms_propagate_between_argument_sharing_predicates() {
        let mut problem = crate::ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
        let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
        let x = int_var("x");
        let y = int_var("y");

        // P(x, y) ∧ x ≥ 7 ⇒ Q(x)
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(p, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())])],
                Some(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(7))),
            ),
            ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
        ));

        let mined = MinedQualifiers::mine(&problem);
        let pv = vec![int_var("a0"), int_var("a1")];
        let qv = vec![int_var("b0")];
        let p_quals = mined.for_predicate(p, &pv);
        let q_quals = mined.for_predicate(q, &qv);

        let p_has = p_quals
            .iter()
            .any(|e| *e == ChcExpr::ge(ChcExpr::var(pv[0].clone()), ChcExpr::int(7)));
        let q_has = q_quals
            .iter()
            .any(|e| *e == ChcExpr::ge(ChcExpr::var(qv[0].clone()), ChcExpr::int(7)));
        assert!(p_has, "atom x ≥ 7 missing from P pool: {p_quals:?}");
        assert!(q_has, "atom x ≥ 7 not propagated to Q pool: {q_quals:?}");
    }

    /// Same-sort Int pairs produce difference qualifiers against harvested
    /// constants.
    #[test]
    fn int_difference_terms_generated() {
        let mut problem = crate::ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
        let x = int_var("x");
        let y = int_var("y");
        // x = 5 ⇒ P(x, y)
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5))),
            ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())]),
        ));

        let mined = MinedQualifiers::mine(&problem);
        let tv = vec![int_var("a0"), int_var("a1")];
        let quals = mined.for_predicate(p, &tv);
        let diff = ChcExpr::sub(ChcExpr::var(tv[0].clone()), ChcExpr::var(tv[1].clone()));
        let want = ChcExpr::le(diff, ChcExpr::int(5));
        assert!(
            quals.iter().any(|e| *e == want),
            "difference qualifier a0 - a1 ≤ 5 missing: {quals:?}"
        );
    }

    /// BV pairs produce bvsub differences BOTH directions and the
    /// wraparound-distance conditional-abs shape.
    #[test]
    fn bv_difference_and_wraparound_terms_generated() {
        let mut problem = crate::ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::BitVec(8), ChcSort::BitVec(8)]);
        let x = bv_var("x", 8);
        let y = bv_var("y", 8);
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(3, 8))),
            ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())]),
        ));

        let mined = MinedQualifiers::mine(&problem);
        let tv = vec![bv_var("a0", 8), bv_var("a1", 8)];
        let quals = mined.for_predicate(p, &tv);
        let (a0, a1) = (ChcExpr::var(tv[0].clone()), ChcExpr::var(tv[1].clone()));
        let d_ij = bv_binop(ChcOp::BvSub, a0.clone(), a1.clone());
        let d_ji = bv_binop(ChcOp::BvSub, a1, a0);
        let has_ij = quals
            .iter()
            .any(|e| *e == ChcExpr::bv_ule(d_ij.clone(), ChcExpr::BitVec(3, 8)));
        let has_ji = quals
            .iter()
            .any(|e| *e == ChcExpr::bv_ule(d_ji.clone(), ChcExpr::BitVec(3, 8)));
        assert!(has_ij && has_ji, "bvsub differences missing: {quals:?}");
        let wd = ChcExpr::ite(
            bv_binop(ChcOp::BvSGe, d_ij.clone(), ChcExpr::BitVec(0, 8)),
            d_ij.clone(),
            bv_unop(ChcOp::BvNeg, d_ij),
        );
        assert!(
            quals
                .iter()
                .any(|e| *e == ChcExpr::bv_ule(wd.clone(), ChcExpr::BitVec(3, 8))),
            "wraparound-distance qualifier missing: {quals:?}"
        );
    }

    /// Self-loop with x' = x+1, y' = y+2 yields the scaled difference
    /// 2·a0 − 1·a1 and unmodified-arg equality for the untouched pair.
    #[test]
    fn loop_templates_scaled_differences_and_unmodified_equalities() {
        let mut problem = crate::ChcProblem::new();
        let p = problem.declare_predicate(
            "P",
            vec![ChcSort::Int, ChcSort::Int, ChcSort::Int, ChcSort::Int],
        );
        let (x, y, u, v) = (int_var("x"), int_var("y"), int_var("u"), int_var("v"));
        let args = vec![
            ChcExpr::var(x.clone()),
            ChcExpr::var(y.clone()),
            ChcExpr::var(u.clone()),
            ChcExpr::var(v.clone()),
        ];
        // P(x,y,u,v) ⇒ P(x+1, y+2, u, v)
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(p, args)], None),
            ClauseHead::Predicate(
                p,
                vec![
                    ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                    ChcExpr::add(ChcExpr::var(y.clone()), ChcExpr::int(2)),
                    ChcExpr::var(u.clone()),
                    ChcExpr::var(v.clone()),
                ],
            ),
        ));

        let mined = MinedQualifiers::mine(&problem);
        let tv = vec![int_var("a0"), int_var("a1"), int_var("a2"), int_var("a3")];
        let quals = mined.for_predicate(p, &tv);
        // Scaled difference 2·a0 − 1·a1 = 0 (x incremented by 1, y by 2).
        let term = ChcExpr::sub(
            ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(tv[0].clone())),
            ChcExpr::mul(ChcExpr::int(1), ChcExpr::var(tv[1].clone())),
        );
        assert!(
            quals
                .iter()
                .any(|e| *e == ChcExpr::eq(term.clone(), ChcExpr::int(0))),
            "scaled difference 2·a0 − a1 = 0 missing: {quals:?}"
        );
        // Unmodified-arg equality a2 = a3.
        let eq = ChcExpr::eq(ChcExpr::var(tv[2].clone()), ChcExpr::var(tv[3].clone()));
        assert!(
            quals.iter().any(|e| *e == eq),
            "unmodified-arg equality a2 = a3 missing: {quals:?}"
        );
    }

    /// Pools are deduped and capped at the documented limit.
    #[test]
    fn pools_are_deduped_and_capped() {
        let mut problem = crate::ChcProblem::new();
        let sorts: Vec<ChcSort> = (0..8).map(|_| ChcSort::Int).collect();
        let p = problem.declare_predicate("P", sorts);
        let vars: Vec<ChcVar> = (0..8).map(|i| int_var(&format!("x{i}"))).collect();
        let args: Vec<ChcExpr> = vars.iter().map(|v| ChcExpr::var(v.clone())).collect();
        // Many constants so the ladders saturate the cap.
        let mut constraints: Vec<ChcExpr> = Vec::new();
        for (i, v) in vars.iter().enumerate() {
            constraints.push(ChcExpr::ge(ChcExpr::var(v.clone()), ChcExpr::int(i as i64)));
        }
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::and_all(constraints)),
            ClauseHead::Predicate(p, args.clone()),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(p, args.clone())], None),
            ClauseHead::Predicate(
                p,
                args.iter()
                    .map(|a| ChcExpr::add(a.clone(), ChcExpr::int(1)))
                    .collect(),
            ),
        ));

        let mined = MinedQualifiers::mine(&problem);
        assert!(
            mined.total() <= QUAL_MINE_MAX_PER_PRED,
            "pool exceeds cap: {}",
            mined.total()
        );
        let tv: Vec<ChcVar> = (0..8).map(|i| int_var(&format!("a{i}"))).collect();
        let quals = mined.for_predicate(p, &tv);
        let mut seen: DetHashSet<ChcExpr> = DetHashSet::default();
        for q in &quals {
            assert!(seen.insert(q.clone()), "duplicate qualifier: {q:?}");
        }
    }

    /// Sort-mismatched instantiation fails safe (empty).
    #[test]
    fn for_predicate_sort_mismatch_returns_empty() {
        let mut problem = crate::ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Int]);
        let x = int_var("x");
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0))),
            ClauseHead::Predicate(p, vec![ChcExpr::var(x)]),
        ));
        let mined = MinedQualifiers::mine(&problem);
        assert!(mined.for_predicate(p, &[bv_var("a0", 8)]).is_empty());
    }

    /// vmt skeleton (4 Bools + BV data): the mixed class (g) emits the full
    /// control-cube oracle rows `±b₀∨±b₁∨±b₂∨±b₃∨(bvadd(x,y)=c)` and the
    /// pair rows `±bᵢ∨±bⱼ∨(x=y)`.
    #[test]
    fn mixed_control_data_clauses_emit_oracle_shape() {
        let mut problem = crate::ChcProblem::new();
        let p = problem.declare_predicate(
            "P",
            vec![
                ChcSort::Bool,
                ChcSort::Bool,
                ChcSort::Bool,
                ChcSort::Bool,
                ChcSort::BitVec(8),
                ChcSort::BitVec(8),
            ],
        );
        let bs: Vec<ChcVar> = (0..4)
            .map(|i| ChcVar::new(format!("b{i}"), ChcSort::Bool))
            .collect();
        let (x, y) = (bv_var("x", 8), bv_var("y", 8));
        let mut args: Vec<ChcExpr> = bs.iter().map(|b| ChcExpr::var(b.clone())).collect();
        args.push(ChcExpr::var(x.clone()));
        args.push(ChcExpr::var(y.clone()));
        // x = 3 ⇒ P(b0..b3, x, y) — harvests the width-8 constant 3 (the
        // seeded 0/1 sort ahead of it) and one class-(a) atom.
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(3, 8))),
            ClauseHead::Predicate(p, args),
        ));

        let mined = MinedQualifiers::mine(&problem);
        let tv = vec![
            ChcVar::new("c0", ChcSort::Bool),
            ChcVar::new("c1", ChcSort::Bool),
            ChcVar::new("c2", ChcSort::Bool),
            ChcVar::new("c3", ChcSort::Bool),
            bv_var("a4", 8),
            bv_var("a5", 8),
        ];
        let quals = mined.for_predicate(p, &tv);
        let ctrl: Vec<ChcExpr> = tv[..4].iter().map(|v| ChcExpr::var(v.clone())).collect();
        let (a4, a5) = (ChcExpr::var(tv[4].clone()), ChcExpr::var(tv[5].clone()));

        // Full 4-Bool cube ∨ (bvadd(a4,a5) = 0) — the 5-literal oracle row
        // (mask 0 = all-positive control literals).
        let sum_eq = ChcExpr::eq(
            bv_binop(ChcOp::BvAdd, a4.clone(), a5.clone()),
            ChcExpr::BitVec(0, 8),
        );
        let want_cube = ChcExpr::or_all([
            ctrl[0].clone(),
            ctrl[1].clone(),
            ctrl[2].clone(),
            ctrl[3].clone(),
            sum_eq,
        ]);
        assert!(
            quals.iter().any(|e| *e == want_cube),
            "full-control-cube mixed row missing: pool size {}",
            quals.len()
        );

        // Pair row: b0 ∨ b1 ∨ (a4 = a5) — the 3-literal mixed shape.
        let want_pair = ChcExpr::or_all([
            ctrl[0].clone(),
            ctrl[1].clone(),
            ChcExpr::eq(a4.clone(), a5.clone()),
        ]);
        assert!(
            quals.iter().any(|e| *e == want_pair),
            "2-control-literal mixed row missing"
        );

        // Signed variant present too (¬b0 ∨ b1 ∨ (a4 = a5)).
        let want_signed = ChcExpr::or_all([
            ChcExpr::not(ctrl[0].clone()),
            ctrl[1].clone(),
            ChcExpr::eq(a4, a5),
        ]);
        assert!(
            quals.iter().any(|e| *e == want_signed),
            "negated-control mixed row missing"
        );
    }

    /// The mixed-class kill switch is honored by the env probe.
    #[test]
    fn mixed_kill_switch_env_var() {
        // SAFETY: test-local env mutation; no other test reads this var.
        std::env::set_var("AY_CHC_DISABLE_QUAL_MIXED", "1");
        assert!(!qual_mixed_enabled());
        std::env::remove_var("AY_CHC_DISABLE_QUAL_MIXED");
        assert!(qual_mixed_enabled());
    }

    /// Kill switch is honored by the env probe.
    #[test]
    fn kill_switch_env_var() {
        // SAFETY: test-local env mutation; no other test reads this var.
        std::env::set_var("AY_CHC_DISABLE_QUAL_MINE", "1");
        assert!(!qual_mine_enabled());
        std::env::remove_var("AY_CHC_DISABLE_QUAL_MINE");
        assert!(qual_mine_enabled());
    }
}
