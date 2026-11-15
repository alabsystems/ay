// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `lemma_from_cores` — Spacer's `l_false` arm + `lemma_inductive_generalizer`
//! (`DESIGN` §4.2.3). Owner: **WP-B1-L**.
//!
//! Phases: 0 seed confirmation (D1/D4) → A core recovery (QuickXplain) →
//! B drop round at the CURRENT `lvl` (`Hyp::Inductive`, confirm-then-adopt
//! multi-drops, within-run CTP) → C weakening (R5, not in R1) → D level climb
//! (legacy) → `Lemma::new(pred, ¬cube, lvl)`. Properties (i)–(iv) of §4.2.3
//! are the soundness contract (S2):
//!
//! 1. every adopted `mask` is justified at `lvl` by an OBSERVED UNSAT of
//!    `Reach` (Phase 0/A) or `Inductive` (Phase B/D) over that very sub-cube,
//!    or by the Q1 UNSATs (untainted all-true seed);
//! 2. every Phase B/D query is issued at the current `lvl`;
//! 3. `¬K ⇒ ¬cand` for `K ⊆ cand`, so adopting a confirmed core keeps
//!    `F ∧ ¬K ∧ T ∧ K'` UNSAT;
//! 4. `lemma_false` is emitted only after an observed UNSAT of `F_{lvl-1} ∧ T`
//!    for every clause (Phase 0 on the empty seed).

#![allow(dead_code, unused)]

use super::oracle::{Budget, Hyp, Verdict};
use crate::pdr::config::DropOrder;
use crate::pdr::cube::literals::LitCube;
use crate::pdr::frame::Lemma;
use crate::pdr::solver::blocking::ClauseCore;
use crate::pdr::solver::{PdrSolver, ProofObligation};
use crate::smt::SmtValue;
use crate::{ChcExpr, ChcOp, ChcSort, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::time::Duration;

/// Why no lemma was minted (both ⇒ `BlockResult::Unknown`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::pdr::solver) enum DeriveError {
    /// INV-L3: exclusions are not frame facts.
    ExclusionDependent,
    /// The exclusion-free Reach oracle (fact variables renamed apart) found a
    /// MODEL of the full cube although every Q1 answered UNSAT and no
    /// exclusion was involved: the Q1 UNSAT is not a sound justification, so
    /// no lemma is inserted (fail-closed; S2). Counted `q1_seed_refuted`.
    SeedRefuted,
}

/// One stored Q2 counter-model for the within-run CTP check: the clause it
/// came from (its head/body argument vectors are what the evaluation needs)
/// and the level the query was issued at (models are valid only for
/// candidates checked at the same level, `F_{lvl-1}` being fixed there).
struct CtpModel {
    clause_index: usize,
    level: usize,
    model: FxHashMap<String, SmtValue>,
}

/// Literal classes of the `PinsFirst` drop order (`DESIGN` §7.3): pins,
/// var–var equalities, arithmetic bounds/atoms, Booleans last (the guards
/// that make the arithmetic literals jointly inductive).
fn drop_class(lit: &ChcExpr) -> u8 {
    fn is_const(e: &ChcExpr) -> bool {
        matches!(
            e,
            ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::Bool(_) | ChcExpr::BitVec(_, _)
        )
    }
    fn is_arith_var(e: &ChcExpr) -> bool {
        matches!(e, ChcExpr::Var(v) if !matches!(v.sort, ChcSort::Bool))
    }
    match lit {
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            let (a, b) = (&*args[0], &*args[1]);
            if (is_arith_var(a) && is_const(b)) || (is_arith_var(b) && is_const(a)) {
                0
            } else if is_arith_var(a) && is_arith_var(b) {
                1
            } else if matches!(a, ChcExpr::Var(v) if matches!(v.sort, ChcSort::Bool))
                || matches!(b, ChcExpr::Var(v) if matches!(v.sort, ChcSort::Bool))
                || matches!(a, ChcExpr::Op(ChcOp::Eq, _))
                || matches!(b, ChcExpr::Op(ChcOp::Eq, _))
                || matches!(a, ChcExpr::Bool(_))
                || matches!(b, ChcExpr::Bool(_))
            {
                3
            } else {
                2
            }
        }
        ChcExpr::Op(ChcOp::Le | ChcOp::Lt | ChcOp::Ge | ChcOp::Gt | ChcOp::Ne, _) => 2,
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => match &*args[0] {
            ChcExpr::Var(_) => 3,
            inner => drop_class(inner).max(2),
        },
        ChcExpr::Var(_) | ChcExpr::Bool(_) => 3,
        ChcExpr::Op(ChcOp::Or | ChcOp::And | ChcOp::Implies | ChcOp::Iff | ChcOp::Ite, _) => 3,
        _ => 2,
    }
}

/// Indices of the kept literals in Phase B order.
fn drop_order(full: &LitCube, mask: &[bool], order: DropOrder) -> Vec<usize> {
    let mut idx: Vec<usize> = (0..full.len()).filter(|&i| mask[i]).collect();
    if order == DropOrder::PinsFirst {
        let lits = full.lits();
        idx.sort_by_key(|&i| drop_class(&lits[i]));
    }
    idx
}

fn count(m: &[bool]) -> usize {
    m.iter().filter(|b| **b).count()
}

/// Compose a core over the literals of `full.subset(mask)` (positional) back
/// onto `full`'s indices. `LitCube::subset` keeps the kept literals in order
/// and `full` carries no duplicates, so the correspondence is 1:1.
fn compose(mask: &[bool], sub_core: &[bool]) -> Vec<bool> {
    let mut out = vec![false; mask.len()];
    let mut j = 0;
    for (i, keep) in mask.iter().enumerate() {
        if *keep {
            if j < sub_core.len() && sub_core[j] {
                out[i] = true;
            }
            j += 1;
        }
    }
    out
}

impl PdrSolver {
    /// `Budget { deadline: min(solve_deadline, now + ind_gen_time_share × remaining),
    /// per_call: min(2 s, remaining/8), max_calls: ind_gen_max_queries }` (§5).
    pub(in crate::pdr::solver) fn ind_gen_budget(&self) -> Budget {
        let lane = &self.config.spacer;
        let now = ay_core::time::Instant::now();
        let remaining = self
            .solve_deadline
            .map(|d| d.saturating_duration_since(now));
        let deadline = remaining.map(|rem| {
            let share = rem.mul_f32(lane.ind_gen_time_share.clamp(0.0, 1.0));
            now + share
        });
        let per_call = match remaining {
            Some(rem) => Duration::from_secs(2)
                .min(rem / 8)
                .max(Duration::from_millis(50)),
            None => Duration::from_secs(2),
        };
        Budget::new(deadline, per_call, lane.ind_gen_max_queries.max(1))
    }

    /// Spacer's `l_false` arm + `lemma_inductive_generalizer`. Returns a lemma
    /// unless INV-L3 fires. See `DESIGN` §4.2.3 for the phase pseudocode.
    pub(in crate::pdr::solver) fn lemma_from_cores(
        &mut self,
        pob: &ProofObligation,
        cores: &[ClauseCore],
        unknown_predecessors: &[(usize, PredicateId, ChcExpr)],
    ) -> Result<Lemma, DeriveError> {
        let started = ay_core::time::Instant::now();
        let full = pob.cube();
        let n = full.len();
        let pred = pob.predicate;
        let lane = self.config.spacer;
        let mut budget = self.ind_gen_budget();
        let top = self.frames.len().saturating_sub(1);
        let mut lvl = pob.level;
        let verbose = self.config.verbose;

        // ---- Coverage (INV-L1): the seed is the union of the per-clause cores;
        // a relevant clause without a record is all-true inexact.
        let relevant: Vec<usize> = self
            .problem
            .clauses_defining_with_index(pred)
            .filter(|(_, c)| {
                matches!(c.head, crate::ClauseHead::Predicate(..)) && (pob.level > 0 || c.is_fact())
            })
            .map(|(i, _)| i)
            .collect();
        let mut mask = vec![false; n];
        let mut exact = true;
        for ci in &relevant {
            let mut recs = cores.iter().filter(|c| c.clause_index == *ci).peekable();
            if recs.peek().is_none() {
                if self.clause_vacuous_at(*ci, pob.level) {
                    // A single-body clause whose body predicate has no fact
                    // at frame index 0: no Q1 query exists, the clause is
                    // UNSAT with the empty core (exactly what the oracle
                    // answers for it).
                    continue;
                }
                mask = vec![true; n];
                exact = false;
                continue;
            }
            for rec in recs {
                if rec.core.len() != n {
                    mask = vec![true; n];
                    exact = false;
                    continue;
                }
                for (m, c) in mask.iter_mut().zip(rec.core.iter()) {
                    *m |= *c;
                }
                exact &= rec.exact;
            }
        }
        if !lane.core_lemma {
            mask = vec![true; n];
            exact = false;
        }
        let tainted = cores.iter().any(|c| c.had_exclusion);
        let all_true = |m: &[bool]| m.iter().all(|b| *b);
        self.spacer_stats.seed_core_size_hist.add(count(&mask));

        // ---- Phase 0 — seed confirmation (D1/D4). Also forced for an EMPTY
        // seed whatever its exactness: lemma `false` needs its own observed
        // UNSAT (property iv).
        let seed_empty = mask.iter().all(|b| !*b);
        let seed_mask = mask.clone();
        if tainted || seed_empty || (lane.confirm_cores && exact && !all_true(&mask)) {
            self.spacer_stats.core_confirm_checks += 1;
            let sub = full.subset(&mask);
            match self.oracle_check_all_clauses(pred, lvl, &sub, Hyp::Reach, &mut budget) {
                Verdict::Unsat { core, exact: e, .. } => {
                    exact = true;
                    // The confirmation's own core can only shrink the seed;
                    // a shrink of ≥ 2 literals is worth one more Reach check
                    // (a single literal is left to its Phase B round), and
                    // the EMPTY core is always confirmed before it can become
                    // lemma `false`.
                    if e {
                        let k = compose(&mask, &core);
                        let shrink = count(&mask).saturating_sub(count(&k));
                        let k_empty = k.iter().all(|b| !*b);
                        if shrink >= 2 || (k_empty && shrink >= 1) {
                            if lane.confirm_cores || k_empty {
                                self.spacer_stats.core_confirm_checks += 1;
                                let ksub = full.subset(&k);
                                match self.oracle_check_all_clauses(
                                    pred,
                                    lvl,
                                    &ksub,
                                    Hyp::Reach,
                                    &mut budget,
                                ) {
                                    Verdict::Unsat { .. } => mask = k,
                                    Verdict::Sat(_) => {
                                        self.spacer_stats.core_confirm_disagree += 1;
                                        self.note_disagree("phase0-shrink", pred, lvl, &full, &k);
                                    }
                                    Verdict::Unknown => {
                                        self.spacer_stats.core_confirm_unknown += 1;
                                    }
                                }
                            } else {
                                mask = k;
                            }
                        }
                    }
                }
                v => {
                    let sub_sat = matches!(v, Verdict::Sat(_));
                    if !sub_sat {
                        self.spacer_stats.core_confirm_unknown += 1;
                    }
                    // `full_sat`: the oracle has a model of the FULL cube;
                    // `full_unsat`: it observed the full cube UNSAT.
                    let (full_sat, full_unsat) = if all_true(&mask) {
                        (sub_sat, false)
                    } else {
                        mask = vec![true; n];
                        exact = false;
                        // Retry once with the full cube. UNSAT ⇒ the strict
                        // subset was a genuine core defect (disagreement).
                        match self.oracle_check_all_clauses(
                            pred,
                            lvl,
                            &full,
                            Hyp::Reach,
                            &mut budget,
                        ) {
                            Verdict::Unsat { .. } => {
                                if sub_sat {
                                    self.spacer_stats.core_confirm_disagree += 1;
                                    self.note_disagree("phase0-seed", pred, lvl, &full, &seed_mask);
                                }
                                (false, true)
                            }
                            Verdict::Sat(_) => (true, false),
                            Verdict::Unknown => (false, false),
                        }
                    };
                    if full_sat || (tainted && !full_unsat) {
                        // Tainted and not re-established exclusion-free
                        // (SAT or Unknown) ⇒ INV-L3 (D4) ⇒ Unknown.
                        if tainted {
                            if verbose {
                                safe_eprintln!(
                                    "PDR-SPACER: INV-L3: exclusion-dependent block at level {} (pred {}) — Unknown",
                                    lvl,
                                    pred.index()
                                );
                            }
                            return Err(DeriveError::ExclusionDependent);
                        }
                        // Untainted with a MODEL of the full cube: the Q1
                        // UNSAT is not a sound justification (this is how the
                        // level-1 fact-local capture showed up before the
                        // per-fact Q1 renamed facts apart under the lane) ⇒
                        // no lemma (fail-closed; S2).
                        self.spacer_stats.q1_seed_refuted += 1;
                        if verbose {
                            safe_eprintln!(
                                "PDR-SPACER: seed refuted: Reach(full cube) SAT at level {} for pred {} while every Q1 was UNSAT (q1_seed_refuted) — no lemma, Unknown",
                                lvl,
                                pred.index()
                            );
                        }
                        return Err(DeriveError::SeedRefuted);
                    }
                    // Untainted, full cube UNSAT or undecided: the Q1 UNSATs
                    // justify the full seed (§4.2.3 Phase 0).
                }
            }
        }

        // ---- Phase A — core recovery when the seed is inexact (a refuted
        // seed never reaches here: QuickXplain's precondition is its UNSAT).
        if !exact
            && lane.core_lemma
            && count(&mask) > 1
            && !budget.exhausted()
            && !self.is_cancelled()
        {
            // A-0 (LIA/Bool only): one Reach oracle call on the current mask
            // returns the union of the per-clause PROXIED cores — exact when
            // every clause's is. This repairs the inexact records P cannot
            // refine (the `propagate_equalities` shortcut is all-true inexact
            // by the C2 coverage rule) at `c` verdict + `c` core solves
            // instead of QuickXplain's `≈ (2k·log2(n/k) + 2k) × c`.
            let mut recovered = false;
            let mut a0_undecided = false;
            if self.lane_lia_ok(&[]) {
                self.spacer_stats.ind_gen_queries_a += 1;
                let sub = full.subset(&mask);
                match self.oracle_check_all_clauses(pred, lvl, &sub, Hyp::Reach, &mut budget) {
                    Verdict::Sat(_) if all_true(&mask) => {
                        // The FULL cube has a model exclusion-free: the Q1
                        // UNSATs are not a sound justification (see Phase 0).
                        if tainted {
                            return Err(DeriveError::ExclusionDependent);
                        }
                        self.spacer_stats.q1_seed_refuted += 1;
                        if verbose {
                            safe_eprintln!(
                                "PDR-SPACER: seed refuted in Phase A-0 at level {} for pred {} (q1_seed_refuted) — no lemma, Unknown",
                                lvl,
                                pred.index()
                            );
                        }
                        return Err(DeriveError::SeedRefuted);
                    }
                    Verdict::Sat(_) => {
                        // A strict sub-cube (an earlier adopted core) has a
                        // model: that core was wrong. Fall back to the full
                        // cube, which QuickXplain then minimises from its
                        // own observed UNSAT (checked below).
                        self.spacer_stats.core_confirm_disagree += 1;
                        self.note_disagree("phaseA0", pred, lvl, &full, &mask);
                        mask = vec![true; n];
                    }
                    Verdict::Unknown => a0_undecided = true,
                    Verdict::Unsat { exact: false, .. } => {}
                    Verdict::Unsat { core, .. } => {
                        let k = compose(&mask, &core);
                        let k_empty = k.iter().all(|b| !*b);
                        if count(&k) < count(&mask) {
                            if lane.confirm_cores || k_empty {
                                self.spacer_stats.core_confirm_checks += 1;
                                let ksub = full.subset(&k);
                                match self.oracle_check_all_clauses(
                                    pred,
                                    lvl,
                                    &ksub,
                                    Hyp::Reach,
                                    &mut budget,
                                ) {
                                    Verdict::Unsat { .. } => {
                                        mask = k;
                                        recovered = true;
                                    }
                                    Verdict::Sat(_) => {
                                        self.spacer_stats.core_confirm_disagree += 1;
                                        self.note_disagree("phaseA0", pred, lvl, &full, &k);
                                    }
                                    Verdict::Unknown => {
                                        self.spacer_stats.core_confirm_unknown += 1;
                                    }
                                }
                            } else {
                                mask = k;
                                recovered = true;
                            }
                        } else {
                            // The mask IS its own exact core.
                            recovered = true;
                        }
                    }
                }
            }
            if recovered {
                exact = true;
            } else if !a0_undecided
                && count(&mask) > 1
                && !budget.exhausted()
                && !self.is_cancelled()
            {
                let (m, ex) = self.quickxplain_reach(pred, lvl, &full, &mask, &mut budget);
                mask = m;
                exact = ex;
            }
        }

        // ---- Phase B — Spacer round 1 over Hyp::Inductive at the current lvl.
        let mut ctp: Vec<CtpModel> = Vec::new();
        if lane.ind_gen && n > 0 {
            let order = drop_order(&full, &mask, lane.drop_order);
            for i in order {
                if !mask[i] {
                    continue; // dropped by an adopted multi-drop core
                }
                if self.is_cancelled() {
                    break;
                }
                if budget.exhausted() {
                    break; // counted once by record_lemma
                }
                let mut cand = mask.clone();
                cand[i] = false;
                if cand.iter().all(|b| !*b) {
                    continue;
                }
                if self.within_run_ctp_rejects(pred, lvl, &full, &cand, &ctp) {
                    self.spacer_stats.ctp_skips += 1;
                    continue;
                }
                self.spacer_stats.ind_gen_queries_b += 1;
                let sub = full.subset(&cand);
                let (v, sat_clause) =
                    self.oracle_check_all_clauses_ex(pred, lvl, &sub, Hyp::Inductive, &mut budget);
                match v {
                    Verdict::Unsat {
                        core,
                        exact: true,
                        uses_level,
                    } => {
                        let k = compose(&cand, &core);
                        let extra = count(&cand).saturating_sub(count(&k));
                        if k.iter().all(|b| !*b) || extra < 2 {
                            // Empty K ⇒ treated as inexact; a single extra
                            // drop is left to its own round.
                            mask = cand;
                        } else if lane.confirm_cores {
                            self.spacer_stats.core_confirm_checks += 1;
                            let ksub = full.subset(&k);
                            let (cv, cclause) = self.oracle_check_all_clauses_ex(
                                pred,
                                lvl,
                                &ksub,
                                Hyp::Inductive,
                                &mut budget,
                            );
                            match cv {
                                Verdict::Unsat { .. } => mask = k,
                                Verdict::Sat(m) => {
                                    mask = cand;
                                    self.spacer_stats.core_confirm_disagree += 1;
                                    self.note_disagree("phaseB", pred, lvl, &full, &k);
                                    if let Some(ci) = cclause {
                                        self.store_ctp_model(&mut ctp, ci, lvl, pred, &ksub, m);
                                    }
                                }
                                Verdict::Unknown => {
                                    mask = cand;
                                    self.spacer_stats.core_confirm_unknown += 1;
                                }
                            }
                        } else {
                            mask = k;
                        }
                        if let Some(u) = uses_level {
                            let u = u.min(top);
                            if u > lvl {
                                self.spacer_stats.uses_level_jumps += 1;
                                lvl = u;
                            }
                        }
                    }
                    Verdict::Unsat { exact: false, .. } => mask = cand,
                    Verdict::Sat(m) => {
                        if let Some(ci) = sat_clause {
                            self.store_ctp_model(&mut ctp, ci, lvl, pred, &sub, m);
                        }
                    }
                    Verdict::Unknown => self.spacer_stats.ind_gen_unknown += 1,
                }
            }
        }

        // ---- Phase D — level climb (legacy backend).
        if lane.ind_gen && lane.eager_push_levels > 0 {
            let max_k = top.min(lvl.saturating_add(lane.eager_push_levels));
            let mut k = lvl + 1;
            while k <= max_k {
                if self.is_cancelled() || budget.exhausted() {
                    break; // exhaustion counted once by record_lemma
                }
                self.spacer_stats.ind_gen_queries_d += 1;
                let sub = full.subset(&mask);
                let (v, sat_clause) =
                    self.oracle_check_all_clauses_ex(pred, k, &sub, Hyp::Inductive, &mut budget);
                match v {
                    Verdict::Unsat {
                        core, exact: true, ..
                    } => {
                        lvl = k;
                        let kmask = compose(&mask, &core);
                        let extra = count(&mask).saturating_sub(count(&kmask));
                        if !kmask.iter().all(|b| !*b) && extra >= 2 {
                            if lane.confirm_cores {
                                self.spacer_stats.core_confirm_checks += 1;
                                let ksub = full.subset(&kmask);
                                match self.oracle_check_all_clauses(
                                    pred,
                                    k,
                                    &ksub,
                                    Hyp::Inductive,
                                    &mut budget,
                                ) {
                                    Verdict::Unsat { .. } => mask = kmask,
                                    Verdict::Sat(_) => {
                                        self.spacer_stats.core_confirm_disagree += 1;
                                        self.note_disagree("phaseD", pred, k, &full, &kmask);
                                    }
                                    Verdict::Unknown => {
                                        self.spacer_stats.core_confirm_unknown += 1;
                                    }
                                }
                            } else {
                                mask = kmask;
                            }
                        }
                    }
                    Verdict::Unsat { exact: false, .. } => lvl = k,
                    Verdict::Sat(m) => {
                        if let Some(ci) = sat_clause {
                            self.store_ctp_model(&mut ctp, ci, k, pred, &sub, m);
                        }
                        break;
                    }
                    Verdict::Unknown => break,
                }
                k += 1;
            }
        }

        // ---- The lemma.
        let cube = full.subset(&mask);
        let generalized = cube.len() < n || lvl > pob.level;
        self.spacer_stats
            .record_lemma(pob, &full, &cube, lvl, &budget);
        self.spacer_stats.ind_gen_ms_total = self
            .spacer_stats
            .ind_gen_ms_total
            .saturating_add(u64::try_from(started.elapsed().as_millis()).unwrap_or(u64::MAX));
        self.lane_lemma_pending = Some(generalized);
        if verbose {
            safe_eprintln!(
                "PDR-SPACER: lemma for pred {} at level {} (pob level {}): {} of {} literals kept, seed_exact={}, oracle_calls={}",
                pred.index(),
                lvl,
                pob.level,
                cube.len(),
                n,
                exact,
                budget.calls
            );
        }
        let mut lemma = Lemma::new(pred, cube.lemma_formula(), lvl);
        if let Some(clause_idx) = pob.incoming_clause {
            if let Some(action) = self.problem.clause_action(clause_idx) {
                lemma = lemma.with_action(action);
            }
        }
        Ok(lemma)
    }

    /// Verbose diagnostics for a confirmation disagreement (a core strictly
    /// smaller than an UNSAT mask answered SAT under the same oracle).
    fn note_disagree(
        &self,
        phase: &str,
        pred: PredicateId,
        lvl: usize,
        full: &LitCube,
        mask: &[bool],
    ) {
        if self.config.verbose {
            safe_eprintln!(
                "PDR-SPACER: core_confirm_disagree [{}] pred {} level {} mask {}/{}: {}",
                phase,
                pred.index(),
                lvl,
                mask.iter().filter(|b| **b).count(),
                full.len(),
                full.subset(mask).expr()
            );
        }
    }

    /// A clause at `level ≥ 1` whose body frame index is 0 and one of whose
    /// body predicates has no fact clause: no query exists for it and it is
    /// vacuously UNSAT (the oracle answers the empty exact core).
    fn clause_vacuous_at(&self, clause_index: usize, level: usize) -> bool {
        if level != 1 {
            return false;
        }
        let clause = &self.problem.clauses()[clause_index];
        clause
            .body
            .predicates
            .iter()
            .any(|(body_pred, _)| !self.predicate_has_facts(*body_pred))
    }

    /// Record a Q2 counter-model: in the run's CTP list AND in the shared
    /// implication cache at `(pred, level)` (head-arg projection; valid for
    /// the push/legacy consumers, never consulted here — D6).
    fn store_ctp_model(
        &mut self,
        ctp: &mut Vec<CtpModel>,
        clause_index: usize,
        level: usize,
        pred: PredicateId,
        cand: &LitCube,
        model: FxHashMap<String, SmtValue>,
    ) {
        if let Some(clause) = self.problem.clauses().get(clause_index) {
            if let crate::ClauseHead::Predicate(_, head_args) = &clause.head {
                let head_args = head_args.clone();
                let canonical_vars = self.canonical_vars(pred).map(|v| v.to_vec());
                let frame_epoch = self.frames_lemma_epoch();
                super::super::core::record_validated_blocking_countermodel_from_head_args(
                    &mut self.caches.implication_cache,
                    frame_epoch,
                    canonical_vars.as_deref(),
                    pred,
                    level,
                    &head_args,
                    &model,
                    cand.expr(),
                );
            }
        }
        if ctp.len() < 64 {
            ctp.push(CtpModel {
                clause_index,
                level,
                model,
            });
        }
    }

    /// Within-run CTP (§4.2.3): `cand` is rejected without a query iff some
    /// stored Q2 model `m` (issued at this `level`, for clause `c`) satisfies
    /// `cand(head_c)` AND, when the clause's body predicate is `pred`,
    /// `¬cand(body_c)`; `m ⊨ F(body) ∧ T_c` already holds. `eval_bool == None`
    /// (opaque atoms) never rejects.
    fn within_run_ctp_rejects(
        &self,
        pred: PredicateId,
        level: usize,
        full: &LitCube,
        cand: &[bool],
        ctp: &[CtpModel],
    ) -> bool {
        if ctp.is_empty() {
            return false;
        }
        let sub = full.subset(cand);
        for entry in ctp {
            if entry.level != level {
                continue;
            }
            let Some(clause) = self.problem.clauses().get(entry.clause_index) else {
                continue;
            };
            let crate::ClauseHead::Predicate(_, head_args) = &clause.head else {
                continue;
            };
            let Some(on_head) = self.apply_to_args(pred, sub.expr(), head_args) else {
                continue;
            };
            if self.mbp.eval_bool(&on_head, &entry.model) != Some(true) {
                continue;
            }
            // `¬cand` must hold on EVERY body occurrence of `pred` (one on a
            // linear clause, several on a hyperedge of the nonlinear lane).
            let rejects = clause
                .body
                .predicates
                .iter()
                .filter(|(body_pred, _)| *body_pred == pred)
                .all(|(_, body_args)| {
                    self.apply_to_args(pred, sub.expr(), body_args)
                        .is_some_and(|on_body| {
                            self.mbp.eval_bool(&on_body, &entry.model) == Some(false)
                        })
                });
            if rejects {
                return true;
            }
        }
        false
    }
}
