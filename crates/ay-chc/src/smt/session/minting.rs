// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `MintState` / `Minter` — two-tier minting for every `TheoryResult` request
//! (design §2.5, §4; owner WP-2 / B).
//!
//! Tier 1 (inline, continue the same solve via `ExtCheckResult::AddClauses`):
//! T-tautological splits — `NeedDisequalitySplit`, `NeedExpressionSplit(s)`,
//! `NeedLemmas` (cuts), model-equality HINTS (triangle axioms); `NeedSplit`
//! (B&B) and bound refinements are Rung 2. Dedup is by ATOM only (an atom that
//! already has a SAT variable is reused through `tseitin.term_to_var`, F10);
//! the clause is ALWAYS re-added (the deletable tier may have dropped it, and
//! an all-false re-added clause is a pending conflict that moves the search,
//! F6).
//!
//! Tier 2 (originals via the re-entry protocol, §4.2): clauses the theory
//! cannot re-derive and that must not live in ay-sat's deletable learned tier
//! (design F7) — `implied` model equalities (LRA ITE links: `cond => (= ite
//! then)`, `¬cond => (= ite else)`) and the Tseitin definitions of any minted
//! COMPOUND atom (an ITE condition that is `(and ..)`, say). They are buffered
//! in `originals`; the session adds them with `add_clause_global` and
//! re-enters the solve. A batch with any tier-2 clause keeps its inline
//! clauses in `originals` too, so the re-entered solve sees all of them at
//! once.
//!
//! Model equalities MUST use `mk_eq_coerce_no_ite_expand` so LRA's `find_eq`
//! gate (design F12) sees the term and never re-requests.
//!
//! Every minted theory atom is registered with the theory (after
//! `theory.rebind(own)`, §5) and enters the bridge tables — `atom_of_var`,
//! `registered`, `active_atom`, `mint_parent` — BEFORE the batch returns
//! (A-sound M1c). Activity: a split atom follows its guard atom, a triangle
//! atom follows its equality, everything else minted is always active
//! (`MINT_ALWAYS_ACTIVE`), because the session's per-query `active_atom`
//! rebuild knows only the assertions' atoms.

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_core::term::TermData;
use ay_core::{
    is_theory_atom, DisequalitySplitRequest, ExpressionSplitRequest, ModelEqualityRequest, Sort,
    SplitRequest, Symbol, TermId, TheoryLemma, TheoryLit, Tseitin, TseitinState,
};
use ay_sat::{Literal, SolverContext};

use super::bridge::{lit_of, BridgeExit, BridgeState, BridgeStats};
use super::ledger::FarkasLedger;
use super::theory_box::TheoryBox;
use super::{PoisonKind, SessionConfig, UnsupportedKind};
use crate::smt::types::{Partition, SmtValue};
use crate::smt::SmtContext;

/// `BridgeState::mint_parent` marker: the var was not minted by the bridge.
pub(crate) const MINT_NONE: u32 = u32::MAX;
/// `BridgeState::mint_parent` marker: a minted atom that is fed every query.
pub(crate) const MINT_ALWAYS_ACTIVE: u32 = u32::MAX - 1;

pub(crate) enum MintOutcome {
    Inline(Vec<Vec<Literal>>),
    Originals,
    NothingNew,
}

#[derive(Default)]
pub(crate) struct MintState {
    /// Atoms that received a FRESH SAT variable this query (stats; the
    /// authoritative dedup is `tseitin.term_to_var`).
    pub(crate) seen_split_atoms: FxHashSet<TermId>,
    /// Normalised `(min, max)` pairs answered this query.
    pub(crate) seen_model_eq: FxHashSet<(TermId, TermId)>,
    /// All mints this query (every clause produced, inline or original).
    pub(crate) count: u32,
    /// Counted only when a NEW pair is minted (design F23).
    pub(crate) model_eq_rounds: u32,
    /// Tier-2 buffer: clauses that must live in the ORIGINAL ledger.
    pub(crate) originals: Vec<Vec<Literal>>,
    /// Caller's phase-seed model (Rung 2).
    pub(crate) phase_seed: Option<FxHashMap<String, SmtValue>>,
}

impl MintState {
    pub(crate) fn new(phase_seed: Option<FxHashMap<String, SmtValue>>) -> Self {
        Self {
            phase_seed,
            ..Self::default()
        }
    }

    /// Per-solve reset (from `Extension::init`). The bridge — and with it this
    /// state — lives for ONE query; a re-entry (§4.2) is another solve of the
    /// same query, so the per-QUERY counters (`count`, `model_eq_rounds`) and
    /// the pair dedup persist, and only the tier-2 buffer is cleared (the
    /// session drained it with `take_originals` before re-entering; this is
    /// the safety net).
    pub(crate) fn begin_solve(&mut self) {
        self.originals.clear();
    }
}

/// Disjoint borrows of the bridge for ONE mint batch (the design's
/// `var_for(&mut self, b: &mut TheoryBridge, ..)` cannot exist: `self` IS
/// `b.mint`). Built by `TheoryBridge::minter`, consumed by one request.
pub(crate) struct Minter<'a> {
    theory: &'a mut TheoryBox,
    own: &'a mut SmtContext,
    tseitin: &'a mut Option<TseitinState>,
    st: &'a mut BridgeState,
    ledger: &'a mut FarkasLedger,
    mint: &'a mut MintState,
    cfg: &'a SessionConfig,
    stats: &'a mut BridgeStats,
    ctx: &'a dyn SolverContext,
    /// Inline (tier-1) clauses of this batch.
    inline: Vec<Vec<Literal>>,
    /// The batch produced a tier-2 clause (definitions of a compound atom or
    /// an implied equality): everything goes to `originals`.
    tier2: bool,
}

impl<'a> Minter<'a> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        theory: &'a mut TheoryBox,
        own: &'a mut SmtContext,
        tseitin: &'a mut Option<TseitinState>,
        st: &'a mut BridgeState,
        ledger: &'a mut FarkasLedger,
        mint: &'a mut MintState,
        cfg: &'a SessionConfig,
        stats: &'a mut BridgeStats,
        ctx: &'a dyn SolverContext,
    ) -> Self {
        Self {
            theory,
            own,
            tseitin,
            st,
            ledger,
            mint,
            cfg,
            stats,
            ctx,
            inline: Vec::new(),
            tier2: false,
        }
    }

    // ------------------------------------------------------------------
    // The one allocation site: atom -> SAT literal (§2.5 `var_for`)
    // ------------------------------------------------------------------

    /// The SAT literal for `term == value`, allocating a variable when the
    /// encoder has none (§2.5 `var_for`):
    /// - hit in `tseitin.term_to_var` (or the encoder's polarity cache) ->
    ///   reuse (F10; also true for atoms minted in earlier queries);
    /// - miss -> `Tseitin::from_state(&own.terms, take(tseitin))`,
    ///   `ensure_min_next_var(ctx.num_vars() + 1)` (refuse with
    ///   `Poison(VarAliasing)` on the 0 sentinel), `encode(term, true)`,
    ///   `defs = take_new_clauses()`, `into_state()`. Non-empty `defs` means
    ///   `term` is COMPOUND: the definitions go to `originals` and the batch
    ///   becomes tier 2 (§4.2). Every theory atom the encoding named (the term
    ///   itself, or the atoms under a compound) is registered after
    ///   `theory.rebind(own)`, enters the bridge tables, and is tagged in the
    ///   ledger with `p`.
    ///
    /// `parent` is the activity parent recorded for a FRESHLY minted theory
    /// atom (`MINT_ALWAYS_ACTIVE` or a guard var index); an atom that already
    /// had a variable keeps its parent (or none, if it is an assertion atom)
    /// and is simply marked active for this query — the theory asked for it.
    fn lit_for(
        &mut self,
        term: TermId,
        value: bool,
        p: Partition,
        parent: u32,
    ) -> Result<Literal, BridgeExit> {
        if self.own.terms.sort(term) != &Sort::Bool {
            return Err(BridgeExit::Unsupported(UnsupportedKind::IllTyped));
        }
        if let Some(lit) = self.tseitin.as_ref().and_then(|ts| lit_of(ts, term, value)) {
            // Existing variable: make sure the theory sees it this query.
            let v = lit.variable().index();
            self.st.grow(v + 1);
            let was_active = self.st.active_atom[v];
            let mut activated = false;
            if let Some(atom) = self.st.atom_of_var[v] {
                self.st.active_atom[v] = true;
                self.ensure_registered(v, atom);
                activated = !was_active;
            } else if is_theory_atom(&self.own.terms, term)
                && lit_names_term(self.tseitin.as_ref(), lit, term)
            {
                // Named by the encoder before the bridge tables knew it (an
                // atom under a compound the session encoded): adopt it.
                self.st.atom_of_var[v] = Some(term);
                self.st.active_atom[v] = true;
                self.ensure_registered(v, term);
                self.ledger.tag(term, p);
                activated = true;
            }
            if activated && self.st.mint_parent[v] == MINT_NONE {
                // Keep it in the split-atom family: from the next solve on it
                // follows its guard's activity (`refresh_minted_activity`), so
                // it is fed in trail order instead of late.
                self.st.mint_parent[v] = parent;
                self.st.minted_vars.push(v as u32);
            }
            if activated && self.ctx.value(lit.variable()).is_some() {
                // An atom of an INACTIVE assertion (the don't-care filter kept
                // it away from the theory) is reused as a split atom while its
                // literal is ALREADY assigned: the trail position is behind the
                // feed cursor, so the theory would never see it, the split
                // clause is satisfied by it, and LRA re-requests the same split
                // until the §4.1 tripwire fires (WP-4 integration: 45 of the 57
                // ak_s1min replay Unknowns). Queue it for a late feed.
                self.st.late_activated.push(v as u32);
                self.stats.late_activations += 1;
            }
            return Ok(lit);
        }

        let num_vars = self.ctx.num_vars();
        if num_vars == 0 {
            // The trait default: "cannot mint safely".
            return Err(BridgeExit::Poison(PoisonKind::VarAliasing));
        }
        let state = self
            .tseitin
            .take()
            .expect("Tseitin state is returned after every encode batch");
        let mut ts = Tseitin::from_state(&self.own.terms, state);
        ts.ensure_min_next_var(num_vars as u32 + 1);
        let first_new = ts.num_vars() + 1; // DIMACS id of the first fresh variable
        let cnf = ts.encode(term, true);
        let defs = ts.take_new_clauses();
        let state = ts.into_state();
        let lit = {
            let l = Literal::from_dimacs(cnf);
            if value {
                l
            } else {
                l.negated()
            }
        };

        // Every variable the encoding created: bridge tables, theory
        // registration for the atoms among them, ledger tag.
        let mut fresh: Vec<(u32, TermId)> = state
            .var_to_term
            .range(first_new..)
            .map(|(&dv, &t)| (dv, t))
            .collect();
        fresh.sort_unstable();
        let own_var = lit.variable().index() as u32;
        *self.tseitin = Some(state);
        if !fresh.is_empty() {
            self.theory.rebind(self.own);
        }
        for (dv, t) in fresh {
            let v = (dv - 1) as usize;
            self.st.grow(v + 1);
            if !is_theory_atom(&self.own.terms, t) {
                continue;
            }
            self.st.atom_of_var[v] = Some(t);
            self.st.active_atom[v] = true;
            self.st.mint_parent[v] = if v as u32 == own_var {
                parent
            } else {
                MINT_ALWAYS_ACTIVE
            };
            self.st.minted_vars.push(v as u32);
            self.mint.seen_split_atoms.insert(t);
            self.stats.minted_atoms += 1;
            self.ensure_registered(v, t);
            self.ledger.tag(t, p);
        }
        if !defs.is_empty() {
            // A compound atom: its definitions are not T-tautologies and must
            // live in the ORIGINAL ledger (§4.2).
            self.tier2 = true;
            for def in defs {
                let clause: Vec<Literal> = def.0.iter().map(|&l| Literal::from_dimacs(l)).collect();
                if !clause.is_empty() {
                    self.mint.originals.push(clause);
                    self.mint.count += 1;
                }
            }
        }
        Ok(lit)
    }

    fn ensure_registered(&mut self, v: usize, atom: TermId) {
        if !self.st.registered[v] {
            self.st.registered[v] = true;
            self.theory.rebind(self.own);
            self.theory.as_dyn().register_atom(atom);
        }
    }

    fn push_inline(&mut self, clause: Vec<Literal>) {
        debug_assert!(!clause.is_empty());
        self.mint.count += 1;
        self.inline.push(clause);
    }

    fn finish(mut self) -> MintOutcome {
        if self.tier2 {
            self.mint.originals.append(&mut self.inline);
            MintOutcome::Originals
        } else if self.inline.is_empty() {
            MintOutcome::NothingNew
        } else {
            MintOutcome::Inline(std::mem::take(&mut self.inline))
        }
    }

    /// Decode a disequality guard term: `(= L R)`, `(distinct L R)`, or either
    /// under `Not`. Returns `(base_term, holds_when, lhs, rhs)` where the
    /// disequality holds when `base_term == holds_when`.
    fn decode_diseq(&self, term: TermId) -> Result<(TermId, bool, TermId, TermId), BridgeExit> {
        // The guard is always expressed on the BASE atom: `Not(base)` is true
        // exactly when `base` is false, so "the disequality holds" is the same
        // condition on `base` whether or not the request named the wrapper.
        let base = match self.own.terms.get(term) {
            TermData::Not(inner) => *inner,
            _ => term,
        };
        let (lhs, rhs, holds_when) = match self.own.terms.get(base) {
            TermData::App(Symbol::Named(name), args) if args.len() == 2 => match &**name {
                "=" => (args[0], args[1], false),
                "distinct" => (args[0], args[1], true),
                _ => return Err(BridgeExit::Unsupported(UnsupportedKind::Shape)),
            },
            _ => return Err(BridgeExit::Unsupported(UnsupportedKind::Shape)),
        };
        Ok((base, holds_when, lhs, rhs))
    }

    /// The guard literal of a split clause: `¬(diseq holds)` =
    /// `lit_for(base, !holds_when)`, so the clause is `[guard, lt, gt]` —
    /// `term ∨ lt ∨ gt` for an `=` term, `¬term ∨ lt ∨ gt` for `distinct`
    /// (`DisequalitySplitRequest` doc). Also returns the guard's var (the
    /// activity parent of the split atoms).
    fn guard_lit(
        &mut self,
        base: TermId,
        holds_when: bool,
        p: Partition,
    ) -> Result<(Literal, u32), BridgeExit> {
        let lit = self.lit_for(base, !holds_when, p, MINT_ALWAYS_ACTIVE)?;
        Ok((lit, lit.variable().index() as u32))
    }

    fn is_bool_const(&self, t: TermId) -> bool {
        matches!(
            self.own.terms.get(t),
            TermData::Const(ay_core::Constant::Bool(_))
        )
    }

    // ------------------------------------------------------------------
    // Requests
    // ------------------------------------------------------------------

    /// `NeedDisequalitySplit` (§2.5): `lt = mk_lt(v, c)`, `gt = mk_gt(v, c)`;
    /// guard by the disequality term's polarity; clause `[guard, +lt, +gt]`;
    /// lt/gt inherit the guard's activity. `disequality_term == None` =>
    /// `Unsupported(DisequalityWithoutTerm)` (the unconditional form is
    /// unsound-prone per the request's doc). An Int variable with a
    /// non-integral excluded value splits as `[guard, v <= ⌊c⌋, v >= ⌈c⌉]`.
    pub(crate) fn diseq_splits(
        mut self,
        reqs: Vec<DisequalitySplitRequest>,
    ) -> Result<MintOutcome, BridgeExit> {
        for req in reqs {
            let Some(d) = req.disequality_term else {
                return Err(BridgeExit::Unsupported(
                    UnsupportedKind::DisequalityWithoutTerm,
                ));
            };
            let (base, holds_when, _, _) = self.decode_diseq(d)?;
            debug_assert_eq!(
                holds_when, req.is_distinct,
                "is_distinct disagrees with the disequality term's shape"
            );
            // Rung 1 tags split atoms AB (the guard's tag is not readable
            // through C4 yet; attribution is Rung 3).
            let p = Partition::AB;
            let (guard, guard_var) = self.guard_lit(base, holds_when, p)?;
            let x = req.variable;
            let (lt, gt) = match self.own.terms.sort(x).clone() {
                Sort::Real => {
                    let c = self.own.terms.mk_rational(req.excluded_value.clone());
                    (self.own.terms.mk_lt(x, c), self.own.terms.mk_gt(x, c))
                }
                Sort::Int => {
                    if req.excluded_value.is_integer() {
                        let c = self.own.terms.mk_int(req.excluded_value.to_integer());
                        (self.own.terms.mk_lt(x, c), self.own.terms.mk_gt(x, c))
                    } else {
                        let lo = self
                            .own
                            .terms
                            .mk_int(req.excluded_value.floor().to_integer());
                        let hi = self
                            .own
                            .terms
                            .mk_int(req.excluded_value.ceil().to_integer());
                        (self.own.terms.mk_le(x, lo), self.own.terms.mk_ge(x, hi))
                    }
                }
                _ => return Err(BridgeExit::Unsupported(UnsupportedKind::Sort)),
            };
            if self.is_bool_const(lt) || self.is_bool_const(gt) {
                return Err(BridgeExit::Unsupported(UnsupportedKind::Shape));
            }
            let lt_lit = self.lit_for(lt, true, p, guard_var)?;
            let gt_lit = self.lit_for(gt, true, p, guard_var)?;
            self.push_inline(vec![guard, lt_lit, gt_lit]);
            self.stats.mints_diseq += 1;
        }
        Ok(self.finish())
    }

    /// `NeedExpressionSplit(s)` (§2.5): decode `disequality_term` as `(= L R)`
    /// / `(distinct L R)` (optionally under `Not`); `lt = mk_lt(L, R)`, `gt =
    /// mk_gt(L, R)`; the same guarded clause; batched (#8707). Undecodable =>
    /// `Unsupported(Shape)`; non-arithmetic or mixed sorts => `Unsupported(Sort)`.
    pub(crate) fn expr_splits(
        mut self,
        reqs: Vec<ExpressionSplitRequest>,
    ) -> Result<MintOutcome, BridgeExit> {
        for req in reqs {
            let (base, holds_when, lhs, rhs) = self.decode_diseq(req.disequality_term)?;
            let ls = self.own.terms.sort(lhs).clone();
            if !matches!(ls, Sort::Int | Sort::Real) || &ls != self.own.terms.sort(rhs) {
                return Err(BridgeExit::Unsupported(UnsupportedKind::Sort));
            }
            let p = Partition::AB;
            let (guard, guard_var) = self.guard_lit(base, holds_when, p)?;
            let lt = self.own.terms.mk_lt(lhs, rhs);
            let gt = self.own.terms.mk_gt(lhs, rhs);
            if self.is_bool_const(lt) || self.is_bool_const(gt) {
                return Err(BridgeExit::Unsupported(UnsupportedKind::Shape));
            }
            let lt_lit = self.lit_for(lt, true, p, guard_var)?;
            let gt_lit = self.lit_for(gt, true, p, guard_var)?;
            self.push_inline(vec![guard, lt_lit, gt_lit]);
            self.stats.mints_expr += 1;
        }
        Ok(self.finish())
    }

    /// `NeedLemmas` (cuts, array axioms): map each literal — fail closed, no
    /// minting (`TheoryIncomplete` on an unmapped literal) — and add inline.
    pub(crate) fn lemmas(mut self, lemmas: Vec<TheoryLemma>) -> Result<MintOutcome, BridgeExit> {
        for lemma in lemmas {
            if lemma.clause.is_empty() {
                return Err(BridgeExit::Poison(PoisonKind::EmptyTheoryConflict));
            }
            let mut clause = Vec::with_capacity(lemma.clause.len());
            for TheoryLit { term, value } in &lemma.clause {
                let Some(lit) = self
                    .tseitin
                    .as_ref()
                    .and_then(|ts| lit_of(ts, *term, *value))
                else {
                    return Err(BridgeExit::TheoryIncomplete);
                };
                clause.push(lit);
            }
            self.push_inline(clause);
            self.stats.mints_lemma += 1;
        }
        Ok(self.finish())
    }

    /// `NeedModelEqualit(y|ies)` (§2.5, §4.1–4.3). For each request, `eq =
    /// mk_eq_coerce_no_ite_expand(lhs, rhs)` — the no-expand constructor, so
    /// LRA's `find_eq(lhs, rhs)` gate (F12) sees the term and never re-requests.
    /// - `implied`: the reason literals are mapped (minting a variable for a
    ///   reason term the encoder never named — an ITE condition under an
    ///   atom, say — which is tier 2 when the term is compound) and the clause
    ///   `[¬r1, …, ¬rk, +eq]` goes to `originals` (tier 2). A pair already
    ///   answered this query means the gate failed: `TheoryIncomplete` (no
    ///   progress is possible, and re-entering forever is not an answer).
    /// - hint (`implied == false`): triangle axioms `[¬eq, L<=R]`, `[¬eq,
    ///   R<=L]`, `[eq, ¬(L<=R), ¬(R<=L)]` inline (T-tautologies that also
    ///   grow the solver), `preferred_phase[eq] = true`; a pair already
    ///   answered this query is nothing new.
    /// Rounds are counted only when a NEW pair is minted (F23); the cap is
    /// `Budget(MintCap)`. No new pair and no tier-2 clause => `NothingNew`
    /// (=> `Sat`, the convergence rule §4.3).
    pub(crate) fn model_equalities(
        mut self,
        reqs: Vec<ModelEqualityRequest>,
    ) -> Result<MintOutcome, BridgeExit> {
        let mut any_new = false;
        for req in reqs {
            let key = if req.lhs <= req.rhs {
                (req.lhs, req.rhs)
            } else {
                (req.rhs, req.lhs)
            };
            let is_new = self.mint.seen_model_eq.insert(key);
            if !is_new {
                if req.implied {
                    // The `=` term exists (we minted it) yet the theory asked
                    // again: the `find_eq` gate did not hold for this pair.
                    return Err(BridgeExit::TheoryIncomplete);
                }
                continue;
            }
            let eq = self.own.terms.mk_eq_coerce_no_ite_expand(req.lhs, req.rhs);
            if self.is_bool_const(eq) {
                // `(= t t)` or two distinct constants: nothing to branch on.
                continue;
            }
            debug_assert_eq!(
                self.own.terms.find_eq(req.lhs, req.rhs),
                Some(eq),
                "model equality must be the hash-consed `=` app LRA's find_eq gate looks up"
            );
            let p = Partition::AB;
            let eq_lit = self.lit_for(eq, true, p, MINT_ALWAYS_ACTIVE)?;
            let eq_var = eq_lit.variable().index() as u32;
            any_new = true;
            if req.implied {
                let mut clause = Vec::with_capacity(req.reason.len() + 1);
                for TheoryLit { term, value } in &req.reason {
                    let r = self.lit_for(*term, *value, p, MINT_ALWAYS_ACTIVE)?;
                    clause.push(r.negated());
                }
                clause.push(eq_lit);
                self.tier2 = true;
                self.mint.originals.push(clause);
                self.mint.count += 1;
            } else {
                let ls = self.own.terms.sort(req.lhs).clone();
                if matches!(ls, Sort::Int | Sort::Real) && &ls == self.own.terms.sort(req.rhs) {
                    let le_lr = self.own.terms.mk_le(req.lhs, req.rhs);
                    let le_rl = self.own.terms.mk_le(req.rhs, req.lhs);
                    if !self.is_bool_const(le_lr) && !self.is_bool_const(le_rl) {
                        let a = self.lit_for(le_lr, true, p, eq_var)?;
                        let b = self.lit_for(le_rl, true, p, eq_var)?;
                        self.push_inline(vec![eq_lit.negated(), a]);
                        self.push_inline(vec![eq_lit.negated(), b]);
                        self.push_inline(vec![eq_lit, a.negated(), b.negated()]);
                    }
                }
                self.st.preferred_phase.insert(eq_var, true);
            }
            self.stats.mints_model_eq += 1;
        }
        if any_new {
            self.mint.model_eq_rounds += 1;
            if self.mint.model_eq_rounds > self.cfg.max_model_eq_rounds {
                return Err(BridgeExit::Budget(super::BudgetKind::MintCap));
            }
        }
        Ok(self.finish())
    }

    /// `NeedSplit(SplitRequest { variable, floor, ceil, .. })` — Rung 2 (LIA
    /// branch-and-bound): `le = mk_le(variable, mk_int(floor))`, `ge =
    /// mk_ge(variable, mk_int(ceil))`, `Partition::Split`, clause `[+le, +ge]`.
    /// The LRA arm never raises it from `check()`; the bridge answers
    /// `Unsupported(Shape)` without calling this.
    #[allow(dead_code)]
    pub(crate) fn integer_split(self, _req: SplitRequest) -> Result<MintOutcome, BridgeExit> {
        todo!("Rung 2 (LIA): MintState::integer_split — inline B&B split, Partition::Split")
    }

    /// `take_bound_refinements` (Rung 2, flag-gated): atom + implication
    /// `[¬reason.., +atom]` inline (re-derivable).
    #[allow(dead_code)]
    pub(crate) fn bound_refinements(
        self,
        _reqs: Vec<ay_core::BoundRefinementRequest>,
    ) -> Result<MintOutcome, BridgeExit> {
        todo!("Rung 2 (LIA): MintState::bound_refinements — flag-gated inline refinements")
    }
}

/// Whether `lit`'s variable is the encoder's variable FOR `term` (and not, say,
/// the variable of the atom under a `Not`).
fn lit_names_term(ts: Option<&TseitinState>, lit: Literal, term: TermId) -> bool {
    ts.is_some_and(|ts| ts.term_to_var.get(&term) == Some(&(lit.variable().id() + 1)))
}
