// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Certified re-derivation of EUF congruence/substitution-chain trust
//! lemmas (#C2, the SEQ/NEQ SMT-COMP finite-model families).
//!
//! The lazy EUF engine exports its theory lemmas as `:rule trust` leaves of
//! two shapes:
//!
//! - **bare**: `(cl E ¬e1 .. ¬ek [extras])` — the hypothesis equalities
//!   `e1..ek` entail the conclusion `E` by congruence closure, where `E` is
//!   either a positive equality or a `¬P(a..) ∨ P(b..)` predicate-transfer
//!   pair; `extras` are conflict-clause literals the entailment never used.
//! - **or-wrapped**: `(cl (or E ¬e1 .. ¬ek [extras]))` — the same lemma as a
//!   single or-term unit (also produced as a mid-proof `assume` of a
//!   preprocessor-derived tautology).
//!
//! The planner runs a small proof-forest congruence closure (union-find with
//! explanation, Nieuwenhuis–Oliveras style) over the hypothesis equalities,
//! finds the entailed conclusion, and precomputes a complete derivation
//! recipe out of the Alethe EUF toolkit:
//!
//! - `eq_congruent` — per-argument congruence tautologies (trivial `a = a`
//!   argument pairs discharged by `eq_reflexive`),
//! - `eq_transitive` — explanation-path chains (simple paths, so the strict
//!   checker's no-redundant-premise rule holds; ≥ 2 edges, carcara's
//!   minimum),
//! - `eq_congruent_pred` — the predicate-transfer conclusion,
//! - `resolution`/`contraction` to compose them, and
//! - `weakening` to append the unused extras of a bare lemma so the
//!   replacement step carries EXACTLY the original clause (as a multiset —
//!   both checkers treat resolution clauses order-insensitively).
//!
//! Every emitted step is one of those independently re-validated rules;
//! planning is fail-closed (any unrecognized literal, non-entailed
//! conclusion, or single-flipped-hypothesis degenerate returns `None` and
//! the surgery aborts, leaving the proof byte-identical). The caller
//! additionally gates the whole rebuilt proof through the executor's contextual
//! strict checker (datatype declarations, selectors, authored assumptions, and
//! array-diff witness provenance included).

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, ProofId, Sort, Symbol, TermId};

use super::proof_trust_surgery_provenance::SurgeryPlanningBudget;
use super::Executor;

#[path = "proof_euf_lemma_plan.rs"]
mod plan;
#[path = "proof_euf_lemma_surface.rs"]
mod surface;
#[path = "proof_euf_lemma_volume.rs"]
mod volume;

/// Justification for one needed equality `s = t` inside the recipe.
#[derive(Clone, Copy, Debug)]
enum EufJust {
    /// `s == t` syntactically; the side term (for the `eq_reflexive` unit).
    Refl(TermId),
    /// A hypothesis literal `(not e)` from the lemma clause whose equality
    /// links `s` and `t` (possibly flipped — both checkers accept either
    /// orientation in `eq_transitive`/`eq_congruent` premises).
    Hyp(TermId),
    /// Index into [`EufLemmaPlan::derivs`].
    Derived(usize),
}

/// One derived-equality emission unit.
#[derive(Clone, Debug)]
enum EufDeriv {
    /// `eq_congruent`: `(cl ¬p1 .. ¬pn eq_term)` with one premise per
    /// argument pair of `eq_term`'s two same-symbol applications.
    Cong {
        eq_term: TermId,
        prems: Vec<EufJust>,
    },
    /// `eq_transitive`: `(cl ¬t1 .. ¬tk eq_term)` over a simple explanation
    /// path (each edge a hypothesis or a derived equality; `k >= 2`).
    Chain {
        eq_term: TermId,
        edges: Vec<EufJust>,
    },
}

/// The entailed conclusion of the lemma.
#[derive(Clone, Debug)]
enum EufConcl {
    /// A positive equality literal, concluded by `derivs[top]`.
    Eq { top: usize },
    /// A reflexive positive equality literal `(= a a)`: one `eq_reflexive`.
    EqRefl { eq_term: TermId },
    /// Predicate transfer `¬P(a..) ∨ P(b..)` via `eq_congruent_pred`, with
    /// one justification per argument pair.
    Pred {
        neg_lit: TermId,
        pos_lit: TermId,
        prems: Vec<EufJust>,
    },
}

/// Replacement target.
#[derive(Clone, Debug)]
pub(super) enum EufTarget {
    /// Replace a bare trust step: the final clause must be the original
    /// clause as a multiset (`extras` appended by `weakening`).
    Bare { extras: Vec<TermId> },
    /// Derive the unit `(cl term)` for an or-wrapped tautology.
    OrUnit { term: TermId },
}

/// A fully planned, guaranteed-emittable derivation for one EUF trust lemma.
#[derive(Clone, Debug)]
pub(super) struct EufLemmaPlan {
    derivs: Vec<EufDeriv>,
    concl: EufConcl,
    pub(super) target: EufTarget,
}

impl EufLemmaPlan {
    /// The or-term of an `OrUnit` plan (used to share derivations and to
    /// reorder scrambled `or`-split consumers), `None` for bare plans.
    pub(super) fn or_term(&self) -> Option<TermId> {
        match self.target {
            EufTarget::OrUnit { term } => Some(term),
            EufTarget::Bare { .. } => None,
        }
    }
}

/// Union-find with a proof forest for explanations.
struct CcForest {
    rep: HashMap<TermId, TermId>,
    /// node -> (forest parent, edge reason); roots absent.
    forest: HashMap<TermId, (TermId, CcReason)>,
    /// Application subterms of the universe (congruence candidates).
    apps: Vec<TermId>,
}

#[derive(Clone, Copy, Debug)]
enum CcReason {
    /// The hypothesis literal `(not e)`.
    Hyp(TermId),
    /// A congruence edge (the two endpoints are same-symbol applications
    /// whose argument pairs are CC-equal).
    Cong,
}

impl CcForest {
    fn new() -> Self {
        Self {
            rep: HashMap::default(),
            forest: HashMap::default(),
            apps: Vec::new(),
        }
    }

    /// Add `t` and all its subterms to the universe.
    fn add_universe(&mut self, terms: &ay_core::TermStore, t: TermId) {
        if self.rep.contains_key(&t) {
            return;
        }
        self.rep.insert(t, t);
        if let TermData::App(_, args) = terms.get(t) {
            self.apps.push(t);
            for a in args.clone() {
                self.add_universe(terms, a);
            }
        }
    }

    fn find(&self, mut x: TermId) -> TermId {
        while self.rep[&x] != x {
            x = self.rep[&x];
        }
        x
    }

    /// Merge `a` and `b` with `reason`; returns whether anything changed.
    fn union(&mut self, a: TermId, b: TermId, reason: CcReason) -> bool {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return false;
        }
        // Reverse the forest path from `a` to its root so `a` can point at
        // `b` (standard proof-forest union).
        let mut node = a;
        let mut prev: Option<(TermId, CcReason)> = None;
        loop {
            let next = self.forest.get(&node).copied();
            match prev {
                Some((p, r)) => {
                    self.forest.insert(node, (p, r));
                }
                None => {
                    self.forest.remove(&node);
                }
            }
            match next {
                Some((parent, r)) => {
                    prev = Some((node, r));
                    node = parent;
                }
                None => break,
            }
        }
        self.forest.insert(a, (b, reason));
        self.rep.insert(ra, rb);
        true
    }

    /// Saturate congruence: merge application pairs whose arguments are
    /// pairwise CC-equal, to fixpoint.
    fn close(&mut self, terms: &ay_core::TermStore) {
        loop {
            let mut changed = false;
            let mut sigs: HashMap<(Symbol, Vec<TermId>), TermId> = HashMap::default();
            for &app in &self.apps.clone() {
                let TermData::App(sym, args) = terms.get(app) else {
                    continue;
                };
                let sig: Vec<TermId> = args.iter().map(|&x| self.find(x)).collect();
                match sigs.get(&(sym.clone(), sig.clone())) {
                    Some(&other) => {
                        if self.find(app) != self.find(other) {
                            changed |= self.union(app, other, CcReason::Cong);
                        }
                    }
                    None => {
                        sigs.insert((sym.clone(), sig), app);
                    }
                }
            }
            if !changed {
                return;
            }
        }
    }

    /// The simple explanation path from `a` to `b` (assumes `find(a) ==
    /// find(b)`): edges `(x, y, reason)` in path order.
    fn explain(&self, a: TermId, b: TermId) -> Option<Vec<(TermId, TermId, CcReason)>> {
        // Ancestor chain of `a` with depths.
        let mut depth: HashMap<TermId, usize> = HashMap::default();
        let mut node = a;
        let mut d = 0usize;
        depth.insert(node, d);
        while let Some(&(p, _)) = self.forest.get(&node) {
            d += 1;
            node = p;
            depth.insert(node, d);
        }
        // Climb from `b` until we hit `a`'s chain.
        let mut b_edges: Vec<(TermId, TermId, CcReason)> = Vec::new();
        let mut node = b;
        while !depth.contains_key(&node) {
            let &(p, r) = self.forest.get(&node)?;
            b_edges.push((p, node, r));
            node = p;
        }
        let lca = node;
        // Edges from `a` up to the LCA.
        let mut edges: Vec<(TermId, TermId, CcReason)> = Vec::new();
        let mut node = a;
        while node != lca {
            let &(p, r) = self.forest.get(&node)?;
            edges.push((node, p, r));
            node = p;
        }
        edges.extend(b_edges.into_iter().rev());
        Some(edges)
    }
}

/// Literal split of a candidate lemma clause.
struct LemmaLits {
    /// `(lit, lhs, rhs)` for each `(not (= lhs rhs))` hypothesis.
    hyps: Vec<(TermId, TermId, TermId)>,
    /// `(lit, lhs, rhs)` for each positive equality.
    pos_eqs: Vec<(TermId, TermId, TermId)>,
    /// `(lit, atom)` for each negated predicate application.
    neg_preds: Vec<(TermId, TermId)>,
    /// Positive predicate applications.
    pos_preds: Vec<TermId>,
}

fn decode_eq(terms: &ay_core::TermStore, t: TermId) -> Option<(TermId, TermId)> {
    match terms.get(t) {
        TermData::App(Symbol::Named(n), args) if n == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// Recipe builder shared by the planning passes.
struct RecipeBuilder<'a> {
    terms: &'a mut ay_core::TermStore,
    cc: &'a CcForest,
    derivs: Vec<EufDeriv>,
    /// Memo: unordered pair -> justification.
    memo: HashMap<(TermId, TermId), EufJust>,
    /// Hypothesis literals used anywhere in the recipe.
    used_hyps: Vec<TermId>,
}

impl RecipeBuilder<'_> {
    fn pair_key(s: TermId, t: TermId) -> (TermId, TermId) {
        if s.0 <= t.0 {
            (s, t)
        } else {
            (t, s)
        }
    }

    fn note_hyp(&mut self, lit: TermId) {
        if !self.used_hyps.contains(&lit) {
            self.used_hyps.push(lit);
        }
    }

    fn raw_eq(&mut self, a: TermId, b: TermId) -> TermId {
        self.terms.mk_app(Symbol::named("="), [a, b], Sort::Bool)
    }

    /// Plan a derivation of `s = t`. `want` forces the conclusion equality
    /// term (the lemma's own literal); only `Derived` results can honor it,
    /// so a `want` that would plan to a bare `Hyp`/`Refl` fails.
    fn derive(&mut self, s: TermId, t: TermId, want: Option<TermId>) -> Option<EufJust> {
        if s == t {
            return match want {
                None => Some(EufJust::Refl(s)),
                Some(_) => None,
            };
        }
        let key = Self::pair_key(s, t);
        if want.is_none() {
            if let Some(&j) = self.memo.get(&key) {
                if let EufJust::Hyp(lit) = j {
                    self.note_hyp(lit);
                }
                return Some(j);
            }
        }
        let path = self.cc.explain(s, t)?;
        let just = if path.len() == 1 {
            match path[0].2 {
                CcReason::Hyp(lit) => {
                    if want.is_some() {
                        // A conclusion identical (modulo flip) to a single
                        // hypothesis has no >= 2-literal tautology to carry
                        // it: fail closed (degenerate, unseen in practice).
                        return None;
                    }
                    self.note_hyp(lit);
                    EufJust::Hyp(lit)
                }
                // The edge endpoints are exactly {s, t}: orient the
                // congruence on the requested sides.
                CcReason::Cong => self.plan_cong(s, t, want)?,
            }
        } else {
            let mut edges = Vec::with_capacity(path.len());
            for &(x, y, reason) in &path {
                let e = match reason {
                    CcReason::Hyp(lit) => {
                        self.note_hyp(lit);
                        EufJust::Hyp(lit)
                    }
                    CcReason::Cong => self.derive(x, y, None)?,
                };
                edges.push(e);
            }
            let eq_term = match want {
                Some(w) => w,
                None => self.raw_eq(s, t),
            };
            self.derivs.push(EufDeriv::Chain { eq_term, edges });
            EufJust::Derived(self.derivs.len() - 1)
        };
        self.memo.insert(key, just);
        Some(just)
    }

    /// Plan an `eq_congruent` derivation of `lhs = rhs` (both applications
    /// of the same symbol with pairwise CC-equal arguments).
    fn plan_cong(&mut self, lhs: TermId, rhs: TermId, want: Option<TermId>) -> Option<EufJust> {
        let (ls, largs) = match self.terms.get(lhs) {
            TermData::App(sym, args) => (sym.clone(), args.clone()),
            _ => return None,
        };
        let (rs, rargs) = match self.terms.get(rhs) {
            TermData::App(sym, args) => (sym.clone(), args.clone()),
            _ => return None,
        };
        if ls != rs || largs.len() != rargs.len() || largs.is_empty() {
            return None;
        }
        let mut prems = Vec::with_capacity(largs.len());
        for (&a, &b) in largs.iter().zip(rargs.iter()) {
            prems.push(self.derive(a, b, None)?);
        }
        let eq_term = match want {
            Some(w) => w,
            None => self.raw_eq(lhs, rhs),
        };
        self.derivs.push(EufDeriv::Cong { eq_term, prems });
        Some(EufJust::Derived(self.derivs.len() - 1))
    }
}

impl Executor {
    /// Cached `eq_reflexive` unit `(cl (= side side))`.
    fn euf_refl_unit(
        &mut self,
        new_proof: &mut Proof,
        refl_units: &mut HashMap<TermId, ProofId>,
        side: TermId,
    ) -> (TermId, ProofId) {
        let eq = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [side, side], Sort::Bool);
        let id = match refl_units.get(&eq) {
            Some(&id) => id,
            None => {
                let id = new_proof.add_rule_step(
                    AletheRule::EqReflexive,
                    vec![eq],
                    Vec::new(),
                    Vec::new(),
                );
                refl_units.insert(eq, id);
                id
            }
        };
        (eq, id)
    }

    /// Emit one EUF tautology (`rule` over `prems` + `concl_tail`) and
    /// discharge its `Refl`/`Derived` premises by resolution; a trailing
    /// `contraction` dedupes accumulated hypothesis literals. Returns the
    /// final (step id, clause).
    #[allow(clippy::too_many_arguments)]
    fn emit_euf_taut(
        &mut self,
        new_proof: &mut Proof,
        plan: &EufLemmaPlan,
        emitted: &[(ProofId, Vec<TermId>)],
        refl_units: &mut HashMap<TermId, ProofId>,
        rule: AletheRule,
        prems: &[EufJust],
        concl_tail: &[TermId],
    ) -> (ProofId, Vec<TermId>) {
        // Tautology clause: one literal per justification + the tail.
        let mut clause: Vec<TermId> = Vec::with_capacity(prems.len() + concl_tail.len());
        let mut discharges: Vec<(TermId, ProofId, Option<usize>)> = Vec::new();
        for &j in prems {
            match j {
                EufJust::Refl(side) => {
                    let (eq, id) = self.euf_refl_unit(new_proof, refl_units, side);
                    let lit = self.ctx.terms.mk_not_raw(eq);
                    clause.push(lit);
                    discharges.push((eq, id, None));
                }
                EufJust::Hyp(lit) => clause.push(lit),
                EufJust::Derived(k) => {
                    let eq = match &plan.derivs[k] {
                        EufDeriv::Cong { eq_term, .. } | EufDeriv::Chain { eq_term, .. } => {
                            *eq_term
                        }
                    };
                    let lit = self.ctx.terms.mk_not_raw(eq);
                    clause.push(lit);
                    discharges.push((eq, emitted[k].0, Some(k)));
                }
            }
        }
        clause.extend_from_slice(concl_tail);
        let mut cur = new_proof.add_rule_step(rule, clause.clone(), Vec::new(), Vec::new());
        for (eq, prem_id, src) in discharges {
            let not_eq = self.ctx.terms.mk_not_raw(eq);
            if let Some(pos) = clause.iter().position(|&l| l == not_eq) {
                let _ = clause.remove(pos);
            }
            if let Some(k) = src {
                // Splice in the derived clause's hypothesis literals
                // (everything but its concluding equality).
                for &l in &emitted[k].1 {
                    if l != eq {
                        clause.push(l);
                    }
                }
            }
            cur = new_proof.add_resolution(clause.clone(), eq, cur, prem_id);
        }
        // Dedupe accumulated hypothesis literals.
        let mut dedup: Vec<TermId> = Vec::with_capacity(clause.len());
        for &l in &clause {
            if !dedup.contains(&l) {
                dedup.push(l);
            }
        }
        if dedup.len() != clause.len() {
            cur = new_proof.add_rule_step(
                AletheRule::Contraction,
                dedup.clone(),
                vec![cur],
                Vec::new(),
            );
            clause = dedup;
        }
        (cur, clause)
    }

    /// Emit the planned derivation into `new_proof`; returns the id of the
    /// replacement step (bare: the exact original clause as a multiset;
    /// or-unit: `(cl term)`). Planning guaranteed emission succeeds.
    pub(super) fn emit_euf_lemma(&mut self, new_proof: &mut Proof, plan: &EufLemmaPlan) -> ProofId {
        let mut refl_units: HashMap<TermId, ProofId> = HashMap::default();
        // Per-deriv final (step id, clause).
        let mut emitted: Vec<(ProofId, Vec<TermId>)> = Vec::with_capacity(plan.derivs.len());
        for deriv in plan.derivs.clone() {
            let out = match deriv {
                EufDeriv::Cong { eq_term, prems } => self.emit_euf_taut(
                    new_proof,
                    plan,
                    &emitted,
                    &mut refl_units,
                    AletheRule::EqCongruent,
                    &prems,
                    &[eq_term],
                ),
                EufDeriv::Chain { eq_term, edges } => self.emit_euf_taut(
                    new_proof,
                    plan,
                    &emitted,
                    &mut refl_units,
                    AletheRule::EqTransitive,
                    &edges,
                    &[eq_term],
                ),
            };
            emitted.push(out);
        }
        let (final_id, final_clause) = match &plan.concl {
            EufConcl::Eq { top } => emitted[*top].clone(),
            EufConcl::EqRefl { eq_term } => {
                let id = new_proof.add_rule_step(
                    AletheRule::EqReflexive,
                    vec![*eq_term],
                    Vec::new(),
                    Vec::new(),
                );
                (id, vec![*eq_term])
            }
            EufConcl::Pred {
                neg_lit,
                pos_lit,
                prems,
            } => {
                let prems = prems.clone();
                self.emit_euf_taut(
                    new_proof,
                    plan,
                    &emitted,
                    &mut refl_units,
                    AletheRule::EqCongruentPred,
                    &prems,
                    &[*neg_lit, *pos_lit],
                )
            }
        };
        match &plan.target {
            EufTarget::Bare { extras } => {
                if extras.is_empty() {
                    final_id
                } else {
                    // `weakening`: the premise clause is the conclusion's
                    // prefix (carcara's check), extras appended; the result
                    // is the original trust clause as a multiset.
                    let mut clause = final_clause;
                    clause.extend(extras.iter().copied());
                    new_proof.add_rule_step(
                        AletheRule::Weakening,
                        clause,
                        vec![final_id],
                        Vec::new(),
                    )
                }
            }
            EufTarget::OrUnit { term } => {
                let term = *term;
                let mut clause = final_clause;
                let mut cur = final_id;
                for &lit in &clause.clone() {
                    let not_lit = self.ctx.terms.mk_not_raw(lit);
                    let on = new_proof.add_rule_step(
                        AletheRule::OrNeg,
                        vec![term, not_lit],
                        Vec::new(),
                        Vec::new(),
                    );
                    if let Some(pos) = clause.iter().position(|&l| l == lit) {
                        let _ = clause.remove(pos);
                    }
                    clause.push(term);
                    cur = new_proof.add_resolution(clause.clone(), lit, cur, on);
                }
                new_proof.add_rule_step(AletheRule::Contraction, vec![term], vec![cur], Vec::new())
            }
        }
    }

    /// Replace individually certified, load-bearing Generic EUF leaves while
    /// preserving the rest of the proof verbatim.
    ///
    /// The broader trust-surgery pass deliberately aborts when it encounters
    /// any unrelated authority defect (for example, a preprocessing-derived
    /// `Assume`).  That must not prevent an independently checkable EUF leaf
    /// from carrying its real certificate.  This pass therefore has a much
    /// narrower contract:
    ///
    /// - only reachable `TheoryLemmaKind::Generic` leaves recognized by
    ///   [`Self::plan_euf_lemma`] are replaced;
    /// - every `Assume` and every unrecognized step is copied byte-for-byte;
    /// - premise ids and valid named assume ids are remapped mechanically; and
    /// - the rebuilt proof is installed atomically only if the whole proof
    ///   passes the strict checker.
    ///
    /// A remaining unsupported Generic leaf makes that final gate fail, so a
    /// partial promotion can never conceal another trust obligation.
    pub(super) fn promote_certified_generic_euf_leaves(&mut self, proof: &mut Proof) {
        self.promote_certified_generic_euf_leaves_bounded(
            proof,
            volume::MAX_PROMOTION_VECTOR_ENTRIES,
        );
    }

    fn promote_certified_generic_euf_leaves_bounded(
        &mut self,
        proof: &mut Proof,
        output_limit: usize,
    ) {
        let Some(preflight) = volume::preflight_promotion(proof) else {
            return;
        };

        let n = proof.steps.len();
        let mut planning = SurgeryPlanningBudget::new();
        let mut plans: Vec<Option<EufLemmaPlan>> = vec![None; n];
        for (idx, step) in proof.steps.iter().enumerate() {
            if !preflight.reachable[idx] {
                continue;
            }
            // Two trust shapes carry certificate-free EUF leaves that
            // `plan_euf_lemma` can independently re-derive:
            //   (1) `TheoryLemma{Generic}`  — the lazy EUF engine's fused
            //       congruence/substitution-chain lemmas; and
            //   (2) `Step{Trust}`           — an `(or …)`-wrapped
            //       eq_transitive/eq_congruent leaf the array-extensionality
            //       lane emits as a raw trust step (it is a `Step`, so the
            //       TheoryLemma-only classifier/splitter passes never touch
            //       it, and its residual presence made this pass's whole-proof
            //       strict gate revert an otherwise-valid rebuild of (1)).
            // Both are self-contained EUF tautologies (their hypotheses are the
            // clause's own negated literals), so re-deriving them as a pure
            // tautology never depends on the original premises. `plan_euf_lemma`
            // is fail-closed (any non-EUF clause → `None`) and the whole-proof
            // strict gate below is the backstop, so a mis-recognition reverts.
            let clause = match step {
                ay_core::ProofStep::TheoryLemma {
                    kind: ay_core::TheoryLemmaKind::Generic,
                    clause,
                    ..
                } => clause,
                ay_core::ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    ..
                } => clause,
                _ => continue,
            };
            if !planning.spend_work(clause.len().saturating_add(1))
                || !planning.spend_terms(&self.ctx.terms, clause)
            {
                return;
            }
            plans[idx] = self.plan_euf_lemma_with_budget(clause, &mut planning);
        }
        if plans.iter().all(Option::is_none) {
            return;
        }
        if !self.generic_euf_promotion_surface_is_safe(proof, &plans) {
            return;
        }
        if !volume::promotion_output_within(&preflight, &plans, output_limit) {
            return;
        }

        let mut rebuilt = Proof::new();
        let mut remap: Vec<ProofId> = Vec::with_capacity(n);
        for (idx, step) in proof.steps.iter().cloned().enumerate() {
            if let Some(plan) = &plans[idx] {
                remap.push(self.emit_euf_lemma(&mut rebuilt, plan));
                continue;
            }
            let remap_id = |id: ProofId| remap.get(id.0 as usize).copied().unwrap_or(id);
            let step = match step {
                ay_core::ProofStep::Resolution {
                    clause,
                    pivot,
                    clause1,
                    clause2,
                } => ay_core::ProofStep::Resolution {
                    clause,
                    pivot,
                    clause1: remap_id(clause1),
                    clause2: remap_id(clause2),
                },
                ay_core::ProofStep::Step {
                    rule,
                    clause,
                    premises,
                    args,
                } => ay_core::ProofStep::Step {
                    rule,
                    clause,
                    premises: premises.into_iter().map(remap_id).collect(),
                    args,
                },
                other => other,
            };
            remap.push(rebuilt.add_step(step));
        }
        let mut remapped_named = proof.named_steps.clone();
        remapped_named.retain(|_, id| {
            let old_idx = id.0 as usize;
            if !matches!(
                proof.steps.get(old_idx),
                Some(ay_core::ProofStep::Assume(_))
            ) {
                return false;
            }
            let Some(new_id) = remap.get(old_idx) else {
                return false;
            };
            *id = *new_id;
            true
        });
        rebuilt.named_steps = remapped_named;

        if self
            .check_proof_strict_derivation_with_datatypes(&rebuilt)
            .is_ok()
        {
            *proof = rebuilt;
        }
    }
}

#[cfg(test)]
mod tests {
    use ay_core::{ProofStep, Sort, TheoryLemmaKind};

    use super::*;

    fn assume_terms(proof: &Proof) -> Vec<TermId> {
        proof
            .steps
            .iter()
            .filter_map(|step| match step {
                ProofStep::Assume(term) => Some(*term),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn certified_generic_euf_leaf_preserves_assumes_and_weakens_explicitly() {
        let mut exec = Executor::new();
        let terms = &mut exec.ctx.terms;
        let a = terms.mk_var("euf_leaf_a", Sort::Int);
        let b = terms.mk_var("euf_leaf_b", Sort::Int);
        let n = terms.mk_var("euf_leaf_n", Sort::Int);
        let zero = terms.mk_int(0.into());
        let eq = terms.mk_eq(a, b);
        let not_eq = terms.mk_not_raw(eq);
        let pa = terms.mk_app(Symbol::named("euf_leaf_p"), [a], Sort::Bool);
        let pb = terms.mk_app(Symbol::named("euf_leaf_p"), [b], Sort::Bool);
        let not_pa = terms.mk_not_raw(pa);
        let not_pb = terms.mk_not_raw(pb);
        let bound = terms.mk_app(Symbol::named("<="), [zero, n], Sort::Bool);
        let not_bound = terms.mk_not_raw(bound);

        let mut proof = Proof::new();
        let h_bound = proof.add_assume(bound, Some("h_bound".to_string()));
        let h_eq = proof.add_assume(eq, Some("h_eq".to_string()));
        let h_pa = proof.add_assume(pa, Some("h_pa".to_string()));
        let h_not_pb = proof.add_assume(not_pb, Some("h_not_pb".to_string()));
        let generic = proof.add_theory_lemma_with_kind(
            "EUF",
            vec![not_bound, not_eq, not_pa, pb],
            TheoryLemmaKind::Generic,
        );
        proof
            .named_steps
            .insert("not_an_assume".to_string(), generic);
        proof
            .named_steps
            .insert("dangling".to_string(), ProofId(u32::MAX));
        let r1 = proof.add_resolution(vec![not_eq, not_pa, pb], bound, generic, h_bound);
        let r2 = proof.add_resolution(vec![not_pa, pb], eq, r1, h_eq);
        let r3 = proof.add_resolution(vec![pb], pa, r2, h_pa);
        proof.add_resolution(Vec::new(), pb, r3, h_not_pb);

        let original_assumes = assume_terms(&proof);
        assert!(ay_proof::check_proof_strict(&proof, terms).is_err());
        exec.ctx.assertions.extend([bound, eq, pa, not_pb]);
        exec.promote_certified_generic_euf_leaves(&mut proof);

        assert_eq!(assume_terms(&proof), original_assumes);
        assert!(!proof.named_steps.contains_key("not_an_assume"));
        assert!(!proof.named_steps.contains_key("dangling"));
        for (name, expected_term) in [
            ("h_bound", bound),
            ("h_eq", eq),
            ("h_pa", pa),
            ("h_not_pb", not_pb),
        ] {
            let id = proof.named_steps[name];
            assert!(
                matches!(proof.steps.get(id.0 as usize), Some(ProofStep::Assume(term)) if *term == expected_term),
                "named assumption {name} must survive with its remapped id"
            );
        }
        assert!(proof.steps.iter().all(|step| !matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::Generic,
                ..
            }
        )));
        assert!(proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::EqCongruentPred,
                ..
            }
        )));
        assert!(proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::Weakening,
                ..
            }
        )));
        ay_proof::check_proof_strict(&proof, &exec.ctx.terms)
            .expect("certified EUF replacement must pass strict checking");
    }

    #[test]
    fn malformed_generic_euf_leaf_is_left_unchanged() {
        let mut exec = Executor::new();
        let terms = &mut exec.ctx.terms;
        let a = terms.mk_var("bad_euf_a", Sort::Int);
        let b = terms.mk_var("bad_euf_b", Sort::Int);
        let eq = terms.mk_eq(a, b);
        let not_eq = terms.mk_not_raw(eq);
        let pa = terms.mk_app(Symbol::named("bad_euf_p"), [a], Sort::Bool);
        let not_pa = terms.mk_not_raw(pa);

        let mut proof = Proof::new();
        let h_eq = proof.add_assume(eq, None);
        let h_pa = proof.add_assume(pa, None);
        let generic =
            proof.add_theory_lemma_with_kind("EUF", vec![not_eq, not_pa], TheoryLemmaKind::Generic);
        let r1 = proof.add_resolution(vec![not_pa], eq, generic, h_eq);
        proof.add_resolution(Vec::new(), pa, r1, h_pa);

        let before = format!("{:?}", proof.steps);
        exec.promote_certified_generic_euf_leaves(&mut proof);
        assert_eq!(format!("{:?}", proof.steps), before);
        assert!(ay_proof::check_proof_strict(&proof, &exec.ctx.terms).is_err());
    }

    #[test]
    fn generic_euf_promotion_rejects_boolean_equality_surface_hypothesis() {
        let mut exec = Executor::new();
        let terms = &mut exec.ctx.terms;
        let a = terms.mk_var("promotion_surface_a", Sort::Int);
        let b = terms.mk_var("promotion_surface_b", Sort::Int);
        let c = terms.mk_var("promotion_surface_c", Sort::Int);
        let ab = terms.mk_eq(a, b);
        let bc = terms.mk_eq(b, c);
        let ac = terms.mk_eq(a, c);
        let not_ab = terms.mk_not_raw(ab);
        let not_bc = terms.mk_not_raw(bc);
        let not_ac = terms.mk_not_raw(ac);

        let mut proof = Proof::new();
        let h_ab = proof.add_assume(ab, None);
        let h_bc = proof.add_assume(bc, None);
        let h_not_ac = proof.add_assume(not_ac, None);
        let generic = proof.add_theory_lemma_with_kind(
            "EUF",
            vec![ac, not_ab, not_bc],
            TheoryLemmaKind::Generic,
        );
        let r1 = proof.add_resolution(vec![ac, not_bc], ab, generic, h_ab);
        let r2 = proof.add_resolution(vec![ac], bc, r1, h_bc);
        proof.add_resolution(Vec::new(), ac, r2, h_not_ac);
        exec.ctx.assertions.extend([ab, bc, not_ac]);

        let before = format!("{:?}", proof.steps);
        let mut active = HashMap::default();
        active.insert(
            not_ab,
            "(= (= promotion_surface_a promotion_surface_b) false)".to_string(),
        );
        exec.last_proof_term_overrides = Some(active.clone());
        exec.promote_certified_generic_euf_leaves(&mut proof);

        assert_eq!(format!("{:?}", proof.steps), before);
        assert_eq!(exec.last_proof_term_overrides.as_ref(), Some(&active));
        assert!(proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::Generic,
                ..
            }
        )));

        // The same proof is otherwise promotable and passes the whole-proof
        // strict gate. This control makes the surface-role rejection, rather
        // than an unrelated native-check failure, decisive above.
        exec.last_proof_term_overrides = None;
        exec.promote_certified_generic_euf_leaves(&mut proof);
        assert!(proof.steps.iter().all(|step| !matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::Generic,
                ..
            }
        )));
        ay_proof::check_proof_strict(&proof, &exec.ctx.terms)
            .expect("canonical-surface EUF promotion must pass strict checking");
    }

    #[test]
    fn unsupported_generic_tautology_is_left_unchanged() {
        let mut exec = Executor::new();
        let terms = &mut exec.ctx.terms;
        let x = terms.mk_var("unsupported_euf_x", Sort::Int);
        let le_xx = terms.mk_app(Symbol::named("<="), [x, x], Sort::Bool);
        let not_le_xx = terms.mk_not_raw(le_xx);

        let mut proof = Proof::new();
        let h = proof.add_assume(not_le_xx, None);
        let generic =
            proof.add_theory_lemma_with_kind("EUF", vec![le_xx], TheoryLemmaKind::Generic);
        proof.add_resolution(Vec::new(), le_xx, generic, h);

        let before = format!("{:?}", proof.steps);
        exec.promote_certified_generic_euf_leaves(&mut proof);
        assert_eq!(format!("{:?}", proof.steps), before);
        assert!(ay_proof::check_proof_strict(&proof, &exec.ctx.terms).is_err());
    }

    /// Shape 2a — the fused congruence-through-a-shared-witness clause
    /// `(cl (= (select a1 i0) (select a1 i1)) ¬(= i0 k) ¬(= i1 k))`: the two
    /// index substitutions `i0 = k` and `i1 = k` chain to `i0 = i1`, which the
    /// `select` congruence lifts to the conclusion. `plan_euf_lemma` must
    /// recognize it (its congruence closure entails the positive equality).
    #[test]
    fn fused_select_congruence_via_shared_witness_is_planned() {
        let mut exec = Executor::new();
        let terms = &mut exec.ctx.terms;
        let a1 = terms.mk_var("fsc_a1", Sort::Int);
        let i0 = terms.mk_var("fsc_i0", Sort::Int);
        let i1 = terms.mk_var("fsc_i1", Sort::Int);
        let k = terms.mk_var("fsc_k", Sort::Int);
        let sel0 = terms.mk_app(Symbol::named("select"), [a1, i0], Sort::Int);
        let sel1 = terms.mk_app(Symbol::named("select"), [a1, i1], Sort::Int);
        let concl = terms.mk_eq(sel0, sel1);
        let eq_i0k = terms.mk_eq(i0, k);
        let not_i0k = terms.mk_not_raw(eq_i0k);
        let eq_i1k = terms.mk_eq(i1, k);
        let not_i1k = terms.mk_not_raw(eq_i1k);

        let clause = vec![concl, not_i0k, not_i1k];
        assert!(
            exec.plan_euf_lemma(&clause).is_some(),
            "the fused select congruence through a shared witness must be recognized"
        );
    }

    /// NEGATIVE shape 2a — the SAME clause with the second required
    /// arg-disequality `¬(= i1 k)` DROPPED. Without it `i0 = i1` is not
    /// entailed, so the conclusion does not follow and `plan_euf_lemma` must
    /// decline (return `None`) rather than fabricate a bogus congruence.
    #[test]
    fn fused_select_congruence_missing_arg_disequality_is_declined() {
        let mut exec = Executor::new();
        let terms = &mut exec.ctx.terms;
        let a1 = terms.mk_var("fscm_a1", Sort::Int);
        let i0 = terms.mk_var("fscm_i0", Sort::Int);
        let i1 = terms.mk_var("fscm_i1", Sort::Int);
        let k = terms.mk_var("fscm_k", Sort::Int);
        let sel0 = terms.mk_app(Symbol::named("select"), [a1, i0], Sort::Int);
        let sel1 = terms.mk_app(Symbol::named("select"), [a1, i1], Sort::Int);
        let concl = terms.mk_eq(sel0, sel1);
        let eq_i0k = terms.mk_eq(i0, k);
        let not_i0k = terms.mk_not_raw(eq_i0k);

        let clause = vec![concl, not_i0k];
        assert!(
            exec.plan_euf_lemma(&clause).is_none(),
            "a fused congruence missing a required arg-disequality must be declined"
        );
    }

    /// Shape 2b — an `(or …)`-wrapped `eq_transitive` leaf emitted as a raw
    /// `Step{Trust}` (not a `TheoryLemma`, so the TheoryLemma-only splitter
    /// passes never touch it). The extended promotion pass must re-derive it as
    /// checkable EUF steps so no trust step remains.
    #[test]
    fn or_wrapped_trust_step_eq_transitive_is_promoted() {
        let mut exec = Executor::new();
        let terms = &mut exec.ctx.terms;
        let a = terms.mk_var("ots_a", Sort::Int);
        let b = terms.mk_var("ots_b", Sort::Int);
        let c = terms.mk_var("ots_c", Sort::Int);
        let eq_ac = terms.mk_eq(a, c);
        let eq_ab = terms.mk_eq(a, b);
        let not_ab = terms.mk_not_raw(eq_ab);
        let eq_bc = terms.mk_eq(b, c);
        let not_bc = terms.mk_not_raw(eq_bc);
        // or_term = (or (= a c) (not (= a b)) (not (= b c)))
        let or_term = terms.mk_app(Symbol::named("or"), [eq_ac, not_ab, not_bc], Sort::Bool);
        let not_or = terms.mk_not_raw(or_term);

        let mut proof = Proof::new();
        let t0 = proof.add_rule_step(AletheRule::Trust, vec![or_term], Vec::new(), Vec::new());
        let h = proof.add_assume(not_or, None);
        proof.add_resolution(Vec::new(), or_term, t0, h);

        assert!(
            proof.steps.iter().any(|s| matches!(
                s,
                ProofStep::Step {
                    rule: AletheRule::Trust,
                    ..
                }
            )),
            "the leaf starts as a Step{{Trust}}"
        );
        exec.promote_certified_generic_euf_leaves(&mut proof);
        assert!(
            !proof.steps.iter().any(|s| matches!(
                s,
                ProofStep::Step {
                    rule: AletheRule::Trust | AletheRule::Hole,
                    ..
                } | ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::Generic,
                    ..
                }
            )),
            "the or-wrapped eq_transitive trust leaf must be replaced (no trust remains)"
        );
        assert!(
            proof.steps.iter().any(|s| matches!(
                s,
                ProofStep::Step {
                    rule: AletheRule::EqTransitive,
                    ..
                }
            )),
            "the replacement must emit a checkable eq_transitive step"
        );
    }

    /// NEGATIVE shape 2b — an `(or …)`-wrapped `Step{Trust}` whose flattened
    /// disjunction is NOT a valid transitivity tautology (the premises do not
    /// connect the conclusion endpoints). `plan_euf_lemma` must decline, so the
    /// pass leaves the proof byte-identical.
    #[test]
    fn or_wrapped_trust_step_disconnected_chain_is_left_unchanged() {
        let mut exec = Executor::new();
        let terms = &mut exec.ctx.terms;
        let a = terms.mk_var("otd_a", Sort::Int);
        let b = terms.mk_var("otd_b", Sort::Int);
        let c = terms.mk_var("otd_c", Sort::Int);
        let d = terms.mk_var("otd_d", Sort::Int);
        let eq_ad = terms.mk_eq(a, d);
        let eq_ab = terms.mk_eq(a, b);
        let not_ab = terms.mk_not_raw(eq_ab);
        let eq_cd = terms.mk_eq(c, d);
        let not_cd = terms.mk_not_raw(eq_cd);
        // (or (= a d) (not (= a b)) (not (= c d))) — a—b and c—d are disjoint.
        let or_term = terms.mk_app(Symbol::named("or"), [eq_ad, not_ab, not_cd], Sort::Bool);
        let not_or = terms.mk_not_raw(or_term);

        let mut proof = Proof::new();
        let t0 = proof.add_rule_step(AletheRule::Trust, vec![or_term], Vec::new(), Vec::new());
        let h = proof.add_assume(not_or, None);
        proof.add_resolution(Vec::new(), or_term, t0, h);

        let before = format!("{:?}", proof.steps);
        exec.promote_certified_generic_euf_leaves(&mut proof);
        assert_eq!(
            format!("{:?}", proof.steps),
            before,
            "a disconnected or-wrapped trust leaf must be left untouched"
        );
    }

    #[test]
    fn generic_euf_promotion_declines_wide_proof_before_mutation() {
        let mut exec = Executor::new();
        let atom = exec
            .ctx
            .terms
            .mk_var("generic_euf_preflight_atom", Sort::Bool);
        let mut proof = Proof::new();
        let assume = proof.add_assume(atom, None);
        proof.add_rule_step(
            AletheRule::Trust,
            Vec::new(),
            vec![assume; volume::MAX_PROMOTION_EDGES + 1],
            Vec::new(),
        );
        let before_len = proof.steps.len();

        exec.promote_certified_generic_euf_leaves(&mut proof);

        assert_eq!(proof.steps.len(), before_len);
        assert!(matches!(proof.steps.first(), Some(ProofStep::Assume(t)) if *t == atom));
        assert!(matches!(
            proof.steps.last(),
            Some(ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                premises,
                args,
            }) if clause.is_empty()
                && premises.len() == volume::MAX_PROMOTION_EDGES + 1
                && args.is_empty()
        ));
    }

    #[test]
    fn repeated_generic_euf_leaves_decline_transactionally_at_output_limit() {
        let mut exec = Executor::new();
        let a = exec.ctx.terms.mk_var("promotion_repeat_a", Sort::Int);
        let b = exec.ctx.terms.mk_var("promotion_repeat_b", Sort::Int);
        let c = exec.ctx.terms.mk_var("promotion_repeat_c", Sort::Int);
        let ab = exec.ctx.terms.mk_eq(a, b);
        let bc = exec.ctx.terms.mk_eq(b, c);
        let ac = exec.ctx.terms.mk_eq(a, c);
        let not_ab = exec.ctx.terms.mk_not_raw(ab);
        let not_bc = exec.ctx.terms.mk_not_raw(bc);
        let clause = vec![ac, not_ab, not_bc];
        let emitted = exec
            .plan_euf_lemma(&clause)
            .and_then(|plan| plan.emitted_literal_volume())
            .expect("bounded transitivity recipe");

        let mut proof = Proof::new();
        let first = proof.add_step(ProofStep::TheoryLemma {
            theory: "EUF".to_string(),
            clause: clause.clone(),
            farkas: None,
            kind: TheoryLemmaKind::Generic,
            lia: None,
        });
        let second = proof.add_step(ProofStep::TheoryLemma {
            theory: "EUF".to_string(),
            clause,
            farkas: None,
            kind: TheoryLemmaKind::Generic,
            lia: None,
        });
        proof.add_rule_step(
            AletheRule::Trust,
            Vec::new(),
            vec![first, second],
            Vec::new(),
        );
        let input = volume::preflight_promotion(&proof)
            .expect("small proof preflight")
            .input_volume;
        let before = format!("{:?}", proof.steps);

        // There is room for exactly one recipe, but both occurrences would
        // be emitted. The aggregate gate must decline before rebuilding.
        exec.promote_certified_generic_euf_leaves_bounded(&mut proof, input + emitted);

        assert_eq!(format!("{:?}", proof.steps), before);
    }
}
