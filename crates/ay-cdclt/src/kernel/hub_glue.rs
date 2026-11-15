// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The kernel's side of the hub (design §3.2 steps 2-3, §4.1, §4.3).
//!
//! - Registration: every uninterpreted application, its arguments, and every
//!   equality over an uninterpreted sort or between terms the hub already
//!   holds become nodes. Arithmetic-sorted nodes get a variable of the
//!   arithmetic plug-in (they are shared), terms of uninterpreted sorts are
//!   announced to EUF.
//! - Feeding: every assigned literal of a Boolean node reaches the hub, in
//!   addition to the atom's owner.
//! - Closure: the hub's conflicts and propagations become kernel effects
//!   (propagations with lazy reasons explained by the proof forest), and its
//!   `new_eq` / `new_diseq` events reach the plug-ins that carry variables
//!   on both classes.
//! - Combination (H3): at a final check every plug-in accepted at every
//!   effort level, shared arithmetic terms with equal model values but
//!   different classes get their equality minted (with its trichotomy
//!   lemma) and preferred true. `sat` needs none left. This is Nelson–Oppen
//!   in the arithmetic-to-hub direction; the hub-to-arithmetic direction is
//!   `new_eq` / `new_diseq` (`shared.rs`).
//! - Relevancy (KC21): with the engine option on, a hub propagation of a
//!   node the relevancy service has not marked is not handed to the search.
//!   Dropping a propagation is safe: every assigned literal still reaches
//!   the hub, and a clash with the hub's classes is a conflict.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Constant, Sort, TermData, TermId, TheoryLemmaKind, TheoryLit};
use ay_sat::{SolverContext, Variable};
use num_rational::BigRational;

use super::{Kernel, Relevancy};
use crate::atoms::{eq_atom, Family};
use crate::content::is_uf_app;
use crate::hub::{HubEvent, HubValue, NodeId};
use crate::lra_lemmas::trichotomy;
use crate::plugin::{
    Conflict, GiveUp, Justification, Lemma, LemmaTier, ProofHint, Propagation, ThId,
};

/// The lazy-reason owner id of hub propagations (never a plug-in index).
pub(crate) const HUB: ThId = ThId::MAX;

fn hub_hint() -> ProofHint {
    ProofHint::kind(TheoryLemmaKind::EufCongruenceExplanation)
}

impl Kernel<'_> {
    fn family_id(&self, family: Family) -> Option<ThId> {
        self.families
            .iter()
            .find(|(f, _)| *f == family)
            .map(|&(_, id)| id)
    }

    /// Give a new node its theory variables: the arithmetic plug-in of its
    /// sort, or EUF for an uninterpreted sort.
    pub(super) fn attach_vars(&mut self, n: NodeId, term: TermId) -> Result<(), GiveUp> {
        let sort = self.terms.sort(term).clone();
        if let Some(family) = Family::of_arith_sort(&sort) {
            let th = self.family_id(family).ok_or_else(|| {
                GiveUp::new(format!("a shared {} term has no plug-in", family.name()))
            })?;
            let var = self
                .call(th, None, |p, ctx| p.attach_term(ctx, term))
                .unwrap_or(Ok(None))?;
            if let Some(v) = var {
                self.hub.attach_var(n, th, v);
            }
        } else if sort.is_uninterpreted() {
            if let Some(th) = self.family_id(Family::Uf) {
                self.call(th, None, |p, ctx| p.attach_term(ctx, term))
                    .unwrap_or(Ok(None))?;
            }
        }
        self.map_hub_var(n, term)
    }

    /// A Boolean node listens to its SAT variable (through `not`s, with the
    /// polarity flipped).
    pub(super) fn map_hub_var(&mut self, n: NodeId, term: TermId) -> Result<(), GiveUp> {
        if self.terms.sort(term) != &Sort::Bool {
            return Ok(());
        }
        let (base, negated) = strip_not(self.terms, term);
        if matches!(self.terms.get(base), TermData::Const(Constant::Bool(_))) {
            return Ok(());
        }
        let var = self
            .atoms
            .var_of(base)
            .ok_or_else(|| GiveUp::new("a Boolean hub term has no SAT variable"))?;
        let idx = var as usize;
        if self.hub_var.len() <= idx {
            self.hub_var.resize(idx + 1, 0);
        }
        if self.hub_var[idx] == 0 {
            self.hub_watch.push(Vec::new());
            self.hub_var[idx] = u32::try_from(self.hub_watch.len())
                .map_err(|_| GiveUp::new("too many hub variables"))?;
        }
        let slot = self.hub_var[idx] as usize - 1;
        if !self.hub_watch[slot].contains(&(n, negated)) {
            self.hub_watch[slot].push((n, negated));
        }
        Ok(())
    }

    /// The node of a term that is not an uninterpreted application.
    pub(super) fn hub_leaf(&mut self, term: TermId) -> Result<NodeId, GiveUp> {
        if let Some(n) = self.hub.node_of(term) {
            return Ok(n);
        }
        let value = match self.terms.get(term) {
            TermData::Const(Constant::Bool(b)) => Some(HubValue::Bool(*b)),
            TermData::Const(Constant::Int(i)) => {
                Some(HubValue::Num(BigRational::from_integer(i.clone())))
            }
            TermData::Const(Constant::Rational(r)) => Some(HubValue::Num(r.0.clone())),
            _ => None,
        };
        let is_bool = self.terms.sort(term) == &Sort::Bool;
        let n = self.hub.add_leaf(term, is_bool, value);
        self.attach_vars(n, term)?;
        Ok(n)
    }

    /// Make an equality atom minted in the search a hub node when both its
    /// sides are nodes already (or, over an uninterpreted sort, when they
    /// can be leaves: every such term is EUF's). It never introduces an
    /// arithmetic term the layout did not name.
    pub(crate) fn watch_minted_equality(&mut self, eq: TermId) -> Result<(), GiveUp> {
        if self.hub.node_of(eq).is_some() {
            return Ok(());
        }
        let TermData::App(sym, args) = self.terms.get(eq) else {
            return Ok(());
        };
        if sym.name() != "=" || args.len() != 2 {
            return Ok(());
        }
        let (a, b) = (args[0], args[1]);
        let sort = self.terms.sort(a);
        if sort == &Sort::Bool {
            return Ok(());
        }
        let (has_a, has_b) = (self.hub.node_of(a).is_some(), self.hub.node_of(b).is_some());
        if !(sort.is_uninterpreted() || (has_a && has_b)) {
            return Ok(());
        }
        let na = self.hub_side(a)?;
        let nb = self.hub_side(b)?;
        let n = self.hub.add_eq(eq, na, nb);
        // A node minted in the search: its `EqTrue` merge (if its sides are
        // already equal) belongs to this level, not a deeper one.
        self.hub.propagate();
        self.map_hub_var(n, eq)
    }

    fn hub_side(&mut self, term: TermId) -> Result<NodeId, GiveUp> {
        match self.hub.node_of(term) {
            Some(n) => Ok(n),
            None if is_uf_app(self.terms, term) => Err(GiveUp::new(
                "an uninterpreted application reached the hub unregistered",
            )),
            None => self.hub_leaf(term),
        }
    }

    /// Run the hub to a fixpoint and turn its output into kernel effects.
    pub(super) fn hub_closure(&mut self, sat: &dyn SolverContext) -> Result<(), GiveUp> {
        self.hub.propagate();
        if let Some(conflict) = self.hub.take_conflict() {
            self.hub.record_transitivity(true);
            let lits = self.hub.explain(conflict.a, conflict.b);
            self.hub.record_transitivity(false);
            let lits = lits
                .filter(|lits| !lits.is_empty())
                .ok_or_else(|| GiveUp::new("hub conflict without an explanation"))?;
            self.transitivity_lemmas();
            self.stats.hub_conflicts += 1;
            if self.effects.conflict.is_none() {
                self.effects.conflict = Some(Conflict {
                    lits,
                    hint: hub_hint(),
                });
            }
            let _ = self.hub.take_props();
            let _ = self.hub.take_events();
            return Ok(());
        }
        for (n, v) in self.hub.take_props() {
            let Some(value) = self.hub.bool_value(v) else {
                continue;
            };
            let term = self.hub.term(n);
            if self
                .relevancy
                .as_ref()
                .is_some_and(|r| !r.is_relevant(term))
            {
                continue;
            }
            self.stats.hub_propagations += 1;
            let token = u64::try_from(self.hub_props.len()).unwrap_or(u64::MAX);
            self.hub_props.push((n, v));
            self.effects.props.push(Propagation {
                plugin: HUB,
                lit: TheoryLit::new(term, value),
                why: Justification::Lazy(token),
            });
        }
        for event in self.hub.take_events() {
            self.dispatch(event, sat)?;
        }
        Ok(())
    }

    fn dispatch(&mut self, event: HubEvent, sat: &dyn SolverContext) -> Result<(), GiveUp> {
        match event {
            HubEvent::NewEq { th, a, b, na, nb } => {
                if self.owner_has(th, na, nb, true, sat) {
                    return Ok(());
                }
                let why = self
                    .hub
                    .explain(na, nb)
                    .ok_or_else(|| GiveUp::new("new_eq across classes"))?;
                self.stats.new_eqs += 1;
                self.call(th, Some(sat), |p, ctx| p.new_eq(ctx, a, b, &why))
                    .unwrap_or(Ok(()))
            }
            HubEvent::NewDiseq {
                th,
                a,
                b,
                eq,
                na,
                nb,
            } => {
                let Some((x, y)) = self.hub.eq_args(eq) else {
                    return Ok(());
                };
                if self.owner_has(th, na, nb, false, sat) {
                    return Ok(());
                }
                self.stats.new_diseqs += 1;
                let mut why = vec![TheoryLit::new(self.hub.term(eq), false)];
                let across = || GiveUp::new("new_diseq across classes");
                why.extend(self.hub.explain(x, na).ok_or_else(across)?);
                why.extend(self.hub.explain(y, nb).ok_or_else(across)?);
                self.call(th, Some(sat), |p, ctx| p.new_diseq(ctx, a, b, &why))
                    .unwrap_or(Ok(()))
            }
        }
    }

    /// Whether plug-in `th` already holds `(= a b)` with this value as an
    /// assigned atom of its own (fed before any hub event of this closure):
    /// then the event tells it nothing, and the explanation is not built.
    fn owner_has(
        &self,
        th: ThId,
        na: NodeId,
        nb: NodeId,
        value: bool,
        sat: &dyn SolverContext,
    ) -> bool {
        let Some(eq) = self.terms.find_eq(self.hub.term(na), self.hub.term(nb)) else {
            return false;
        };
        let Some(var) = self.atoms.var_of(eq) else {
            return false;
        };
        self.atoms
            .entry(var as usize)
            .is_some_and(|entry| entry.owner == th)
            && sat.value(Variable::new(var)) == Some(value)
    }

    /// The hub's explanation for a lazily propagated literal.
    pub(super) fn explain_hub(&mut self, token: u64) -> Option<(Vec<TheoryLit>, ProofHint)> {
        let &(n, v) = self.hub_props.get(usize::try_from(token).ok()?)?;
        // Asked during conflict analysis: the path counts toward dynamic
        // transitivity like a conflict's.
        self.hub.record_transitivity(true);
        let lits = self.hub.explain(n, v);
        self.hub.record_transitivity(false);
        self.transitivity_lemmas();
        Some((lits?, hub_hint()))
    }

    /// The transitivity lemmas the hub's counters made due
    /// (`hub/transitivity.rs`): `¬(a = b) ∨ ¬(b = c) ∨ (a = c)`, EUF-valid
    /// (K4); the kernel mints `a = c` when it maps the lemma.
    fn transitivity_lemmas(&mut self) {
        for due in self.hub.take_transitivity() {
            let (ta, tb) = (self.hub.term(due.a), self.hub.term(due.b));
            let eq = eq_atom(self.terms, ta, tb);
            self.stats.transitivity_lemmas += 1;
            self.effects.lemmas.push(Lemma {
                clause: vec![
                    TheoryLit::new(due.first.term, false),
                    TheoryLit::new(due.second.term, false),
                    TheoryLit::new(eq, true),
                ],
                tier: LemmaTier::Redundant,
                hint: ProofHint::kind(TheoryLemmaKind::EufTransitive),
            });
        }
    }

    /// Model-based theory combination at a final check every plug-in
    /// accepted (design H3). `Ok(true)`: candidate equalities were minted and
    /// preferred; the search continues.
    pub(super) fn combine(&mut self, sat: &dyn SolverContext) -> Result<bool, GiveUp> {
        let shared: Vec<NodeId> = self.hub.shared_nodes().to_vec();
        if shared.is_empty() {
            return Ok(false);
        }
        // Every plug-in accepted the assignment: let each keep the model of
        // its current state, which `model_value` reads.
        for id in 0..self.plugin_count() {
            self.call(id, Some(sat), |p, ctx| p.on_sat(ctx));
        }
        let mut first: HashMap<(ThId, BigRational), NodeId> = HashMap::default();
        let mut done: HashSet<(NodeId, NodeId)> = HashSet::default();
        let mut pairs: Vec<(ThId, NodeId, NodeId)> = Vec::new();
        for n in shared {
            let term = self.hub.term(n);
            let Some(th) = Family::of_arith_sort(self.terms.sort(term))
                .and_then(|family| self.family_id(family))
            else {
                continue;
            };
            let value = self
                .call(th, Some(sat), |p, ctx| p.model_value(ctx, term))
                .flatten()
                .and_then(|v| numeral(self.terms, v))
                .ok_or_else(|| GiveUp::new("combination: a shared term has no model value"))?;
            match first.get(&(th, value.clone())) {
                Some(&m) => {
                    let (rm, rn) = (self.hub.root(m), self.hub.root(n));
                    if rm != rn && done.insert((rm.min(rn), rm.max(rn))) {
                        pairs.push((th, m, n));
                    }
                }
                None => {
                    first.insert((th, value), n);
                }
            }
        }
        for &(th, m, n) in &pairs {
            let (ta, tb) = (self.hub.term(m), self.hub.term(n));
            self.stats.combination_equalities += 1;
            let outcome = self.call(th, Some(sat), |_, ctx| {
                let terms = ctx.terms_mut();
                let eq = eq_atom(terms, ta, tb);
                match ctx.value(eq) {
                    Some(true) => Err(GiveUp::new(
                        "combination: an asserted shared equality did not reach the hub",
                    )),
                    Some(false) => Err(GiveUp::new(
                        "combination: a model violates an asserted shared disequality",
                    )),
                    None => {
                        let terms = ctx.terms_mut();
                        let lt = terms.mk_lt(ta, tb);
                        let gt = terms.mk_gt(ta, tb);
                        ctx.lemma(trichotomy(lt, gt, eq));
                        ctx.prefer(TheoryLit::new(eq, true));
                        Ok(())
                    }
                }
            });
            outcome.unwrap_or(Ok(()))?;
        }
        Ok(!pairs.is_empty())
    }

    /// Start the relevancy service (KC21) when the engine option is on: the
    /// assertions are relevant at level 0.
    pub(crate) fn start_relevancy(&mut self, assertions: &[TermId]) -> Result<(), GiveUp> {
        if !self.hub_relevancy {
            return Ok(());
        }
        let mut relevancy = Relevancy::new(&self.atoms);
        for &root in assertions {
            relevancy.mark_root(root, self.terms, &self.atoms, &mut self.hub);
        }
        self.stats.relevant_marked = relevancy.marked();
        self.relevancy = Some(relevancy);
        Ok(())
    }

    /// A term minted during the search is relevant from then on.
    pub(super) fn minted_relevant(&mut self, term: TermId) {
        if let Some(relevancy) = self.relevancy.as_mut() {
            relevancy.always(term);
        }
    }

    /// SAT variables the hub reads (to be frozen against inprocessing).
    pub(crate) fn hub_vars(&self) -> Vec<u32> {
        self.hub_var
            .iter()
            .enumerate()
            .filter(|(_, &w)| w != 0)
            .filter_map(|(var, _)| u32::try_from(var).ok())
            .collect()
    }
}

fn strip_not(terms: &ay_core::TermStore, mut term: TermId) -> (TermId, bool) {
    let mut negated = false;
    while let TermData::Not(inner) = terms.get(term) {
        term = *inner;
        negated = !negated;
    }
    (term, negated)
}

fn numeral(terms: &ay_core::TermStore, term: TermId) -> Option<BigRational> {
    match terms.get(term) {
        TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
        TermData::Const(Constant::Int(i)) => Some(BigRational::from_integer(i.clone())),
        _ => None,
    }
}
