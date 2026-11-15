// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Turning plug-in effects into SAT clauses: minting, lemma and conflict
//! mapping, propagation reasons (design §3.3, §3.4, §3.7). Every clause is
//! recorded with its proof hint at the moment it is made (P1).

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Constant, TermData, TermId, TermStore, TheoryLit};
use ay_sat::{ExtPropagateResult, Literal, SolverContext, Variable};
use num_traits::Zero;

use super::hub_glue::HUB;
use super::{Kernel, LazyEntry};
use crate::atoms::{owner_of, Owner};
use crate::plugin::{
    Conflict, Explanation, GiveUp, Justification, Lemma, LemmaTier, ProofHint, Propagation, ThId,
};

/// Lemmas of one callback, split by tier (K5).
#[derive(Default)]
pub(super) struct MappedLemmas {
    pub(super) redundant: Vec<Vec<Literal>>,
    pub(super) definitional: Vec<Vec<Literal>>,
}

impl Kernel<'_> {
    pub(super) fn mint(&mut self, term: TermId, sat: &dyn SolverContext) -> Result<u32, GiveUp> {
        let owner = match owner_of(self.terms, term)? {
            Owner::Family(family) => self
                .families
                .iter()
                .find(|(f, _)| *f == family)
                .map(|&(_, id)| id)
                .ok_or_else(|| {
                    GiveUp::new(format!(
                        "a minted {} atom has no plug-in in this check",
                        family.name()
                    ))
                })?,
            Owner::Ground(_) => self
                .families
                .iter()
                .find(|(f, _)| f.is_arith())
                .map(|&(_, id)| id)
                .ok_or_else(|| GiveUp::new("a minted ground atom has no plug-in"))?,
        };
        let base = sat.num_vars();
        if base == 0 {
            return Err(GiveUp::new("cannot mint: solver size unknown"));
        }
        self.next_mint = self.next_mint.max(base);
        let var = u32::try_from(self.next_mint)
            .map_err(|_| GiveUp::new("SAT variable space exhausted"))?;
        self.next_mint += 1;
        self.atoms.insert(var, term, owner);
        self.minted.push((var, owner, term));
        self.stats.minted_atoms += 1;
        self.minted_relevant(term);
        self.watch_minted_equality(term)?;
        Ok(var)
    }

    /// Map a lemma to a SAT clause, minting atoms that have no variable (safe
    /// on every path since ay-sat G3). `Ok(None)`: a Boolean constant already
    /// satisfies the lemma.
    pub(super) fn lemma_clause(
        &mut self,
        lemma: Lemma,
        sat: &dyn SolverContext,
    ) -> Result<Option<Vec<Literal>>, GiveUp> {
        let mut clause = Vec::with_capacity(lemma.clause.len());
        // The literals that reach the SAT clause, and whether a `false`
        // constant that does not was weighted by the hint's certificate.
        let mut kept = Vec::with_capacity(lemma.clause.len());
        let mut dropped_weighted = false;
        for (pos, lit) in lemma.clause.iter().enumerate() {
            let (term, value) = strip_not(self.terms, lit.term, lit.value);
            match bool_const(self.terms, term) {
                Some(b) if b == value => return Ok(None),
                Some(_) => {
                    dropped_weighted |= lemma
                        .hint
                        .farkas
                        .as_ref()
                        .is_some_and(|f| f.coefficients.get(pos).is_some_and(|c| !c.is_zero()));
                    continue;
                }
                None => {}
            }
            let var = match self.atoms.var_of(term) {
                Some(var) => var,
                None => self.mint(term, sat)?,
            };
            clause.push(sat_lit(var, value));
            kept.push(pos);
        }
        if clause.is_empty() {
            return Err(GiveUp::new("a plug-in lemma reduced to the empty clause"));
        }
        match lemma.tier {
            LemmaTier::Redundant => self.stats.lemmas += 1,
            LemmaTier::Definitional => self.stats.definitions += 1,
        }
        if self.proof.is_some() {
            let mut hint = lemma.hint;
            if kept.len() != lemma.clause.len() {
                hint.farkas = hint.farkas.filter(|_| !dropped_weighted).map(|f| {
                    ay_core::FarkasAnnotation::new(
                        kept.iter()
                            .filter_map(|&p| f.coefficients.get(p).copied())
                            .collect(),
                    )
                });
            }
            let recorded = kept
                .iter()
                .filter_map(|&p| lemma.clause.get(p).copied())
                .collect();
            self.record(recorded, &clause, hint, lemma.tier);
        }
        Ok(Some(clause))
    }

    /// The clause negating a conflict. Fails closed unless every literal is
    /// an atom that is currently true (else the clause would not be falsified).
    pub(super) fn conflict_clause(
        &mut self,
        conflict: Conflict,
        sat: &dyn SolverContext,
    ) -> Result<Vec<Literal>, GiveUp> {
        if conflict.lits.is_empty() {
            return Err(GiveUp::new("empty theory conflict"));
        }
        let mut clause = Vec::with_capacity(conflict.lits.len());
        let mut negated = Vec::with_capacity(conflict.lits.len());
        for lit in &conflict.lits {
            let (term, value) = strip_not(self.terms, lit.term, lit.value);
            let var = self
                .atoms
                .var_of(term)
                .ok_or_else(|| GiveUp::new("conflict literal has no SAT variable"))?;
            let slit = sat_lit(var, value);
            if sat.lit_value(slit) != Some(true) {
                return Err(GiveUp::new("conflict literal is not true on the trail"));
            }
            clause.push(slit.negated());
            negated.push(TheoryLit::new(lit.term, !lit.value));
        }
        self.stats.conflicts += 1;
        self.record(negated, &clause, conflict.hint, LemmaTier::Redundant);
        Ok(clause)
    }

    /// `[lit, ¬r1, ..]` when every reason literal is an atom that is true now.
    pub(super) fn reason_clause(
        &self,
        lit: Literal,
        reason: &[TheoryLit],
        sat: &dyn SolverContext,
    ) -> Option<Vec<Literal>> {
        let mut clause = Vec::with_capacity(reason.len() + 1);
        clause.push(lit);
        for r in reason {
            let (term, value) = strip_not(self.terms, r.term, r.value);
            let rlit = sat_lit(self.atoms.var_of(term)?, value);
            if sat.lit_value(rlit) != Some(true) {
                return None;
            }
            clause.push(rlit.negated());
        }
        Some(clause)
    }

    /// Whether a buffered propagation names a literal that is false now (at
    /// a final check that is a conflict the final check must report).
    pub(super) fn a_propagation_is_refuted(&self, sat: &dyn SolverContext) -> bool {
        self.effects.props.iter().any(|prop| {
            let (term, value) = strip_not(self.terms, prop.lit.term, prop.lit.value);
            self.atoms
                .var_of(term)
                .is_some_and(|var| sat.lit_value(sat_lit(var, value)) == Some(false))
        })
    }

    pub(super) fn explain_entry(
        &mut self,
        plugin: ThId,
        token: u64,
        lit: TheoryLit,
    ) -> Option<(Vec<TheoryLit>, ProofHint)> {
        if plugin == HUB {
            self.stats.lazy_explained += 1;
            return self.explain_hub(token);
        }
        let explanation = self.call(plugin, None, |p, ctx| p.explain(ctx, lit, token))??;
        self.reset_effects_keeping_lemmas();
        self.stats.lazy_explained += 1;
        Some((explanation.reason, explanation.hint))
    }

    /// Record the reason clause `[lit, ¬r1, ..]` (as `sat_clause`, in the
    /// same order) of a propagation.
    pub(super) fn record_reason(
        &mut self,
        lit: TheoryLit,
        reason: &[TheoryLit],
        sat_clause: &[Literal],
        hint: ProofHint,
    ) {
        if self.proof.is_none() {
            return;
        }
        let mut clause = Vec::with_capacity(reason.len() + 1);
        clause.push(lit);
        clause.extend(reason.iter().map(|r| TheoryLit::new(r.term, !r.value)));
        self.record(clause, sat_clause, hint, LemmaTier::Redundant);
    }

    pub(super) fn push_propagation(
        &mut self,
        prop: Propagation,
        sat: &dyn SolverContext,
        seen: &mut HashSet<u32>,
        result: &mut ExtPropagateResult,
    ) {
        let (term, value) = strip_not(self.terms, prop.lit.term, prop.lit.value);
        let Some(var) = self.atoms.var_of(term) else {
            return; // not an atom: nothing for the SAT solver to learn
        };
        if seen.contains(&var) {
            return; // one propagation per variable per batch (ay-sat requires unassigned)
        }
        let lit = sat_lit(var, value);
        match sat.lit_value(lit) {
            Some(true) => {}
            Some(false) => {
                if result.conflict.is_some() {
                    return;
                }
                let (reason, hint) = match prop.why {
                    Justification::Eager(e) => (e.reason, e.hint),
                    Justification::Lazy(token) => {
                        let Some(found) = self.explain_entry(prop.plugin, token, prop.lit) else {
                            return;
                        };
                        found
                    }
                };
                if let Some(clause) = self.reason_clause(lit, &reason, sat) {
                    self.record_reason(prop.lit, &reason, &clause, hint);
                    self.stats.conflicts += 1;
                    result.conflict = Some(clause);
                }
            }
            None => {
                seen.insert(var);
                // Recording: a level-0 propagation is explained now. ay-sat
                // proves each level-0 fact by a unit clause built from its
                // reason clause, and a lazy reason at level 0 has none, so the
                // refutation's final chain would lose it.
                let why = match prop.why {
                    Justification::Lazy(token)
                        if self.proof.is_some() && sat.decision_level() == 0 =>
                    {
                        match self.explain_entry(prop.plugin, token, prop.lit) {
                            Some((reason, hint)) => {
                                Justification::Eager(Explanation { reason, hint })
                            }
                            None => return,
                        }
                    }
                    why => why,
                };
                match why {
                    Justification::Eager(e) => {
                        if let Some(clause) = self.reason_clause(lit, &e.reason, sat) {
                            self.record_reason(prop.lit, &e.reason, &clause, e.hint);
                            self.stats.eager_propagations += 1;
                            result.propagations.push((clause, lit));
                        }
                    }
                    Justification::Lazy(token) => {
                        let tag = u64::try_from(self.lazy.len()).unwrap_or(u64::MAX);
                        self.lazy.push(LazyEntry {
                            plugin: prop.plugin,
                            token,
                            lit: prop.lit,
                        });
                        self.stats.lazy_propagations += 1;
                        result.lazy_propagations.push((lit, tag));
                    }
                }
            }
        }
    }

    /// Map every lemma of the current effects, minting as needed (G3).
    pub(super) fn map_lemmas(
        &mut self,
        lemmas: Vec<Lemma>,
        sat: &dyn SolverContext,
    ) -> Result<MappedLemmas, GiveUp> {
        let mut mapped = MappedLemmas::default();
        for lemma in lemmas {
            let tier = lemma.tier;
            if let Some(clause) = self.lemma_clause(lemma, sat)? {
                match tier {
                    LemmaTier::Redundant => mapped.redundant.push(clause),
                    LemmaTier::Definitional => mapped.definitional.push(clause),
                }
            }
        }
        Ok(mapped)
    }

    /// Record preferred literals (H3). Their atoms exist by now: either they
    /// had a variable already or a lemma of this callback minted one.
    pub(super) fn note_preferred(&mut self, preferred: Vec<TheoryLit>) -> Result<(), GiveUp> {
        for lit in preferred {
            let (term, value) = strip_not(self.terms, lit.term, lit.value);
            if bool_const(self.terms, term).is_some() {
                continue;
            }
            let var = self.atoms.var_of(term).ok_or_else(|| {
                GiveUp::new("a preferred literal names an atom no lemma introduced")
            })?;
            self.preferred.push(sat_lit(var, value));
        }
        Ok(())
    }
}

pub(super) fn sat_lit(var: u32, value: bool) -> Literal {
    let v = Variable::new(var);
    if value {
        Literal::positive(v)
    } else {
        Literal::negative(v)
    }
}

pub(super) fn strip_not(terms: &TermStore, mut term: TermId, mut value: bool) -> (TermId, bool) {
    while let TermData::Not(inner) = terms.get(term) {
        term = *inner;
        value = !value;
    }
    (term, value)
}

pub(super) fn bool_const(terms: &TermStore, term: TermId) -> Option<bool> {
    match terms.get(term) {
        TermData::Const(Constant::Bool(b)) => Some(*b),
        _ => None,
    }
}
