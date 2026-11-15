// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Turning the assembled DAG into proof steps: literal and term mapping,
//! then the steps themselves, premises first (see the parent module).

use ay_core::{
    AletheRule, FarkasAnnotation, ProofId, ProofStep, TermData, TermId, TermStore, TheoryLemmaKind,
    TheoryLit,
};
use ay_sat::{Literal, Variable};
use num_traits::Zero;

use super::rup::Derivation;
use super::{Assembler, Node, Plan, ProofFailure};
use crate::plugin::ProofHint;

impl Assembler<'_> {
    /// The SAT literal of a theory literal: its atom's variable, or a fresh
    /// variable past the solver's for an atom only a hint premise names.
    pub(super) fn lit_of(&mut self, lit: TheoryLit) -> Literal {
        let (atom, value) = strip_not(self.terms, lit.term, lit.value);
        if self.term_vars.is_empty() {
            for (var, term) in self.var_terms.iter().enumerate() {
                if let Some(term) = term {
                    self.term_vars.insert(*term, var as u32);
                }
            }
        }
        let next = (self.var_terms.len() + self.extra_terms.len()) as u32;
        let var = *self.term_vars.entry(atom).or_insert(next);
        if var == next {
            self.extra_terms.push(atom);
        }
        let var = Variable::new(var);
        if value {
            Literal::positive(var)
        } else {
            Literal::negative(var)
        }
    }

    pub(super) fn lit_term(&mut self, lit: Literal) -> Option<TermId> {
        if let Some(&t) = self.lit_terms.get(&lit) {
            return Some(t);
        }
        let index = lit.variable().index();
        let atom = match self.var_terms.get(index) {
            Some(named) => (*named)?,
            None => *self.extra_terms.get(index - self.var_terms.len())?,
        };
        let term = if lit.is_positive() {
            atom
        } else {
            match self.terms.get(atom) {
                TermData::Not(inner) => *inner,
                _ => self.terms.mk_not_raw(atom),
            }
        };
        self.lit_terms.insert(lit, term);
        Some(term)
    }

    pub(super) fn clause_terms(&mut self, lits: &[Literal]) -> Result<Vec<TermId>, ProofFailure> {
        lits.iter()
            .map(|&l| {
                self.lit_term(l)
                    .ok_or(ProofFailure::UnnamedVariable(l.variable().index() as u32))
            })
            .collect()
    }

    /// Emit `root` and everything it depends on, premises first.
    pub(super) fn emit(&mut self, root: usize) -> Result<ProofId, ProofFailure> {
        let mut stack = vec![(root, false)];
        while let Some((n, expanded)) = stack.pop() {
            if self.nodes[n].emitted.is_some() {
                continue;
            }
            if !expanded {
                stack.push((n, true));
                if let Plan::Chain(d) = &self.nodes[n].plan {
                    for p in d.premises() {
                        if self.nodes[p].emitted.is_none() {
                            stack.push((p, false));
                        }
                    }
                }
                continue;
            }
            let id = self.emit_node(n)?;
            self.nodes[n].emitted = Some(id);
        }
        self.nodes[root].emitted.ok_or(ProofFailure::NoEmptyClause)
    }

    fn push_step(&mut self, step: ProofStep) -> ProofId {
        let id = ProofId(u32::try_from(self.steps.len()).unwrap_or(u32::MAX));
        self.steps.push(step);
        id
    }

    fn emit_node(&mut self, n: usize) -> Result<ProofId, ProofFailure> {
        let plan = self.nodes[n].plan.clone();
        match plan {
            Plan::Assume(term) => {
                self.stats.assumes += 1;
                Ok(self.push_step(ProofStep::Assume(term)))
            }
            Plan::Tautology {
                rule,
                source,
                clause,
            } => {
                self.stats.clausification += 1;
                Ok(self.push_step(ProofStep::Step {
                    rule,
                    clause,
                    premises: Vec::new(),
                    args: vec![source],
                }))
            }
            Plan::Theory(r) => {
                let records = self.records;
                let step = &records[r];
                Ok(self.emit_theory(&step.clause, &step.hint))
            }
            Plan::Premise(r, j) => {
                let records = self.records;
                let premise = &records[r].hint.premises[j];
                Ok(self.emit_theory(&premise.clause, &premise.hint))
            }
            Plan::Chain(d) => self.emit_chain(n, &d),
            Plan::Hole => {
                self.stats.holes += 1;
                self.stats.unjustified += 1;
                let clause = self.clause_terms(&self.nodes[n].lits.clone())?;
                Ok(self.push_step(ProofStep::Step {
                    rule: AletheRule::Hole,
                    clause,
                    premises: Vec::new(),
                    args: Vec::new(),
                }))
            }
        }
    }

    /// A theory lemma step over its certificate's support.
    fn emit_theory(&mut self, lits: &[TheoryLit], hint: &ProofHint) -> ProofId {
        let mut kind = hint.kind;
        let farkas = hint
            .farkas
            .as_ref()
            .filter(|f| f.coefficients.len() == lits.len());
        let mut clause: Vec<TermId> = Vec::with_capacity(lits.len());
        let mut coefficients = Vec::new();
        for pos in support(lits, hint) {
            let lit = lits[pos];
            let (atom, value) = strip_not(self.terms, lit.term, lit.value);
            let term = if value {
                atom
            } else {
                self.terms.mk_not_raw(atom)
            };
            clause.push(term);
            coefficients.extend(farkas.map(|f| f.coefficients[pos]));
        }
        let mut farkas = farkas.map(|_| FarkasAnnotation::new(coefficients));
        // Merge repeated literals (a clause is a set); the certificate sums.
        let mut dedup = clause.clone();
        {
            let mut seen = std::collections::BTreeSet::new();
            dedup.retain(|t| seen.insert(*t));
        }
        if dedup.len() != clause.len() {
            farkas = farkas.and_then(|f| f.rebind_by_literal(&clause, &dedup));
            clause = dedup;
        }
        if kind == TheoryLemmaKind::LraFarkas && farkas.is_none() {
            // A Farkas kind without its certificate is a claim, not a step.
            kind = TheoryLemmaKind::Generic;
        }
        if kind == TheoryLemmaKind::Generic {
            self.stats.holes += 1;
        }
        self.stats.theory_lemmas += 1;
        *self
            .stats
            .theory_kinds
            .entry(format!("{kind:?}"))
            .or_default() += 1;
        let theory = match kind {
            TheoryLemmaKind::LraFarkas
            | TheoryLemmaKind::ArithDisequalitySplit
            | TheoryLemmaKind::ArithEqTriangle => "LRA",
            TheoryLemmaKind::IntBoundsTautology => "LIA",
            _ => "kernel",
        };
        self.push_step(ProofStep::TheoryLemma {
            theory: theory.to_string(),
            clause,
            farkas,
            kind,
            lia: None,
        })
    }

    /// One n-ary `resolution` step: the conflict premise, then each reason
    /// premise in the order the chain cancels their pivots. Each premise
    /// cancels exactly one literal of the accumulator, so the step needs no
    /// pivot list; with one, AY's checker would also refuse a literal the
    /// accumulator and the premise share, which conflict analysis produces
    /// routinely.
    fn emit_chain(&mut self, n: usize, d: &Derivation) -> Result<ProofId, ProofFailure> {
        let emitted = |node: &Node| node.emitted.ok_or(ProofFailure::NoEmptyClause);
        if d.links.is_empty() {
            // An identity: this node concludes its premise's clause.
            return emitted(&self.nodes[d.conflict]);
        }
        let mut premises = Vec::with_capacity(d.links.len() + 1);
        premises.push(emitted(&self.nodes[d.conflict])?);
        for link in &d.links {
            premises.push(emitted(&self.nodes[link.premise])?);
        }
        let clause = self.clause_terms(&self.nodes[n].lits.clone())?;
        self.stats.resolutions += 1;
        Ok(self.push_step(ProofStep::Step {
            rule: AletheRule::Resolution,
            clause,
            premises,
            args: Vec::new(),
        }))
    }
}

/// The positions of `lits` a hint's certificate uses: every position, less
/// those a Farkas certificate weights 0.
pub(super) fn support<'h>(
    lits: &'h [TheoryLit],
    hint: &'h ProofHint,
) -> impl Iterator<Item = usize> + 'h {
    let farkas = hint
        .farkas
        .as_ref()
        .filter(|f| f.coefficients.len() == lits.len());
    (0..lits.len()).filter(move |&p| farkas.map_or(true, |f| !f.coefficients[p].is_zero()))
}

fn strip_not(terms: &TermStore, mut term: TermId, mut value: bool) -> (TermId, bool) {
    while let TermData::Not(inner) = terms.get(term) {
        term = *inner;
        value = !value;
    }
    (term, value)
}
