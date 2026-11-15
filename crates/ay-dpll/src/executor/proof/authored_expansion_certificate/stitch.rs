// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The stitch: the renamed probe refutation, with every probe `assume`
//! replaced by an authored-scope derivation of the same unit.
//!
//! Nothing here is authority. An `assume` the stitch does not recognize is
//! passed through unchanged, so its refusal is the installation boundary's
//! (reachable assumes must be exact authored roots), never a silent accept.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{AletheRule, Proof, ProofId, ProofStep, TermId};

use crate::executor::expansion::lemma_plan::{Lemma, LemmaKind};
use crate::executor::Executor;

/// Constant-atom facts: the renamed unit (`a` or `(not a)`) → `(a, value)`.
pub(super) type ConstantFacts = HashMap<TermId, (TermId, bool)>;

/// The unit `fact` for a constant atom: `(cl true)` / `(cl (not false))` by
/// the `true` / `false` rules, or a one-literal `la_generic` (Farkas
/// coefficient 1) whose negation is the variable-free infeasible comparison.
/// A wrong truth value is a unit the strict checker refuses.
fn derive_constant_fact(
    terms: &ay_core::TermStore,
    candidate: &mut Proof,
    fact: TermId,
    atom: TermId,
    truth: bool,
) -> ProofId {
    if matches!(terms.get(atom), ay_core::term::TermData::Const(_)) {
        let rule = if truth {
            AletheRule::True
        } else {
            AletheRule::False
        };
        return candidate.add_rule_step(rule, vec![fact], Vec::new(), Vec::new());
    }
    candidate.add_theory_lemma_with_farkas(
        "LRA",
        vec![fact],
        ay_core::FarkasAnnotation::from_ints(&[1]),
    )
}

/// What the stitch may derive a probe `assume` from.
pub(super) struct StitchSources<'a> {
    pub(super) authored: &'a [TermId],
    pub(super) lemmas: &'a [Lemma],
    pub(super) constants: &'a ConstantFacts,
}

/// The stitch's lookup tables and the derived-unit memo.
struct StitchState<'a> {
    authored_set: HashSet<TermId>,
    authored: &'a [TermId],
    lemmas: HashMap<TermId, &'a Lemma>,
    constants: &'a ConstantFacts,
    units: HashMap<TermId, ProofId>,
}

impl Executor {
    /// Replace every probe `assume` with an authored-scope derivation and
    /// re-index the remaining steps (premises always point backward).
    pub(super) fn stitch_expansion_certificate(
        &mut self,
        probe: &Proof,
        sources: &StitchSources<'_>,
    ) -> Option<Proof> {
        let mut state = StitchState {
            authored_set: sources.authored.iter().copied().collect(),
            authored: sources.authored,
            lemmas: sources
                .lemmas
                .iter()
                .map(|lemma| (lemma.term, lemma))
                .collect(),
            constants: sources.constants,
            units: HashMap::default(),
        };
        let mut candidate = Proof::new();
        let mut remap: Vec<Option<ProofId>> = vec![None; probe.steps.len()];
        let premise = |remap: &[Option<ProofId>], id: ProofId| -> Option<ProofId> {
            remap.get(id.0 as usize).copied().flatten()
        };
        for (index, step) in probe.steps.iter().enumerate() {
            let mapped = match step {
                ProofStep::Assume(term) => match state.units.get(term) {
                    Some(&unit) => unit,
                    None => {
                        let unit = self.expansion_unit(&mut candidate, *term, &mut state);
                        state.units.insert(*term, unit);
                        unit
                    }
                },
                ProofStep::Resolution {
                    clause,
                    pivot,
                    clause1,
                    clause2,
                } => {
                    let clause1 = premise(&remap, *clause1)?;
                    let clause2 = premise(&remap, *clause2)?;
                    candidate.add_resolution(clause.clone(), *pivot, clause1, clause2)
                }
                ProofStep::TheoryLemma { .. } => candidate.add_step(step.clone()),
                ProofStep::Step {
                    rule,
                    clause,
                    premises,
                    args,
                } => {
                    let premises = premises
                        .iter()
                        .map(|&id| premise(&remap, id))
                        .collect::<Option<Vec<_>>>()?;
                    candidate.add_rule_step(rule.clone(), clause.clone(), premises, args.clone())
                }
                _ => return None,
            };
            remap[index] = Some(mapped);
        }
        Some(candidate)
    }

    /// The unit `(cl term)` for a probe assumption: an authored root, a
    /// lemma's derivation, a constant fact, an `and_pos` projection of a root
    /// — or, for anything else, a bare `assume` the boundary will refuse.
    fn expansion_unit(
        &mut self,
        candidate: &mut Proof,
        term: TermId,
        state: &mut StitchState<'_>,
    ) -> ProofId {
        if state.authored_set.contains(&term) {
            return *state
                .units
                .entry(term)
                .or_insert_with(|| candidate.add_assume(term, None));
        }
        if let Some(lemma) = state.lemmas.get(&term) {
            return self.derive_expansion_lemma(candidate, lemma);
        }
        if let Some(&(atom, truth)) = state.constants.get(&term) {
            return derive_constant_fact(&self.ctx.terms, candidate, term, atom, truth);
        }
        for &root in state.authored {
            let Some(path) = self.and_path_to(root, term) else {
                continue;
            };
            let mut unit = *state
                .units
                .entry(root)
                .or_insert_with(|| candidate.add_assume(root, None));
            for (gate, index, child) in path {
                let not_gate = self.ctx.terms.mk_not_raw(gate);
                let projection = candidate.add_rule_step(
                    AletheRule::AndPos(index),
                    vec![not_gate, child],
                    Vec::new(),
                    vec![gate],
                );
                unit = candidate.add_resolution(vec![child], gate, projection, unit);
            }
            return unit;
        }
        candidate.add_assume(term, None)
    }

    /// The strict derivation of one lemma unit.
    fn derive_expansion_lemma(&mut self, candidate: &mut Proof, lemma: &Lemma) -> ProofId {
        let term = lemma.term;
        match &lemma.kind {
            LemmaKind::ForallInst { values, .. } => candidate.add_rule_step(
                AletheRule::ForallInst,
                vec![term],
                Vec::new(),
                values.clone(),
            ),
            LemmaKind::Skolem { witness, .. } => {
                candidate.add_rule_step(AletheRule::Skolem, vec![term], Vec::new(), vec![*witness])
            }
            LemmaKind::NegatedExists { exists, dual } => {
                // (cl E F), then (cl (or E F)) by or_neg on each disjunct.
                let (exists, dual) = (*exists, *dual);
                let duality = candidate.add_rule_step(
                    AletheRule::QntNegExists,
                    vec![exists, dual],
                    Vec::new(),
                    Vec::new(),
                );
                let not_exists = self.ctx.terms.mk_not_raw(exists);
                let first = candidate.add_rule_step(
                    AletheRule::OrNeg,
                    vec![term, not_exists],
                    Vec::new(),
                    Vec::new(),
                );
                let half = candidate.add_resolution(vec![dual, term], exists, duality, first);
                let not_dual = self.ctx.terms.mk_not_raw(dual);
                let second = candidate.add_rule_step(
                    AletheRule::OrNeg,
                    vec![term, not_dual],
                    Vec::new(),
                    Vec::new(),
                );
                candidate.add_resolution(vec![term], dual, half, second)
            }
        }
    }
}
