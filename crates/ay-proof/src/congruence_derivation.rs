// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lower a packed EUF **congruence-closure explanation** to a derivation built
//! only from rules the strict checker validates and
//! [`ay_core::CHECKABLE_ALETHE_RULES`] carries — so the emitted document is
//! checkable by an external Alethe checker, not only by AY.
//!
//! # The clause, and what replaces it
//!
//! ```text
//! (cl (not (= a_1 b_1)) .. (not (= a_n b_n)) (= s t))
//! ```
//!
//! [`crate::checker`]'s `EufCongruenceExplanation` arm ACCEPTS this clause —
//! soundly, from nothing — but `euf_congruence_explanation` is not a pinned
//! Alethe rule, so `wire_rule_name` lowers it to `hole` and an external
//! checker learns nothing. This module replaces the single lemma with
//!
//! ```text
//!   eq_congruent   one per congruence link on the explanation path
//!   eq_reflexive   the identical argument positions its full arity needs
//!   eq_transitive  the path itself, conclusion LAST
//!   th_resolution  discharging each derived link against its own derivation
//!   weakening      re-introducing hypotheses the explanation never used
//!   reordering     restoring the recorded literal order
//! ```
//!
//! every one of which is in `CHECKABLE_ALETHE_RULES` and has a strict
//! validator in this crate.
//!
//! # Authority
//!
//! This module asserts NOTHING. `eq_congruent` and `eq_transitive` clauses are
//! premise-free tautologies whose validity is decided by the checker's own
//! `validate_euf_congruent` / `validate_euf_transitive` from the clause
//! structure alone; `th_resolution`, `weakening` and `reordering` are decided
//! from their premises. The caller re-runs the untouched strict checker over
//! the emitted fragment before it may replace anything, and a fragment that
//! does not check is DISCARDED, leaving the certified lemma byte-identical.
//!
//! Also `contraction`, when a tautology step legitimately repeats a premise.
//!
//! # Fail-closed by construction
//!
//! Every construction step is verified against the term store rather than
//! assumed: a built equality must decode back to the pair it was built for, a
//! built negation must decode back to its positive, and the finished clause
//! must be exactly the recorded literal multiset. Any mismatch returns
//! `None`, and the caller then keeps its certified lemma unchanged.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{AletheRule, ProofId, ProofStep, Sort, Symbol, TermData, TermId, TermStore};

use crate::congruence_forest::{CongruenceForest, MergeReason};

#[path = "congruence_derivation_clause.rs"]
mod clause;

use clause::{as_application, decode_eq, parse_clause, resolvent, Fact, Hypothesis};

/// Largest number of steps one lemma may be lowered to. A derivation needs
/// roughly two steps per congruence link, so this bounds an adversarial clause
/// without reaching any measured shape (the corpus maximum is far below it).
pub(crate) const MAX_DERIVATION_STEPS: usize = 512;

/// A derivation of one explanation clause.
pub struct CongruenceDerivation {
    /// The steps, with premise ids RELATIVE to the fragment (`ProofId(0)` is
    /// `steps[0]`). The caller offsets them by the position it splices them
    /// in at.
    pub steps: Vec<ProofStep>,
    /// The clause of the LAST step — byte-identical to the literals the
    /// caller passed in.
    pub clause: Vec<TermId>,
}

/// Emits the steps for one clause.
struct Emitter<'a> {
    terms: &'a mut TermStore,
    forest: &'a CongruenceForest,
    hypotheses: &'a [Hypothesis],
    steps: Vec<ProofStep>,
    /// Memo per forest edge, so a link shared by two positions is derived
    /// once. `None` marks an edge whose derivation is IN PROGRESS.
    facts: HashMap<usize, Option<Fact>>,
    /// Memo per reflexive argument term, so one `eq_reflexive` step serves
    /// every position that needs it.
    reflexives: HashMap<TermId, Fact>,
}

impl Emitter<'_> {
    /// Push a premise-free tautology step and return its index.
    fn push_leaf(&mut self, rule: AletheRule, clause: Vec<TermId>) -> Option<usize> {
        if self.steps.len() >= MAX_DERIVATION_STEPS {
            return None;
        }
        let id = self.steps.len();
        self.steps.push(ProofStep::Step {
            rule,
            clause,
            premises: Vec::new(),
            args: Vec::new(),
        });
        Some(id)
    }

    /// `(= lhs rhs)` as a RAW binary application, verified to decode back to
    /// exactly that pair.
    ///
    /// Deliberately NOT `mk_eq`: that builder folds a reflexive, Boolean,
    /// `to_real` or `store` equality into something that is not a binary `=`
    /// application at all, and the measured QF_AX population needs precisely
    /// the equality it rewrites — a congruence over `select` needs
    /// `(= (store A i v) A')` as an intermediate, which `mk_eq`'s self-store
    /// rule turns into `(= (select A i) v)`. Measured: 123 of 11717 corpus
    /// lemmas were declined for that reason alone before this changed.
    ///
    /// SAFE because the term lives only INSIDE the fragment: the emitter
    /// builds both this equality and its negation, resolves the pair away
    /// before the last step, and the last step's clause is checked against the
    /// recorded literals. The reflexive and sort guards keep the raw builder
    /// from minting a term `mk_eq` would have refused to build at all, and the
    /// decode check keeps a future builder change fail-closed.
    fn equality(&mut self, lhs: TermId, rhs: TermId) -> Option<TermId> {
        if lhs == rhs || self.terms.sort(lhs) != self.terms.sort(rhs) {
            return None;
        }
        let built = self
            .terms
            .mk_app(Symbol::named("="), [lhs, rhs], Sort::Bool);
        let (built_lhs, built_rhs) = decode_eq(self.terms, built)?;
        (built_lhs == lhs && built_rhs == rhs).then_some(built)
    }

    /// `eq_reflexive` for an argument position whose two terms are the same.
    ///
    /// The raw `(= x x)` never escapes the fragment: it is resolved away
    /// before the last step, whose clause is checked against the recorded
    /// literals. `mk_eq` cannot build it — it folds to `true` — which is why
    /// this, like the other intermediates, is a raw application.
    fn reflexivity(&mut self, term: TermId) -> Option<Fact> {
        if let Some(fact) = self.reflexives.get(&term) {
            return Some(fact.clone());
        }
        let positive = self
            .terms
            .mk_app(Symbol::named("="), [term, term], Sort::Bool);
        let (left, right) = decode_eq(self.terms, positive)?;
        if left != term || right != term {
            return None;
        }
        let negative = self.negation(positive)?;
        let step = self.push_leaf(AletheRule::EqReflexive, vec![positive])?;
        let fact = Fact::Derived {
            step,
            positive,
            negative,
            clause: vec![positive],
        };
        self.reflexives.insert(term, fact.clone());
        Some(fact)
    }

    /// `(not positive)` with an explicit `Not` wrapper, verified.
    fn negation(&mut self, positive: TermId) -> Option<TermId> {
        let built = self.terms.mk_not_raw(positive);
        matches!(self.terms.get(built), TermData::Not(inner) if *inner == positive).then_some(built)
    }

    /// Discharge each derived premise of `clause` against its own derivation.
    fn resolve_out(
        &mut self,
        step: usize,
        clause: Vec<TermId>,
        positive: TermId,
        derived: &[Fact],
    ) -> Option<Fact> {
        let mut step = step;
        let mut clause = clause;
        for fact in derived {
            let Fact::Derived {
                step: premise,
                positive: pivot,
                negative: pivot_negation,
                clause: premise_clause,
            } = fact
            else {
                continue;
            };
            let next = resolvent(&clause, premise_clause, *pivot, *pivot_negation);
            if self.steps.len() >= MAX_DERIVATION_STEPS {
                return None;
            }
            let id = self.steps.len();
            self.steps.push(ProofStep::Step {
                rule: AletheRule::ThResolution,
                clause: next.clone(),
                premises: vec![
                    ProofId(u32::try_from(step).ok()?),
                    ProofId(u32::try_from(*premise).ok()?),
                ],
                args: Vec::new(),
            });
            step = id;
            clause = next;
        }
        let negative = self.negation(positive)?;
        Some(Fact::Derived {
            step,
            positive,
            negative,
            clause,
        })
    }

    /// The fact for one forest edge, deriving and memoizing it on first use.
    fn edge_fact(&mut self, edge: usize) -> Option<Fact> {
        // A congruence edge's argument explanations only ever use edges
        // recorded EARLIER — the two children were already equal when the
        // merge fired, and a forest path never changes once it exists — so
        // this recursion terminates. The in-progress marker does not rely on
        // that argument: re-entering an edge would mean the invariant is
        // broken, and declining is the only safe answer to a proof forest that
        // is not a forest.
        match self.facts.get(&edge) {
            Some(Some(fact)) => return Some(fact.clone()),
            Some(None) => return None,
            None => self.facts.insert(edge, None),
        };
        let (left, right, reason) = *self.forest.edges.get(edge)?;
        let fact = match reason {
            MergeReason::Hypothesis(index) => Fact::Stated {
                literal: self.hypotheses.get(index)?.literal,
            },
            MergeReason::Congruence => {
                let conclusion = self.equality(self.forest.term[left], self.forest.term[right])?;
                self.congruence(left, right, conclusion)?
            }
        };
        self.facts.insert(edge, Some(fact.clone()));
        Some(fact)
    }

    /// `eq_congruent` over the two nodes' argument positions, then the
    /// resolutions that discharge each derived argument equality.
    ///
    /// `conclusion` is supplied by the caller so the TOP-level step can carry
    /// the clause's own recorded positive literal verbatim.
    fn congruence(&mut self, left: usize, right: usize, conclusion: TermId) -> Option<Fact> {
        let (left_symbol, left_args) = as_application(self.terms, self.forest.term[left])?;
        let (right_symbol, right_args) = as_application(self.terms, self.forest.term[right])?;
        if left_symbol != right_symbol
            || left_args.len() != right_args.len()
            || left_args.is_empty()
        {
            return None;
        }
        let mut premises = Vec::with_capacity(left_args.len());
        let mut derived: Vec<Fact> = Vec::new();
        for (&left_arg, &right_arg) in left_args.iter().zip(right_args.iter()) {
            // ONE hypothesis per argument position, including the identical
            // ones. `validate_euf_congruent` tolerates an omitted reflexive
            // position, but the Alethe rule is stated over EVERY position and
            // the printer's surface bridge requires the full arity, so the
            // spec-exact form is what an external checker gets. The reflexive
            // hypothesis is discharged by `eq_reflexive` below, exactly as
            // `split_euf_congruence_lemmas` does.
            let fact = if left_arg == right_arg {
                self.reflexivity(left_arg)?
            } else {
                self.derive(left_arg, right_arg)?
            };
            premises.push(fact.literal());
            if let Fact::Derived { positive, .. } = &fact {
                // A chain shared by two positions is resolved ONCE: the pivot
                // is gone from the accumulator after the first resolution.
                if !derived.iter().any(|other| {
                    matches!(other, Fact::Derived { positive: seen, .. } if seen == positive)
                }) {
                    derived.push(fact);
                }
            }
        }
        let mut clause = premises;
        clause.push(conclusion);
        let step = self.push_leaf(AletheRule::EqCongruent, clause.clone())?;
        self.resolve_out(step, clause, conclusion, &derived)
    }

    /// `eq_transitive` over the explanation path, then its resolutions.
    fn transitivity(&mut self, path: &[usize], conclusion: TermId) -> Option<Fact> {
        let mut clause = Vec::with_capacity(path.len() + 1);
        let mut derived: Vec<Fact> = Vec::new();
        for &edge in path {
            let fact = self.edge_fact(edge)?;
            clause.push(fact.literal());
            if let Fact::Derived { positive, .. } = &fact {
                if !derived.iter().any(|other| {
                    matches!(other, Fact::Derived { positive: seen, .. } if seen == positive)
                }) {
                    derived.push(fact);
                }
            }
        }
        clause.push(conclusion);
        let step = self.push_leaf(AletheRule::EqTransitive, clause.clone())?;
        self.resolve_out(step, clause, conclusion, &derived)
    }

    /// Derive `(= lhs rhs)` from the explanation path between them.
    fn derive(&mut self, lhs: TermId, rhs: TermId) -> Option<Fact> {
        let path = self
            .forest
            .explain(self.forest.node_of(lhs)?, self.forest.node_of(rhs)?)?;
        match path.as_slice() {
            [] => None,
            [edge] => self.edge_fact(*edge),
            path => {
                let conclusion = self.equality(lhs, rhs)?;
                self.transitivity(path, conclusion)
            }
        }
    }

    /// Derive the clause's own positive literal, whose recorded spelling the
    /// top step carries verbatim.
    fn derive_goal(&mut self, lhs: TermId, rhs: TermId, literal: TermId) -> Option<Fact> {
        let path = self
            .forest
            .explain(self.forest.node_of(lhs)?, self.forest.node_of(rhs)?)?;
        match path.as_slice() {
            // An empty path means `s` and `t` are the same term and a
            // one-edge HYPOTHESIS path means the clause carries both `(= s t)`
            // and its negation: propositional tautologies, not congruence
            // explanations, and already owned by earlier recognizers.
            [] => None,
            [edge] => {
                let (left, right, reason) = *self.forest.edges.get(*edge)?;
                match reason {
                    MergeReason::Hypothesis(_) => None,
                    MergeReason::Congruence => self.congruence(left, right, literal),
                }
            }
            path => self.transitivity(path, literal),
        }
    }
}

/// Plan a derivation of one congruence-closure explanation clause, or `None`
/// when it cannot be extracted (the caller then keeps its certified lemma).
///
/// `literals` must be the FLAT literal list; the caller unpacks a
/// `(cl (or ..))` unit itself, because reconnecting the packed form is its
/// consumer's business, not this planner's.
#[must_use]
pub fn plan_euf_congruence_derivation(
    terms: &mut TermStore,
    literals: &[TermId],
) -> Option<CongruenceDerivation> {
    let (mut steps, step, clause) = plan_core(terms, literals)?;
    finish(&mut steps, step, clause, literals)
}

/// The literals a derivation of `literals`'s goal ACTUALLY cites — the goal
/// plus exactly the hypotheses some emitted step depends on, before
/// [`finish`] weakens the result back to every recorded hypothesis.
///
/// Used by [`crate::definition_bridge`] to MINIMISE a bridge clause: it offers
/// the whole authored equality scope as candidate hypotheses and needs to know
/// which of them the explanation actually used, so the emitted clause carries
/// those and no others. Sharing `plan_core` with the planner above is what
/// keeps the two answers from drifting.
#[must_use]
pub(crate) fn essential_clause(terms: &mut TermStore, literals: &[TermId]) -> Option<Vec<TermId>> {
    plan_core(terms, literals).map(|(_, _, clause)| clause)
}

/// The shared half: build the forest, derive the goal, and return the emitted
/// steps together with the index and clause of the step that derives it.
fn plan_core(
    terms: &mut TermStore,
    literals: &[TermId],
) -> Option<(Vec<ProofStep>, usize, Vec<TermId>)> {
    let (hypotheses, goal_literal, goal_lhs, goal_rhs) = parse_clause(terms, literals)?;
    let mut forest = CongruenceForest::new();
    forest.add(terms, goal_lhs)?;
    forest.add(terms, goal_rhs)?;
    let mut endpoints = Vec::with_capacity(hypotheses.len());
    for hypothesis in &hypotheses {
        endpoints.push((
            forest.add(terms, hypothesis.lhs)?,
            forest.add(terms, hypothesis.rhs)?,
        ));
    }
    for (index, (lhs, rhs)) in endpoints.into_iter().enumerate() {
        forest.merge(lhs, rhs, MergeReason::Hypothesis(index));
    }
    if !forest.close() {
        return None;
    }
    let mut emitter = Emitter {
        terms,
        forest: &forest,
        hypotheses: &hypotheses,
        steps: Vec::new(),
        facts: HashMap::default(),
        reflexives: HashMap::default(),
    };
    let fact = emitter.derive_goal(goal_lhs, goal_rhs, goal_literal)?;
    let Fact::Derived { step, clause, .. } = fact else {
        return None;
    };
    Some((emitter.steps, step, clause))
}

#[path = "congruence_derivation_assembly.rs"]
mod assembly;

use assembly::finish;
pub use assembly::{close_congruence_derivation, congruence_derivation_renders};

#[cfg(test)]
#[path = "congruence_derivation_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "congruence_derivation_sweep_tests.rs"]
pub(crate) mod sweep_tests;
