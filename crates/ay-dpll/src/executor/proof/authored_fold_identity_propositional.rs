// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A raw authored refutation through Boolean structure: complementary literals,
//! constants, and intrinsic ITE branch projections under actual derived guard
//! facts, reached through `and`, `or`, implication and their negations.
//!
//! ## The class, as measured
//!
//! The complement argument of the parent module walks the `and`-spine only.
//! The elaborator's folds do not stop there: `mk_or` drops `false` disjuncts
//! and collapses a unary `or` onto its operand, `mk_and` drops `true`
//! conjuncts, and the complement scan then folds the whole root to `false`.
//! Measured on 2026-10-06 (Trust's in-process lane and the SMT-LIB text lane
//! agree): `(or (and (<= a b) (not (<= a b))))`,
//! `(or (and (<= a b) (and true (not (<= a b)))) false)`,
//! `(not (or (not (<= a b)) (and true (<= a b))))` and
//! `(and (<= a b) (or (and true (not (<= a b)))))` all answered
//! `unknown (incomplete self-check-rejected)` — every rescue declined, the
//! proof was erased to the bare hole, and mandatory strict certification
//! withheld a correct `unsat`. Over Bool atoms the bounded BV/LIA interpreter
//! closes the same shapes by evaluation; over Int atoms nothing did.
//!
//! ## The derivation
//!
//! A refutation of `T` from a derived clause `(cl T S..)` that leaves
//! `(cl S..)`, by cases on `T`:
//!
//! * a literal whose complement is a FACT already derived on this branch:
//!   one resolution;
//! * `false`: resolve against the `false` axiom `(cl (not false))`;
//!   `(not true)`: against the `true` axiom `(cl true)`;
//! * `(and c..)`: `and_pos` projects every conjunct to `(cl c_i S..)`; each
//!   becomes a fact, and the first conjunct that is itself refutable closes
//!   the branch;
//! * `(not (or d..))`: `or_neg` projects every `(not d_i)` the same way
//!   (the complement of a `(not a)` disjunct is `a`, the IR's compact form);
//! * `(or d..)`: `or_pos` gives `(cl d.. S..)`, and the disjuncts are
//!   refuted IN TURN, each with the remaining ones as side literals;
//! * `(not (and c..))`: `and_neg` gives `(cl (not c).. S..)`, refuted in
//!   turn the same way.
//! * `(=> a b)`: `implies_pos` gives `(cl (not a) b S..)`, refuted in turn;
//! * `(not (=> a b))`: `implies_neg1` and `implies_neg2` project `a` and
//!   `(not b)` as branch facts.
//! * a disequality to an ITE branch: the existing checked
//!   `IteBranchProjection` lemma and two resolutions close it ONLY when the
//!   corresponding guard is a derived fact on this branch. Scalar values and
//!   uninterpreted applications are never evaluated or assigned meanings.
//!
//! A fact carries the side literals of the branch that derived it, which are
//! always a subset of the current branch's (inner branches only ADD side
//! literals), so a closing resolution leaves exactly the current side. Every
//! rule is a standard Alethe rule AY's strict checker re-derives structurally
//! (`validate_and_pos`, `validate_or_pos`, `validate_or_neg`,
//! `validate_and_neg`, the Boolean-constant tautology check) and resolution
//! is checked as a set operation.
//!
//! ## What keeps this honest
//!
//! The pass only BUILDS a candidate. The parent's gates commit it: the
//! single `assume` is the author's own assertion re-interned raw and printed
//! back as authored, the UNCHANGED strict checker must accept the whole
//! candidate as complete, the exporter's premise-scope authority check must
//! accept its `assume`, and the exporter itself must render it. A wrong step
//! here is refused there (pinned by
//! `a_planted_propositional_refutation_of_a_satisfiable_root_is_refused`).

use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, ProofId, Symbol, TermId, TermStore};

/// Proof-building steps one root's refutation may take. The search is
/// exponential in the alternation of `and` over `or`; this bound keeps a
/// pathological root a decline instead of a stall.
const MAX_PROPOSITIONAL_REFUTATION_STEPS: usize = 4_096;

/// A derived clause: the step that concludes it and its literals.
#[derive(Clone)]
struct Derived {
    id: ProofId,
    clause: Vec<TermId>,
}

struct Refuter<'a> {
    terms: &'a mut TermStore,
    proof: &'a mut Proof,
    /// Literal facts on the current branch, innermost last.
    facts: Vec<(TermId, Derived)>,
    budget: usize,
}

/// Build the propositional refutation of `root` into `candidate`, whose step
/// `assume` concludes `(cl root)`. `Some(())` when the empty clause was
/// derived; `None` leaves `candidate` partially built and must be discarded.
pub(super) fn refute_root(
    terms: &mut TermStore,
    candidate: &mut Proof,
    assume: ProofId,
    root: TermId,
) -> Option<()> {
    let mut refuter = Refuter {
        terms,
        proof: candidate,
        facts: Vec::new(),
        budget: MAX_PROPOSITIONAL_REFUTATION_STEPS,
    };
    let unit = Derived {
        id: assume,
        clause: vec![root],
    };
    let closed = refuter.refute(root, &unit)?;
    closed.clause.is_empty().then_some(())
}

/// The literals of `clause` other than `term`, in order. `None` unless
/// `term` occurs exactly once (the side bookkeeping below needs that).
fn side_of(clause: &[TermId], term: TermId) -> Option<Vec<TermId>> {
    (clause.iter().filter(|&&literal| literal == term).count() == 1).then(|| {
        clause
            .iter()
            .copied()
            .filter(|&literal| literal != term)
            .collect()
    })
}

fn same_set(left: &[TermId], right: &[TermId]) -> bool {
    left.iter().all(|literal| right.contains(literal))
        && right.iter().all(|literal| left.contains(literal))
}

impl Refuter<'_> {
    /// The complement of `term` in the proof IR's compact convention: the
    /// operand of a negation, a raw `not` otherwise. The strict `or_neg` and
    /// `and_neg` validators accept exactly this one double-negation
    /// cancellation (`matches_negation_of_term`), and the Alethe printer
    /// expands it with `not_not`; a raw `(not (not a))` would instead be a
    /// literal no fact on this branch can resolve against.
    fn complement(&mut self, term: TermId) -> TermId {
        match self.terms.get(term) {
            TermData::Not(inner) => *inner,
            _ => self.terms.mk_not_raw(term),
        }
    }

    fn spend(&mut self) -> Option<()> {
        self.budget = self.budget.checked_sub(1)?;
        Some(())
    }

    /// Resolve `negative` (carrying `(not pivot)`) against `positive`
    /// (carrying `pivot`); the conclusion is the order-preserving,
    /// duplicate-free union of what remains.
    fn resolve(&mut self, negative: &Derived, positive: &Derived, pivot: TermId) -> Derived {
        let not_pivot = self.terms.mk_not_raw(pivot);
        let mut clause: Vec<TermId> = Vec::new();
        for &literal in negative
            .clause
            .iter()
            .filter(|&&literal| literal != not_pivot)
        {
            if !clause.contains(&literal) {
                clause.push(literal);
            }
        }
        for &literal in positive.clause.iter().filter(|&&literal| literal != pivot) {
            if !clause.contains(&literal) {
                clause.push(literal);
            }
        }
        let id = self
            .proof
            .add_resolution(clause.clone(), pivot, negative.id, positive.id);
        Derived { id, clause }
    }

    /// Refute negated structure and selected ITE equalities by checked rules.
    fn refute_negated(
        &mut self,
        inner: TermId,
        derived: &Derived,
        side: &[TermId],
    ) -> Option<Derived> {
        if let Some(closed) = self.refute_selected_ite(inner, derived, side) {
            return Some(closed);
        }
        match self.terms.get(inner).clone() {
            TermData::App(Symbol::Named(name), args) if name == "=>" && args.len() == 2 => {
                self.project_negated_implication(inner, &args, derived)
            }
            TermData::App(Symbol::Named(name), args) if name == "or" && !args.is_empty() => {
                let mut children = Vec::with_capacity(args.len());
                for &disjunct in &args {
                    self.spend()?;
                    let complement = self.complement(disjunct);
                    let tautology = Derived {
                        id: self.proof.add_rule_step(
                            AletheRule::OrNeg,
                            vec![inner, complement],
                            Vec::new(),
                            vec![inner],
                        ),
                        clause: vec![inner, complement],
                    };
                    children.push((complement, self.resolve(derived, &tautology, inner)));
                }
                self.refute_some_fact(children)
            }
            TermData::App(Symbol::Named(name), args) if name == "and" && !args.is_empty() => {
                let negations: Vec<TermId> = args
                    .iter()
                    .map(|&conjunct| self.complement(conjunct))
                    .collect();
                let mut clause = vec![inner];
                clause.extend(negations.iter().copied());
                let tautology = Derived {
                    id: self.proof.add_rule_step(
                        AletheRule::AndNeg,
                        clause.clone(),
                        Vec::new(),
                        vec![inner],
                    ),
                    clause,
                };
                let split = self.resolve(derived, &tautology, inner);
                self.refute_every_literal(&negations, split, side)
            }
            _ => None,
        }
    }

    /// From `derived : (cl T S..)`, derive `(cl S..)`.
    fn refute(&mut self, term: TermId, derived: &Derived) -> Option<Derived> {
        self.spend()?;
        let side = side_of(&derived.clause, term)?;
        let not_term = self.terms.mk_not_raw(term);
        let negated_atom = match self.terms.get(term) {
            TermData::Not(inner) => Some(*inner),
            _ => None,
        };

        // A complementary fact on this branch.
        let complement = self.facts.iter().rev().find_map(|(literal, fact)| {
            if *literal == not_term {
                Some((fact.clone(), true))
            } else if Some(*literal) == negated_atom {
                Some((fact.clone(), false))
            } else {
                None
            }
        });
        if let Some((fact, fact_is_negative)) = complement {
            let closed = if fact_is_negative {
                self.resolve(&fact, derived, term)
            } else {
                let atom = negated_atom?;
                self.resolve(derived, &fact, atom)
            };
            return same_set(&closed.clause, &side).then_some(closed);
        }

        let false_term = self.terms.false_term();
        let true_term = self.terms.true_term();
        if term == false_term {
            let not_false = self.terms.mk_not_raw(false_term);
            let axiom = Derived {
                id: self.proof.add_rule_step(
                    AletheRule::False,
                    vec![not_false],
                    Vec::new(),
                    Vec::new(),
                ),
                clause: vec![not_false],
            };
            return Some(self.resolve(&axiom, derived, false_term));
        }
        if negated_atom == Some(true_term) {
            let axiom = Derived {
                id: self.proof.add_rule_step(
                    AletheRule::True,
                    vec![true_term],
                    Vec::new(),
                    Vec::new(),
                ),
                clause: vec![true_term],
            };
            return Some(self.resolve(derived, &axiom, true_term));
        }

        match self.terms.get(term).clone() {
            TermData::App(Symbol::Named(name), args) if name == "and" && !args.is_empty() => {
                let mut children = Vec::with_capacity(args.len());
                for (index, &child) in args.iter().enumerate() {
                    self.spend()?;
                    let position = u32::try_from(index).ok()?;
                    let tautology = Derived {
                        id: self.proof.add_rule_step(
                            AletheRule::AndPos(position),
                            vec![not_term, child],
                            Vec::new(),
                            vec![term],
                        ),
                        clause: vec![not_term, child],
                    };
                    children.push((child, self.resolve(&tautology, derived, term)));
                }
                self.refute_some_fact(children)
            }
            TermData::App(Symbol::Named(name), args) if name == "or" && !args.is_empty() => {
                let mut clause = vec![not_term];
                clause.extend(args.iter().copied());
                let tautology = Derived {
                    id: self.proof.add_rule_step(
                        AletheRule::OrPos(0),
                        clause.clone(),
                        Vec::new(),
                        vec![term],
                    ),
                    clause,
                };
                let split = self.resolve(&tautology, derived, term);
                self.refute_every_literal(&args, split, &side)
            }
            TermData::Not(inner) => self.refute_negated(inner, derived, &side),
            TermData::App(Symbol::Named(name), args) if name == "=>" && args.len() == 2 => {
                self.split_implication(term, &args, derived, &side)
            }
            _ => None,
        }
    }

    fn split_implication(
        &mut self,
        term: TermId,
        args: &[TermId],
        derived: &Derived,
        side: &[TermId],
    ) -> Option<Derived> {
        let literals = [self.complement(args[0]), args[1]];
        let clause = vec![self.terms.mk_not_raw(term), literals[0], literals[1]];
        let tautology = Derived {
            id: self.proof.add_rule_step(
                AletheRule::ImpliesPos,
                clause.clone(),
                Vec::new(),
                Vec::new(),
            ),
            clause,
        };
        let split = self.resolve(&tautology, derived, term);
        self.refute_every_literal(&literals, split, side)
    }

    fn project_negated_implication(
        &mut self,
        term: TermId,
        args: &[TermId],
        derived: &Derived,
    ) -> Option<Derived> {
        let projections = [
            (AletheRule::ImpliesNeg1, args[0]),
            (AletheRule::ImpliesNeg2, self.complement(args[1])),
        ];
        let mut children = Vec::with_capacity(projections.len());
        for (rule, literal) in projections {
            self.spend()?;
            let clause = vec![term, literal];
            let tautology = Derived {
                id: self
                    .proof
                    .add_rule_step(rule, clause.clone(), Vec::new(), Vec::new()),
                clause,
            };
            children.push((literal, self.resolve(derived, &tautology, term)));
        }
        self.refute_some_fact(children)
    }

    /// Record every projected child as a fact of this branch, then close the
    /// branch through the first child that is itself refutable. Facts are
    /// scoped: whatever this branch added is gone when it returns.
    fn refute_some_fact(&mut self, children: Vec<(TermId, Derived)>) -> Option<Derived> {
        let scope = self.facts.len();
        self.facts.extend(children.iter().cloned());
        let mut closed = None;
        for (child, derived) in &children {
            if let Some(result) = self.refute(*child, derived) {
                closed = Some(result);
                break;
            }
        }
        self.facts.truncate(scope);
        closed
    }

    /// From `split : (cl l_1 .. l_k S..)`, refute every `l_i` in turn, each
    /// with the not-yet-refuted ones as side literals, leaving `(cl S..)`.
    fn refute_every_literal(
        &mut self,
        literals: &[TermId],
        split: Derived,
        side: &[TermId],
    ) -> Option<Derived> {
        // Distinct literals, none of them already a side literal: otherwise
        // removing one would also remove a literal the branch must keep.
        for (index, literal) in literals.iter().enumerate() {
            if side.contains(literal) || literals[..index].contains(literal) {
                return None;
            }
        }
        let mut current = split;
        for &literal in literals {
            current = self.refute(literal, &current)?;
        }
        same_set(&current.clause, side).then_some(current)
    }
}

#[path = "authored_fold_ite_projection.rs"]
mod ite_projection;

#[cfg(test)]
#[path = "authored_fold_implication_tests.rs"]
mod implication_tests;
