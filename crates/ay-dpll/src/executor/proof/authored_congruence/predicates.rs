// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact authored predicate clauses, not Boolean model values or FP encodings.

use ay_core::{Proof, ProofId, Sort, Symbol, TermData, TermId, TheoryLemmaKind};
use ay_frontend::{CheckedProjectionBinding, ProjectionBindingRequest};

use super::Executor;
use crate::{UnknownOrigin, UnknownReason};

#[path = "predicates/boolean_clauses.rs"]
mod boolean_clauses;
#[path = "predicates/equality_evidence.rs"]
mod equality_evidence;
use equality_evidence::{EqualityEvidence, NanPremise};

// Local search envelopes, not additional solver configuration or authority.
const MAX_ROOTS: usize = 128;
const MAX_ARITY: usize = 16;
const MAX_IDENTITY_BYTES: usize = 256;
const MAX_WORK: usize = 4_096;
// A commit may also recheck a respelled proof; this caps attempts, not walks.
const MAX_COMMIT_ATTEMPTS: usize = 4;

#[derive(Debug, PartialEq, Eq)]
pub(super) enum Outcome {
    Declined,
    Stopped,
    Committed,
}

struct Pair {
    positive: TermId,
    negative: TermId,
    negative_atom: TermId,
    equalities: Vec<EqualityEvidence>,
    binding: CheckedProjectionBinding,
}

fn flat_sort(sort: &Sort) -> bool {
    matches!(
        sort,
        Sort::Bool | Sort::Int | Sort::Real | Sort::BitVec(_) | Sort::FloatingPoint(..)
    ) || matches!(sort, Sort::Uninterpreted(name) if name.len() <= MAX_IDENTITY_BYTES)
}

fn open(executor: &mut Executor) -> bool {
    // A recovered live flag/footprint cannot undo an already observed stop.
    !matches!(
        executor.last_unknown_reason.map(UnknownReason::origin),
        Some(
            UnknownOrigin::InterruptFlag
                | UnknownOrigin::SolveDeadline
                | UnknownOrigin::MemoryBudget
                | UnknownOrigin::DeterministicResourceBudget
        )
    ) && !executor.should_abort_theory_loop()
}

fn spend(work: &mut usize) -> Option<()> {
    charge(work, 1)
}

fn charge(work: &mut usize, amount: usize) -> Option<()> {
    // Exhaustion is sticky within this attempt, including a failed precharge.
    let Some(remaining) = work.checked_sub(amount) else {
        *work = 0;
        return None;
    };
    *work = remaining;
    Some(())
}

struct Attempt {
    work: usize,
    checks: usize,
}

impl Attempt {
    fn new() -> Self {
        Self {
            work: MAX_WORK,
            checks: 0,
        }
    }

    fn tick(&mut self, executor: &mut Executor) -> Option<()> {
        if !open(executor) {
            return None;
        }
        spend(&mut self.work)
    }
}

fn declined(executor: &mut Executor) -> Outcome {
    if open(executor) {
        Outcome::Declined
    } else {
        Outcome::Stopped
    }
}

impl Executor {
    pub(super) fn try_authored_predicate_congruence(
        &mut self,
        proof: &mut Proof,
        authored: &[TermId],
        equalities: &[(TermId, TermId, TermId)],
    ) -> Outcome {
        self.try_authored_predicate_with_attempt(proof, authored, equalities, &mut Attempt::new())
    }

    fn try_authored_predicate_with_attempt(
        &mut self,
        proof: &mut Proof,
        authored: &[TermId],
        equalities: &[(TermId, TermId, TermId)],
        attempt: &mut Attempt,
    ) -> Outcome {
        if !open(self) {
            return Outcome::Stopped;
        }
        if authored.len() > MAX_ROOTS || equalities.len() > MAX_ROOTS {
            return declined(self);
        }
        let Some(nans) = equality_evidence::collect(self, authored, attempt) else {
            return declined(self);
        };
        let mut positive = Vec::new();
        let mut negative = Vec::new();
        for &root in authored {
            if attempt.tick(self).is_none() {
                return declined(self);
            }
            if self.ctx.terms.sort(root) != &Sort::Bool {
                continue;
            }
            match self.ctx.terms.get(root) {
                TermData::App(_, _) => positive.push(root),
                TermData::Not(atom) => negative.push((root, *atom)),
                _ => {}
            }
        }
        if self
            .ctx
            .bounded_projection_declaration_inventory_size()
            .is_none()
        {
            return declined(self);
        }
        for positive in positive {
            for &(negative, atom) in &negative {
                let Some(()) = attempt.tick(self) else {
                    return declined(self);
                };
                let Some(pair) = self.authored_predicate_pair(
                    positive,
                    negative,
                    atom,
                    equalities,
                    &nans,
                    &mut attempt.work,
                ) else {
                    if attempt.work == 0 {
                        return declined(self);
                    }
                    continue;
                };
                let Some(candidate) = self.emit_authored_predicate_pair(&pair, &mut attempt.work)
                else {
                    return declined(self);
                };
                let outcome =
                    self.commit_predicate_candidate(proof, candidate, authored, &pair, attempt);
                if outcome != Outcome::Declined {
                    return outcome;
                }
                if attempt.work == 0 || attempt.checks == MAX_COMMIT_ATTEMPTS {
                    return declined(self);
                }
            }
        }
        self.try_authored_binary_predicates(proof, authored, equalities, &nans, attempt)
    }

    fn commit_predicate_candidate(
        &mut self,
        proof: &mut Proof,
        candidate: Proof,
        authored: &[TermId],
        pair: &Pair,
        attempt: &mut Attempt,
    ) -> Outcome {
        if attempt.checks == MAX_COMMIT_ATTEMPTS || attempt.tick(self).is_none() {
            return declined(self);
        }
        if !self.ctx.projection_binding_still_current(&pair.binding) {
            return declined(self);
        }
        attempt.checks += 1;
        // Strict replay and respelling remain opaque intervals under existing
        // proof controls. Never replace the caller's proof before the postpoll.
        let mut checked = Proof::new();
        let accepted = self.commit_if_strictly_checked(&mut checked, candidate, authored);
        if !open(self) {
            return Outcome::Stopped;
        }
        if accepted && self.ctx.projection_binding_still_current(&pair.binding) {
            *proof = checked;
            Outcome::Committed
        } else {
            declined(self)
        }
    }

    fn authored_predicate_pair(
        &self,
        positive: TermId,
        negative: TermId,
        negative_atom: TermId,
        authored_equalities: &[(TermId, TermId, TermId)],
        nans: &[NanPremise],
        work: &mut usize,
    ) -> Option<Pair> {
        let terms = &self.ctx.terms;
        let TermData::App(symbol @ Symbol::Named(name), left) = terms.get(positive) else {
            return None;
        };
        let TermData::App(other, right) = terms.get(negative_atom) else {
            return None;
        };
        if name.len() > MAX_IDENTITY_BYTES
            || symbol != other
            || left.is_empty()
            || left.len() > MAX_ARITY
            || left.len() != right.len()
            || terms.sort(positive) != &Sort::Bool
            || terms.sort(negative_atom) != &Sort::Bool
            || terms.sort(negative) != &Sort::Bool
            || !matches!(terms.get(negative), TermData::Not(inner) if *inner == negative_atom)
        {
            return None;
        }
        let mut equalities = Vec::new();
        let mut parameter_sorts = Vec::new();
        for (&left, &right) in left.iter().zip(right) {
            spend(work)?;
            if !flat_sort(terms.sort(left))
                || !flat_sort(terms.sort(right))
                || terms.sort(left) != terms.sort(right)
            {
                return None;
            }
            parameter_sorts.push(terms.sort(left).clone());
            if left == right {
                continue;
            }
            let mut premise = None;
            for &(root, a, b) in authored_equalities {
                spend(work)?;
                // Re-decode the exact structural equality, never fp.eq or a
                // producer-supplied endpoint annotation. The final checker
                // independently repeats position-by-position matching.
                if ((a == left && b == right) || (a == right && b == left))
                    && terms.sort(root) == &Sort::Bool
                    && super::decode_eq_local(terms, root) == Some((a, b))
                {
                    premise = Some(root);
                    break;
                }
            }
            let evidence = match premise {
                Some(root) => EqualityEvidence::Authored(root),
                None => equality_evidence::find_nan(nans, left, right, work)?,
            };
            equalities.push(evidence);
        }
        // An all-reflexive pair is already the same predicate term. Leave
        // that complementary-unit case to the existing Boolean proof path.
        if equalities.is_empty() {
            return None;
        }
        let binding = self
            .ctx
            .check_projection_declaration(&ProjectionBindingRequest {
                symbol: symbol.clone(),
                parameter_sorts,
                result_sort: Sort::Bool,
            })
            .ok()?;
        Some(Pair {
            positive,
            negative,
            negative_atom,
            equalities,
            binding,
        })
    }

    fn emit_predicate_implication(
        &mut self,
        pair: &Pair,
        left: TermId,
        right: TermId,
        proof: &mut Proof,
        work: &mut usize,
    ) -> Option<(Vec<TermId>, ProofId)> {
        // At most MAX_ARITY premises. This envelope covers every premise
        // visit, duplicate probe, clause copy/retain and emitted proof entry.
        // Precharge before any terms/steps are allocated; no checker work is
        // claimed by this local search envelope.
        let width = pair.equalities.len().checked_add(2)?;
        charge(work, width.checked_mul(width)?.checked_mul(4)?)?;
        let mut proven: Vec<(TermId, ProofId)> = Vec::new();
        let mut clause = Vec::new();
        for &evidence in &pair.equalities {
            let root = evidence.literal(self, work)?;
            if !proven.iter().any(|(term, _)| *term == root) {
                let step = evidence.emit(self, root, proof, work)?;
                proven.push((root, step));
            }
            // Keep repeated argument positions in the congruence schema,
            // while each distinct equality is proved/discharged just once.
            clause.push(self.ctx.terms.mk_not_raw(root));
        }
        let not_positive = self.ctx.terms.mk_not_raw(left);
        clause.extend([not_positive, right]);
        let mut current = proof.add_theory_lemma_with_kind(
            "euf",
            clause.clone(),
            TheoryLemmaKind::EufCongruentPred,
        );
        for (root, premise) in proven {
            let negated = self.ctx.terms.mk_not_raw(root);
            // The schema retains repeated argument-position premises, while
            // resolution operates on clause sets and removes every copy.
            clause.retain(|&literal| literal != negated);
            current = proof.add_resolution(clause.clone(), root, current, premise);
        }
        Some((clause, current))
    }

    fn emit_authored_predicate_pair(&mut self, pair: &Pair, work: &mut usize) -> Option<Proof> {
        let mut proof = Proof::new();
        let (_, mut current) = self.emit_predicate_implication(
            pair,
            pair.positive,
            pair.negative_atom,
            &mut proof,
            work,
        )?;
        charge(work, 8)?;
        let positive = proof.add_assume(pair.positive, None);
        current = proof.add_resolution(vec![pair.negative_atom], pair.positive, current, positive);
        let negative = proof.add_assume(pair.negative, None);
        proof.add_resolution(Vec::new(), pair.negative_atom, current, negative);
        Some(proof)
    }
}

#[cfg(test)]
#[path = "predicates/tests.rs"]
mod tests;
