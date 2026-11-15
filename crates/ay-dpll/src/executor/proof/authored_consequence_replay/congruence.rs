// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Congruence derivation for planned ground equalities
//! (`ConsequencePlan::CongruenceEquality`, #exists-bridge-chain).
//!
//! A planned equality `(= L R)` is derived structurally: `refl` at
//! identical sides, otherwise one `cong` step whose premises are the
//! argument equalities — each itself an authored/planned unit
//! (`consequence_unit`, either orientation) or recursively congruent.
//! The recursion descends the term DAG, so it terminates; a depth cap
//! bounds pathological nesting. Every step is re-derived by the strict
//! `cong`/`refl` validators, which check the head, arity, and that every
//! differing argument position is discharged by a premise equality.

use super::*;

/// Recursion cap for nested congruence derivations.
const MAX_CONGRUENCE_DEPTH: u32 = 8;

impl Executor {
    /// Derive `(cl equality)` for a planned congruence equality.
    pub(super) fn add_congruence_equality_unit(
        &mut self,
        candidate: &mut Proof,
        equality: TermId,
        scope: &mut ConsequenceScope<'_>,
    ) -> Option<ProofId> {
        let (lhs, rhs) = self.decode_equality(equality)?;
        self.derive_equality_pair(candidate, lhs, rhs, equality, scope, 0)
    }

    /// The two sides of an `(= L R)` application, or `None`.
    fn decode_equality(&self, term: TermId) -> Option<(TermId, TermId)> {
        match self.ctx.terms.get(term) {
            TermData::App(symbol, args) if symbol.name() == "=" && args.len() == 2 => {
                Some((args[0], args[1]))
            }
            _ => None,
        }
    }

    /// Derive `(cl target)` where `target` is `(= lhs rhs)`, by `refl` or
    /// a `cong` step over recursively derived argument equalities.
    fn derive_equality_pair(
        &mut self,
        candidate: &mut Proof,
        lhs: TermId,
        rhs: TermId,
        target: TermId,
        scope: &mut ConsequenceScope<'_>,
        depth: u32,
    ) -> Option<ProofId> {
        if depth > MAX_CONGRUENCE_DEPTH || self.ctx.terms.sort(lhs) != self.ctx.terms.sort(rhs) {
            return None;
        }
        if lhs == rhs {
            return Some(candidate.add_rule_step(
                AletheRule::Refl,
                vec![target],
                Vec::new(),
                Vec::new(),
            ));
        }
        let (lhead, largs) = self.application_parts(lhs)?;
        let (rhead, rargs) = self.application_parts(rhs)?;
        if lhead != rhead || largs.len() != rargs.len() {
            return None;
        }
        let mut premises: Vec<ProofId> = Vec::new();
        for (&a, &b) in largs.iter().zip(&rargs) {
            if a == b {
                continue;
            }
            premises.push(self.derive_argument_equality(candidate, a, b, scope, depth)?);
        }
        if premises.is_empty() {
            return None;
        }
        Some(candidate.add_rule_step(AletheRule::Cong, vec![target], premises, Vec::new()))
    }

    /// Derive `(cl (= a b))` for one differing argument position: an
    /// authored/planned unit in either orientation if one exists, else a
    /// recursive congruence derivation.
    fn derive_argument_equality(
        &mut self,
        candidate: &mut Proof,
        a: TermId,
        b: TermId,
        scope: &mut ConsequenceScope<'_>,
        depth: u32,
    ) -> Option<ProofId> {
        let forward = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [a, b], Sort::Bool);
        if let Some(unit) = self.consequence_unit(
            candidate,
            forward,
            scope.authored_set,
            scope.authored,
            scope.instance_plan,
            scope.unit_ids,
        ) {
            return Some(unit);
        }
        let flipped = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [b, a], Sort::Bool);
        if flipped != forward {
            // The `cong` validator accepts either orientation per premise.
            if let Some(unit) = self.consequence_unit(
                candidate,
                flipped,
                scope.authored_set,
                scope.authored,
                scope.instance_plan,
                scope.unit_ids,
            ) {
                return Some(unit);
            }
        }
        self.derive_equality_pair(candidate, a, b, forward, scope, depth + 1)
    }

    /// Head symbol and arguments of a congruence-admissible application,
    /// mirroring the strict `cong` validator (`App`, `Ite`, `Not`).
    fn application_parts(&self, term: TermId) -> Option<(CongruenceHead, Vec<TermId>)> {
        match self.ctx.terms.get(term).clone() {
            TermData::App(symbol, args) => Some((CongruenceHead::App(symbol), args)),
            TermData::Ite(condition, then_branch, else_branch) => Some((
                CongruenceHead::Ite,
                vec![condition, then_branch, else_branch],
            )),
            TermData::Not(inner) => Some((CongruenceHead::Not, vec![inner])),
            _ => None,
        }
    }
}

#[derive(PartialEq, Eq)]
enum CongruenceHead {
    App(Symbol),
    Ite,
    Not,
}
