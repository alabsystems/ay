// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact authored polynomial-identity refutation.
//!
//! Arithmetic normalization can replace an authored `not (= lhs rhs)` with a
//! solver-visible normal form.  A SAT proof for that replacement is not, by
//! itself, a derivation from the authored assertion.  This lane instead builds
//! the complete two-leaf proof from the frozen source scope: the authored
//! negation is an assumption, the positive equality is independently checked
//! as an exact polynomial identity, and resolution derives the empty clause.

use super::*;

const MAX_AUTHORED_POLY_ROOTS: usize = 128;
// Each exact polynomial recognizer has its own bounded but deliberately large
// normalization budget. Do not reset that budget for every authored root: a
// hostile source scope can otherwise multiply the local limit by 128. This
// repair is a completeness-only fallback, so a small shared attempt cap is the
// fail-closed way to bound aggregate normalization work.
const MAX_AUTHORED_POLY_RECOGNIZER_ATTEMPTS: usize = 8;

impl Executor {
    pub(super) fn replace_with_exact_authored_poly_refutation(
        &mut self,
        proof: &mut Proof,
        entry: RepairEntry,
    ) {
        let Some(authored) = self.bounded_authored_poly_scope() else {
            return;
        };
        // Admit the exact cheap source shape before walking the provisional
        // proof.  This member is present in the generic cascade, so an unrelated
        // large proof must not pay a full wire/strict publication check merely
        // because it has an authored assertion stack.
        let identities: Vec<(TermId, TermId)> = authored
            .iter()
            .filter_map(|&assertion| {
                self.authored_poly_identity_candidate(assertion)
                    .map(|identity| (assertion, identity))
            })
            .take(MAX_AUTHORED_POLY_RECOGNIZER_ATTEMPTS)
            .collect();
        if identities.is_empty() {
            return;
        }
        // A semantically revalidated Generic arithmetic lemma can make the
        // native proof strict-complete while still printing as an honest Alethe
        // `hole`. This authored lane is a presentation repair, so only a proof
        // that is both strict-complete and wire-clean may suppress it.
        if entry == RepairEntry::Check && self.authored_cascade_publishable(proof) {
            return;
        }

        for (assertion, identity) in identities {
            let clause = [identity];
            if !ay_proof::recognize_arith_poly_simp(&self.ctx.terms, &clause)
                || !ay_proof::recognize_arith_clause_tautology(&self.ctx.terms, &clause)
            {
                continue;
            }

            let mut candidate = Proof::new();
            // Keep this unnamed: the shared authored-surface commit rebuilds
            // the proof positionally and deliberately refuses to discard a
            // named-step table. It then re-interns the frozen source spelling
            // and moves the assume, lemma, pivot, and resolution onto that
            // exact raw DAG together, so the checked `poly_simp` clause stays
            // byte-identical to what the Alethe printer emits.
            let assumption = candidate.add_assume(assertion, None);
            let lemma = candidate.add_theory_lemma_with_kind(
                "arith",
                clause.to_vec(),
                TheoryLemmaKind::ArithClauseTautology,
            );
            candidate.add_resolution(Vec::new(), identity, assumption, lemma);

            if self.commit_if_strictly_checked(proof, candidate, &authored) {
                return;
            }
        }
    }

    fn authored_poly_identity_candidate(&self, assertion: TermId) -> Option<TermId> {
        let TermData::Not(identity) = self.ctx.terms.get(assertion) else {
            return None;
        };
        let identity = *identity;
        let TermData::App(Symbol::Named(operator), arguments) = self.ctx.terms.get(identity) else {
            return None;
        };
        let [left, right] = arguments.as_slice() else {
            return None;
        };
        let sort = self.ctx.terms.sort(*left);
        (operator == "="
            && self.ctx.terms.sort(identity) == &Sort::Bool
            && self.ctx.terms.sort(*right) == sort
            && matches!(sort, Sort::Int | Sort::Real))
        .then_some(identity)
    }

    /// Collect only the source-aligned authored scope after cardinality is
    /// known to fit. `exact_concrete_authored_scope` clones the complete source
    /// ledger before its caller can inspect the length, which defeats this
    /// lane's root cap on a hostile assertion/assumption stack.
    fn bounded_authored_poly_scope(&self) -> Option<Vec<TermId>> {
        let source = self.proof_original_problem_assertions_slice();
        let assumptions = self.last_assumptions.as_deref().unwrap_or(&[]);
        let supplied_roots = source.len().checked_add(assumptions.len())?;
        if supplied_roots > MAX_AUTHORED_POLY_ROOTS {
            return None;
        }

        let mut seen = ay_core::kani_compat::DetHashSet::default();
        let mut authored = Vec::with_capacity(supplied_roots);
        for &term in source.iter().chain(assumptions) {
            if seen.insert(term) {
                authored.push(term);
            }
        }
        Some(authored)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn executor_with_false_poly_candidates_before_valid(count: usize) -> Executor {
        let mut executor = Executor::new();
        let x = executor.ctx.terms.mk_var("poly_attempt_x", Sort::Int);
        let zero = executor.ctx.terms.mk_int(BigInt::from(0));
        let mut assumptions = Vec::with_capacity(count + 1);
        for index in 0..count {
            let value = executor
                .ctx
                .terms
                .mk_int(BigInt::from(index.saturating_add(1)));
            let false_identity = executor.ctx.terms.mk_eq(x, value);
            assumptions.push(executor.ctx.terms.mk_not_raw(false_identity));
        }
        let x_plus_zero = executor
            .ctx
            .terms
            .mk_app(Symbol::named("+"), [x, zero], Sort::Int);
        let identity = executor.ctx.terms.mk_eq(x_plus_zero, x);
        assumptions.push(executor.ctx.terms.mk_not_raw(identity));
        executor.last_assumptions = Some(assumptions);
        executor
    }

    fn trust_proof() -> Proof {
        let mut proof = Proof::new();
        proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
        proof
    }

    #[test]
    fn authored_poly_recognizer_attempt_boundary_reaches_valid_identity() {
        let mut executor = executor_with_false_poly_candidates_before_valid(
            MAX_AUTHORED_POLY_RECOGNIZER_ATTEMPTS - 1,
        );
        let mut proof = trust_proof();

        executor.replace_with_exact_authored_poly_refutation(&mut proof, RepairEntry::Check);

        assert!(Executor::proof_derives_empty_clause(&proof));
        assert!(executor.check_proof_strict_with_datatypes(&proof).is_ok());
        assert!(!proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::Trust,
                ..
            }
        )));
    }

    #[test]
    fn authored_poly_recognizer_attempt_over_boundary_declines() {
        let mut executor =
            executor_with_false_poly_candidates_before_valid(MAX_AUTHORED_POLY_RECOGNIZER_ATTEMPTS);
        let mut proof = trust_proof();

        executor.replace_with_exact_authored_poly_refutation(&mut proof, RepairEntry::Check);

        assert!(matches!(
            proof.steps.as_slice(),
            [ProofStep::Step {
                rule: AletheRule::Trust,
                ..
            }]
        ));
    }

    #[test]
    fn authored_scope_above_cap_declines_before_whole_ledger_clone() {
        let mut executor = Executor::new();
        let x = executor.ctx.terms.mk_var("poly_cap_x", Sort::Int);
        let zero = executor.ctx.terms.mk_int(BigInt::from(0));
        let x_plus_zero = executor
            .ctx
            .terms
            .mk_app(Symbol::named("+"), [x, zero], Sort::Int);
        let identity = executor
            .ctx
            .terms
            .mk_app(Symbol::named("="), [x_plus_zero, x], Sort::Bool);
        let authored_negation = executor.ctx.terms.mk_not_raw(identity);
        let mut assumptions = vec![authored_negation];
        assumptions.extend((0..MAX_AUTHORED_POLY_ROOTS).map(|index| {
            executor
                .ctx
                .terms
                .mk_var(format!("poly_scope_filler_{index}"), Sort::Bool)
        }));
        executor.last_assumptions = Some(assumptions);
        let supplied_roots = executor.proof_original_problem_assertions_slice().len()
            + executor
                .last_assumptions
                .as_deref()
                .map_or(0, |assumptions| assumptions.len());
        assert!(supplied_roots > MAX_AUTHORED_POLY_ROOTS);
        assert!(
            executor.bounded_authored_poly_scope().is_none(),
            "the borrowed source/assumption cardinality gate must refuse before collecting"
        );

        let mut proof = trust_proof();
        executor.replace_with_exact_authored_poly_refutation(&mut proof, RepairEntry::Check);

        assert!(matches!(
            proof.steps.as_slice(),
            [ProofStep::Step {
                rule: AletheRule::Trust,
                ..
            }]
        ));
    }

    #[test]
    fn unrelated_authored_scope_declines_before_publication_walk() {
        let mut executor = Executor::new();
        let unrelated = executor
            .ctx
            .terms
            .mk_var("poly_unrelated_authored_root", Sort::Bool);
        executor.last_assumptions = Some(vec![unrelated]);
        let mut proof = Proof::new();
        let checks_before = executor.strict_check_invocations.get();

        executor.replace_with_exact_authored_poly_refutation(&mut proof, RepairEntry::Check);

        assert_eq!(executor.strict_check_invocations.get(), checks_before);
        assert!(proof.steps.is_empty());
    }

    #[test]
    fn native_checked_generic_wire_gap_reaches_authored_poly_replacement() {
        let mut executor = Executor::new();
        let x = executor.ctx.terms.mk_var("native_poly_wire_x", Sort::Int);
        let one = executor.ctx.terms.mk_int(BigInt::from(1));
        let two = executor.ctx.terms.mk_int(BigInt::from(2));
        let x_plus_one = executor.ctx.terms.mk_add(vec![x, one]);
        let left = executor.ctx.terms.mk_mul(vec![x_plus_one, x_plus_one]);
        let x_squared = executor.ctx.terms.mk_mul(vec![x, x]);
        let twice_x = executor.ctx.terms.mk_mul(vec![two, x]);
        let tail = executor.ctx.terms.mk_add(vec![twice_x, one]);
        let right = executor.ctx.terms.mk_add(vec![x_squared, tail]);
        let identity = executor.ctx.terms.mk_eq(left, right);
        let negated_identity = executor.ctx.terms.mk_not_raw(identity);
        executor.last_assumptions = Some(vec![negated_identity]);

        let mut proof = Proof::new();
        let assumption = proof.add_assume(negated_identity, None);
        let generic =
            proof.add_theory_lemma_with_kind("NIA", vec![identity], TheoryLemmaKind::Generic);
        proof.add_resolution(Vec::new(), identity, assumption, generic);

        let native_quality = executor
            .check_proof_strict_with_datatypes(&proof)
            .expect("the Generic identity is independently revalidated");
        assert!(
            !native_quality.is_complete(),
            "the trust-bearing producer tag must keep the native proof unpublished"
        );
        assert_eq!(native_quality.trust_count, 1);
        assert!(executor.proof_has_known_wire_gap(&proof));

        executor.run_authored_replacement_cascade(&mut proof);

        let repaired_quality = executor
            .check_proof_strict_with_datatypes(&proof)
            .expect("the authored polynomial replacement must remain strict");
        assert!(repaired_quality.is_complete());
        assert!(!executor.proof_has_known_wire_gap(&proof));
        assert!(proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::ArithClauseTautology,
                ..
            }
        )));
        assert!(!proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::Generic,
                ..
            }
        )));
    }
}
