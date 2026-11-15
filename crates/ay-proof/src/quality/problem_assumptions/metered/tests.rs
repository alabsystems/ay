// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::Sort;

use super::*;

mod boundaries;
mod progress;

struct Fixture {
    terms: TermStore,
    proof: Proof,
    roots: Vec<TermId>,
    branch: TermId,
    ite: TermId,
    then_implication: TermId,
    else_implication: TermId,
}

impl Fixture {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let first_guard = terms.mk_var("assumption_g1", Sort::Bool);
        let second_guard = terms.mk_var("assumption_g2", Sort::Bool);
        let condition = terms.mk_and(vec![first_guard, second_guard]);
        let branch = terms.mk_var("assumption_t", Sort::Bool);
        let alternate = terms.mk_var("assumption_e", Sort::Bool);
        let ite = terms.mk_ite_raw(condition, branch, alternate);
        let then_implication = terms.mk_implies(condition, branch);
        let negated_condition = terms.mk_not(condition);
        let else_implication = terms.mk_implies(negated_condition, alternate);
        let mut proof = Proof::new();
        proof.add_assume(then_implication, None);
        proof.add_assume(else_implication, None);
        Self {
            terms,
            proof,
            roots: vec![ite],
            branch,
            ite,
            then_implication,
            else_implication,
        }
    }

    fn run(&self, progress: Progress<'_>) -> Result<(), ProofCheckError> {
        validate_problem_assumptions_with_progress(&self.proof, &self.terms, &self.roots, progress)
    }

    fn compare(&self) -> Result<(), ProofCheckError> {
        let old = super::super::validate_problem_assumptions_metered(
            &self.proof,
            &self.terms,
            &self.roots,
            &mut |_, _| true,
        );
        let new = self.run(&mut |_, _| true);
        assert_eq!(old, new);
        new
    }

    fn replace_entries(&mut self, entries: Vec<(TermData, Sort)>) {
        let (true_term, false_term) = self.terms.boolean_constant_ids();
        self.terms =
            TermStore::from_entries(entries, true_term, false_term, self.terms.var_counter());
    }
}

fn assert_resource<T>(result: Result<T, ProofCheckError>) {
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
}

#[test]
fn authored_ite_branches_and_combined_form_match_the_legacy_oracle() {
    let mut fixture = Fixture::new();
    fixture.compare().expect("authored branch consequences");
    let combined = fixture
        .terms
        .mk_and(vec![fixture.then_implication, fixture.else_implication]);
    fixture.proof.add_assume(combined, None);
    fixture.compare().expect("combined producer form");
}

#[test]
fn authored_conjunctions_keep_direct_roots_duplicates_and_nested_ite_authority() {
    let mut fixture = Fixture::new();
    let fact = fixture.terms.mk_var("authored_fact", Sort::Bool);
    let inner = fixture
        .terms
        .mk_app(Symbol::named("and"), [fixture.ite, fact, fact], Sort::Bool);
    let outer = fixture
        .terms
        .mk_app(Symbol::named("and"), [inner, inner], Sort::Bool);
    fixture.roots = vec![outer, outer];
    for assumption in [outer, inner, fixture.ite, fact, fact] {
        fixture.proof.add_assume(assumption, None);
    }
    fixture
        .compare()
        .expect("exact authored conjunction closure");
}

#[test]
fn unauthorized_assumptions_preserve_exact_step_and_term_ids() {
    let mut fixture = Fixture::new();
    fixture.proof.steps.push(ProofStep::Anchor {
        end_step: ProofId(0),
        variables: vec![],
    });
    fixture.proof.add_assume(fixture.branch, None);
    assert_eq!(
        fixture.compare(),
        Err(ProofCheckError::UnauthorizedAssumption {
            step: ProofId(3),
            term: fixture.branch
        })
    );
}

#[test]
fn indexed_and_or_unreachable_ite_does_not_grant_conjunction_authority() {
    let mut fixture = Fixture::new();
    let indexed = fixture
        .terms
        .mk_app(Symbol::indexed("and", vec![]), [fixture.ite], Sort::Bool);
    let disjunction = fixture
        .terms
        .mk_app(Symbol::named("or"), [fixture.ite], Sort::Bool);
    for root in [indexed, disjunction, fixture.terms.true_term()] {
        fixture.roots = vec![root];
        assert_eq!(
            fixture.compare(),
            Err(ProofCheckError::UnauthorizedAssumption {
                step: ProofId(0),
                term: fixture.then_implication
            })
        );
    }
}
