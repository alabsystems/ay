// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;

pub(super) struct Fixture {
    pub(super) terms: TermStore,
    pub(super) proof: Proof,
    pub(super) assertions: Vec<TermId>,
    pub(super) d: TermId,
    pub(super) x: TermId,
}

pub(super) fn append(
    terms: &mut TermStore,
    proof: &mut Proof,
    rule: AletheRule,
    defined: TermId,
    expression: TermId,
) {
    let symbol = match &rule {
        AletheRule::FreshDefBound => "<=",
        AletheRule::FreshDefEq => "=",
        _ => panic!("fixture rule"),
    };
    let clause = terms.mk_app(Symbol::named(symbol), [defined, expression], Sort::Bool);
    proof.add_rule_step(rule, vec![clause], vec![], vec![defined]);
}

impl Fixture {
    pub(super) fn new() -> Self {
        let mut terms = TermStore::new();
        let d = terms.mk_var("cancel-definition", Sort::Int);
        let x = terms.mk_var("cancel-source", Sort::Int);
        let mut proof = Proof::new();
        append(&mut terms, &mut proof, AletheRule::FreshDefBound, d, x);
        Self {
            terms,
            proof,
            assertions: vec![],
            d,
            x,
        }
    }

    pub(super) fn add(&mut self, rule: AletheRule, defined: TermId, expression: TermId) {
        append(&mut self.terms, &mut self.proof, rule, defined, expression);
    }

    pub(super) fn rich() -> Self {
        let mut fixture = Self::new();
        let predicate = fixture.terms.mk_app(
            Symbol::named("source-predicate"),
            vec![fixture.x; 5],
            Sort::Bool,
        );
        let not_predicate = fixture.terms.mk_not_raw(predicate);
        let universal = fixture.terms.mk_forall_with_triggers(
            vec![("bound-source".to_owned(), Sort::Int)],
            predicate,
            vec![vec![], vec![fixture.x, fixture.x, predicate]],
        );
        let existential = fixture.terms.mk_exists_with_triggers(
            vec![("other-bound-source".to_owned(), Sort::Int)],
            not_predicate,
            vec![vec![fixture.x]],
        );
        let ite = fixture.terms.mk_ite(predicate, universal, existential);
        let root = fixture
            .terms
            .mk_let(vec![("local-source".to_owned(), fixture.x)], ite);
        fixture.assertions = vec![root, root];
        fixture.proof.add_assume(root, None);
        fixture
    }
}
