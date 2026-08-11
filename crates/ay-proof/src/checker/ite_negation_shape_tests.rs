// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! NNF complements of ITE terms must retain exact Boolean-rule polarity.

use crate::checker::*;
use ay_core::{AletheRule, ProofId, ProofStep, Sort, TermId, TermStore};

fn validate_and_pos(
    terms: &TermStore,
    source: TermId,
    clause: Vec<TermId>,
) -> Result<(), ProofCheckError> {
    let step = ProofStep::Step {
        rule: AletheRule::AndPos(0),
        clause,
        premises: vec![],
        args: vec![source],
    };
    let mut derived = vec![];
    validate_step(terms, &mut derived, ProofId(0), &step, true, None)
}

fn fixture() -> (TermStore, TermId, TermId, TermId, TermId, TermId) {
    let mut terms = TermStore::new();
    let gate = terms.mk_var("gate", Sort::Bool);
    let condition = terms.mk_var("condition", Sort::Bool);
    let then_term = terms.mk_var("then_term", Sort::Bool);
    let else_term = terms.mk_var("else_term", Sort::Bool);
    let ite = terms.mk_ite(condition, then_term, else_term);
    let source = terms.mk_and(vec![gate, ite]);
    (terms, source, gate, condition, then_term, else_term)
}

#[test]
fn and_pos_accepts_nnf_ite_inside_de_morgan_gate() {
    let (mut terms, source, gate, condition, then_term, else_term) = fixture();
    let not_gate = terms.mk_not(gate);
    let not_then = terms.mk_not(then_term);
    let not_else = terms.mk_not(else_term);
    let negated_ite = terms.mk_ite(condition, not_then, not_else);
    let de_morgan_gate = terms.mk_or(vec![not_gate, negated_ite]);

    validate_and_pos(&terms, source, vec![de_morgan_gate, gate])
        .expect("the exact NNF complement of the ITE branch must be accepted");
}

#[test]
fn and_pos_rejects_nnf_ite_with_wrong_branch_polarity() {
    let (mut terms, source, gate, condition, then_term, else_term) = fixture();
    let not_gate = terms.mk_not(gate);
    let not_else = terms.mk_not(else_term);
    let malformed_negated_ite = terms.mk_ite(condition, then_term, not_else);
    let malformed_gate = terms.mk_or(vec![not_gate, malformed_negated_ite]);

    validate_and_pos(&terms, source, vec![malformed_gate, gate])
        .expect_err("an unnegated then-branch must remain rejected");
}

#[test]
fn and_pos_rejects_nnf_ite_with_wrong_condition() {
    let (mut terms, source, gate, _condition, then_term, else_term) = fixture();
    let wrong_condition = terms.mk_var("wrong_condition", Sort::Bool);
    let not_gate = terms.mk_not(gate);
    let not_then = terms.mk_not(then_term);
    let not_else = terms.mk_not(else_term);
    let malformed_negated_ite = terms.mk_ite(wrong_condition, not_then, not_else);
    let malformed_gate = terms.mk_or(vec![not_gate, malformed_negated_ite]);

    validate_and_pos(&terms, source, vec![malformed_gate, gate])
        .expect_err("changing the ITE condition must remain rejected");
}
