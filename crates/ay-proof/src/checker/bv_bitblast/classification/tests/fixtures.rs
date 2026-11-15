// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;

pub(super) fn eq(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [left, right], Sort::Bool)
}

pub(super) fn tagged(literal: TermId, kind: TheoryLemmaKind) -> ProofStep {
    ProofStep::TheoryLemma {
        theory: "BV".to_owned(),
        clause: vec![literal],
        kind,
        farkas: None,
        lia: None,
    }
}

pub(super) fn evaluate(terms: &mut TermStore, name: &str) -> ProofStep {
    let zero = terms.mk_bitvec(BigInt::from(0u8), 8);
    let symbol = match name {
        "zero_extend" => Symbol::indexed(name, vec![0]),
        "extract" => Symbol::indexed(name, vec![7, 0]),
        _ => Symbol::named(name),
    };
    // Deliberately malformed operation arity: the census must still charge
    // these supported costly root families without running their evaluator.
    let operation = terms.mk_app(symbol, Vec::<TermId>::new(), Sort::bitvec(8));
    let equality = eq(terms, operation, zero);
    ProofStep::Step {
        rule: AletheRule::Evaluate,
        clause: vec![equality],
        premises: vec![],
        args: vec![],
    }
}
