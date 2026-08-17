// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Mixed-polarity packed-clausification checks.

use super::validate_theory_lemma_strict;
use ay_core::{Sort, TermId, TermStore, TheoryLemmaKind};

#[test]
fn negated_and_member_requires_its_exact_positive_complement() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let eq = |terms: &mut TermStore, a: TermId, b: TermId| {
        terms.mk_app(ay_core::Symbol::named("="), vec![a, b], Sort::Bool)
    };
    // Int equalities keep these atoms opaque to the bounded evaluator: only
    // the structural propositional checker can establish the exact schema.
    let p = eq(&mut terms, x, y);
    let q = eq(&mut terms, y, z);
    let r = eq(&mut terms, x, z);
    let not_p = terms.mk_not_raw(p);
    let not_q = terms.mk_not_raw(q);
    let not_r = terms.mk_not_raw(r);
    let conjunction = terms.mk_app(ay_core::Symbol::named("and"), vec![p, q, not_r], Sort::Bool);
    let packed = |terms: &mut TermStore, tail: Vec<TermId>| {
        let mut disjuncts = vec![conjunction, not_p, not_q];
        disjuncts.extend(tail);
        terms.mk_app(ay_core::Symbol::named("or"), disjuncts, Sort::Bool)
    };

    let exact = packed(&mut terms, vec![r]);
    validate_theory_lemma_strict(&terms, vec![exact], TheoryLemmaKind::BoolTautology)
        .expect("(p /\\ q /\\ !r) \\/ !p \\/ !q \\/ r is a tautology");

    let missing = packed(&mut terms, vec![]);
    assert!(
        validate_theory_lemma_strict(&terms, vec![missing], TheoryLemmaKind::BoolTautology)
            .is_err(),
        "omitting r is falsifiable by p=q=true, r=false"
    );
    let same_polarity = packed(&mut terms, vec![not_r]);
    assert!(
        validate_theory_lemma_strict(&terms, vec![same_polarity], TheoryLemmaKind::BoolTautology)
            .is_err(),
        "using !r again is falsifiable by p=q=r=true"
    );
}
