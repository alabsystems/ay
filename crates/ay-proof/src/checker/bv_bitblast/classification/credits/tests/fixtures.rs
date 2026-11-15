// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
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

pub(super) fn ordinary(count: usize) -> (Proof, TermStore) {
    let mut terms = TermStore::new();
    let wide = terms.mk_var("expensive", Sort::bitvec(16));
    let equality = terms.mk_app(Symbol::named("="), [wide, wide], Sort::Bool);
    (
        Proof::from_steps(vec![tagged(equality, TheoryLemmaKind::BvBitBlast); count]),
        terms,
    )
}

pub(super) fn mixed() -> (Proof, TermStore) {
    let (_, mut terms) = ordinary(0);
    let wide = terms.mk_var("mixed", Sort::bitvec(16));
    let equality = terms.mk_app(Symbol::named("="), [wide, wide], Sort::Bool);
    let mut proof = Proof::from_steps(vec![ProofStep::Assume(terms.true_term())]);
    for kind in [
        TheoryLemmaKind::BvBitBlast,
        TheoryLemmaKind::BvBitBlastGate {
            gate_type: BvGateType::And,
            width: 3,
        },
        TheoryLemmaKind::BvLiaTautology,
        TheoryLemmaKind::SeqExtensionalCompanionContradiction,
    ] {
        proof.add_step(tagged(equality, kind));
    }
    // As in the legacy census fixture, costly malformed Evaluate roots still
    // consume their family budget, without running semantic validation.
    let zero = terms.mk_bitvec(num_bigint::BigInt::from(0), 8);
    let mul = terms.mk_app(Symbol::named("bvmul"), [], Sort::bitvec(8));
    let eq = terms.mk_app(Symbol::named("="), [mul, zero], Sort::Bool);
    proof.add_step(ProofStep::Step {
        rule: ay_core::AletheRule::Evaluate,
        clause: vec![eq],
        premises: vec![],
        args: vec![],
    });
    for _ in 0..3 {
        proof.add_step(tagged(equality, TheoryLemmaKind::BvLiaTautology));
    }
    (proof, terms)
}

pub(super) fn plan<'a>(proof: &'a Proof, terms: &'a TermStore) -> ExpensiveBvCreditPlan<'a> {
    plan_expensive_bv_credits_with_progress(proof, terms, &mut |_, _| true).unwrap()
}

pub(super) fn prepaid<'a>(proof: &'a Proof, terms: &'a TermStore) -> PrepaidBvCredits<'a> {
    plan(proof, terms)
        .prepay(deadline(), &mut |_, _| true)
        .unwrap()
}
