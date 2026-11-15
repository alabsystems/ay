// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{NraSosCertificate, NraSosOrigin, NraSosRational, NraSosTerm, ProofId, Symbol};
use num_bigint::BigInt;

fn rational(value: i64) -> NraSosRational {
    NraSosRational {
        numerator: BigInt::from(value),
        denominator: BigInt::from(1u8),
    }
}

fn single_step_proof(clause: Vec<TermId>, certificate: NraSosCertificate) -> Proof {
    let mut proof = Proof::new();
    proof.add_step(ProofStep::NraSos {
        clause,
        certificate,
    });
    proof
}

fn square_is_nonnegative(executor: &mut Executor, rhs: i64) -> Proof {
    let x = executor.ctx.terms.mk_var("wire_sos_x", Sort::Real);
    let zero = executor
        .ctx
        .terms
        .mk_rational(num_rational::BigRational::from_integer(BigInt::from(0u8)));
    let square = executor.ctx.terms.mk_mul(vec![x, x]);
    let nonnegative = executor.ctx.terms.mk_ge(square, zero);
    let certificate = NraSosCertificate {
        basis: vec![vec![], vec![x]],
        gram: vec![
            vec![rational(0), rational(0)],
            vec![rational(0), rational(1)],
        ],
        terms: vec![NraSosTerm {
            origin: NraSosOrigin::ClauseLiteral { position: 0 },
            multiplier: rational(1),
        }],
        rhs: rational(rhs),
    };
    single_step_proof(vec![nonnegative], certificate)
}

/// The printer lowers the checked `x² >= 0` theorem, so the publication
/// screen sees no wire gap and the document carries no hole.
#[test]
fn native_nra_sos_wire_gap_closes_under_the_checked_lowering() {
    let mut executor = Executor::new();
    let proof = square_is_nonnegative(&mut executor, 0);
    let authenticated = ay_proof::authenticate_premise_clauses_strict_with_context(
        &proof,
        &executor.ctx.terms,
        None,
        None,
        &[],
    )
    .expect("x²>=0 is a checked native theorem");
    let ProofStep::NraSos { clause, .. } = &proof.steps[0] else {
        panic!("SOS fixture")
    };
    assert_eq!(authenticated.clause(ProofId(0)), Some(clause.as_slice()));
    assert!(!executor.proof_has_known_wire_gap(&proof));
    let document =
        ay_proof::try_export_alethe(&proof, &executor.ctx.terms).expect("checked SOS lowering");
    assert!(!document.contains(":rule hole"), "{document}");
    assert!(document.contains(":rule la_mult_neg"), "{document}");
}

/// NEGATIVE TWINS: the screen admits nothing the lowering does not render. A
/// certificate only the strict checker refuses (a misstated `rhs`; its rows
/// still refute) and a checked certificate outside the lowering's one-sort
/// envelope both keep the wire gap and the honest hole.
#[test]
fn native_nra_sos_wire_gap_stays_where_the_lowering_declines() {
    let mut executor = Executor::new();
    let refused = square_is_nonnegative(&mut executor, -1);
    assert!(ay_proof::authenticate_premise_clauses_strict_with_context(
        &refused,
        &executor.ctx.terms,
        None,
        None,
        &[],
    )
    .is_err());
    assert!(executor.proof_has_known_wire_gap(&refused));

    let terms = &mut executor.ctx.terms;
    let x = terms.mk_var("wire_sos_real", Sort::Real);
    let n = terms.mk_var("wire_sos_int", Sort::Int);
    let [real_zero, real_one] = [0u8, 1u8]
        .map(|value| terms.mk_rational(num_rational::BigRational::from_integer(value.into())));
    let [int_zero, int_one] = [0u8, 1u8].map(|value| terms.mk_int(value.into()));
    let mut compare = |left, right| terms.mk_app(Symbol::named("<="), [left, right], Sort::Bool);
    let sources = [
        compare(real_one, x),
        compare(x, real_zero),
        compare(int_one, n),
        compare(n, int_zero),
    ];
    let clause: Vec<TermId> = sources.into_iter().map(|s| terms.mk_not(s)).collect();
    let product = |left, right| NraSosTerm {
        origin: NraSosOrigin::Product { left, right },
        multiplier: rational(1),
    };
    let literal = |position, value| NraSosTerm {
        origin: NraSosOrigin::ClauseLiteral { position },
        multiplier: rational(value),
    };
    // (x-1)(n-1) + (-x)(n-1) + 2(n-1) + (-n) = -1.
    let mixed = single_step_proof(
        clause,
        NraSosCertificate {
            basis: vec![vec![]],
            gram: vec![vec![rational(0)]],
            terms: vec![product(0, 2), product(1, 2), literal(2, 2), literal(3, 1)],
            rhs: rational(-1),
        },
    );
    ay_proof::authenticate_premise_clauses_strict_with_context(
        &mixed,
        &executor.ctx.terms,
        None,
        None,
        &[],
    )
    .expect("the mixed-sort product identity is a checked native theorem");
    assert!(executor.proof_has_known_wire_gap(&mixed));
    assert!(ay_proof::try_export_alethe(&mixed, &executor.ctx.terms)
        .expect("explicit-hole diagnostic")
        .contains(":rule hole"));
}
