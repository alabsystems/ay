// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn signed_theorem(f: &mut Fixture, op: FpOp, not_nan: TermId, sign: TermId) -> TermId {
    let source = f.app(
        if op == FpOp::IsNegative {
            "fp.isNegative"
        } else {
            "fp.isPositive"
        },
        &[f.value],
        Sort::Bool,
    );
    let lowered = f.and(not_nan, sign);
    f.eq(source, lowered)
}

fn source_sign(f: &mut Fixture, op: FpOp) -> TermId {
    f.test_field(
        f.fields.sign,
        1,
        if op == FpOp::IsNegative {
            WordConstant::Ones
        } else {
            WordConstant::Zero
        },
        EqualitySense::Equal,
    )
}

#[test]
fn raw_not_nan_signed_schemas_remain_supported() {
    for op in [FpOp::IsPositive, FpOp::IsNegative] {
        let mut f = Fixture::new(11, 53);
        let nan = f.predicate(FpOp::IsNaN);
        let not_nan = f.terms.mk_not_raw(nan);
        let sign = source_sign(&mut f, op);
        let theorem = signed_theorem(&mut f, op, not_nan, sign);
        f.validate(theorem, op).expect("exact raw not-NaN schema");
    }
}

#[test]
fn normalized_not_nan_and_sign_orders_and_equality_orientation_are_exact() {
    for op in [FpOp::IsPositive, FpOp::IsNegative] {
        let mut f = Fixture::new(8, 24);
        let nan = f.predicate(FpOp::IsNaN);
        let normalized = f.terms.mk_not(nan);
        let Some([left, right]) = (match f.terms.get(normalized) {
            TermData::App(Symbol::Named(name), args) if name == "or" => {
                <[TermId; 2]>::try_from(args.as_slice()).ok()
            }
            _ => None,
        }) else {
            panic!("actual mk_not must produce the normalized disjunction");
        };
        let reversed = f.app("or", &[right, left], Sort::Bool);
        let sign = source_sign(&mut f, op);
        for not_nan in [normalized, reversed] {
            let source = f.app(
                if op == FpOp::IsNegative {
                    "fp.isNegative"
                } else {
                    "fp.isPositive"
                },
                &[f.value],
                Sort::Bool,
            );
            for lowered in [f.and(not_nan, sign), f.and(sign, not_nan)] {
                for theorem in [f.eq(source, lowered), f.eq(lowered, source)] {
                    f.validate(theorem, op)
                        .expect("both exact commutative orientations");
                }
            }
        }
    }
}

#[test]
fn signed_schema_rejects_weakened_or_changed_normalized_nan_conditions() {
    for op in [FpOp::IsPositive, FpOp::IsNegative] {
        let mut f = Fixture::new(8, 24);
        let exponent_equal = f.test_field(
            f.fields.exponent,
            8,
            WordConstant::Ones,
            EqualitySense::Equal,
        );
        let exponent_different = f.terms.mk_not_raw(exponent_equal);
        let fraction_equal = f.test_field(
            f.fields.fraction,
            23,
            WordConstant::Zero,
            EqualitySense::Equal,
        );
        let fraction_different = f.terms.mk_not_raw(fraction_equal);
        let other = f.terms.mk_var("other_exponent", Sort::bitvec(8));
        let other_different = f.test_field(other, 8, WordConstant::Ones, EqualitySense::Different);
        let sign = source_sign(&mut f, op);
        let malformed = [
            f.terms.mk_bool(true),
            f.app("or", &[exponent_equal, fraction_equal], Sort::Bool),
            f.app("or", &[exponent_different, fraction_different], Sort::Bool),
            f.app("or", &[other_different, fraction_equal], Sort::Bool),
            f.app(
                "or",
                &[exponent_different, fraction_equal, sign],
                Sort::Bool,
            ),
            f.app("or", &[exponent_different, fraction_equal], Sort::bitvec(1)),
            f.app("or", &[exponent_different, TermId::SENTINEL], Sort::Bool),
        ];
        for not_nan in malformed {
            let theorem = signed_theorem(&mut f, op, not_nan, sign);
            assert!(f.validate(theorem, op).is_err());
        }
    }
}

#[test]
fn normalized_signed_schema_runs_through_actual_strict_dispatch() {
    for op in [FpOp::IsPositive, FpOp::IsNegative] {
        let mut f = Fixture::new(5, 11);
        let theorem = f.theorem(op);
        let negative = f.terms.mk_not_raw(theorem);
        let mut proof = Proof::new();
        let premise = proof.add_assume(negative, None);
        let lemma = proof.add_theory_lemma_with_kind(
            "FP",
            vec![theorem],
            TheoryLemmaKind::FpToBv { operation: op },
        );
        proof.add_step(ProofStep::Resolution {
            clause: vec![],
            pivot: theorem,
            clause1: lemma,
            clause2: premise,
        });
        crate::check_proof_strict(&proof, &f.terms)
            .expect("actual complete normalized signed schema and terminal resolution");
    }
}

#[test]
fn normalized_signed_schema_preserves_terminal_and_entry_owner_refusal() {
    let mut f = Fixture::new(11, 53);
    let theorem = f.theorem(FpOp::IsNegative);
    let mut healthy_calls = 0;
    super::super::super::validate_fp_to_bv(
        &f.terms,
        ProofId(0),
        &[theorem],
        FpOp::IsNegative,
        &mut |_, _| {
            healthy_calls += 1;
            true
        },
    )
    .expect("normalized healthy schema");
    for refusal in [1, healthy_calls] {
        let mut calls = 0;
        let outcome = super::super::super::validate_fp_to_bv(
            &f.terms,
            ProofId(0),
            &[theorem],
            FpOp::IsNegative,
            &mut |_, _| {
                calls += 1;
                calls < refusal
            },
        );
        assert!(matches!(outcome, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(calls, refusal);
    }
}
