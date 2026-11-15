// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{FpOp, Proof, ProofId, ProofStep, TheoryLemmaKind};

#[test]
fn complete_symbolic_add_sub_schemas_accept_all_modes_and_standard_formats() {
    for operation in [Arithmetic::Add, Arithmetic::Sub] {
        for (eb, p) in [(2, 2), (5, 11), (8, 24), (11, 53), (15, 113)] {
            assert!(SumFixture::new(eb, p, operation).certificate().accepts());
        }
    }
}

#[test]
fn actual_strict_proof_dispatcher_rechecks_add_and_sub_and_exact_annotation() {
    for operation in [Arithmetic::Add, Arithmetic::Sub] {
        let mut f = SumFixture::new(8, 24, operation).certificate();
        let negative = f.fixture.terms.mk_not(f.theorem);
        let mut proof = Proof::new();
        let assumption = proof.add_assume(negative, None);
        let kind = match operation {
            Arithmetic::Add => FpOp::Add,
            Arithmetic::Sub => FpOp::Sub,
            Arithmetic::Mul => panic!("sum fixture"),
        };
        let theorem = proof.add_theory_lemma_with_kind(
            "FP",
            vec![f.theorem],
            TheoryLemmaKind::FpToBv { operation: kind },
        );
        proof.add_step(ProofStep::Resolution {
            clause: vec![],
            pivot: f.theorem,
            clause1: theorem,
            clause2: assumption,
        });
        crate::check_proof_strict(&proof, &f.fixture.terms).expect("actual complete word theorem");
        let opposite = if operation == Arithmetic::Add {
            FpOp::Sub
        } else {
            FpOp::Add
        };
        assert!(crate::checker::fp_to_bv::validate_fp_to_bv(
            &f.fixture.terms,
            ProofId(0),
            &[f.theorem],
            opposite,
            &mut |_, _| true,
        )
        .is_err());
    }
    // No captured native CNF/source journal or original-query permit is minted.
}

#[test]
fn literal_rounding_and_reversed_complete_equality_remain_source_bound() {
    for operation in [Arithmetic::Add, Arithmetic::Sub] {
        for name in [
            "RNE",
            "RNA",
            "RTP",
            "RTN",
            "RTZ",
            "roundNearestTiesToEven",
            "roundNearestTiesToAway",
            "roundTowardPositive",
            "roundTowardNegative",
            "roundTowardZero",
        ] {
            let mut sum = SumFixture::new(3, 4, operation);
            let rm = app(
                &mut sum.fixture.terms,
                name,
                &[],
                Sort::Uninterpreted("RoundingMode".into()),
            );
            let TermData::App(_, args) = sum.fixture.terms.get(sum.fixture.source) else {
                panic!("source");
            };
            let args = args.clone();
            sum.fixture.source = app(
                &mut sum.fixture.terms,
                operation.name(),
                &[rm, args[1], args[2]],
                Sort::FloatingPoint(3, 4),
            );
            let mut f = sum.certificate();
            assert!(f.accepts());
            let reverse = app(
                &mut f.fixture.terms,
                "=",
                &[f.lowered, f.fixture.source],
                Sort::Bool,
            );
            assert!(
                recognizes_arithmetic(&f.fixture.terms, &[reverse], operation, &mut |_, _| true)
                    .expect("complete reverse")
            );
        }
    }
}

#[test]
fn changed_source_and_rm_and_added_literal_cannot_complete_old_sum_schema() {
    for operation in [Arithmetic::Add, Arithmetic::Sub] {
        let mut f = SumFixture::new(3, 4, operation).certificate();
        let TermData::App(_, args) = f.fixture.terms.get(f.fixture.source) else {
            panic!("source");
        };
        let args = args.clone();
        let other_rm = f
            .fixture
            .terms
            .mk_var("foreign_rm", Sort::Uninterpreted("RoundingMode".into()));
        let changed = app(
            &mut f.fixture.terms,
            operation.name(),
            &[other_rm, args[1], args[2]],
            Sort::FloatingPoint(3, 4),
        );
        let theorem = app(&mut f.fixture.terms, "=", &[changed, f.lowered], Sort::Bool);
        assert!(
            !recognizes_arithmetic(&f.fixture.terms, &[theorem], operation, &mut |_, _| true)
                .expect("different actual RM")
        );
        let unrelated = f.fixture.terms.mk_var("unrelated", Sort::Bool);
        assert!(!recognizes_arithmetic(
            &f.fixture.terms,
            &[f.theorem, unrelated],
            operation,
            &mut |_, _| true
        )
        .expect("complete unit only"));
        let missing = app(
            &mut f.fixture.terms,
            operation.name(),
            &[f.fixture.rm, args[1], TermId::SENTINEL],
            Sort::FloatingPoint(3, 4),
        );
        let theorem = app(&mut f.fixture.terms, "=", &[missing, f.lowered], Sort::Bool);
        assert!(
            !recognizes_arithmetic(&f.fixture.terms, &[theorem], operation, &mut |_, _| true)
                .expect("missing child refuses")
        );
    }
}

#[test]
fn missing_fractional_borrow_or_changed_sum_operator_cannot_certify_alignment() {
    use graph::{Binary, Operation};
    for operation in [Arithmetic::Add, Arithmetic::Sub] {
        let f = SumFixture::new(8, 24, operation).certificate();
        let borrow = f
            .nodes
            .iter()
            .position(|node| {
                let Operation::Binary(Binary::Sub, _, b) = node.operation else {
                    return false;
                };
                let Operation::Resize(inner) = f.nodes[b.0].operation else {
                    return false;
                };
                f.nodes[inner.0].width == 1
            })
            .expect("actual fractional-tail borrow");
        let sum = f
            .nodes
            .iter()
            .position(|node| matches!(node.operation, Operation::Binary(Binary::Add, _, _)))
            .expect("actual full sum");
        for (index, replacement) in [(borrow, "bvadd"), (sum, "bvsub")] {
            let mut entries = f.fixture.terms.entries_snapshot();
            let TermData::App(_, args) = entries[f.emitted[index].index()].0.clone() else {
                panic!("actual word op");
            };
            entries[f.emitted[index].index()].0 = TermData::App(Symbol::named(replacement), args);
            let imported =
                TermStore::from_entries(entries, None, None, f.fixture.terms.var_counter());
            assert!(
                !recognizes_arithmetic(&imported, &[f.theorem], operation, &mut |_, _| true)
                    .expect("changed full alignment declines")
            );
        }
    }
}
