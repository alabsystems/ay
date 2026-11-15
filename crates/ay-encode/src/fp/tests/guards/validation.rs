// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::term::{Constant, Symbol, TermData, TermId, TermStore};

#[test]
fn arithmetic_output_conversions_uf_and_unchosen_guard_descendants_still_refuse() {
    let (words, targets) = inputs(32);
    let bindings = links(&words, &targets);
    let namespace = ChcProblem::new();
    with_owner(|budget| {
        let arithmetic = words[0].clone().bvadd(Expr::bitvec_const(0u8, 32));
        let conversion = fields(words[0].clone(), 32).fp_to_ieee_bv();
        let nested = words[0].clone().extract(31, 0).extract(31, 0);
        let uf =
            Expr::func_app_with_sort("user_bv", vec![words[0].clone()], crate::Sort::bitvec(32));
        for unsupported in [arithmetic, conversion, nested, uf] {
            let guard = unsupported.bvult(words[1].clone());
            let root = Expr::ite(Expr::true_(), Expr::true_(), guard);
            assert!(matches!(
                lower_fp_expr_clause(&[root], &bindings, &namespace, budget),
                Err(FpAdapterError::Unsupported(_))
            ));
        }
        let wide = Expr::var("wide", crate::Sort::bitvec(65));
        let target = ChcVar::new("wide", ChcSort::BitVec(65));
        let binding = [FpExprInputBinding {
            source: &wide,
            target: &target,
        }];
        assert!(lower_fp_expr_clause(
            &[wide.clone().eq(wide.clone())],
            &binding,
            &namespace,
            budget
        )
        .is_err());
        let many = Expr::distinct(vec![words[0].clone(), words[1].clone(), words[0].clone()]);
        assert!(matches!(
            lower_fp_expr_clause(&[many], &bindings, &namespace, budget),
            Err(FpAdapterError::Unsupported(_))
        ));
    });
}

fn malformed(
    symbol: Symbol,
    args: Vec<TermId>,
    operand_sort: ay_core::Sort,
    root_sort: ay_core::Sort,
    budget: &mut WorkBudget<'_>,
) -> Result<(), FpAdapterError> {
    budget.admit(65_536, 65_536)?;
    let entries = [
        (TermData::Const(Constant::Bool(true)), ay_core::Sort::Bool),
        (TermData::Const(Constant::Bool(false)), ay_core::Sort::Bool),
        (
            TermData::Var("guard_a".into(), 2),
            ay_core::Sort::bitvec(32),
        ),
        (
            TermData::Const(Constant::BitVec {
                value: 0u8.into(),
                width: 32,
            }),
            operand_sort,
        ),
        (TermData::App(symbol, args), root_sort),
    ];
    let mut refusal = None;
    let terms = TermStore::from_entries_with_progress(
        &entries,
        Some(TermId(0)),
        Some(TermId(1)),
        5,
        &mut |w, b| match budget.admit(w, b) {
            Ok(()) => true,
            Err(error) => {
                refusal = Some(error);
                false
            }
        },
    )
    .map_err(|_| FpAdapterError::Owner(refusal.unwrap_or_else(|| budget.refuse_exhaustion())))?;
    let target = ChcVar::new("guard_a", ChcSort::BitVec(32));
    let bindings = [ay_chc::fp_adapter::FpInputBinding {
        source: TermId(2),
        target: &target,
    }];
    let namespace = ChcProblem::new();
    let result =
        ay_chc::fp_adapter::lower_fp_clause(&terms, &[TermId(4)], &bindings, &namespace, budget)
            .map(drop);
    drop(terms);
    drop(entries);
    budget.charge(0)?;
    result
}

#[test]
fn native_whole_source_rejects_dead_mixed_sort_wrong_arity_and_indexed_predicates() {
    with_owner(|budget| {
        for (symbol, args, operand, root) in [
            (
                Symbol::named("bvult"),
                vec![TermId(2), TermId(99)],
                ay_core::Sort::bitvec(32),
                ay_core::Sort::Bool,
            ),
            (
                Symbol::named("bvult"),
                vec![TermId(2)],
                ay_core::Sort::bitvec(32),
                ay_core::Sort::Bool,
            ),
            (
                Symbol::named("bvult"),
                vec![TermId(2), TermId(3)],
                ay_core::Sort::bitvec(64),
                ay_core::Sort::Bool,
            ),
            (
                Symbol::named("bvult"),
                vec![TermId(2), TermId(3)],
                ay_core::Sort::bitvec(32),
                ay_core::Sort::bitvec(1),
            ),
            (
                Symbol::indexed("bvult", vec![0]),
                vec![TermId(2), TermId(3)],
                ay_core::Sort::bitvec(32),
                ay_core::Sort::Bool,
            ),
        ] {
            assert!(malformed(symbol, args, operand, root, budget).is_err());
        }
    });
}
