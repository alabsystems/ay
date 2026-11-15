// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::term::{Constant, Symbol, TermData, TermId, TermStore};

pub(super) mod native;
mod ownership;

fn raw_input(width: u32) -> (Expr, ChcVar) {
    (
        Expr::var("raw_x", crate::Sort::bitvec(width)),
        ChcVar::new("raw_x", ChcSort::BitVec(width)),
    )
}

fn fields(word: Expr, width: u32) -> Expr {
    let fraction = if width == 32 { 23 } else { 52 };
    Expr::fp_from_bvs(
        word.clone().extract(width - 1, width - 1),
        word.clone().extract(width - 2, fraction),
        word.extract(fraction - 1, 0),
    )
}

fn raw_attempt(budget: &mut WorkBudget<'_>) -> Result<(), FpAdapterError> {
    let (word, target) = raw_input(32);
    let roots = [fields(word.clone(), 32).fp_is_normal()];
    let bindings = [FpExprInputBinding {
        source: &word,
        target: &target,
    }];
    let problem = ChcProblem::new();
    let output = lower_fp_expr_clause(&roots, &bindings, &problem, budget)?;
    let (body, source) = output.into_body(ClauseBody::empty())?.into_parts()?;
    drop(body);
    drop(source);
    budget.charge(0)?;
    Ok(())
}

#[test]
fn exact_word_extracts_remain_separate_source_records() {
    with_owner(|budget| {
        for width in [32, 64] {
            let (word, target) = raw_input(width);
            let roots = [fields(word.clone(), width).fp_is_normal()];
            let bindings = [FpExprInputBinding {
                source: &word,
                target: &target,
            }];
            let plan = source::plan(&roots, &bindings, budget).unwrap();
            let mut slices = Vec::new();
            budget.admit(4096, 4096).unwrap();
            for expr in &plan.nodes {
                budget.charge(256).unwrap();
                let shape = typed::describe(expr).unwrap();
                if let typed::Operator::Extract(high, low) = shape.op {
                    let children = shape.children.collect::<Vec<_>>();
                    assert_eq!(children.len(), 1);
                    assert!(std::ptr::eq(children[0].value(), word.value()));
                    assert!(plan.index(children[0]).unwrap() < plan.index(expr).unwrap());
                    slices.push(vec![high, low]);
                }
            }
            let fraction = if width == 32 { 23 } else { 52 };
            assert_eq!(
                slices,
                [
                    vec![width - 1, width - 1],
                    vec![width - 2, fraction],
                    vec![fraction - 1, 0]
                ]
            );
            drop(slices);
            drop(plan);
            budget.charge(0).unwrap();
        }
    });
}

#[test]
fn complete_raw_leaf_links_survive_repeated_roots_and_body_consumption() {
    with_owner(|budget| {
        for width in [32, 64] {
            let (word, target) = raw_input(width);
            let fp = fields(word.clone(), width);
            let first = fp.clone().fp_is_normal();
            let roots = [first.clone(), fp.fp_is_positive(), first];
            let bindings = [FpExprInputBinding {
                source: &word,
                target: &target,
            }];
            let mut problem = ChcProblem::new();
            let p = problem.declare_predicate("p", vec![ChcSort::BitVec(width)]);
            let old = ClauseBody::new(vec![(p, vec![ChcExpr::Var(target.clone())])], None);
            let output = lower_fp_expr_clause(&roots, &bindings, &problem, budget).unwrap();
            let (body, source) = output.into_body(old).unwrap().into_parts().unwrap();
            assert!(std::ptr::eq(source.roots(), roots.as_slice()));
            assert!(std::ptr::eq(source.bindings()[0].source, &word));
            assert_eq!(body.predicates[0].1, [ChcExpr::Var(target.clone())]);
            let ChcExpr::Op(ChcOp::And, outer) = body.constraint.as_ref().unwrap() else {
                panic!()
            };
            let ChcExpr::Op(ChcOp::And, entries) = outer[0].as_ref() else {
                panic!()
            };
            let mut linked = Vec::new();
            budget.admit(4096, 4096).unwrap();
            for entry in entries.iter().rev().take(width as usize).rev() {
                budget.charge(256).unwrap();
                let ChcExpr::Op(ChcOp::Eq, pair) = entry.as_ref() else {
                    panic!()
                };
                let ChcExpr::Op(ChcOp::Eq, bit) = pair[1].as_ref() else {
                    panic!()
                };
                let ChcExpr::Op(ChcOp::BvExtract(hi, lo), input) = bit[0].as_ref() else {
                    panic!()
                };
                assert_eq!(hi, lo);
                assert_eq!(input[0].as_ref(), &ChcExpr::Var(target.clone()));
                linked.push(*lo);
            }
            assert_eq!(linked, (0..width).collect::<Vec<_>>());
            let clause = HornClause::new(
                body,
                ClauseHead::Predicate(p, vec![ChcExpr::Var(target.clone())]),
            );
            assert_eq!(clause.body.predicates.len(), 1);
            drop(clause);
            drop(source);
            drop(linked);
            budget.charge(0).unwrap();
        }
    });
}

#[test]
fn constants_are_sliced_without_erasing_the_original_field_nodes() {
    with_owner(|budget| {
        for (width, bits) in [(32, 0x80000000u64), (64, 0xfff0000000000000u64)] {
            let word = Expr::bitvec_const(bits, width);
            let roots = [fields(word, width).fp_is_negative()];
            let problem = ChcProblem::new();
            let output = relation(&roots, &[], &problem, budget);
            assert!(matches!(
                output.source().roots()[0].value(),
                ExprValue::FpIsNegative(_)
            ));
            let (body, source) = output.into_parts().unwrap();
            drop(body);
            drop(source);
            budget.charge(0).unwrap();
        }
    });
}

#[test]
fn omitted_mismatched_or_projected_raw_inputs_refuse() {
    let (word, target) = raw_input(32);
    let roots = [fields(word.clone(), 32).fp_is_normal()];
    let wrong = ChcVar::new("raw_x", ChcSort::BitVec(64));
    let projected = word.clone().extract(31, 31);
    let problem = ChcProblem::new();
    with_owner(|budget| {
        assert!(matches!(
            lower_fp_expr_clause(&roots, &[], &problem, budget),
            Err(FpAdapterError::Invalid(_))
        ));
        for binding in [
            FpExprInputBinding {
                source: &word,
                target: &wrong,
            },
            FpExprInputBinding {
                source: &projected,
                target: &target,
            },
        ] {
            assert!(matches!(
                lower_fp_expr_clause(&roots, &[binding], &problem, budget),
                Err(FpAdapterError::Invalid(_))
            ));
        }
    });
}

#[test]
fn compound_nested_and_unchosen_raw_aliases_remain_unsupported() {
    let (word, target) = raw_input(32);
    let arithmetic = word.clone().bvadd(Expr::bitvec_const(0u8, 32));
    let nested = word.clone().extract(31, 0);
    let from_fp = Expr::fp_plus_zero(&crate::Sort::fp(8, 24)).fp_to_ieee_bv();
    let problem = ChcProblem::new();
    let bindings = [FpExprInputBinding {
        source: &word,
        target: &target,
    }];
    with_owner(|budget| {
        for alias in [arithmetic, nested, from_fp] {
            let bad = fields(alias, 32);
            let selected = Expr::ite(
                Expr::true_(),
                Expr::fp_plus_zero(&crate::Sort::fp(8, 24)),
                bad,
            );
            assert!(matches!(
                lower_fp_expr_clause(&[selected.fp_is_zero()], &bindings, &problem, budget),
                Err(FpAdapterError::Unsupported(_))
            ));
        }
    });
}

enum RawOperand {
    Leaf,
    Add,
}

fn native_source_attempt(
    width: u32,
    high: u32,
    low: u32,
    sign_width: u32,
    operand: RawOperand,
    budget: &mut WorkBudget<'_>,
) -> Result<(), FpAdapterError> {
    budget.admit(65_536, 65_536)?;
    let (e, s) = if width == 32 { (8, 24) } else { (11, 53) };
    let mut entries = vec![
        (TermData::Const(Constant::Bool(true)), ay_core::Sort::Bool),
        (TermData::Const(Constant::Bool(false)), ay_core::Sort::Bool),
        (
            TermData::Var("raw_x".into(), 0),
            ay_core::Sort::bitvec(width),
        ),
    ];
    let word = match operand {
        RawOperand::Add => {
            entries.push((
                TermData::App(Symbol::named("bvadd"), vec![TermId(2), TermId(2)]),
                ay_core::Sort::bitvec(width),
            ));
            TermId(3)
        }
        RawOperand::Leaf => TermId(2),
    };
    let sign = TermId(entries.len() as u32);
    entries.push((
        TermData::App(Symbol::indexed("extract", vec![high, low]), vec![word]),
        ay_core::Sort::bitvec(sign_width),
    ));
    let exponent = TermId(entries.len() as u32);
    entries.push((
        TermData::App(
            Symbol::indexed("extract", vec![width - 2, s - 1]),
            vec![word],
        ),
        ay_core::Sort::bitvec(e),
    ));
    let fraction = TermId(entries.len() as u32);
    entries.push((
        TermData::App(Symbol::indexed("extract", vec![s - 2, 0]), vec![word]),
        ay_core::Sort::bitvec(s - 1),
    ));
    let fp = TermId(entries.len() as u32);
    entries.push((
        TermData::App(Symbol::named("fp"), vec![sign, exponent, fraction]),
        ay_core::Sort::FloatingPoint(e, s),
    ));
    let root = TermId(entries.len() as u32);
    entries.push((
        TermData::App(Symbol::named("fp.isNormal"), vec![fp]),
        ay_core::Sort::Bool,
    ));
    let terms = TermStore::from_entries_with_progress(
        &entries,
        Some(TermId(0)),
        Some(TermId(1)),
        entries.len() as u32,
        &mut |work, bytes| budget.admit(work, bytes).is_ok(),
    )
    .unwrap();
    let target = ChcVar::new("raw_x", ChcSort::BitVec(width));
    let bindings = [ay_chc::fp_adapter::FpInputBinding {
        source: TermId(2),
        target: &target,
    }];
    let roots = [root];
    let namespace = ChcProblem::new();
    let result = ay_chc::fp_adapter::lower_fp_clause(&terms, &roots, &bindings, &namespace, budget);
    let result = result.map(|data| drop(data));
    drop(terms);
    drop(entries);
    budget.charge(0)?;
    result
}

#[test]
fn native_validator_refuses_bad_ranges_widths_and_compound_words() {
    with_owner(|budget| {
        for width in [32, 64] {
            assert!(native_source_attempt(
                width,
                width - 1,
                width - 1,
                1,
                RawOperand::Leaf,
                budget
            )
            .is_ok());
            for (high, low, sort) in [
                (width, width, 1),
                (0, 1, 1),
                (width - 1, width - 2, 1),
                (width - 1, width - 1, 2),
            ] {
                assert!(
                    native_source_attempt(width, high, low, sort, RawOperand::Leaf, budget)
                        .is_err()
                );
            }
            assert!(
                native_source_attempt(width, width - 1, width - 1, 1, RawOperand::Add, budget)
                    .is_err()
            );
        }
    });
}
