// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_chc::{SmtContext, SmtResult};
use std::sync::Arc;

mod ownership;
mod refusal;
mod semantics;

#[derive(Clone, Copy)]
enum Kind {
    Signed,
    Unsigned,
}

fn cast(word: Expr, kind: Kind, width: u32) -> Expr {
    let (e, s) = if width == 32 { (8, 24) } else { (11, 53) };
    match kind {
        Kind::Signed => word.try_bv_to_fp(RoundingMode::RNE, e, s).unwrap(),
        Kind::Unsigned => word.try_bv_to_fp_unsigned(RoundingMode::RNE, e, s).unwrap(),
    }
}

fn fields(bits: u64, width: u32) -> Expr {
    let e = if width == 32 { 8 } else { 11 };
    let word = Expr::bitvec_const(bits, width);
    Expr::fp_from_bvs(
        word.clone().extract(width - 1, width - 1),
        word.clone().extract(width - 2, width - e - 1),
        word.extract(width - e - 2, 0),
    )
}

fn solve(
    roots: &[Expr],
    inputs: &[(Expr, ChcVar, u64, u32)],
    expected: bool,
    budget: &mut WorkBudget<'_>,
    end: Instant,
) {
    budget.admit(1_048_576, 1_048_576).unwrap();
    let problem = ChcProblem::new();
    let bindings: Vec<_> = inputs
        .iter()
        .map(|(source, target, _, _)| FpExprInputBinding { source, target })
        .collect();
    let pins: Vec<_> = inputs
        .iter()
        .map(|(_, target, raw, width)| {
            Arc::new(ChcExpr::Op(
                ChcOp::Eq,
                vec![
                    Arc::new(ChcExpr::Var(target.clone())),
                    Arc::new(ChcExpr::BitVec(u128::from(*raw), *width)),
                ],
            ))
        })
        .collect();
    {
        let data = lower_fp_expr_clause(roots, &bindings, &problem, budget).unwrap();
        let old = ClauseBody::constraint(ChcExpr::Op(ChcOp::And, pins));
        let (body, source) = data.into_body(old).unwrap().into_parts().unwrap();
        assert!(std::ptr::eq(source.roots(), roots));
        assert_eq!(source.bindings().len(), inputs.len());
        budget.charge(0).unwrap();
        let mut native = SmtContext::new();
        native.set_term_memory_budget(Some(128 * 1024 * 1024));
        let remaining = end.saturating_duration_since(Instant::now());
        assert!(!remaining.is_zero());
        let result = native.check_sat_with_timeout(body.constraint.as_ref().unwrap(), remaining);
        if expected {
            assert!(matches!(result, SmtResult::Sat(_)));
        } else {
            assert!(result.is_unsat());
        }
        drop(result);
        drop(native);
        drop(body);
    }
    budget.charge(0).unwrap();
}

fn word_case(
    n: u32,
    raw: u64,
    out: u32,
    kind: Kind,
    expected: u64,
    budget: &mut WorkBudget<'_>,
    end: Instant,
) {
    budget.admit(1_048_576, 1_048_576).unwrap();
    let word = Expr::var("numeric_word", crate::Sort::bitvec(n));
    let input = [(
        word.clone(),
        ChcVar::new("numeric_word", ChcSort::BitVec(n)),
        raw,
        n,
    )];
    let equal = cast(word, kind, out).eq(fields(expected, out));
    solve(&[equal.clone()], &input, true, budget, end);
    solve(&[equal.not()], &input, false, budget, end);
}

struct Fixture {
    roots: [Expr; 1],
    problem: ChcProblem,
}
impl Fixture {
    fn new() -> Self {
        Self {
            roots: [cast(Expr::bitvec_const(127u8, 8), Kind::Signed, 32).fp_is_normal()],
            problem: ChcProblem::new(),
        }
    }
    fn attempt(&self, budget: &mut WorkBudget<'_>) -> Result<(), FpAdapterError> {
        {
            let data = lower_fp_expr_clause(&self.roots, &[], &self.problem, budget)?;
            let (body, _source) = data.into_body(ClauseBody::empty())?.into_parts()?;
            drop(body);
        }
        budget.charge(0)?;
        Ok(())
    }
}

fn assert_word_link(entry: &ChcExpr, bit: u32, target: &ChcVar) {
    let ChcExpr::Op(ChcOp::Eq, pair) = entry else {
        panic!()
    };
    let ChcExpr::Op(ChcOp::Eq, value) = pair[1].as_ref() else {
        panic!()
    };
    let ChcExpr::Op(ChcOp::BvExtract(high, low), word) = value[0].as_ref() else {
        panic!()
    };
    assert_eq!((*high, *low), (bit, bit));
    assert_eq!(word[0].as_ref(), &ChcExpr::Var(target.clone()));
    assert_eq!(value[1].as_ref(), &ChcExpr::BitVec(1, 1));
}

#[test]
fn numeric_eight_bit_links_and_repeated_source_identity_survive_complete_move() {
    raw_words::native::original_owner(|budget, _| {
        budget.admit(1_048_576, 1_048_576).unwrap();
        let word = Expr::var("numeric_link", crate::Sort::bitvec(8));
        let target = ChcVar::new("numeric_link", ChcSort::BitVec(8));
        let root = cast(word.clone(), Kind::Signed, 32).fp_is_normal();
        let roots = [root.clone(), root];
        let bindings = [FpExprInputBinding {
            source: &word,
            target: &target,
        }];
        let problem = ChcProblem::new();
        {
            let data = lower_fp_expr_clause(&roots, &bindings, &problem, budget).unwrap();
            let (body, source) = data
                .into_body(ClauseBody::empty())
                .unwrap()
                .into_parts()
                .unwrap();
            assert!(std::ptr::eq(source.roots(), roots.as_slice()));
            assert!(std::ptr::eq(source.bindings()[0].source, &raw const word));
            let ChcExpr::Op(ChcOp::And, outer) = body.constraint.as_ref().unwrap() else {
                panic!()
            };
            let ChcExpr::Op(ChcOp::And, entries) = outer[0].as_ref() else {
                panic!()
            };
            for (bit, entry) in entries.iter().skip(entries.len() - 8).enumerate() {
                budget.charge(256).unwrap();
                assert_word_link(entry, bit as u32, &target);
            }
            drop(body);
        }
        budget.charge(0).unwrap();
    });
}
