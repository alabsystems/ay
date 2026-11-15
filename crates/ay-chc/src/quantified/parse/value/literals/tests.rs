// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::unwrap_used)]

use super::*;
use num_traits::{One, ToPrimitive};

fn sexp(text: &str) -> SExpr {
    let mut values = ay_frontend::sexp::parse_sexps(text).unwrap();
    assert_eq!(values.len(), 1);
    values.pop().unwrap()
}

fn parse(text: &str) -> Arc<ChcExpr> {
    literal(&sexp(text), &mut Budget::default())
        .unwrap()
        .unwrap()
}

// Independent positional oracle: visits only raw leaves/concats and appends
// every leaf's declared bits in source operand order. It does not use AY's
// evaluator or literal constructor (which have modulo semantics).
fn number(expression: &ChcExpr) -> (BigUint, u32, usize) {
    let mut pending = vec![(expression, 0usize)];
    let mut value = BigUint::default();
    let mut width = 0_u32;
    let mut depth = 0usize;
    while let Some((expr, level)) = pending.pop() {
        depth = depth.max(level);
        match expr {
            ChcExpr::BitVec(bits, size) => {
                assert!((1..=128).contains(size));
                assert!(BigUint::from(*bits).bits() <= u64::from(*size));
                value = (value << *size) | BigUint::from(*bits);
                width += size;
            }
            ChcExpr::Op(ChcOp::BvConcat, children) => {
                assert_eq!(children.len(), 2);
                pending.push((&children[1], level + 1));
                pending.push((&children[0], level + 1));
            }
            _ => panic!("literal introduced a nonliteral operation"),
        }
    }
    (value, width, depth)
}

#[test]
fn exact_wide_literals_agree_across_decimal_binary_and_hexadecimal() {
    for width in [65_u32, 72, 127, 128, 129, 136, 256, 513] {
        let expected = (BigUint::one() << (width - 1)) | BigUint::from(0x35_u32);
        let decimal = parse(&format!("(_ bv{expected} {width})"));
        let binary = parse(&format!("#b{}", expected.to_str_radix(2)));
        assert_eq!(number(&decimal).0, expected);
        assert_eq!(number(&decimal).1, width);
        assert_eq!(number(&binary), number(&decimal));
        if width % 4 == 0 {
            let hex = parse(&format!("#x{}", expected.to_str_radix(16)));
            assert_eq!(number(&hex), number(&decimal));
            assert_eq!(
                *hex, *decimal,
                "equivalent literal spellings have one chunk layout"
            );
        }
        if width <= 128 {
            assert_eq!(
                *decimal,
                ChcExpr::BitVec(expected.to_u128().unwrap(), width)
            );
        }
    }
}

#[test]
fn high_bits_and_non_chunk_aligned_leading_zeroes_survive() {
    let high = parse("#x8000000000000000000000000000000007");
    let low = parse("#x0000000000000000000000000000000007");
    assert_ne!(number(&high).0, number(&low).0);
    assert_eq!(number(&high).1, 136);
    assert_eq!(number(&low).1, 136);
    for width in [129, 130, 255, 257] {
        let zero = parse(&format!("(_ bv0000 {width})"));
        let seven = parse(&format!("(_ bv0007 {width})"));
        assert_eq!(number(&zero).0, BigUint::default());
        assert_eq!(number(&seven).0, BigUint::from(7_u32));
        assert_eq!(number(&seven).1, width);
    }
}

#[test]
fn maximum_width_zero_uses_a_balanced_not_linear_concat_tree() {
    let width = crate::MAX_BITVECTOR_WIDTH;
    let expr = parse(&format!("(_ bv0 {width})"));
    let (value, actual, depth) = number(&expr);
    assert_eq!(value, BigUint::default());
    assert_eq!(actual, width);
    assert_eq!(depth, 13);
    assert_eq!(expr.sort(), ChcSort::BitVec(width));
}

#[test]
fn declared_overflow_and_invalid_raw_syntax_refuse_without_modulo() {
    for width in [1_u32, 64, 128, 129, 136, 256] {
        let overflow = BigUint::one() << width;
        for text in [
            format!("(_ bv{overflow} {width})"),
            format!("(_ bv-1 {width})"),
            format!("(_ bv+1 {width})"),
        ] {
            assert!(
                literal(&sexp(&text), &mut Budget::default()).is_err(),
                "{text}"
            );
        }
    }
    for expr in [
        SExpr::Binary("#b1012".into()),
        SExpr::Hexadecimal("#x0z".into()),
        SExpr::List(vec![
            SExpr::Symbol("_".into()),
            SExpr::Symbol("bv1".into()),
            SExpr::Numeral("0129".into()),
        ]),
        sexp("(_ bv1 0)"),
        sexp("(_ bv1 1048577)"),
        sexp("(_ bv1 4294967296)"),
        sexp("(_ bv1 129 extra)"),
    ] {
        assert!(matches!(
            literal(&expr, &mut Budget::default()),
            Err(crate::ChcError::Parse(_))
        ));
    }
}

#[test]
fn all_literal_costs_share_one_parser_ledger_and_refuse_before_construction() {
    let expr = sexp("(_ bv1361129467683753853853498429727072845825 136)");
    let mut measured = Budget::default();
    let expected = literal(&expr, &mut measured).unwrap().unwrap();
    assert!(measured.work > 2 * 40);
    assert!(measured.bytes > 256);
    for (work_short, bytes_short) in [(0, 0), (1, 0), (0, 1)] {
        let mut budget = Budget {
            work: super::super::super::MAX_WORK - measured.work + work_short,
            bytes: super::super::super::MAX_COPY_BYTES - measured.bytes + bytes_short,
        };
        let result = literal(&expr, &mut budget);
        if work_short == 0 && bytes_short == 0 {
            assert_eq!(result.unwrap().unwrap(), expected);
        } else {
            assert!(result.is_err());
            assert!(
                literal(&expr, &mut budget).is_err(),
                "an exhausted ledger cannot restart"
            );
        }
    }
    assert_eq!(
        literal(&expr, &mut Budget::default()).unwrap().unwrap(),
        expected
    );
}

#[test]
fn numeric_conversion_and_input_scans_cannot_bypass_shared_work_limit() {
    // Raw SExpr deliberately bypasses lexical text size admission. Conversion
    // of this otherwise fitting decimal would exceed the fixed work ledger.
    let huge = SExpr::List(vec![
        SExpr::Symbol("_".into()),
        SExpr::Symbol(format!("bv{}", "9".repeat(10_000))),
        SExpr::Numeral("40000".into()),
    ]);
    let mut budget = Budget::default();
    assert!(literal(&huge, &mut budget).is_err());
    assert!(budget.work > super::super::super::MAX_WORK);
    let zeros = SExpr::List(vec![
        SExpr::Symbol("_".into()),
        SExpr::Symbol(format!("bv{}", "0".repeat(super::super::super::MAX_WORK))),
        SExpr::Numeral("1".into()),
    ]);
    let mut budget = Budget::default();
    assert!(literal(&zeros, &mut budget).is_err());
    assert_eq!(
        budget.bytes, 0,
        "digit scanning refuses before numeric/AST allocation"
    );
    assert_eq!(number(&parse("(_ bv1 136)")).0, BigUint::one());
}

#[test]
fn wide_key_cell_operations_and_ascriptions_remain_exactly_typed() {
    let key = ChcSort::BitVec(136);
    let cell = ChcSort::BitVec(256);
    let array = ChcSort::Array(Box::new(key.clone()), Box::new(cell.clone()));
    let zero = parse("(_ bv0 256)");
    let (constant, actual) = super::super::application(
        &sexp("(as const (Array (_ BitVec 136) (_ BitVec 256)))"),
        vec![zero.clone()],
        &[cell.clone()],
    )
    .unwrap();
    assert_eq!(actual, array);
    assert!(
        matches!(constant.as_ref(), ChcExpr::ConstArray(actual, child) if actual == &key && Arc::ptr_eq(child, &zero))
    );
    let index = parse("(_ bv680564733841876926926749214863536422913 136)");
    let (selected, actual) = super::super::application(
        &SExpr::Symbol("select".into()),
        vec![constant, index],
        &[array, key],
    )
    .unwrap();
    assert_eq!(actual, cell);
    assert!(matches!(selected.as_ref(), ChcExpr::Op(ChcOp::Select, _)));
    assert!(super::super::application(
        &sexp("(as const (Array (_ BitVec 136) (_ BitVec 255)))"),
        vec![zero],
        &[cell],
    )
    .is_err());
}

#[test]
fn wide_indexed_results_keep_the_existing_crate_width_ceiling() {
    let input = Arc::new(ChcExpr::BitVec(1, 128));
    for (head, width) in [
        ("(_ zero_extend 8)", 136),
        ("(_ sign_extend 128)", 256),
        ("(_ repeat 3)", 384),
    ] {
        let (value, actual) =
            super::super::application(&sexp(head), vec![input.clone()], &[ChcSort::BitVec(128)])
                .unwrap();
        assert_eq!(actual, ChcSort::BitVec(width));
        assert!(
            matches!(value.as_ref(), ChcExpr::Op(_, children) if Arc::ptr_eq(&children[0], &input))
        );
    }
    for head in [
        "(_ zero_extend 1048449)",
        "(_ sign_extend 4294967295)",
        "(_ repeat 8193)",
        "(_ extract 128 0)",
    ] {
        assert!(super::super::application(
            &sexp(head),
            vec![input.clone()],
            &[ChcSort::BitVec(128)]
        )
        .is_err());
    }
}

#[test]
fn real_term_entry_uses_its_existing_budget_not_a_fresh_literal_budget() {
    use super::super::super::{Dialect, Parser, Phase, MAX_COPY_BYTES};
    let make = || Parser {
        declarations: crate::ChcProblem::new(),
        functions: Default::default(),
        records: Default::default(),
        clauses: Vec::new(),
        bindings: Default::default(),
        reserved: Default::default(),
        fresh: 0,
        qf: Default::default(),
        budget: Budget::default(),
        dialect: Dialect::Unset,
        phase: Phase::Declarations,
        logic_seen: false,
    };
    let expr = sexp("(_ bv1361129467683753853853498429727072845825 136)");
    let mut measured = make();
    let value = measured.term(&expr, 0).unwrap();
    assert!(matches!(
        value.as_ref(),
        super::super::super::Term::Value(_, ChcSort::BitVec(136))
    ));
    let needed = measured.budget.bytes;
    for shortfall in [0, 1] {
        let mut parser = make();
        parser.budget.bytes = MAX_COPY_BYTES - needed + shortfall;
        assert_eq!(parser.term(&expr, 0).is_ok(), shortfall == 0);
        assert!(
            parser.term(&expr, 0).is_err(),
            "subsequent literals share the exhausted allowance"
        );
    }
    assert!(make().term(&expr, 0).is_ok());
}

#[test]
fn textual_wide_state_preserves_raw_later_binders_but_not_wide_premise_binders() {
    use crate::quantified::QuantifiedChcProblem;
    let source = "(declare-rel P ((_ BitVec 136)))
      (rule (P (_ bv1361129467683753853853498429727072845825 136)))
      (query (P (_ bv1361129467683753853853498429727072845825 136)))";
    let problem = QuantifiedChcProblem::parse_smtlib(source).unwrap();
    assert!(problem.source_smtlib().contains("(_ BitVec 136)"));
    assert!(problem.source_smtlib().contains("(concat "));
    // The rendered canonical source is always HORN; only the `; fixedpoint=`
    // header records the original dialect, and it is deliberately not read
    // back (see `counterexample/trace/artifact.rs`: "parser binder freshening
    // and fixedpoint provenance are not idempotent", pinned by
    // `caller_source_not_reparsed_wire_controls_binders_and_fixedpoint_provenance`).
    // Everything else -- including the wide 136-bit `concat` literal -- must
    // round-trip byte for byte, and the HORN rendering must then be an exact
    // fixed point of parse+render.
    let roundtrip = QuantifiedChcProblem::parse_smtlib(problem.source_smtlib()).unwrap();
    assert_eq!(
        roundtrip.source_smtlib(),
        problem
            .source_smtlib()
            .replace("; fixedpoint=true\n", "; fixedpoint=false\n")
    );
    let again = QuantifiedChcProblem::parse_smtlib(roundtrip.source_smtlib()).unwrap();
    assert_eq!(again.source_smtlib(), roundtrip.source_smtlib());
    for width in [64, 65, 136] {
        let source = format!(
            "(declare-rel P ())
          (rule (=> (forall ((i (_ BitVec {width}))) (= i i)) P)) (query P)"
        );
        assert_eq!(
            QuantifiedChcProblem::parse_smtlib(&source).is_ok(),
            width == 64
        );
    }
}
