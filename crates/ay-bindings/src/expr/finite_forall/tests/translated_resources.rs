// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[derive(Clone, Copy)]
enum IndexCase {
    Direct,
    Literal,
    Variable,
}

fn read_index(case: IndexCase, reverse: bool) -> Expr {
    let offset = match case {
        IndexCase::Direct => return index(),
        IndexCase::Literal => Expr::bitvec_const(3, 64),
        IndexCase::Variable => Expr::var("o", Sort::bitvec(64)),
    };
    if reverse {
        offset.bvsub(index())
    } else {
        index().bvadd(offset)
    }
}

fn body(case: IndexCase, reverse: bool, name: &str, upper: u64) -> Expr {
    index().bvult(Expr::bitvec_const(upper, 64)).implies(
        array(name, Sort::bool())
            .select(read_index(case, reverse))
            .eq(Expr::true_()),
    )
}

#[test]
fn direct_and_translated_constructor_work_limits_have_exact_distinct_costs() {
    for (case, input, output) in [
        (IndexCase::Direct, 17, 11),
        (IndexCase::Literal, 19, 14),
        (IndexCase::Variable, 23, 14),
    ] {
        let instances = (MAX_WORK - input) / output;
        let padding = MAX_WORK - (input + output * instances);
        let exact_name = "a".repeat(padding + 1);
        let over_name = "a".repeat(padding + 2);
        for reverse in [false, true] {
            let exact = body(case, reverse, &exact_name, instances as u64);
            let result = quantify(exact.clone());
            assert!(matches!(result.value(), ExprValue::And(args) if args.len() == instances));
            retained(body(case, reverse, &over_name, instances as u64));
            retained(body(case, reverse, "a", instances as u64 + 1));
            // Both refusals are local: the exact same admitted input can retry.
            let retry = quantify(exact);
            assert!(matches!(retry.value(), ExprValue::And(args) if args.len() == instances));
        }
    }
}

fn two_read_body(name: &str, upper: u64) -> Expr {
    index().bvult(Expr::bitvec_const(upper, 64)).implies(
        array(name, Sort::bool())
            .select(index().bvadd(Expr::bitvec_const(3, 64)))
            .eq(array("b", Sort::bool()).select(Expr::bitvec_const(5, 64).bvsub(index()))),
    )
}

#[test]
fn two_translated_reads_pay_both_translation_output_and_input_costs() {
    // Two literal translations cost 27 input units and 17 per output equality.
    let instances = (MAX_WORK - 27) / 17;
    let padding = MAX_WORK - (27 + 17 * instances);
    assert_eq!(instances, 3853);
    assert_eq!(padding, 8);
    let exact = two_read_body(&"a".repeat(padding + 1), instances as u64);
    let result = quantify(exact.clone());
    assert!(matches!(result.value(), ExprValue::And(args) if args.len() == instances));
    retained(two_read_body(&"a".repeat(padding + 2), instances as u64));
    retained(two_read_body("a", instances as u64 + 1));
    assert!(matches!(quantify(exact).value(), ExprValue::And(args) if args.len() == instances));
}

#[test]
fn equality_output_charge_counts_translations_and_respects_its_own_limit() {
    let read = |at| array("a", Sort::bool()).select(at);
    for (equality, cost) in [
        (read(index()).eq(Expr::true_()), 11),
        (
            read(index().bvadd(Expr::bitvec_const(3, 64))).eq(Expr::true_()),
            14,
        ),
        (
            read(index().bvadd(Expr::bitvec_const(3, 64)))
                .eq(read(Expr::bitvec_const(5, 64).bvsub(index()))),
            17,
        ),
    ] {
        let mut parser_budget = Budget::new();
        let parsed =
            Equality::parse(&equality, "i", 64, &mut parser_budget).expect("admitted equality");
        assert_eq!(parsed.output_cost(), Some(cost));

        // The public work ceiling includes parsing and binds before the output
        // ceiling. Isolate the real output ledger to pin that second boundary.
        let mut budget = Budget::new();
        budget.work_left = usize::MAX;
        let instances = MAX_OUTPUT / cost;
        assert_eq!(budget.output(instances * cost), Some(()));
        let remainder = MAX_OUTPUT - instances * cost;
        assert_eq!(budget.output(remainder), Some(()));
        assert_eq!(budget.output_left, 0);
        assert_eq!(budget.output(1), None);
        assert_eq!(Budget::new().output(cost), Some(()));
    }
}

#[test]
fn translated_offset_name_limit_applies_even_without_output_instances() {
    let make = |name: &str, upper| {
        index().bvult(Expr::bitvec_const(upper, 64)).implies(
            array("a", Sort::bool())
                .select(index().bvadd(Expr::var(name, Sort::bitvec(64))))
                .eq(Expr::true_()),
        )
    };
    for upper in [0, 1] {
        let exact_name = "o".repeat(MAX_NAME_BYTES);
        let exact = quantify(make(&exact_name, upper));
        if upper == 0 {
            assert!(matches!(exact.value(), ExprValue::BoolConst(true)));
        } else {
            assert!(matches!(exact.value(), ExprValue::And(args) if args.len() == 1));
        }
        retained(make(&"o".repeat(MAX_NAME_BYTES + 1), upper));
    }
    assert!(matches!(quantify(make("o", 1)).value(), ExprValue::And(args) if args.len() == 1));
}

#[test]
fn oversized_translated_output_refuses_without_partial_emission_or_poisoning() {
    let small = body(IndexCase::Literal, false, "a", 2);
    let huge = body(IndexCase::Literal, true, "a", u64::MAX);
    retained(boolean(ExprValue::And(vec![small.clone(), huge])));
    assert!(matches!(quantify(small).value(), ExprValue::And(args) if args.len() == 2));
}
