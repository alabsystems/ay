// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `EVALUATED_OPERATORS`: a closed index the printer can only spell in a form
//! pinned Carcara refuses is never evaluated, so the lane declines.

use super::*;

/// [`NEWEST_HIT`] at `width` bits with the hitting write's index spelled
/// `index`, a closed term equal to `#x40`.
fn newest_hit_through(index: &str, width: u32) -> String {
    let sort = format!("(_ BitVec {width})");
    let lit = |value: u32| format!("(_ bv{value} {width})");
    format!(
        "(set-option :produce-proofs true)\n(set-logic ALL)\n\
         (declare-datatype Cell ((mk_cell (cell_data (Array {sort} {sort})))))\n\
         (declare-const a (Array {sort} Cell))\n\
         (assert (= (select (store (store (cell_data (select a {nine})) {t} {one}) \
         {index} {two}) {t}) {one}))\n(check-sat)\n",
        nine = lit(9),
        t = lit(0x40),
        one = lit(1),
        two = lit(2),
    )
}

/// NEGATIVE TWIN of the evaluation path: each problem is unsat by exactly the
/// newest-write hit [`NEWEST_HIT`] proves through `(bvadd #x3f #x01)`, but
/// its closed index is a quotient, a remainder by zero or a zero extension.
/// Pinned Carcara refuses the `bitblast_udiv`/`bitblast_urem` steps and the
/// `zero_extend`/`concat` reflexivity the printer spells for those, and the
/// wire screen cannot see a refusal, so the lane must not propose the edge:
/// the verdict stays `unknown` and a placeholder stays untouched.
/// Counterfactual (measured on 938ec0327): with `bvudiv`, `bvurem` and
/// `zero_extend` in `EVALUATED_OPERATORS` each answers `unsat` with a
/// Carcara-`invalid` document.
#[test]
fn a_closed_division_or_zero_extension_index_is_not_evaluated() {
    for (index, width) in [
        ("(bvudiv (_ bv128 8) (_ bv2 8))", 8),
        ("(bvurem (_ bv64 8) (_ bv0 8))", 8),
        ("((_ zero_extend 1) (_ bv64 15))", 16),
    ] {
        let mut exec = solved(&newest_hit_through(index, width), "unknown");
        let mut proof = placeholder();
        let before = format!("{:?}", proof.steps);
        exec.replace_with_raw_authored_ground_closure_refutation(&mut proof);
        assert_eq!(format!("{:?}", proof.steps), before, "{index}");
    }
}

/// The positive control: the same shape through an evaluated operator
/// (`bvsub`, `extract`) is still refuted, so the test above is not vacuous.
#[test]
fn a_closed_subtraction_or_extraction_index_is_still_evaluated() {
    for (index, width) in [
        ("(bvsub (_ bv65 8) (_ bv1 8))", 8),
        ("((_ extract 15 0) (_ bv64 24))", 16),
    ] {
        let exec = solved(&newest_hit_through(index, width), "unsat");
        assert!(exec.last_proof().is_some(), "{index}");
    }
}

#[test]
fn closed_value_proposals_do_not_spend_probes_guessing_other_constants() {
    for (operator, left, right, expected) in [
        ("bvadd", 255, Some(2), 1),
        ("bvsub", 0, Some(1), 255),
        ("bvmul", 200, Some(3), 88),
        ("bvshl", 1, Some(7), 128),
        ("bvlshr", 128, Some(7), 1),
        ("bvneg", 1, None, 255),
        ("bvnot", 1, None, 254),
        ("bvand", 170, Some(15), 10),
        ("bvor", 160, Some(5), 165),
        ("bvxor", 170, Some(15), 165),
    ] {
        let mut exec = Executor::new();
        let mut closure = GroundClosure::default();
        let constants: Vec<_> = (0..256)
            .map(|value| {
                let constant = exec.ctx.terms.mk_bitvec(value.into(), 8);
                assert!(closure.register(constant));
                constant
            })
            .collect();
        let mut args = vec![constants[left]];
        if let Some(right) = right {
            args.push(constants[right]);
        }
        let term = exec
            .ctx
            .terms
            .mk_app(Symbol::named(operator), args, Sort::bitvec(8));
        assert!(closure.register(term));
        let mut budget = 1;
        exec.add_ground_evaluation_edges(&mut closure, &[term], &mut budget);
        assert!(closure.same_class(term, constants[expected]), "{operator}");
        assert_eq!(budget, 0, "the actual semantic check still pays its probe");
    }
}

#[test]
fn closed_value_hints_do_not_create_constants_or_bypass_zero_probes() {
    for budget in [0, 1] {
        let mut exec = Executor::new();
        let mut closure = GroundClosure::default();
        let one = exec.ctx.terms.mk_bitvec(1.into(), 8);
        let two = exec.ctx.terms.mk_bitvec(2.into(), 8);
        let term = exec
            .ctx
            .terms
            .mk_app(Symbol::named("bvadd"), [one, one], Sort::bitvec(8));
        assert!(closure.register(one));
        assert!(closure.register(term));
        if budget == 0 {
            assert!(closure.register(two));
        }
        let nodes = closure.nodes().len();
        let mut remaining = budget;
        exec.add_ground_evaluation_edges(&mut closure, &[term], &mut remaining);
        assert!(!closure.same_class(term, one));
        assert!(!closure.same_class(term, two));
        assert!(closure.edges().is_empty());
        assert_eq!(closure.nodes().len(), nodes);
        assert_eq!(remaining, budget);
    }
}
