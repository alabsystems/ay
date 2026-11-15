// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::tests::{certificate, original, TestResult};
use super::*;

fn problem(width: u32, length: u32, sibling: &str, last: u32) -> String {
    let start = format!("(bvsub stack (_ bv{length} {width}))");
    let mut memory = "memory".to_owned();
    for offset in 0..length {
        let offset = if offset + 1 == length { last } else { offset };
        memory = format!("(store {memory} (bvadd {start} (_ bv{offset} {width})) value)");
    }
    format!(
        "(set-logic QF_ABV)
        (declare-const stack (_ BitVec {width}))
        (declare-const observe (_ BitVec {width}))
        (declare-const value (_ BitVec 8))
        (declare-const other Bool)
        (declare-const memory (Array (_ BitVec {width}) (_ BitVec 8)))
        (assert (and (bvuge stack (_ bv{length} {width}))
          (not (and {sibling}
            (or (not (or (bvult observe {start}) (bvuge observe stack)))
                (= (select {memory} observe) (select memory observe)))))))
        (check-sat)"
    )
}

#[test]
fn local_property_is_discharged_before_full_conjunction_replay() -> TestResult {
    for (width, length) in [(9, 2), (64, 2), (64, 48), (128, 2)] {
        let problem = problem(width, length, "(= value value)", length - 1);
        let (context, _, negative) = original(&problem)?;
        assert!(
            crate::checker::bv_bitblast::proof_producing_control::outside_frame_candidate(
                &context.terms,
                &[negative]
            )
            .is_some()
        );
        certificate(&format!("local-outside-{width}-{length}"), &problem)?;
    }
    Ok(())
}

#[test]
fn false_sibling_and_unproved_local_properties_cannot_be_dropped() -> TestResult {
    let good = problem(9, 2, "true", 1);
    for problem in [
        problem(9, 2, "other", 1),
        problem(9, 2, "true", 2),
        good.replace("(bvuge stack (_ bv2 9))", "true"),
    ] {
        let (context, _, negative) = original(&problem)?;
        assert!(AlethePrinter::new(&context.terms)
            .format_bv_circuit_refutation(ProofId(7), &[negative])
            .is_none());
    }
    Ok(())
}

#[test]
fn normalized_guards_and_siblings_preserve_negative_controls() {
    let good = problem(9, 2, "true", 1);
    for problem in [
        problem(9, 2, "other", 1),
        problem(9, 2, "true", 2),
        good.replace("(bvuge stack (_ bv2 9))", "(bvule stack (_ bv2 9))"),
    ] {
        let mut context = ay_frontend::Context::new();
        for command in ay_frontend::parse(&problem).unwrap() {
            context.process_command(&command).unwrap();
        }
        let root = context.assertions[0];
        let negative = context.terms.mk_not_raw(root);
        assert!(!crate::recognize_bv_bitblast(&context.terms, &[negative]));
        assert!(AlethePrinter::new(&context.terms)
            .format_bv_circuit_refutation(ProofId(7), &[negative])
            .is_none());
    }
}

#[test]
fn reversed_disjunctions_and_nary_guards_have_checked_steps() -> TestResult {
    fn reorder(terms: &mut ay_core::TermStore, term: TermId) -> TermId {
        match terms.get(term).clone() {
            TermData::Not(child) => {
                let child = reorder(terms, child);
                terms.mk_not_raw(child)
            }
            TermData::App(Symbol::Named(op), args) if op == "and" || op == "or" => {
                let mut args: Vec<_> = args.into_iter().map(|a| reorder(terms, a)).collect();
                if op == "or" {
                    args.reverse();
                }
                terms.mk_app(Symbol::Named(op), args, Sort::Bool)
            }
            TermData::App(Symbol::Named(op), args) if op == "bvuge" || op == "bvult" => {
                let op = if op == "bvuge" { "bvule" } else { "bvugt" };
                terms.mk_app(Symbol::named(op), [args[1], args[0]], Sort::Bool)
            }
            _ => term,
        }
    }
    for (width, length) in [(9, 2), (64, 48)] {
        let source = problem(width, length, "true", length - 1)
            .replace("(assert (and ", "(assert (and other ");
        let (mut context, root, _) = original(&source)?;
        let root = reorder(&mut context.terms, root);
        let rendered = AlethePrinter::new(&context.terms).format_term(root);
        let declarations = source.split_once("(assert").unwrap().0;
        certificate(
            &format!("reordered-outside-{width}-{length}"),
            &format!("{declarations}(assert {rendered})\n(check-sat)\n"),
        )?;
    }
    Ok(())
}

#[test]
fn false_counterexample_does_not_hide_malformed_siblings() {
    let mut context = ay_frontend::Context::new();
    for command in ay_frontend::parse(&problem(9, 2, "true", 1)).unwrap() {
        context.process_command(&command).unwrap();
    }
    let root = context.assertions[0];
    let TermData::App(op, args) = context.terms.get(root).clone() else {
        panic!("normalized counterexample conjunction")
    };
    assert_eq!(op.name(), "and");
    let value = context.terms.mk_var("bad_value", Sort::bitvec(8));
    let malformed = context
        .terms
        .mk_app(Symbol::named("bvadd"), [value], Sort::bitvec(8));
    let malformed = context
        .terms
        .mk_app(Symbol::named("="), [malformed, value], Sort::Bool);
    let mistyped = context
        .terms
        .mk_app(Symbol::named("="), [value, value], Sort::bitvec(8));
    for sibling in [malformed, mistyped] {
        let mut children = args.clone();
        children.push(sibling);
        let root = context.terms.mk_app(op.clone(), children, Sort::Bool);
        let negative = context.terms.mk_not_raw(root);
        assert!(!crate::recognize_bv_bitblast(&context.terms, &[negative]));
        assert!(AlethePrinter::new(&context.terms)
            .format_bv_circuit_refutation(ProofId(7), &[negative])
            .is_none());
    }
}

#[test]
fn local_property_preserves_sibling_validation_and_effective_source() -> TestResult {
    let problem = problem(9, 2, "true", 1);
    let (mut context, root, _) = original(&problem)?;
    let negative = context.terms.mk_not_raw(root);
    let shape = crate::checker::bv_bitblast::proof_producing_control::outside_frame_candidate(
        &context.terms,
        &[negative],
    )
    .unwrap();
    let (guard, property) = (shape.guard, shape.property);
    let mut overrides = DetHashMap::default();
    overrides.insert(property, "false".into());
    let negative = context.terms.mk_not_raw(root);
    assert!(
        AlethePrinter::new_with_overrides(&context.terms, Some(&overrides))
            .format_bv_circuit_refutation(ProofId(7), &[negative])
            .is_none()
    );
    let printer = AlethePrinter::new_with_overrides_and_budget(&context.terms, None, Some(1024));
    assert!(printer
        .format_bv_circuit_refutation(ProofId(7), &[negative])
        .is_none());
    assert!(printer.work_budget_exhausted());
    // Proving one property must not bypass a malformed sibling expression.
    let value = context.terms.mk_var("v", Sort::bitvec(8));
    let bad = context
        .terms
        .mk_app(Symbol::named("bvadd"), [value], Sort::bitvec(8));
    let bad_eq = context
        .terms
        .mk_app(Symbol::named("="), [bad, bad], Sort::Bool);
    let body = context
        .terms
        .mk_app(Symbol::named("and"), [bad_eq, property], Sort::Bool);
    let no = context.terms.mk_not_raw(body);
    let query = context
        .terms
        .mk_app(Symbol::named("and"), [guard, no], Sort::Bool);
    let negative = context.terms.mk_not_raw(query);
    assert!(AlethePrinter::new(&context.terms)
        .format_bv_circuit_refutation(ProofId(7), &[negative])
        .is_none());
    Ok(())
}

#[test]
fn local_property_rejects_mistyped_internal_equality() -> TestResult {
    let problem = problem(9, 2, "true", 1);
    let (mut context, _, negative) = original(&problem)?;
    let shape = crate::checker::bv_bitblast::proof_producing_control::outside_frame_candidate(
        &context.terms,
        &[negative],
    )
    .unwrap();
    let TermData::App(_, args) = context.terms.get(shape.property).clone() else {
        panic!("property")
    };
    let TermData::App(op, reads) = context.terms.get(args[1]).clone() else {
        panic!("equality")
    };
    let bad = context.terms.mk_app(op, reads, Sort::bitvec(8));
    let property = context
        .terms
        .mk_app(Symbol::named("or"), [args[0], bad], Sort::Bool);
    let no = context.terms.mk_not_raw(property);
    let root = context
        .terms
        .mk_app(Symbol::named("and"), [shape.guard, no], Sort::Bool);
    let negative = context.terms.mk_not_raw(root);
    assert!(AlethePrinter::new(&context.terms)
        .format_bv_circuit_refutation(ProofId(7), &[negative])
        .is_none());
    Ok(())
}
