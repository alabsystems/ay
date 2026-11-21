// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{Sort, Symbol};

const ARRAY_READ_BOUND: &str = r"
    (set-logic AUFLIA)
    (declare-sort S 0)
    (declare-fun data (S) (Array Int Int))
    (declare-const s S)
    (assert (forall ((x S) (i Int))
      (>= (select (data x) i) 0)))
";

fn fixture(extra: &str) -> Executor {
    let mut exec = Executor::new();
    exec.set_self_check(true);
    let commands = ay_frontend::parse(&format!("{ARRAY_READ_BOUND}{extra}")).unwrap();
    exec.execute_all(&commands).unwrap();
    let info = exec.ctx.symbol_info("data").unwrap();
    assert!(exec.is_ordinary_free_primary_declaration("data", info));
    exec.last_model = Some(source_model(&exec));
    exec
}

fn source_model(exec: &Executor) -> Model {
    let mut model = Model::empty();
    let s = exec.ctx.symbol_info("s").unwrap().term.unwrap();
    assert!(Executor::insert_completed_value(
        &exec.ctx.terms,
        &mut model,
        s,
        &EvalValue::Element("@S!0".into())
    ));
    model
}

fn data_symbol(exec: &Executor) -> Symbol {
    let info = exec.ctx.symbol_info("data").unwrap();
    Symbol::named(exec.ctx.symbol_identity_name("data", info))
}

fn term(exec: &mut Executor, spelling: &str) -> TermId {
    let commands = ay_frontend::parse(&format!("(get-value ({spelling}))")).unwrap();
    let ay_frontend::Command::GetValue(terms) = &commands[0] else {
        panic!("getter fixture")
    };
    exec.ctx.elaborate_surface_subterm(&terms[0].1).unwrap()
}

#[test]
fn array_result_qmc_substitution_discharges_universal_read_bound() {
    let mut exec = fixture("");
    let roots = exec.ctx.assertions.clone();
    let leaves = exec.qmc_leaves(&roots).unwrap();
    let interp = exec.model_check_interpretation(&leaves, &roots).unwrap();
    let table = interp
        .tables
        .iter()
        .find(|table| table.symbol == data_symbol(&exec))
        .unwrap();
    assert!(matches!(table.result_sort, Sort::Array(_)));
    assert!(table.rows.is_empty());
    assert_eq!(exec.ctx.terms.sort(table.default), &table.result_sort);
    let fixed = interp.substitute(&mut exec.ctx.terms, leaves[0].body);
    let printed = ay_proof::render_term_canonical(&exec.ctx.terms, fixed);
    assert!(
        !printed.contains("select"),
        "typed read-over-const reduction must expose the scalar fact: {printed}"
    );
    let negated = exec.ctx.terms.mk_not(fixed);
    assert!(
        exec.qmc_refutes(vec![negated], LaneBudget::start(1000)),
        "the constant read bound needs the ordinary checked refutation"
    );
    assert_eq!(exec.finite_model_lane.discharged_trust_refutations, 0);
    assert!(matches!(
        exec.qmc_truth_value(&leaves[0], &interp, LaneBudget::start(1000)),
        TruthOutcome::Determined(true)
    ));
}

#[test]
fn array_result_qmc_certifies_the_original_universal_read_bound() {
    let mut exec = fixture("");
    assert!(exec.try_model_check_sat_certificate());
    assert_eq!(
        exec.last_model
            .as_ref()
            .unwrap()
            .certified_const_interp_entries()
            .len(),
        1
    );
}

#[test]
fn array_result_qmc_boolean_completion_certifies_a_reflexive_relation() {
    let mut exec = fixture(
        "(declare-fun related (S S) Bool) \
         (assert (forall ((x S)) (related x x))) \
         (assert (related s s))",
    );
    assert!(exec.try_model_check_sat_certificate());
    let related = term(&mut exec, "(related s s)");
    let read = term(&mut exec, "(select (data s) 0)");
    let zero = exec.ctx.terms.mk_int(0.into());
    let read_is_zero = exec.ctx.terms.mk_eq(read, zero);
    let model = exec.last_model.as_ref().unwrap();
    assert_eq!(exec.evaluate_term(model, related), EvalValue::Bool(true));
    assert_eq!(
        exec.evaluate_term(model, read_is_zero),
        EvalValue::Bool(true)
    );
    assert!(exec.skolem_witness_terms_evaluate_true(&[related, read_is_zero]));
}

#[test]
fn array_result_qmc_boolean_completion_cannot_override_a_negative_ground_fact() {
    let mut exec = fixture(
        "(declare-fun related (S S) Bool) \
         (assert (forall ((x S)) (related x x))) \
         (assert (not (related s s)))",
    );
    assert!(!exec.try_model_check_sat_certificate());
    assert!(exec
        .last_model
        .as_ref()
        .unwrap()
        .certified_const_interp_entries()
        .is_empty());
}

#[test]
fn array_result_qmc_candidate_cannot_override_inconsistent_read() {
    let mut exec = fixture("(assert (= (select (data s) 0) 1))");
    let roots = exec.ctx.assertions.clone();
    let leaves = exec.qmc_leaves(&roots).unwrap();
    let interp = exec.model_check_interpretation(&leaves, &roots).unwrap();
    let mut instances = Vec::new();
    let outcome = exec.qmc_certificate_pass(
        0,
        &roots,
        &leaves,
        &mut instances,
        LaneBudget::start(1000),
        None,
    );
    assert!(matches!(outcome, PassOutcome::Declined));
    assert!(exec
        .last_model
        .as_ref()
        .unwrap()
        .certified_const_interp_entries()
        .is_empty());
    // The zero array candidate is not licensed merely because a table was built.
    assert!(interp
        .tables
        .iter()
        .any(|table| table.symbol == data_symbol(&exec)));
}

#[test]
fn array_result_qmc_installs_typed_constant_into_both_model_readers() {
    let mut exec = fixture("");
    let mut model = source_model(&exec);
    let zero = exec.ctx.terms.mk_int(0.into());
    let array = exec.ctx.terms.mk_const_array(Sort::Int, zero);
    let array_sort = exec.ctx.terms.sort(array).clone();
    exec.install_model_check_array_defaults(
        &mut model,
        vec![(
            data_symbol(&exec),
            vec![Sort::Uninterpreted("S".into())],
            array_sort.clone(),
            array,
        )],
    )
    .unwrap();
    let read = term(&mut exec, "(select (data s) 0)");
    assert_eq!(
        exec.evaluate_term(&model, read),
        EvalValue::Rational(num_rational::BigRational::from_integer(0.into()))
    );
    assert_eq!(model.certified_const_interp_entries().len(), 1);
    let read_is_zero = exec.ctx.terms.mk_eq(read, zero);
    exec.last_model = Some(model);
    assert!(exec.skolem_witness_terms_evaluate_true(&[read_is_zero]));
}

#[test]
fn array_result_qmc_wrong_sort_is_atomic_refusal() {
    let mut exec = fixture("");
    let mut model = Model::empty();
    let wrong = exec.ctx.terms.mk_bool(true);
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    assert!(exec
        .install_model_check_array_defaults(
            &mut model,
            vec![(
                data_symbol(&exec),
                vec![Sort::Uninterpreted("S".into())],
                array_sort,
                wrong
            )]
        )
        .is_none());
    assert!(model.certified_const_interp_entries().is_empty());
}

#[test]
fn array_result_qmc_malformed_application_cannot_borrow_the_array_package() {
    let mut exec = fixture("");
    let mut model = source_model(&exec);
    let zero = exec.ctx.terms.mk_int(0.into());
    let array = exec.ctx.terms.mk_const_array(Sort::Int, zero);
    let array_sort = exec.ctx.terms.sort(array).clone();
    let symbol = data_symbol(&exec);
    exec.install_model_check_array_defaults(
        &mut model,
        vec![(
            symbol.clone(),
            vec![Sort::Uninterpreted("S".into())],
            array_sort.clone(),
            array,
        )],
    )
    .unwrap();
    let valid = term(&mut exec, "(select (data s) 0)");
    assert_eq!(
        exec.evaluate_term(&model, valid),
        EvalValue::Rational(num_rational::BigRational::from_integer(0.into()))
    );
    // Raw malformed applications bypass the frontend only for this control.
    // A matching head cannot replace the declared S argument with Int or drop it.
    for args in [vec![zero], Vec::new()] {
        let wrong = exec
            .ctx
            .terms
            .mk_app(symbol.clone(), args, array_sort.clone());
        let read = exec.ctx.terms.mk_select(wrong, zero);
        assert!(matches!(
            exec.evaluate_term(&model, read),
            EvalValue::Unknown
        ));
    }
}

#[test]
fn array_result_qmc_scoped_redeclaration_invalidates_the_array_package() {
    let mut exec = Executor::new();
    exec.execute_all(
        &ay_frontend::parse(
            "(set-logic AUFLIA) (declare-sort S 0) (declare-const s S) \
             (push 1) (declare-fun data (S) (Array Int Int))",
        )
        .unwrap(),
    )
    .unwrap();
    let mut model = source_model(&exec);
    let zero = exec.ctx.terms.mk_int(0.into());
    let array = exec.ctx.terms.mk_const_array(Sort::Int, zero);
    exec.install_model_check_array_defaults(
        &mut model,
        vec![(
            data_symbol(&exec),
            vec![Sort::Uninterpreted("S".into())],
            exec.ctx.terms.sort(array).clone(),
            array,
        )],
    )
    .unwrap();
    let original = term(&mut exec, "(select (data s) 0)");
    assert_eq!(
        exec.evaluate_term(&model, original),
        EvalValue::Rational(num_rational::BigRational::from_integer(0.into()))
    );
    exec.execute_all(
        &ay_frontend::parse("(pop 1) (declare-fun data (S) (Array Int Int))").unwrap(),
    )
    .unwrap();
    let replacement = term(&mut exec, "(select (data s) 0)");
    for read in [original, replacement] {
        assert!(matches!(
            exec.evaluate_term(&model, read),
            EvalValue::Unknown
        ));
    }
}
