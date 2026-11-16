// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One candidate assignment must feed ordinary and independent evaluation.

use super::super::independent_gate::IndependentModelView;
use super::*;
use ay_arrays::ArrayInterpretation;
use ay_model_check::{confirm_model, GateVerdict};

const VALUE: &str = "(OPayload (IPayload #x2a true) #x7f)";
const SOURCE: &str = r#"
(set-logic ALL)
(declare-datatype Inner ((IPayload (iv (_ BitVec 8)) (ib Bool)) (IEmpty)))
(declare-datatype Outer ((OPayload (oi Inner) (ot (_ BitVec 8))) (OEmpty (ox (_ BitVec 8)))))
(declare-const seed Outer)
; Keep this fixture in the array-bearing lane that does not own an e-graph assignment.
(declare-const noise (Array (_ BitVec 4) Bool))
(assert ((_ is OPayload) seed))
(assert (= ((_ is OPayload) seed) (= seed (OPayload (oi seed) (ot seed)))))
(assert (= (ot seed) #x7f))
(assert ((_ is IPayload) (oi seed)))
(assert (= ((_ is IPayload) (oi seed)) (= (oi seed) (IPayload (iv (oi seed)) (ib (oi seed))))))
(assert (= (iv (oi seed)) #x2a))
(assert (ib (oi seed)))
(assert (or ((_ is OPayload) seed) (= (ox seed) #x55)))
"#;

fn declared(exec: &Executor, name: &str) -> TermId {
    exec.ctx
        .symbol_info_by_identity(name)
        .and_then(|info| info.term)
        .unwrap_or_else(|| panic!("missing fixture declaration {name}"))
}

fn app(exec: &Executor, name: &str, argument: TermId) -> TermId {
    exec.ctx
        .terms
        .term_ids()
        .find(|&term| {
            matches!(exec.ctx.terms.get(term), TermData::App(Symbol::Named(symbol), args)
            if symbol.as_str() == name && args.as_slice() == [argument])
        })
        .unwrap_or_else(|| panic!("missing fixture application {name}"))
}

fn fixture() -> (Executor, Model) {
    let commands = ay_frontend::parse(SOURCE).expect("valid projection fixture");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("declarations and assertions execute");
    let seed = declared(&exec, "seed");
    let inner = app(&exec, "oi", seed);
    let tag = app(&exec, "ot", seed);
    let bits = app(&exec, "iv", inner);
    let flag = app(&exec, "ib", inner);
    let wrong = app(&exec, "ox", seed);
    let outer_test = app(&exec, "is-OPayload", seed);
    let inner_test = app(&exec, "is-IPayload", inner);
    let mut model = empty_model();
    let mut euf = EufModel::default();
    euf.term_values.insert(seed, VALUE.to_string());
    euf.term_values.insert(inner, "@Inner!old".to_string());
    model.euf_model = Some(euf);
    model.sat_model = vec![false, false];
    model.term_to_var.insert(outer_test, 0);
    model.term_to_var.insert(inner_test, 1);
    model.bool_overrides.insert(flag, false);
    model.bv_model = Some(BvModel {
        values: HashMap::from_iter([
            (tag, BigInt::from(0)),
            (bits, BigInt::from(0)),
            (wrong, BigInt::from(0x55)),
        ]),
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    (exec, model)
}

fn unchanged(exec: &Executor, mut model: Model) {
    let before = format!("{model:?}");
    assert_eq!(exec.complete_structured_datatype_values(&mut model, &[]), 0);
    assert_eq!(format!("{model:?}"), before, "refusal must be atomic");
}

#[test]
fn structured_assignment_is_shared_by_evaluator_and_independent_view() {
    let (exec, mut model) = fixture();
    let seed = declared(&exec, "seed");
    let inner = app(&exec, "oi", seed);
    let wrong = app(&exec, "ox", seed);
    let raw_bv = model.bv_model.as_ref().unwrap().values.clone();
    let raw_sat = model.sat_model.clone();
    assert!(model.dt_ground.is_empty() && model.dt_pins.is_empty());
    assert!(exec.complete_structured_datatype_values(&mut model, &[]) > 0);
    assert_eq!(
        exec.evaluate_term(&model, seed),
        EvalValue::Element(VALUE.to_string())
    );
    assert_eq!(
        exec.evaluate_term(&model, inner),
        EvalValue::Element("(IPayload #x2a true)".to_string())
    );
    for &assertion in &exec.ctx.assertions {
        assert_eq!(
            exec.evaluate_term(&model, assertion),
            EvalValue::Bool(true),
            "all observed facts must use the same candidate assignment"
        );
    }
    let view = IndependentModelView::new(&exec, &model);
    assert!(
        matches!(
            confirm_model(&exec.ctx.terms, &view, &exec.ctx.assertions),
            GateVerdict::ConfirmedSat
        ),
        "independent evaluation must confirm the same values"
    );
    assert!(
        !model.dt_pins.contains_key(&wrong),
        "wrong-constructor selector stays unspecified"
    );
    assert_eq!(model.bv_model.as_ref().unwrap().values, raw_bv);
    assert_eq!(
        model.sat_model, raw_sat,
        "projection does not rewrite the solver's SAT trail"
    );
    let before = format!("{model:?}");
    assert_eq!(exec.complete_structured_datatype_values(&mut model, &[]), 0);
    assert_eq!(
        format!("{model:?}"),
        before,
        "repeated completion is stable"
    );
}

#[test]
fn structured_assignment_rejects_conflicting_semantic_pin_atomically() {
    let (exec, mut model) = fixture();
    let tag = app(&exec, "ot", declared(&exec, "seed"));
    model.dt_pins.insert(
        tag,
        EvalValue::BitVec {
            value: BigInt::from(0),
            width: 8,
        },
    );
    unchanged(&exec, model);
}

#[test]
fn structured_assignment_rejects_conflicting_completed_projection_atomically() {
    let (exec, mut model) = fixture();
    let flag = app(&exec, "ib", app(&exec, "oi", declared(&exec, "seed")));
    model.completed_values.insert(flag, EvalValue::Bool(false));
    unchanged(&exec, model);
}

#[test]
fn structured_assignment_requires_live_reachable_well_typed_raw_values() {
    for raw in [
        "@Outer!opaque",
        "(IPayload #x2a true)",
        "(OPayload (IPayload #x2a true))",
        "(OPayload (IPayload #x002a true) #x7f)",
        "(OPayload (IPayload #x2a true) #x7f) trailing",
    ] {
        let (exec, mut model) = fixture();
        model
            .euf_model
            .as_mut()
            .unwrap()
            .term_values
            .insert(declared(&exec, "seed"), raw.to_string());
        unchanged(&exec, model);
    }
    let (mut exec, model) = fixture();
    exec.ctx.assertions.clear();
    exec.independent_gate_authored_assertions = None;
    exec.self_check_authored_assertions = None;
    unchanged(&exec, model); // Retained arena entries alone are not query roots.
}

#[test]
fn structured_assignment_never_uses_an_indexed_application_as_a_seed() {
    let (mut exec, mut model) = fixture();
    let seed = declared(&exec, "seed");
    let forged = exec.ctx.terms.mk_app(
        Symbol::indexed("oi", vec![0]),
        vec![seed],
        Sort::Uninterpreted("Inner".to_string()),
    );
    exec.ctx.assertions.clear();
    exec.independent_gate_authored_assertions = None;
    exec.self_check_authored_assertions = None;
    model.euf_model.as_mut().unwrap().term_values.clear();
    model
        .euf_model
        .as_mut()
        .unwrap()
        .term_values
        .insert(forged, "(IPayload #x2a true)".to_string());
    let before = format!("{model:?}");
    assert_eq!(
        exec.complete_structured_datatype_values(&mut model, &[forged]),
        0
    );
    assert_eq!(format!("{model:?}"), before);
}

#[test]
fn structured_assignment_preserves_owned_and_scoped_models() {
    let (exec, mut model) = fixture();
    let before = format!("{model:?}");
    let changed = with_scoped_term_evaluation_override_for_test(
        declared(&exec, "seed"),
        EvalValue::Element(VALUE.to_string()),
        || exec.complete_structured_datatype_values(&mut model, &[]),
    );
    assert_eq!(changed, 0);
    assert_eq!(format!("{model:?}"), before);

    let (mut exec, model) = fixture();
    exec.dt_lazy_splits = Some((Vec::new(), Vec::new()));
    unchanged(&exec, model);

    let (exec, mut model) = fixture();
    let seed = declared(&exec, "seed");
    model.certified_total_ufs.ground_pins.insert(
        seed,
        StampedCertificatePin {
            entry_stamp: exec.ctx.terms.entry_stamp(seed).expect("live seed"),
            value: EvalValue::Element(VALUE.to_string()),
        },
    );
    unchanged(&exec, model);
}

#[test]
fn structured_assignment_budget_failure_never_commits_earlier_candidates() {
    let (mut exec, mut model) = fixture();
    let extra = exec
        .ctx
        .terms
        .mk_var("oversized_seed", Sort::Uninterpreted("Outer".to_string()));
    let text = format!("({})", "x".repeat(1_048_576));
    model
        .euf_model
        .as_mut()
        .unwrap()
        .term_values
        .insert(extra, text);
    let before = format!("{model:?}");
    assert_eq!(
        exec.complete_structured_datatype_values(&mut model, &[extra]),
        0
    );
    assert_eq!(
        format!("{model:?}"),
        before,
        "one exhausted shared budget cannot publish a partial assignment"
    );
}

fn late_array_fixture() -> (Executor, Model, TermId) {
    let commands = ay_frontend::parse(
        r#"
        (set-logic ALL)
        (declare-datatype Late ((LValue (lv (_ BitVec 8)) (lb Bool)) (LEmpty)))
        (declare-const late Late)
        (declare-const array (Array (_ BitVec 4) Late))
        (declare-const aux (Array Int Int))
        (declare-const n Int)
        (assert (= n (select aux 0)))
        (assert (= late (select array #x0)))
        (assert (= (lv late) #x2a))
        (assert (lb late))
        (assert ((_ is LValue) late))
    "#,
    )
    .expect("valid late-alias fixture");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("declarations and assertions execute");
    let leaf = declared(&exec, "late");
    let array = declared(&exec, "array");
    let aux = declared(&exec, "aux");
    let n = declared(&exec, "n");
    let value = app(&exec, "lv", leaf);
    let flag = app(&exec, "lb", leaf);
    let tester = app(&exec, "is-LValue", leaf);
    let mut model = empty_model();
    let mut euf = EufModel::default();
    // A separate ordinary read-pin repair triggers late alias refresh.
    // `late` has no raw value until that refresh reads its typed array cell.
    euf.term_values.insert(n, "1".to_string());
    euf.int_values.insert(n, BigInt::from(1));
    model.euf_model = Some(euf);
    model.lia_model = Some(LiaModel {
        values: HashMap::from_iter([(n, BigInt::from(1))]),
    });
    model.array_model = Some(ArrayModel {
        array_values: HashMap::from_iter([
            (
                array,
                ArrayInterpretation {
                    index_sort: Some(Sort::bitvec(4)),
                    element_sort: Some(Sort::Uninterpreted("Late".to_string())),
                    default: Some("(LValue #x2a true)".to_string()),
                    stores: Vec::new(),
                },
            ),
            (
                aux,
                ArrayInterpretation {
                    index_sort: Some(Sort::Int),
                    element_sort: Some(Sort::Int),
                    default: Some("0".to_string()),
                    stores: Vec::new(),
                },
            ),
        ]),
        ..Default::default()
    });
    model.bv_model = Some(BvModel {
        values: HashMap::from_iter([(value, BigInt::from(0x2a))]),
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    model.bool_overrides.insert(flag, true);
    model.sat_model = vec![true];
    model.term_to_var.insert(tester, 0);
    (exec, model, leaf)
}

#[test]
fn strict_gate_completes_a_late_array_read_alias_before_validation() {
    let (mut exec, mut model, leaf) = late_array_fixture();
    assert_eq!(
        exec.complete_structured_datatype_values(&mut model, &[]),
        0,
        "no raw datatype value exists before the late read repair"
    );
    exec.last_result = Some(SolveResult::Sat);
    exec.last_model = Some(model);
    assert_eq!(
        exec.apply_strict_model_gate(SolveResult::Sat),
        SolveResult::Sat,
        "the real prevalidation repair path must leave a coherent candidate"
    );
    let model = exec.last_model.as_ref().expect("candidate retained");
    assert_eq!(
        model
            .euf_model
            .as_ref()
            .unwrap()
            .term_values
            .get(&leaf)
            .map(String::as_str),
        Some("(LValue #x2a true)"),
        "actual array repair must refresh the alias"
    );
    assert!(
        model.dt_ground.contains_key(&leaf),
        "late value must reach shared typed storage"
    );
    for &assertion in &exec.ctx.assertions {
        assert_eq!(exec.evaluate_term(model, assertion), EvalValue::Bool(true));
    }
    assert!(matches!(
        exec.confirm_sat_with_independent_gate(),
        GateVerdict::ConfirmedSat
    ));
}

#[test]
fn structured_assignment_refuses_a_changed_raw_seed_after_completion() {
    use ay_model_check::ModelValue;

    let (exec, mut model) = fixture();
    let seed = declared(&exec, "seed");
    // Model a prior alias producer's handoff: the variable is already exact,
    // but none of its observed selector/tester projections is installed.
    model.dt_ground.insert(
        seed,
        ModelValue::Datatype {
            ctor: "OPayload".to_string(),
            args: vec![
                ModelValue::Datatype {
                    ctor: "IPayload".to_string(),
                    args: vec![
                        ModelValue::bitvec(BigInt::from(0x2a), 8),
                        ModelValue::Bool(true),
                    ],
                },
                ModelValue::bitvec(BigInt::from(0x7f), 8),
            ],
        },
    );
    model
        .dt_pins
        .insert(seed, EvalValue::Element(VALUE.to_string()));
    let tag = app(&exec, "ot", seed);
    assert!(!model.dt_pins.contains_key(&tag));
    assert!(exec.complete_structured_datatype_values(&mut model, &[]) > 0);
    assert_eq!(
        exec.evaluate_term(&model, tag),
        EvalValue::BitVec {
            value: BigInt::from(0x7f),
            width: 8
        }
    );
    assert_eq!(
        model
            .euf_model
            .as_mut()
            .unwrap()
            .term_values
            .insert(seed, "(OPayload (IPayload #x2b false) #x7e)".to_string()),
        Some(VALUE.to_string()),
    );
    unchanged(&exec, model);
}

#[test]
fn structured_assignment_uses_ground_seed_when_raw_constructor_is_absent_or_opaque() {
    use ay_model_check::ModelValue;

    for raw in [None, Some("@Outer!opaque")] {
        let (exec, mut model) = fixture();
        let seed = declared(&exec, "seed");
        model.dt_ground.insert(
            seed,
            ModelValue::Datatype {
                ctor: "OPayload".to_string(),
                args: vec![
                    ModelValue::Datatype {
                        ctor: "IPayload".to_string(),
                        args: vec![
                            ModelValue::bitvec(BigInt::from(0x2a), 8),
                            ModelValue::Bool(true),
                        ],
                    },
                    ModelValue::bitvec(BigInt::from(0x7f), 8),
                ],
            },
        );
        let euf = model.euf_model.as_mut().unwrap();
        if let Some(raw) = raw {
            euf.term_values.insert(seed, raw.to_string());
        } else {
            euf.term_values.remove(&seed);
        }
        let raw_before = euf.term_values.clone();
        assert!(model.dt_pins.is_empty());
        assert!(exec.complete_structured_datatype_values(&mut model, &[]) > 0);
        assert_eq!(
            exec.evaluate_term(&model, seed),
            EvalValue::Element(VALUE.to_string())
        );
        for &assertion in &exec.ctx.assertions {
            assert_eq!(exec.evaluate_term(&model, assertion), EvalValue::Bool(true));
        }
        assert!(matches!(
            confirm_model(
                &exec.ctx.terms,
                &IndependentModelView::new(&exec, &model),
                &exec.ctx.assertions
            ),
            GateVerdict::ConfirmedSat
        ));
        assert_eq!(model.euf_model.as_ref().unwrap().term_values, raw_before);
    }
}
