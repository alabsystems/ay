// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact constructor syntax must not become an opaque ordinary-EUF value.

use super::*;
use ay_model_check::ModelValue;

mod raw_labels;
mod selector_ground;

fn fixture() -> Executor {
    let commands = ay_frontend::parse(
        r#"
        (set-logic ALL)
        (declare-datatype Field
          ((LiteralPayload (ptr (_ BitVec 8)) (funptr (_ BitVec 8)) (flag Bool))))
        (declare-datatype Outer ((WrapPayload (payload Field))))
        (declare-datatype Wider ((WidePayload (number Int))))
        (declare-datatype Tree ((Stop) (Fork (left Tree) (right Tree))))
        (declare-fun opaque_payload ((_ BitVec 8)) Field)
        "#,
    )
    .expect("valid constructor fixture");
    let mut exec = Executor::new();
    for command in commands {
        assert!(exec
            .execute(&command)
            .expect("declaration executes")
            .is_none());
    }
    assert!(
        exec.ctx.assertions.is_empty(),
        "no solving or equality shortcut"
    );
    exec
}

fn field_sort() -> Sort {
    Sort::Uninterpreted("Field".to_string())
}

fn literal_fields(exec: &mut Executor) -> Vec<TermId> {
    vec![
        exec.ctx.terms.mk_bitvec(BigInt::from(0x2au8), 8),
        exec.ctx.terms.mk_bitvec(BigInt::from(0x7fu8), 8),
        exec.ctx.terms.true_term(),
    ]
}

fn raw_model(terms: &[(TermId, &str)]) -> Model {
    let mut model = empty_model();
    let mut euf = EufModel::default();
    for &(term, value) in terms {
        euf.term_values.insert(term, value.to_string());
    }
    model.euf_model = Some(euf);
    model
}

#[test]
fn nonnullary_constructor_uses_known_fields_before_opaque_euf_slot() {
    for ground_proxy in [false, true] {
        let mut exec = fixture();
        let fields = literal_fields(&mut exec);
        let literal = exec
            .ctx
            .terms
            .mk_app(Symbol::named("LiteralPayload"), fields, field_sort());
        let field = if ground_proxy {
            exec.ctx.terms.mk_var("committed_field", field_sort())
        } else {
            literal
        };
        let outer = exec.ctx.terms.mk_app(
            Symbol::named("WrapPayload"),
            vec![field],
            Sort::Uninterpreted("Outer".to_string()),
        );
        let mut model = raw_model(&[(field, "@Field!0"), (outer, "@Outer!0")]);
        if ground_proxy {
            model.dt_ground.insert(
                field,
                ModelValue::Datatype {
                    ctor: "LiteralPayload".to_string(),
                    args: vec![
                        ModelValue::bitvec(BigInt::from(0x2au8), 8),
                        ModelValue::bitvec(BigInt::from(0x7fu8), 8),
                        ModelValue::Bool(true),
                    ],
                },
            );
        }
        let euf_before = model.euf_model.as_ref().unwrap().term_values.clone();
        assert_eq!(
            exec.evaluate_term(&model, outer),
            EvalValue::Element("(WrapPayload (LiteralPayload #x2a #x7f true))".to_string()),
            "exact constructor fields outrank its ordinary EUF token"
        );
        assert_eq!(model.euf_model.as_ref().unwrap().term_values, euf_before);
        assert!(
            model.dt_pins.is_empty(),
            "evaluation must not install a shortcut pin"
        );
    }
}

#[test]
fn nonnullary_constructor_missing_field_keeps_opaque_fallback() {
    let mut exec = fixture();
    let missing = exec.ctx.terms.mk_var("missing_bits", Sort::bitvec(8));
    let mut fields = literal_fields(&mut exec);
    fields[0] = missing;
    let constructor = exec
        .ctx
        .terms
        .mk_app(Symbol::named("LiteralPayload"), fields, field_sort());
    let model = raw_model(&[(constructor, "@Field!missing")]);
    assert_eq!(exec.evaluate_term(&model, missing), EvalValue::Unknown);
    assert_eq!(
        exec.evaluate_term(&model, constructor),
        EvalValue::Element("@Field!missing".to_string()),
        "an incomplete structural attempt must not invent constructor fields"
    );
    assert!(model.dt_ground.is_empty());
    assert!(model.dt_pins.is_empty());
}

#[test]
fn nonnullary_constructor_recognition_keeps_exact_symbol_identity() {
    let mut exec = fixture();
    let fields = literal_fields(&mut exec);
    let indexed = exec.ctx.terms.mk_app(
        Symbol::indexed("LiteralPayload", vec![0]),
        fields.clone(),
        field_sort(),
    );
    let ordinary = exec.ctx.terms.mk_app(
        Symbol::named("opaque_payload"),
        vec![fields[0]],
        field_sort(),
    );
    let model = raw_model(&[(indexed, "@Field!indexed"), (ordinary, "@Field!ordinary")]);
    assert_eq!(
        exec.evaluate_term(&model, indexed),
        EvalValue::Element("@Field!indexed".to_string()),
        "an indexed lookalike is not the registered Named constructor"
    );
    assert_eq!(
        exec.evaluate_term(&model, ordinary),
        EvalValue::Element("@Field!ordinary".to_string()),
        "ordinary UF evaluation remains unchanged"
    );
    let integer = exec.ctx.terms.mk_int(BigInt::from(7));
    let wider = exec.ctx.terms.mk_app(
        Symbol::named("WidePayload"),
        vec![integer],
        Sort::Uninterpreted("Wider".to_string()),
    );
    let wider_model = raw_model(&[(wider, "@Wider!unsupported")]);
    assert_eq!(
        exec.evaluate_term(&wider_model, wider),
        EvalValue::Element("@Wider!unsupported".to_string()),
        "an unsupported scalar fragment keeps its existing fallback"
    );
}

#[test]
fn nonnullary_constructor_refuses_malformed_arity_and_sorts() {
    for malformed in 0..4 {
        let mut exec = fixture();
        let mut fields = literal_fields(&mut exec);
        let result_sort = if malformed == 2 {
            Sort::Uninterpreted("Outer".to_string())
        } else {
            field_sort()
        };
        if malformed == 0 {
            fields.truncate(2);
        } else if malformed == 1 {
            fields[0] = exec.ctx.terms.false_term();
        } else if malformed == 3 {
            // Empty application syntax must not impersonate a nullary constructor.
            fields.clear();
        }
        let constructor =
            exec.ctx
                .terms
                .mk_app(Symbol::named("LiteralPayload"), fields, result_sort);
        let model = raw_model(&[(constructor, "@malformed!0")]);
        assert_eq!(
            exec.evaluate_term(&model, constructor),
            EvalValue::Unknown,
            "malformed exact constructor cannot gain an ordinary-EUF value"
        );
    }
}

#[test]
fn nonnullary_constructor_budget_refusal_preserves_opaque_value() {
    // eval_dt_constructor's MAX_NODES is 65,536. This has 17 shared syntax
    // nodes but 131,071 expanded value nodes: enough to cross the real bound
    // without constructing an enormous native test fixture.
    let mut exec = fixture();
    let stop = exec
        .ctx
        .symbol_info_by_identity("Stop")
        .and_then(|info| info.term)
        .expect("live nullary tree constructor");
    let tree_sort = Sort::Uninterpreted("Tree".to_string());
    let mut tree = stop;
    for _ in 0..16 {
        tree = exec
            .ctx
            .terms
            .mk_app(Symbol::named("Fork"), vec![tree, tree], tree_sort.clone());
    }
    let model = raw_model(&[(tree, "@Tree!node_budget")]);
    let euf_before = model.euf_model.as_ref().unwrap().term_values.clone();
    assert_eq!(
        exec.evaluate_term(&model, tree),
        EvalValue::Element("@Tree!node_budget".to_string()),
        "a refused structural attempt must preserve the old opaque fallback"
    );
    assert!(model.dt_ground.is_empty());
    assert!(model.dt_pins.is_empty());
    assert_eq!(model.euf_model.as_ref().unwrap().term_values, euf_before);

    // A typed ground field is small in node count but exceeds MAX_DEPTH=64.
    // Preflight must refuse before cloning/rendering that value into a root.
    let mut exec = fixture();
    let stop = exec
        .ctx
        .symbol_info_by_identity("Stop")
        .and_then(|info| info.term)
        .expect("live nullary tree constructor");
    let proxy = exec.ctx.terms.mk_var("deep_ground", tree_sort.clone());
    let root = exec
        .ctx
        .terms
        .mk_app(Symbol::named("Fork"), vec![proxy, stop], tree_sort);
    let mut value = ModelValue::Datatype {
        ctor: "Stop".to_string(),
        args: vec![],
    };
    for _ in 0..65 {
        value = ModelValue::Datatype {
            ctor: "Fork".to_string(),
            args: vec![
                value,
                ModelValue::Datatype {
                    ctor: "Stop".to_string(),
                    args: vec![],
                },
            ],
        };
    }
    let mut model = raw_model(&[(root, "@Tree!depth_budget")]);
    model.dt_ground.insert(proxy, value);
    let ground_before = format!("{:?}", model.dt_ground);
    let euf_before = model.euf_model.as_ref().unwrap().term_values.clone();
    assert_eq!(
        exec.evaluate_term(&model, root),
        EvalValue::Element("@Tree!depth_budget".to_string()),
        "oversized typed ground values cannot become an invented constructor"
    );
    assert_eq!(format!("{:?}", model.dt_ground), ground_before);
    assert!(model.dt_pins.is_empty());
    assert_eq!(model.euf_model.as_ref().unwrap().term_values, euf_before);
}

fn assert_raw_field_fallback(raw: &str, label: &str) {
    let mut exec = fixture();
    let field = exec.ctx.terms.mk_var("raw_field", field_sort());
    let outer = exec.ctx.terms.mk_app(
        Symbol::named("WrapPayload"),
        vec![field],
        Sort::Uninterpreted("Outer".to_string()),
    );
    let model = raw_model(&[(field, raw), (outer, "@Outer!fallback")]);
    assert_eq!(
        exec.evaluate_term(&model, outer),
        EvalValue::Element("@Outer!fallback".to_string()),
        "invalid or oversized raw field must retain fallback: {label}"
    );
    assert!(model.dt_ground.is_empty());
    assert!(model.dt_pins.is_empty());
    assert_eq!(
        model
            .euf_model
            .as_ref()
            .unwrap()
            .term_values
            .get(&field)
            .map(String::as_str),
        Some(raw)
    );
}

#[test]
fn nonnullary_constructor_reads_its_typed_structural_euf_field() {
    for (raw, expected) in [
        (
            "(LiteralPayload #x2a #x7f true)",
            "(WrapPayload (LiteralPayload #x2a #x7f true))",
        ),
        (
            "(LiteralPayload #x01 #x02 false)",
            "(WrapPayload (LiteralPayload #x01 #x02 false))",
        ),
    ] {
        let mut exec = fixture();
        let field = exec.ctx.terms.mk_var("structured_raw_field", field_sort());
        let outer = exec.ctx.terms.mk_app(
            Symbol::named("WrapPayload"),
            vec![field],
            Sort::Uninterpreted("Outer".to_string()),
        );
        let model = raw_model(&[(field, raw), (outer, "@Outer!raw")]);
        let euf_before = model.euf_model.as_ref().unwrap().term_values.clone();
        assert!(model.dt_ground.is_empty());
        assert!(model.dt_pins.is_empty());
        assert_eq!(
            exec.evaluate_term(&model, outer),
            EvalValue::Element(expected.to_string()),
            "read the exact variable's typed constructor value, not its class label"
        );
        assert!(model.dt_ground.is_empty());
        assert!(model.dt_pins.is_empty());
        assert_eq!(model.euf_model.as_ref().unwrap().term_values, euf_before);
    }
}

#[test]
fn nonnullary_constructor_rejects_inexact_or_oversized_raw_euf_fields() {
    for (label, raw) in [
        ("opaque token", "@Field!opaque"),
        (
            "wrong result sort",
            "(WrapPayload (LiteralPayload #x2a #x7f true))",
        ),
        ("wrong constructor", "(NotRegistered #x2a #x7f true)"),
        ("wrong field sort", "(LiteralPayload true #x7f true)"),
        ("wrong BV width", "(LiteralPayload #x002a #x7f true)"),
        (
            "wrong indexed BV width",
            "(LiteralPayload (_ bv42 16) #x7f true)",
        ),
        (
            "trailing garbage",
            "(LiteralPayload #x2a #x7f true) garbage",
        ),
        (
            "non-ground field",
            "(LiteralPayload missing_bits #x7f true)",
        ),
        ("missing field", "(LiteralPayload #x2a #x7f)"),
        ("unclosed syntax", "(LiteralPayload #x2a #x7f true"),
    ] {
        assert_raw_field_fallback(raw, label);
    }
    // Whitespace padding keeps the value syntactically valid while crossing
    // both the evaluator's and rendered-DT parser's actual 1 MiB byte bound.
    let oversized = format!("{}(LiteralPayload #x2a #x7f true)", " ".repeat(1_048_577));
    assert_raw_field_fallback(&oversized, "valid syntax over the raw-byte bound");
}

fn malformed_scalar_pin_cases() -> [(&'static str, bool, bool, EvalValue); 8] {
    [
        (
            "Bool wrong kind",
            true,
            false,
            EvalValue::BitVec {
                value: BigInt::from(1),
                width: 1,
            },
        ),
        ("BV wrong kind", false, false, EvalValue::Bool(true)),
        (
            "BV wrong width",
            false,
            false,
            EvalValue::BitVec {
                value: BigInt::from(0x2a),
                width: 16,
            },
        ),
        (
            "BV negative",
            false,
            false,
            EvalValue::BitVec {
                value: BigInt::from(-1),
                width: 8,
            },
        ),
        (
            "BV overflow",
            false,
            false,
            EvalValue::BitVec {
                value: BigInt::from(1u8) << 1024usize,
                width: 8,
            },
        ),
        ("unknown pin", false, false, EvalValue::Unknown),
        (
            "Bool literal contradiction",
            true,
            true,
            EvalValue::Bool(false),
        ),
        (
            "BV literal contradiction",
            false,
            true,
            EvalValue::BitVec {
                value: BigInt::from(0x2b),
                width: 8,
            },
        ),
    ]
}

#[test]
fn nonnullary_constructor_rejects_malformed_scalar_pins() {
    for (label, boolean, literal, pin) in malformed_scalar_pin_cases() {
        let mut exec = fixture();
        let mut fields = literal_fields(&mut exec);
        let index = if boolean { 2 } else { 0 };
        let field = if literal {
            fields[index]
        } else {
            exec.ctx.terms.mk_var(
                "pinned_scalar",
                if boolean { Sort::Bool } else { Sort::bitvec(8) },
            )
        };
        fields[index] = field;
        let constructor =
            exec.ctx
                .terms
                .mk_app(Symbol::named("LiteralPayload"), fields, field_sort());
        let mut model = raw_model(&[(constructor, "@Field!refused_pin")]);
        let valid_raw = if boolean {
            model.bool_overrides.insert(field, true);
            EvalValue::Bool(true)
        } else {
            model.bv_model = Some(BvModel {
                values: HashMap::from_iter([(field, BigInt::from(0x2a))]),
                term_to_bits: HashMap::default(),
                bool_overrides: HashMap::default(),
            });
            EvalValue::BitVec {
                value: BigInt::from(0x2a),
                width: 8,
            }
        };
        // Lower-priority valid sources must not rescue a malformed pin or
        // replace a literal's intrinsic value with a contradictory pin.
        model.completed_values.insert(field, valid_raw);
        model.dt_pins.insert(field, pin);
        let before = format!("{model:?}");
        assert_eq!(
            exec.evaluate_term(&model, constructor),
            EvalValue::Element("@Field!refused_pin".to_string()),
            "{label}: malformed scalar cannot produce a constructor tree",
        );
        assert_eq!(
            format!("{model:?}"),
            before,
            "{label}: evaluation mutated model"
        );
    }
}
