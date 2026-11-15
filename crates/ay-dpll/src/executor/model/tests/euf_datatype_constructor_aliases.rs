// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The EUF alias producer may recover committed constructor fields, but may
//! never choose among conflicting values or invent fields for opaque classes.

mod raw_fields;

use super::super::dt_construct::mv_to_eval;
use super::*;
use ay_model_check::ModelValue;

fn fixture() -> Executor {
    let commands = ay_frontend::parse(
        r#"
        (set-logic ALL)
        (declare-datatype Arg
          ((Placeholder (ptr (_ BitVec 8)) (funptr (_ BitVec 8)) (flag Bool))
           (Count (count (_ BitVec 8))) (Empty)))
        (declare-datatype Outer ((Wrap (arg Arg))))
        (declare-datatype Foreign ((ForeignValue (foreign_bits (_ BitVec 8)))))
        (declare-datatype Chain ((End) (Link (next Chain))))
        (declare-datatype Tree ((Stop) (Fork (left Tree) (right Tree))))
        "#,
    )
    .expect("valid alias fixture declarations");
    let mut exec = Executor::new();
    for command in commands {
        assert!(exec.execute(&command).expect("fixture executes").is_none());
    }
    assert!(
        exec.ctx.assertions.is_empty(),
        "no asserted-equality shortcut"
    );
    exec
}

fn sort(name: &str) -> Sort {
    Sort::Uninterpreted(name.to_string())
}

fn bv(exec: &mut Executor, value: u8) -> TermId {
    exec.ctx.terms.mk_bitvec(BigInt::from(value), 8)
}

fn app(exec: &mut Executor, name: &str, args: Vec<TermId>, result: &str) -> TermId {
    exec.ctx
        .terms
        .mk_app(Symbol::named(name), args, sort(result))
}

fn placeholder(exec: &mut Executor, ptr: u8) -> TermId {
    let ptr = bv(exec, ptr);
    let funptr = bv(exec, 0x7f);
    let flag = exec.ctx.terms.true_term();
    app(exec, "Placeholder", vec![ptr, funptr, flag], "Arg")
}

fn placeholder_value(ptr: u8) -> ModelValue {
    ModelValue::Datatype {
        ctor: "Placeholder".to_string(),
        args: vec![
            ModelValue::bitvec(BigInt::from(ptr), 8),
            ModelValue::bitvec(BigInt::from(0x7fu8), 8),
            ModelValue::Bool(true),
        ],
    }
}

fn model_with_classes(rows: &[(TermId, &str)]) -> Model {
    let mut model = empty_model();
    let mut euf = EufModel::default();
    for &(term, token) in rows {
        euf.term_values.insert(term, token.to_string());
    }
    model.euf_model = Some(euf);
    model
}

fn assert_value(model: &Model, term: TermId, expected: &ModelValue) {
    let actual = model
        .dt_ground
        .get(&term)
        .expect("expected structured ground value");
    // Derived Debug includes every variant, constructor, width and field; this
    // independent assertion does not reuse the producer's equality helper.
    assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    assert_eq!(model.dt_pins.get(&term), Some(&mv_to_eval(expected)));
}

fn assert_unpinned(model: &Model, terms: &[TermId]) {
    for term in terms {
        assert!(
            !model.dt_ground.contains_key(term),
            "unexpected ground value for {term:?}"
        );
        assert!(
            !model.dt_pins.contains_key(term),
            "unexpected pin for {term:?}"
        );
    }
}

#[test]
fn euf_constructor_aliases_preserve_nested_nonzero_fields() {
    let mut exec = fixture();
    let inner = exec.ctx.terms.mk_var("field_proxy", sort("Arg"));
    let constructor = placeholder(&mut exec, 0x2a);
    let outer = exec.ctx.terms.mk_var("outer_proxy", sort("Outer"));
    let alias = exec.ctx.terms.mk_var("outer_alias", sort("Outer"));
    let wrapper = app(&mut exec, "Wrap", vec![inner], "Outer");
    let mut model = model_with_classes(&[
        (inner, "@Arg!0"),
        (constructor, "@Arg!0"),
        (outer, "@Outer!0"),
        (alias, "@Outer!0"),
        (wrapper, "@Outer!0"),
    ]);
    let euf_before = model.euf_model.as_ref().unwrap().term_values.clone();
    let roots = [inner, constructor, outer, alias, wrapper];
    assert_eq!(
        exec.complete_euf_datatype_constructor_aliases(&mut model, &roots),
        3
    );
    let inner_value = placeholder_value(0x2a);
    let outer_value = ModelValue::Datatype {
        ctor: "Wrap".to_string(),
        args: vec![inner_value.clone()],
    };
    assert_value(&model, inner, &inner_value);
    assert_value(&model, outer, &outer_value);
    assert_value(&model, alias, &outer_value);
    assert_unpinned(&model, &[constructor, wrapper]);
    assert_eq!(model.euf_model.as_ref().unwrap().term_values, euf_before);
}

#[test]
fn euf_constructor_aliases_refuse_conflicting_class_values() {
    for conflict_kind in 0..3 {
        for reversed in [false, true] {
            let mut exec = fixture();
            let proxy = exec.ctx.terms.mk_var("conflicting_proxy", sort("Arg"));
            // Reverse term creation, not just map insertion: an implementation
            // must not choose whichever conflicting constructor has lower ID.
            let mut constructors = Vec::new();
            for conflicting in if reversed {
                [true, false]
            } else {
                [false, true]
            } {
                let constructor = if conflicting && conflict_kind == 1 {
                    let count = bv(&mut exec, 1);
                    app(&mut exec, "Count", vec![count], "Arg")
                } else if conflicting && conflict_kind == 2 {
                    exec.ctx
                        .symbol_info_by_identity("Empty")
                        .and_then(|info| info.term)
                        .expect("live nullary constructor")
                } else {
                    placeholder(&mut exec, if conflicting { 0x2b } else { 0x2a })
                };
                constructors.push(constructor);
            }
            let roots = [proxy, constructors[0], constructors[1]];
            let mut model = model_with_classes(&[
                (proxy, "@Arg!conflict"),
                (constructors[0], "@Arg!conflict"),
                (constructors[1], "@Arg!conflict"),
            ]);
            assert_eq!(
                exec.complete_euf_datatype_constructor_aliases(&mut model, &roots),
                0
            );
            assert_unpinned(&model, &roots);
        }
    }

    // Existing model facts are not overwritten to make a new candidate fit.
    let mut exec = fixture();
    let proxy = exec.ctx.terms.mk_var("already_pinned", sort("Arg"));
    let constructor = placeholder(&mut exec, 0x2a);
    let mut model = model_with_classes(&[(proxy, "@Arg!old"), (constructor, "@Arg!old")]);
    let old = placeholder_value(0x2b);
    model.dt_ground.insert(proxy, old.clone());
    model.dt_pins.insert(proxy, mv_to_eval(&old));
    let ground_before = model.dt_ground.clone();
    let pins_before = model.dt_pins.clone();
    assert_eq!(
        exec.complete_euf_datatype_constructor_aliases(&mut model, &[proxy, constructor]),
        0
    );
    assert_eq!(model.dt_ground.len(), ground_before.len());
    for (term, expected) in &ground_before {
        let actual = model
            .dt_ground
            .get(term)
            .expect("existing ground key is preserved");
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }
    assert_eq!(model.dt_pins, pins_before);
}

#[test]
fn euf_constructor_aliases_refuse_recursive_cycles() {
    for two_classes in [false, true] {
        let mut exec = fixture();
        let first = exec.ctx.terms.mk_var("cycle_first", sort("Chain"));
        let second = if two_classes {
            exec.ctx.terms.mk_var("cycle_second", sort("Chain"))
        } else {
            first
        };
        let first_constructor = app(&mut exec, "Link", vec![second], "Chain");
        let mut roots = vec![first, second, first_constructor];
        let mut rows = vec![(first, "@Chain!0"), (first_constructor, "@Chain!0")];
        if two_classes {
            let second_constructor = app(&mut exec, "Link", vec![first], "Chain");
            roots.push(second_constructor);
            rows.extend([(second, "@Chain!1"), (second_constructor, "@Chain!1")]);
        }
        let mut model = model_with_classes(&rows);
        assert_eq!(
            exec.complete_euf_datatype_constructor_aliases(&mut model, &roots),
            0
        );
        assert_unpinned(&model, &roots);
    }
}

#[test]
fn euf_constructor_aliases_require_committed_scalar_fields() {
    for missing_bool in [true, false] {
        let mut exec = fixture();
        let proxy = exec.ctx.terms.mk_var("partial_proxy", sort("Arg"));
        let missing = exec.ctx.terms.mk_var(
            "missing_field",
            if missing_bool {
                Sort::Bool
            } else {
                Sort::bitvec(8)
            },
        );
        let ptr = if missing_bool {
            bv(&mut exec, 0x2a)
        } else {
            missing
        };
        let funptr = bv(&mut exec, 0x7f);
        let flag = if missing_bool {
            missing
        } else {
            exec.ctx.terms.true_term()
        };
        let constructor = app(&mut exec, "Placeholder", vec![ptr, funptr, flag], "Arg");
        let roots = [proxy, constructor];
        let mut model =
            model_with_classes(&[(proxy, "@Arg!partial"), (constructor, "@Arg!partial")]);
        assert_eq!(
            exec.complete_euf_datatype_constructor_aliases(&mut model, &roots),
            0
        );
        assert_unpinned(&model, &roots);

        if missing_bool {
            model.bool_overrides.insert(missing, true);
        } else {
            let mut values = HashMap::default();
            values.insert(missing, BigInt::from(0x2au8));
            model.bv_model = Some(BvModel {
                values,
                term_to_bits: HashMap::default(),
                bool_overrides: HashMap::default(),
            });
        }
        // A committed scalar row must not be replaced by an inconsistent
        // pre-existing completion pin, nor silently overwrite that pin.
        let wrong_pin = if missing_bool {
            EvalValue::Bool(false)
        } else {
            EvalValue::BitVec {
                value: BigInt::from(0x2bu8),
                width: 8,
            }
        };
        model.dt_pins.insert(missing, wrong_pin.clone());
        let pins_before = model.dt_pins.clone();
        assert_eq!(
            exec.complete_euf_datatype_constructor_aliases(&mut model, &roots),
            0
        );
        assert_eq!(model.dt_pins, pins_before);
        assert_unpinned(&model, &roots);
        assert_eq!(model.dt_pins.remove(&missing), Some(wrong_pin));

        assert_eq!(
            exec.complete_euf_datatype_constructor_aliases(&mut model, &roots),
            1
        );
        assert_value(&model, proxy, &placeholder_value(0x2a));
        assert_unpinned(&model, &[constructor, missing]);
    }
}

#[test]
fn euf_constructor_aliases_keep_exact_symbol_and_sort_ownership() {
    let mut exec = fixture();
    let arg = exec.ctx.terms.mk_var("arg_proxy", sort("Arg"));
    let foreign = exec.ctx.terms.mk_var("foreign_proxy", sort("Foreign"));
    let constructor = placeholder(&mut exec, 0x2a);
    let foreign_bits = bv(&mut exec, 0x55);
    let foreign_constructor = app(&mut exec, "ForeignValue", vec![foreign_bits], "Foreign");
    let roots = [arg, foreign, constructor, foreign_constructor];
    let mut model = model_with_classes(&roots.map(|term| (term, "@shared!0")));
    assert_eq!(
        exec.complete_euf_datatype_constructor_aliases(&mut model, &roots),
        2
    );
    assert_value(&model, arg, &placeholder_value(0x2a));
    assert_value(
        &model,
        foreign,
        &ModelValue::Datatype {
            ctor: "ForeignValue".to_string(),
            args: vec![ModelValue::bitvec(BigInt::from(0x55u8), 8)],
        },
    );
    assert_unpinned(&model, &[constructor, foreign_constructor]);

    for indexed in [true, false] {
        let mut exec = fixture();
        let result_sort = if indexed { "Arg" } else { "Foreign" };
        let proxy = exec.ctx.terms.mk_var("lookalike_proxy", sort(result_sort));
        let ptr = bv(&mut exec, 0x2a);
        let funptr = bv(&mut exec, 0x7f);
        let flag = exec.ctx.terms.true_term();
        let symbol = if indexed {
            Symbol::indexed("Placeholder", vec![0])
        } else {
            Symbol::named("Placeholder")
        };
        let lookalike = exec
            .ctx
            .terms
            .mk_app(symbol, vec![ptr, funptr, flag], sort(result_sort));
        let roots = [proxy, lookalike];
        let mut model = model_with_classes(&[(proxy, "@lookalike!0"), (lookalike, "@lookalike!0")]);
        assert_eq!(
            exec.complete_euf_datatype_constructor_aliases(&mut model, &roots),
            0
        );
        assert_unpinned(&model, &roots);
    }
}

#[test]
fn euf_constructor_aliases_bound_shared_expansion_and_recovered_depth() {
    // Sixteen shared Fork levels have only 33 relevant term nodes, but
    // expanding the last value needs 131,071 ModelValue nodes. This exceeds
    // the production 65,536-node budget while keeping the old unbounded path
    // modest enough for a regression test (262,124 nodes across all aliases).
    let mut exec = fixture();
    let mut previous = exec
        .ctx
        .symbol_info_by_identity("Stop")
        .and_then(|info| info.term)
        .expect("live nullary tree constructor");
    let mut roots = vec![previous];
    let mut rows = Vec::new();
    for depth in 0..16 {
        let proxy = exec
            .ctx
            .terms
            .mk_var(format!("shared_tree_{depth}"), sort("Tree"));
        let constructor = app(&mut exec, "Fork", vec![previous, previous], "Tree");
        let token = format!("@Tree!{depth}");
        roots.extend([proxy, constructor]);
        rows.extend([(proxy, token.clone()), (constructor, token)]);
        previous = proxy;
    }
    let borrowed: Vec<_> = rows
        .iter()
        .map(|(term, token)| (*term, token.as_str()))
        .collect();
    let mut model = model_with_classes(&borrowed);
    assert_eq!(
        exec.complete_euf_datatype_constructor_aliases(&mut model, &roots),
        0
    );
    assert!(
        model.dt_ground.is_empty(),
        "budget refusal must precede every ground write"
    );
    assert!(
        model.dt_pins.is_empty(),
        "budget refusal must precede every pin write"
    );

    // A unary recovered chain stays tiny but its 65 Link nodes plus End
    // exceed the actual-tree depth bound64. Per-call syntactic depth is only
    // one when a prior alias is cloned, so checking that alone misses this.
    let mut exec = fixture();
    let mut previous = exec
        .ctx
        .symbol_info_by_identity("End")
        .and_then(|info| info.term)
        .expect("live nullary chain constructor");
    let mut roots = vec![previous];
    let mut rows = Vec::new();
    for depth in 0..65 {
        let proxy = exec
            .ctx
            .terms
            .mk_var(format!("deep_chain_{depth}"), sort("Chain"));
        let constructor = app(&mut exec, "Link", vec![previous], "Chain");
        let token = format!("@Chain!{depth}");
        roots.extend([proxy, constructor]);
        rows.extend([(proxy, token.clone()), (constructor, token)]);
        previous = proxy;
    }
    let borrowed: Vec<_> = rows
        .iter()
        .map(|(term, token)| (*term, token.as_str()))
        .collect();
    let mut model = model_with_classes(&borrowed);
    assert_eq!(
        exec.complete_euf_datatype_constructor_aliases(&mut model, &roots),
        0
    );
    assert!(
        model.dt_ground.is_empty(),
        "depth refusal must precede every ground write"
    );
    assert!(
        model.dt_pins.is_empty(),
        "depth refusal must precede every pin write"
    );
}
