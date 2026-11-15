// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

//! Exercise the actual term recovery boundary, without running an SMT solver.

use super::*;
use ay_core::term::Symbol;
use ay_core::TermId;

fn record(name: &str, constructor: &str, fields: &[(&str, ChcSort)]) -> ChcSort {
    ChcSort::Datatype {
        name: name.to_owned(),
        constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
            name: constructor.to_owned(),
            selectors: fields
                .iter()
                .map(|(name, sort)| ChcDtSelector {
                    name: (*name).to_owned(),
                    sort: sort.clone(),
                })
                .collect(),
        }]),
    }
}

fn variants(name: &str, records: &[ChcSort]) -> ChcSort {
    let mut combined = Vec::new();
    for record in records {
        let ChcSort::Datatype { constructors, .. } = record else {
            panic!("constructor fixture")
        };
        combined.extend(constructors.iter().cloned());
    }
    ChcSort::Datatype {
        name: name.to_owned(),
        constructors: crate::ChcDtConstructors::new(combined),
    }
}

fn context(records: &[ChcSort], reverse: bool) -> SmtContext {
    let mut definitions = FxHashMap::default();
    for index in 0..records.len() {
        let index = if reverse {
            records.len() - 1 - index
        } else {
            index
        };
        let ChcSort::Datatype { name, constructors } = &records[index] else {
            panic!("record fixture")
        };
        definitions.insert(
            name.clone(),
            constructors
                .iter()
                .map(|constructor| {
                    (
                        constructor.name.clone(),
                        constructor
                            .selectors
                            .iter()
                            .map(|field| (field.name.clone(), field.sort.clone()))
                            .collect(),
                    )
                })
                .collect(),
        );
    }
    let mut context = SmtContext::new();
    context.set_datatype_defs(definitions);
    context
}

fn app(name: &str, sort: ChcSort, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::FuncApp(
        name.to_owned(),
        sort,
        args.into_iter().map(Arc::new).collect(),
    )
}

fn var(name: &str, sort: &ChcSort) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, sort.clone()))
}

fn array(value: &ChcSort) -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(value.clone()))
}

fn roundtrip(context: &mut SmtContext, source: ChcExpr) {
    let term = context.convert_expr(&source);
    assert_eq!(
        context.terms.sort(term),
        &SmtContext::convert_sort(&source.sort())
    );
    assert_eq!(context.term_to_chc_expr(term), Some(source));
}

fn refused(context: &mut SmtContext, name: &str, args: &[TermId], result: &ChcSort) {
    let term = context
        .terms
        .mk_app(Symbol::named(name), args, SmtContext::convert_sort(result));
    assert_eq!(context.term_to_chc_expr(term), None, "{name}: {result:?}");
}

#[test]
fn overloaded_selectors_keep_the_actual_receiver_and_declared_return_sort() {
    let left = record(
        "Left",
        "mkLeft",
        &[("value", ChcSort::Bool), ("len", ChcSort::BitVec(64))],
    );
    let right = record(
        "Right",
        "mkRight",
        &[("value", ChcSort::BitVec(8)), ("len", ChcSort::BitVec(64))],
    );
    for reverse in [false, true] {
        let mut ctx = context(&[left.clone(), right.clone()], reverse);
        // Hash-map iteration is not insertion order: always test BOTH receivers.
        for (sort, value_sort, name) in [
            (&left, ChcSort::Bool, "left"),
            (&right, ChcSort::BitVec(8), "right"),
        ] {
            roundtrip(&mut ctx, app("value", value_sort, vec![var(name, sort)]));
            // Equal-return overloads must remain valid, not become ambiguous.
            roundtrip(
                &mut ctx,
                app("len", ChcSort::BitVec(64), vec![var(name, sort)]),
            );
        }
    }
}

#[test]
fn overloaded_constructors_match_arguments_and_the_complete_result_signature() {
    let left = record("Left", "make_cell", &[("value", ChcSort::Bool)]);
    let right = record("Right", "make_cell", &[("value", ChcSort::BitVec(8))]);
    let twin = record("Twin", "make_cell", &[("value", ChcSort::Bool)]);
    for reverse in [false, true] {
        let mut ctx = context(&[left.clone(), right.clone(), twin.clone()], reverse);
        for (sort, value) in [
            (&left, ChcExpr::Bool(true)),
            (&right, ChcExpr::BitVec(37, 8)),
            (&twin, ChcExpr::Bool(false)),
        ] {
            roundtrip(&mut ctx, app("make_cell", sort.clone(), vec![value]));
        }
    }
}

#[test]
fn overloaded_testers_require_a_declared_receiver_and_boolean_result() {
    let left = record("Left", "make_cell", &[("value", ChcSort::Bool)]);
    let right = record("Right", "make_cell", &[("value", ChcSort::BitVec(8))]);
    for reverse in [false, true] {
        let mut ctx = context(&[left.clone(), right.clone()], reverse);
        for (sort, name) in [(&left, "left"), (&right, "right")] {
            let receiver = var(name, sort);
            roundtrip(
                &mut ctx,
                app("is-make_cell", ChcSort::Bool, vec![receiver.clone()]),
            );
            let receiver = ctx.convert_expr(&receiver);
            refused(&mut ctx, "is-make_cell", &[receiver], &ChcSort::BitVec(8));
        }
        let scalar = ctx.convert_expr(&ChcExpr::Bool(true));
        refused(&mut ctx, "is-make_cell", &[scalar], &ChcSort::Bool);
        refused(&mut ctx, "is-make_cell", &[], &ChcSort::Bool);
    }
}

#[test]
fn nested_record_array_reads_preserve_each_overloaded_data_selector() {
    let inner_bv = record(
        "InnerBv",
        "mkInnerBv",
        &[
            ("len", ChcSort::BitVec(64)),
            ("data", array(&ChcSort::BitVec(8))),
        ],
    );
    let inner_bool = record(
        "InnerBool",
        "mkInnerBool",
        &[
            ("len", ChcSort::BitVec(64)),
            ("data", array(&ChcSort::Bool)),
        ],
    );
    let outer_bv = record("OuterBv", "mkOuterBv", &[("data", array(&inner_bv))]);
    let outer_bool = record("OuterBool", "mkOuterBool", &[("data", array(&inner_bool))]);
    for reverse in [false, true] {
        let mut ctx = context(
            &[
                outer_bv.clone(),
                inner_bool.clone(),
                inner_bv.clone(),
                outer_bool.clone(),
            ],
            reverse,
        );
        for (outer, inner, leaf, name) in [
            (&outer_bv, &inner_bv, ChcSort::BitVec(8), "outer_bv"),
            (&outer_bool, &inner_bool, ChcSort::Bool, "outer_bool"),
        ] {
            let cells = app("data", array(inner), vec![var(name, outer)]);
            let cell = ChcExpr::select(cells, ChcExpr::BitVec(33, 64));
            roundtrip(
                &mut ctx,
                app("len", ChcSort::BitVec(64), vec![cell.clone()]),
            );
            let data = app("data", array(&leaf), vec![cell]);
            roundtrip(&mut ctx, ChcExpr::select(data, ChcExpr::BitVec(64, 64)));
        }
    }
}

#[test]
fn selectors_refuse_wrong_receiver_result_arity_and_forged_metadata() {
    let left = record("Left", "mkLeft", &[("value", ChcSort::Bool)]);
    let right = record("Right", "mkRight", &[("value", ChcSort::BitVec(8))]);
    let foreign = record("Foreign", "mkForeign", &[("other", ChcSort::Bool)]);
    let forged = record("Left", "mkLeft", &[("value", ChcSort::BitVec(8))]);
    for reverse in [false, true] {
        let mut ctx = context(&[left.clone(), right.clone(), foreign.clone()], reverse);
        let left_term = ctx.convert_expr(&var("left", &left));
        let right_term = ctx.convert_expr(&var("right", &right));
        let foreign_term = ctx.convert_expr(&var("foreign", &foreign));
        let forged_term = ctx.convert_expr(&var("forged", &forged));
        let scalar = ctx.convert_expr(&ChcExpr::Bool(true));
        refused(&mut ctx, "value", &[left_term], &ChcSort::BitVec(8));
        refused(&mut ctx, "value", &[right_term], &ChcSort::Bool);
        refused(&mut ctx, "value", &[foreign_term], &ChcSort::Bool);
        refused(&mut ctx, "value", &[forged_term], &ChcSort::Bool);
        refused(&mut ctx, "value", &[forged_term], &ChcSort::BitVec(8));
        refused(&mut ctx, "value", &[scalar], &ChcSort::Bool);
        refused(&mut ctx, "value", &[], &ChcSort::Bool);
        refused(&mut ctx, "value", &[left_term, left_term], &ChcSort::Bool);
        refused(&mut ctx, "is-mkLeft", &[foreign_term], &ChcSort::Bool);
        refused(&mut ctx, "is-mkLeft", &[forged_term], &ChcSort::Bool);
    }
}

#[test]
fn constructors_refuse_wrong_arguments_results_and_nested_metadata() {
    let inner = record("Inner", "mkInner", &[("value", ChcSort::Bool)]);
    let outer = record("Outer", "mkOuter", &[("cell", inner.clone())]);
    let byte = record("Byte", "mkByte", &[("byte", ChcSort::BitVec(8))]);
    let forged_inner = record("Inner", "mkInner", &[("value", ChcSort::BitVec(8))]);
    let forged_outer = record("Outer", "mkOuter", &[("cell", forged_inner.clone())]);
    let mut ctx = context(&[inner.clone(), outer.clone(), byte.clone()], false);
    let boolean = ctx.convert_expr(&ChcExpr::Bool(true));
    let bitvec = ctx.convert_expr(&ChcExpr::BitVec(1, 8));
    let valid_inner = ctx.convert_expr(&app("mkInner", inner.clone(), vec![ChcExpr::Bool(true)]));
    let bad_inner = ctx.convert_expr(&var("bad_inner", &forged_inner));
    refused(&mut ctx, "mkInner", &[bitvec], &inner);
    refused(&mut ctx, "mkInner", &[boolean], &forged_inner);
    refused(&mut ctx, "mkInner", &[boolean], &ChcSort::Bool);
    refused(&mut ctx, "mkInner", &[], &inner);
    refused(&mut ctx, "mkInner", &[boolean, boolean], &inner);
    refused(&mut ctx, "mkOuter", &[bad_inner], &outer);
    refused(&mut ctx, "mkOuter", &[valid_inner], &forged_outer);
    // The raw child claims BV8, so the constructor's raw signature matches.
    // Recovery reveals BV16 operands/result and must fail its second check.
    let wide = ctx.convert_expr(&ChcExpr::BitVec(1, 16));
    let bad_child = ctx.terms.mk_app(
        Symbol::named("bvadd"),
        [wide, wide],
        ay_core::Sort::bitvec(8),
    );
    assert_eq!(
        ctx.term_to_chc_expr(bad_child).map(|expr| expr.sort()),
        Some(ChcSort::BitVec(16))
    );
    refused(&mut ctx, "mkByte", &[bad_child], &byte);
    roundtrip(
        &mut ctx,
        app(
            "mkOuter",
            outer,
            vec![app("mkInner", inner, vec![ChcExpr::Bool(true)])],
        ),
    );
}

#[test]
fn absent_or_unrelated_datatype_declarations_do_not_authorize_arbitrary_ufs() {
    let declared = record("Declared", "mkDeclared", &[("value", ChcSort::Bool)]);
    let undeclared = record("Undeclared", "mkUndeclared", &[("value", ChcSort::Bool)]);
    for records in [Vec::new(), vec![declared]] {
        let mut ctx = context(&records, false);
        let boolean = ctx.convert_expr(&ChcExpr::Bool(true));
        refused(&mut ctx, "ordinary_uf", &[boolean], &ChcSort::Bool);
        refused(&mut ctx, "mkUndeclared", &[boolean], &undeclared);
        let receiver = ctx.convert_expr(&var("undeclared", &undeclared));
        refused(&mut ctx, "value", &[receiver], &ChcSort::Bool);
        refused(&mut ctx, "is-mkUndeclared", &[receiver], &ChcSort::Bool);
    }
}

#[test]
fn duplicate_constructor_or_field_declarations_refuse_recovery() {
    let single = record("Duplicate", "mkDuplicate", &[("value", ChcSort::Bool)]);
    let duplicate_constructors = variants("Duplicate", &[single.clone(), single]);
    let duplicate_fields = record(
        "Duplicate",
        "mkDuplicate",
        &[("value", ChcSort::Bool), ("value", ChcSort::Bool)],
    );
    for declaration in [duplicate_constructors, duplicate_fields] {
        let mut ctx = context(std::slice::from_ref(&declaration), false);
        let receiver = ctx.convert_expr(&var("receiver", &declaration));
        let boolean = ctx.convert_expr(&ChcExpr::Bool(true));
        refused(&mut ctx, "value", &[receiver], &ChcSort::Bool);
        refused(&mut ctx, "is-mkDuplicate", &[receiver], &ChcSort::Bool);
        for arguments in [vec![boolean], vec![boolean, boolean]] {
            refused(&mut ctx, "mkDuplicate", &arguments, &declaration);
        }
    }
}

#[test]
fn selectors_shared_across_constructors_are_valid_but_operation_kind_collisions_refuse() {
    let choice = variants(
        "Choice",
        &[
            record("Choice", "left", &[("value", ChcSort::Bool)]),
            record("Choice", "right", &[("value", ChcSort::Bool)]),
        ],
    );
    let tester_collision = record("Conflict", "ctor", &[("is-ctor", ChcSort::Bool)]);
    // An inhabited recursive type makes both clash(T)->T interpretations real:
    // one constructor and one selector, not merely equal result sorts.
    let constructor_collision = variants(
        "Recursive",
        &[
            record("Recursive", "end", &[]),
            record(
                "Recursive",
                "clash",
                &[("clash", ChcSort::Uninterpreted("Recursive".into()))],
            ),
        ],
    );
    let mut ctx = context(
        &[
            choice.clone(),
            tester_collision.clone(),
            constructor_collision.clone(),
        ],
        false,
    );
    for name in ["value", "is-left", "is-right"] {
        roundtrip(
            &mut ctx,
            app(name, ChcSort::Bool, vec![var("choice", &choice)]),
        );
    }
    let receiver = ctx.convert_expr(&var("conflict", &tester_collision));
    refused(&mut ctx, "is-ctor", &[receiver], &ChcSort::Bool);
    let recursive = ctx.convert_expr(&var("recursive", &constructor_collision));
    refused(&mut ctx, "clash", &[recursive], &constructor_collision);
}

#[test]
fn registered_recursive_references_recover_full_receiver_and_array_cell_sorts() {
    let reference = ChcSort::Uninterpreted("List".into());
    let list = variants(
        "List",
        &[
            record("List", "nil", &[]),
            record(
                "List",
                "cons",
                &[
                    ("head", ChcSort::Bool),
                    ("tail", reference.clone()),
                    ("branches", array(&reference)),
                ],
            ),
        ],
    );
    let mut ctx = context(std::slice::from_ref(&list), false);
    let tail = var("tail", &list);
    let branches = var("branches", &array(&list));
    roundtrip(&mut ctx, app("nil", list.clone(), vec![]));
    roundtrip(
        &mut ctx,
        app(
            "cons",
            list.clone(),
            vec![ChcExpr::Bool(true), tail.clone(), branches],
        ),
    );
    roundtrip(&mut ctx, app("tail", list.clone(), vec![tail.clone()]));
    let children = app("branches", array(&list), vec![tail]);
    roundtrip(&mut ctx, children.clone());
    roundtrip(
        &mut ctx,
        app(
            "head",
            ChcSort::Bool,
            vec![ChcExpr::select(children, ChcExpr::BitVec(33, 64))],
        ),
    );
    // A bare nominal reference is not an authenticated full receiver.
    let nominal = ctx.convert_expr(&var("nominal", &reference));
    refused(&mut ctx, "tail", &[nominal], &list);
    let forged = record("List", "cons", &[("head", ChcSort::BitVec(8))]);
    let forged = ctx.convert_expr(&var("forged", &forged));
    refused(&mut ctx, "tail", &[forged], &list);
    let unregistered = record("Foreign", "mkForeign", &[]);
    let unregistered = ctx.convert_expr(&var("foreign", &unregistered));
    refused(&mut ctx, "tail", &[unregistered], &list);
}

#[test]
fn unsupported_nested_core_sorts_cannot_be_laundered_through_lossy_chc_metadata() {
    use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

    for (name, unsupported) in [
        ("String", Sort::String),
        ("FloatingPoint_8_24", Sort::FloatingPoint(8, 24)),
    ] {
        let declared_cell = ChcSort::Uninterpreted(name.into());
        let holder = record("Holder", "mkHolder", &[("data", array(&declared_cell))]);
        let mut ctx = context(std::slice::from_ref(&holder), false);
        let raw_array = Sort::array(Sort::bitvec(64), unsupported);
        let raw_value = ctx.terms.mk_var("unsupported", raw_array.clone());
        refused(&mut ctx, "mkHolder", &[raw_value], &holder);
        let forged = Sort::Datatype(DatatypeSort::new(
            "Holder",
            vec![DatatypeConstructor::new(
                "mkHolder",
                vec![DatatypeField::new("data", raw_array)],
            )],
        ));
        let receiver = ctx.terms.mk_var("forged_holder", forged);
        refused(&mut ctx, "data", &[receiver], &array(&declared_cell));
        refused(&mut ctx, "is-mkHolder", &[receiver], &ChcSort::Bool);
    }
}
