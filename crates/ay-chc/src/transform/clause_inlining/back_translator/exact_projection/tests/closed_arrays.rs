// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn array(name: &str) -> ChcVar {
    ChcVar::new(
        name,
        ChcSort::Array(Box::new(ChcSort::BitVec(1)), Box::new(ChcSort::Bool)),
    )
}

fn constant(value: bool) -> ChcExpr {
    ChcExpr::ConstArray(ChcSort::BitVec(1), Arc::new(ChcExpr::Bool(value)))
}

fn fixture() -> (ChcExpr, Vec<ChcVar>) {
    let memory = array("memory");
    let index = var("index", 1);
    let image = var("image", 2);
    let local = var("local", 2);
    let guard = eq(
        expr(&memory),
        op(
            ChcOp::Store,
            vec![constant(false), expr(&index), ChcExpr::Bool(true)],
        ),
    );
    (
        op(
            ChcOp::And,
            vec![guard, eq(expr(&image), quotient(&local, 2))],
        ),
        vec![memory, index, image],
    )
}

#[test]
fn retained_array_guard_and_scalar_existential_match_every_tiny_model() {
    let (formula, keep) = fixture();
    let projected = closed(&formula, &keep);
    assert!(projected.vars().iter().all(|var| keep.contains(var)));
    for memory in 0..4 {
        for index in 0..2 {
            for image in 0..4 {
                let values = [("memory", memory), ("index", index), ("image", image)];
                let exists = (0..4).any(|local| {
                    oracle::truth(
                        &formula,
                        &[values[0], values[1], values[2], ("local", local)],
                    )
                });
                assert_eq!(
                    oracle::truth(&projected, &values),
                    exists,
                    "memory={memory}, index={index}, image={image}"
                );
            }
        }
    }
}

#[test]
fn array_extensional_equality_closed_or_select_and_ite_are_preserved() {
    let memory = array("memory");
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let all_false = op(
        ChcOp::Store,
        vec![
            op(
                ChcOp::Store,
                vec![constant(true), ChcExpr::BitVec(0, 1), ChcExpr::Bool(false)],
            ),
            ChcExpr::BitVec(1, 1),
            ChcExpr::Bool(false),
        ],
    );
    let guard = op(
        ChcOp::Or,
        vec![
            eq(expr(&memory), all_false),
            op(
                ChcOp::Select,
                vec![
                    op(
                        ChcOp::Ite,
                        vec![expr(&flag), expr(&memory), constant(false)],
                    ),
                    ChcExpr::BitVec(0, 1),
                ],
            ),
        ],
    );
    let projected = closed(&guard, &[memory, flag]);
    for memory in 0..4 {
        for flag in 0..2 {
            let values = [("memory", memory), ("flag", flag)];
            assert_eq!(
                oracle::truth(&projected, &values),
                oracle::truth(&guard, &values)
            );
            assert_eq!(
                oracle::truth(&projected, &values),
                memory == 0 || (flag == 1 && memory & 1 == 1)
            );
        }
    }
}

#[test]
fn unused_non_scalar_formals_do_not_enter_the_scalar_arena() {
    let image = var("image", 2);
    let local = var("local", 2);
    let keep = vec![
        array("unused_array"),
        ChcVar::new("unused_int", ChcSort::Int),
        ChcVar::new("unused_real", ChcSort::Real),
        ChcVar::new("unused_sort", ChcSort::Uninterpreted("Opaque".into())),
        var("unused_wide", 129),
        image,
    ];
    let arena = Arena::new(&keep, &mut Scope::new(Limits::default(), &|| true)).unwrap();
    // Since 5eb47055a the arena holds flat arrays: the flat array formal is a
    // retained arena variable; the unsupported scalar formals stay outside.
    assert_eq!(arena.vars, vec![&keep[0], &keep[5]]);
    assert_eq!(arena.kept, 2);
    let projected = closed(&eq(expr(&keep[5]), quotient(&local, 2)), &keep);
    for image in 0..4 {
        assert_eq!(oracle::truth(&projected, &[("image", image)]), image < 2);
    }
    assert_eq!(closed(&ChcExpr::Bool(true), &keep), ChcExpr::Bool(true));
}

/// Every value of a tiny fixture sort (a `BitVec(1) -> Bool` array has four).
fn tiny_domain(var: &ChcVar) -> u128 {
    match var.sort {
        ChcSort::Bool => 2,
        ChcSort::BitVec(width) => 1u128 << width,
        _ => 4,
    }
}

/// Every assignment of `vars` over their tiny domains.
fn tiny_assignments(vars: &[&ChcVar]) -> Vec<Vec<(String, u128)>> {
    let mut all: Vec<Vec<(String, u128)>> = vec![Vec::new()];
    for &var in vars {
        let mut next = Vec::new();
        for prefix in &all {
            for value in 0..tiny_domain(var) {
                let mut assignment = prefix.clone();
                assignment.push((var.name.clone(), value));
                next.push(assignment);
            }
        }
        all = next;
    }
    all
}

/// Since 5eb47055a the arena eliminates an array local through an
/// occurs-checked definition. A local is never erased: the projection either
/// declines or is exactly `exists locals. formula` over every tiny model, and
/// names no local.
fn declined_or_exact(formula: &ChcExpr, keep: &[ChcVar], locals: &[&ChcVar]) {
    let projected = match run(formula, keep, &mut Scope::new(Limits::default(), &|| true)) {
        Projection::Declined => return,
        Projection::Closed(projected) => projected,
        Projection::Stopped => panic!("fixture exhausted the projection scope"),
    };
    assert!(projected.vars().iter().all(|var| keep.contains(var)));
    let kept: Vec<&ChcVar> = keep.iter().collect();
    for outer in tiny_assignments(&kept) {
        let expected = tiny_assignments(locals).into_iter().any(|inner| {
            let values: Vec<(&str, u128)> = outer
                .iter()
                .chain(inner.iter())
                .map(|(name, value)| (name.as_str(), *value))
                .collect();
            oracle::truth(formula, &values)
        });
        let values: Vec<(&str, u128)> = outer
            .iter()
            .map(|(name, value)| (name.as_str(), *value))
            .collect();
        assert_eq!(oracle::truth(&projected, &values), expected);
    }
}

#[test]
fn array_locals_in_base_indices_values_and_mixed_or_are_not_erased() {
    let memory = array("memory");
    let local_array = array("local_array");
    let index = var("index", 1);
    let value = ChcVar::new("value", ChcSort::Bool);
    let local = var("local", 2);
    let image = var("image", 2);
    for atom in [
        eq(expr(&memory), expr(&local_array)),
        op(ChcOp::Select, vec![expr(&memory), expr(&index)]),
        eq(
            expr(&memory),
            op(
                ChcOp::Store,
                vec![constant(false), ChcExpr::BitVec(0, 1), expr(&value)],
            ),
        ),
        eq(
            expr(&memory),
            ChcExpr::ConstArray(ChcSort::BitVec(1), Arc::new(expr(&value))),
        ),
        op(
            ChcOp::Select,
            vec![expr(&local_array), ChcExpr::BitVec(0, 1)],
        ),
        op(
            ChcOp::Or,
            vec![
                eq(expr(&memory), constant(false)),
                eq(expr(&image), quotient(&local, 2)),
            ],
        ),
    ] {
        let keep = [memory.clone(), image.clone()];
        let locals = [&local_array, &index, &value, &local];
        declined_or_exact(&atom, &keep, &locals);
        declined_or_exact(
            &op(ChcOp::And, vec![ChcExpr::Bool(false), atom]),
            &keep,
            &locals,
        );
    }
}

#[test]
fn full_retained_registry_rejects_duplicates_and_conflicting_occurrences() {
    let memory = array("same");
    declined(&ChcExpr::Bool(true), &[memory.clone(), memory.clone()]);
    declined(&ChcExpr::Bool(true), &[memory.clone(), var("same", 2)]);
    declined(
        &eq(expr(&var("same", 2)), ChcExpr::BitVec(0, 2)),
        &[memory.clone()],
    );
    let wrong_array = ChcVar::new(
        "same",
        ChcSort::Array(Box::new(ChcSort::BitVec(2)), Box::new(ChcSort::Bool)),
    );
    declined(&eq(expr(&wrong_array), expr(&wrong_array)), &[memory]);
}

#[test]
fn malformed_array_guards_are_rejected_even_in_dead_source_arms() {
    let memory = array("memory");
    let bad = [
        op(ChcOp::Select, vec![expr(&memory), ChcExpr::BitVec(0, 2)]),
        eq(
            expr(&memory),
            op(
                ChcOp::Store,
                vec![expr(&memory), ChcExpr::BitVec(0, 1), ChcExpr::BitVec(0, 1)],
            ),
        ),
        eq(
            expr(&memory),
            ChcExpr::ConstArray(ChcSort::BitVec(0), Arc::new(ChcExpr::Bool(false))),
        ),
        op(ChcOp::Select, vec![expr(&memory), ChcExpr::BitVec(2, 1)]),
        eq(
            expr(&memory),
            ChcExpr::FuncApp("opaque".into(), memory.sort.clone(), vec![]),
        ),
        eq(expr(&memory), ChcExpr::ConstArrayMarker(ChcSort::BitVec(1))),
        op(ChcOp::And, vec![eq(expr(&memory), constant(false))]),
    ];
    for atom in bad {
        declined(
            &op(ChcOp::Or, vec![ChcExpr::Bool(true), atom]),
            std::slice::from_ref(&memory),
        );
    }
}

/// Nested array sorts remain unsupported (5eb47055a,
/// `arrays::negative::opaque_functions_markers_and_nested_array_sorts_remain_unsupported`);
/// a full-width flat array guard is still preserved without scalarization.
#[test]
fn nested_array_sorts_decline_and_full_width_flat_guards_are_preserved() {
    let value = ChcExpr::ConstArray(
        ChcSort::BitVec(64),
        Arc::new(ChcExpr::BitVec(u128::MAX, 128)),
    );
    let flat_sort = ChcSort::Array(
        Box::new(ChcSort::BitVec(64)),
        Box::new(ChcSort::BitVec(128)),
    );
    let nested = ChcExpr::ConstArray(ChcSort::BitVec(2), Arc::new(value.clone()));
    let sort = ChcSort::Array(Box::new(ChcSort::BitVec(2)), Box::new(flat_sort.clone()));
    let memory = ChcVar::new("memory", sort);
    declined(&eq(expr(&memory), nested), &[memory]);

    let wide = ChcVar::new("wide", flat_sort);
    let guard = eq(expr(&wide), value);
    let projected = closed(&guard, std::slice::from_ref(&wide));
    let ChcExpr::Op(ChcOp::And, args) = &projected else {
        panic!("preserved conjunction")
    };
    assert_eq!(args[0].as_ref(), &guard);
    assert_eq!(args[1].as_ref(), &ChcExpr::Bool(true));
}

#[test]
fn array_partition_copy_and_scalar_projection_share_one_terminal_scope() {
    let (formula, keep) = fixture();
    resources::assert_poll_boundaries(&formula, &keep);
    resources::assert_numeric_boundaries(&formula, &keep);
    let guard = eq(expr(&keep[0]), constant(false));
    resources::assert_poll_boundaries(&guard, &keep);
    resources::assert_numeric_boundaries(&guard, &keep);
}

#[test]
fn scope_remains_terminal_after_a_foreign_owner_panics() {
    let calls = std::cell::Cell::new(0);
    let open = || {
        calls.set(calls.get() + 1);
        panic!("owner panic");
    };
    let mut scope = Scope::new(Limits::default(), &open);
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| scope.poll())).is_err());
    assert_eq!(scope.poll(), Err(Failure::Stopped));
    assert_eq!(calls.get(), 1);
}

#[test]
fn unused_formal_names_and_nested_sort_spines_are_not_free_work() {
    let keep = [ChcVar::new(
        "unused",
        ChcSort::Uninterpreted("s".repeat(4096)),
    )];
    let mut scope = Scope::new(
        Limits {
            work: 128,
            ..Limits::default()
        },
        &|| true,
    );
    assert!(matches!(
        run(&ChcExpr::Bool(true), &keep, &mut scope),
        Projection::Stopped
    ));
    assert!(matches!(
        run(&ChcExpr::Bool(true), &[], &mut scope),
        Projection::Stopped
    ));

    let mut sort = ChcSort::Bool;
    for _ in 0..8 {
        sort = ChcSort::Array(Box::new(ChcSort::BitVec(1)), Box::new(sort));
    }
    let keep = [ChcVar::new("unused", sort)];
    let mut scope = Scope::new(
        Limits {
            depth: 4,
            ..Limits::default()
        },
        &|| true,
    );
    assert!(matches!(
        run(&ChcExpr::Bool(true), &keep, &mut scope),
        Projection::Stopped
    ));
}
