// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The native lane never answers under a datatype definition other than the
//! one the checked expression API authenticated the assertion against. The
//! program refuses a conflicting definition at declaration; when the
//! declarations bypass the program (constraints pushed directly, in either
//! order), the lowering's own registry check refuses them before the solver.

use super::*;
use crate::constraint::Constraint;
use crate::program::AYProgram;

fn level() -> Sort {
    Sort::enum_type(
        "Level",
        vec![
            ("zero", vec![]),
            ("succ", vec![("pred", Sort::datatype_ref("Level"))]),
        ],
    )
}

fn block_small() -> Sort {
    Sort::enum_type("Block", vec![("leaf", Vec::<(&str, Sort)>::new())])
}

fn block_big() -> Sort {
    Sort::enum_type(
        "Block",
        vec![("leaf", vec![]), ("other", vec![("n", Sort::int())])],
    )
}

fn tower_with_top(top: Sort) -> Sort {
    Sort::enum_type(
        "Tower",
        vec![
            ("empty", vec![]),
            (
                "stack",
                vec![("top", top), ("rest", Sort::datatype_ref("Tower"))],
            ),
        ],
    )
}

/// Push a datatype declaration without the program's authentication.
fn inject_datatype(program: &mut AYProgram, sort: &Sort) {
    program.commands.push(Constraint::declare_datatype(
        sort.datatype_sort().unwrap().clone(),
    ));
}

/// Push a constant declaration without the program's authentication.
fn inject_const(program: &mut AYProgram, name: &str, sort: Sort) -> Expr {
    program
        .commands
        .push(Constraint::declare_const(name, sort.clone()));
    Expr::var(name, sort)
}

fn assert_refused_at_lowering(result: Result<ExecuteResult, ExecuteError>, what: &str) {
    assert!(
        matches!(
            result,
            Err(ExecuteError::SortTranslation(_) | ExecuteError::ExprTranslation(_))
        ),
        "{what} must be refused before the solver answers, got {result:?}"
    );
}

/// The trust-types `Level` shapes natively: constructor, selector, tester and
/// equality, acyclicity included.
#[test]
fn test_level_shapes_execute_natively() {
    let dt = level().datatype_sort().unwrap().clone();
    // succ l = l is refutable (acyclicity).
    let mut p = AYProgram::new();
    p.set_logic("ALL");
    p.declare_datatype(dt.clone());
    let l = p.declare_const("l", level());
    let succ = Expr::try_datatype_constructor("Level", "succ", vec![l.clone()], level()).unwrap();
    p.assert(succ.clone().try_eq(l.clone()).unwrap());
    p.check_sat();
    let r = execute(&p).unwrap();
    assert!(
        matches!(r, ExecuteResult::Verified),
        "succ l = l must be UNSAT, got {r:?}"
    );

    // is_succ (succ l) holds.
    let mut p = AYProgram::new();
    p.set_logic("ALL");
    p.declare_datatype(dt.clone());
    let l = p.declare_const("l", level());
    let succ = Expr::try_datatype_constructor("Level", "succ", vec![l.clone()], level()).unwrap();
    p.assert(succ.try_is_constructor("Level", "succ").unwrap().not());
    p.check_sat();
    let r = execute(&p).unwrap();
    assert!(
        matches!(r, ExecuteResult::Verified),
        "is_succ (succ l) must hold, got {r:?}"
    );

    // pred (succ l) = l.
    let mut p = AYProgram::new();
    p.set_logic("ALL");
    p.declare_datatype(dt.clone());
    let l = p.declare_const("l", level());
    let succ = Expr::try_datatype_constructor("Level", "succ", vec![l.clone()], level()).unwrap();
    let pred = succ.try_field_select("Level", "pred", level()).unwrap();
    p.assert(pred.try_eq(l).unwrap().not());
    p.check_sat();
    let r = execute(&p).unwrap();
    assert!(
        matches!(r, ExecuteResult::Verified),
        "pred (succ l) = l, got {r:?}"
    );

    // exists m. m = succ zero.
    let mut p = AYProgram::new();
    p.set_logic("ALL");
    p.declare_datatype(dt);
    let m = p.declare_const("m", level());
    let zero = Expr::try_datatype_constructor("Level", "zero", vec![], level()).unwrap();
    let sz = Expr::try_datatype_constructor("Level", "succ", vec![zero], level()).unwrap();
    p.assert(m.try_eq(sz).unwrap());
    p.check_sat();
    let r = execute(&p).unwrap();
    assert!(
        matches!(r, ExecuteResult::Counterexample { .. }),
        "m = succ zero SAT, got {r:?}"
    );
}

/// A `Block` inlined in `Tower` that differs from the registered `Block`:
/// under the inlined descriptor two tops can be distinct (SAT), under the
/// registered one they cannot (Verified). The program refuses the second
/// declaration in either order; with both declarations injected, the
/// lowering refuses the program before the solver answers.
#[test]
fn test_nested_inline_definition_differing_from_the_registry_never_reaches_the_solver() {
    for (registered, inlined) in [(block_small(), block_big()), (block_big(), block_small())] {
        let tower = tower_with_top(inlined.clone());
        for registry_first in [true, false] {
            let mut p = AYProgram::new();
            p.set_logic("ALL");
            let (first, second) = if registry_first {
                (registered.clone(), tower.clone())
            } else {
                (tower.clone(), registered.clone())
            };
            assert!(p
                .try_declare_datatype(first.datatype_sort().unwrap().clone())
                .unwrap());
            assert!(p
                .try_declare_datatype(second.datatype_sort().unwrap().clone())
                .is_err());

            let mut p = AYProgram::new();
            p.set_logic("ALL");
            inject_datatype(&mut p, &first);
            inject_datatype(&mut p, &second);
            let x = inject_const(&mut p, "x", tower.clone());
            let y = inject_const(&mut p, "y", tower.clone());
            p.assert(x.clone().try_is_constructor("Tower", "stack").unwrap());
            p.assert(y.clone().try_is_constructor("Tower", "stack").unwrap());
            let tx = x.try_field_select("Tower", "top", inlined.clone()).unwrap();
            let ty = y.try_field_select("Tower", "top", inlined.clone()).unwrap();
            p.assert(Expr::try_distinct(vec![tx, ty]).unwrap());
            p.check_sat();
            assert_refused_at_lowering(
                execute(&p),
                "a Tower inlining a Block that differs from the declared Block",
            );
        }
    }
}

/// A same-named inner `Level` with a constructor the outer one lacks: the
/// assertion is satisfiable under the inner (authenticated) descriptor and
/// unsatisfiable under the outer one the solver would register. Refused at
/// declaration, and at lowering when injected.
#[test]
fn test_shadowing_definition_never_reaches_the_solver() {
    let inner = Sort::enum_type(
        "Level",
        vec![
            ("zero", vec![]),
            ("one", vec![]),
            ("succ", vec![("pred", Sort::datatype_ref("Level"))]),
        ],
    );
    let outer = Sort::enum_type(
        "Level",
        vec![("zero", vec![]), ("succ", vec![("pred", inner.clone())])],
    );
    let mut p = AYProgram::new();
    p.set_logic("ALL");
    assert!(p
        .try_declare_datatype(outer.datatype_sort().unwrap().clone())
        .is_err());
    assert!(p.try_declare_const("x", outer.clone()).is_err());

    inject_datatype(&mut p, &outer);
    let x = inject_const(&mut p, "x", outer.clone());
    p.assert(x.clone().try_is_constructor("Level", "succ").unwrap());
    let px = x.try_field_select("Level", "pred", inner.clone()).unwrap();
    p.assert(
        px.clone()
            .try_is_constructor("Level", "zero")
            .unwrap()
            .not(),
    );
    p.assert(px.try_is_constructor("Level", "succ").unwrap().not());
    p.check_sat();
    assert_refused_at_lowering(execute(&p), "a same-named shadowing definition");

    // The singleton variant, distinct tops under a `{zero}` inner Level.
    let inner = Sort::enum_type("Level", vec![("zero", Vec::<(&str, Sort)>::new())]);
    let outer = Sort::enum_type("Level", vec![("succ", vec![("pred", inner.clone())])]);
    let mut p = AYProgram::new();
    p.set_logic("ALL");
    assert!(p
        .try_declare_datatype(outer.datatype_sort().unwrap().clone())
        .is_err());
    inject_datatype(&mut p, &outer);
    let x = inject_const(&mut p, "x", outer.clone());
    let y = inject_const(&mut p, "y", outer.clone());
    let px = x.try_field_select("Level", "pred", inner.clone()).unwrap();
    let py = y.try_field_select("Level", "pred", inner).unwrap();
    p.assert(Expr::try_distinct(vec![px, py]).unwrap());
    p.check_sat();
    assert_refused_at_lowering(execute(&p), "a same-named shadowing definition");
}

/// A constant whose descriptor differs from the registered definition of its
/// name (an extra nullary constructor on either side): refused by
/// `try_declare_const`, and at lowering when injected.
#[test]
fn test_constant_descriptor_differing_from_the_registry_never_reaches_the_solver() {
    let v1 = level();
    let v2 = Sort::enum_type(
        "Level",
        vec![
            ("zero", vec![]),
            ("succ", vec![("pred", Sort::datatype_ref("Level"))]),
            ("extra", vec![]),
        ],
    );
    for (registered, other) in [(v1.clone(), v2.clone()), (v2, v1)] {
        let mut p = AYProgram::new();
        p.set_logic("ALL");
        p.declare_datatype(registered.datatype_sort().unwrap().clone());
        assert!(p.try_declare_const("x", other.clone()).is_err());
        let x = inject_const(&mut p, "x", other.clone());
        // Under `other`: `not zero and not succ` is SAT iff `other` is v2.
        p.assert(x.clone().try_is_constructor("Level", "zero").unwrap().not());
        p.assert(x.try_is_constructor("Level", "succ").unwrap().not());
        p.check_sat();
        assert_refused_at_lowering(
            execute(&p),
            "a constant of a descriptor that differs from the declared one",
        );

        // A term of the other descriptor over a properly declared constant is
        // refused the same way, through the constructor's own sort.
        let mut p = AYProgram::new();
        p.set_logic("ALL");
        p.declare_datatype(registered.datatype_sort().unwrap().clone());
        let x = p.declare_const("x", registered.clone());
        let zero = Expr::try_datatype_constructor("Level", "zero", vec![], other.clone()).unwrap();
        p.assert(x.try_is_constructor("Level", "zero").unwrap());
        p.assert(zero.try_is_constructor("Level", "zero").unwrap());
        p.check_sat();
        assert_refused_at_lowering(
            execute(&p),
            "a constructor term of a descriptor that differs from the declared one",
        );
    }
}

/// Mutually recursive datatypes spelled as two declarations are refused at
/// the program; injected, the first declaration nests a definition that
/// refers back out to it and is refused at lowering.
#[test]
fn test_mutual_recursion_is_refused_at_declaration_and_lowering() {
    let b_in_a = |ba: Sort| Sort::enum_type("B", vec![("b0", vec![]), ("mk_b", vec![("ba", ba)])]);
    let a_with = |ab: Sort| Sort::enum_type("A", vec![("mk_a", vec![("ab", ab)])]);
    let a_top = a_with(b_in_a(Sort::datatype_ref("A")));
    let b_top = b_in_a(a_with(Sort::datatype_ref("B")));
    let mut p = AYProgram::new();
    p.set_logic("ALL");
    assert!(p
        .try_declare_datatype(a_top.datatype_sort().unwrap().clone())
        .is_err());
    assert!(p
        .try_declare_datatype(b_top.datatype_sort().unwrap().clone())
        .is_err());
    assert!(p.try_declare_const("a", a_top.clone()).is_err());
    inject_datatype(&mut p, &a_top);
    inject_datatype(&mut p, &b_top);
    let a = inject_const(&mut p, "a", a_top.clone());
    let b = inject_const(&mut p, "b", b_top);
    let mk_a = Expr::try_datatype_constructor("A", "mk_a", vec![b], a_top).unwrap();
    p.assert(a.try_eq(mk_a).unwrap());
    p.check_sat();
    let r = execute(&p);
    assert!(
        r.is_err(),
        "genuine mutual recursion must not be admitted natively: {r:?}"
    );
}
