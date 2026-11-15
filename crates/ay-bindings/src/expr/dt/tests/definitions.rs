// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One datatype definition per name, everywhere a descriptor enters the
//! program: the checked expression API never mixes two same-named
//! definitions, `try_declare_datatype` authenticates every nested definition
//! against the enclosing declaration and the registry, `try_declare_const`
//! authenticates the constant's sort the same way, and a sort containing a
//! dangling reference is the same sort as nothing.

#![cfg(test)]

use super::super::check::Check;
use super::{raw_constructor, raw_ite};
use crate::expr::{Expr, ExprValue};
use crate::program::AYProgram;
use crate::sort::Sort;
use crate::SortError;

/// `(declare-datatype Level ((zero) (succ (pred Level))))`
fn level() -> Sort {
    Sort::enum_type(
        "Level",
        vec![
            ("zero", vec![]),
            ("succ", vec![("pred", Sort::datatype_ref("Level"))]),
        ],
    )
}

/// `Block { leaf }`
fn block_small() -> Sort {
    Sort::enum_type("Block", vec![("leaf", Vec::<(&str, Sort)>::new())])
}

/// `Block { leaf | other (n: Int) }`
fn block_big() -> Sort {
    Sort::enum_type(
        "Block",
        vec![("leaf", vec![]), ("other", vec![("n", Sort::int())])],
    )
}

/// `Tower { empty | stack (top: <top>, rest: Tower) }`
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

fn refusal<T: std::fmt::Debug>(result: Result<T, SortError>) -> String {
    match result {
        Err(error) => error.to_string(),
        Ok(admitted) => panic!("expected a refusal, got Ok({admitted:?})"),
    }
}

fn declare(program: &mut AYProgram, sort: &Sort) -> Result<bool, SortError> {
    program.try_declare_datatype(sort.datatype_sort().unwrap().clone())
}

/// The exact trust-types `Level` example through the checked API, and its
/// SMT-LIB spelling through the program.
#[test]
fn trust_level_example_end_to_end() {
    let l = Expr::var("l", level());
    let succ = Expr::try_datatype_constructor("Level", "succ", vec![l.clone()], level()).unwrap();
    assert_eq!(succ.to_string(), "(succ l)");
    let pred = succ
        .clone()
        .try_field_select("Level", "pred", level())
        .unwrap();
    assert_eq!(pred.to_string(), "(pred (succ l))");
    assert!(matches!(pred.value(), ExprValue::DatatypeSelector { .. }));
    assert_eq!(pred.sort(), &level());
    let tester = succ.clone().try_is_constructor("Level", "succ").unwrap();
    assert_eq!(tester.to_string(), "((_ is succ) (succ l))");
    let eq = succ.clone().try_eq(succ.clone()).unwrap();
    assert_eq!(eq.to_string(), "(= (succ l) (succ l))");
    let eq2 = pred.try_eq(l.clone()).unwrap();
    assert_eq!(eq2.to_string(), "(= (pred (succ l)) l)");
    let fidelity = succ.clone().try_eq(l).unwrap();
    assert_eq!(fidelity.to_string(), "(= (succ l) l)");
    let mut program = AYProgram::new();
    program.set_logic("ALL");
    assert!(declare(&mut program, &level()).unwrap());
    let x = program.try_declare_const("x", level()).unwrap();
    program.assert(x.try_is_constructor("Level", "zero").unwrap());
    let text = program.to_string();
    assert!(
        text.contains("(declare-datatype Level ((zero) (succ (pred Level))))"),
        "{text}"
    );
    assert!(text.contains("(declare-const x Level)"), "{text}");
}

/// Two distinct datatypes under one name: neither's term is admitted as the
/// other's through any checked entry point.
#[test]
fn same_name_distinct_definitions_never_mix() {
    let v1 = level();
    let v2 = Sort::enum_type(
        "Level",
        vec![
            ("zero", vec![]),
            ("succ", vec![("pred", Sort::datatype_ref("Level"))]),
            ("extra", vec![("b", Sort::bool())]),
        ],
    );
    let v3 = Sort::enum_type(
        "Level",
        vec![("zero", vec![]), ("succ", vec![("pred", Sort::bool())])],
    );
    let x1 = Expr::var("x", v1.clone());
    let x2 = Expr::var("x", v2.clone());
    let x3 = Expr::var("x", v3.clone());
    assert!(Expr::try_datatype_constructor("Level", "succ", vec![x2.clone()], v1.clone()).is_err());
    assert!(Expr::try_datatype_constructor("Level", "succ", vec![x1.clone()], v2.clone()).is_err());
    assert!(x2
        .clone()
        .try_field_select("Level", "pred", v1.clone())
        .is_err());
    assert!(x1
        .clone()
        .try_field_select("Level", "pred", v2.clone())
        .is_err());
    assert!(x3
        .clone()
        .try_field_select("Level", "pred", v1.clone())
        .is_err());
    assert!(x1
        .clone()
        .try_field_select("Level", "pred", Sort::bool())
        .is_err());
    assert!(x3
        .clone()
        .try_field_select("Level", "pred", Sort::bool())
        .is_ok());
    assert!(x1.clone().try_eq(x2.clone()).is_err());
    assert!(x2.clone().try_eq(x1.clone()).is_err());
    assert!(Expr::try_ite(Expr::bool_const(true), x1.clone(), x2.clone()).is_err());
    assert!(Expr::try_distinct(vec![x1.clone(), x1.clone(), x2.clone()]).is_err());
    assert!(Expr::try_distinct(vec![x2.clone(), x1.clone()]).is_err());
    assert!(x1.clone().try_is_constructor("Level", "extra").is_err());
    // A raw ITE (bypassing try_ite) over mixed descriptors feeding a selector.
    let succ1 =
        Expr::try_datatype_constructor("Level", "succ", vec![x1.clone()], v1.clone()).unwrap();
    let succ2 =
        Expr::try_datatype_constructor("Level", "succ", vec![x2.clone()], v2.clone()).unwrap();
    let mixed = raw_ite(Expr::bool_const(true), succ1, succ2, v1.clone());
    assert!(mixed.try_field_select("Level", "pred", v1.clone()).is_err());
}

/// A struct fold through a raw ITE refuses an impostor branch whose fields
/// are swapped, and a raw constructor whose arguments disagree with its own
/// descriptor.
#[test]
fn struct_fold_refuses_swapped_impostor_branch() {
    let s1 = Sort::struct_type("S", [("a", Sort::bool()), ("b", Sort::bv8())]);
    let s2 = Sort::struct_type("S", [("a", Sort::bv8()), ("b", Sort::bool())]);
    let mk1 = Expr::try_datatype_constructor(
        "S",
        "S_mk",
        vec![Expr::bool_const(true), Expr::bitvec_const(5, 8)],
        s1.clone(),
    )
    .unwrap();
    let mk2 = raw_constructor(
        "S",
        "S_mk",
        vec![Expr::bitvec_const(7, 8), Expr::bool_const(false)],
        s2,
    );
    let ite = raw_ite(
        Expr::var("c", Sort::bool()),
        mk1.clone(),
        mk2.clone(),
        s1.clone(),
    );
    assert!(ite.try_field_select("S", "a", Sort::bool()).is_err());
    let bad = raw_constructor(
        "S",
        "S_mk",
        vec![Expr::bitvec_const(7, 8), Expr::bool_const(false)],
        s1.clone(),
    );
    assert!(bad.try_field_select("S", "a", Sort::bool()).is_err());
    let folded = mk1.try_field_select("S", "a", Sort::bool()).unwrap();
    assert!(matches!(folded.value(), ExprValue::BoolConst(true)));
}

/// A same-named definition nested inside a declaration must be that
/// declaration unfolded. The checked API resolves a reference to the nearest
/// enclosing name, so a shadowing inner `Level` with a constructor the outer
/// one lacks would authenticate terms the solver, answering under the outer
/// `Level`, never sees: the declaration is refused.
#[test]
fn a_same_name_definition_shadowing_its_enclosing_one_is_refused() {
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
    let mut program = AYProgram::new();
    let message = refusal(declare(&mut program, &outer));
    assert!(
        message.contains("conflicting datatype definitions under one name: `Level`"),
        "{message}"
    );
    assert!(!program.has_datatypes());

    // The singleton variant: `Level { succ (pred: Level { zero }) }`.
    let singleton = Sort::enum_type("Level", vec![("zero", Vec::<(&str, Sort)>::new())]);
    let outer = Sort::enum_type("Level", vec![("succ", vec![("pred", singleton)])]);
    assert!(declare(&mut program, &outer).is_err());
    assert!(!program.has_datatypes());

    // The same shape with the ref form used inside the shadowing definition,
    // nested one level deeper through an array, is refused too.
    let inner = Sort::enum_type(
        "Level",
        vec![("zero", vec![]), ("succ", vec![("pred", Sort::bool())])],
    );
    let outer = Sort::enum_type(
        "Level",
        vec![
            ("zero", vec![]),
            (
                "succ",
                vec![("pred", Sort::array(Sort::int(), inner.clone()))],
            ),
        ],
    );
    assert!(declare(&mut program, &outer).is_err());
    assert!(!program.has_datatypes());

    // An honest unfolding is the declaration itself.
    let unfolded = Sort::enum_type(
        "Level",
        vec![("zero", vec![]), ("succ", vec![("pred", level())])],
    );
    assert!(declare(&mut program, &unfolded).unwrap());
    assert!(!declare(&mut program, &level()).unwrap());
    assert!(program.try_declare_const("l", level()).is_ok());
}

/// A definition inlined in a field must equal the definition registered
/// under its name, whichever is declared first; a new name inlined in a field
/// is registered as a definition of its own, so a later different definition
/// of that name conflicts.
#[test]
fn a_nested_inline_definition_must_equal_the_registered_one() {
    for (registered, inlined) in [(block_big(), block_small()), (block_small(), block_big())] {
        // Registry first.
        let mut program = AYProgram::new();
        assert!(declare(&mut program, &registered).unwrap());
        let message = refusal(declare(&mut program, &tower_with_top(inlined.clone())));
        assert!(
            message.contains("conflicting datatype definitions under one name: `Block`"),
            "{message}"
        );
        assert!(!program.is_datatype_declared("Tower"));
        assert!(program
            .try_declare_const("t", tower_with_top(inlined.clone()))
            .is_err());
        assert!(declare(&mut program, &tower_with_top(registered.clone())).unwrap());

        // Inline first: `Tower` registers the `Block` it inlines.
        let mut program = AYProgram::new();
        assert!(declare(&mut program, &tower_with_top(inlined.clone())).unwrap());
        assert!(program.is_datatype_declared("Block"));
        let text = program.to_string();
        assert!(
            text.find("(declare-datatype Block").unwrap()
                < text.find("(declare-datatype Tower").unwrap(),
            "{text}"
        );
        let message = refusal(declare(&mut program, &registered));
        assert!(
            message.contains("conflicting datatype definitions under one name: `Block`"),
            "{message}"
        );
        assert!(!declare(&mut program, &inlined).unwrap());
        assert!(program.try_declare_const("b", registered.clone()).is_err());
        assert!(program.try_declare_const("b", inlined.clone()).is_ok());
    }
}

/// Two different definitions of one name inside one declaration conflict;
/// two equal ones are one definition, registered once.
#[test]
fn two_definitions_of_one_name_inside_one_declaration_must_agree() {
    let twice = |first: Sort, second: Sort| {
        Sort::enum_type("Pair", vec![("mk", vec![("a", first), ("b", second)])])
    };
    let mut program = AYProgram::new();
    let message = refusal(declare(&mut program, &twice(block_small(), block_big())));
    assert!(
        message.contains("conflicting datatype definitions under one name: `Block`"),
        "{message}"
    );
    assert!(!program.has_datatypes());
    assert!(declare(&mut program, &twice(block_small(), block_small())).unwrap());
    assert_eq!(
        program
            .to_string()
            .matches("(declare-datatype Block")
            .count(),
        1
    );
}

/// A constant's sort is authenticated against the registry like a
/// declaration: a datatype in it that differs from the registered definition
/// of its name is refused, a new one is registered and declared first, and a
/// dangling reference is refused.
#[test]
fn a_constant_sort_is_authenticated_against_the_registry() {
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
        let mut program = AYProgram::new();
        assert!(declare(&mut program, &registered).unwrap());
        let message = refusal(program.try_declare_const("x", other.clone()));
        assert!(
            message.contains("conflicting datatype definitions under one name: `Level`"),
            "{message}"
        );
        assert!(!program.is_declared("x"));
        assert!(program
            .try_declare_const("x", Sort::array(Sort::int(), other))
            .is_err());
        assert!(program.try_declare_const("x", registered).is_ok());
    }

    let mut program = AYProgram::new();
    assert!(!program.has_datatypes());
    let seq = program
        .try_declare_const("s", Sort::seq(tower_with_top(block_small())))
        .unwrap();
    assert!(program.is_datatype_declared("Block"));
    assert!(program.is_datatype_declared("Tower"));
    assert_eq!(seq.sort(), &Sort::seq(tower_with_top(block_small())));
    let text = program.to_string();
    let block = text.find("(declare-datatype Block").unwrap();
    let tower = text.find("(declare-datatype Tower").unwrap();
    let constant = text.find("(declare-const s").unwrap();
    assert!(block < tower && tower < constant, "{text}");
    assert!(declare(&mut program, &block_big()).is_err());

    assert!(program
        .try_declare_const("r", Sort::datatype_ref("Level"))
        .is_err());
    assert!(program
        .try_declare_const("r", tower_with_top(Sort::datatype_ref("Block")))
        .is_err());
    assert!(!program.is_declared("r"));
}

/// Mutual recursion in the inlined spelling: forged inner definitions are
/// refused by the checked API, unfoldings agree, a bare cross-reference is
/// dangling, and a nested definition referring back to the datatype enclosing
/// it cannot be registered as a definition of its own.
#[test]
fn mutual_recursion_forgeries() {
    let b_in_a = |ba: Sort| Sort::enum_type("B", vec![("b0", vec![]), ("mk_b", vec![("ba", ba)])]);
    let a_with = |ab: Sort| Sort::enum_type("A", vec![("mk_a", vec![("ab", ab)])]);
    let a_top = a_with(b_in_a(Sort::datatype_ref("A")));
    let b_top = b_in_a(a_with(Sort::datatype_ref("B")));
    let a = Expr::var("a", a_top.clone());
    let b = Expr::var("b", b_top.clone());
    assert!(Expr::try_datatype_constructor("A", "mk_a", vec![b.clone()], a_top.clone()).is_ok());
    assert!(Expr::try_datatype_constructor("B", "mk_b", vec![a.clone()], b_top.clone()).is_ok());
    assert!(a.clone().try_field_select("A", "ab", b_top.clone()).is_ok());
    assert!(b.clone().try_field_select("B", "ba", a_top.clone()).is_ok());
    // Forged B inside A: an extra constructor.
    let forged_b = Sort::enum_type(
        "B",
        vec![
            ("b0", vec![]),
            ("mk_b", vec![("ba", Sort::datatype_ref("A"))]),
            ("b2", vec![]),
        ],
    );
    let a_forged = a_with(forged_b);
    assert!(
        Expr::try_datatype_constructor("A", "mk_a", vec![b.clone()], a_forged.clone()).is_err()
    );
    assert!(Expr::var("a", a_forged.clone())
        .try_field_select("A", "ab", b_top.clone())
        .is_err());
    assert!(Expr::var("a", a_forged).try_eq(a.clone()).is_err());
    // Forged A inside B inside A: the deepest level differs (ab renamed).
    let deep_forged = a_with(b_in_a(Sort::enum_type(
        "A",
        vec![("mk_a", vec![("xx", Sort::datatype_ref("B"))])],
    )));
    assert!(
        Expr::try_datatype_constructor("A", "mk_a", vec![b.clone()], deep_forged.clone()).is_err()
    );
    assert!(Expr::var("a", deep_forged).try_eq(a.clone()).is_err());
    // Deep but honest: A{ab: B{ba: A{ab: B{ba: ref A}}}} equals a_top.
    let deep_honest = a_with(b_in_a(a_with(b_in_a(Sort::datatype_ref("A")))));
    assert!(Expr::var("a", deep_honest.clone())
        .try_eq(a.clone())
        .is_ok());
    assert!(Expr::try_datatype_constructor("A", "mk_a", vec![b.clone()], deep_honest).is_ok());
    // A bare cross-reference (the by-name sibling form) is dangling: unequal
    // to the inlined spelling, to a fresh copy of itself, and to its clone.
    let a_bare = a_with(Sort::datatype_ref("B"));
    assert!(Expr::try_datatype_constructor("A", "mk_a", vec![b.clone()], a_bare.clone()).is_err());
    let mut check = Check::new("mutual_recursion_forgeries");
    assert!(!check.same_sort(&a_bare, &a_top).unwrap());
    assert!(!check.same_sort(&a_bare, &a_bare.clone()).unwrap());
    assert!(!check
        .same_sort(&a_bare, &a_with(Sort::datatype_ref("B")))
        .unwrap());

    // The pair cannot be declared separately: each spelling nests the other
    // with a reference back out to the datatype enclosing it.
    let mut program = AYProgram::new();
    let message = refusal(declare(&mut program, &a_top));
    assert!(
        message.contains("mutual recursion between separately declared datatypes"),
        "{message}"
    );
    assert!(declare(&mut program, &b_top).is_err());
    assert!(program.try_declare_const("a", a_top).is_err());
    assert!(!program.has_datatypes());
}

/// Nesting through `Array` and `Seq`, with references in element, index and
/// requested-result positions.
#[test]
fn nesting_through_array_and_seq() {
    let forest = |kids: Sort| {
        Sort::enum_type(
            "Forest",
            vec![("leaf", vec![]), ("node", vec![("kids", Sort::seq(kids))])],
        )
    };
    let declared = forest(Sort::datatype_ref("Forest"));
    let kids = Expr::var("kids", Sort::seq(declared.clone()));
    assert!(
        Expr::try_datatype_constructor("Forest", "node", vec![kids.clone()], declared.clone())
            .is_ok()
    );
    let n = Expr::var("n", declared.clone());
    assert!(n
        .clone()
        .try_field_select("Forest", "kids", Sort::seq(declared.clone()))
        .is_ok());
    assert!(n
        .clone()
        .try_field_select("Forest", "kids", Sort::seq(Sort::datatype_ref("Forest")))
        .is_err());
    assert!(n
        .try_field_select("Forest", "kids", Sort::seq(Sort::uninterpreted("Forest")))
        .is_err());
    let weird = Sort::enum_type(
        "W",
        vec![
            ("leaf", vec![]),
            (
                "node",
                vec![("m", Sort::array(Sort::datatype_ref("W"), Sort::int()))],
            ),
        ],
    );
    let m = Expr::var("m", Sort::array(weird.clone(), Sort::int()));
    assert!(Expr::try_datatype_constructor("W", "node", vec![m], weird.clone()).is_ok());
    let m2 = Expr::var("m", Sort::array(Sort::uninterpreted("W"), Sort::int()));
    assert!(Expr::try_datatype_constructor("W", "node", vec![m2], weird.clone()).is_err());
    let level2 = Sort::enum_type(
        "Level",
        vec![("zero", vec![]), ("succ", vec![("pred", level())])],
    );
    let arr1 = Expr::var("a", Sort::array(Sort::int(), level()));
    let arr2 = Expr::var("a", Sort::array(Sort::int(), level2));
    assert!(arr1.try_eq(arr2).is_ok());
    let mut program = AYProgram::new();
    assert!(declare(&mut program, &declared).unwrap());
    assert!(declare(&mut program, &weird).unwrap());
    assert!(program
        .try_declare_const("m", Sort::array(weird, Sort::int()))
        .is_ok());
}

/// A sort containing a dangling reference is the same sort as nothing, not
/// even a derived-equal spelling or a clone of itself: the derived-equality
/// fast path and the shared-node shortcut do not bypass the rule.
#[test]
fn a_sort_with_a_dangling_reference_agrees_with_nothing_not_even_itself() {
    let r = Expr::var("r", Sort::datatype_ref("Level"));
    let s = Expr::var("s", Sort::datatype_ref("Level"));
    assert!(r.clone().try_eq(s.clone()).is_err());
    assert!(r.clone().try_eq(r.clone()).is_err());
    assert!(Expr::try_distinct(vec![r.clone(), s.clone()]).is_err());
    assert!(Expr::try_ite(Expr::bool_const(true), r.clone(), s).is_err());

    let closed_over_dangling =
        Sort::enum_type("T", vec![("mk", vec![("f", Sort::datatype_ref("U"))])]);
    let x = Expr::var("x", closed_over_dangling.clone());
    let y = Expr::var("y", closed_over_dangling.clone());
    assert!(x.clone().try_eq(y.clone()).is_err());
    assert!(x.clone().try_eq(x.clone()).is_err());
    assert!(Expr::try_distinct(vec![x.clone(), y.clone()]).is_err());
    assert!(Expr::try_ite(Expr::bool_const(true), x.clone(), y).is_err());
    let mut check = Check::new("dangling_nested");
    assert!(!check
        .same_sort(&closed_over_dangling, &closed_over_dangling)
        .unwrap());
    assert!(!check
        .same_sort(&closed_over_dangling, &closed_over_dangling.clone())
        .unwrap());
    assert!(Expr::try_datatype_constructor(
        "T",
        "mk",
        vec![Expr::var("u", Sort::uninterpreted("U"))],
        closed_over_dangling.clone(),
    )
    .is_err());
    assert!(Expr::try_datatype_constructor(
        "T",
        "mk",
        vec![Expr::var("u", Sort::datatype_ref("U"))],
        closed_over_dangling.clone(),
    )
    .is_err());
    assert!(x
        .try_field_select("T", "f", Sort::datatype_ref("U"))
        .is_err());

    // A closed sort still takes the fast paths: equal to itself and to its
    // clone, and a shared closed node inside two spellings compares equal.
    let l = Expr::var("l", level());
    assert!(l.clone().try_eq(l.clone()).is_ok());
    assert!(l.clone().try_eq(Expr::var("m", level())).is_ok());
    let shared = level();
    let left = tower_with_top(shared.clone());
    let right = tower_with_top(shared);
    assert!(Expr::var("a", left).try_eq(Expr::var("b", right)).is_ok());
}
