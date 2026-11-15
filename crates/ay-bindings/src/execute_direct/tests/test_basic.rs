// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Basic execution, sort translation, boolean operations, ITE, and datatype tests.

use super::*;

use crate::constraint::{logic, Constraint};
use ay_dpll::api::Logic;

#[test]
fn test_named_bv_lia_logics_parse_for_direct_execution() {
    for (name, expected) in [
        (logic::QF_UFBVLIA, Logic::QfUfbvlia),
        (logic::QF_AUFBVLIA, Logic::QfAufbvlia),
    ] {
        let mut program = AYProgram::new();
        program.set_logic(name);
        assert!(
            matches!(
                super::super::logic::parse_logic(&program).expect("public logic must parse"),
                super::super::logic::Declaration::Capability(logic) if logic == expected
            ),
            "{name} must parse to the {expected:?} capability"
        );
    }
}

#[test]
fn test_execute_bool_sat() {
    // Use QF_UF (simpler logic) to avoid ay-dpll LIA model validation bugs
    let mut program = AYProgram::new();
    program.set_logic("QF_UF");
    let x = program.declare_const("x", Sort::bool());
    // x is satisfiable (x = true)
    program.assert(x);
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Counterexample { .. }));
}

#[test]
fn test_execute_bool_unsat() {
    let mut program = AYProgram::new();
    program.set_logic("QF_UF");
    let x = program.declare_const("x", Sort::bool());
    // x AND NOT x is unsatisfiable
    program.assert(x.clone());
    program.assert(x.not());
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Verified));
}

#[test]
fn test_datatype_direct_execution() {
    // DT programs should execute directly, not fall back (#5404)
    use crate::sort::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut program = AYProgram::new();
    let dt = DatatypeSort {
        name: "Pair".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "mk-Pair".to_string(),
            fields: vec![
                DatatypeField {
                    name: "fst".to_string(),
                    sort: Sort::bitvec(32),
                },
                DatatypeField {
                    name: "snd".to_string(),
                    sort: Sort::bitvec(32),
                },
            ],
        }],
    };
    let pair_sort = Sort::struct_type("Pair", [("fst", Sort::bv32()), ("snd", Sort::bv32())]);
    // `struct_type` names its constructor `Pair_mk`: a `Pair` declared with
    // `mk-Pair` is a different definition under the name, and a constant of
    // the `Pair_mk` descriptor is refused against it.
    program.declare_datatype(dt);
    assert!(program.try_declare_const("q", pair_sort.clone()).is_err());
    let mut program = AYProgram::new();
    program.declare_datatype(pair_sort.datatype_sort().unwrap().clone());

    // Declare a variable of Pair sort
    let p = program.declare_const("p", pair_sort.clone());

    // Assert fst(p) = 42
    let fst_p = p.clone().field_select("Pair", "fst", Sort::bv32());
    let forty_two = Expr::bitvec_const(42i64, 32);
    program.assert(fst_p.eq(forty_two));

    // Assert snd(p) != 0
    let snd_p = p.field_select("Pair", "snd", Sort::bv32());
    let zero = Expr::bitvec_const(0i64, 32);
    program.assert(snd_p.eq(zero).not());

    program.check_sat();

    let result = execute(&program).unwrap();
    // Should get Counterexample (SAT) via direct path, not NeedsFallback
    assert!(
        matches!(result, ExecuteResult::Counterexample { .. }),
        "expected Counterexample, got {:?}",
        result
    );
}

#[test]
fn test_sort_translation() {
    assert!(matches!(lower_sort(&Sort::bool()), Ok(ApiSort::Bool)));
    assert!(matches!(lower_sort(&Sort::int()), Ok(ApiSort::Int)));
    assert!(matches!(lower_sort(&Sort::real()), Ok(ApiSort::Real)));

    // BitVec sort uses BitVecSort wrapper
    let bv_sort = lower_sort(&Sort::bv32()).unwrap();
    assert!(matches!(bv_sort, ApiSort::BitVec(bv) if bv.width == 32));

    // Array sort uses ArraySort wrapper in Box
    let arr = Sort::array(Sort::bv64(), Sort::bv8());
    let translated = lower_sort(&arr).unwrap();
    assert!(matches!(translated, ApiSort::Array(_)));
}

#[test]
fn test_bool_operations() {
    let mut program = AYProgram::new();
    program.set_logic("QF_UF");
    let a = program.declare_const("a", Sort::bool());
    let b = program.declare_const("b", Sort::bool());

    // (a AND b) AND NOT(a AND b) is UNSAT
    let ab = a.and(b);
    let not_ab = ab.clone().not();
    program.assert(ab.and(not_ab));
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Verified));
}

#[test]
fn test_ite_operations() {
    let mut program = AYProgram::new();
    program.set_logic("QF_UF");
    let c = program.declare_const("c", Sort::bool());
    let t = program.declare_const("t", Sort::bool());
    let e = program.declare_const("e", Sort::bool());

    // ite(c, t, e) AND NOT(ite(c, t, e)) is UNSAT
    let ite_expr = Expr::ite(c.clone(), t, e);
    program.assert(ite_expr.clone());
    program.assert(ite_expr.not());
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Verified));
}

#[test]
fn test_translate_bridge_array_uf_int_roundtrip() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFLIA");
    let arr = program.declare_const("arr", Sort::array(Sort::int(), Sort::int()));
    let x = program.declare_const("x", Sort::int());
    program.declare_fun("f", vec![Sort::int()], Sort::int());

    let x_plus_one = x.clone().int_add(Expr::int(1));
    let fx = Expr::func_app_with_sort("f", vec![x_plus_one], Sort::int());
    let read_back = arr.store(x.clone(), fx.clone()).select(x);

    program.assert(read_back.eq(fx).not());
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        matches!(result, ExecuteResult::Verified),
        "store/select over shared UF result should stay on the direct bridge path, got {:?}",
        result
    );
}

/// A recursive datatype declared with `Sort::datatype_ref` executes natively:
/// `pred (succ l) = l` is entailed, and a `succ` value is not `zero`.
#[test]
fn test_recursive_datatype_ref_direct_execution() {
    let level = Sort::enum_type(
        "Level",
        vec![
            ("zero", vec![]),
            ("succ", vec![("pred", Sort::datatype_ref("Level"))]),
        ],
    );
    let dt = level.datatype_sort().expect("Level is a datatype").clone();

    let mut unsat = AYProgram::new();
    unsat.set_logic("ALL");
    unsat.declare_datatype(dt.clone());
    let l = unsat.declare_const("l", level.clone());
    let succ_l = Expr::datatype_constructor("Level", "succ", vec![l.clone()], level.clone());
    let pred = succ_l.field_select("Level", "pred", level.clone());
    unsat.assert(pred.eq(l).not());
    unsat.check_sat();
    let result = execute(&unsat).unwrap();
    assert!(
        matches!(result, ExecuteResult::Verified),
        "pred (succ l) = l must be entailed, got {result:?}"
    );

    let mut sat = AYProgram::new();
    sat.set_logic("ALL");
    sat.declare_datatype(dt);
    let m = sat.declare_const("m", level.clone());
    sat.assert(m.clone().is_constructor("Level", "succ"));
    sat.assert(
        m.field_select("Level", "pred", level)
            .is_constructor("Level", "zero"),
    );
    sat.check_sat();
    let result = execute(&sat).unwrap();
    assert!(
        matches!(result, ExecuteResult::Counterexample { .. }),
        "m = succ zero is a model, got {result:?}"
    );
}

/// A datatype reference outside a declaration of its name is refused at
/// lowering: it must not become a bare sort name.
#[test]
fn test_dangling_datatype_ref_is_refused_at_lowering() {
    assert!(matches!(
        lower_sort(&Sort::datatype_ref("Level")),
        Err(ExecuteError::SortTranslation(_))
    ));
    assert!(matches!(
        lower_sort(&Sort::array(Sort::int(), Sort::datatype_ref("Level"))),
        Err(ExecuteError::SortTranslation(_))
    ));
    // Inside its own declaration (even nested in an array) it lowers.
    let tree = Sort::enum_type(
        "Tree",
        vec![
            ("leaf", vec![]),
            (
                "node",
                vec![("kids", Sort::array(Sort::int(), Sort::datatype_ref("Tree")))],
            ),
        ],
    );
    assert!(lower_sort(&tree).is_ok());
    let dt = tree.datatype_sort().unwrap();
    assert!(datatypes::bridge_datatype(dt).is_ok());

    // A declaration whose field names a different datatype is refused.
    let mislabelled = Sort::enum_type(
        "Level",
        vec![
            ("zero", vec![]),
            ("succ", vec![("pred", Sort::datatype_ref("Other"))]),
        ],
    );
    let dt = mislabelled.datatype_sort().unwrap();
    assert!(matches!(
        datatypes::bridge_datatype(dt),
        Err(ExecuteError::SortTranslation(_))
    ));
    // The program refuses a dangling reference as a constant's sort; a
    // declaration that reaches the lowering anyway is refused there.
    let mut program = AYProgram::new();
    program.set_logic("ALL");
    assert!(program
        .try_declare_const("r", Sort::datatype_ref("Level"))
        .is_err());
    // Such a sort is the same sort as nothing, not even itself, so no
    // checked equality over it can be built either.
    let r = Expr::var("r", Sort::datatype_ref("Level"));
    assert!(r.clone().try_eq(r).is_err());
    program
        .commands
        .push(Constraint::declare_const("r", Sort::datatype_ref("Level")));
    program.assert(Expr::bool_const(true));
    program.check_sat();
    let result = execute(&program);
    assert!(
        matches!(result, Err(ExecuteError::SortTranslation(_))),
        "a dangling datatype ref must not be declared, got {result:?}"
    );

    // A quantifier binder of a dangling reference sort is refused the same way.
    let mut program = AYProgram::new();
    program.set_logic("ALL");
    program.assert(Expr::forall(
        vec![("r".to_string(), Sort::datatype_ref("Level"))],
        Expr::bool_const(true),
    ));
    program.check_sat();
    let result = execute(&program);
    assert!(
        matches!(result, Err(ExecuteError::SortTranslation(_))),
        "a dangling datatype ref binder must not be lowered, got {result:?}"
    );
}

/// `(declare-datatype Block ((leaf)))`
fn block_sort() -> Sort {
    Sort::enum_type("Block", vec![("leaf", Vec::<(&str, Sort)>::new())])
}

/// `(declare-datatype Tower ((empty) (stack (top Block) (rest Tower))))`, the
/// sibling `Block` inlined in the field.
fn tower_sort() -> Sort {
    Sort::enum_type(
        "Tower",
        vec![
            ("empty", vec![]),
            (
                "stack",
                vec![("top", block_sort()), ("rest", Sort::datatype_ref("Tower"))],
            ),
        ],
    )
}

/// A sibling inlined in a field executes natively once the sibling itself is
/// declared first; declared in the other order it errors cleanly.
#[test]
fn test_sibling_inlined_declaration_executes_in_dependency_order() {
    let block = block_sort().datatype_sort().unwrap().clone();
    let tower = tower_sort().datatype_sort().unwrap().clone();

    let mut program = AYProgram::new();
    program.set_logic("ALL");
    program.declare_datatype(block.clone());
    program.declare_datatype(tower.clone());
    let b = program.declare_const("b", block_sort());
    let t = program.declare_const("t", tower_sort());
    let stack = Expr::datatype_constructor("Tower", "stack", vec![b.clone(), t], tower_sort());
    let top = stack.field_select("Tower", "top", block_sort());
    program.assert(top.eq(b).not());
    program.check_sat();
    let result = execute(&program).unwrap();
    assert!(
        matches!(result, ExecuteResult::Verified),
        "top (stack b t) = b must be entailed, got {result:?}"
    );

    // Declared in the other order, `Tower` registers the `Block` it inlines
    // as a definition of its own and declares it first, so the program text
    // and the native lane both see `Block` before `Tower`.
    let mut reversed = AYProgram::new();
    reversed.set_logic("ALL");
    assert!(reversed.try_declare_datatype(tower).unwrap());
    assert!(reversed.is_datatype_declared("Block"));
    assert!(!reversed.try_declare_datatype(block).unwrap());
    let text = reversed.to_string();
    assert!(
        text.find("(declare-datatype Block").unwrap()
            < text.find("(declare-datatype Tower").unwrap(),
        "{text}"
    );
    let b = reversed.declare_const("b", block_sort());
    let t = reversed.declare_const("t", tower_sort());
    let stack = Expr::datatype_constructor("Tower", "stack", vec![b.clone(), t], tower_sort());
    reversed.assert(stack.field_select("Tower", "top", block_sort()).eq(b).not());
    reversed.check_sat();
    let result = execute(&reversed).unwrap();
    assert!(
        matches!(result, ExecuteResult::Verified),
        "top (stack b t) = b must be entailed in either order, got {result:?}"
    );
}

/// A term authenticated against a descriptor that is not the registered
/// declaration of its name is refused: by `try_declare_const` at the program,
/// and by the lowering's registry check when the declaration bypasses the
/// program (the constraints pushed directly), before the solver sees it.
#[test]
fn test_impostor_descriptor_on_a_term_is_refused_by_the_solver_registry() {
    let level = Sort::enum_type(
        "Level",
        vec![
            ("zero", vec![]),
            ("succ", vec![("pred", Sort::datatype_ref("Level"))]),
        ],
    );
    let impostor = Sort::enum_type(
        "Level",
        vec![("zero", vec![]), ("succ", vec![("pred", Sort::int())])],
    );
    let mut program = AYProgram::new();
    program.set_logic("ALL");
    program.declare_datatype(level.datatype_sort().unwrap().clone());
    assert!(program
        .try_declare_datatype(impostor.datatype_sort().unwrap().clone())
        .is_err());
    // Self-consistent against its own descriptor, so the checked API admits it.
    let forged =
        Expr::try_datatype_constructor("Level", "succ", vec![Expr::int(1)], impostor.clone())
            .expect("the impostor descriptor is internally consistent");
    assert!(program.try_declare_const("m", impostor.clone()).is_err());
    let m = Expr::var("m", impostor.clone());
    program
        .commands
        .push(Constraint::declare_const("m", impostor));
    program.assert(m.eq(forged));
    program.check_sat();
    let result = execute(&program);
    assert!(
        matches!(result, Err(ExecuteError::SortTranslation(_))),
        "a constant of the impostor descriptor must be refused at lowering, got {result:?}"
    );
}
