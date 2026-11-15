// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Nested datatype terms (constructor, selector, tester applications over
//! one another) must round-trip through the retained assertion source: the
//! SMT-LIB spelling the program prints re-elaborates to the very term the
//! native lane asserted, so a proof-producing program over a recursive
//! datatype executes natively with the right verdict.

use super::*;
use ay_dpll::api::ProofAcceptanceMode;

fn level() -> Sort {
    Sort::enum_type(
        "Level",
        vec![
            ("zero", vec![]),
            ("succ", vec![("pred", Sort::datatype_ref("Level"))]),
        ],
    )
}

fn succ(inner: Expr) -> Expr {
    Expr::datatype_constructor("Level", "succ", vec![inner], level())
}

fn zero() -> Expr {
    Expr::datatype_constructor("Level", "zero", vec![], level())
}

fn pred(inner: Expr) -> Expr {
    inner.field_select("Level", "pred", level())
}

fn is_succ(inner: Expr) -> Expr {
    inner.is_constructor("Level", "succ")
}

/// A proof-producing program over `Level` with one constant `l` and the
/// assertion `build(l)`.
fn level_program(build: impl FnOnce(Expr) -> Expr) -> AYProgram {
    let mut program = AYProgram::new();
    program.set_option(":produce-proofs", "true");
    program.set_logic("ALL");
    program.declare_datatype(level().datatype_sort().unwrap().clone());
    let l = program.declare_const("l", level());
    program.assert(build(l));
    program.check_sat();
    program
}

fn verified(program: &AYProgram) {
    let outcomes = execute_incremental(program).unwrap_or_else(|error| {
        panic!("native execution failed for {program}: {error}");
    });
    assert_eq!(outcomes.len(), 1);
    assert!(
        matches!(outcomes[0].result, ExecuteTypedResult::Verified),
        "{program} should be Verified, got {:?}",
        outcomes[0].result
    );
    outcomes[0]
        .unsat_proof
        .as_ref()
        .expect("strict artifact")
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .unwrap();
}

fn counterexample(program: &AYProgram) {
    let outcomes = execute_incremental(program).unwrap_or_else(|error| {
        panic!("native execution failed for {program}: {error}");
    });
    assert_eq!(outcomes.len(), 1);
    assert!(
        matches!(outcomes[0].result, ExecuteTypedResult::Counterexample(_)),
        "{program} should be a Counterexample, got {:?}",
        outcomes[0].result
    );
}

#[test]
fn flat_constructor_equation_is_verified() {
    verified(&level_program(|l| succ(l.clone()).eq(l)));
}

#[test]
fn nested_tester_over_constructor_is_verified() {
    verified(&level_program(|l| is_succ(succ(l)).not()));
}

#[test]
fn nested_selector_over_constructor_is_verified() {
    verified(&level_program(|l| pred(succ(l.clone())).eq(l).not()));
}

#[test]
fn nested_constructor_over_constructor_is_verified() {
    verified(&level_program(|l| succ(succ(l.clone())).eq(succ(l))));
}

#[test]
fn three_level_shapes_execute_natively() {
    verified(&level_program(|l| succ(succ(succ(l.clone()))).eq(l)));
    verified(&level_program(|l| is_succ(succ(succ(l))).not()));
    verified(&level_program(|l| succ(succ(l)).eq(succ(zero()))));
    counterexample(&level_program(|l| pred(pred(succ(succ(l.clone())))).eq(l)));
    counterexample(&level_program(|l| is_succ(pred(succ(succ(l))))));
}

/// Three-level shapes whose whole assertion folds to `false` through two
/// nested datatype folds reconstruct from their source and are decided
/// natively. The proof exporter cannot yet certify that double fold, so with
/// proofs requested the self-check WITHDRAWS the verdict to Unknown — the
/// fail-closed direction. What must never happen is an inversion, so this
/// pins both halves: the proving lane is never a counterexample, and the
/// non-proving lane decides the same programs Verified.
#[test]
fn three_level_folds_to_false_are_never_inverted() {
    let shapes: Vec<fn(Expr) -> Expr> = vec![
        |l| pred(pred(succ(succ(l.clone())))).eq(l).not(),
        |l| is_succ(pred(succ(succ(l)))).not(),
        |l| succ(pred(succ(l.clone()))).eq(succ(l)).not(),
    ];
    for build in shapes {
        let proving = level_program(build);
        let outcomes = execute_incremental(&proving).unwrap_or_else(|error| {
            panic!("native execution failed for {proving}: {error}");
        });
        assert!(
            matches!(
                outcomes[0].result,
                ExecuteTypedResult::Verified | ExecuteTypedResult::Unknown(_)
            ),
            "{proving} must not be a counterexample, got {:?}",
            outcomes[0].result
        );

        let mut plain = AYProgram::new();
        plain.set_logic("ALL");
        plain.declare_datatype(level().datatype_sort().unwrap().clone());
        let l = plain.declare_const("l", level());
        plain.assert(build(l));
        plain.check_sat();
        assert!(
            matches!(execute_typed(&plain).unwrap(), ExecuteTypedResult::Verified),
            "{plain} should be Verified natively"
        );
    }
}

#[test]
fn nullary_constructor_equation_is_a_counterexample() {
    counterexample(&level_program(|m| m.eq(succ(zero()))));
    counterexample(&level_program(|m| {
        is_succ(m.clone()).and(pred(m).eq(zero()))
    }));
    verified(&level_program(|m| {
        is_succ(m.clone())
            .and(pred(m).eq(zero()))
            .and(Expr::false_())
    }));
}

#[test]
fn struct_selector_over_constructor_executes_natively() {
    let pair = Sort::enum_type(
        "Pair",
        vec![("mk", vec![("fst", Sort::int()), ("snd", Sort::int())])],
    );
    let build = |expected: i64| {
        let mut program = AYProgram::new();
        program.set_option(":produce-proofs", "true");
        program.set_logic("ALL");
        program.declare_datatype(pair.datatype_sort().unwrap().clone());
        let mk = Expr::datatype_constructor(
            "Pair",
            "mk",
            vec![Expr::int(1), Expr::int(2)],
            pair.clone(),
        );
        program.assert(
            mk.field_select("Pair", "fst", Sort::int())
                .eq(Expr::int(expected))
                .not(),
        );
        program.check_sat();
        program
    };
    verified(&build(1));
    counterexample(&build(2));
}

/// A datatype constructor reached THROUGH an array — stored, read back, then
/// destructured by constructor injectivity — round-trips through its source
/// too: the array rewrite happens on both sides of the reconstruction check.
#[test]
fn datatype_through_array_executes_natively() {
    let build = |rhs: fn(Expr, Expr) -> Expr| {
        let mut program = AYProgram::new();
        program.set_option(":produce-proofs", "true");
        program.set_logic("ALL");
        program.declare_datatype(level().datatype_sort().unwrap().clone());
        let cells = program.declare_const("cells", Sort::array(Sort::int(), level()));
        let l = program.declare_const("l", level());
        let m = program.declare_const("m", level());
        let read = cells
            .store(Expr::int(0), succ(l.clone()))
            .select(Expr::int(0));
        program.assert(read.eq(rhs(l, m)));
        program.check_sat();
        program
    };
    // `(select (store cells 0 (succ l)) 0)` is `(succ l)`, so injectivity
    // leaves `(= l (succ l))` — refuted by acyclicity — and `(= l m)` — not.
    verified(&build(|l, _| succ(succ(l))));
    counterexample(&build(|_, m| succ(m)));
}

/// The retained source of a nested datatype assertion is the program's own
/// SMT-LIB spelling and the proof carries it.
#[test]
fn nested_datatype_proof_carries_the_authored_spelling() {
    let program = level_program(|l| pred(succ(l.clone())).eq(l).not());
    let outcomes = execute_incremental(&program).unwrap();
    let proof = outcomes[0].unsat_proof.as_ref().unwrap();
    assert!(proof.alethe.contains("(pred (succ l))"), "{}", proof.alethe);
}
