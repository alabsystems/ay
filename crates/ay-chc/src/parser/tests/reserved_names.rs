// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Input variables whose names lie in an engine-reserved family
//! (`is_engine_reserved_var_name`) are renamed apart by the parser, as a
//! quantifier binder, a `declare-var` and an undeclared symbol.
//!
//! Example the first script is taken from: z3 answers `unsat` on it, and AY
//! answered `sat` while the clause variable `_mod_r_1` was the variable the
//! mod elimination mints for `(mod x 3)`.

use super::*;
use crate::expr::is_engine_reserved_var_name;

const MOD_AUX_BINDER: &str = "(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 2)) (inv (+ x 1)))))
(assert (forall ((x Int) (_mod_r_1 Int)) (=> (and (inv x) (>= x 2) (not (= (mod x 3) _mod_r_1)) (= _mod_r_1 1000)) (inv _mod_r_1))))
(assert (forall ((x Int)) (=> (and (inv x) (>= x 1000)) false)))
(check-sat)
";

fn variable_names(input: &str) -> Vec<String> {
    let problem = ChcParser::parse(input).expect("parses");
    let mut names = Vec::new();
    for clause in problem.clauses() {
        for var in clause.vars() {
            if !names.contains(&var.name) {
                names.push(var.name);
            }
        }
    }
    names
}

#[test]
fn the_reserved_families_are_the_elimination_prefixes_and_the_catamorphism_prefix() {
    for name in [
        "_ite_0",
        "_mod_q_0",
        "_mod_r_1",
        "_div_q_0",
        "_div_r_1",
        "__cata0_size",
        "__cata_opq3",
    ] {
        assert!(is_engine_reserved_var_name(name), "{name}");
    }
    for name in [
        "x",
        "_x",
        "_mod_q",
        "mod_q_0",
        "a__b",
        "v0",
        "x_next",
        "_ite",
        "__",
        "__p0_a0",
        "__fact_0_x",
        "_cata0_size",
    ] {
        assert!(!is_engine_reserved_var_name(name), "{name}");
    }
}

#[test]
fn a_binder_named_like_a_mod_auxiliary_is_renamed_apart() {
    let names = variable_names(MOD_AUX_BINDER);
    assert!(
        names.iter().all(|name| !is_engine_reserved_var_name(name)),
        "{names:?}"
    );
    assert_eq!(
        names
            .iter()
            .filter(|name| name.ends_with("!_mod_r_1"))
            .count(),
        1,
        "{names:?}"
    );
    assert!(names.contains(&"x".to_string()), "{names:?}");
}

#[test]
fn a_binder_named_like_a_catamorphism_variable_is_renamed_apart() {
    let names = variable_names(
        "(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((n Int) (__cata0_size Int)) (=> (and (= n 0) (< __cata0_size 1)) (P n))))
(assert (forall ((n Int)) (=> (and (P n) (>= n 10)) false)))
(check-sat)
",
    );
    assert!(
        names.iter().all(|name| !is_engine_reserved_var_name(name)),
        "{names:?}"
    );
    assert!(
        names.iter().any(|name| name.ends_with("!__cata0_size")),
        "{names:?}"
    );
}

#[test]
fn a_declared_variable_in_a_reserved_family_is_one_renamed_variable_per_file() {
    let names = variable_names(
        "(declare-rel P (Int))
(declare-var _mod_q_0 Int)
(declare-var x Int)
(rule (=> (= _mod_q_0 0) (P _mod_q_0)))
(rule (=> (and (P x) (= _mod_q_0 (+ x 1)) (< x 3)) (P _mod_q_0)))
(query P)
",
    );
    let renamed: Vec<&String> = names
        .iter()
        .filter(|name| name.ends_with("!_mod_q_0"))
        .collect();
    assert_eq!(renamed.len(), 1, "{names:?}");
    assert!(
        names.iter().all(|name| !is_engine_reserved_var_name(name)),
        "{names:?}"
    );
}

#[test]
fn a_let_bound_name_in_a_reserved_family_still_denotes_its_value() {
    let problem = ChcParser::parse(
        "(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (let ((_ite_0 5)) (= x _ite_0)) (P x))))
(assert (forall ((x Int)) (=> (and (P x) (> x 7)) false)))
(check-sat)
",
    )
    .expect("parses");
    let fact = &problem.clauses()[0];
    let names: Vec<String> = fact.vars().into_iter().map(|var| var.name).collect();
    assert_eq!(names, ["x"], "{fact}");
}
