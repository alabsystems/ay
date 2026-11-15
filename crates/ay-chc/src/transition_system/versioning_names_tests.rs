// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Time shifts over state variables whose own names end in `_<digits>`.
//!
//! SingleLoop names its state `.loc_<pred>` and `.arg_<pred>_<arg>`. Reading
//! `.loc_1` as `.loc` at time 1 left it (and every `.arg_p_a` with `a > 0`)
//! unshifted, so TPA's two-step composition linked only `.loc_0` between its
//! copies and checked its target at time 0 (model-checker-consumer
//! `safe_symbolic_from_elem`, multi-predicate TPA).

use super::*;
use crate::{ChcSort, PredicateId};

fn system(names: &[(&str, ChcSort)]) -> TransitionSystem {
    let vars = names
        .iter()
        .map(|(name, sort)| ChcVar::new(*name, sort.clone()))
        .collect();
    TransitionSystem::new(
        PredicateId::new(0),
        vars,
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
    )
}

fn names(expr: &ChcExpr) -> Vec<String> {
    let mut names: Vec<String> = expr.vars().into_iter().map(|v| v.name).collect();
    names.sort();
    names
}

fn var(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, sort))
}

#[test]
fn single_loop_names_shift_as_whole_names() {
    let ts = system(&[
        (".loc_0", ChcSort::Int),
        (".loc_1", ChcSort::Int),
        (".arg_0_0", ChcSort::BitVec(64)),
        (".arg_0_6", ChcSort::BitVec(64)),
    ]);
    let expr = ChcExpr::and_all([
        ChcExpr::eq(var(".loc_0", ChcSort::Int), var(".loc_1", ChcSort::Int)),
        ChcExpr::eq(var(".loc_1_1", ChcSort::Int), ChcExpr::int(1)),
        ChcExpr::eq(
            var(".arg_0_0", ChcSort::BitVec(64)),
            var(".arg_0_6", ChcSort::BitVec(64)),
        ),
        ChcExpr::eq(var("J", ChcSort::Int), ChcExpr::int(0)),
    ]);
    assert_eq!(
        names(&ts.shift_versioned_state_vars(&expr, 1)),
        [
            ".arg_0_0_1",
            ".arg_0_6_1",
            ".loc_0_1",
            ".loc_1_1",
            ".loc_1_2",
            "J"
        ],
    );
    assert_eq!(
        names(&ts.shift_versioned_state_vars(&expr, 2)),
        [
            ".arg_0_0_2",
            ".arg_0_6_2",
            ".loc_0_2",
            ".loc_1_2",
            ".loc_1_3",
            "J"
        ],
    );
    let back = ts.shift_versioned_state_vars(&ts.shift_versioned_state_vars(&expr, 2), -2);
    assert_eq!(names(&back), names(&expr));
}

#[test]
fn only_canonical_positive_suffixes_are_times() {
    let bases: FxHashSet<&str> = ["x", ".loc_1"].into_iter().collect();
    assert_eq!(state_var_time("x", &bases), Some(("x", 0)));
    assert_eq!(state_var_time("x_3", &bases), Some(("x", 3)));
    assert_eq!(state_var_time(".loc_1", &bases), Some((".loc_1", 0)));
    assert_eq!(state_var_time(".loc_1_12", &bases), Some((".loc_1", 12)));
    for not_a_time in ["x_0", "x_01", "x_+1", "x_-1", "x_", ".loc", ".loc_2", "y_1"] {
        assert_eq!(state_var_time(not_a_time, &bases), None, "{not_a_time}");
    }
}
