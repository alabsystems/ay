// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `mk_fresh_var_avoiding` skips refused spellings, and
//! `find_fresh_var_spelled` finds a `mk_fresh_var` variable by its spelling.

use super::*;

#[test]
fn a_fresh_variable_is_found_by_its_spelling_and_not_by_the_name_table() {
    let mut store = TermStore::new();
    let declared = store.mk_var("c", Sort::Int);
    let fresh = store.mk_fresh_var("x", Sort::Int);
    assert_eq!(store.find_fresh_var_spelled("x_1"), Some(fresh));
    assert_eq!(store.find_var("x_1"), None);
    assert!(!store.has_var_name("x_1"));
    assert_ne!(declared, fresh);
}

#[test]
fn spellings_no_fresh_variable_has_are_not_found() {
    let mut store = TermStore::new();
    let _ = store.mk_fresh_var("x", Sort::Int);
    for spelling in [
        "x_1",
        "x_01",
        "x_+0",
        "y_0",
        "x",
        "x_",
        "_",
        "x_00",
        "x_4294967296",
    ] {
        assert_eq!(store.find_fresh_var_spelled(spelling), None, "{spelling}");
    }
    assert!(store.find_fresh_var_spelled("x_0").is_some());
}

#[test]
fn a_fresh_variable_is_found_whatever_its_sort() {
    let mut store = TermStore::new();
    let fresh = store.mk_fresh_var("b", Sort::Bool);
    assert_eq!(store.find_fresh_var_spelled("b_0"), Some(fresh));
}

#[test]
fn a_refused_spelling_is_skipped_and_interns_no_term() {
    let mut store = TermStore::new();
    let fresh = store.mk_fresh_var_avoiding("y", Sort::Int, |name| name == "y_0" || name == "y_1");
    match store.get(fresh) {
        TermData::Var(name, id) => {
            assert_eq!(name, "y_2");
            assert_eq!(*id, 2);
        }
        other => panic!("expected a variable, got {other:?}"),
    }
    assert_eq!(store.find_fresh_var_spelled("y_0"), None);
    assert_eq!(store.find_fresh_var_spelled("y_1"), None);
    assert_eq!(store.find_fresh_var_spelled("y_2"), Some(fresh));
}

#[test]
fn a_fresh_variable_skips_a_spelling_in_the_name_table() {
    let mut store = TermStore::new();
    let _ = store.mk_var("x_1", Sort::Int);
    let fresh = store.mk_fresh_var("x", Sort::Int);
    match store.get(fresh) {
        TermData::Var(name, _) => assert_eq!(name, "x_2"),
        other => panic!("expected a variable, got {other:?}"),
    }
}
