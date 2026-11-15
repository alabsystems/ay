// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn wide_connective_refuses_before_copying_operand_strings() {
    let surface = format!(
        "(or {} false)",
        vec!["p"; MAX_EQUIVALENCE_NODES + 1].join(" ")
    );
    let mut calls = Vec::new();
    let mut nodes = 0;
    let result = fold_surface_with_progress(&surface, "t0", 0, &mut nodes, &mut |amount| {
        calls.push(amount);
        true
    });
    assert!(result.is_none());
    assert_eq!(nodes, 1);
    assert_eq!(calls, [surface.len() as u64 + 1]);
}

#[test]
fn a_refusal_cannot_be_recovered_by_an_unchanged_mirror_arm() {
    let mut calls = 0;
    let mut nodes = 0;
    let result = fold_surface_with_progress("(or p false)", "t0", 0, &mut nodes, &mut |_| {
        calls += 1;
        calls != 2
    });
    assert!(result.is_none());
    assert_eq!(calls, 2);
}

#[test]
fn opaque_application_arguments_stay_opaque_instead_of_using_fold_nodes() {
    let atom = format!("(P {})", vec!["x"; MAX_EQUIVALENCE_NODES + 1].join(" "));
    let surface = format!("(or {atom} false)");
    let (text, _, folded) = fold_surface(&surface, "t0", 0, &mut 0).expect("one opaque atom");
    assert_eq!(text, atom);
    assert!(folded);
}

#[test]
fn controlled_and_ordinary_nested_folds_have_identical_bytes() {
    let text = "(not (and (not p) (= x x)))";
    let ordinary = fold_surface(text, "t0", 0, &mut 0);
    assert!(ordinary.is_some());
    let controlled = fold_surface_with_progress(text, "t0", 0, &mut 0, &mut |_| true);
    assert_eq!(ordinary, controlled);
}

#[test]
fn bounded_fold_keeps_ascii_head_whitespace_and_delimiter_adjacency() {
    for surface in ["( or p false)", "(or(= x x)false)"] {
        let (text, _, folded) = fold_surface(surface, "t0", 0, &mut 0)
            .expect("the same native connective grammar as the borrowed scanner");
        assert_eq!(text, if surface.contains('=') { "true" } else { "p" });
        assert!(folded);
    }
}

#[test]
fn cumulative_comparison_work_is_bounded_for_a_wide_unique_conjunction() {
    let surface = format!(
        "(and {} true)",
        (0..200)
            .map(|i| format!("p{i:04}"))
            .collect::<Vec<_>>()
            .join(" ")
    );
    let mut total = 0u64;
    let result = fold_surface_with_progress(&surface, "t0", 0, &mut 0, &mut |amount| {
        total += amount;
        true
    });
    assert!(result.is_none());
    assert!(total <= MAX_FOLD_WORK);
}
