// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::finite_enum::{MAX_PROOF_CELLS, MAX_RENDER_WORK};
use super::finite_enum_surface::{
    add_repeated_render_work, canonical_surface_work_is_bounded, surface_text_bounds,
};
use crate::executor::Executor;
use ay_core::{Sort, TermId};
use ay_frontend::command::Term as FrontendTerm;

#[test]
fn bounded_pair_and_cell_caps_cover_exact_boundary() {
    assert_eq!(Executor::bounded_pair_count(255, 256), Some(32_640));
    assert_eq!(Executor::bounded_pair_count(256, 257), None);
    assert_eq!(32_640usize * 4 + 3, 130_563);
    assert!(130_563 <= MAX_PROOF_CELLS);
}

#[test]
fn finite_surface_repeated_render_budget_is_checked() {
    let (source, equality) = surface_text_bounds("left", "right").unwrap();
    let mut used = usize::try_from(MAX_RENDER_WORK).unwrap() - 1;
    assert!(!add_repeated_render_work(&mut used, source, equality));
}

fn binary_surface_fixture(parsed: FrontendTerm) -> (Executor, TermId, TermId, [TermId; 2]) {
    let mut exec = Executor::new();
    let sort = Sort::Uninterpreted("FiniteSurfaceUnit".to_string());
    let left = exec.ctx.terms.mk_var("surface_left", sort.clone());
    let right = exec.ctx.terms.mk_var("surface_right", sort);
    let equality = exec.ctx.terms.mk_eq(left, right);
    let source = exec.ctx.terms.mk_not_raw(equality);
    exec.ctx.add_assertion_with_parsed(source, parsed);
    (exec, source, equality, [left, right])
}

fn exact_binary_surface() -> FrontendTerm {
    FrontendTerm::App(
        "not".to_string(),
        vec![FrontendTerm::App(
            "=".to_string(),
            vec![
                FrontendTerm::Symbol("surface_right".to_string()),
                FrontendTerm::Symbol("surface_left".to_string()),
            ],
        )],
    )
}

#[test]
fn finite_surface_preserves_authored_equality_orientation() {
    let (exec, source, equality, members) = binary_surface_fixture(exact_binary_surface());
    let surface = exec
        .build_finite_enum_proof_surface(&[source], &[(0, source)], &[equality], &members)
        .expect("exact direct binary source is externally printable");
    assert_eq!(
        surface.overrides.get(&source).map(String::as_str),
        Some("(not (= surface_right surface_left))")
    );
    assert_eq!(
        surface.overrides.get(&equality).map(String::as_str),
        Some("(= surface_right surface_left)")
    );
}

#[test]
fn binary_distinct_and_nested_sources_have_no_external_surface() {
    let distinct = FrontendTerm::App(
        "distinct".to_string(),
        vec![
            FrontendTerm::Symbol("surface_left".to_string()),
            FrontendTerm::Symbol("surface_right".to_string()),
        ],
    );
    let (exec, source, equality, members) = binary_surface_fixture(distinct);
    assert!(exec
        .build_finite_enum_proof_surface(&[source], &[(0, source)], &[equality], &members)
        .is_none());

    let nested = FrontendTerm::App("and".to_string(), vec![exact_binary_surface()]);
    let (exec, source, equality, members) = binary_surface_fixture(nested);
    assert!(exec
        .build_finite_enum_proof_surface(&[source], &[(0, source)], &[equality], &members)
        .is_none());
}

#[test]
fn finite_surface_rejects_misaligned_root_and_excess_canonical_depth() {
    let (mut exec, source, equality, members) = binary_surface_fixture(exact_binary_surface());
    let foreign = exec.ctx.terms.mk_var("foreign_root", Sort::Bool);
    assert!(exec
        .build_finite_enum_proof_surface(&[foreign], &[(0, source)], &[equality], &members)
        .is_none());

    let mut deep = foreign;
    for _ in 0..300 {
        deep = exec.ctx.terms.mk_not_raw(deep);
    }
    assert!(!canonical_surface_work_is_bounded(
        &exec.ctx.terms,
        &[(0, deep)],
        &[],
        &[]
    ));
}
