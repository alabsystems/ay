// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

const FOLDS: [(&str, &str); 3] = [
    ("(or p false)", "p"),
    ("(not (and (not p) (= x x)))", "p"),
    ("(or (= (* 3 m) x) false)", "(= x (* 3 m))"),
];

#[test]
fn accepting_document_fold_preserves_exact_and_alpha_bridge_bytes() {
    for (surface, rendering) in FOLDS {
        let ordinary = render_folded_document_equivalence("t0", surface, rendering);
        let controlled =
            render_folded_document_equivalence_with_progress("t0", surface, rendering, &mut |_| {
                true
            });
        assert!(ordinary.0.is_some(), "{surface}");
        assert_eq!(ordinary, controlled);
    }
    let actual =
        render_folded_document_equivalence_with_progress("t0", "(or p false)", "p", &mut |_| true)
            .0
            .expect("exact fold");
    assert_eq!(
        actual,
        "(assume t0.a (or p false))\n\
         (step t0.n (cl (= (or p false) p)) :rule or_simplify)\n\
         (step t0.e (cl (not (= (or p false) p)) (not (or p false)) p) :rule equiv_pos2)\n\
         (step t0 (cl p) :rule resolution :premises (t0.e t0.n t0.a))"
    );
}

#[test]
fn every_fold_parse_comparison_and_terminal_poll_can_refuse() {
    for (surface, rendering) in FOLDS {
        let mut charges = Vec::new();
        let (accepted, _) = render_folded_document_equivalence_with_progress(
            "t0",
            surface,
            rendering,
            &mut |amount| {
                charges.push(amount);
                true
            },
        );
        let accepted = accepted.expect("baseline bridge");
        assert!(charges.len() > 3);
        assert_eq!(charges.last(), Some(&0), "terminal observation");
        assert!(
            charges[charges.len() - 2] >= accepted.len() as u64,
            "assembly is admitted before its allocation"
        );
        for stop_at in 1..=charges.len() {
            let mut calls = 0;
            let (refused, _) = render_folded_document_equivalence_with_progress(
                "t0",
                surface,
                rendering,
                &mut |_| {
                    calls += 1;
                    calls != stop_at
                },
            );
            assert!(
                refused.is_none(),
                "poll {stop_at} of {}: {surface}",
                charges.len()
            );
            assert_eq!(calls, stop_at, "no retry after refusal");
        }
    }
}

#[test]
fn stopped_document_fold_does_not_visit_any_nodes() {
    let (result, nodes) =
        render_folded_document_equivalence_with_progress("t0", "(or p false)", "p", &mut |_| false);
    assert!(result.is_none());
    assert_eq!(nodes, 0);
}

#[test]
fn controlled_document_fold_keeps_opaque_and_malformed_refusals() {
    for surface in [
        "(or (let ((x p)) x) false)",
        "(or (! p :named x) false)",
        "(or (forall ((x Bool)) x) false)",
        "(or p false",
        "(distinct p q)",
    ] {
        assert_eq!(
            render_folded_document_equivalence_with_progress("t0", surface, "p", &mut |_| true),
            render_folded_document_equivalence("t0", surface, "p"),
        );
        assert!(render_folded_document_equivalence("t0", surface, "p")
            .0
            .is_none());
    }
}

#[test]
fn assembly_bound_includes_long_identifiers_and_every_fold_step() {
    let id = "identifier".repeat(128);
    let surface = "(or (= x y) false)";
    let rendering = "(= y x)";
    let mut charges = Vec::new();
    let document =
        render_folded_document_equivalence_with_progress(&id, surface, rendering, &mut |amount| {
            charges.push(amount);
            true
        })
        .0
        .expect("bounded long-id alpha bridge");
    assert!(charges[charges.len() - 2] >= document.len() as u64);
    assert!(bridge_output_bound(&id, surface, "(= x y)", rendering, &[]).is_some());
}
