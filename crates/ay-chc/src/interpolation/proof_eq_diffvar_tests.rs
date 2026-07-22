// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the script-level EqDiffVar reduction (rank-4 inc-17).

use super::*;

fn bvar(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Bool))
}

fn ivar(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

fn guarded(guard: ChcExpr, eq: ChcExpr) -> ChcExpr {
    ChcExpr::or(ChcExpr::not(guard), eq)
}

fn sorts(pairs: &[(&str, ChcSort)]) -> FxHashMap<String, ChcSort> {
    pairs
        .iter()
        .map(|(n, s)| ((*n).to_string(), s.clone()))
        .collect()
}

fn int_sorts(names: &[&str]) -> FxHashMap<String, ChcSort> {
    names
        .iter()
        .map(|n| ((*n).to_string(), ChcSort::Int))
        .collect()
}

/// Render for containment assertions in tests.
fn render(e: &ChcExpr) -> String {
    format!("{e:?}")
}

#[test]
fn test_guarded_var_var_equality_rewrites_with_a_side_def() {
    let a = vec![
        guarded(bvar("g"), ChcExpr::eq(ivar("x"), ivar("y"))),
        bvar("g"),
    ];
    let b = vec![ChcExpr::or(
        bvar("h"),
        ChcExpr::le(ChcExpr::add(ivar("p"), ivar("q")), ChcExpr::Int(0)),
    )];
    let var_sorts = sorts(&[
        ("g", ChcSort::Bool),
        ("h", ChcSort::Bool),
        ("x", ChcSort::Int),
        ("y", ChcSort::Int),
        ("p", ChcSort::Int),
        ("q", ChcSort::Int),
    ]);
    let rw = apply_for_proof_script(&a, &b, &var_sorts).expect("nested var-var eq must rewrite");
    assert_eq!(rw.diff_vars, 1);
    assert_eq!(rw.rewritten_constraints, 1);
    // A partition: rewritten guard clause + unchanged g + the def PAIR.
    assert_eq!(rw.a_constraints.len(), 4);
    // B partition unchanged (no eq atoms).
    assert_eq!(rw.b_constraints.len(), 1);
    assert_eq!(rw.b_constraints[0], b[0]);
    // The rewritten clause mentions the difference variable; the original
    // atom is gone.
    let folded = render(&rw.a_constraints[0]);
    assert!(folded.contains("ay_eqdv_p"), "rewritten clause: {folded}");
    // The substitution maps the dvar to x - y (sign-normalized on the
    // lexicographically smallest name).
    assert_eq!(rw.subst.len(), 1);
    let (name, lin) = rw.subst.iter().next().expect("one substitution");
    assert!(name.starts_with("ay_eqdv_p"));
    assert_eq!(*lin, ChcExpr::add(ivar("x"), ChcExpr::neg(ivar("y"))));
}

#[test]
fn test_atoms_sharing_canonical_row_share_one_diff_var() {
    // (= x y) and (= x (+ y 5)) share `lin = x - y`; rhs 0 vs 5.
    let a = vec![
        guarded(bvar("g"), ChcExpr::eq(ivar("x"), ivar("y"))),
        guarded(
            bvar("h"),
            ChcExpr::eq(ivar("x"), ChcExpr::add(ivar("y"), ChcExpr::Int(5))),
        ),
    ];
    let b = vec![ChcExpr::lt(ivar("x"), ivar("y"))];
    let var_sorts = sorts(&[
        ("g", ChcSort::Bool),
        ("h", ChcSort::Bool),
        ("x", ChcSort::Int),
        ("y", ChcSort::Int),
    ]);
    let rw = apply_for_proof_script(&a, &b, &var_sorts).expect("must rewrite");
    assert_eq!(rw.diff_vars, 1, "one shared difference variable");
    assert_eq!(rw.rewritten_constraints, 2);
    let c0 = render(&rw.a_constraints[0]);
    let c1 = render(&rw.a_constraints[1]);
    assert!(c0.contains("ay_eqdv_p0") && c0.contains("Int(0)"), "{c0}");
    assert!(c1.contains("ay_eqdv_p0") && c1.contains("Int(5)"), "{c1}");
}

#[test]
fn test_b_side_occurrence_places_def_in_b() {
    let a = vec![ChcExpr::le(ivar("x"), ivar("y"))];
    let b = vec![
        guarded(bvar("g"), ChcExpr::eq(ivar("x"), ivar("y"))),
        bvar("g"),
    ];
    let var_sorts = sorts(&[
        ("g", ChcSort::Bool),
        ("x", ChcSort::Int),
        ("y", ChcSort::Int),
    ]);
    let rw = apply_for_proof_script(&a, &b, &var_sorts).expect("must rewrite");
    assert_eq!(rw.a_constraints.len(), 1, "A untouched, no defs");
    assert_eq!(rw.b_constraints.len(), 4, "B rewritten + def pair");
}

#[test]
fn test_both_side_occurrence_places_def_in_a_only() {
    let a = vec![
        guarded(bvar("g"), ChcExpr::eq(ivar("x"), ivar("y"))),
        bvar("g"),
    ];
    let b = vec![
        guarded(bvar("h"), ChcExpr::not(ChcExpr::eq(ivar("x"), ivar("y")))),
        bvar("h"),
    ];
    let var_sorts = sorts(&[
        ("g", ChcSort::Bool),
        ("h", ChcSort::Bool),
        ("x", ChcSort::Int),
        ("y", ChcSort::Int),
    ]);
    let rw = apply_for_proof_script(&a, &b, &var_sorts).expect("must rewrite");
    assert_eq!(rw.diff_vars, 1);
    assert_eq!(
        rw.a_constraints.len(),
        4,
        "def pair joins the A partition when both sides use the dvar"
    );
    assert_eq!(rw.b_constraints.len(), 2, "B rewritten, no duplicate defs");
    assert!(render(&rw.b_constraints[0]).contains("ay_eqdv_p0"));
}

#[test]
fn test_skips_bool_eq_single_var_nonlinear_and_nonintegral() {
    let a = vec![
        // Bool iff: not an Int atom.
        ChcExpr::or(bvar("g"), ChcExpr::eq(bvar("p"), bvar("q"))),
        // Single-variable atom: already var-const shaped.
        ChcExpr::or(bvar("g"), ChcExpr::eq(ivar("x"), ChcExpr::Int(3))),
        // Non-linear atom.
        ChcExpr::or(
            bvar("g"),
            ChcExpr::eq(ChcExpr::mul(ivar("x"), ivar("y")), ivar("z")),
        ),
        // Non-integral normalized rhs: 2x - 2y = 1.
        ChcExpr::or(
            bvar("g"),
            ChcExpr::eq(
                ChcExpr::sub(
                    ChcExpr::mul(ChcExpr::Int(2), ivar("x")),
                    ChcExpr::mul(ChcExpr::Int(2), ivar("y")),
                ),
                ChcExpr::Int(1),
            ),
        ),
    ];
    let b = vec![ChcExpr::lt(ivar("x"), ivar("z"))];
    let var_sorts = sorts(&[
        ("g", ChcSort::Bool),
        ("p", ChcSort::Bool),
        ("q", ChcSort::Bool),
        ("x", ChcSort::Int),
        ("y", ChcSort::Int),
        ("z", ChcSort::Int),
    ]);
    assert!(
        apply_for_proof_script(&a, &b, &var_sorts).is_none(),
        "no candidate atom may survive the canonicalization filters"
    );
}

#[test]
fn test_top_level_unit_atom_is_not_a_candidate() {
    // The equality IS a whole constraint (a fixed fact): nothing to prune.
    let a = vec![ChcExpr::eq(ivar("x"), ivar("y"))];
    let b = vec![ChcExpr::lt(ivar("x"), ivar("y"))];
    assert!(apply_for_proof_script(&a, &b, &int_sorts(&["x", "y"])).is_none());
}

#[test]
fn test_top_level_atom_also_folds_when_nested_elsewhere() {
    // Same atom as a unit fact AND nested under a guard: inc-14 folds both
    // occurrences once the atom qualifies as nested somewhere.
    let eq = ChcExpr::eq(ivar("x"), ivar("y"));
    let a = vec![eq.clone(), guarded(bvar("g"), eq)];
    let b = vec![ChcExpr::lt(ivar("x"), ivar("y"))];
    let var_sorts = sorts(&[
        ("g", ChcSort::Bool),
        ("x", ChcSort::Int),
        ("y", ChcSort::Int),
    ]);
    let rw = apply_for_proof_script(&a, &b, &var_sorts).expect("must rewrite");
    assert_eq!(rw.rewritten_constraints, 2);
    assert!(render(&rw.a_constraints[0]).contains("ay_eqdv_p0"));
}

#[test]
fn test_collapse_to_duplicate_constraints_skips_rewrite() {
    // Structurally distinct atoms with one canonical row, in otherwise
    // identical clauses: the fold would collapse the two constraints into
    // one expr, breaking the script/assert 1:1 correspondence downstream.
    let a = vec![
        guarded(bvar("g"), ChcExpr::eq(ivar("x"), ivar("y"))),
        guarded(
            bvar("g"),
            ChcExpr::eq(ChcExpr::add(ivar("x"), ChcExpr::Int(0)), ivar("y")),
        ),
    ];
    let b = vec![ChcExpr::lt(ivar("x"), ivar("y"))];
    let var_sorts = sorts(&[
        ("g", ChcSort::Bool),
        ("x", ChcSort::Int),
        ("y", ChcSort::Int),
    ]);
    assert!(
        apply_for_proof_script(&a, &b, &var_sorts).is_none(),
        "duplicate-introducing rewrites must be skipped"
    );
}

#[test]
fn test_ne_atom_rewrites_preserving_operator() {
    let a = vec![
        ChcExpr::or(bvar("g"), ChcExpr::ne(ivar("x"), ivar("y"))),
        bvar("g"),
    ];
    let b = vec![ChcExpr::eq(ivar("x"), ivar("y"))];
    let var_sorts = sorts(&[
        ("g", ChcSort::Bool),
        ("x", ChcSort::Int),
        ("y", ChcSort::Int),
    ]);
    let rw = apply_for_proof_script(&a, &b, &var_sorts).expect("must rewrite");
    let folded = render(&rw.a_constraints[0]);
    assert!(
        folded.contains("Ne") && folded.contains("ay_eqdv_p0"),
        "{folded}"
    );
}

#[test]
fn test_coefficient_normalization_and_sign() {
    // -3x + 3y = 6  ->  x - y = -2 (gcd 3, sign on lowest name "x").
    let atom = ChcExpr::eq(
        ChcExpr::add(
            ChcExpr::mul(ChcExpr::Int(-3), ivar("x")),
            ChcExpr::mul(ChcExpr::Int(3), ivar("y")),
        ),
        ChcExpr::Int(6),
    );
    let a = vec![ChcExpr::or(bvar("g"), atom), bvar("g")];
    let b = vec![ChcExpr::lt(ivar("x"), ivar("y"))];
    let var_sorts = sorts(&[
        ("g", ChcSort::Bool),
        ("x", ChcSort::Int),
        ("y", ChcSort::Int),
    ]);
    let rw = apply_for_proof_script(&a, &b, &var_sorts).expect("must rewrite");
    let (_, lin) = rw.subst.iter().next().expect("one substitution");
    assert_eq!(*lin, ChcExpr::add(ivar("x"), ChcExpr::neg(ivar("y"))));
    assert!(
        render(&rw.a_constraints[0]).contains("Int(-2)"),
        "normalized rhs must be -2: {}",
        render(&rw.a_constraints[0])
    );
}

#[test]
fn test_fresh_name_collision_avoidance() {
    let a = vec![
        guarded(bvar("g"), ChcExpr::eq(ivar("x"), ivar("y"))),
        bvar("g"),
    ];
    let b = vec![ChcExpr::lt(ivar("x"), ivar("y"))];
    let mut var_sorts = sorts(&[
        ("g", ChcSort::Bool),
        ("x", ChcSort::Int),
        ("y", ChcSort::Int),
    ]);
    var_sorts.insert("ay_eqdv_p0".to_string(), ChcSort::Int);
    let rw = apply_for_proof_script(&a, &b, &var_sorts).expect("must rewrite");
    assert!(
        rw.subst.contains_key("ay_eqdv_p1"),
        "collision must skip to p1"
    );
}
