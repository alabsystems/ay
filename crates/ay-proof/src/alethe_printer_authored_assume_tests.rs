// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fail-closed tests for authored-assume dependency planning.

use super::*;
use crate::{
    try_export_alethe_with_problem_scope_and_overrides,
    try_export_alethe_with_problem_scope_overrides_and_budget,
};
use ay_core::AletheRule;

fn malformed_dependency_error(proof: &Proof, terms: &TermStore, root: TermId) -> AlethePrintError {
    let mut overrides = HashMap::default();
    overrides.insert(root, "(or x false)".to_string());
    try_export_alethe_with_problem_scope_and_overrides(proof, terms, &[root], Some(&overrides))
        .expect_err("an out-of-range dependency must fail authored-assume planning")
}

fn assert_out_of_range_dependency(error: AlethePrintError, expected_id: ProofId) {
    assert!(
        matches!(
            error,
            AlethePrintError::InvalidSurfaceStep { id, ref reason }
                if id == expected_id && reason.contains("out-of-range premise")
        ),
        "expected a typed out-of-range dependency error at {expected_id}, got: {error}"
    );
}

#[test]
fn test_authored_malformed_step_premise_fails_closed() {
    let mut terms = TermStore::new();
    let root = terms.mk_var("x", Sort::Bool);
    let mut proof = Proof::new();
    let malformed = proof.add_rule_step(
        AletheRule::Trust,
        Vec::new(),
        vec![ProofId(u32::MAX)],
        Vec::new(),
    );

    assert_out_of_range_dependency(malformed_dependency_error(&proof, &terms, root), malformed);
}

#[test]
fn test_authored_malformed_resolution_premise_fails_closed() {
    let mut terms = TermStore::new();
    let root = terms.mk_var("x", Sort::Bool);
    let mut proof = Proof::new();
    let valid = proof.add_assume(root, None);
    let malformed = proof.add_resolution(Vec::new(), root, valid, ProofId(u32::MAX));

    assert_out_of_range_dependency(malformed_dependency_error(&proof, &terms, root), malformed);
}

#[test]
fn test_authored_malformed_anchor_premise_fails_closed() {
    let mut terms = TermStore::new();
    let root = terms.mk_var("x", Sort::Bool);
    let mut proof = Proof::new();
    let malformed = proof.add_step(ProofStep::Anchor {
        end_step: ProofId(u32::MAX),
        variables: Vec::new(),
    });

    assert_out_of_range_dependency(malformed_dependency_error(&proof, &terms, root), malformed);
}

#[test]
fn test_authored_comparison_assume_bridges_back_to_identity_spelling() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let b = terms.mk_var("b", Sort::Int);
    let f_b = terms.mk_app(Symbol::named("f"), [b], Sort::Int);
    let zero = terms.mk_int(0.into());
    let canonical = terms.mk_app(Symbol::named("<="), [zero, f_b], Sort::Bool);
    let negated = terms.mk_not_raw(canonical);
    let mut proof = Proof::new();
    let positive = proof.add_assume(canonical, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), canonical, positive, negative);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(canonical, "(>= (f b) 0)".to_string());
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[canonical, negated],
        Some(&overrides),
    )
    .expect("an exact comparison reversal has a checked assume bridge");
    assert!(output.contains("(assume t0.a (>= (f b) 0))"), "{output}");
    assert!(
        output.contains("(step t0.n (cl (= (>= (f b) 0) (<= 0 (f b)))) :rule comp_simplify)"),
        "{output}"
    );
    assert!(
        output.contains("(step t0 (cl (<= 0 (f b))) :rule resolution"),
        "{output}"
    );
    assert!(
        output.contains("(assume t1 (not (<= 0 (f b))))"),
        "{output}"
    );
}

#[test]
fn test_authored_strict_comparison_uses_checker_normal_form() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let ten = terms.mk_int(10.into());
    let canonical = terms.mk_app(Symbol::named("<"), [ten, x], Sort::Bool);
    let negated = terms.mk_not_raw(canonical);
    let mut proof = Proof::new();
    let positive = proof.add_assume(canonical, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), canonical, positive, negative);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(canonical, "(> x 10)".to_string());
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[canonical, negated],
        Some(&overrides),
    )
    .expect("an exact strict comparison reversal has a checked assume bridge");
    assert!(
        output.contains("(step t0.n.s0 (cl (= (> x 10) (not (<= x 10)))) :rule comp_simplify)")
            && output
                .contains("(step t0.n.s1 (cl (= (not (<= x 10)) (< 10 x))) :rule comp_simplify)")
            && output.contains(
                "(step t0.n (cl (= (> x 10) (< 10 x))) :rule trans :premises (t0.n.s0 t0.n.s1))"
            ),
        "{output}"
    );
}

#[test]
fn test_authored_assume_bridge_budget_exhaustion_and_unbudgeted_parity() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let b = terms.mk_var("b", Sort::Int);
    let f_b = terms.mk_app(Symbol::named("f"), [b], Sort::Int);
    let zero = terms.mk_int(0.into());
    let canonical = terms.mk_app(Symbol::named("<="), [zero, f_b], Sort::Bool);
    let negated = terms.mk_not_raw(canonical);
    let mut proof = Proof::new();
    let positive = proof.add_assume(canonical, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), canonical, positive, negative);

    let surface = "(>= (f b) 0)";
    let canonical_text = "(<= 0 (f b))";
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(canonical, surface.to_string());
    let bridge_precharge = (surface.len() + canonical_text.len()) as u64;
    let exhausted_budget = bridge_precharge - 1;
    let err = try_export_alethe_with_problem_scope_overrides_and_budget(
        &proof,
        &terms,
        &[canonical, negated],
        Some(&overrides),
        Some(exhausted_budget),
    )
    .expect_err("the authored bridge must atomically precharge its bounded plan");
    assert!(
        matches!(
            err,
            AlethePrintError::EmissionBudgetExhausted { budget, .. }
                if budget == exhausted_budget
        ),
        "expected typed authored-bridge budget exhaustion: {err}"
    );

    let unbudgeted = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[canonical, negated],
        Some(&overrides),
    )
    .expect("unbudgeted authored bridge export");
    let generous = try_export_alethe_with_problem_scope_overrides_and_budget(
        &proof,
        &terms,
        &[canonical, negated],
        Some(&overrides),
        Some(1_000_000),
    )
    .expect("generously budgeted authored bridge export");
    assert_eq!(unbudgeted, generous);
}

#[test]
fn test_unsupported_authored_assume_probe_work_is_precharged() {
    use ay_core::kani_compat::DetHashMap;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not_raw(x);
    let mut proof = Proof::new();
    let positive = proof.add_assume(x, None);
    let negative = proof.add_assume(not_x, None);
    proof.add_resolution(Vec::new(), x, positive, negative);

    // This fold-shaped surface is outside the exact comparison/multiplication
    // bridge schemas. The failed probe still parses and inspects input, so its
    // bounded work must be charged before any proof step reaches the sink.
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(x, "(or x false)".to_string());
    let budget = 20;
    let err = try_export_alethe_with_problem_scope_overrides_and_budget(
        &proof,
        &terms,
        &[x, not_x],
        Some(&overrides),
        Some(budget),
    )
    .expect_err("an unsupported authored-assume probe must still consume planning budget");
    assert!(
        matches!(
            err,
            AlethePrintError::EmissionBudgetExhausted {
                budget: observed,
                steps_rendered: 0,
            } if observed == budget
        ),
        "unsupported bridge planning work must fail atomically: {err}"
    );
}

#[test]
fn test_duplicate_consumed_authored_assumes_are_precharged_per_proof_id() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let b = terms.mk_var("b", Sort::Int);
    let f_b = terms.mk_app(Symbol::named("f"), [b], Sort::Int);
    let zero = terms.mk_int(0.into());
    let canonical = terms.mk_app(Symbol::named("<="), [zero, f_b], Sort::Bool);
    let negated = terms.mk_not_raw(canonical);
    let mut proof = Proof::new();
    let negative = proof.add_assume(negated, None);
    for _ in 0..32 {
        let positive = proof.add_assume(canonical, None);
        proof.add_resolution(Vec::new(), canonical, positive, negative);
    }

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(canonical, "(>= (f b) 0)".to_string());
    let budget = 5_000;
    let err = try_export_alethe_with_problem_scope_overrides_and_budget(
        &proof,
        &terms,
        &[canonical, negated],
        Some(&overrides),
        Some(budget),
    )
    .expect_err("every consumed duplicate assume id must precharge its emitted bridge");
    assert!(
        matches!(
            err,
            AlethePrintError::EmissionBudgetExhausted {
                budget: observed,
                steps_rendered: 0,
            } if observed == budget
        ),
        "duplicate bridge work must be rejected atomically before emission: {err}"
    );
}

#[test]
fn test_unconsumed_duplicate_authored_assume_keeps_source_without_a_bridge() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let b = terms.mk_var("b", Sort::Int);
    let f_b = terms.mk_app(Symbol::named("f"), [b], Sort::Int);
    let zero = terms.mk_int(0.into());
    let canonical = terms.mk_app(Symbol::named("<="), [zero, f_b], Sort::Bool);
    let negated = terms.mk_not_raw(canonical);
    let mut proof = Proof::new();
    let unused = proof.add_assume(canonical, None);
    let used = proof.add_assume(canonical, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), canonical, used, negative);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(canonical, "(>= (f b) 0)".to_string());
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[canonical, negated],
        Some(&overrides),
    )
    .expect("only the consumed duplicate needs an equivalence bridge");

    assert!(
        output.contains(&format!("(assume {unused} (>= (f b) 0))")),
        "{output}"
    );
    assert!(
        !output.contains(&format!("(assume {unused}.a"))
            && !output.contains(&format!("(step {unused}.n")),
        "an unconsumed duplicate must not emit an unneeded bridge: {output}"
    );
    assert!(
        output.contains(&format!("(assume {used}.a (>= (f b) 0))"))
            && output.contains(&format!("(step {used}.n")),
        "the consumed duplicate must retain the checked bridge: {output}"
    );
}

#[test]
fn test_deep_canonical_authored_assume_declines_before_recursive_rendering() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let mut nested = terms.mk_var("deep_x", Sort::Int);
    let mut nested_surface = "deep_x".to_string();
    for _ in 0..80 {
        nested = terms.mk_app(Symbol::named("deep_f"), [nested], Sort::Int);
        nested_surface = format!("(deep_f {nested_surface})");
    }
    let zero = terms.mk_int(0.into());
    let canonical = terms.mk_app(Symbol::named("<="), [zero, nested], Sort::Bool);
    let negated = terms.mk_not_raw(canonical);
    let mut proof = Proof::new();
    let positive = proof.add_assume(canonical, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), canonical, positive, negative);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(canonical, format!("(>= {nested_surface} 0)"));
    let err = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[canonical, negated],
        Some(&overrides),
    )
    .expect_err("a deep canonical DAG must fail iterative preflight before rendering");
    assert!(
        matches!(
            err,
            AlethePrintError::InvalidSurfaceStep { ref reason, .. }
                if reason.contains("structural rendering bound")
        ),
        "expected the canonical pre-render bound, got: {err}"
    );
}

#[test]
fn test_oversized_authored_assume_bridge_declines_with_typed_error() {
    use ay_core::kani_compat::DetHashMap;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not_raw(x);
    let mut proof = Proof::new();
    let positive = proof.add_assume(x, None);
    let negative = proof.add_assume(not_x, None);
    proof.add_resolution(Vec::new(), x, positive, negative);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(x, "a".repeat(64 * 1024 + 1));
    let err = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[x, not_x],
        Some(&overrides),
    )
    .expect_err("an over-bound authored bridge must fail closed before emission");
    assert!(
        matches!(
            err,
            AlethePrintError::InvalidSurfaceStep { ref reason, .. }
                if reason.contains("input-size bound")
        ),
        "expected a typed authored-bridge size refusal: {err}"
    );
}

#[test]
fn test_authored_nested_multiplication_assume_uses_aci_and_congruence() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let a = terms.mk_var("a", Sort::Int);
    let four = terms.mk_int(4.into());
    let one = terms.mk_int(1.into());
    let product = terms.mk_app(Symbol::named("*"), [a, four], Sort::Int);
    let affine = terms.mk_app(Symbol::named("+"), [product, one], Sort::Int);
    let canonical = terms.mk_app(Symbol::named("="), [x, affine], Sort::Bool);
    let negated = terms.mk_not_raw(canonical);
    let mut proof = Proof::new();
    let positive = proof.add_assume(canonical, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), canonical, positive, negative);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(canonical, "(= x (+ (* 4 a) 1))".to_string());
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[canonical, negated],
        Some(&overrides),
    )
    .expect("an exact nested multiplication swap has a checked assume bridge");
    assert!(
        output.contains("(step t0.n.c1.c0 (cl (= (* 4 a) (* a 4))) :rule aci_simp)"),
        "{output}"
    );
    assert!(
        output.contains(
            "(step t0.n.c1 (cl (= (+ (* 4 a) 1) (+ (* a 4) 1))) :rule cong :premises (t0.n.c1.c0))"
        ),
        "{output}"
    );
    assert!(
        output.contains(
            "(step t0.n (cl (= (= x (+ (* 4 a) 1)) (= x (+ (* a 4) 1)))) :rule cong :premises (t0.n.c1))"
        ),
        "{output}"
    );
    assert!(
        output.contains("(step t0 (cl (= x (+ (* a 4) 1))) :rule resolution"),
        "{output}"
    );
    assert!(
        output.contains("(assume t1 (not (= x (+ (* a 4) 1))))"),
        "{output}"
    );
}

/// A binder is a SHAPE the authored-assume bridge lane cannot render, and no
/// size makes it renderable. The preflight must therefore DECLINE THE BRIDGE —
/// the way every other unsupported schema declines, into
/// `AuthoredAssumePlanner::unsupported` — rather than fail the export. The
/// escalation propagated out of `plan_equivalent_authored_assumes`, and
/// `Solver::export_last_unsat_artifact` maps any `Err` to `None`, so ONE
/// quantified assertion left a certified UNSAT with no publishable proof.
#[test]
fn quantified_authored_assume_declines_its_bridge_without_failing_the_document() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let bound = terms.mk_var("q", Sort::Int);
    let zero = terms.mk_int(0.into());
    let body = terms.mk_app(Symbol::named("<="), [zero, bound], Sort::Bool);
    let quantified = terms.mk_forall(vec![("q".to_string(), Sort::Int)], body);
    let negated = terms.mk_not_raw(quantified);
    let mut proof = Proof::new();
    let positive = proof.add_assume(quantified, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), quantified, positive, negative);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(quantified, "(forall ((q Int)) (>= q 0))".to_string());
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[quantified, negated],
        Some(&overrides),
    )
    .expect("a binder must decline its authored bridge, not the whole document");
    assert!(
        output.contains("(forall ((q Int)) (>= q 0))"),
        "the authored spelling must still reach the document:\n{output}"
    );
    assert!(
        !output.contains(":rule cong") && !output.contains(":rule comp_simplify"),
        "a shape this lane cannot render must get no equivalence bridge:\n{output}"
    );
}

/// AY's internal `(const-array v)` application declines for the same reason:
/// the canonical renderer would recursively format a sort this preflight does
/// not meter, so the bridge is impossible at ANY size. Same requirement as the
/// binder case — no bridge, but still a document.
#[test]
fn const_array_authored_assume_declines_its_bridge_without_failing_the_document() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let byte = Sort::bitvec(8);
    let array_sort = Sort::array(byte.clone(), byte.clone());
    let fill = terms.mk_bitvec(0u32.into(), 8);
    let const_array = terms.mk_app(Symbol::named("const-array"), [fill], array_sort);
    let key = terms.mk_var("k", byte.clone());
    let read = terms.mk_app(Symbol::named("select"), [const_array, key], byte);
    let equality = terms.mk_app(Symbol::named("="), [read, fill], Sort::Bool);
    let negated = terms.mk_not_raw(equality);
    let mut proof = Proof::new();
    let positive = proof.add_assume(equality, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), equality, positive, negative);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(
        equality,
        "(= (select ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) k) #x00)".to_string(),
    );
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[equality, negated],
        Some(&overrides),
    )
    .expect("a constant array must decline its authored bridge, not the whole document");
    assert!(
        output.contains("(as const (Array (_ BitVec 8) (_ BitVec 8)))"),
        "the authored spelling must still reach the document:\n{output}"
    );
    assert!(
        !output.contains("(const-array"),
        "AY's internal constant-array spelling must never reach the wire:\n{output}"
    );
}
