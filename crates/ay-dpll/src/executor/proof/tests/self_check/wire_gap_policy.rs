// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `executor::proof::tests` to preserve test FQNs.
//
// The publication-policy half of the self-check suite: the shared executor
// fixtures (single-step proof, symbolic LIA Farkas refutation, Alethe export)
// and every test of `unsat_proof_has_known_wire_gap` /
// `unsat_proof_terminal_trust_detected` — the gate that decides whether an
// internal proof carries EXTERNAL authority. Its sibling in `self_check.rs`
// covers the self-check verdict itself and the internal checker's statistics.

fn executor_with_single_proof_step(step: ProofStep) -> Executor {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    exec.last_proof = Some(Proof::from_steps(vec![step]));
    assert!(
        exec.last_proof.is_some(),
        "fixture must retain its internal proof"
    );
    exec
}

fn executor_with_symbolic_lia_farkas(coefficients: &[i64]) -> (Executor, TermId) {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let x = exec.ctx.terms.mk_var("lia_wire_x", Sort::Int);
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let lower = exec
        .ctx
        .terms
        .mk_app(Symbol::named("<="), [zero, x], Sort::Bool);
    let upper = exec
        .ctx
        .terms
        .mk_app(Symbol::named("<"), [x, zero], Sort::Bool);
    let not_lower = exec.ctx.terms.mk_not_raw(lower);
    let not_upper = exec.ctx.terms.mk_not_raw(upper);
    let mut proof = Proof::new();
    let lower_assumption = proof.add_assume(lower, None);
    let upper_assumption = proof.add_assume(upper, None);
    let lemma = proof.add_step(ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause: vec![not_lower, not_upper],
        farkas: Some(FarkasAnnotation::from_ints(coefficients)),
        kind: TheoryLemmaKind::LiaGeneric,
        lia: None,
    });
    let reduced = proof.add_resolution(vec![not_upper], lower, lower_assumption, lemma);
    proof.add_resolution(Vec::new(), upper, upper_assumption, reduced);
    exec.last_proof = Some(proof);
    (exec, x)
}

fn export_executor_proof(exec: &Executor) -> String {
    let proof = exec.last_proof.as_ref().expect("fixture retains its proof");
    let overrides = exec.proof_export_term_overrides();
    let scope: Vec<_> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Assume(term) => Some(*term),
            _ => None,
        })
        .collect();
    ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        proof,
        &exec.ctx.terms,
        &scope,
        overrides.as_ref(),
    )
    .expect("the diagnostic proof must remain printable")
}

#[test]
fn lia_farkas_promotion_is_shared_by_gate_and_printer() {
    let (exec, _) = executor_with_symbolic_lia_farkas(&[1, 1]);
    let quality = ay_proof::check_proof_strict(
        exec.last_proof.as_ref().expect("fixture retains its proof"),
        &exec.ctx.terms,
    )
    .expect("AY's strict checker must independently accept the actual certificate");
    assert!(quality.is_complete());
    assert!(
        !exec.unsat_proof_has_known_wire_gap(),
        "the exact checked Farkas promotion carries external authority"
    );
    let wire = export_executor_proof(&exec);
    assert!(wire.contains(":rule la_generic :args (1 1)"), "{wire}");
    assert!(!wire.contains(":rule lia_generic"), "{wire}");
    assert!(!wire.contains(":rule hole"), "{wire}");
}

#[test]
fn poly_simp_promotion_is_shared_by_gate_and_printer_and_rejects_surface_divergence() {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let x = exec.ctx.terms.mk_var("poly_wire_x", Sort::Int);
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let x_plus_zero = exec
        .ctx
        .terms
        .mk_app(Symbol::named("+"), [x, zero], Sort::Int);
    let identity = exec.ctx.terms.mk_eq(x_plus_zero, x);
    let negated_identity = exec.ctx.terms.mk_not_raw(identity);
    let mut proof = Proof::new();
    let assumption = proof.add_assume(negated_identity, None);
    let lemma = proof.add_step(ProofStep::TheoryLemma {
        theory: "arith".to_string(),
        clause: vec![identity],
        farkas: None,
        kind: TheoryLemmaKind::ArithClauseTautology,
        lia: None,
    });
    proof.add_resolution(Vec::new(), identity, assumption, lemma);
    let quality = ay_proof::check_proof_strict(&proof, &exec.ctx.terms)
        .expect("the internal polynomial identity must replay strictly");
    assert!(quality.is_complete());
    exec.last_proof = Some(proof);

    assert!(
        !exec.unsat_proof_has_known_wire_gap(),
        "the exact poly_simp lowering must carry external authority"
    );
    let wire = export_executor_proof(&exec);
    assert!(wire.contains(":rule poly_simp"), "{wire}");
    assert!(!wire.contains(":rule hole"), "{wire}");

    let mut divergent = ay_core::kani_compat::DetHashMap::default();
    divergent.insert(identity, "(= poly_wire_x (+ poly_wire_x 1))".to_string());
    exec.last_proof_term_overrides = Some(divergent);
    assert!(
        exec.unsat_proof_has_known_wire_gap(),
        "a changed printed equality must withhold poly_simp authority"
    );
    let wire = export_executor_proof(&exec);
    assert!(wire.contains(":rule hole"), "{wire}");
    assert!(!wire.contains(":rule poly_simp"), "{wire}");
}

#[test]
fn repeated_poly_simp_promotions_obey_the_exact_proof_wide_boundary() {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let x = exec.ctx.terms.mk_var("poly_wire_budget_x", Sort::Int);
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let x_plus_zero = exec
        .ctx
        .terms
        .mk_app(Symbol::named("+"), [x, zero], Sort::Int);
    let identity = exec.ctx.terms.mk_eq(x_plus_zero, x);
    let negated_identity = exec.ctx.terms.mk_not_raw(identity);
    let repeated = |count| {
        let mut proof = Proof::new();
        let assumption = proof.add_assume(negated_identity, None);
        let mut closing_lemma = None;
        for _ in 0..count {
            closing_lemma = Some(proof.add_step(ProofStep::TheoryLemma {
                theory: "arith".to_string(),
                clause: vec![identity],
                farkas: None,
                kind: TheoryLemmaKind::ArithClauseTautology,
                lia: None,
            }));
        }
        let closing_lemma = closing_lemma.expect("the positive promotion cap is nonzero");
        proof.add_resolution(Vec::new(), identity, assumption, closing_lemma);
        proof
    };

    exec.last_proof = Some(repeated(ay_proof::MAX_ARITH_POLY_SIMP_PROMOTIONS_PER_PROOF));
    assert!(
        !exec.unsat_proof_has_known_wire_gap(),
        "the exact aggregate boundary remains externally checkable"
    );
    let exact_wire = export_executor_proof(&exec);
    assert_eq!(
        exact_wire.matches(":rule poly_simp").count(),
        ay_proof::MAX_ARITH_POLY_SIMP_PROMOTIONS_PER_PROOF
    );
    assert!(!exact_wire.contains(":rule hole"), "{exact_wire}");

    exec.last_proof = Some(repeated(
        ay_proof::MAX_ARITH_POLY_SIMP_PROMOTIONS_PER_PROOF + 1,
    ));
    assert!(
        exec.unsat_proof_has_known_wire_gap(),
        "the borrowed preflight must fail wire-closed at boundary + 1"
    );
    let over_wire = export_executor_proof(&exec);
    assert_eq!(
        over_wire.matches(":rule hole").count(),
        ay_proof::MAX_ARITH_POLY_SIMP_PROMOTIONS_PER_PROOF + 1
    );
    assert!(
        !over_wire.contains(":rule poly_simp"),
        "an over-cap proof must disable promotion before its first expensive recognizer: {over_wire}"
    );
}

#[test]
fn int_bounds_promotion_is_shared_by_gate_and_printer_and_rejects_surface_divergence() {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let x = exec.ctx.terms.mk_var("int_bounds_wire_x", Sort::Int);
    let five = exec.ctx.terms.mk_int(BigInt::from(5));
    let six = exec.ctx.terms.mk_int(BigInt::from(6));
    let upper = exec.ctx.terms.mk_le(x, five);
    let lower = exec.ctx.terms.mk_lt(x, six);
    let not_upper = exec.ctx.terms.mk_not_raw(upper);
    let not_lower = exec.ctx.terms.mk_not_raw(lower);
    let clause = vec![not_upper, lower];
    let mut proof = Proof::new();
    let upper_assumption = proof.add_assume(upper, None);
    let lower_assumption = proof.add_assume(not_lower, None);
    let lemma = proof.add_step(ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause,
        farkas: None,
        kind: TheoryLemmaKind::IntBoundsTautology,
        lia: None,
    });
    let reduced = proof.add_resolution(vec![lower], upper, upper_assumption, lemma);
    proof.add_resolution(Vec::new(), lower, lower_assumption, reduced);
    let quality = ay_proof::check_proof_strict(&proof, &exec.ctx.terms)
        .expect("the integer bounds tautology must replay strictly");
    assert!(quality.is_complete());
    exec.last_proof = Some(proof);

    assert!(
        !exec.unsat_proof_has_known_wire_gap(),
        "the exact int-bounds lowering must carry external authority"
    );
    let wire = export_executor_proof(&exec);
    assert!(wire.contains(":rule la_generic :args (1 1)"), "{wire}");
    assert!(!wire.contains(":rule hole"), "{wire}");

    let mut divergent = ay_core::kani_compat::DetHashMap::default();
    divergent.insert(x, "(+ int_bounds_wire_x 1)".to_string());
    exec.last_proof_term_overrides = Some(divergent);
    assert!(
        exec.unsat_proof_has_known_wire_gap(),
        "a changed printed bound must withhold int-bounds authority"
    );
    let proof = exec.last_proof.as_ref().expect("fixture retains its proof");
    let overrides = exec.proof_export_term_overrides();
    assert!(
        ay_proof::try_export_alethe_with_problem_scope_and_overrides(
            proof,
            &exec.ctx.terms,
            &[],
            overrides.as_ref(),
        )
        .is_err(),
        "the printer must fail closed on the same divergent surface"
    );
}

#[test]
fn int_bounds_wire_gate_rejects_carcara_inexact_nary_coefficients() {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let x = exec.ctx.terms.mk_var("int_bounds_nary_wire_x", Sort::Int);
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let two = exec.ctx.terms.mk_int(BigInt::from(2));
    let three = exec.ctx.terms.mk_int(BigInt::from(3));
    let six = exec.ctx.terms.mk_int(BigInt::from(6));
    let nary = exec
        .ctx
        .terms
        .mk_app(Symbol::named("*"), [two, three, x], Sort::Int);
    let binary = exec
        .ctx
        .terms
        .mk_app(Symbol::named("*"), [six, x], Sort::Int);
    let upper = exec
        .ctx
        .terms
        .mk_app(Symbol::named("<="), [nary, zero], Sort::Bool);
    let lower = exec
        .ctx
        .terms
        .mk_app(Symbol::named("<="), [one, binary], Sort::Bool);
    let clause = vec![
        exec.ctx.terms.mk_not_raw(upper),
        exec.ctx.terms.mk_not_raw(lower),
    ];
    assert!(
        ay_core::proof_validation::recognize_int_bounds_tautology(&exec.ctx.terms, &clause),
        "the internal checker deliberately normalizes the n-ary coefficient"
    );
    let proof = Proof::from_steps(vec![ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause,
        farkas: None,
        kind: TheoryLemmaKind::IntBoundsTautology,
        lia: None,
    }]);
    ay_proof::authenticate_premise_clauses_strict_with_context(
        &proof,
        &exec.ctx.terms,
        None,
        None,
        &[],
    )
    .expect("the broader internal IntBounds rule remains strict-checkable");
    exec.last_proof = Some(proof);

    assert!(
        exec.unsat_proof_has_known_wire_gap(),
        "the terminal screen must withhold Carcara-inexact la_generic authority"
    );
    let proof = exec.last_proof.as_ref().expect("fixture retains its proof");
    assert!(
        ay_proof::try_export_alethe_with_problem_scope_and_overrides(
            proof,
            &exec.ctx.terms,
            &[],
            None,
        )
        .is_err(),
        "the printer must fail closed on the same n-ary coefficient"
    );
}

#[test]
fn arith_eq_triangle_lowering_is_shared_and_rejects_surface_divergence() {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let x = exec.ctx.terms.mk_var("triangle_wire_x", Sort::Int);
    let y = exec.ctx.terms.mk_var("triangle_wire_y", Sort::Int);
    let forward = exec.ctx.terms.mk_le(x, y);
    let reverse = exec.ctx.terms.mk_le(y, x);
    let equality = exec.ctx.terms.mk_eq(x, y);
    let not_forward = exec.ctx.terms.mk_not_raw(forward);
    let not_reverse = exec.ctx.terms.mk_not_raw(reverse);
    let not_equality = exec.ctx.terms.mk_not_raw(equality);
    let mut proof = Proof::new();
    let forward_assumption = proof.add_assume(forward, None);
    let reverse_assumption = proof.add_assume(reverse, None);
    let disequality_assumption = proof.add_assume(not_equality, None);
    let triangle = proof.add_step(ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause: vec![not_forward, not_reverse, equality],
        farkas: None,
        kind: TheoryLemmaKind::ArithEqTriangle,
        lia: None,
    });
    let after_forward = proof.add_resolution(
        vec![not_reverse, equality],
        forward,
        forward_assumption,
        triangle,
    );
    let equality_unit =
        proof.add_resolution(vec![equality], reverse, reverse_assumption, after_forward);
    proof.add_resolution(Vec::new(), equality, disequality_assumption, equality_unit);
    let quality = ay_proof::check_proof_strict(&proof, &exec.ctx.terms)
        .expect("the arithmetic equality triangle must replay strictly");
    assert!(quality.is_complete());
    exec.last_proof = Some(proof);

    let mut identity = ay_core::kani_compat::DetHashMap::default();
    identity.insert(x, "triangle_wire_x".to_string());
    exec.last_proof_term_overrides = Some(identity);
    assert!(
        !exec.unsat_proof_has_known_wire_gap(),
        "an identity surface must retain the checked triangle lowering"
    );
    let wire = export_executor_proof(&exec);
    assert!(wire.contains(":rule la_disequality"), "{wire}");
    assert!(!wire.contains(":rule hole"), "{wire}");

    let mut divergent = ay_core::kani_compat::DetHashMap::default();
    divergent.insert(x, "(+ triangle_wire_x 1)".to_string());
    exec.last_proof_term_overrides = Some(divergent);
    assert!(
        exec.unsat_proof_has_known_wire_gap(),
        "a changed printed triangle operand must withhold wire authority"
    );
    let proof = exec.last_proof.as_ref().expect("fixture retains its proof");
    let overrides = exec.proof_export_term_overrides();
    assert!(
        ay_proof::try_export_alethe_with_problem_scope_and_overrides(
            proof,
            &exec.ctx.terms,
            &[forward, reverse, not_equality],
            overrides.as_ref(),
        )
        .is_err(),
        "the printer must fail closed on the same divergent triangle surface"
    );
}

#[test]
fn arith_eq_implies_bound_lowering_is_shared_and_rejects_surface_divergence() {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let x = exec.ctx.terms.mk_var("eq_bound_wire_x", Sort::Int);
    let y = exec.ctx.terms.mk_var("eq_bound_wire_y", Sort::Int);
    let equality = exec.ctx.terms.mk_eq(x, y);
    let not_equality = exec.ctx.terms.mk_not_raw(equality);
    let bound = exec.ctx.terms.mk_le(x, y);
    let not_bound = exec.ctx.terms.mk_not_raw(bound);
    let mut proof = Proof::new();
    let equality_assumption = proof.add_assume(equality, None);
    let not_bound_assumption = proof.add_assume(not_bound, None);
    let lemma = proof.add_step(ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause: vec![not_equality, bound],
        farkas: None,
        kind: TheoryLemmaKind::ArithEqImpliesBound,
        lia: None,
    });
    let bound_unit = proof.add_resolution(vec![bound], equality, equality_assumption, lemma);
    proof.add_resolution(Vec::new(), bound, not_bound_assumption, bound_unit);
    ay_proof::authenticate_premise_clauses_strict_with_context(
        &proof,
        &exec.ctx.terms,
        None,
        None,
        &[equality, not_bound],
    )
    .expect("the exact equality-to-bound adapter must replay strictly");
    exec.last_proof = Some(proof);

    let mut identity = ay_core::kani_compat::DetHashMap::default();
    identity.insert(x, "eq_bound_wire_x".to_string());
    exec.last_proof_term_overrides = Some(identity);
    assert!(
        !exec.unsat_proof_has_known_wire_gap(),
        "an identity surface must retain the fixed Farkas lowering"
    );
    let wire = export_executor_proof(&exec);
    assert!(wire.contains(":rule la_generic :args (-1 1)"), "{wire}");
    assert!(!wire.contains(":rule hole"), "{wire}");

    let mut divergent = ay_core::kani_compat::DetHashMap::default();
    divergent.insert(x, "(+ eq_bound_wire_x 1)".to_string());
    exec.last_proof_term_overrides = Some(divergent);
    assert!(
        exec.unsat_proof_has_known_wire_gap(),
        "a changed printed operand must withhold equality-to-bound authority"
    );
    let proof = exec.last_proof.as_ref().expect("fixture retains its proof");
    let overrides = exec.proof_export_term_overrides();
    assert!(
        ay_proof::try_export_alethe_with_problem_scope_and_overrides(
            proof,
            &exec.ctx.terms,
            &[],
            overrides.as_ref(),
        )
        .is_err(),
        "the printer must fail closed on the same divergent equality-to-bound surface"
    );
}

#[test]
fn trans_surface_gate_rejects_a_divergent_conclusion_override() {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let x = exec.ctx.terms.mk_var("trans_wire_x", Sort::Int);
    let y = exec.ctx.terms.mk_var("trans_wire_y", Sort::Int);
    let z = exec.ctx.terms.mk_var("trans_wire_z", Sort::Int);
    let xy = exec.ctx.terms.mk_eq(x, y);
    let yz = exec.ctx.terms.mk_eq(y, z);
    let xz = exec.ctx.terms.mk_eq(x, z);
    let mut proof = Proof::new();
    let xy_id = proof.add_assume(xy, None);
    let yz_id = proof.add_assume(yz, None);
    proof.add_rule_step(AletheRule::Trans, vec![xz], vec![xy_id, yz_id], Vec::new());
    ay_proof::authenticate_premise_clauses_strict_with_context(
        &proof,
        &exec.ctx.terms,
        None,
        None,
        &[xy, yz],
    )
    .expect("the internal equality chain is a valid trans step");
    exec.last_proof = Some(proof);
    let mut overrides = ay_core::kani_compat::DetHashMap::default();
    overrides.insert(xz, "(= (+ trans_wire_x 0) trans_wire_z)".to_string());
    exec.last_proof_term_overrides = Some(overrides);

    assert!(
        exec.unsat_proof_has_known_wire_gap(),
        "a printed conclusion that no longer follows positionally must fail closed"
    );
    let proof = exec.last_proof.as_ref().expect("fixture retains its proof");
    let overrides = exec.proof_export_term_overrides();
    assert!(
        ay_proof::try_export_alethe_with_problem_scope_and_overrides(
            proof,
            &exec.ctx.terms,
            &[xy, yz],
            overrides.as_ref(),
        )
        .is_err(),
        "the printer and terminal policy must reject the same changed trans chain"
    );
}

#[test]
fn bv_zero_test_wire_gate_accepts_direct_and_idempotent_carriers_only() {
    for gate_operator in [None, Some("bvand"), Some("bvor")] {
        for zero_reversed in [false, true] {
            for reversed in [false, true] {
                let mut exec = Executor::new();
                exec.set_produce_proofs(true);
                let sort = Sort::bitvec(4);
                let subject = exec.ctx.terms.mk_var("bv_zero_wire_x", sort.clone());
                let one = exec.ctx.terms.mk_bitvec(BigInt::from(1_u8), 4);
                let zero = exec.ctx.terms.mk_bitvec(BigInt::from(0_u8), 4);
                let ult = exec
                    .ctx
                    .terms
                    .mk_app(Symbol::named("bvult"), [subject, one], Sort::Bool);
                let zero_subject = gate_operator.map_or(subject, |operator| {
                    exec.ctx
                        .terms
                        .mk_app(Symbol::named(operator), [subject, subject], sort.clone())
                });
                let eq_args = if zero_reversed {
                    [zero, zero_subject]
                } else {
                    [zero_subject, zero]
                };
                let eq_zero = exec
                    .ctx
                    .terms
                    .mk_app(Symbol::named("="), eq_args, Sort::Bool);
                let endpoints = if reversed {
                    [eq_zero, ult]
                } else {
                    [ult, eq_zero]
                };
                let equality = exec
                    .ctx
                    .terms
                    .mk_app(Symbol::named("="), endpoints, Sort::Bool);
                assert!(
                    ay_proof::recognize_bv_bitblast(&exec.ctx.terms, &[equality]),
                    "the internal checker must authenticate gate={gate_operator:?} \
                     zero_reversed={zero_reversed} reversed={reversed}"
                );
                assert!(
                    ay_proof::checked_bv_bitblast_lowering_supported(
                        &exec.ctx.terms,
                        &TheoryLemmaKind::BvBitBlast,
                        &[equality],
                        None,
                    ),
                    "the shared printer admission must recognize gate={gate_operator:?} \
                     zero_reversed={zero_reversed} reversed={reversed}"
                );
                let negated_equality = exec.ctx.terms.mk_not_raw(equality);
                let mut proof = Proof::new();
                let lemma = proof.add_step(ProofStep::TheoryLemma {
                    theory: "bv".to_string(),
                    clause: vec![equality],
                    farkas: None,
                    kind: TheoryLemmaKind::BvBitBlast,
                    lia: None,
                });
                let assumption = proof.add_assume(negated_equality, None);
                proof.add_resolution(Vec::new(), equality, lemma, assumption);
                exec.last_proof = Some(proof);

                assert!(
                    !exec.unsat_proof_has_known_wire_gap(),
                    "the terminal gate must admit gate={gate_operator:?} \
                     zero_reversed={zero_reversed} reversed={reversed}"
                );
                let wire = export_executor_proof(&exec);
                assert!(wire.contains(":rule pbblast_bvult"), "{wire}");
                assert!(!wire.contains(":rule hole"), "{wire}");

                if gate_operator.is_some() {
                    let mut divergent = ay_core::kani_compat::DetHashMap::default();
                    divergent.insert(zero_subject, "(bvand bv_zero_wire_x #b0000)".to_string());
                    exec.last_proof_term_overrides = Some(divergent);
                    assert!(
                        exec.unsat_proof_has_known_wire_gap(),
                        "a changed gate surface must lose external authority"
                    );
                    let wire = export_executor_proof(&exec);
                    assert!(wire.contains(":rule hole"), "{wire}");
                    assert!(!wire.contains(":rule pbblast_bvult"), "{wire}");
                }
            }
        }
    }
}

#[test]
fn closed_bv_evaluate_wire_gate_rejects_reachable_surface_divergence() {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let zero64 = exec.ctx.terms.mk_bitvec(BigInt::from(0_u8), 64);
    let zero_extended = exec.ctx.terms.mk_app(
        Symbol::indexed("zero_extend", vec![64]),
        [zero64],
        Sort::bitvec(128),
    );
    let eight = exec.ctx.terms.mk_bitvec(BigInt::from(8_u8), 128);
    let product = exec.ctx.terms.mk_app(
        Symbol::named("bvmul"),
        [zero_extended, eight],
        Sort::bitvec(128),
    );
    let high_half = exec.ctx.terms.mk_app(
        Symbol::indexed("extract", vec![127, 64]),
        [product],
        Sort::bitvec(64),
    );
    let equality = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [high_half, zero64], Sort::Bool);
    let proof = Proof::from_steps(vec![ProofStep::Step {
        rule: AletheRule::Evaluate,
        clause: vec![equality],
        premises: Vec::new(),
        args: Vec::new(),
    }]);
    ay_proof::authenticate_premise_clauses_strict_with_context(
        &proof,
        &exec.ctx.terms,
        None,
        None,
        &[],
    )
    .expect("the closed wide-BV evaluation must replay strictly");
    exec.last_proof = Some(proof);

    let mut identity = ay_core::kani_compat::DetHashMap::default();
    identity.insert(zero64, format!("#b{}", "0".repeat(64)));
    exec.last_proof_term_overrides = Some(identity);
    assert!(
        !exec.unsat_proof_has_known_wire_gap(),
        "an identity subterm override must retain evaluate wire authority"
    );
    let wire = export_executor_proof(&exec);
    assert!(wire.contains(":rule evaluate"), "{wire}");
    assert!(!wire.contains(":rule hole"), "{wire}");

    let mut divergent = ay_core::kani_compat::DetHashMap::default();
    divergent.insert(zero64, format!("#b{}1", "0".repeat(63)));
    exec.last_proof_term_overrides = Some(divergent);
    assert!(
        exec.unsat_proof_has_known_wire_gap(),
        "a changed reachable evaluated subterm must fail the wire gate"
    );
    let proof = exec.last_proof.as_ref().expect("fixture retains its proof");
    let overrides = exec.proof_export_term_overrides();
    assert!(
        ay_proof::try_export_alethe_with_problem_scope_and_overrides(
            proof,
            &exec.ctx.terms,
            &[],
            overrides.as_ref(),
        )
        .is_err(),
        "the printer must fail closed on the same divergent evaluate surface"
    );
}

#[test]
fn lia_farkas_mismatch_is_a_disclosed_hole_in_both_consumers() {
    let (exec, _) = executor_with_symbolic_lia_farkas(&[1, 0]);
    assert!(
        ay_proof::check_proof_strict(
            exec.last_proof.as_ref().expect("fixture retains its proof"),
            &exec.ctx.terms,
        )
        .is_err(),
        "AY's strict checker must reject the mismatched coefficients"
    );
    assert!(
        exec.unsat_proof_has_known_wire_gap(),
        "a coefficient mismatch must withhold external authority"
    );
    let wire = export_executor_proof(&exec);
    assert!(wire.contains(":rule hole"), "{wire}");
    assert!(!wire.contains(":rule lia_generic"), "{wire}");
    assert!(!wire.contains(":rule la_generic"), "{wire}");
    assert!(
        !wire.contains(":args"),
        "a hole carries no Farkas args: {wire}"
    );
}

#[test]
fn lia_surface_override_barrier_is_shared_by_gate_and_printer() {
    let (mut exec, x) = executor_with_symbolic_lia_farkas(&[1, 1]);
    let mut overrides = ay_core::kani_compat::DetHashMap::default();
    overrides.insert(x, "(+ lia_wire_x 1)".to_string());
    exec.last_proof_term_overrides = Some(overrides);

    assert!(exec.unsat_proof_has_known_wire_gap());
    let wire = export_executor_proof(&exec);
    assert!(wire.contains("(+ lia_wire_x 1)"), "{wire}");
    assert!(wire.contains(":rule hole"), "{wire}");
    assert!(!wire.contains(":rule lia_generic"), "{wire}");
    assert!(!wire.contains(":rule la_generic"), "{wire}");

    // The barrier is per-CLAUSE, not per-document: what makes the promotion
    // honest is that the text the checker reads is the text the Farkas
    // validator accepted. An installed-but-EMPTY channel cannot change any
    // clause, so it is not a barrier. This still pins the exact state input —
    // gate and printer must answer identically for `Some(empty)`, neither may
    // follow a stricter branch than the other — but it now demands the checked
    // promotion instead of accepting a discarded certificate.
    let (mut empty, _) = executor_with_symbolic_lia_farkas(&[1, 1]);
    empty.last_proof_term_overrides = Some(ay_core::kani_compat::DetHashMap::default());
    assert!(!empty.unsat_proof_has_known_wire_gap());
    let wire = export_executor_proof(&empty);
    assert!(wire.contains(":rule la_generic :args (1 1)"), "{wire}");
    assert!(!wire.contains(":rule hole"), "{wire}");
    assert!(!wire.contains(":rule lia_generic"), "{wire}");

    // The defect the narrowing removes: a channel installed for some OTHER
    // term must not discard THIS clause's certificate. The lemma's clause
    // renders byte-identically with and without the channel, so the promotion
    // stands — while the first half above shows an override that DOES reach
    // the clause still withholds it.
    let (mut unrelated, _) = executor_with_symbolic_lia_farkas(&[1, 1]);
    let other = unrelated.ctx.terms.mk_var("lia_wire_other", Sort::Int);
    let mut elsewhere = ay_core::kani_compat::DetHashMap::default();
    elsewhere.insert(other, "(+ lia_wire_other 1)".to_string());
    unrelated.last_proof_term_overrides = Some(elsewhere);
    assert!(!unrelated.unsat_proof_has_known_wire_gap());
    let wire = export_executor_proof(&unrelated);
    assert!(wire.contains(":rule la_generic :args (1 1)"), "{wire}");
    assert!(!wire.contains(":rule hole"), "{wire}");
}

#[test]
fn known_wire_gap_rejects_bare_required_string_content_theory() {
    let exec = executor_with_single_proof_step(ProofStep::TheoryLemma {
        theory: "String".to_string(),
        clause: Vec::new(),
        farkas: None,
        kind: TheoryLemmaKind::StringContentAxiom,
        lia: None,
    });
    assert!(exec.unsat_proof_has_known_wire_gap());
}

#[test]
fn carcara_surface_preflight_rejects_unsupported_sorts_and_unquotable_names() {
    let mut floating_point = Executor::new();
    floating_point.set_produce_proofs(true);
    let fp = floating_point
        .ctx
        .terms
        .mk_var("fp_surface", Sort::FloatingPoint(8, 24));
    let fp_atom = floating_point
        .ctx
        .terms
        .mk_app(Symbol::named("="), [fp, fp], Sort::Bool);
    floating_point.last_proof = Some(Proof::from_steps(vec![ProofStep::Assume(fp_atom)]));
    assert!(
        floating_point.unsat_proof_references_uncheckable_seq_theory(),
        "pinned Carcara cannot parse FloatingPoint sorts"
    );

    for name in ["a|b", "a\\b"] {
        let mut unquotable = Executor::new();
        unquotable.set_produce_proofs(true);
        let atom = unquotable.ctx.terms.mk_var(name, Sort::Bool);
        unquotable.last_proof = Some(Proof::from_steps(vec![ProofStep::Assume(atom)]));
        assert!(
            unquotable.unsat_proof_references_uncheckable_seq_theory(),
            "{name:?} has no lossless Carcara symbol spelling"
        );
    }

    let mut reserved = Executor::new();
    reserved.set_produce_proofs(true);
    let quoted = reserved.ctx.terms.mk_var("cl", Sort::Bool);
    reserved.last_proof = Some(Proof::from_steps(vec![ProofStep::Assume(quoted)]));
    assert!(
        !reserved.unsat_proof_references_uncheckable_seq_theory(),
        "Alethe reserved names are losslessly pipe-quoted"
    );
}

#[test]
fn known_wire_gap_accepts_only_fixed_true_and_false_axiom_shapes() {
    for true_rule in [true, false] {
        let mut exec = Executor::new();
        exec.set_produce_proofs(true);
        let source = exec.ctx.terms.mk_bool(true_rule);
        let literal = if true_rule {
            source
        } else {
            exec.ctx.terms.mk_not_raw(source)
        };
        exec.last_proof = Some(Proof::from_steps(vec![ProofStep::Step {
            rule: if true_rule {
                AletheRule::True
            } else {
                AletheRule::False
            },
            clause: vec![literal],
            premises: Vec::new(),
            args: vec![source],
        }]));
        assert!(
            !exec.unsat_proof_has_known_wire_gap(),
            "the exact fixed Boolean axiom is checker-supported"
        );
    }
}

#[test]
fn known_wire_gap_rejects_mutated_true_and_false_axiom_shapes() {
    let malformed_steps = [
        ProofStep::Step {
            rule: AletheRule::True,
            clause: Vec::new(),
            premises: Vec::new(),
            args: Vec::new(),
        },
        ProofStep::Step {
            rule: AletheRule::False,
            clause: Vec::new(),
            premises: vec![ProofId(0)],
            args: Vec::new(),
        },
    ];
    for step in malformed_steps {
        let exec = executor_with_single_proof_step(step);
        assert!(exec.unsat_proof_has_known_wire_gap());
    }

    let mut overridden = Executor::new();
    overridden.set_produce_proofs(true);
    let false_term = overridden.ctx.terms.mk_bool(false);
    let not_false = overridden.ctx.terms.mk_not_raw(false_term);
    overridden.last_proof = Some(Proof::from_steps(vec![ProofStep::Step {
        rule: AletheRule::False,
        clause: vec![not_false],
        premises: Vec::new(),
        args: vec![false_term],
    }]));
    let mut overrides = ay_core::kani_compat::DetHashMap::default();
    overrides.insert(false_term, "true".to_string());
    overridden.last_proof_term_overrides = Some(overrides);
    assert!(
        overridden.unsat_proof_has_known_wire_gap(),
        "a surface mutation of a fixed axiom must fail closed"
    );
}

#[test]
fn known_wire_gap_distinguishes_certified_and_unproved_let_assumes() {
    let mut structural = Executor::new();
    structural.set_produce_proofs(true);
    let value = structural.ctx.terms.true_term();
    let term = structural
        .ctx
        .terms
        .mk_let(vec![("x".to_string(), value)], value);
    structural.last_proof = Some(Proof::from_steps(vec![ProofStep::Assume(term)]));
    assert!(structural.last_proof.is_some());
    assert!(structural.unsat_proof_has_known_wire_gap());

    let consumed_surface = |source: &str| {
        let mut executor = Executor::new();
        executor.set_produce_proofs(true);
        let term = executor.ctx.terms.true_term();
        let not_term = executor.ctx.terms.mk_not_raw(term);
        let mut proof = Proof::new();
        let positive = proof.add_assume(term, None);
        let negative = proof.add_assume(not_term, None);
        proof.add_resolution(Vec::new(), term, positive, negative);
        executor.last_proof = Some(proof);
        let mut overrides = ay_core::kani_compat::DetHashMap::default();
        overrides.insert(term, source.to_string());
        executor.last_proof_term_overrides = Some(overrides);
        executor
    };

    for source in ["(let ((x true)) x)", "(let((x true))x)"] {
        assert!(
            !consumed_surface(source).unsat_proof_has_known_wire_gap(),
            "the shared printer planner must certify exact let elimination, including legal \
             SMT-LIB delimiter adjacency: {source}"
        );
    }

    let divergent = "(let ((x true)) (and x false))";
    assert!(
        consumed_surface(divergent).unsat_proof_has_known_wire_gap(),
        "a consumed source spelling that does not eliminate to the internal term must fail \
         closed: {divergent}"
    );
}

#[test]
fn known_wire_gap_allows_plain_euf_reflexive_theory() {
    let exec = executor_with_single_proof_step(ProofStep::TheoryLemma {
        theory: "EUF".to_string(),
        clause: Vec::new(),
        farkas: None,
        kind: TheoryLemmaKind::EufReflexive,
        lia: None,
    });
    assert!(!exec.unsat_proof_has_known_wire_gap());
}

#[test]
fn terminal_policy_reads_hidden_internal_proof_and_respects_lifecycle() {
    let mut exec = Executor::new();
    exec.last_proof = Some(Proof::from_steps(vec![ProofStep::TheoryLemma {
        theory: "String".to_string(),
        clause: Vec::new(),
        farkas: None,
        kind: TheoryLemmaKind::StringContentAxiom,
        lia: None,
    }]));
    assert!(!exec.is_producing_proofs());
    assert!(
        exec.last_proof().is_none(),
        "public artifact accessor must keep the internal proof hidden"
    );
    assert!(
        exec.unsat_proof_has_known_wire_gap(),
        "strict publication policy must inspect the hidden internal proof"
    );

    exec.last_unsat_proof_reconstruction_suppressed = true;
    assert!(!exec.unsat_proof_has_known_wire_gap());

    exec.last_unsat_proof_reconstruction_suppressed = false;
    assert!(exec.unsat_proof_has_known_wire_gap());
    exec.invalidate_last_check_result();
    assert!(exec.last_proof.is_none());
    assert!(!exec.unsat_proof_has_known_wire_gap());
}

#[test]
fn terminal_trust_policy_reads_hidden_internal_proof() {
    let mut exec = Executor::new();
    exec.last_proof = Some(Proof::from_steps(vec![ProofStep::Step {
        rule: AletheRule::Trust,
        clause: Vec::new(),
        premises: Vec::new(),
        args: Vec::new(),
    }]));
    assert!(!exec.is_producing_proofs());
    assert!(exec.last_proof().is_none());
    assert!(exec.unsat_proof_terminal_trust_detected());
    exec.last_unsat_proof_reconstruction_suppressed = true;
    assert!(!exec.unsat_proof_terminal_trust_detected());
}
