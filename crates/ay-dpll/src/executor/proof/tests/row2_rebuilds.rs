// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[test]
fn non_false_authored_boolean_cannot_authorize_the_false_rewrite() {
    let mut exec = Executor::new();
    let authored = exec.ctx.terms.mk_var("authored", Sort::Bool);
    exec.ctx
        .add_assertion_with_parsed(authored, parsed_placeholder());

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    let original = format!("{:?}", proof.steps);
    exec.replace_with_exact_authored_false_refutation(&mut proof);

    assert_eq!(format!("{:?}", proof.steps), original);
}

#[test]
fn bv_promotion_caps_cumulative_proof_producer_attempts() {
    let mut terms = TermStore::new();
    let bv = terms.mk_var("bv-promotion-budget", Sort::bitvec(32));
    let doubled = terms.mk_app(Symbol::named("bvadd"), vec![bv, bv], Sort::bitvec(32));
    let one = terms.mk_bitvec(BigInt::from(1), 32);
    let shifted = terms.mk_app(Symbol::named("bvshl"), vec![bv, one], Sort::bitvec(32));
    let equality = terms.mk_app(Symbol::named("="), vec![doubled, shifted], Sort::Bool);
    let mut proof = Proof::new();
    for _ in 0..=ay_proof::MAX_PROOF_PRODUCING_BV_LEMMAS_PER_PROOF {
        proof.add_theory_lemma("generic", vec![equality]);
    }

    Executor::promote_semantically_checked_bv_lemmas(&terms, &mut proof);

    assert_eq!(
        proof
            .steps
            .iter()
            .filter(|step| matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::BvBitBlast,
                    ..
                }
            ))
            .count(),
        ay_proof::MAX_PROOF_PRODUCING_BV_LEMMAS_PER_PROOF
    );
    assert!(matches!(
        proof.steps.last(),
        Some(ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::Generic,
            ..
        })
    ));
}

#[test]
fn contextual_row2_unit_is_rebuilt_as_guarded_strict_proof() {
    let mut exec = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = exec.ctx.terms.mk_var("a", array_sort);
    let i = exec.ctx.terms.mk_var("i", Sort::Int);
    let j = exec.ctx.terms.mk_var("j", Sort::Int);
    let v = exec.ctx.terms.mk_var("v", Sort::Int);
    let store = exec.ctx.terms.mk_store(a, i, v);
    let store_read = exec.ctx.terms.mk_select(store, j);
    let base_read = exec.ctx.terms.mk_select(a, j);
    let row_eq = exec.ctx.terms.mk_eq(store_read, base_read);
    let not_row_eq = exec.ctx.terms.mk_not(row_eq);
    let index_eq = exec.ctx.terms.mk_eq(i, j);
    let not_index_eq = exec.ctx.terms.mk_not(index_eq);
    exec.ctx.assertions = vec![not_index_eq, not_row_eq];

    // Exact pruned shape formerly published by the eager array lane: the unit
    // equality is only contextually valid and therefore remains Generic/trust.
    let mut proof = Proof::new();
    let trust = proof.add_theory_lemma("array", vec![row_eq]);
    let row_assume = proof.add_assume(not_row_eq, None);
    proof.add_resolution(Vec::new(), row_eq, row_assume, trust);

    exec.promote_contextual_array_row2_lemmas(&mut proof);

    assert_eq!(proof.steps.len(), 5);
    assert_eq!(
        proof
            .steps
            .iter()
            .filter(|step| matches!(step, ProofStep::Assume(_)))
            .count(),
        2
    );
    assert!(proof.steps.iter().any(|step| {
        matches!(
            step,
            ProofStep::TheoryLemma {
                clause,
                kind: TheoryLemmaKind::ArraySelectStore { index_eq: false },
                ..
            } if clause.as_slice() == [index_eq, row_eq]
        )
    }));
    assert!(proof
        .steps
        .iter()
        .all(|step| !matches!(step, ProofStep::TheoryLemma { kind, .. } if kind.is_trust())));
    ay_proof::check_proof_strict(&proof, &exec.ctx.terms)
        .expect("rebuilt contextual ROW2 proof must pass strict checking");
}

#[test]
fn direct_authored_row2_is_rebuilt_after_sat_side_ite_expansion() {
    let mut exec = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = exec.ctx.terms.mk_var("a", array_sort);
    let i = exec.ctx.terms.mk_var("i", Sort::Int);
    let j = exec.ctx.terms.mk_var("j", Sort::Int);
    let v = exec.ctx.terms.mk_var("v", Sort::Int);
    let store = exec.ctx.terms.mk_store(a, i, v);
    let store_read = exec.ctx.terms.mk_select(store, j);
    let base_read = exec.ctx.terms.mk_select(a, j);
    let row_eq = exec.ctx.terms.mk_eq(store_read, base_read);
    let not_row_eq = exec.ctx.terms.mk_not(row_eq);
    let index_eq = exec.ctx.terms.mk_eq(i, j);
    let not_index_eq = exec.ctx.terms.mk_not(index_eq);
    exec.ctx.assertions = vec![not_index_eq, not_row_eq];
    exec.proof_problem_assertion_provenance = Some(
        crate::executor::theories::solve_harness::ProofProblemAssertionProvenance {
            original_problem_assertions: exec.ctx.assertions.clone(),
            problem_assertions: exec.ctx.assertions.clone(),
            assertion_sources: Default::default(),
        },
    );

    // Exact shape retained after ABV's select-store expansion: the current
    // proof speaks about an internal ITE equality, not the authored ROW2 term.
    // The repair must derive the contradiction only from the frozen authored
    // roots above.
    let expanded_read = exec.ctx.terms.mk_ite(index_eq, v, base_read);
    let expanded_eq = exec.ctx.terms.mk_eq(expanded_read, base_read);
    let not_expanded_eq = exec.ctx.terms.mk_not(expanded_eq);
    let mut proof = Proof::new();
    let negative = proof.add_rule_step(
        AletheRule::Trust,
        vec![not_expanded_eq],
        Vec::new(),
        Vec::new(),
    );
    let positive =
        proof.add_rule_step(AletheRule::Trust, vec![expanded_eq], Vec::new(), Vec::new());
    proof.add_resolution(Vec::new(), expanded_eq, negative, positive);

    exec.replace_with_exact_authored_array_row2_refutation(&mut proof);

    assert_eq!(proof.steps.len(), 5);
    assert!(proof.steps.iter().any(|step| {
        matches!(
            step,
            ProofStep::TheoryLemma {
                clause,
                kind: TheoryLemmaKind::ArraySelectStore { index_eq: false },
                ..
            } if clause.as_slice() == [index_eq, row_eq]
        )
    }));
    assert!(proof.steps.iter().all(|step| !matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::Trust,
            ..
        }
    )));
    ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &exec.ctx.assertions)
        .expect("rebuilt direct ROW2 proof may assume only exact authored roots");
    ay_proof::check_proof_strict(&proof, &exec.ctx.terms)
        .expect("rebuilt direct ROW2 proof must pass strict checking");
}

#[test]
fn contextual_row2_repair_skips_unowned_candidate_and_uses_later_owned_unit() {
    let mut exec = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);

    let a0 = exec.ctx.terms.mk_var("a0", array_sort.clone());
    let i0 = exec.ctx.terms.mk_var("i0", Sort::Int);
    let j0 = exec.ctx.terms.mk_var("j0", Sort::Int);
    let v0 = exec.ctx.terms.mk_var("v0", Sort::Int);
    let store0 = exec.ctx.terms.mk_store(a0, i0, v0);
    let store_read0 = exec.ctx.terms.mk_select(store0, j0);
    let base_read0 = exec.ctx.terms.mk_select(a0, j0);
    let unowned_row_eq = exec.ctx.terms.mk_eq(store_read0, base_read0);

    let a1 = exec.ctx.terms.mk_var("a1", array_sort);
    let i1 = exec.ctx.terms.mk_var("i1", Sort::Int);
    let j1 = exec.ctx.terms.mk_var("j1", Sort::Int);
    let v1 = exec.ctx.terms.mk_var("v1", Sort::Int);
    let store1 = exec.ctx.terms.mk_store(a1, i1, v1);
    let store_read1 = exec.ctx.terms.mk_select(store1, j1);
    let base_read1 = exec.ctx.terms.mk_select(a1, j1);
    let owned_row_eq = exec.ctx.terms.mk_eq(store_read1, base_read1);
    let not_owned_row_eq = exec.ctx.terms.mk_not(owned_row_eq);
    let owned_index_eq = exec.ctx.terms.mk_eq(i1, j1);
    let not_owned_index_eq = exec.ctx.terms.mk_not(owned_index_eq);
    exec.ctx.assertions = vec![not_owned_index_eq, not_owned_row_eq];

    let mut proof = Proof::new();
    proof.add_theory_lemma("array", vec![unowned_row_eq]);
    proof.add_theory_lemma("array", vec![owned_row_eq]);

    exec.promote_contextual_array_row2_lemmas(&mut proof);

    assert!(proof.steps.iter().any(|step| {
        matches!(
            step,
            ProofStep::TheoryLemma {
                clause,
                kind: TheoryLemmaKind::ArraySelectStore { index_eq: false },
                ..
            } if clause.as_slice() == [owned_index_eq, owned_row_eq]
        )
    }));
    ay_proof::check_proof_strict(&proof, &exec.ctx.terms)
        .expect("a later contextual unit with owned roots must be repaired");
}

#[test]
fn contextual_row2_repair_accepts_owned_check_sat_assuming_roots() {
    let mut exec = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = exec.ctx.terms.mk_var("a", array_sort);
    let i = exec.ctx.terms.mk_var("i", Sort::Int);
    let j = exec.ctx.terms.mk_var("j", Sort::Int);
    let v = exec.ctx.terms.mk_var("v", Sort::Int);
    let store = exec.ctx.terms.mk_store(a, i, v);
    let store_read = exec.ctx.terms.mk_select(store, j);
    let base_read = exec.ctx.terms.mk_select(a, j);
    let row_eq = exec.ctx.terms.mk_eq(store_read, base_read);
    let not_row_eq = exec.ctx.terms.mk_not(row_eq);
    let index_eq = exec.ctx.terms.mk_eq(i, j);
    let not_index_eq = exec.ctx.terms.mk_not(index_eq);
    exec.last_assumptions = Some(vec![not_index_eq, not_row_eq]);

    let mut proof = Proof::new();
    proof.add_theory_lemma("array", vec![row_eq]);

    exec.promote_contextual_array_row2_lemmas(&mut proof);

    assert_eq!(
        proof
            .steps
            .iter()
            .filter(|step| matches!(step, ProofStep::Assume(_)))
            .count(),
        2
    );
    ay_proof::check_proof_strict(&proof, &exec.ctx.terms)
        .expect("active check-sat-assuming roots are legitimate ROW2 proof inputs");
}

#[test]
fn shadowed_store_generic_lemma_expands_to_strict_primitives() {
    let mut exec = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = exec.ctx.terms.mk_var("a", array_sort);
    let i = exec.ctx.terms.mk_var("i", Sort::Int);
    let j = exec.ctx.terms.mk_var("j", Sort::Int);
    let v = exec.ctx.terms.mk_var("v", Sort::Int);
    let w = exec.ctx.terms.mk_var("w", Sort::Int);
    let x = exec.ctx.terms.mk_var("x", Sort::Int);

    let lhs_inner = exec.ctx.terms.mk_store(a, i, v);
    let rhs_inner = exec.ctx.terms.mk_store(a, i, w);
    let lhs = exec.ctx.terms.mk_store(lhs_inner, j, x);
    let rhs = exec.ctx.terms.mk_store(rhs_inner, j, x);
    let array_eq = exec.ctx.terms.mk_eq(lhs, rhs);
    let not_array_eq = exec.ctx.terms.mk_not(array_eq);
    let index_eq = exec.ctx.terms.mk_eq(i, j);
    let value_eq = exec.ctx.terms.mk_eq(v, w);
    let compact = exec.ctx.terms.mk_or(vec![not_array_eq, index_eq, value_eq]);
    let not_compact = exec.ctx.terms.mk_not_raw(compact);

    let mut proof = Proof::new();
    let lemma = proof.add_theory_lemma("array", vec![compact]);
    // Keep the named assumption after the expanded lemma so proof surgery must
    // remap the public name→ProofId index, not merely the inference premises.
    let assumption = proof.add_assume(not_compact, Some("shadowed_input".to_string()));
    proof.add_rule_step(
        AletheRule::ThResolution,
        Vec::new(),
        vec![lemma, assumption],
        Vec::new(),
    );
    // The strict/revert gate authenticates every Assume against the active
    // problem. Model this fixture as a check-sat-assuming refutation instead
    // of relying on the pre-authority-check behavior that admitted any leaf.
    exec.last_assumptions = Some(vec![not_compact]);
    exec.split_shadowed_store_equality_lemmas(&mut proof);

    let named = proof
        .named_steps
        .get("shadowed_input")
        .expect("named assumption must survive proof-id remapping");
    assert!(matches!(
        proof.steps.get(named.0 as usize),
        Some(ProofStep::Assume(term)) if *term == not_compact
    ));

    assert!(proof
        .steps
        .iter()
        .all(|step| { !matches!(step, ProofStep::TheoryLemma { kind, .. } if kind.is_trust()) }));
    assert!(proof.steps.iter().any(|step| {
        matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::ArraySelectStore { index_eq: true },
                ..
            }
        )
    }));
    assert!(proof.steps.iter().any(|step| {
        matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::ArraySelectStore { index_eq: false },
                ..
            }
        )
    }));
    assert!(proof.steps.iter().any(|step| {
        matches!(step, ProofStep::Step { clause, .. } if clause.as_slice() == [compact])
    }));
    assert!(matches!(
        proof.steps.last(),
        Some(ProofStep::Step { clause, .. }) if clause.is_empty()
    ));
    ay_proof::check_proof_strict(&proof, &exec.ctx.terms)
        .expect("expanded shadowed-store lemma must be strictly checkable");
}

#[test]
fn shadowed_store_expansion_handles_deduplicated_index_and_value_equality() {
    let mut exec = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = exec.ctx.terms.mk_var("a", array_sort);
    let i = exec.ctx.terms.mk_var("i", Sort::Int);
    let j = exec.ctx.terms.mk_var("j", Sort::Int);
    let x = exec.ctx.terms.mk_var("x", Sort::Int);

    // The inner values are i and j, so the index and value side conditions
    // are both the exact term `(= i j)`.  `mk_or` canonicalizes the compact
    // theorem to two disjuncts; proof surgery must not mistake that for a
    // malformed three-literal theorem and leave a trust step behind.
    let lhs_inner = exec.ctx.terms.mk_store(a, i, i);
    let rhs_inner = exec.ctx.terms.mk_store(a, i, j);
    let lhs = exec.ctx.terms.mk_store(lhs_inner, j, x);
    let rhs = exec.ctx.terms.mk_store(rhs_inner, j, x);
    let array_eq = exec.ctx.terms.mk_eq(lhs, rhs);
    let not_array_eq = exec.ctx.terms.mk_not(array_eq);
    let shared_eq = exec.ctx.terms.mk_eq(i, j);
    let compact = exec
        .ctx
        .terms
        .mk_or(vec![not_array_eq, shared_eq, shared_eq]);
    let TermData::App(_, compact_args) = exec.ctx.terms.get(compact) else {
        panic!("expected compact disjunction");
    };
    assert_eq!(compact_args.len(), 2, "duplicate side condition must fold");
    let not_compact = exec.ctx.terms.mk_not_raw(compact);

    let mut proof = Proof::new();
    let assumption = proof.add_assume(not_compact, None);
    let lemma = proof.add_theory_lemma("array", vec![compact]);
    proof.add_rule_step(
        AletheRule::ThResolution,
        Vec::new(),
        vec![lemma, assumption],
        Vec::new(),
    );
    exec.last_assumptions = Some(vec![not_compact]);
    exec.split_shadowed_store_equality_lemmas(&mut proof);

    assert!(proof
        .steps
        .iter()
        .all(|step| !matches!(step, ProofStep::TheoryLemma { kind, .. } if kind.is_trust())));
    assert!(matches!(
        proof.steps.last(),
        Some(ProofStep::Step { clause, .. }) if clause.is_empty()
    ));
    ay_proof::check_proof_strict(&proof, &exec.ctx.terms)
        .expect("deduplicated shadowed-store proof must be strictly checkable");
}
