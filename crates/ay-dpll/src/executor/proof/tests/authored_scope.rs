// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[cfg(test)]
fn emit_firewall_lean(exec: &Executor, proof: &Proof) -> Vec<String> {
    exec.emit_datatype_firewall_lean_bounded(proof, usize::MAX, usize::MAX)
        .expect("test fixture must fit in the address-space bounds")
}

#[test]
fn exact_concrete_authored_scope_deduplicates_without_reordering() {
    let mut exec = Executor::new();
    let first = exec.ctx.terms.mk_var("scope_first", Sort::Bool);
    let second = exec.ctx.terms.mk_var("scope_second", Sort::Bool);
    let assumption = exec.ctx.terms.mk_var("scope_assumption", Sort::Bool);
    exec.proof_problem_assertion_provenance = Some(
        crate::executor::theories::solve_harness::ProofProblemAssertionProvenance {
            original_problem_assertions: vec![first, second, first],
            problem_assertions: vec![first, second, first],
            assertion_sources: Default::default(),
        },
    );
    exec.last_assumptions = Some(vec![second, assumption, first, assumption]);

    assert_eq!(
        exec.exact_concrete_authored_scope(),
        vec![first, second, assumption],
        "set-backed membership must preserve the first-seen Vec order and cross-source dedup"
    );
}

/// Regression for `fmap_deref`: two equality chains refute an authored `or`; unrelated equality
/// roots deliberately make the bounded saturation cross its former 48-fact
/// ceiling. The rebuilt proof must derive every required equality and then use
/// the checker-validated `or`/resolution rules to close the exact authored root.
#[test]
fn authored_equality_closure_scales_to_disjunctive_disequality_goal() {
    let mut exec = Executor::new();
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let k = exec.ctx.terms.mk_var("wp-k", Sort::Int);
    let v = exec.ctx.terms.mk_var("wp-v", Sort::Int);
    let mut roots = Vec::new();

    for (prefix, end) in [("k", k), ("v", v)] {
        let a = exec.ctx.terms.mk_var(format!("wp-{prefix}-a"), Sort::Int);
        let b = exec.ctx.terms.mk_var(format!("wp-{prefix}-b"), Sort::Int);
        let c = exec.ctx.terms.mk_var(format!("wp-{prefix}-c"), Sort::Int);
        roots.push(exec.ctx.terms.mk_eq(one, a));
        roots.push(exec.ctx.terms.mk_eq(a, b));
        roots.push(exec.ctx.terms.mk_eq(b, c));
        roots.push(exec.ctx.terms.mk_eq(c, end));
    }
    // Irrelevant roots expand the pairwise transitive closure enough to exercise the bound that rejected the live
    // 70-assertion artifact.
    for group in 0..3 {
        let mut previous = exec
            .ctx
            .terms
            .mk_var(format!("wp-noise-{group}-0"), Sort::Int);
        for index in 1..=4 {
            let next = exec
                .ctx
                .terms
                .mk_var(format!("wp-noise-{group}-{index}"), Sort::Int);
            roots.push(exec.ctx.terms.mk_eq(previous, next));
            previous = next;
        }
    }
    let k_eq_one = exec.ctx.terms.mk_eq(k, one);
    let v_eq_one = exec.ctx.terms.mk_eq(v, one);
    let not_k_eq_one = exec.ctx.terms.mk_not_raw(k_eq_one);
    let not_v_eq_one = exec.ctx.terms.mk_not_raw(v_eq_one);
    let goal = exec.ctx.terms.mk_app(
        Symbol::named("or"),
        [not_k_eq_one, not_v_eq_one],
        Sort::Bool,
    );
    roots.push(goal);
    for &root in &roots {
        exec.ctx
            .add_assertion_with_parsed(root, parsed_placeholder());
    }

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    exec.replace_with_exact_authored_equality_closure_refutation(&mut proof);

    exec.check_proof_strict_with_datatypes(&proof)
        .expect("large disjunctive equality closure must pass the plain strict checker");
    ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &roots)
        .expect("the rebuilt proof may assume only exact authored roots");
    assert!(ay_proof::terminal_trust_report(&proof).is_trust_free());
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::Or,
            ..
        }
    )));
    assert!(
        proof
            .steps
            .iter()
            .filter(|step| matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::EqTransitive,
                    ..
                }
            ))
            .count()
            >= 6,
        "both four-edge goal chains must be derived, not assumed"
    );
    let printed = ay_proof::try_export_alethe(&proof, &exec.ctx.terms)
        .expect("the Or+resolution dependency cone must export as Alethe");
    assert!(printed.contains(":rule or"));
    assert!(printed.contains(":rule resolution"));
    assert!(
        !printed.contains(":rule trust") && !printed.contains(":rule hole"),
        "exported proof must contain no tolerated step:\n{printed}"
    );
}

/// Regression for the exact cardinality that used to reject verification-consumer's
/// snapshot-alias preservation proof: two three-edge authored equality chains,
/// one disjunctive disequality goal, and 26 unrelated singleton equalities make
/// 33 distinct roots.  The decoys cannot participate in either goal chain.
#[test]
fn authored_equality_closure_accepts_thirty_three_exact_roots() {
    let mut exec = Executor::new();
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let k = exec.ctx.terms.mk_var("wp-33-k", Sort::Int);
    let v = exec.ctx.terms.mk_var("wp-33-v", Sort::Int);
    let mut roots = Vec::new();

    for (prefix, end) in [("k", k), ("v", v)] {
        let left = exec
            .ctx
            .terms
            .mk_var(format!("wp-33-{prefix}-left"), Sort::Int);
        let right = exec
            .ctx
            .terms
            .mk_var(format!("wp-33-{prefix}-right"), Sort::Int);
        roots.push(exec.ctx.terms.mk_eq(one, left));
        roots.push(exec.ctx.terms.mk_eq(left, right));
        roots.push(exec.ctx.terms.mk_eq(right, end));
    }
    for index in 0..26 {
        let left = exec
            .ctx
            .terms
            .mk_var(format!("wp-33-decoy-{index}-left"), Sort::Int);
        let right = exec
            .ctx
            .terms
            .mk_var(format!("wp-33-decoy-{index}-right"), Sort::Int);
        roots.push(exec.ctx.terms.mk_eq(left, right));
    }
    let k_eq_one = exec.ctx.terms.mk_eq(k, one);
    let v_eq_one = exec.ctx.terms.mk_eq(v, one);
    let not_k_eq_one = exec.ctx.terms.mk_not_raw(k_eq_one);
    let not_v_eq_one = exec.ctx.terms.mk_not_raw(v_eq_one);
    roots.push(exec.ctx.terms.mk_app(
        Symbol::named("or"),
        [not_k_eq_one, not_v_eq_one],
        Sort::Bool,
    ));
    assert_eq!(roots.len(), 33);
    for &root in &roots {
        exec.ctx
            .add_assertion_with_parsed(root, parsed_placeholder());
    }

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    exec.replace_with_exact_authored_equality_closure_refutation(&mut proof);

    exec.check_proof_strict_with_datatypes(&proof)
        .expect("the exact 33-root snapshot-alias class must be strictly checked");
    ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &roots)
        .expect("the widened lane may assume only its 33 exact authored roots");
    assert!(ay_proof::terminal_trust_report(&proof).is_trust_free());

    // A forged foreign premise must still fail the independent scope gate.
    let foreign = exec.ctx.terms.mk_var("wp-33-foreign-premise", Sort::Bool);
    let not_foreign = exec.ctx.terms.mk_not_raw(foreign);
    let mut forged = Proof::new();
    let premise = forged.add_assume(foreign, None);
    let complement = forged.add_assume(not_foreign, None);
    forged.add_resolution(Vec::new(), foreign, premise, complement);
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&forged, &roots).is_err());
}

/// Resource-bound control: 65 distinct roots remain outside this lane even
/// when two of them directly contradict.  Declining preserves the original
/// rejected proof and cannot mint authority past the explicit root cap.
#[test]
fn authored_equality_closure_above_root_bound_declines() {
    let mut exec = Executor::new();
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let target = exec.ctx.terms.mk_var("wp-65-target", Sort::Int);
    let equality = exec.ctx.terms.mk_eq(target, one);
    let disequality = exec.ctx.terms.mk_not_raw(equality);
    let mut roots = vec![equality, disequality];
    for index in 0..63 {
        let left = exec
            .ctx
            .terms
            .mk_var(format!("wp-65-decoy-{index}-left"), Sort::Int);
        let right = exec
            .ctx
            .terms
            .mk_var(format!("wp-65-decoy-{index}-right"), Sort::Int);
        roots.push(exec.ctx.terms.mk_eq(left, right));
    }
    assert_eq!(roots.len(), 65);
    for &root in &roots {
        exec.ctx
            .add_assertion_with_parsed(root, parsed_placeholder());
    }

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    let original = format!("{:?}", proof.steps);
    exec.replace_with_exact_authored_equality_closure_refutation(&mut proof);

    assert_eq!(format!("{:?}", proof.steps), original);
    assert!(exec.check_proof_strict_with_datatypes(&proof).is_err());
}

/// Soundness control for the disjunctive closer: deriving only one equality is
/// insufficient. The pass must leave the rejected trust proof untouched.
#[test]
fn authored_equality_closure_disjunctive_goal_requires_every_equality() {
    let mut exec = Executor::new();
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let k = exec.ctx.terms.mk_var("wp-negative-k", Sort::Int);
    let v = exec.ctx.terms.mk_var("wp-negative-v", Sort::Int);
    let k_eq_one = exec.ctx.terms.mk_eq(k, one);
    let v_eq_one = exec.ctx.terms.mk_eq(v, one);
    let not_k_eq_one = exec.ctx.terms.mk_not_raw(k_eq_one);
    let not_v_eq_one = exec.ctx.terms.mk_not_raw(v_eq_one);
    let goal = exec.ctx.terms.mk_app(
        Symbol::named("or"),
        [not_k_eq_one, not_v_eq_one],
        Sort::Bool,
    );
    for root in [k_eq_one, goal] {
        exec.ctx
            .add_assertion_with_parsed(root, parsed_placeholder());
    }

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    let original = format!("{:?}", proof.steps);
    exec.replace_with_exact_authored_equality_closure_refutation(&mut proof);

    assert_eq!(format!("{:?}", proof.steps), original);
    assert!(exec.check_proof_strict_with_datatypes(&proof).is_err());
}

/// Completeness bound control: a nine-way disequality disjunction is outside
/// this reconstruction lane's explicit arity budget. Even when every branch
/// can be refuted, the pass must decline and preserve the rejected proof.
#[test]
fn authored_equality_closure_disjunctive_goal_above_bound_declines() {
    let mut exec = Executor::new();
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let mut roots = Vec::new();
    let mut disequalities = Vec::new();
    for index in 0..9 {
        let value = exec
            .ctx
            .terms
            .mk_var(format!("wp-over-bound-{index}"), Sort::Int);
        let equality = exec.ctx.terms.mk_eq(value, one);
        roots.push(equality);
        disequalities.push(exec.ctx.terms.mk_not_raw(equality));
    }
    let goal = exec
        .ctx
        .terms
        .mk_app(Symbol::named("or"), disequalities, Sort::Bool);
    roots.push(goal);
    for &root in &roots {
        exec.ctx
            .add_assertion_with_parsed(root, parsed_placeholder());
    }

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    let original = format!("{:?}", proof.steps);
    exec.replace_with_exact_authored_equality_closure_refutation(&mut proof);

    assert_eq!(format!("{:?}", proof.steps), original);
    assert!(exec.check_proof_strict_with_datatypes(&proof).is_err());
}

/// Structural control: only `(or (not (= ..)) ..)` is in the closer lane. A
/// positive equality disjunct must not be silently reinterpreted as negative.
#[test]
fn authored_equality_closure_disjunctive_goal_wrong_polarity_declines() {
    let mut exec = Executor::new();
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let k = exec.ctx.terms.mk_var("wp-wrong-polarity-k", Sort::Int);
    let v = exec.ctx.terms.mk_var("wp-wrong-polarity-v", Sort::Int);
    let k_eq_one = exec.ctx.terms.mk_eq(k, one);
    let v_eq_one = exec.ctx.terms.mk_eq(v, one);
    let not_v_eq_one = exec.ctx.terms.mk_not_raw(v_eq_one);
    let goal = exec
        .ctx
        .terms
        .mk_app(Symbol::named("or"), [k_eq_one, not_v_eq_one], Sort::Bool);
    for root in [k_eq_one, v_eq_one, goal] {
        exec.ctx
            .add_assertion_with_parsed(root, parsed_placeholder());
    }

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    let original = format!("{:?}", proof.steps);
    exec.replace_with_exact_authored_equality_closure_refutation(&mut proof);

    assert_eq!(format!("{:?}", proof.steps), original);
    assert!(exec.check_proof_strict_with_datatypes(&proof).is_err());
}

#[test]
fn over_depth_authored_source_poison_is_installed_before_proof_clones() {
    let mut exec = Executor::new();
    let atom = exec
        .ctx
        .terms
        .mk_var("over_depth_authored_source", Sort::Bool);
    let mut parsed = FrontendTerm::Symbol("over_depth_authored_source".to_string());
    for _ in 0..300 {
        parsed = FrontendTerm::App("not".to_string(), vec![parsed]);
    }
    exec.ctx.add_assertion_with_parsed(atom, parsed);
    exec.last_finite_enum_pigeonhole = Some(crate::executor::FiniteEnumPigeonholeWitness {
        k: 1,
        members: Vec::new(),
        edge_sources: Default::default(),
    });

    exec.build_unsat_proof();

    let proof = exec.last_proof.as_ref().expect("poison proof is retained");
    assert!(matches!(
        proof.steps.as_slice(),
        [ProofStep::Step {
            rule: AletheRule::Trust,
            clause,
            premises,
            ..
        }] if clause.is_empty() && premises.is_empty()
    ));
    assert!(exec.last_checked_finite_enum_pigeonhole.is_none());
}

const OVERSIZED_PROOF_ROOTS: usize = 100_001;
