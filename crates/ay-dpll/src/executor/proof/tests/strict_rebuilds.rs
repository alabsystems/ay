// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[test]
fn lra_reconstruction_rebinds_solver_coefficients_to_clause_order() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("farkas-order-x", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let seven = terms.mk_int(BigInt::from(7));
    let x_le_two = terms.mk_le(x, two);
    let two_x = terms.mk_mul(vec![two, x]);
    let seven_le_two_x = terms.mk_le(seven, two_x);
    let not_x_le_two = terms.mk_not_raw(x_le_two);
    let not_seven_le_two_x = terms.mk_not_raw(seven_le_two_x);
    let clause = vec![not_x_le_two, not_seven_le_two_x];

    let mut farkas = None;
    let mut kind = TheoryLemmaKind::Generic;
    assert!(super::super::proof_farkas::try_lra_farkas_reconstruction(
        &terms,
        &clause,
        &mut farkas,
        &mut kind,
    ));

    let farkas = farkas.expect("an exact Farkas certificate");
    assert_eq!(
        farkas.coefficients,
        vec![
            num_rational::Rational64::new(1, 1),
            num_rational::Rational64::new(1, 2),
        ],
        "coefficients must follow the target proof-clause order, not the LRA conflict order"
    );
    assert!(!kind.is_trust());
}

#[test]
fn exact_authored_false_gets_a_trust_free_strict_refutation() {
    let mut exec = Executor::new();
    let false_term = exec.ctx.terms.false_term();
    exec.ctx
        .add_assertion_with_parsed(false_term, FrontendTerm::Const(FrontendConstant::False));

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    exec.replace_with_exact_authored_false_refutation(&mut proof);

    assert_eq!(proof.steps.len(), 3);
    assert!(matches!(proof.steps[0], ProofStep::Assume(term) if term == false_term));
    assert!(matches!(
        proof.steps[1],
        ProofStep::Step {
            rule: AletheRule::False,
            ..
        }
    ));
    assert!(matches!(
        proof.steps[2],
        ProofStep::Resolution { ref clause, .. } if clause.is_empty()
    ));
    exec.check_proof_strict_with_datatypes(&proof)
        .expect("exact authored false refutation must pass the full strict boundary");
    assert!(ay_proof::terminal_trust_report(&proof).is_trust_free());
}

#[test]
fn literal_false_authority_clears_a_competing_folded_surface_override() {
    let mut exec = Executor::new();
    let false_term = exec.ctx.terms.false_term();
    exec.ctx.add_assertion_with_parsed(
        false_term,
        FrontendTerm::App(
            "not".to_string(),
            vec![FrontendTerm::Const(FrontendConstant::True)],
        ),
    );
    exec.begin_public_solve(false);
    exec.bind_authored_unsat_query_assumptions(
        &[false_term],
        &Command::CheckSatAssuming(vec![FrontendTerm::Const(FrontendConstant::False)]),
    );
    let mut overrides = ay_core::kani_compat::DetHashMap::default();
    overrides.insert(false_term, "(not true)".to_string());
    exec.last_proof_term_overrides = Some(overrides);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    exec.replace_with_exact_authored_false_refutation(&mut proof);
    false_source::demote_unattributed_assumed_false(&mut exec, &mut proof);

    assert!(matches!(
        proof.steps.last(),
        Some(ProofStep::Resolution { clause, .. }) if clause.is_empty()
    ));
    assert!(!exec
        .last_proof_term_overrides
        .as_ref()
        .is_some_and(|current| current.contains_key(&false_term)));
}

#[test]
fn affine_uf_refutation_uses_exact_inequality_bounds() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_var("affine-uf-x", Sort::Int);
    let y = exec.ctx.terms.mk_var("affine-uf-y", Sort::Int);
    let five = exec.ctx.terms.mk_int(BigInt::from(5));
    let ten = exec.ctx.terms.mk_int(BigInt::from(10));
    let twenty = exec.ctx.terms.mk_int(BigInt::from(20));
    let x_ge_five = exec.ctx.terms.mk_ge(x, five);
    let x_le_five = exec.ctx.terms.mk_le(x, five);
    let y_eq_five = exec.ctx.terms.mk_eq(y, five);
    let f_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("affine-uf-f"), [x], Sort::Int);
    let f_y = exec
        .ctx
        .terms
        .mk_app(Symbol::named("affine-uf-f"), [y], Sort::Int);
    let f_x_eq_ten = exec.ctx.terms.mk_eq(f_x, ten);
    let f_y_eq_twenty = exec.ctx.terms.mk_eq(f_y, twenty);
    for root in [x_ge_five, x_le_five, y_eq_five, f_x_eq_ten, f_y_eq_twenty] {
        exec.ctx
            .add_assertion_with_parsed(root, parsed_placeholder());
    }

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    exec.replace_with_exact_authored_affine_euf_refutation(&mut proof);

    assert!(ay_proof::terminal_trust_report(&proof).is_trust_free());
    exec.check_proof_strict_with_datatypes(&proof)
        .expect("inequality bounds must compose with EUF under strict replay");
    ay_proof::validate_reachable_assumes_in_problem_scope(
        &proof,
        &[x_ge_five, x_le_five, y_eq_five, f_x_eq_ten, f_y_eq_twenty],
    )
    .expect("the reconstructed proof may assume only exact authored roots");
}

#[test]
fn affine_uf_refutation_skips_interpreted_incremental_lia_terms() {
    let mut exec = Executor::new();
    let mut counts = Vec::new();
    for step in 0..=10 {
        counts.push(
            exec.ctx
                .terms
                .mk_var(format!("lia-count-{step}"), Sort::Int),
        );
    }
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let twenty = exec.ctx.terms.mk_int(BigInt::from(20));
    let init = exec.ctx.terms.mk_eq(counts[0], zero);
    exec.ctx
        .add_assertion_with_parsed(init, parsed_placeholder());
    for step in 1..=10 {
        let increment = exec.ctx.terms.mk_add(vec![counts[step - 1], one]);
        let transition = exec.ctx.terms.mk_eq(counts[step], increment);
        exec.ctx
            .add_assertion_with_parsed(transition, parsed_placeholder());
    }
    let safe = exec.ctx.terms.mk_le(counts[10], twenty);
    let violation = exec.ctx.terms.mk_not_raw(safe);
    exec.ctx
        .add_assertion_with_parsed(violation, parsed_placeholder());

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    exec.replace_with_exact_authored_affine_euf_refutation(&mut proof);

    assert!(matches!(
        proof.steps.as_slice(),
        [ProofStep::Step {
            rule: AletheRule::Trust,
            ..
        }]
    ));
}

#[test]
fn solver_only_false_cannot_authorize_the_authored_false_rewrite() {
    let mut exec = Executor::new();
    let authored = exec.ctx.terms.mk_var("authored", Sort::Bool);
    exec.ctx
        .add_assertion_with_parsed(authored, parsed_placeholder());
    // Deliberately append `false` without a parallel parsed/authored entry.
    // This models a solver-generated assertion outside the problem scope.
    let false_term = exec.ctx.terms.false_term();
    exec.ctx.assertions.push(false_term);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    let original = format!("{:?}", proof.steps);
    exec.replace_with_exact_authored_false_refutation(&mut proof);

    assert_eq!(format!("{:?}", proof.steps), original);
}

#[test]
fn solver_only_false_cannot_authorize_rewrite_without_parsed_retention() {
    let mut exec = Executor::new();
    exec.ctx.set_retain_parsed_assertions(false);
    let authored = exec.ctx.terms.mk_var("authored-no-ast", Sort::Bool);
    exec.ctx
        .add_assertion_with_parsed(authored, parsed_placeholder());
    assert!(exec.ctx.assertions_parsed().is_empty());

    // The transient term is indistinguishable from an authored term in the
    // raw solver stack; only Context's concrete-authored provenance may grant
    // the canonical false refutation.
    let false_term = exec.ctx.terms.false_term();
    exec.ctx.assertions.push(false_term);
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    let original = format!("{:?}", proof.steps);
    exec.replace_with_exact_authored_false_refutation(&mut proof);

    assert_eq!(format!("{:?}", proof.steps), original);
}

#[test]
fn exact_authored_false_still_authorizes_without_parsed_retention() {
    let mut exec = Executor::new();
    exec.ctx.set_retain_parsed_assertions(false);
    let false_term = exec.ctx.terms.false_term();
    exec.ctx
        .add_assertion_with_parsed(false_term, FrontendTerm::Const(FrontendConstant::False));
    assert!(exec.ctx.assertions_parsed().is_empty());

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    exec.replace_with_exact_authored_false_refutation(&mut proof);

    assert!(matches!(
        proof.steps.last(),
        Some(ProofStep::Resolution { clause, .. }) if clause.is_empty()
    ));
    exec.check_proof_strict_with_datatypes(&proof)
        .expect("the exact concrete-authored false term remains authoritative");
}

#[test]
fn folded_authored_false_cannot_masquerade_as_literal_false_without_parsed_retention() {
    let mut exec = Executor::new();
    exec.ctx.set_retain_parsed_assertions(false);
    let false_term = exec.ctx.terms.false_term();
    // This source is contradictory and therefore elaborates to the same
    // canonical false TermId, but the problem did not literally assert
    // `false`. The compact authored-source bit must retain that distinction
    // after the full parsed tree is discarded.
    let folded_source = FrontendTerm::App(
        "not".to_string(),
        vec![FrontendTerm::Const(FrontendConstant::True)],
    );
    exec.ctx
        .add_assertion_with_parsed(false_term, folded_source);
    assert!(exec.ctx.assertions_parsed().is_empty());

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    let original = format!("{:?}", proof.steps);
    exec.replace_with_exact_authored_false_refutation(&mut proof);

    assert_eq!(format!("{:?}", proof.steps), original);
}

fn terminal_empty_trust(proof: &mut Proof, premise: Option<ProofId>) {
    proof.add_rule_step(
        AletheRule::Trust,
        Vec::new(),
        premise.into_iter().collect(),
        Vec::new(),
    );
}

#[test]
fn terminal_trust_rebuilds_from_exact_multi_assertion_bv_refutation() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_var("mc-join-x", Sort::bitvec(32));
    let zero = exec.ctx.terms.mk_bitvec(BigInt::from(0), 32);
    let one = exec.ctx.terms.mk_bitvec(BigInt::from(1), 32);
    let x_is_zero = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![x, zero], Sort::Bool);
    let x_is_one = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![x, one], Sort::Bool);
    exec.ctx
        .add_assertion_with_parsed(x_is_zero, parsed_placeholder());
    exec.ctx
        .add_assertion_with_parsed(x_is_one, parsed_placeholder());

    let mut proof = Proof::new();
    let old = proof.add_assume(x_is_zero, Some("legacy".to_string()));
    terminal_empty_trust(&mut proof, Some(old));
    exec.replace_with_exact_authored_bv_refutation(&mut proof);

    assert!(ay_proof::terminal_trust_report(&proof).is_trust_free());
    assert!(matches!(
        proof.steps.last(),
        Some(ProofStep::Step { rule: AletheRule::ThResolution, clause, .. })
            if clause.is_empty()
    ));
    exec.check_proof_strict_with_datatypes(&proof)
        .expect("the reconstructed exact authored BV proof must replay strictly");
}

fn add_authored_roots(exec: &mut Executor, assertions: &[TermId]) {
    for &assertion in assertions {
        exec.ctx
            .add_assertion_with_parsed(assertion, parsed_placeholder());
    }
}

#[cfg(test)]
fn assert_terminal_bv_rebuild_is_strict(exec: &mut Executor) {
    let mut proof = Proof::new();
    terminal_empty_trust(&mut proof, None);
    exec.replace_with_exact_authored_bv_refutation(&mut proof);
    assert!(
        ay_proof::terminal_trust_report(&proof).is_trust_free(),
        "the exact authored QF_BV roots must replace terminal trust"
    );
    exec.check_proof_strict_with_datatypes(&proof)
        .expect("the reconstructed authored QF_BV proof must replay strictly");
}

#[test]
fn terminal_trust_rebuilds_real_mc_join_guard_bvuge_obligation() {
    let mut exec = Executor::new();
    let terms = &mut exec.ctx.terms;
    let condition = terms.mk_var("mc_join_condition", Sort::Bool);
    let guard_else = terms.mk_var("mc_join_else", Sort::Bool);
    let guard_then = terms.mk_var("mc_join_then", Sort::Bool);
    let guard_join = terms.mk_var("mc_join_guard", Sort::Bool);
    let value = terms.mk_var("mc_join_value", Sort::bitvec(32));
    let one = terms.mk_bitvec(BigInt::from(1), 32);
    let two = terms.mk_bitvec(BigInt::from(2), 32);

    let not_condition = terms.mk_not(condition);
    let else_definition = terms.mk_eq(guard_else, not_condition);
    let then_definition = terms.mk_eq(guard_then, condition);
    let branch_join = terms.mk_or(vec![guard_else, guard_then]);
    let join_definition = terms.mk_eq(guard_join, branch_join);
    let value_is_two = terms.mk_eq(value, two);
    let value_is_one = terms.mk_eq(value, one);
    let else_value = terms.mk_implies(guard_else, value_is_two);
    let then_value = terms.mk_implies(guard_then, value_is_one);
    let lower_bound = terms.mk_app(Symbol::named("bvuge"), vec![value, one], Sort::Bool);
    let violates_lower_bound = terms.mk_not(lower_bound);
    let terminal = terms.mk_and(vec![guard_join, violates_lower_bound]);
    add_authored_roots(
        &mut exec,
        &[
            else_definition,
            then_definition,
            join_definition,
            else_value,
            then_value,
            terminal,
        ],
    );
    assert_terminal_bv_rebuild_is_strict(&mut exec);
}

#[test]
fn terminal_trust_rebuilds_real_mc_switch_default_bvule_obligation() {
    let mut exec = Executor::new();
    let terms = &mut exec.ctx.terms;
    let selector = terms.mk_var("mc_switch_selector", Sort::bitvec(32));
    let value = terms.mk_var("mc_switch_value", Sort::bitvec(32));
    let case_two = terms.mk_var("mc_switch_case_two", Sort::Bool);
    let case_one = terms.mk_var("mc_switch_case_one", Sort::Bool);
    let case_zero = terms.mk_var("mc_switch_case_zero", Sort::Bool);
    let default = terms.mk_var("mc_switch_default", Sort::Bool);
    let join = terms.mk_var("mc_switch_join", Sort::Bool);
    let zero = terms.mk_bitvec(BigInt::from(0), 32);
    let one = terms.mk_bitvec(BigInt::from(1), 32);
    let two = terms.mk_bitvec(BigInt::from(2), 32);
    let three = terms.mk_bitvec(BigInt::from(3), 32);

    let selector_is_zero = terms.mk_eq(selector, zero);
    let selector_is_one = terms.mk_eq(selector, one);
    let selector_is_two = terms.mk_eq(selector, two);
    let case_zero_definition = terms.mk_eq(case_zero, selector_is_zero);
    let case_one_definition = terms.mk_eq(case_one, selector_is_one);
    let case_two_definition = terms.mk_eq(case_two, selector_is_two);
    let selector_not_zero = terms.mk_not(selector_is_zero);
    let selector_not_one = terms.mk_not(selector_is_one);
    let selector_not_two = terms.mk_not(selector_is_two);
    let is_default = terms.mk_and(vec![selector_not_zero, selector_not_one, selector_not_two]);
    let default_definition = terms.mk_eq(default, is_default);
    let joined = terms.mk_or(vec![case_two, case_one, case_zero, default]);
    let join_definition = terms.mk_eq(join, joined);
    let value_is_three = terms.mk_eq(value, three);
    let value_is_two = terms.mk_eq(value, two);
    let value_is_one = terms.mk_eq(value, one);
    let value_is_zero = terms.mk_eq(value, zero);
    let case_two_value = terms.mk_implies(case_two, value_is_three);
    let case_one_value = terms.mk_implies(case_one, value_is_two);
    let case_zero_value = terms.mk_implies(case_zero, value_is_one);
    let default_value = terms.mk_implies(default, value_is_zero);
    let upper_bound = terms.mk_app(Symbol::named("bvule"), vec![value, three], Sort::Bool);
    let violates_upper_bound = terms.mk_not(upper_bound);
    let terminal = terms.mk_and(vec![join, violates_upper_bound]);
    add_authored_roots(
        &mut exec,
        &[
            case_two_definition,
            case_one_definition,
            case_zero_definition,
            default_definition,
            join_definition,
            case_two_value,
            case_one_value,
            case_zero_value,
            default_value,
            terminal,
        ],
    );
    assert_terminal_bv_rebuild_is_strict(&mut exec);
}

#[test]
fn terminal_trust_bv_rebuild_rejects_sat_or_non_authored_roots() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_var("mc-sat-x", Sort::bitvec(32));
    let zero = exec.ctx.terms.mk_bitvec(BigInt::from(0), 32);
    let x_is_zero = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![x, zero], Sort::Bool);
    exec.ctx
        .add_assertion_with_parsed(x_is_zero, parsed_placeholder());
    let mut proof = Proof::new();
    terminal_empty_trust(&mut proof, None);
    let original = format!("{:?}", proof.steps);
    exec.replace_with_exact_authored_bv_refutation(&mut proof);
    assert_eq!(
        format!("{:?}", proof.steps),
        original,
        "a SAT root is not a refutation"
    );

    let mut transient_only = Executor::new();
    let y = transient_only
        .ctx
        .terms
        .mk_var("transient-only-y", Sort::bitvec(32));
    let zero = transient_only.ctx.terms.mk_bitvec(BigInt::from(0), 32);
    let one = transient_only.ctx.terms.mk_bitvec(BigInt::from(1), 32);
    let y0 = transient_only
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![y, zero], Sort::Bool);
    let y1 = transient_only
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![y, one], Sort::Bool);
    transient_only.ctx.assertions.extend([y0, y1]);
    let mut transient_proof = Proof::new();
    terminal_empty_trust(&mut transient_proof, None);
    let original = format!("{:?}", transient_proof.steps);
    transient_only.replace_with_exact_authored_bv_refutation(&mut transient_proof);
    assert_eq!(format!("{:?}", transient_proof.steps), original);
}

#[test]
fn terminal_trust_bv_rebuild_enforces_authored_root_cap() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_var("mc-cap-x", Sort::bitvec(32));
    for value in 0..65_u32 {
        let constant = exec.ctx.terms.mk_bitvec(BigInt::from(value), 32);
        let assertion = exec
            .ctx
            .terms
            .mk_app(Symbol::named("="), vec![x, constant], Sort::Bool);
        exec.ctx
            .add_assertion_with_parsed(assertion, parsed_placeholder());
    }
    let mut proof = Proof::new();
    terminal_empty_trust(&mut proof, None);
    let original = format!("{:?}", proof.steps);
    exec.replace_with_exact_authored_bv_refutation(&mut proof);
    assert_eq!(format!("{:?}", proof.steps), original);
}
