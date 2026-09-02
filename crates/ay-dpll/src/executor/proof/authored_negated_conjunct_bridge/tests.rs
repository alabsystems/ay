// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Focused positive and fail-closed tests for the authored NIA bridge.

use super::direct_refutation::MAX_DIRECT_FACTS;
use super::*;

use ay_core::{AletheRule, Proof, ProofStep, TheoryLemmaKind};
use ay_frontend::{parse, Command};

const MINIMAL_NIA: &str = r#"
    (set-logic QF_NIA)
    (declare-const n Int)
    (declare-const sum Int)
    (declare-const i Int)
    (declare-const sq Int)
    (declare-const sum_next Int)
    (declare-const i_next Int)
    (declare-const sq_next Int)
    (assert (>= n 0))
    (assert (= (+ (* 2 sum) i) sq))
    (assert (= sq (* i i)))
    (assert (>= i 0))
    (assert (<= i n))
    (assert (>= sum 0))
    (assert (>= sq 0))
    (assert (<= sum sq))
    (assert (< i n))
    (assert (= sum_next (+ sum i)))
    (assert (= i_next (+ i 1)))
    (assert (= sq_next (+ sq (+ (* 2 i) 1))))
    (assert
      (not
        (and (= (+ (* 2 sum_next) i_next) sq_next)
             (= sq_next (* i_next i_next))
             (>= i_next 0)
             (<= i_next n)
             (>= sum_next 0)
             (>= sq_next 0)
             (<= sum_next sq_next))))
    (check-sat)
"#;

const STANDALONE_T21: &str = r#"
    (set-logic QF_NIA)
    (declare-const n Int)
    (declare-const sum Int)
    (declare-const i Int)
    (assert
      (or (not (<= 0 (+ i 1)))
          (not (<= (+ i 1) n))
          (not (<= 0 (+ sum i)))
          (not (<= 0 (+ (* sum 2) (* i 3) 1)))
          (not (<= (+ sum i) (+ (* sum 2) (* i 3) 1)))
          (not (= (+ (* sum 2) (* i 3) 1) (+ (* i 2) (* i i) 1)))))
"#;

fn execute_authored(script: &str, self_check: bool) -> (Executor, Vec<String>) {
    let commands = parse(script).expect("fixture must parse");
    let mut executor = Executor::new();
    executor.set_self_check(self_check);
    let output = commands
        .iter()
        .filter_map(|command| {
            executor
                .execute_authored(command)
                .expect("authored fixture must execute")
        })
        .collect();
    (executor, output)
}

fn execute_authored_with_mandatory_proof_policy(
    script: &str,
    explicit_artifact: bool,
) -> (Executor, Vec<String>) {
    let commands = parse(script).expect("fixture must parse");
    let mut executor = Executor::new();
    executor.set_self_check(true);
    if explicit_artifact {
        executor.set_produce_proofs(true);
    } else {
        executor.set_mandatory_proof_collection();
    }
    let output = commands
        .iter()
        .filter_map(|command| {
            executor
                .execute_authored(command)
                .expect("authored fixture must execute")
        })
        .collect();
    (executor, output)
}

fn execute_authored_with_script_proof_demand(script: &str) -> (Executor, Vec<String>) {
    let commands = parse(&format!("(set-option :produce-proofs true)\n{script}"))
        .expect("fixture with an in-script proof demand must parse");
    let mut executor = Executor::new();
    let output = commands
        .iter()
        .filter_map(|command| {
            executor
                .execute_authored(command)
                .expect("authored fixture with an in-script proof demand must execute")
        })
        .collect();
    (executor, output)
}

fn load_raw_authored_roots(executor: &mut Executor, script: &str) -> Vec<TermId> {
    let commands = parse(script).expect("fixture must parse");
    for command in &commands {
        if matches!(command, Command::CheckSat) {
            continue;
        }
        assert!(executor
            .execute_authored(command)
            .expect("fixture setup must execute")
            .is_none());
    }
    commands
        .iter()
        .filter_map(|command| match command {
            Command::Assert(surface) => Some(
                executor
                    .raw_intern_surface(surface)
                    .expect("binder-free authored assertion must raw-intern"),
            ),
            _ => None,
        })
        .collect()
}

fn standalone_t21_surface() -> ay_frontend::command::Term {
    parse(STANDALONE_T21)
        .expect("standalone t21 must parse")
        .into_iter()
        .find_map(|command| match command {
            Command::Assert(surface) => Some(surface),
            _ => None,
        })
        .expect("standalone t21 must contain its assertion")
}

fn plan_fixture_t21_against_retained_roots(executor: &mut Executor) -> SourcePlan {
    let raw_roots = executor.authenticated_raw_roots_for_negated_conjunct_bridge();
    let definitions = collect_definitions(&executor.ctx.terms, &raw_roots);
    let packed = executor
        .raw_intern_surface(&standalone_t21_surface())
        .expect("standalone t21 must raw-intern in the declared fixture context");
    let goals = packed_children(&executor.ctx.terms, packed).expect("t21 must be a packed or");
    let mut budget = EqBudget::new(EQ_WORK);
    executor
        .plan_negated_conjunct_fragment(packed, &goals, &raw_roots, &definitions, &mut budget)
        .map(|(_, plan)| plan)
        .expect("the exact fixture t21 must map to its retained authored root")
}

fn assert_direct_assumption_prologue(proof: &Proof) {
    let mut saw_inference = false;
    for step in &proof.steps {
        if matches!(step, ProofStep::Assume(_)) {
            assert!(
                !saw_inference,
                "direct refutation must hoist every top-level assumption"
            );
        } else {
            saw_inference = true;
        }
    }
}

fn assert_full_arity_predicate_congruence(executor: &Executor, proof: &Proof) {
    let mut congruences = 0usize;
    let mut saw_reflexive_position = false;
    for step in &proof.steps {
        let ProofStep::TheoryLemma {
            clause,
            kind: TheoryLemmaKind::EufCongruentPred,
            ..
        } = step
        else {
            continue;
        };
        congruences += 1;
        let positive = *clause.last().expect("congruence has a conclusion");
        let TermData::App(_, arguments) = executor.ctx.terms.get(positive) else {
            panic!("predicate congruence conclusion must be an application");
        };
        assert_eq!(
            clause.len() - 2,
            arguments.len(),
            "wire predicate congruence needs one equality per argument"
        );
        saw_reflexive_position |= clause[..clause.len() - 2].iter().any(|literal| {
            let TermData::Not(equality) = executor.ctx.terms.get(*literal) else {
                return false;
            };
            matches!(
                executor.ctx.terms.get(*equality),
                TermData::App(Symbol::Named(name), sides)
                    if name == "=" && sides.len() == 2 && sides[0] == sides[1]
            )
        });
    }
    assert!(
        congruences > 0,
        "fixture must exercise predicate congruence"
    );
    assert!(
        saw_reflexive_position,
        "fixture must retain the n=n argument required on the Alethe wire"
    );
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::Refl,
            ..
        }
    )));
}

fn assert_direct_farkas_uses_raw_identity_surfaces(executor: &Executor, proof: &Proof) {
    let (facts, authority) = executor
        .bounded_direct_refutation_scopes()
        .expect("fixture must retain its bounded direct authority");
    let mut expected = Vec::new();
    for &fact in &executor.last_proof_raw_original_assertions {
        if !expected.contains(&fact) {
            expected.push(fact);
        }
    }
    if let Some(assumptions) = &executor.last_assumptions {
        for &fact in assumptions {
            if !expected.contains(&fact) {
                expected.push(fact);
            }
        }
    }
    assert_eq!(
        facts, expected,
        "direct arithmetic authority must preserve authored operand orientation"
    );
    assert!(facts.iter().all(|fact| authority.contains(fact)));

    let overrides = executor.proof_export_term_overrides();
    let mut selected = 0usize;
    for step in &proof.steps {
        let ProofStep::TheoryLemma {
            clause,
            kind: TheoryLemmaKind::LraFarkas,
            ..
        } = step
        else {
            continue;
        };
        let raw_support = clause
            .iter()
            .filter_map(|literal| match executor.ctx.terms.get(*literal) {
                TermData::Not(atom) if facts.contains(atom) => Some(*atom),
                _ => None,
            })
            .count();
        if raw_support < 2 {
            continue;
        }
        selected += 1;
        assert!(ay_proof::exact_clause_surface_preserved(
            &executor.ctx.terms,
            clause,
            overrides.as_ref(),
        ));
    }
    assert!(
        selected >= 2,
        "fixture must exercise the two raw-source equality-bound certificates"
    );
}

#[test]
fn exact_model_checker_consumer_fixture_gets_a_strict_wire_clean_proof() {
    let (executor, output) = execute_authored(MINIMAL_NIA, true);
    assert_eq!(output, ["unsat"]);
    let proof = executor
        .last_proof
        .as_ref()
        .expect("self-check UNSAT must retain its checked proof");
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::NotAnd,
            ..
        }
    )));
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::ArithClauseTautology,
            ..
        }
    )));
    assert!(!proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::Trust,
            ..
        }
    )));
    let scope = executor.proof_export_scope_assertions();
    let rendered = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        proof,
        &executor.ctx.terms,
        &scope,
        executor.last_proof_term_overrides.as_ref(),
    )
    .expect("the checked proof must render under its authenticated problem surface");
    assert!(rendered.contains(":rule not_and"));
    assert!(rendered.contains(":rule poly_simp"));
    assert!(!rendered.contains(":rule hole"));
    assert!(!rendered.contains(":rule trust"));
    assert_direct_farkas_uses_raw_identity_surfaces(&executor, proof);
}

#[test]
fn exact_model_checker_consumer_fixture_certifies_with_mandatory_internal_collection() {
    let (executor, output) = execute_authored_with_mandatory_proof_policy(MINIMAL_NIA, false);
    assert_eq!(output, ["unsat"]);
    let proof = executor
        .last_proof
        .as_ref()
        .expect("mandatory collection must retain its checked proof");
    assert!(executor
        .check_proof_strict_with_datatypes(proof)
        .is_ok_and(|quality| quality.is_complete()));
    assert!(!executor.proof_has_known_wire_gap(proof));
    assert_direct_assumption_prologue(proof);
    assert_full_arity_predicate_congruence(&executor, proof);
    assert_direct_farkas_uses_raw_identity_surfaces(&executor, proof);
}

#[test]
fn exact_model_checker_consumer_fixture_certifies_with_explicit_artifact_demand() {
    let (executor, output) = execute_authored_with_mandatory_proof_policy(MINIMAL_NIA, true);
    assert_eq!(output, ["unsat"]);
    let proof = executor
        .last_proof
        .as_ref()
        .expect("explicit artifact demand must retain its checked proof");
    assert!(executor
        .check_proof_strict_with_datatypes(proof)
        .is_ok_and(|quality| quality.is_complete()));
    assert!(!executor.proof_has_known_wire_gap(proof));
    assert_direct_assumption_prologue(proof);
    assert_full_arity_predicate_congruence(&executor, proof);
    assert_direct_farkas_uses_raw_identity_surfaces(&executor, proof);
}

#[test]
fn exact_model_checker_consumer_fixture_certifies_with_script_artifact_demand_without_self_check() {
    let (executor, output) = execute_authored_with_script_proof_demand(MINIMAL_NIA);
    assert!(!executor.self_check());
    assert_eq!(output, ["unsat"]);
    let proof = executor
        .last_proof
        .as_ref()
        .expect("the SMT-LIB proof request must retain its checked proof");
    assert!(executor
        .check_proof_strict_with_datatypes(proof)
        .is_ok_and(|quality| quality.is_complete()));
    assert!(!executor.proof_has_known_wire_gap(proof));
    assert_direct_assumption_prologue(proof);
    assert_full_arity_predicate_congruence(&executor, proof);
    assert_direct_farkas_uses_raw_identity_surfaces(&executor, proof);
}

#[test]
fn native_fixture_is_committed_from_authenticated_roots() {
    let (executor, output) = execute_authored(MINIMAL_NIA, false);
    assert_eq!(output, ["unsat"]);
    let proof = executor
        .last_proof
        .as_ref()
        .expect("the standard UNSAT solve must retain its proof");
    let checked = executor.check_proof_strict_with_datatypes(proof);
    assert!(checked.is_ok_and(|quality| quality.is_complete()));
    assert!(!executor.proof_has_known_wire_gap(proof));
    let polynomial_tautologies = proof
        .steps
        .iter()
        .filter(|step| {
            matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::ArithClauseTautology,
                    ..
                }
            )
        })
        .count();
    assert!(
        polynomial_tautologies <= 16,
        "wire-clean proof emitted {polynomial_tautologies} polynomial tautologies"
    );
    let scope = executor.proof_export_scope_assertions();
    let rendered = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        proof,
        &executor.ctx.terms,
        &scope,
        executor.last_proof_term_overrides.as_ref(),
    )
    .expect("native replacement must export under the authenticated surface");
    assert!(!rendered.contains(":rule hole"));
    assert!(!rendered.contains(":rule trust"));
}

#[test]
fn direct_fallback_declines_before_cloning_an_oversized_scope() {
    let (mut executor, output) = execute_authored(MINIMAL_NIA, false);
    assert_eq!(output, ["unsat"]);
    assert!(executor.bounded_direct_refutation_scopes().is_some());

    executor.last_assumptions = Some(
        (0..=MAX_DIRECT_FACTS)
            .map(|index| {
                executor
                    .ctx
                    .terms
                    .mk_var(format!("direct_scope_cap_{index}"), ay_core::Sort::Bool)
            })
            .collect(),
    );
    assert!(executor.bounded_direct_refutation_scopes().is_none());
}

#[test]
fn direct_fallback_still_rejects_a_divergent_downstream_override() {
    let (mut executor, output) = execute_authored_with_script_proof_demand(MINIMAL_NIA);
    assert_eq!(output, ["unsat"]);
    let (facts, _) = executor
        .bounded_direct_refutation_scopes()
        .expect("fixture must retain its bounded direct authority");
    let candidate = executor
        .last_proof
        .clone()
        .expect("explicit proof demand must retain the checked direct candidate");
    assert!(executor
        .check_proof_strict_with_datatypes(&candidate)
        .is_ok_and(|quality| quality.is_complete()));

    let downstream_atom = candidate
        .steps
        .iter()
        .find_map(|step| match step {
            ProofStep::TheoryLemma {
                clause,
                kind: TheoryLemmaKind::LraFarkas,
                ..
            } => clause.last().copied().filter(|atom| !facts.contains(atom)),
            _ => None,
        })
        .expect("the direct fixture must derive a non-input Farkas conclusion");
    let mut overrides = executor
        .last_proof_term_overrides
        .clone()
        .unwrap_or_default();
    overrides.insert(downstream_atom, "false".to_string());
    executor.last_proof_term_overrides = Some(overrides);

    let raw_overrides = executor.proof_export_term_overrides();
    let effective = ay_proof::effective_wire_term_overrides_for_proof(
        &candidate,
        &executor.ctx.terms,
        raw_overrides.as_ref(),
    )
    .expect("the bounded authored-assume planner must accept the diagnostic surface")
    .expect("the divergent downstream surface must remain active");
    assert_eq!(
        effective.get(&downstream_atom).map(String::as_str),
        Some("false"),
        "a downstream override must not be confined as an authored-assume-only spelling"
    );
    assert!(
        executor.proof_has_known_wire_gap(&candidate),
        "the mandatory candidate wire screen must reject the divergent Farkas surface"
    );
}

#[test]
fn direct_source_equality_plan_fails_closed_when_its_shared_budget_is_empty() {
    let (mut executor, output) = execute_authored(MINIMAL_NIA, false);
    assert_eq!(output, ["unsat"]);
    let facts = executor
        .bounded_direct_refutation_scopes()
        .expect("fixture must retain its bounded direct authority")
        .0;
    let definitions = collect_definitions(&executor.ctx.terms, &facts);
    let plan = plan_fixture_t21_against_retained_roots(&mut executor);
    let bridge = plan
        .bridges
        .iter()
        .find(|bridge| {
            let TermData::Not(goal_atom) = executor.ctx.terms.get(bridge.goal) else {
                return false;
            };
            matches!(
                executor.ctx.terms.get(*goal_atom),
                TermData::App(symbol, _) if symbol.name() == "="
            )
        })
        .expect("fixture must retain its mapped nonlinear equality");
    let mut exhausted = EqBudget::new(0);
    assert!(
        direct_refutation::plan_direct_source_equality_unit(
            &mut executor,
            bridge,
            &definitions,
            &mut exhausted,
        )
        .is_none(),
        "an exhausted shared equality budget must decline without emitting a proof"
    );
}

#[test]
fn a_mutated_update_is_not_certified_unsat() {
    let mutated = MINIMAL_NIA.replace("(+ sq (+ (* 2 i) 1))", "(+ sq (+ (* 3 i) 1))");
    assert_ne!(mutated, MINIMAL_NIA);
    let (_executor, output) = execute_authored(&mutated, true);
    assert_eq!(output, ["sat"]);
}

#[test]
fn a_mutated_definition_cannot_plan_the_t21_bridge() {
    let mutated = MINIMAL_NIA.replace("(+ sq (+ (* 2 i) 1))", "(+ sq (+ (* 3 i) 1))");
    let mut executor = Executor::new();
    let raw_roots = load_raw_authored_roots(&mut executor, &mutated);
    let definitions = collect_definitions(&executor.ctx.terms, &raw_roots);
    let packed = executor
        .raw_intern_surface(&standalone_t21_surface())
        .expect("standalone t21 must raw-intern in the declared fixture context");
    let goals = packed_children(&executor.ctx.terms, packed).expect("t21 must be a packed or");

    let mut budget = EqBudget::new(EQ_WORK);
    assert!(
        executor
            .plan_negated_conjunct_fragment(packed, &goals, &raw_roots, &definitions, &mut budget,)
            .is_none(),
        "coefficient 3 destroys the required authored polynomial identities"
    );
}

#[test]
fn exact_authored_definitions_plan_the_fixture_t21_bridge() {
    let mut executor = Executor::new();
    let raw_roots = load_raw_authored_roots(&mut executor, MINIMAL_NIA);
    let definitions = collect_definitions(&executor.ctx.terms, &raw_roots);
    let packed = executor
        .raw_intern_surface(&standalone_t21_surface())
        .expect("standalone t21 must raw-intern in the declared fixture context");
    let goals = packed_children(&executor.ctx.terms, packed).expect("t21 must be a packed or");
    let (root, conjuncts) = raw_roots
        .iter()
        .find_map(|&root| {
            raw_negated_conjuncts(&executor.ctx.terms, root).map(|terms| (root, terms))
        })
        .expect("fixture must retain its exact raw not-and source");
    for (goal_index, source_index) in [(0, 2), (1, 3), (2, 4), (3, 5), (4, 6), (5, 0)] {
        let mut pair_budget = EqBudget::new(EQ_WORK);
        assert!(
            executor
                .plan_literal_bridge(
                    source_index,
                    conjuncts[source_index],
                    goals[goal_index],
                    &definitions,
                    &mut pair_budget,
                )
                .is_some(),
            "source conjunct {source_index} must bridge target disjunct {goal_index}"
        );
    }
    let omitted = decode_relation(&executor.ctx.terms, conjuncts[1])
        .expect("the omitted source conjunct must be an equality");
    let mut omitted_budget = EqBudget::new(EQ_WORK);
    assert!(
        plan_numeric_equality(
            &mut executor.ctx.terms,
            omitted.semantic_args[0],
            omitted.semantic_args[1],
            &definitions,
            &mut omitted_budget,
        )
        .is_some(),
        "the second source equality must follow from the authored definitions"
    );
    let mut budget = EqBudget::new(EQ_WORK);
    let plan = executor
        .plan_source_mapping(root, &conjuncts, &goals, &definitions, &mut budget)
        .expect("the exact source/goal relation mapping must plan");
    let step_upper_bound = plan
        .fragment_step_upper_bound(goals.len())
        .expect("fixture step upper bound must fit usize");
    assert!(emitted_steps_admitted(
        Some(step_upper_bound),
        MAX_FRAGMENT_STEPS
    ));
    let attempts_used = MAX_POLY_ATTEMPTS - budget.remaining_poly_attempts();
    assert!(
        attempts_used <= 16,
        "fixture source mapping used {attempts_used} polynomial attempts"
    );
    let derivation = executor
        .emit_source_plan(&plan, packed, &goals)
        .expect("the planned exact bridge must emit and repack");
    assert!(derivation.steps.len() <= step_upper_bound);
    let closed = ay_proof::close_congruence_derivation(&mut executor.ctx.terms, &derivation);
    let checked = ay_proof::check_proof_strict(&closed, &executor.ctx.terms);
    assert!(checked.is_ok(), "closed bridge must replay: {checked:?}");
}

#[test]
fn fragment_step_upper_bound_admission_is_exact() {
    assert!(emitted_steps_admitted(
        Some(MAX_FRAGMENT_STEPS),
        MAX_FRAGMENT_STEPS
    ));
    assert!(!emitted_steps_admitted(
        MAX_FRAGMENT_STEPS.checked_add(1),
        MAX_FRAGMENT_STEPS
    ));
    assert!(!emitted_steps_admitted(None, MAX_FRAGMENT_STEPS));
}

#[test]
fn standalone_non_tautological_t21_stays_rejected() {
    let (mut executor, output) = execute_authored(STANDALONE_T21, false);
    assert!(output.is_empty());
    assert!(executor.last_proof_raw_original_assertions.is_empty());
    let packed = *executor
        .ctx
        .assertions
        .last()
        .expect("the standalone packed-or assertion must be retained");
    assert!(packed_children(&executor.ctx.terms, packed).is_some());
    let mut proof = Proof::new();
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![packed],
        premises: Vec::new(),
        args: Vec::new(),
    });
    let original = format!("{:?}", proof.steps);

    executor.replace_with_exact_authored_negated_conjunct_bridge(&mut proof);

    assert_eq!(format!("{:?}", proof.steps), original);
    assert!(ay_proof::check_proof_strict(&proof, &executor.ctx.terms).is_err());
}

#[test]
fn missing_raw_route_declines_before_publication_walk() {
    let mut executor = Executor::new();
    let mut proof = Proof::new();
    let checks_before = executor.strict_check_invocations.get();

    executor.replace_with_exact_authored_negated_conjunct_bridge(&mut proof);

    assert_eq!(executor.strict_check_invocations.get(), checks_before);
    assert!(proof.steps.is_empty());
}

#[test]
fn oversized_provisional_proof_is_left_untouched() {
    let mut executor = Executor::new();
    let mut proof = Proof::new();
    for _ in 0..=MAX_INPUT_PROOF_STEPS {
        proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    }
    let original_len = proof.steps.len();

    executor.replace_with_exact_authored_negated_conjunct_bridge(&mut proof);

    assert_eq!(proof.steps.len(), original_len);
    assert!(proof.steps.iter().all(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::Trust,
            ..
        }
    )));
}
