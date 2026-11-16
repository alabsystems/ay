// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::tests::{conditional_source, parsed, reachable_steps, scope, CONDITIONAL_OR};
use super::*;
use crate::api::{Logic, Solver};
use ay_core::ProofStep;

#[path = "tests/resources.rs"]
mod resources;

fn assert_conditional_bundle(source: &str, expected_assumes: usize) {
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_proofs(true);
    solver.parse_smtlib2(source).unwrap();
    assert!(
        solver.check_sat().is_unsat(),
        "{:?}",
        solver.unknown_reason()
    );
    assert!(solver
        .last_strict_proof_quality()
        .unwrap()
        .unwrap()
        .is_complete());
    let bundle = solver.export_last_unsat_bundle().unwrap();
    let encoded = serde_json::to_vec(&bundle).unwrap();
    let restored: ay_proof::SerializableProofBundle = serde_json::from_slice(&encoded).unwrap();
    assert!(ay_proof::re_check_bundle_strict(&restored)
        .unwrap()
        .quality
        .is_complete());
    let proof = Proof::from_steps(restored.steps.clone());
    let reachable = reachable_steps(&proof);
    let mut assumes: Vec<_> = proof
        .steps
        .iter()
        .enumerate()
        .filter_map(|(index, step)| match step {
            ProofStep::Assume(term) if reachable[index] => Some(*term),
            _ => None,
        })
        .collect();
    assumes.sort_unstable();
    assumes.dedup();
    assert_eq!(assumes.len(), expected_assumes);
    assert!(assumes
        .iter()
        .all(|term| restored.obligation_assertions.contains(term)));
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::Or,
            ..
        }
    )));
    // A reachable derived unit is evidence, not an authored premise. Replacing
    // its derivation with an Assume must fail even though the clause is unchanged.
    let (index, unit) = proof
        .steps
        .iter()
        .enumerate()
        .find_map(|(index, step)| match step {
            ProofStep::Resolution { clause, .. }
                if reachable[index]
                    && clause.len() == 1
                    && !restored.obligation_assertions.contains(&clause[0]) =>
            {
                Some((index, clause[0]))
            }
            _ => None,
        })
        .expect("a genuinely derived reachable unit");
    let mut forged = restored.clone();
    forged.steps[index] = ProofStep::Assume(unit);
    assert!(ay_proof::re_check_bundle_strict(&forged).is_err());
    let forged_proof = Proof::from_steps(forged.steps);
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(
        &forged_proof,
        &restored.obligation_assertions,
    )
    .is_err());
}

#[test]
fn conditional_fp_check10_native_bundle_retains_four_authored_premises() {
    for equality in ["(= x63 x64)", "(= x64 x63)"] {
        assert_conditional_bundle(
            &conditional_source(&[
                CONDITIONAL_OR[0],
                CONDITIONAL_OR[1],
                equality,
                "(not condition)",
            ]),
            4,
        );
    }
}

#[test]
fn conditional_fp_check12_native_bundle_retains_five_authored_premises() {
    for equality in ["(= x63 x64)", "(= x64 x63)"] {
        assert_conditional_bundle(
            &conditional_source(&[
                CONDITIONAL_OR[0],
                CONDITIONAL_OR[1],
                CONDITIONAL_OR[2],
                CONDITIONAL_OR[3],
                equality,
            ]),
            5,
        );
    }
}

#[test]
fn conditional_nan_equalities_retain_five_and_six_authored_roots() {
    assert_conditional_bundle(
        &conditional_source(&[
            CONDITIONAL_OR[0],
            CONDITIONAL_OR[1],
            "(not condition)",
            "(fp.isNaN x63)",
            "(fp.isNaN x64)",
        ]),
        5,
    );
    assert_conditional_bundle(
        &conditional_source(&[
            CONDITIONAL_OR[0],
            CONDITIONAL_OR[1],
            CONDITIONAL_OR[2],
            CONDITIONAL_OR[3],
            "(fp.isNaN x63)",
            "(fp.isNaN x64)",
        ]),
        6,
    );
}

#[test]
fn conditional_nan_equalities_share_the_existing_work_and_commit_allowance() {
    for clauses in [
        vec![
            CONDITIONAL_OR[0],
            CONDITIONAL_OR[1],
            "(not condition)",
            "(fp.isNaN x63)",
            "(fp.isNaN x64)",
        ],
        vec![
            CONDITIONAL_OR[0],
            CONDITIONAL_OR[1],
            CONDITIONAL_OR[2],
            CONDITIONAL_OR[3],
            "(fp.isNaN x63)",
            "(fp.isNaN x64)",
        ],
    ] {
        let source = conditional_source(&clauses);
        let (outcome, _, measured) = with_budget(&source, MAX_WORK, 0);
        assert_eq!(outcome, Outcome::Committed);
        let used = MAX_WORK - measured.work;
        assert!(
            used > 0 && used < MAX_WORK,
            "metered NaN composition cost {used}"
        );
        assert_eq!(with_budget(&source, used, 0).0, Outcome::Committed);
        assert_eq!(with_budget(&source, used - 1, 0).0, Outcome::Declined);
        assert_eq!(
            with_budget(&source, MAX_WORK, MAX_COMMIT_ATTEMPTS).0,
            Outcome::Declined
        );
    }
}

#[test]
fn conditional_fp_missing_each_critical_premise_is_validated_sat() {
    let activated = [
        CONDITIONAL_OR[0],
        CONDITIONAL_OR[1],
        "(= x63 x64)",
        "(not condition)",
    ];
    let both = [
        CONDITIONAL_OR[0],
        CONDITIONAL_OR[1],
        CONDITIONAL_OR[2],
        CONDITIONAL_OR[3],
        "(= x63 x64)",
    ];
    for clauses in [activated.as_slice(), both.as_slice()] {
        for omitted in 0..clauses.len() {
            let remaining: Vec<_> = clauses
                .iter()
                .enumerate()
                .filter_map(|(index, &clause)| (index != omitted).then_some(clause))
                .collect();
            let mut solver = Solver::new(Logic::All);
            solver.set_produce_proofs(true);
            solver
                .parse_smtlib2(&conditional_source(&remaining))
                .unwrap();
            let details = solver.check_sat_with_details();
            assert!(details.result.is_sat(), "omit {omitted}: {details:?}");
            assert!(details.verification.sat_model_validated);
            assert!(solver.export_last_unsat_bundle().is_none());
        }
    }
}

#[test]
fn conditional_fp_native_scope_pop_restores_validated_sat() {
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(&conditional_source(&[
            CONDITIONAL_OR[0],
            CONDITIONAL_OR[1],
            "(= x63 x64)",
        ]))
        .unwrap();
    let details = solver.check_sat_with_details();
    assert!(details.result.is_sat(), "{details:?}");
    assert!(details.verification.sat_model_validated);
    solver.push();
    solver.parse_smtlib2("(assert (not condition))").unwrap();
    assert!(solver.check_sat().is_unsat());
    let bundle = solver.export_last_unsat_bundle().unwrap();
    assert!(ay_proof::re_check_bundle_strict(&bundle)
        .unwrap()
        .quality
        .is_complete());
    solver.pop();
    let details = solver.check_sat_with_details();
    assert!(details.result.is_sat(), "{details:?}");
    assert!(details.verification.sat_model_validated);
    assert!(solver.export_last_unsat_bundle().is_none());
}

fn activated() -> String {
    conditional_source(&[
        CONDITIONAL_OR[0],
        CONDITIONAL_OR[1],
        "(= x63 x64)",
        "(not condition)",
    ])
}

fn both_branches() -> String {
    conditional_source(&[
        CONDITIONAL_OR[0],
        CONDITIONAL_OR[1],
        CONDITIONAL_OR[2],
        CONDITIONAL_OR[3],
        "(= x63 x64)",
    ])
}

fn with_budget(source: &str, work: usize, checks: usize) -> (Outcome, Proof, Attempt) {
    let mut executor = parsed(source);
    let (roots, equalities) = scope(&executor);
    let mut proof = Proof::new();
    proof.add_assume(roots[0], None);
    let before = proof.steps.clone();
    let mut attempt = Attempt { work, checks };
    let outcome =
        executor.try_authored_predicate_with_attempt(&mut proof, &roots, &equalities, &mut attempt);
    if outcome == Outcome::Committed {
        assert!(executor
            .check_proof_strict_with_datatypes(&proof)
            .unwrap()
            .is_complete());
        ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &roots).unwrap();
    } else {
        assert_eq!(
            proof.steps, before,
            "a partial candidate cannot replace the caller's proof"
        );
    }
    (outcome, proof, attempt)
}

#[test]
fn conditional_pool_skips_unrelated_units_and_unsupported_or_roots() {
    let mut executor = parsed(&both_branches());
    let (mut roots, equalities) = scope(&executor);
    let condition = executor.ctx.symbol_info("condition").unwrap().term.unwrap();
    let not_condition = executor.ctx.terms.mk_not_raw(condition);
    let double_not = executor.ctx.terms.mk_not_raw(not_condition);
    let x63 = executor.ctx.symbol_info("x63").unwrap().term.unwrap();
    let p = executor
        .ctx
        .terms
        .mk_app(Symbol::named("g"), [x63], Sort::Bool);
    let or = Symbol::named("or");
    let duplicate = executor
        .ctx
        .terms
        .mk_app(or.clone(), [condition, condition], Sort::Bool);
    let tautology = executor
        .ctx
        .terms
        .mk_app(or.clone(), [condition, not_condition], Sort::Bool);
    let nested_not = executor
        .ctx
        .terms
        .mk_app(or.clone(), [double_not, p], Sort::Bool);
    let ternary = executor
        .ctx
        .terms
        .mk_app(or.clone(), [condition, not_condition, p], Sort::Bool);
    let nested_or = executor.ctx.terms.mk_app(or, [duplicate, p], Sort::Bool);
    roots.extend([duplicate, tautology, nested_not, ternary, nested_or]);
    let inputs = Inputs::collect(&mut executor, &roots, &mut Attempt::new()).unwrap();
    assert_eq!(inputs.clauses.len(), 4);
    assert_eq!(inputs.atoms.len(), 3);
    assert!(inputs.atoms.contains(&condition));
    let x0 = executor.ctx.symbol_info("x0").unwrap().term.unwrap();
    let unrelated = executor
        .ctx
        .terms
        .mk_app(Symbol::named("g"), [x0], Sort::Bool);
    assert!(!inputs.atoms.contains(&unrelated));
    // The additional roots are not even admitted source premises. Skipping
    // them is harmless: the actual supported subset still proves the result.
    let mut proof = Proof::new();
    assert_eq!(
        executor.try_authored_predicate_with_attempt(
            &mut proof,
            &roots,
            &equalities,
            &mut Attempt::new(),
        ),
        Outcome::Committed
    );
    ay_proof::validate_reachable_assumes_in_problem_scope(
        &proof,
        &executor.exact_concrete_authored_scope(),
    )
    .unwrap();
}

#[test]
fn conditional_or_steps_keep_exact_children_and_actual_premise_ids() {
    let mut executor = parsed(&both_branches());
    let (roots, equalities) = scope(&executor);
    let mut proof = Proof::new();
    assert_eq!(
        executor.try_authored_predicate_with_attempt(
            &mut proof,
            &roots,
            &equalities,
            &mut Attempt::new(),
        ),
        Outcome::Committed
    );
    let reachable = reachable_steps(&proof);
    let index = proof
        .steps
        .iter()
        .enumerate()
        .find_map(|(index, step)| {
            matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::Or,
                    ..
                }
            )
            .then_some(index)
            .filter(|index| reachable[*index])
        })
        .unwrap();
    let ProofStep::Step {
        clause, premises, ..
    } = &proof.steps[index]
    else {
        panic!()
    };
    assert_eq!(premises.len(), 1);
    let ProofStep::Assume(root) = proof.steps[premises[0].0 as usize] else {
        panic!()
    };
    let TermData::App(Symbol::Named(name), children) = executor.ctx.terms.get(root) else {
        panic!()
    };
    assert_eq!(name, "or");
    assert_eq!(clause, children);
    let mut missing = Proof::from_steps(proof.steps.clone());
    let ProofStep::Step { clause, .. } = &mut missing.steps[index] else {
        panic!()
    };
    clause.pop();
    assert!(executor
        .check_proof_strict_with_datatypes(&missing)
        .is_err());
    let mut no_premise = Proof::from_steps(proof.steps.clone());
    let ProofStep::Step { premises, .. } = &mut no_premise.steps[index] else {
        panic!()
    };
    premises.clear();
    assert!(executor
        .check_proof_strict_with_datatypes(&no_premise)
        .is_err());
}

#[test]
fn conditional_refuses_ieee_wrong_endpoint_and_missing_equality_support() {
    for support in ["(fp.eq x63 x64)", "(= x0 x64)", "(fp.isNaN x63)"] {
        let source = conditional_source(&[
            CONDITIONAL_OR[0],
            CONDITIONAL_OR[1],
            CONDITIONAL_OR[2],
            CONDITIONAL_OR[3],
            support,
        ]);
        assert_eq!(
            with_budget(&source, MAX_WORK, 0).0,
            Outcome::Declined,
            "{support}"
        );
    }
}

#[test]
fn conditional_foreign_equality_and_popped_sources_do_not_grant_authority() {
    let source = conditional_source(&[
        CONDITIONAL_OR[0],
        CONDITIONAL_OR[1],
        CONDITIONAL_OR[2],
        CONDITIONAL_OR[3],
    ]);
    let mut executor = parsed(&source);
    let (mut roots, _) = scope(&executor);
    let x = executor.ctx.symbol_info("x63").unwrap().term.unwrap();
    let y = executor.ctx.symbol_info("x64").unwrap().term.unwrap();
    let equality = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), [x, y], Sort::Bool);
    roots.push(equality);
    let mut proof = Proof::new();
    assert_eq!(
        executor.try_authored_predicate_with_attempt(
            &mut proof,
            &roots,
            &[(equality, x, y)],
            &mut Attempt::new(),
        ),
        Outcome::Declined
    );
    assert_eq!(proof.steps, [] as [ProofStep; 0]);

    let source = both_branches().replacen("(set-logic ALL)", "(set-logic ALL) (push 1)", 1);
    let mut executor = parsed(&source);
    let (roots, equalities) = scope(&executor);
    executor
        .execute_all(&ay_frontend::parse("(pop 1)").unwrap())
        .unwrap();
    assert_eq!(
        executor.try_authored_predicate_with_attempt(
            &mut proof,
            &roots,
            &equalities,
            &mut Attempt::new(),
        ),
        Outcome::Declined
    );
    assert_eq!(proof.steps, [] as [ProofStep; 0]);
}
