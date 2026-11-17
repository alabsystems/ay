// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A checked Horn answer concerns this explicit raw-operation contract, not Rust replay.
use super::*;
use crate::invoke::{solve_with_proof, EncodeConfig, ProofMode};
use ay_chc::VerifiedChcResult;

fn problem(width: u32, budget: &mut WorkBudget<'_>) -> ChcProblem {
    budget.admit(FIXTURE, FIXTURE).unwrap();
    let (_, infinity, quiet, _) = layout(width);
    let zero = Expr::bitvec_const(0u8, width);
    let inputs = [&zero, &zero];
    let (output, target) = raw("original_ssa_word", width);
    let results = [FpRawResultRelation {
        operation: FpRawOperation::Arithmetic {
            operation: RustFpArithmetic::Divide,
            inputs: &inputs,
            nan_policy: RustNanPolicy::NoExtra,
        },
        output: &output,
    }];
    let bindings = [FpExprInputBinding {
        source: &output,
        target: &target,
    }];
    let mut namespace = ChcProblem::new();
    let p = namespace.declare_predicate("raw_result_state", vec![ChcSort::BitVec(width)]);
    let q = namespace.declare_predicate("later_raw_observation", vec![ChcSort::BitVec(width)]);
    let body = {
        let (body, source) =
            lower_fp_raw_result_clause(&[], &results, &bindings, &namespace, budget)
                .unwrap()
                .into_body(ClauseBody::empty())
                .unwrap()
                .into_parts()
                .unwrap();
        assert!(std::ptr::eq(source.namespace(), &raw const namespace));
        assert!(std::ptr::eq(
            source.raw_results()[0].output,
            &raw const output
        ));
        body
    };
    namespace.add_clause(HornClause::new(
        body,
        ClauseHead::Predicate(p, vec![ChcExpr::Var(target.clone())]),
    ));
    // The next rule carries the SAME raw word. Re-running a relation or using a
    // new body-local NaN choice here would not model a stored SSA observation.
    namespace.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::Var(target.clone())])], None),
        ClauseHead::Predicate(q, vec![ChcExpr::Var(target.clone())]),
    ));
    namespace.add_clause(HornClause::query(ClauseBody::new(
        vec![(q, vec![ChcExpr::Var(target.clone())])],
        Some(negate(pin(&target, infinity | quiet, width))),
    )));
    namespace.validate().unwrap();
    assert_eq!(namespace.clauses().len(), 3);
    assert!(!namespace.has_stripped_body_forall());
    budget.charge(0).unwrap();
    namespace
}

#[test]
fn horn_heads_and_later_rules_keep_all_permitted_raw_words_not_a_favorable_choice() {
    original_owner(|budget, end| {
        for width in [32, 64] {
            let problem = problem(width, budget);
            budget.admit(FIXTURE, FIXTURE).unwrap();
            let input_hash = crate::normalized_chc_input_sha256(&problem);
            let remaining = end.saturating_duration_since(Instant::now());
            assert!(!remaining.is_zero());
            let config = EncodeConfig::new()
                .with_proof_mode(ProofMode::Strict)
                .with_memory_budget(128 * 1024 * 1024)
                .with_timeout(remaining);
            // original_owner keeps the immutable absolute end in CheckStop.
            // Relative child timeout cannot extend that observer.
            let run = solve_with_proof(problem, &config).unwrap();
            let VerifiedChcResult::Unsafe(counterexample) = run.result() else {
                panic!("both signs of the permitted preferred NaN must remain reachable");
            };
            assert!(!counterexample.counterexample().steps.is_empty());
            let certificate = run.certificate();
            assert_eq!(certificate.result(), "unsafe");
            assert_eq!(certificate.normalized_input_sha256(), input_hash);
            // Even this native proof-grade result authenticates only this
            // relation problem, NOT an original Rust harness or payload replay.
            drop(certificate);
            drop(run);
            drop(config);
            drop(input_hash);
            budget.charge(0).unwrap();
        }
    });
}
