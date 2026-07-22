// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression test: 022c-horn_000 (eldarica-misc/LIA/reve) is UNSAT, but the
//! adaptive portfolio answered SAT in ~0.1s with an all-`true` certificate.
//!
//! Root cause: `build_query_safety_candidate` negated the full query
//! constraint, including conjuncts over clause-local variables that are NOT
//! predicate arguments (`(= G H)`, `(= I J)`). The synthesized
//! `INV1 := ¬(... ∧ (= G H) ∧ (= I J))` therefore had FREE variables. During
//! model validation, substitution into each clause CAPTURED same-named
//! clause variables; clause constraints like `(>= (- G H) 1)` contradicted
//! the captured conjuncts, making every consecution check vacuously UNSAT.
//! The malformed model "passed" full validation and was printed as all-`true`
//! after output sanitization dropped the free-variable formula.
//!
//! Fixes under test:
//! 1. `build_query_safety_candidate` keeps only constraint conjuncts closed
//!    over the predicate arguments (candidate has no free variables).
//! 2. `verify_model` rejects any model whose interpretation mentions free
//!    (non-binder) variables — capture makes its clause checks vacuous.
//! 3. `accept_synthesized_invariant` no longer accepts models on structural
//!    shape checks alone; all acceptance routes through full validation.

use ay_chc::{
    AdaptiveConfig, AdaptivePortfolio, ChcExpr, ChcParser, ChcSort, ChcVar, InvariantModel,
    PdrConfig, PredicateInterpretation, SmtContext, SmtResult,
};
use ntest::timeout;
use std::time::Duration;

const REVE_022C_HORN: &str = include_str!("../fixtures/chc_comp/reve/022c-horn_000.smt2");

/// 022c-horn_000 is UNSAT (golem-confirmed). The solver must never answer
/// sat; unknown or unsat are both acceptable.
#[test]
#[timeout(120000)]
fn test_022c_horn_must_not_answer_sat() {
    let problem = ChcParser::parse(REVE_022C_HORN).expect("parse 022c-horn_000");
    problem.validate().expect("validate 022c-horn_000");

    let config = AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(5));
    let solver = AdaptivePortfolio::new(problem, config);
    let result = solver.solve();

    assert!(
        !result.is_safe(),
        "022c-horn_000 is UNSAT (ground truth); answering sat is a soundness bug. Got: {result:?}",
    );
}

/// `verify_model` must reject ill-formed models whose interpretations mention
/// free variables: substitution into clauses captures same-named clause
/// variables and turns the checks into vacuous UNSAT queries.
#[test]
#[timeout(60000)]
fn test_verify_model_rejects_free_variable_interpretation() {
    let problem = ChcParser::parse(REVE_022C_HORN).expect("parse 022c-horn_000");

    // Reconstruct the malformed pre-fix model: INV1 := ¬(query constraint)
    // with free G/H/I/J, everything else `true`.
    let mut model = InvariantModel::new();
    for pred in problem.predicates() {
        let vars: Vec<ChcVar> = pred
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(i, sort)| ChcVar::new(format!("__p{}_a{}", pred.id.index(), i), sort.clone()))
            .collect();
        let formula = if pred.name == "INV1" {
            // ¬( (= G H) ∧ ¬(= a1 a4) ∧ ¬(≥ a3-a5 1) ∧ ¬(≥ a0-a2 1) ∧ (= I J) )
            // G, H, I, J are FREE — not among the binder vars.
            let fv = |n: &str| ChcExpr::var(ChcVar::new(n.to_string(), ChcSort::Int));
            let av = |i: usize| ChcExpr::var(vars[i].clone());
            ChcExpr::not(ChcExpr::and_vec(vec![
                ChcExpr::eq(fv("G"), fv("H")),
                ChcExpr::not(ChcExpr::eq(av(1), av(4))),
                ChcExpr::not(ChcExpr::ge(ChcExpr::sub(av(3), av(5)), ChcExpr::int(1))),
                ChcExpr::not(ChcExpr::ge(ChcExpr::sub(av(0), av(2)), ChcExpr::int(1))),
                ChcExpr::eq(fv("I"), fv("J")),
            ]))
        } else {
            ChcExpr::bool_const(true)
        };
        model.set(pred.id, PredicateInterpretation::new(vars, formula));
    }

    let mut verifier = ay_chc::testing::new_pdr_solver(problem, PdrConfig::default());
    assert!(
        !verifier.verify_model(&model),
        "verify_model must reject interpretations with free variables \
         (capture makes clause checks vacuous)",
    );
}

/// The query-clause body of 022c-horn_000 under the all-`true` model is
/// trivially SAT (pick G=H, I=J, E<=F, C<=D, A!=B). The DPLL(T) theory loop
/// previously returned a false UNSAT with core `[A != B]`: when the extracted
/// theory model disagreed with the SAT-assigned value of `(= A B)`, the
/// "violated constraint" repair added a UNIT clause permanently forcing
/// `(= A B)` true, contradicting the assumption pinning it false.
#[test]
#[timeout(60000)]
fn test_smt_query_body_with_diseq_is_sat() {
    let iv = |n: &str| ChcExpr::var(ChcVar::new(n.to_string(), ChcSort::Int));
    // (and (= G H) (not (= A B)) (not (>= (+ E (* -1 F)) 1))
    //      (not (>= (+ C (* -1 D)) 1)) (= I J))
    let body = ChcExpr::and_vec(vec![
        ChcExpr::eq(iv("G"), iv("H")),
        ChcExpr::not(ChcExpr::eq(iv("A"), iv("B"))),
        ChcExpr::not(ChcExpr::ge(
            ChcExpr::add(iv("E"), ChcExpr::mul(ChcExpr::int(-1), iv("F"))),
            ChcExpr::int(1),
        )),
        ChcExpr::not(ChcExpr::ge(
            ChcExpr::add(iv("C"), ChcExpr::mul(ChcExpr::int(-1), iv("D"))),
            ChcExpr::int(1),
        )),
        ChcExpr::eq(iv("I"), iv("J")),
    ]);

    let mut smt = SmtContext::new();
    let result = smt.check_sat_with_timeout(&body, Duration::from_secs(5));
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "query body is trivially SAT, got {result:?}"
    );
}
