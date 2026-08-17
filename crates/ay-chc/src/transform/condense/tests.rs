// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tests for the unified fixpoint condense superpass.

use super::*;
use crate::parser::ChcParser;
use crate::pdr::{PdrConfig, PdrResult, PdrSolver};
use crate::portfolio::{EngineConfig, PortfolioConfig, PortfolioResult, PortfolioSolver};
use crate::transform::TransformationPipeline;
use crate::{ChcExpr, PredicateInterpretation};

fn parse(smt: &str) -> ChcProblem {
    ChcParser::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"))
}

fn condense(problem: ChcProblem) -> TransformationResult {
    TransformationPipeline::new()
        .with(CondenseSuperpass::new())
        .transform(problem)
}

fn bounded_pdr_config() -> PdrConfig {
    PdrConfig {
        solve_timeout: Some(std::time::Duration::from_mins(1)),
        ..PdrConfig::default()
    }
}

fn solve_with_pdr(problem: ChcProblem) -> PortfolioResult {
    let config = PortfolioConfig::with_engines(vec![EngineConfig::Pdr(PdrConfig::default())])
        .parallel(false);
    PortfolioSolver::new(problem, config).solve()
}

/// 6-predicate copy chain (crank-style `h_i => h_{i+1}` edges) feeding a
/// self-loop: condense must collapse the chain and the back-translated Safe
/// model must verify on the ORIGINAL clauses (G1).
#[test]
fn condense_collapses_copy_chain_and_backtranslates_model() {
    let mut input = String::from("(set-logic HORN)\n");
    for i in 0..6 {
        input.push_str(&format!("(declare-fun h{i} (Int Int) Bool)\n"));
    }
    input.push_str("(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 0)) (h0 x y))))\n");
    for i in 0..5 {
        input.push_str(&format!(
            "(assert (forall ((x Int) (y Int)) (=> (h{i} x y) (h{} x y))))\n",
            i + 1
        ));
    }
    input.push_str(
        "(assert (forall ((x Int) (y Int) (x2 Int))
            (=> (and (h5 x y) (< x 10) (= x2 (+ x 1))) (h5 x2 y))))\n",
    );
    input.push_str("(assert (forall ((x Int) (y Int)) (=> (and (h5 x y) (< x 0)) false)))\n");
    input.push_str("(check-sat)\n");
    let problem = parse(&input);
    let result = condense(problem.clone());

    assert!(
        result.problem.predicates().len() <= 2,
        "copy chain must collapse: {} -> {} predicates",
        problem.predicates().len(),
        result.problem.predicates().len()
    );

    let mut solver = PdrSolver::new(result.problem.clone(), bounded_pdr_config());
    match solver.solve() {
        PdrResult::Safe(model) => {
            let translated = result.back_translator.translate_validity(model);
            let mut verifier = PdrSolver::new(problem, bounded_pdr_config());
            assert!(
                verifier.verify_model(&translated),
                "back-translated model must verify on the original chain clauses"
            );
        }
        other => panic!("expected Safe on condensed chain, got {other:?}"),
    }
}

/// Same chain with a reachable bad state: the condensed problem must stay
/// Unsafe (no sat<->unsat flip).
#[test]
fn condense_preserves_unsat_on_copy_chain() {
    let mut input = String::from("(set-logic HORN)\n");
    for i in 0..6 {
        input.push_str(&format!("(declare-fun h{i} (Int) Bool)\n"));
    }
    input.push_str("(assert (forall ((x Int)) (=> (= x 0) (h0 x))))\n");
    for i in 0..5 {
        input.push_str(&format!(
            "(assert (forall ((x Int)) (=> (h{i} x) (h{} x))))\n",
            i + 1
        ));
    }
    input.push_str(
        "(assert (forall ((x Int) (y Int)) (=> (and (h5 x) (< x 10) (= y (+ x 1))) (h5 y))))\n",
    );
    input.push_str("(assert (forall ((x Int)) (=> (and (h5 x) (> x 5)) false)))\n");
    input.push_str("(check-sat)\n");
    let problem = parse(&input);
    let result = condense(problem);

    match solve_with_pdr(result.problem) {
        PortfolioResult::Unsafe(_) => {}
        other => panic!("expected Unsafe on condensed chain, got {other:?}"),
    }
}

/// Backward-irrelevant island: `Iso` never reaches the query, so its clauses
/// are removed. The back-translated model must interpret `Iso` as `true`
/// (its fact clause `x = 1 => Iso(x)` must still hold). A naive translator
/// interpreting removed predicates as `false` fails verification — this pins
/// the polarity soundness detail.
#[test]
fn reachability_island_removed_with_true_interpretation() {
    let input = r#"
(set-logic HORN)
(declare-fun Loop (Int) Bool)
(declare-fun Iso (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Loop x))))
(assert (forall ((x Int) (y Int))
    (=> (and (Loop x) (< x 10) (= y (+ x 1))) (Loop y))))
(assert (forall ((x Int)) (=> (= x 1) (Iso x))))
(assert (forall ((x Int)) (=> (and (Loop x) (< x 0)) false)))
(check-sat)
"#;
    let problem = parse(input);
    let result = TransformationPipeline::new()
        .with(UnreachableClauseEliminator::new())
        .transform(problem.clone());

    let iso = problem.lookup_predicate("Iso").unwrap();
    assert!(
        !result
            .problem
            .clauses()
            .iter()
            .any(|c| c.head.predicate_id() == Some(iso)),
        "Iso's defining clause must be pruned as backward-irrelevant"
    );

    let mut solver = PdrSolver::new(result.problem.clone(), bounded_pdr_config());
    match solver.solve() {
        PdrResult::Safe(model) => {
            let translated = result.back_translator.translate_validity(model);
            let mut verifier = PdrSolver::new(problem.clone(), bounded_pdr_config());
            assert!(
                verifier.verify_model(&translated),
                "back-translated model (Iso := true) must verify on the original clauses"
            );

            // Naive polarity (Iso := false) must NOT verify: the fail-closed
            // firewall would reject it and keep the verdict at Unknown.
            let mut naive = translated.clone();
            let interp = naive.get(&iso).expect("Iso interpretation").clone();
            naive.set(
                iso,
                PredicateInterpretation::new(interp.vars.clone(), ChcExpr::Bool(false)),
            );
            let mut naive_verifier = PdrSolver::new(problem, bounded_pdr_config());
            assert!(
                !naive_verifier.verify_model(&naive),
                "naive Iso := false interpretation must fail original verification"
            );
        }
        other => panic!("expected Safe, got {other:?}"),
    }
}

/// Forward-unreachable predicate feeding the query: `Ghost` has no fact
/// clause, so the query through it can never fire. Removing it must keep the
/// problem Safe, with `Ghost := false` verifying on the original clauses.
#[test]
fn reachability_forward_unreachable_query_arm_removed() {
    let input = r#"
(set-logic HORN)
(declare-fun Loop (Int) Bool)
(declare-fun Ghost (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Loop x))))
(assert (forall ((x Int) (y Int))
    (=> (and (Loop x) (< x 10) (= y (+ x 1))) (Loop y))))
(assert (forall ((x Int) (y Int)) (=> (and (Ghost x) (Loop y)) false)))
(assert (forall ((x Int)) (=> (and (Loop x) (< x 0)) false)))
(check-sat)
"#;
    let problem = parse(input);
    let result = TransformationPipeline::new()
        .with(UnreachableClauseEliminator::new())
        .transform(problem.clone());

    assert!(
        result.problem.clauses().len() < problem.clauses().len(),
        "the Ghost query arm must be pruned as forward-unreachable"
    );

    let mut solver = PdrSolver::new(result.problem.clone(), bounded_pdr_config());
    match solver.solve() {
        PdrResult::Safe(model) => {
            let translated = result.back_translator.translate_validity(model);
            let ghost = problem.lookup_predicate("Ghost").unwrap();
            assert!(
                matches!(
                    translated.get(&ghost).map(|i| &i.formula),
                    Some(ChcExpr::Bool(false))
                ),
                "forward-unreachable Ghost must be interpreted as false"
            );
            let mut verifier = PdrSolver::new(problem, bounded_pdr_config());
            assert!(
                verifier.verify_model(&translated),
                "back-translated model must verify on the original clauses"
            );
        }
        other => panic!("expected Safe, got {other:?}"),
    }
}

/// Constant propagation: `Mode`'s argument is 1 in every derivable fact, so
/// the query guard `m = 2` folds to false and the problem condenses to Safe.
/// The back-translated model must carry `arg = 1` so the original clauses
/// verify.
#[test]
fn constant_propagation_folds_guards_and_strengthens_model() {
    let input = r#"
(set-logic HORN)
(declare-fun Mode (Int Int) Bool)
(assert (forall ((m Int) (x Int)) (=> (and (= m 1) (= x 0)) (Mode m x))))
(assert (forall ((m Int) (x Int) (y Int))
    (=> (and (Mode m x) (< x 10) (= y (+ x 1))) (Mode m y))))
(assert (forall ((m Int) (x Int)) (=> (and (Mode m x) (= m 2)) false)))
(check-sat)
"#;
    let problem = parse(input);
    let result = TransformationPipeline::new()
        .with(ConstantPropagator::new())
        .transform(problem.clone());

    // The strengthened query constraint `m = 2 /\ m = 1` folds to false, so
    // add_clause prunes the query clause.
    assert!(
        result.problem.clauses().len() < problem.clauses().len(),
        "constant folding must prune the contradictory query clause"
    );

    let mut solver = PdrSolver::new(result.problem.clone(), bounded_pdr_config());
    match solver.solve() {
        PdrResult::Safe(model) => {
            let translated = result.back_translator.translate_validity(model);
            let mut verifier = PdrSolver::new(problem, bounded_pdr_config());
            assert!(
                verifier.verify_model(&translated),
                "back-translated model must carry m = 1 and verify on the original clauses"
            );
        }
        other => panic!("expected Safe after constant folding, got {other:?}"),
    }
}

/// SOUNDNESS PIN: a naive constant propagator that marks `P`'s argument as
/// constant 0 (from the fact clause) despite the incrementing self-loop
/// would strengthen the loop body with `x = 0`, cutting the derivation of
/// `P(5)` and flipping this Unsafe problem to Safe. The justified dataflow
/// must keep the verdict Unsafe.
#[test]
fn constant_propagation_does_not_flip_unsat_on_incrementing_loop() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int) (y Int)) (=> (and (P x) (= y (+ x 1))) (P y))))
(assert (forall ((x Int)) (=> (and (P x) (= x 5)) false)))
(check-sat)
"#;
    let problem = parse(input);
    let result = TransformationPipeline::new()
        .with(ConstantPropagator::new())
        .transform(problem.clone());

    // The head position must NOT be treated as constant: clause set unchanged.
    assert_eq!(
        result.problem.clauses().len(),
        problem.clauses().len(),
        "incrementing loop must block constant propagation"
    );

    match solve_with_pdr(result.problem) {
        PortfolioResult::Unsafe(_) => {}
        other => panic!("expected Unsafe preserved, got {other:?}"),
    }
}

/// SOUNDNESS PIN (fixpoint interplay): constant propagation opens up
/// reachability pruning in a later round, but an Unsafe verdict reachable
/// through the *other* mode value must survive the whole superpass.
#[test]
fn condense_fixpoint_preserves_unsat_through_mode_split() {
    let input = r#"
(set-logic HORN)
(declare-fun A (Int Int) Bool)
(declare-fun B (Int Int) Bool)
(assert (forall ((m Int) (x Int)) (=> (and (= m 1) (= x 0)) (A m x))))
(assert (forall ((m Int) (x Int) (y Int))
    (=> (and (A m x) (= y (+ x 1))) (A m y))))
(assert (forall ((m Int) (x Int)) (=> (A m x) (B m x))))
(assert (forall ((m Int) (x Int)) (=> (and (B m x) (= m 1) (= x 3)) false)))
(check-sat)
"#;
    let problem = parse(input);
    let result = condense(problem);
    match solve_with_pdr(result.problem) {
        PortfolioResult::Unsafe(_) => {}
        other => panic!("expected Unsafe preserved through condense, got {other:?}"),
    }
}

/// The condense fixpoint must chain constituent effects across rounds:
/// constant propagation folds the guard feeding `Sink`, which makes `Sink`
/// forward-unreachable, and reachability pruning then drops its query arm.
#[test]
fn condense_fixpoint_chains_constant_prop_into_reachability() {
    let input = r#"
(set-logic HORN)
(declare-fun Mode (Int Int) Bool)
(declare-fun Sink (Int) Bool)
(assert (forall ((m Int) (x Int)) (=> (and (= m 1) (= x 0)) (Mode m x))))
(assert (forall ((m Int) (x Int) (y Int))
    (=> (and (Mode m x) (< x 10) (= y (+ x 1))) (Mode m y))))
(assert (forall ((m Int) (x Int)) (=> (and (Mode m x) (= m 2)) (Sink x))))
(assert (forall ((x Int)) (=> (Sink x) false)))
(assert (forall ((m Int) (x Int)) (=> (and (Mode m x) (< x 0)) false)))
(check-sat)
"#;
    let problem = parse(input);
    let result = condense(problem.clone());

    assert!(
        result.problem.lookup_predicate("Sink").is_none()
            || result
                .problem
                .clauses()
                .iter()
                .all(
                    |c| c.head.predicate_id() != result.problem.lookup_predicate("Sink")
                        && c.body
                            .predicates
                            .iter()
                            .all(|(pid, _)| Some(*pid) != result.problem.lookup_predicate("Sink"))
                ),
        "Sink must be condensed away"
    );

    let mut solver = PdrSolver::new(result.problem.clone(), bounded_pdr_config());
    match solver.solve() {
        PdrResult::Safe(model) => {
            let translated = result.back_translator.translate_validity(model);
            let mut verifier = PdrSolver::new(problem, bounded_pdr_config());
            assert!(
                verifier.verify_model(&translated),
                "back-translated model must verify on the original clauses"
            );
        }
        other => panic!("expected Safe, got {other:?}"),
    }
}

/// Condense on a problem it cannot shrink must be the identity (identity
/// back-translator, same clauses) so the default path stays byte-identical.
#[test]
fn condense_noops_on_irreducible_problem() {
    let input = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (y Int)) (=> (and (Inv x) (= y (+ x 1))) (Inv y))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
    let problem = parse(input);
    let clause_count = problem.clauses().len();
    let result = condense(problem);
    assert_eq!(result.problem.clauses().len(), clause_count);
}

/// Oversized problems must skip the condense loop entirely.
#[test]
fn condense_skips_oversized_problem() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![]);
    let q = problem.declare_predicate("Q", vec![]);
    for _ in 0..=MAX_CONDENSE_CLAUSES {
        problem.add_clause(crate::HornClause::new(
            crate::ClauseBody::predicates_only(vec![(p, vec![])]),
            crate::ClauseHead::Predicate(q, vec![]),
        ));
    }
    let clause_count = problem.clauses().len();
    let result = condense(problem);
    assert_eq!(result.problem.clauses().len(), clause_count);
    assert!(result
        .back_translator
        .transform_memory()
        .is_identity_grade());
}

/// A real (shrinking) condense stack must NOT be identity-grade: the
/// portfolio firewall then forces original-clause validation for Safe and
/// original replay for Unsafe (fail-closed G1 gating).
#[test]
fn condense_transform_memory_forces_original_validation() {
    let input = r#"
(set-logic HORN)
(declare-fun Init (Int) Bool)
(declare-fun Loop (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Init x))))
(assert (forall ((x Int)) (=> (Init x) (Loop x))))
(assert (forall ((x Int) (y Int)) (=> (and (Loop x) (= y (+ x 1))) (Loop y))))
(assert (forall ((x Int)) (=> (and (Loop x) (< x 0)) false)))
(check-sat)
"#;
    let problem = parse(input);
    let result = condense(problem.clone());
    assert!(
        result.problem.predicates().len() < problem.predicates().len(),
        "Init must be condensed away"
    );
    let memory = result.back_translator.transform_memory();
    assert!(!memory.is_identity_grade());
    assert!(memory.unsafe_backtranslation_complete());
}

/// ClauseIndexMap: dropped clauses clear identity and unmapped indices
/// translate to None (fail-closed original replay).
#[test]
fn clause_index_map_remaps_and_fails_closed() {
    use crate::pdr::counterexample::{Counterexample, CounterexampleStep};
    use ay_core::kani_compat::DetHashMap as FxHashMap;

    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![]);
    let mut map = ClauseIndexMap::new();
    // Original clause 0: dropped (constraint folds to false).
    map.record_add(
        &mut problem,
        crate::HornClause::new(
            crate::ClauseBody::new(vec![], Some(ChcExpr::Bool(false))),
            crate::ClauseHead::Predicate(p, vec![]),
        ),
        0,
    );
    // Original clause 2 lands at kept index 0.
    map.record_add(
        &mut problem,
        crate::HornClause::new(
            crate::ClauseBody::predicates_only(vec![]),
            crate::ClauseHead::Predicate(p, vec![]),
        ),
        2,
    );

    let cex = Counterexample::new(vec![
        CounterexampleStep::new(p, FxHashMap::default()).with_clause(0),
        CounterexampleStep::new(p, FxHashMap::default()).with_clause(7),
    ]);
    let translated = map.translate_invalidity(cex);
    assert_eq!(translated.steps[0].clause_index, Some(2));
    assert_eq!(translated.steps[1].clause_index, None);
}

/// Problem-level metadata (datatype definitions) must survive the condense
/// rebuilds: condense runs at stage -1, BEFORE the stage-0.5 DtFlattener,
/// which reads `datatype_defs()` from the problem it receives. Losing the
/// defs would silently no-op DT flattening downstream.
#[test]
fn condense_preserves_datatype_defs_metadata() {
    let mut input = String::from("(set-logic HORN)\n");
    for i in 0..3 {
        input.push_str(&format!("(declare-fun h{i} (Int) Bool)\n"));
    }
    input.push_str("(assert (forall ((x Int)) (=> (= x 0) (h0 x))))\n");
    for i in 0..2 {
        input.push_str(&format!(
            "(assert (forall ((x Int)) (=> (h{i} x) (h{} x))))\n",
            i + 1
        ));
    }
    input.push_str("(assert (forall ((x Int)) (=> (and (h2 x) (< x 0)) false)))\n");
    input.push_str("(check-sat)\n");
    let mut problem = parse(&input);
    problem.add_datatype_def(
        "Pair".to_string(),
        vec![("mk-pair".to_string(), Vec::new())],
    );
    let clause_count = problem.clauses().len();

    let result = condense(problem);
    assert!(
        result.problem.clauses().len() < clause_count,
        "chain must shrink so the metadata-dropping rebuild path is exercised"
    );
    assert!(
        result.problem.datatype_defs().contains_key("Pair"),
        "datatype definitions must survive the condense rebuilds"
    );
}

/// When EVERY query arm rides an underivable predicate, condense collapses
/// the problem to (near-)empty. The condensed problem must still satisfy
/// `ChcProblem::validate` (pruned-query evidence) so engines return Safe
/// instead of NoQuery/Unknown, and the back-translated model must verify on
/// the ORIGINAL clauses (G1).
#[test]
fn condense_zero_query_collapse_stays_valid_and_safe() {
    let input = r#"
(set-logic HORN)
(declare-fun Loop (Int) Bool)
(declare-fun Ghost (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Loop x))))
(assert (forall ((x Int) (y Int))
    (=> (and (Loop x) (= y (+ x 1))) (Loop y))))
(assert (forall ((x Int) (y Int)) (=> (and (Ghost x) (Loop y)) false)))
(check-sat)
"#;
    let problem = parse(input);
    let result = condense(problem.clone());

    assert!(
        result.problem.queries().next().is_none(),
        "the only query arm rides the underivable Ghost and must be pruned"
    );
    assert!(
        result.problem.validate().is_ok(),
        "condensed problem must keep pruned-query evidence for validate()"
    );

    // PDR alone cannot prove query-free problems Safe (no bad states, no
    // lemmas, fixpoint check rejects empty frames); the portfolio's
    // trivially-safe no-query path is the production handler for this shape.
    match solve_with_pdr(result.problem.clone()) {
        PortfolioResult::Safe(model) => {
            let translated = result.back_translator.translate_validity(model);
            let mut verifier = PdrSolver::new(problem, bounded_pdr_config());
            assert!(
                verifier.verify_model(&translated),
                "back-translated model must verify on the original clauses"
            );
        }
        other => panic!("expected Safe on the query-free condensed problem, got {other:?}"),
    }
}

/// The kill-switch default: condense is enabled unless `--chc-no-condense`
/// (or a test override) turns it off.
#[test]
fn condense_enabled_by_default() {
    assert!(condense_enabled());
}
