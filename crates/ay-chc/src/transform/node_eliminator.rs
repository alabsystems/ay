// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Graph-collapse node elimination for multi-predicate linear CHC.
//!
//! Mirrors golem's preprocessing loop of `NodeEliminator` (internal-vertex
//! contraction) and `MultiEdgeMerger` (parallel-edge disjunction):
//! `reference/golem/src/transformers/{NodeEliminator,MultiEdgeMerger}.cc`.
//! Golem's `Normalizer`+pipeline collapses e.g. 20-vertex/22-clause HOLA/reve
//! control-flow graphs to 3-vertex/3-clause systems before solving.
//!
//! Vertex contraction is implemented at clause level by reusing the existing
//! `ClauseInliner` machinery in graph-collapse mode (predicate-application
//! inlining + substitution-based existential elimination of the contracted
//! predicate's arguments, golem's `|in|*|out| <= |in|+|out|` candidate rule).
//! That machinery carries witness back-translation in both directions:
//!
//! - Safe: interpretations for eliminated predicates are synthesized from
//!   their defining clauses (disjunction of strongest postconditions, with
//!   capped AllSAT+MBP existential projection that FAILS CLOSED), and the
//!   portfolio re-validates the translated model against the ORIGINAL
//!   clauses (`validate_safe_with_mode_translating`).
//! - Unsafe: witnesses are remapped to original predicate ids and replayed
//!   against the ORIGINAL clauses; entries that no longer match any original
//!   clause make verification inconclusive, which the portfolio treats as
//!   fail-closed Unknown.
//!
//! The pass alternates contraction and parallel-edge merging until a
//! fixpoint (merging two parallel composed clauses lowers in/out degrees,
//! which unlocks further contraction — the same loop golem runs).
//!
//! Routed strictly behind `AY_GRAPH_COLLAPSE=1` (default OFF): a previous
//! MultiEdgeMerger-adjacent routing caused the s_split_36 regression
//! (removed in a4d94e3), so the off-path must stay byte-identical.

use super::multi_edge_merger::MultiEdgeMerger;
use super::{
    BackTranslator, ClauseInliner, CompositeBackTranslator, IdentityBackTranslator,
    TransformationResult, Transformer,
};
use crate::ChcProblem;

/// Problems larger than this skip the collapse loop entirely. The target
/// class (HOLA/reve/llreve/hopv CFGs) is tens of clauses; huge systems get
/// no benefit and would pay repeated clause-vector rebuilds.
const MAX_COLLAPSE_CLAUSES: usize = 1024;

/// Bound on alternating (contract, merge) rounds. Each round must strictly
/// shrink the (predicates, clauses) pair or the loop stops early, so this is
/// a safety cap, not the usual termination path.
const MAX_COLLAPSE_ROUNDS: usize = 8;

/// Golem-style node-elimination preprocessing pass (AY_GRAPH_COLLAPSE=1).
pub(crate) struct NodeEliminator {
    verbose: bool,
}

impl NodeEliminator {
    pub(crate) fn new() -> Self {
        Self { verbose: false }
    }

    pub(crate) fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }
}

impl Transformer for NodeEliminator {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        if problem.clauses().len() > MAX_COLLAPSE_CLAUSES {
            return TransformationResult {
                problem,
                back_translator: Box::new(IdentityBackTranslator),
            };
        }

        let initial = (problem.predicates().len(), problem.clauses().len());
        let mut current = problem;
        let mut translators: Vec<Box<dyn BackTranslator>> = Vec::new();

        for _round in 0..MAX_COLLAPSE_ROUNDS {
            let before = (current.predicates().len(), current.clauses().len());

            // Vertex contraction: unique-definition inlining (1-in/N-out)
            // plus golem's |in|*|out| <= |in|+|out| multi-definition rule.
            let contract = Box::new(
                ClauseInliner::new()
                    .with_verbose(self.verbose)
                    .with_graph_collapse_node_rule(),
            )
            .transform(current);
            current = contract.problem;
            translators.push(contract.back_translator);

            // Parallel-edge merging: disjoin constraints of clauses that
            // connect the same predicates with identical argument vectors.
            let merge = Box::new(MultiEdgeMerger::new()).transform(current);
            current = merge.problem;
            translators.push(merge.back_translator);

            let after = (current.predicates().len(), current.clauses().len());
            if after == before {
                break;
            }
        }

        if self.verbose {
            let after = (current.predicates().len(), current.clauses().len());
            if after != initial {
                safe_eprintln!(
                    "CHC graph collapse: {} predicates / {} clauses -> {} / {}",
                    initial.0,
                    initial.1,
                    after.0,
                    after.1
                );
            }
        }

        translators.reverse();
        TransformationResult {
            problem: current,
            back_translator: Box::new(CompositeBackTranslator { inner: translators }),
        }
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::ChcParser;
    use crate::pdr::{PdrConfig, PdrResult, PdrSolver};
    use crate::transform::TransformationPipeline;

    fn parse(smt: &str) -> ChcProblem {
        ChcParser::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"))
    }

    fn collapse(problem: ChcProblem) -> TransformationResult {
        TransformationPipeline::new()
            .with(NodeEliminator::new())
            .transform(problem)
    }

    /// PdrConfig with a hard timeout so a slow solve fails the test instead
    /// of hanging the suite.
    fn bounded_pdr_config() -> PdrConfig {
        PdrConfig {
            solve_timeout: Some(std::time::Duration::from_secs(60)),
            ..PdrConfig::default()
        }
    }

    /// 3-predicate linear chain: Init -> Mid -> Loop with a self-loop and a
    /// query. Init and Mid are 1-in/1-out internal vertices and must be
    /// contracted away; the verdict must stay Safe and the back-translated
    /// model must verify on the ORIGINAL clauses.
    #[test]
    fn chain_contraction_preserves_sat_and_backtranslates_model() {
        let input = r#"
(set-logic HORN)
(declare-fun Init (Int) Bool)
(declare-fun Mid (Int) Bool)
(declare-fun Loop (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Init x))))
(assert (forall ((x Int)) (=> (Init x) (Mid x))))
(assert (forall ((x Int)) (=> (Mid x) (Loop x))))
(assert (forall ((x Int) (y Int))
    (=> (and (Loop x) (< x 10) (= y (+ x 1))) (Loop y))))
(assert (forall ((x Int)) (=> (and (Loop x) (< x 0)) false)))
(check-sat)
"#;
        let problem = parse(input);
        let result = collapse(problem.clone());

        assert!(
            result.problem.predicates().len() < problem.predicates().len(),
            "chain vertices must be contracted: {} -> {}",
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
                    "back-translated model must verify on the original clauses"
                );
            }
            other => panic!("expected Safe on collapsed chain, got {other:?}"),
        }
    }

    /// Same chain shape but with a reachable bad state: the collapsed
    /// problem must stay Unsafe (satisfiability preserved exactly).
    #[test]
    fn chain_contraction_preserves_unsat() {
        let input = r#"
(set-logic HORN)
(declare-fun Init (Int) Bool)
(declare-fun Mid (Int) Bool)
(declare-fun Loop (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Init x))))
(assert (forall ((x Int)) (=> (Init x) (Mid x))))
(assert (forall ((x Int)) (=> (Mid x) (Loop x))))
(assert (forall ((x Int) (y Int))
    (=> (and (Loop x) (< x 10) (= y (+ x 1))) (Loop y))))
(assert (forall ((x Int)) (=> (and (Loop x) (> x 5)) false)))
(check-sat)
"#;
        let problem = parse(input);
        let result = collapse(problem);

        let mut solver = PdrSolver::new(result.problem, bounded_pdr_config());
        match solver.solve() {
            PdrResult::Unsafe(_) => {}
            other => panic!("expected Unsafe on collapsed chain, got {other:?}"),
        }
    }

    /// A join vertex with more definitions than the default Z3-style
    /// `max_multi_defs = 8` cap: golem's rule (9-in/1-out, 9*1 <= 9+1)
    /// contracts it, while the default ClauseInliner keeps it. `Z` keeps a
    /// self-loop so a loop vertex survives the collapse (like the HOLA CFGs).
    fn many_in_one_out_problem() -> ChcProblem {
        let mut input = String::from(
            "(set-logic HORN)\n(declare-fun A (Int) Bool)\n(declare-fun J (Int) Bool)\n(declare-fun Z (Int) Bool)\n",
        );
        input.push_str("(assert (forall ((x Int)) (=> (= x 0) (A x))))\n");
        for k in 0..9 {
            input.push_str(&format!(
                "(assert (forall ((x Int) (y Int)) (=> (and (A x) (= y {k})) (J y))))\n"
            ));
        }
        input.push_str("(assert (forall ((x Int)) (=> (J x) (Z x))))\n");
        input.push_str(
            "(assert (forall ((x Int) (y Int)) (=> (and (Z x) (< x 100) (= y (+ x 1))) (Z y))))\n",
        );
        input.push_str("(assert (forall ((x Int)) (=> (and (Z x) (< x 0)) false)))\n");
        input.push_str("(check-sat)\n");
        parse(&input)
    }

    #[test]
    fn golem_rule_contracts_many_in_one_out_join() {
        let problem = many_in_one_out_problem();
        let join = problem.predicates().iter().any(|p| p.name == "J");
        assert!(join, "test problem must declare the join predicate");

        // Default inliner: J has 9 definitions > max_multi_defs, stays.
        let default_result = TransformationPipeline::new()
            .with(ClauseInliner::new())
            .transform(problem.clone());
        assert!(
            default_result
                .problem
                .predicates()
                .iter()
                .any(|p| p.name == "J"),
            "default caps must keep the 9-definition join predicate"
        );

        // Graph-collapse rule: 9-in/1-out satisfies |in|*|out| <= |in|+|out|.
        let collapsed = collapse(problem.clone());
        assert!(
            collapsed.problem.predicates().iter().all(|p| p.name != "J"),
            "golem node rule must contract the 9-in/1-out join predicate"
        );

        // Verdict preserved + model back-translation covers the join.
        let mut solver = PdrSolver::new(collapsed.problem.clone(), bounded_pdr_config());
        match solver.solve() {
            PdrResult::Safe(model) => {
                let translated = collapsed.back_translator.translate_validity(model);
                let mut verifier = PdrSolver::new(problem, bounded_pdr_config());
                assert!(
                    verifier.verify_model(&translated),
                    "back-translated model must verify on the original join problem"
                );
            }
            other => panic!("expected Safe on collapsed join, got {other:?}"),
        }
    }

    /// Contraction must compose in-edge and out-edge constraints: the only
    /// path Init -> Mid -> query forces x = 7 at Mid; query demands x = 7,
    /// so the collapsed problem is Unsafe exactly like the original. The
    /// chain collapses into a predicate-free query, which the portfolio's
    /// trivial handler decides.
    #[test]
    fn contraction_composes_constraints_exactly() {
        use crate::portfolio::{EngineConfig, PortfolioConfig, PortfolioResult, PortfolioSolver};

        let input = r#"
(set-logic HORN)
(declare-fun Init (Int) Bool)
(declare-fun Mid (Int) Bool)
(assert (forall ((x Int)) (=> (= x 7) (Init x))))
(assert (forall ((x Int) (y Int)) (=> (and (Init x) (= y x)) (Mid y))))
(assert (forall ((x Int)) (=> (and (Mid x) (= x 7)) false)))
(check-sat)
"#;
        let problem = parse(input);
        let result = collapse(problem);
        let config = PortfolioConfig::with_engines(vec![EngineConfig::Pdr(PdrConfig::default())])
            .parallel(false);
        let solver = PortfolioSolver::new(result.problem, config);
        match solver.solve() {
            PortfolioResult::Unsafe(_) => {}
            other => panic!("expected Unsafe after exact composition, got {other:?}"),
        }
    }

    /// Oversized problems must pass through untouched (identity translator).
    #[test]
    fn oversized_problem_skips_collapse() {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![]);
        for _ in 0..(MAX_COLLAPSE_CLAUSES + 1) {
            problem.add_clause(crate::HornClause::new(
                crate::ClauseBody::predicates_only(vec![(p, vec![])]),
                crate::ClauseHead::Predicate(p, vec![]),
            ));
        }
        let clause_count = problem.clauses().len();
        let result = collapse(problem);
        assert_eq!(result.problem.clauses().len(), clause_count);
    }
}
