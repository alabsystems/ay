use super::*;

fn bounded_solver(problem: ChcProblem) -> BmcSolver {
    BmcSolver::new(
        problem,
        BmcConfig {
            max_depth: 3,
            acyclic_safe: true,
            time_budget: Some(std::time::Duration::from_secs(5)),
            per_depth_timeout: Some(std::time::Duration::from_secs(5)),
            enable_k_induction: false,
            enable_adaptive_stepping: false,
            ..BmcConfig::default()
        },
    )
}

#[test]
#[ntest::timeout(15_000)]
fn cone_coverage_live_uneven_query_cannot_be_safe() {
    let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(256 << 20));
    let solver = bounded_solver(uneven_problem());
    let queries: Vec<_> = solver.problem.queries().collect();
    let result = solver.solve_acyclic_cone_level_flat_once(&queries, 3, &solver.defs_by_head());
    // This safety-only lane intentionally has no SAT witness extractor.
    assert!(matches!(result, ChcEngineResult::Unknown), "{result:?}");
    assert!(!solver.stats().exhausted_search);
}

#[test]
#[ntest::timeout(15_000)]
fn cone_coverage_live_bodyless_query_cannot_be_safe() {
    let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(256 << 20));
    for constraint in [None, Some(ChcExpr::Bool(true))] {
        let mut problem = ChcProblem::new();
        problem.add_clause(HornClause::new(
            ClauseBody::new(Vec::new(), constraint),
            ClauseHead::False,
        ));
        let solver = bounded_solver(problem);
        let queries: Vec<_> = solver.problem.queries().collect();
        let result = solver.solve_acyclic_cone_level_flat_once(&queries, 0, &solver.defs_by_head());
        assert!(matches!(result, ChcEngineResult::Unknown), "{result:?}");
        assert!(!solver.stats().exhausted_search);
    }
}

#[test]
#[ntest::timeout(15_000)]
fn cone_coverage_false_bodyless_query_is_still_safe() {
    let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(256 << 20));
    // Pass the query directly: adding literal false to ChcProblem would
    // prune it, testing the empty query list instead of this encoding.
    let query = HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(false)),
        ClauseHead::False,
    );
    let solver = bounded_solver(ChcProblem::new());
    let result = solver.solve_acyclic_cone_level_flat_once(&[&query], 0, &solver.defs_by_head());
    assert!(matches!(result, ChcEngineResult::Safe(_)), "{result:?}");
}
