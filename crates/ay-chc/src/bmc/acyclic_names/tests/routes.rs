// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;

#[test]
fn symbolic_hidden_local_never_captures_query_variable_or_reach_formal() {
    for query_name in ["z", "__bmc_dag_p0_r0_i0_x", "__bmc_reach_p0_a0"] {
        let (problem, pred) = collision_problem(query_name);
        let solver = BmcSolver::new(problem, BmcConfig::default());
        let mut live = || true;
        let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
        let reach = solver
            .acyclic_reach_formula_fresh(pred, &mut names, &mut DetHashSet::default())
            .unwrap();
        let formula = solver
            .instantiate_reach_formula(pred, &reach, &[variable(query_name)], &mut names)
            .unwrap();
        assert_reachable(&formula, query_name);
        let queries: Vec<_> = solver.problem.queries().collect();
        let simplified = solver.acyclic_symbolic_query(&queries, &mut names).unwrap();
        assert_reachable(&simplified, query_name);
        assert!(!matches!(simplified, ChcExpr::Bool(false)));
    }
}

#[test]
fn direct_and_streaming_instances_preserve_original_query_and_path_bindings() {
    for query_name in ["z", "__bmc_dag_e0_v0"] {
        let (problem, pred) = collision_problem(query_name);
        let solver = BmcSolver::new(problem, BmcConfig::default());
        let deadline = ay_core::time::Instant::now() + std::time::Duration::from_secs(60);
        let defs = solver.defs_by_head();
        let mut live = || true;
        let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
        let formula = solver
            .acyclic_reach_instance(
                pred,
                &[variable(query_name)],
                &defs,
                &mut DetHashSet::default(),
                &mut names,
                deadline,
            )
            .unwrap();
        assert_reachable(&formula, query_name);

        let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
        let mut count = 0;
        let outcome = solver.enumerate_acyclic_linear_pred_branches(
            pred,
            &[variable(query_name)],
            &defs,
            &mut DetHashSet::default(),
            &mut names,
            deadline,
            &mut Vec::new(),
            &mut Vec::new(),
            &mut |branch, path, _names| {
                count += 1;
                assert_reachable(&ChcExpr::and_all(branch.to_vec()), query_name);
                assert_eq!(path.len(), 1);
                assert_eq!(path[0].args, vec![variable(query_name)]);
                assert!(path[0].clause_var_renaming.contains_key("x"));
                assert_ne!(path[0].clause_var_renaming["x"], variable(query_name));
                true
            },
        );
        assert!(matches!(outcome, AcyclicBranchEnumeration::Completed));
        assert_eq!(count, 1);
    }
}

#[test]
fn repeated_expansions_have_independent_hidden_locals() {
    let (problem, pred) = collision_problem("__bmc_dag_p0_r0_i0_x");
    let solver = BmcSolver::new(problem, BmcConfig::default());
    let mut live = || true;
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    let first = solver
        .acyclic_reach_formula_fresh(pred, &mut names, &mut DetHashSet::default())
        .unwrap();
    let second = solver
        .acyclic_reach_formula_fresh(pred, &mut names, &mut DetHashSet::default())
        .unwrap();
    let locals = |expression: ChcExpr| {
        expression
            .vars()
            .into_iter()
            .filter(|var| var.name.starts_with("__bmc_dag_"))
            .map(|var| var.name)
            .collect::<Vec<_>>()
    };
    let first = locals(first);
    let second = locals(second);
    assert_eq!(first.len(), 1);
    assert_eq!(second.len(), 1);
    assert_ne!(first, second);
}

#[test]
fn preflight_refusal_does_not_retry_the_level_flat_encoding() {
    let (problem, _) = collision_problem("z");
    let mut config = BmcConfig::default();
    config.time_budget = Some(std::time::Duration::ZERO);
    let solver = BmcSolver::new(problem, config);
    let queries: Vec<_> = solver.problem.queries().collect();
    assert!(matches!(
        solver.solve_acyclic_symbolic_reachability_once(&queries, 1),
        Err(ExactExpansionRefused)
    ));
    assert!(matches!(
        solver.solve_acyclic_exhaustive_once(&queries, 1),
        Some(crate::ChcEngineResult::Unknown)
    ));
    assert!(!solver.stats.borrow().exhausted_search);
}

#[test]
fn live_depth_refusal_is_terminal_before_preferred_exact_concrete_recovery() {
    let (mut problem, pred) = collision_problem("z");
    let mut expression = variable("deep");
    for _ in 0..crate::expr::MAX_EXPR_RECURSION_DEPTH {
        expression = ChcExpr::Op(
            ChcOp::Add,
            vec![Arc::new(expression), Arc::new(ChcExpr::Int(0))],
        );
    }
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(pred, vec![expression]),
    ));
    let mut config = BmcConfig::default();
    config.acyclic_safe = true;
    config.prefer_exact_acyclic_first = true;
    config.enable_adaptive_stepping = false;
    config.enable_k_induction = false;
    config.time_budget = Some(std::time::Duration::from_secs(60));
    let solver = BmcSolver::new(problem, config);
    assert!(solver.prefer_exact_acyclic_executor_first());
    let queries: Vec<_> = solver.problem.queries().collect();
    assert!(matches!(
        solver.solve_via_executor(&queries),
        Err(ExactExpansionRefused)
    ));
    assert!(matches!(solver.solve(), crate::ChcEngineResult::Unknown));
    assert!(!solver.stats.borrow().used_legacy_fallback);
    assert!(!solver.stats.borrow().budget_exhausted);
    assert!(!solver.stats.borrow().exhausted_search);
    // No SMT solver is reached: the complete source scan refuses first.
    drop(solver);
}
