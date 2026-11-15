use super::*;

/// A separate recursive derivation-tree-height oracle. The generated graphs
/// are acyclic and tiny; no production reachable-level set is consulted.
fn has_tree_at_height(problem: &ChcProblem, pred: PredicateId, height: usize) -> bool {
    problem.clauses_defining(pred).any(|clause| {
        clause.body.predicates.is_empty()
            || (height > 0
                && clause
                    .body
                    .predicates
                    .iter()
                    .all(|(child, _)| has_tree_at_height(problem, *child, height - 1)))
    })
}

#[test]
fn cone_coverage_matches_tree_height_oracle_on_256_acyclic_graphs() {
    for mask in 0_u16..256 {
        let mut problem = ChcProblem::new();
        let predicates: Vec<_> = (0..4)
            .map(|index| problem.declare_predicate(&format!("P{index}"), Vec::new()))
            .collect();
        for (index, &pred) in predicates.iter().enumerate() {
            if mask & (1 << index) != 0 {
                nullary_rule(&mut problem, pred, &[]);
            }
        }
        for index in 1..4 {
            if mask & (1 << (3 + index)) != 0 {
                nullary_rule(&mut problem, predicates[index], &[predicates[index - 1]]);
            }
        }
        if mask & 128 != 0 {
            nullary_rule(&mut problem, predicates[3], &[predicates[0], predicates[2]]);
        }
        let solver = BmcSolver::new(problem, BmcConfig::default());
        let cone = predicates.iter().copied().collect();
        let reachable = solver.reachable_levels_by_pred(4, &cone, &solver.defs_by_head());
        for pred in predicates {
            for height in 0..=4 {
                assert_eq!(
                    reachable
                        .get(&pred)
                        .is_some_and(|levels| levels.contains(&height)),
                    has_tree_at_height(&solver.problem, pred, height),
                    "mask={mask}, predicate={pred:?}, height={height}",
                );
            }
        }
    }
}

#[test]
fn cone_coverage_unfounded_cycle_does_not_become_reachable() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", Vec::new());
    let q = problem.declare_predicate("Q", Vec::new());
    let dead = problem.declare_predicate("Dead", Vec::new());
    nullary_rule(&mut problem, p, &[q]);
    nullary_rule(&mut problem, q, &[p]);
    let solver = BmcSolver::new(problem, BmcConfig::default());
    let cone = FxHashSet::from_iter([p, q, dead]);
    let reachable = solver.reachable_levels_by_pred(4, &cone, &solver.defs_by_head());
    assert!(reachable.is_empty());
}
