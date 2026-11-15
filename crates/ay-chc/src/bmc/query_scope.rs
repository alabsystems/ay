// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Query-clause variables that share a name at different sorts.
//!
//! Several BMC lanes compile all query clauses into ONE formula: the acyclic
//! symbolic and exhaustive probes OR every query, the level encodings OR the
//! per-query groups. A query's constraint-local variables keep their source
//! names there (`compile_query`, `acyclic_symbolic_query`), which is exact
//! across a disjunction as long as each name has one sort. Two queries that
//! bind one name at two sorts, `(t Bool)` in one and `(t Int)` in the other,
//! put two different variables under one SMT name: the acyclic probe then
//! refuted an unsafe system and published `Safe` with an empty invariant
//! (CHC differential generator, `gen/chc` job `headonly_1`; z3 5.1: `unsat`).
//!
//! [`rename_query_sort_clashes`] renames such variables apart, per query
//! clause, before any lane runs. Problems without a clash are untouched.

use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseHead};
use ay_core::kani_compat::{DetHashMap, DetHashSet};

pub(super) fn rename_query_sort_clashes(mut problem: ChcProblem) -> ChcProblem {
    let mut sorts: DetHashMap<String, Vec<ChcSort>> = DetHashMap::default();
    for clause in problem.clauses().iter().filter(|clause| clause.is_query()) {
        for var in clause.vars() {
            let seen = sorts.entry(var.name).or_default();
            if !seen.contains(&var.sort) {
                seen.push(var.sort);
            }
        }
    }
    let clashing: DetHashSet<String> = sorts
        .into_iter()
        .filter(|(_, seen)| seen.len() > 1)
        .map(|(name, _)| name)
        .collect();
    if clashing.is_empty() {
        return problem;
    }
    let mut taken: DetHashSet<String> = problem
        .clauses()
        .iter()
        .flat_map(|clause| clause.vars())
        .map(|var| var.name)
        .collect();
    for (index, clause) in problem.clauses_mut().iter_mut().enumerate() {
        if !matches!(clause.head, ClauseHead::False) {
            continue;
        }
        let subst: Vec<(ChcVar, ChcExpr)> = clause
            .vars()
            .into_iter()
            .filter(|var| clashing.contains(&var.name))
            .map(|var| {
                let mut fresh = format!("{}!bmcq{index}", var.name);
                while !taken.insert(fresh.clone()) {
                    fresh.push('!');
                }
                let renamed = ChcExpr::var(ChcVar::new(fresh, var.sort.clone()));
                (var, renamed)
            })
            .collect();
        for (_, args) in &mut clause.body.predicates {
            for arg in args.iter_mut() {
                *arg = arg.substitute(&subst);
            }
        }
        if let Some(constraint) = &clause.body.constraint {
            clause.body.constraint = Some(constraint.substitute(&subst));
        }
    }
    problem
}

#[cfg(test)]
mod tests {
    use super::rename_query_sort_clashes;
    use crate::ChcParser;

    #[test]
    fn a_name_bound_at_two_sorts_in_two_queries_is_renamed_apart() {
        let problem = ChcParser::parse(
            "(set-logic HORN)
             (declare-fun Q (Int) Bool)
             (assert (forall ((y Int)) (=> (>= y 2) (Q y))))
             (assert (forall ((c Int) (t Bool)) (=> (and (= t (= c 1)) (Q c) t) false)))
             (assert (forall ((y Int) (t Int)) (=> (and (= t y) (>= t 5) (Q y)) false)))",
        )
        .expect("parses");
        let renamed = rename_query_sort_clashes(problem);
        let names: Vec<Vec<String>> = renamed
            .clauses()
            .iter()
            .filter(|clause| clause.is_query())
            .map(|clause| clause.vars().into_iter().map(|var| var.name).collect())
            .collect();
        assert!(
            names
                .iter()
                .all(|vars| !vars.iter().any(|name| name == "t")),
            "both `t`s must be renamed apart: {names:?}"
        );
        assert_ne!(names[0], names[1]);
        // The fact is not a query and keeps its names.
        assert!(renamed.clauses()[0]
            .vars()
            .iter()
            .any(|var| var.name == "y"));
    }

    #[test]
    fn a_problem_without_a_clash_is_untouched() {
        let input = "(set-logic HORN)
             (declare-fun Q (Int) Bool)
             (assert (forall ((y Int)) (=> (>= y 2) (Q y))))
             (assert (forall ((y Int) (t Int)) (=> (and (= t y) (>= t 5) (Q y)) false)))
             (assert (forall ((c Int) (t Int)) (=> (and (= t c) (Q c)) false)))";
        let problem = ChcParser::parse(input).expect("parses");
        let before = format!("{:?}", problem.clauses());
        let after = format!("{:?}", rename_query_sort_clashes(problem).clauses());
        assert_eq!(before, after);
    }
}
