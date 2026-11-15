// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;
use crate::ClauseBody;
use std::cell::Cell;
use std::time::Duration;

mod fixtures;
mod progress;
mod witness;
use fixtures::*;

#[test]
fn ordinary_polynomial_names_and_variable_order_match_the_legacy_constructors() {
    let solver = fixture(None);
    let mut live = || true;
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    assert_eq!(generated(&solver, &mut names), STEMS.map(str::to_owned));
    for (index, clause) in solver.problem.clauses().iter().enumerate() {
        let actual = match &clause.head {
            ClauseHead::Predicate(pred, _) => {
                solver.mk_dag_clause_vars(clause, *pred, index, &mut names)
            }
            ClauseHead::False => solver.mk_dag_query_vars(clause, 0, &mut names),
        }
        .unwrap();
        let expected = clause
            .vars()
            .into_iter()
            .enumerate()
            .map(|(ordinal, var)| {
                let stem = match &clause.head {
                    ClauseHead::Predicate(pred, _) => {
                        format!("__bmc_poly_p{}_c{index}_v{ordinal}", pred.index())
                    }
                    ClauseHead::False => format!("__bmc_poly_q0_v{ordinal}"),
                };
                (var.name, ChcExpr::var(ChcVar::new(stem, var.sort)))
            })
            .collect::<FxHashMap<_, _>>();
        assert_eq!(actual, expected);
    }
}

#[test]
fn each_global_uf_family_is_kept_verbatim_and_disjoint_from_compiled_variables() {
    for source in STEMS {
        let solver = fixture(Some(source));
        let before = format!("{:?}", solver.problem.clauses());
        let mut live = || true;
        let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
        let generated = generated(&solver, &mut names);
        assert_eq!(generated, STEMS.map(|stem| format!("{stem}__ay_exact_0")));
        let formula = compile(&solver, &mut names).unwrap();
        assert!(contains_global(&formula, source));
        assert!(formula.vars().iter().all(|var| var.name != source));
        let applications =
            collect_uninterpreted_function_applications_for_exprs(std::iter::once(&formula))
                .unwrap();
        assert!(applications.contains(&global(source)));
        assert_eq!(before, format!("{:?}", solver.problem.clauses()));
    }
}

#[test]
fn unused_declarations_also_reserve_polynomial_names_and_suffix_endings() {
    for source in STEMS {
        let mut solver = fixture(None);
        solver.problem.declare_predicate(source, Vec::new());
        solver
            .problem
            .declare_predicate("unused__ay_exact_0", Vec::new());
        let mut live = || true;
        let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
        assert_eq!(
            generated(&solver, &mut names),
            STEMS.map(|stem| format!("{stem}__ay_exact_1"))
        );
    }
}

#[test]
fn inferred_source_constants_are_not_renamed_and_growing_surfaces_refuse() {
    let solver = fixture(Some(STEMS[0]));
    let p = PredicateId::new(0);
    let global = global(STEMS[0]);
    let mut live = || true;
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    for value in [global, ChcExpr::Int(37)] {
        let constants = FxHashMap::from_iter([((p, 0), value.clone())]);
        assert_eq!(
            solver.dag_arg_with_constants(p, 0, &constants, &mut names),
            Some(value)
        );
    }
    let mut deep = ChcExpr::Int(0);
    for _ in 0..crate::expr::MAX_EXPR_RECURSION_DEPTH {
        deep = ChcExpr::FuncApp("f".to_owned(), ChcSort::Int, vec![Arc::new(deep)]);
    }
    let constants = FxHashMap::from_iter([((p, 0), deep)]);
    assert!(solver
        .dag_arg_with_constants(p, 0, &constants, &mut names)
        .is_none());
    assert!(names.stopped());
}

#[test]
fn missing_polynomial_argument_metadata_is_sticky_instead_of_panicking() {
    let solver = fixture(None);
    for (pred, arg) in [(PredicateId::new(0), 1), (PredicateId::new(u32::MAX), 0)] {
        let mut live = || true;
        let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
        assert!(solver.dag_arg(pred, arg, &mut names).is_none());
        assert!(names.stopped());
        assert!(solver
            .dag_predicate(PredicateId::new(0), &mut names)
            .is_none());
    }
}

#[test]
fn full_variable_order_and_renamed_range_guards_remain_consistent() {
    let solver = fixture(Some(STEMS[2]));
    let mut live = || true;
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    let p = PredicateId::new(0);
    let clause = HornClause::new(
        ClauseBody::new(
            vec![(p, vec![variable("b")])],
            Some(ChcExpr::lt(variable("a"), variable("b"))),
        ),
        ClauseHead::Predicate(p, vec![variable("c")]),
    );
    let substitutions = solver
        .mk_dag_clause_vars(&clause, p, 2, &mut names)
        .unwrap();
    for (index, var) in clause.vars().into_iter().enumerate() {
        assert_eq!(
            substitutions[&var.name],
            variable(&format!("__bmc_poly_p0_c2_v{index}__ay_exact_0"))
        );
    }
    let bounds = FxHashMap::from_iter([(
        (p, 0),
        IntInterval {
            lower: Some(2),
            upper: Some(7),
        },
    )]);
    let mut conjuncts = Vec::new();
    assert_eq!(
        solver.push_acyclic_dag_arg_bound_conjuncts(
            &[p],
            &bounds,
            &FxHashMap::default(),
            &mut conjuncts,
            &mut names,
        ),
        Some(1)
    );
    let formula = ChcExpr::and_all(conjuncts);
    let generated = generated(&solver, &mut names);
    let mut model = FxHashMap::from_iter([
        (generated[0].clone(), SmtValue::Bool(true)),
        (generated[2].clone(), SmtValue::Int(3)),
    ]);
    assert_eq!(evaluate_expr(&formula, &model), Some(SmtValue::Bool(true)));
    model.insert(generated[2].clone(), SmtValue::Int(8));
    assert_eq!(evaluate_expr(&formula, &model), Some(SmtValue::Bool(false)));
}
