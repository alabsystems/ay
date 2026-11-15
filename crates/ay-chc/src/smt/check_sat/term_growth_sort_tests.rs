// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{Constant, DisequalitySplitRequest, TermData};
use ay_sat::{Literal, Variable};
use num_rational::BigRational;

struct SplitFixture {
    context: SmtContext,
    var_to_term: BTreeMap<u32, TermId>,
    num_vars: u32,
    clauses: Vec<Vec<Literal>>,
}

fn apply_split(mut context: SmtContext, variable: TermId, value: BigRational) -> SplitFixture {
    let mut term_to_var = BTreeMap::new();
    let mut var_to_term = BTreeMap::new();
    let mut num_vars = 0;
    let mut sat = LoopSat::new(ay_sat::Solver::new(0));
    context
        .apply_disequality_split(
            Vec::new(),
            DisequalitySplitRequest {
                variable,
                excluded_value: value,
                disequality_term: None,
                is_distinct: false,
            },
            &mut term_to_var,
            &mut var_to_term,
            &mut num_vars,
            &mut sat,
            &mut SplitState::new(),
            false,
            0,
        )
        .unwrap();
    SplitFixture {
        context,
        var_to_term,
        num_vars,
        clauses: sat.added_clauses().to_vec(),
    }
}

fn solve_with(fixture: &SplitFixture, forced: &[Literal]) -> ay_sat::SolverSatResult {
    let mut sat = ay_sat::Solver::new(fixture.num_vars as usize);
    for clause in &fixture.clauses {
        sat.add_clause(clause.clone());
    }
    for &literal in forced {
        sat.add_clause(vec![literal]);
    }
    sat.solve()
}

fn assert_numeric_sorts(fixture: &SplitFixture, clause: &[Literal], sort: &Sort, denominator: i32) {
    let fractional_int = sort == &Sort::Int && denominator == 2;
    assert!((2..=3).contains(&clause.len()));
    assert!(clause.iter().all(|literal| literal.is_positive()));
    if clause.len() == 3 {
        let guard = fixture.var_to_term[&(clause[0].variable().index() as u32 + 1)];
        match fixture.context.terms.get(guard) {
            TermData::Const(Constant::Bool(false)) => assert!(fractional_int),
            TermData::App(symbol, args) => {
                assert_eq!(symbol.name(), "=");
                assert_eq!(
                    fixture.context.terms.sort(args[0]),
                    fixture.context.terms.sort(args[1])
                );
                assert_eq!(fixture.context.terms.sort(args[0]), sort);
            }
            other => panic!("unexpected numeric guard {other:?}"),
        }
    } else {
        assert!(
            fractional_int,
            "only an impossible Int/fraction equality loses its guard"
        );
    }
    for literal in &clause[clause.len() - 2..] {
        let atom = fixture.var_to_term[&(literal.variable().index() as u32 + 1)];
        let TermData::App(_, args) = fixture.context.terms.get(atom) else {
            panic!("expected a split comparison");
        };
        assert!(args
            .iter()
            .all(|arg| fixture.context.terms.sort(*arg) == sort));
    }
}

#[test]
fn disequality_split_guards_and_bounds_preserve_numeric_sorts() {
    for sort in [Sort::Int, Sort::Real] {
        for denominator in [1, 2] {
            let mut context = SmtContext::new();
            let variable = context.terms.mk_var("x", sort.clone());
            let fixture = apply_split(
                context,
                variable,
                BigRational::new(3.into(), denominator.into()),
            );
            let clause = fixture
                .clauses
                .iter()
                .find(|clause| clause.len() >= 2)
                .unwrap();
            assert_numeric_sorts(&fixture, clause, &sort, denominator);
            let branches = &clause[clause.len() - 2..];
            let left_false = Literal::negative(branches[0].variable());
            let right_false = Literal::negative(branches[1].variable());
            if sort == Sort::Int && denominator == 2 {
                // An Int cannot equal 3/2: a free Boolean standing for `false`
                // must not let both sides of the integer partition be false.
                assert!(solve_with(&fixture, &[left_false, right_false]).is_unsat());
                assert!(solve_with(&fixture, &[branches[0], right_false]).is_sat());
            } else {
                // At the excluded value, the equality guard keeps the clause
                // conditional. Removing that live guard would overconstrain it.
                assert!(solve_with(&fixture, &[clause[0], left_false, right_false]).is_sat());
                let guard_false = Literal::negative(clause[0].variable());
                assert!(solve_with(&fixture, &[guard_false, left_false, right_false]).is_unsat());
            }
        }
    }
}

#[test]
fn a_true_constant_guard_does_not_exclude_its_satisfying_value() {
    let mut context = SmtContext::new();
    let variable = context.terms.mk_int(3.into());
    let fixture = apply_split(context, variable, BigRational::from_integer(3.into()));
    let false_term = fixture.context.terms.false_term();
    let false_comparisons: Vec<_> = fixture
        .var_to_term
        .iter()
        .filter(|(_, term)| **term == false_term)
        .map(|(cnf, _)| Literal::negative(Variable::new(*cnf - 1)))
        .collect();
    assert!(!false_comparisons.is_empty());
    assert!(solve_with(&fixture, &false_comparisons).is_sat());
}
