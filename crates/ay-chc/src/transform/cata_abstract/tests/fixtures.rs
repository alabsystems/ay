// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

// Textually included by `cata_abstract::tests` so fixture helpers retain
// access to the parent test module's private imports.

/// Recursive `Lst = nil | cons(hd: Int, tl: Lst)`; the recursive tail field is
/// an `Uninterpreted("Lst")` self-reference, exactly as the parser leaves it.
fn list_sort() -> ChcSort {
    ChcSort::Datatype {
        name: "Lst".to_string(),
        constructors: Arc::new(vec![
            ChcDtConstructor {
                name: "nil".to_string(),
                selectors: vec![],
            },
            ChcDtConstructor {
                name: "cons".to_string(),
                selectors: vec![
                    ChcDtSelector {
                        name: "hd".to_string(),
                        sort: ChcSort::Int,
                    },
                    ChcDtSelector {
                        name: "tl".to_string(),
                        sort: ChcSort::Uninterpreted("Lst".to_string()),
                    },
                ],
            },
        ]),
    }
}

fn lst_var(name: &str) -> ChcVar {
    ChcVar::new(name, list_sort())
}

fn nil() -> ChcExpr {
    ChcExpr::FuncApp("nil".to_string(), list_sort(), vec![])
}

fn cons(hd: ChcExpr, tl: ChcExpr) -> ChcExpr {
    ChcExpr::FuncApp(
        "cons".to_string(),
        list_sort(),
        vec![Arc::new(hd), Arc::new(tl)],
    )
}

/// `R(x, y)` relating equal-shape lists:
///   x = nil ∧ y = nil                     ⇒ R(x, y)
///   R(x, y) ∧ x' = cons(a,x) ∧ y' = cons(b,y) ⇒ R(x', y')
///   R(x, y) ∧ x = nil ∧ y = cons(c, d)    ⇒ false          (SAFE)
fn equal_shape_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let r = problem.declare_predicate("R", vec![list_sort(), list_sort()]);

    let x = lst_var("x");
    let y = lst_var("y");
    let xp = lst_var("xp");
    let yp = lst_var("yp");
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);
    let c = ChcVar::new("c", ChcSort::Int);
    let d = lst_var("d");

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x.clone()), nil()),
            ChcExpr::eq(ChcExpr::var(y.clone()), nil()),
        )),
        ClauseHead::Predicate(r, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(r, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())])],
            Some(ChcExpr::and(
                ChcExpr::eq(
                    ChcExpr::var(xp.clone()),
                    cons(ChcExpr::var(a), ChcExpr::var(x.clone())),
                ),
                ChcExpr::eq(
                    ChcExpr::var(yp.clone()),
                    cons(ChcExpr::var(b), ChcExpr::var(y.clone())),
                ),
            )),
        ),
        ClauseHead::Predicate(r, vec![ChcExpr::var(xp), ChcExpr::var(yp)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(r, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())])],
            Some(ChcExpr::and(
                ChcExpr::eq(ChcExpr::var(x), nil()),
                ChcExpr::eq(ChcExpr::var(y), cons(ChcExpr::var(c), ChcExpr::var(d))),
            )),
        ),
        ClauseHead::False,
    ));
    problem
}
