// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for the catamorphism-abstraction adaptive route.

use std::sync::{Arc, Mutex, OnceLock};
use std::time::Duration;

use crate::adaptive::{AdaptiveConfig, AdaptivePortfolio};
use crate::engine_result::ValidationEvidence;
use crate::portfolio::PortfolioResult;
use crate::{
    ChcDtConstructor, ChcDtSelector, ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead,
    HornClause, VerifiedChcResult,
};

/// The route reads `AY_CHC_DISABLE_CATA` from the process environment, so
/// every test in this module serializes through one lock to keep the
/// kill-switch test from perturbing concurrently running route tests.
fn env_lock() -> &'static Mutex<()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

/// Serialize route tests; recover from a poisoned lock (a panicking sibling
/// test must not cascade into spurious PoisonError failures here).
fn env_guard() -> std::sync::MutexGuard<'static, ()> {
    env_lock()
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

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

/// SAFE: R relates equal-shape lists; the query needs the recursive invariant
/// `size(x) = size(y)`, which depth-bounded flattening cannot express.
fn equal_shape_safe_problem() -> ChcProblem {
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

/// SAFE, but the base {Size, RootDisc} abstraction has a SPURIOUS abstract
/// counterexample: P holds exactly of `cons(1, nil)` and the query asks for
/// `cons(2, nil)` — same size, same root constructor, different head value.
/// A naive lane that trusted the abstract UNSAT would answer `unsat` (WRONG).
fn spurious_abstract_unsat_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![list_sort()]);
    let v = lst_var("v");
    let x = lst_var("x");
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(
            ChcExpr::var(v.clone()),
            cons(ChcExpr::int(1), nil()),
        )),
        ClauseHead::Predicate(p, vec![ChcExpr::var(v)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(x), cons(ChcExpr::int(2), nil()))),
        ),
        ClauseHead::False,
    ));
    problem
}

/// UNSAFE: `P` holds of every list (nil ∈ P; cons(a,x) ∈ P if x ∈ P), and the
/// query `P(x) ∧ x = cons(5, nil) ⇒ false` is genuinely reachable (`[5] ∈ P`).
/// A size-only abstraction is coarse — it cannot see the element `5` — but it
/// must STILL never prove this Safe: the abstraction over-approximates, so the
/// abstract system is also unsafe (`size = 2` is reachable), Houdini cannot
/// prove it, and no certified Safe can be produced. This is the CRITICAL
/// no-false-Safe adversarial pin for CATA v2.
fn all_lists_unsafe_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![list_sort()]);
    let x = lst_var("x");
    let a = ChcVar::new("a", ChcSort::Int);
    let xp = lst_var("xp");
    // nil ∈ P
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), nil())),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));
    // P(x) ∧ xp = cons(a, x) ⇒ P(xp)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(xp.clone()),
                cons(ChcExpr::var(a), ChcExpr::var(x.clone())),
            )),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::var(xp)]),
    ));
    // P(x) ∧ x = cons(5, nil) ⇒ false  (REACHABLE: [5] ∈ P)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(x), cons(ChcExpr::int(5), nil()))),
        ),
        ClauseHead::False,
    ));
    problem
}

/// UNSAFE, sortedness-flavoured: `Q` holds of EVERY list, and the query
/// `Q(l) ∧ l = cons(a, cons(b, t)) ∧ a > b ⇒ false` claims no Q-list has a
/// descending adjacent pair — i.e. a broken "everything is sorted" property.
/// `[2,1] ∈ Q` with `2 > 1` makes it genuinely reachable. The `Sorted`/`Min`
/// catamorphisms MUST NOT let this be proved Safe: the abstraction
/// over-approximates, so `sorted = 0` states remain reachable in the abstract
/// system and no certified Safe can be produced. CATA v3 no-false-Safe pin.
fn broken_sortedness_unsafe_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let q = problem.declare_predicate("Q", vec![list_sort()]);
    let x = lst_var("x");
    let xp = lst_var("xp");
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);
    let t = lst_var("t");
    let l = lst_var("l");
    // nil ∈ Q
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), nil())),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
    ));
    // Q(x) ∧ xp = cons(a, x) ⇒ Q(xp)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(xp.clone()),
                cons(ChcExpr::var(a.clone()), ChcExpr::var(x.clone())),
            )),
        ),
        ClauseHead::Predicate(q, vec![ChcExpr::var(xp)]),
    ));
    // Q(l) ∧ l = cons(a, cons(b, t)) ∧ a > b ⇒ false   (REACHABLE: [2,1] ∈ Q)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(l.clone())])],
            Some(ChcExpr::and(
                ChcExpr::eq(
                    ChcExpr::var(l),
                    cons(
                        ChcExpr::var(a.clone()),
                        cons(ChcExpr::var(b.clone()), ChcExpr::var(t)),
                    ),
                ),
                ChcExpr::gt(ChcExpr::var(a), ChcExpr::var(b)),
            )),
        ),
        ClauseHead::False,
    ));
    problem
}

fn route_solver(problem: ChcProblem) -> AdaptivePortfolio {
    let config = AdaptiveConfig::with_budget(Duration::from_secs(30), false);
    AdaptivePortfolio::new(problem, config)
}

/// Stage diagnostic: the L0 abstract LIA system of the equal-shape problem
/// must be PDR-solvable, its model must fresh-verify, and composition must
/// succeed — these pin each stage the route depends on.
#[test]
fn cata_abstract_stages_work_for_equal_shape() {
    use crate::transform::cata_abstract::{CataAbstraction, CataKind};
    let problem = equal_shape_safe_problem();
    let abstraction = CataAbstraction::build(&problem, &[CataKind::Size, CataKind::RootDisc])
        .expect("abstraction applies");
    assert!(
        abstraction.discharge_obligations(Duration::from_secs(5), None),
        "stage 1: obligations"
    );

    let nested = AdaptivePortfolio::new(
        abstraction.abstract_problem.clone(),
        AdaptiveConfig::with_budget(Duration::from_secs(20), false),
    );
    let VerifiedChcResult::Safe(verified) = nested.solve() else {
        panic!("stage 2: nested adaptive solve did not prove the abstract system Safe");
    };
    let abstract_model = verified.into_inner();

    let verify_config = crate::pdr::PdrConfig {
        strict_proofs: true,
        solve_timeout: Some(Duration::from_secs(10)),
        ..crate::pdr::PdrConfig::default()
    };
    assert!(
        matches!(
            crate::engines::validate_external_invariant_model(
                &abstraction.abstract_problem,
                &abstract_model,
                &verify_config,
            ),
            Ok(true)
        ),
        "stage 3: abstract model fresh verification"
    );

    assert!(
        abstraction.compose_model(&abstract_model).is_some(),
        "stage 4: composition"
    );
}

#[test]
fn cata_route_certifies_equal_shape_list_problem_safe() {
    let _guard = env_guard();
    let solver = route_solver(equal_shape_safe_problem());
    let result = solver.try_cata_abstraction_route(None);
    match result {
        Some((PortfolioResult::Safe(model), evidence)) => {
            match evidence {
                ValidationEvidence::CataAbstraction {
                    pool_size,
                    obligations_discharged,
                } => {
                    // The ladder's leanest level is {Size} (pool_size == 1);
                    // {Size, RootDisc} is the next refinement. Since the
                    // per-conjunct obligation discharge now certifies the
                    // over-approximation at the leanest level that admits a
                    // re-verified safe invariant (the monolithic `¬(⋀ θ#)`
                    // discharge previously stalled to `unknown` on the {Size}
                    // level and forced a needless refinement), the equal-shape
                    // problem certifies at {Size}. The certification is
                    // re-verified sound — see the sibling
                    // `cata_route_safe_survives_finalize_boundary`, which admits
                    // this exact model through the finalize re-proof.
                    assert!(pool_size >= 1, "at least the {{size}} column");
                    assert_eq!(obligations_discharged, 3, "one per original clause");
                }
                other => panic!("expected CataAbstraction evidence, got {other:?}"),
            }
            // The composed model interprets the original predicate over its
            // ORIGINAL (datatype-sorted) signature.
            let interp = model
                .get(&solver.problem().predicates()[0].id)
                .expect("original predicate interpreted");
            assert!(matches!(interp.vars[0].sort, ChcSort::Datatype { .. }));
            let smt = crate::InvariantModel::expr_to_smtlib(&interp.formula);
            assert!(smt.contains("cata_"), "formula: {smt}");
        }
        other => panic!("expected certified Safe from the cata route, got {other:?}"),
    }
}

#[test]
fn cata_route_safe_survives_finalize_boundary() {
    let _guard = env_guard();
    let solver = route_solver(equal_shape_safe_problem());
    let Some((result, evidence)) = solver.try_cata_abstraction_route(None) else {
        panic!("cata route did not certify the equal-shape problem");
    };
    let verified = solver.finalize_verified_result(result, evidence);
    assert!(
        matches!(verified, VerifiedChcResult::Safe(_)),
        "finalize must admit CataAbstraction-certified Safe, got {verified}"
    );
}

/// SOUNDNESS REGRESSION: the abstract system has a counterexample that is
/// INFEASIBLE on the original clauses. A naive catamorphism lane would report
/// `unsat` — a wrong verdict. This route must never do that: it either
/// refines to a pool that certifies SAFE, or withholds (returns None).
#[test]
fn cata_route_never_reports_spurious_abstract_unsat() {
    let _guard = env_guard();
    let solver = route_solver(spurious_abstract_unsat_problem());
    let result = solver.try_cata_abstraction_route(None);
    match &result {
        Some((PortfolioResult::Unsafe(_), _)) => {
            panic!("cata route reported the SPURIOUS abstract counterexample as unsat")
        }
        Some((PortfolioResult::Safe(_), _)) | None => {
            // Correct: either the IntSum refinement certified SAFE, or the
            // lane withheld. Both are sound.
        }
        Some((other, _)) => panic!("unexpected route result {other:?}"),
    }
}

/// CRITICAL no-false-Safe adversarial pin (CATA v2): a genuinely UNSAFE ADT
/// problem whose unsafety is invisible to the (size) abstraction must NEVER be
/// reported Safe. The abstraction over-approximates ⇒ the abstract system is
/// also unsafe ⇒ the affine Houdini cannot prove it ⇒ no certified Safe. The
/// route may return None (withhold) or a CONCRETE Unsafe (via original-clause
/// BMC), but never Safe.
#[test]
fn cata_route_never_reports_false_safe_on_unsafe_problem() {
    let _guard = env_guard();
    let solver = route_solver(all_lists_unsafe_problem());
    match solver.try_cata_abstraction_route(None) {
        Some((PortfolioResult::Safe(_), _)) => {
            panic!("CATA v2 reported a FALSE Safe on a genuinely unsafe problem")
        }
        Some((PortfolioResult::Unsafe(_), _)) | None => {
            // Sound: either a concrete counterexample or withheld.
        }
        Some((other, _)) => panic!("unexpected route result {other:?}"),
    }
}

/// CRITICAL no-false-Safe adversarial pin (CATA v3, ordering): a genuinely
/// UNSAFE problem whose property is a BROKEN sortedness claim ("no Q-list has a
/// descending pair", but `[2,1] ∈ Q`) must NEVER be reported Safe, even with
/// the `Sorted`/`Min` catamorphisms engaged. The obligations certify only the
/// SAT direction; concretization/over-approximation keeps the unsafety visible.
#[test]
fn cata_route_never_reports_false_safe_on_broken_sortedness() {
    let _guard = env_guard();
    // The CATA v3 element/ordering levels are on by default, so the route
    // exercises the `Sorted`/`Min` catamorphisms on this problem. Guard against
    // a sibling test leaving the opt-out kill switch set.
    std::env::remove_var("AY_CHC_DISABLE_CATA_ELEMENTS");
    let solver = route_solver(broken_sortedness_unsafe_problem());
    let outcome = solver.try_cata_abstraction_route(None);
    match outcome {
        Some((PortfolioResult::Safe(_), _)) => {
            panic!("CATA v3 reported a FALSE Safe on a broken-sortedness unsafe problem")
        }
        Some((PortfolioResult::Unsafe(_), _)) | None => {
            // Sound: concrete counterexample or withheld.
        }
        Some((other, _)) => panic!("unexpected route result {other:?}"),
    }
}

#[test]
fn cata_route_respects_kill_switch() {
    let _guard = env_guard();
    std::env::set_var("AY_CHC_DISABLE_CATA", "1");
    let solver = route_solver(equal_shape_safe_problem());
    let result = solver.try_cata_abstraction_route(None);
    std::env::remove_var("AY_CHC_DISABLE_CATA");
    assert!(result.is_none(), "kill switch must disable the cata lane");
}

#[test]
fn cata_route_skips_non_recursive_datatype_problems() {
    let _guard = env_guard();
    // Pair(Int, Int) — non-recursive: dt_flatten territory, not cata.
    let pair_sort = ChcSort::Datatype {
        name: "Pair".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mk".to_string(),
            selectors: vec![
                ChcDtSelector {
                    name: "fst".to_string(),
                    sort: ChcSort::Int,
                },
                ChcDtSelector {
                    name: "snd".to_string(),
                    sort: ChcSort::Int,
                },
            ],
        }]),
    };
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![pair_sort.clone()]);
    let x = ChcVar::new("x", pair_sort);
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(x)])], None),
        ClauseHead::False,
    ));
    let solver = route_solver(problem);
    assert!(
        solver.try_cata_abstraction_route(None).is_none(),
        "non-recursive datatype problems keep the exact DtFlattener pipeline"
    );
}
