// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for the catamorphism abstraction (CATA v1).

use std::sync::Arc;
use std::time::Duration;

use super::*;
use crate::{ChcDtConstructor, ChcDtSelector};

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

#[test]
fn ladder_is_nonempty_for_recursive_list_problem() {
    // Default (v2) ladder: element/ordering levels off.
    let ladder = build_cata_ladder(&equal_shape_problem(), false);
    assert!(!ladder.is_empty());
    // Level 0 is the lean {Size}-only base pool (CATA v2); RootDisc is L1.
    assert_eq!(
        ladder[0],
        vec![CataKind::Size],
        "base pool must be size only (lean L0)"
    );
    assert_eq!(
        ladder[1],
        vec![CataKind::Size, CataKind::RootDisc],
        "L1 adds the root discriminant"
    );
    // Int head fields exist, so an IntSum refinement level must follow.
    assert!(ladder.iter().any(|pool| pool.contains(&CataKind::IntSum)));
}

#[test]
fn abstraction_builds_datatype_free_lia_problem() {
    let problem = equal_shape_problem();
    let pool = vec![CataKind::Size, CataKind::RootDisc];
    let abstraction = CataAbstraction::build(&problem, &pool).expect("abstraction applies");

    assert!(!abstraction.abstract_problem.has_datatype_sorts());
    let r = &abstraction.abstract_problem.predicates()[0];
    // Two ADT args × two catamorphisms.
    assert_eq!(r.arity(), 4);
    assert!(r.arg_sorts.iter().all(|s| *s == ChcSort::Int));
    assert_eq!(
        abstraction.obligations.len(),
        problem.clauses().len(),
        "one implication obligation per original clause"
    );
    assert_eq!(
        abstraction.abstract_problem.clauses().len(),
        problem.clauses().len()
    );
}

#[test]
fn obligation_scripts_declare_unreserved_cata_symbols() {
    // The frontend elaborator rejects `__ay_`-prefixed declarations, so the
    // obligation scripts must never use that prefix for the catamorphism UFs.
    let problem = equal_shape_problem();
    let pool = vec![CataKind::Size, CataKind::RootDisc];
    let abstraction = CataAbstraction::build(&problem, &pool).expect("abstraction applies");
    for script in abstraction.obligation_scripts() {
        assert!(!script.contains("__ay_"), "reserved prefix in: {script}");
        assert!(script.contains("cata_size@Lst"));
    }
}

#[test]
fn obligations_discharge_on_supported_clauses() {
    let problem = equal_shape_problem();
    let pool = vec![CataKind::Size, CataKind::RootDisc];
    let abstraction = CataAbstraction::build(&problem, &pool).expect("abstraction applies");
    assert!(
        abstraction.discharge_obligations(Duration::from_secs(5), None),
        "well-formed abstraction obligations must discharge unsat"
    );
}

#[test]
fn obligations_discharge_with_full_pool() {
    let problem = equal_shape_problem();
    let pool = vec![
        CataKind::Size,
        CataKind::RootDisc,
        CataKind::IntSum,
        CataKind::CtorCount("cons".to_string()),
        CataKind::CtorCount("nil".to_string()),
        CataKind::Height,
    ];
    let abstraction = CataAbstraction::build(&problem, &pool).expect("abstraction applies");
    assert!(
        abstraction.discharge_obligations(Duration::from_secs(8), None),
        "full-pool obligations must discharge unsat"
    );
}

/// SOUNDNESS PIN: a corrupted abstraction (wrong size recurrence, the classic
/// off-by-one a naive implementation could ship) must FAIL the obligation
/// check — the fail-closed gate is what keeps a buggy transform from ever
/// producing a wrong verdict.
#[test]
fn poisoned_recurrence_fails_obligation_check() {
    let problem = equal_shape_problem();
    let pool = vec![CataKind::Size, CataKind::RootDisc];
    let abstraction = CataAbstraction::build(&problem, &pool).expect("abstraction applies");

    // Clause 1 is the cons/cons transition: its θ# contains size recurrences
    // of the form `(= c (+ 1 c_sub))`. Poison ONLY the negated θ# (the final
    // `(assert (not …))`), leaving the true catamorphism facts intact — this
    // simulates a transform that emits `size(cons(h,t)) = 2 + size(t)`.
    let script = &abstraction.obligations[1].script;
    let marker = "(assert (not ";
    let split = script.rfind(marker).expect("script has a negated theta#");
    let (facts, negated) = script.split_at(split);
    assert!(
        negated.contains("(+ 1 "),
        "transition theta# must contain a size recurrence to poison"
    );
    let poisoned = format!("{facts}{}", negated.replace("(+ 1 ", "(+ 2 "));

    assert!(
        run_obligation_expect_unsat(script, Duration::from_secs(5)),
        "sanity: unpoisoned obligation discharges"
    );
    assert!(
        !run_obligation_expect_unsat(&poisoned, Duration::from_secs(5)),
        "poisoned recurrence MUST fail the implication obligation (fail-closed)"
    );
}

#[test]
fn compose_model_materializes_cata_funcapps_without_free_vars() {
    let problem = equal_shape_problem();
    let pool = vec![CataKind::Size, CataKind::RootDisc];
    let abstraction = CataAbstraction::build(&problem, &pool).expect("abstraction applies");

    // Abstract invariant: size(x) = size(y) (the real equal-shape invariant).
    let abs_vars: Vec<ChcVar> = (0..4)
        .map(|i| ChcVar::new(format!("v{i}"), ChcSort::Int))
        .collect();
    let formula = ChcExpr::eq(
        ChcExpr::var(abs_vars[0].clone()),
        ChcExpr::var(abs_vars[2].clone()),
    );
    let mut abstract_model = InvariantModel::new();
    abstract_model.set(
        problem.predicates()[0].id,
        PredicateInterpretation::new(abs_vars, formula),
    );

    let composed = abstraction
        .compose_model(&abstract_model)
        .expect("composition succeeds");
    let interp = composed
        .get(&problem.predicates()[0].id)
        .expect("original predicate interpreted");

    // Binder vars follow the canonical original signature.
    assert_eq!(interp.vars.len(), 2);
    assert_eq!(interp.vars[0].name, "__p0_a0");
    assert!(matches!(interp.vars[0].sort, ChcSort::Datatype { .. }));

    // The formula mentions the reserved catamorphism symbol and has no free
    // variables beyond the binders (capture-soundness requirement of
    // verify_model).
    let smt = InvariantModel::expr_to_smtlib(&interp.formula);
    assert!(smt.contains("cata_size@Lst"), "formula: {smt}");
    let binder_names: Vec<&str> = interp.vars.iter().map(|v| v.name.as_str()).collect();
    for var in interp.formula.vars() {
        assert!(
            binder_names.contains(&var.name.as_str()),
            "free variable {} in composed interpretation",
            var.name
        );
    }
}

/// The cata-aware query gate must certify a composed model that genuinely
/// excludes the error (size(x)=size(y) against the nil-vs-cons query) and
/// reject one that does not — both directions of the final CLI gate.
#[test]
fn cata_query_gate_certifies_strong_and_rejects_weak_composed_models() {
    let problem = equal_shape_problem();
    let pool = vec![CataKind::Size, CataKind::RootDisc];
    let abstraction = CataAbstraction::build(&problem, &pool).expect("abstraction applies");

    // Strong abstract invariant: size(x) = size(y).
    let abs_vars: Vec<ChcVar> = (0..4)
        .map(|i| ChcVar::new(format!("v{i}"), ChcSort::Int))
        .collect();
    let mut strong = InvariantModel::new();
    strong.set(
        problem.predicates()[0].id,
        PredicateInterpretation::new(
            abs_vars.clone(),
            ChcExpr::eq(
                ChcExpr::var(abs_vars[0].clone()),
                ChcExpr::var(abs_vars[2].clone()),
            ),
        ),
    );
    let composed_strong = abstraction.compose_model(&strong).expect("composes");
    assert!(
        cata_model_excludes_error(&problem, &composed_strong, Duration::from_secs(5), None),
        "strong composed model must discharge every query clause"
    );

    // Weak abstract invariant: `size(x) >= 1` is TRUE of every list, so it
    // cannot exclude the error — the gate must refuse (a naive gate that
    // rubber-stamps cata models would return true here).
    let mut weak = InvariantModel::new();
    weak.set(
        problem.predicates()[0].id,
        PredicateInterpretation::new(
            abs_vars.clone(),
            ChcExpr::ge(ChcExpr::var(abs_vars[0].clone()), ChcExpr::int(1)),
        ),
    );
    let composed_weak = abstraction.compose_model(&weak).expect("composes");
    assert!(
        !cata_model_excludes_error(&problem, &composed_weak, Duration::from_secs(5), None),
        "weak composed model must NOT pass the query gate (fail-closed)"
    );

    // Non-cata models are out of scope for this gate entirely.
    let mut scalar = InvariantModel::new();
    scalar.set(
        problem.predicates()[0].id,
        PredicateInterpretation::new(abs_vars, ChcExpr::Bool(true)),
    );
    assert!(!cata_model_excludes_error(
        &problem,
        &scalar,
        Duration::from_secs(2),
        None
    ));
}

#[test]
fn cata_symbol_roundtrips_through_parse() {
    for kind in [
        CataKind::Size,
        CataKind::Height,
        CataKind::IntSum,
        CataKind::RootDisc,
        CataKind::CtorCount("cons".to_string()),
        // CATA v3 element / ordering catamorphisms.
        CataKind::Min,
        CataKind::Max,
        CataKind::Sorted,
    ] {
        let name = kind.uf_name("Lst");
        let (parsed, sort) = CataKind::parse_symbol(&name).expect("parses");
        assert_eq!(parsed, kind);
        assert_eq!(sort, "Lst");
    }
    assert!(CataKind::parse_symbol("not_a_cata").is_none());
    assert!(CataKind::parse_symbol("cata_bogus@Lst").is_none());
}

// ── CATA v3: element / ordering catamorphisms ──────────────────────────────

/// The ladder synthesizes the element (`Min`/`Max`) and ordering (`Sorted`)
/// levels for an int-list problem, and `Sorted` is always accompanied by
/// `Min` (its recurrence references the min column of the recursive field).
#[test]
fn element_cata_ladder_includes_min_max_and_sorted() {
    // Element/ordering levels are opt-in (CATA v3).
    let ladder = build_cata_ladder(&equal_shape_problem(), true);
    let min_max_level = ladder
        .iter()
        .find(|p| p.contains(&CataKind::Min) && p.contains(&CataKind::Max))
        .expect("ladder has a min/max element level");
    assert!(!min_max_level.contains(&CataKind::Sorted));

    let sorted_level = ladder
        .iter()
        .find(|p| p.contains(&CataKind::Sorted))
        .expect("int-list problem gets a sortedness level");
    assert!(
        sorted_level.contains(&CataKind::Min),
        "Sorted must be paired with Min (its recurrence needs the min column)"
    );
}

/// Min/Max obligations discharge on the equal-shape (cons/cons + nil) problem:
/// the min/max recurrences instantiated at the `cons(a, x)` terms are true
/// facts of the real catamorphisms, so `θ ⇒ θ#` holds.
#[test]
fn min_max_obligations_discharge() {
    let problem = equal_shape_problem();
    let pool = vec![
        CataKind::Size,
        CataKind::RootDisc,
        CataKind::IntSum,
        CataKind::Min,
        CataKind::Max,
    ];
    let abstraction = CataAbstraction::build(&problem, &pool).expect("abstraction applies");
    assert!(
        abstraction.discharge_obligations(Duration::from_secs(8), None),
        "min/max element obligations must discharge unsat"
    );
    // The cons/cons transition constraint must carry the min recurrence (an
    // ite over the head vs the recursive min column).
    let smt = InvariantModel::expr_to_smtlib(
        abstraction.abstract_problem.clauses()[1]
            .body
            .constraint
            .as_ref()
            .expect("transition has a constraint"),
    );
    assert!(
        smt.contains("cata_min") || smt.contains("ite"),
        "min recurrence missing: {smt}"
    );
}

/// The sortedness fold (with its required `Min` column) discharges: the
/// `sorted(cons(a,x)) = ite(a ≤ min(x) ∧ sorted(x)=1, 1, 0)` recurrence and the
/// `Min` recurrence it references are both true facts.
#[test]
fn sorted_fold_obligations_discharge() {
    let problem = equal_shape_problem();
    let pool = vec![
        CataKind::Size,
        CataKind::RootDisc,
        CataKind::Min,
        CataKind::Sorted,
    ];
    let abstraction = CataAbstraction::build(&problem, &pool).expect("abstraction applies");
    assert!(
        abstraction.discharge_obligations(Duration::from_secs(10), None),
        "sortedness-fold obligations must discharge unsat"
    );
    // Every obligation script declares BOTH the sorted UF and the min UF it
    // references (else the sorted recurrence would mention an undeclared sym).
    for script in abstraction.obligation_scripts() {
        if script.contains("cata_sorted@Lst") {
            assert!(
                script.contains("cata_min@Lst"),
                "sorted recurrence references cata_min but it is not declared: {script}"
            );
        }
    }
}

/// SOUNDNESS PIN (ordering): a broken sortedness claim — a transform that
/// asserts `sorted(cons(a,x)) = 1` UNCONDITIONALLY (dropping the head-vs-rest
/// guard) — MUST fail the fail-closed obligation gate. This is the property
/// that keeps a bogus ordering abstraction from ever yielding a wrong Safe.
#[test]
fn poisoned_sorted_recurrence_fails_obligation_check() {
    let problem = equal_shape_problem();
    let pool = vec![
        CataKind::Size,
        CataKind::RootDisc,
        CataKind::Min,
        CataKind::Sorted,
    ];
    let abstraction = CataAbstraction::build(&problem, &pool).expect("abstraction applies");

    // Clause 1 (cons/cons transition) has the sortedness recurrence in θ#. The
    // recurrence RHS is `(ite <guard> 1 0)`; poison ONLY the negated θ# by
    // turning the else-branch `1 0)` into `1 1)`, i.e. asserting sortedness
    // holds even on a descent — a classic unsound ordering shortcut.
    let script = &abstraction.obligations[1].script;
    let marker = "(assert (not ";
    let split = script.rfind(marker).expect("script has a negated theta#");
    let (facts, negated) = script.split_at(split);
    assert!(
        negated.contains("1 0)"),
        "transition theta# must contain a sortedness ite to poison: {negated}"
    );
    let poisoned = format!("{facts}{}", negated.replace("1 0)", "1 1)"));

    assert!(
        run_obligation_expect_unsat(script, Duration::from_secs(6)),
        "sanity: unpoisoned sortedness obligation discharges"
    );
    assert!(
        !run_obligation_expect_unsat(&poisoned, Duration::from_secs(6)),
        "poisoned (unconditional) sortedness MUST fail the obligation (fail-closed)"
    );
}

/// A directly-constructed FALSE sortedness claim is not certifiable: asserting
/// `sorted([2,1]) = 1` alongside the true `Min`/`Sorted` recurrences is SAT for
/// `¬θ#`, so `run_obligation_expect_unsat` refuses it. This pins the semantics
/// of the fold independently of the abstraction plumbing: an unsorted list can
/// NEVER be certified sorted.
#[test]
fn false_sortedness_fact_is_rejected() {
    // θ# claims sorted(cons(2, cons(1, nil))) = 1 (FALSE: 2 > 1 is a descent).
    // The script asserts the real recurrences + ¬θ#; expected SAT ⇒ NOT
    // dischargeable ⇒ the gate rejects the false claim.
    let script = "\
(set-logic ALL)
(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
(declare-fun |cata_min@Lst| (Lst) Int)
(declare-fun |cata_sorted@Lst| (Lst) Int)
(assert (= (|cata_min@Lst| nil) 1000000000))
(assert (= (|cata_min@Lst| (cons 1 nil)) (ite (<= 1 (|cata_min@Lst| nil)) 1 (|cata_min@Lst| nil))))
(assert (= (|cata_min@Lst| (cons 2 (cons 1 nil))) \
  (ite (<= 2 (|cata_min@Lst| (cons 1 nil))) 2 (|cata_min@Lst| (cons 1 nil)))))
(assert (= (|cata_sorted@Lst| nil) 1))
(assert (= (|cata_sorted@Lst| (cons 1 nil)) \
  (ite (and (<= 1 (|cata_min@Lst| nil)) (= (|cata_sorted@Lst| nil) 1)) 1 0)))
(assert (= (|cata_sorted@Lst| (cons 2 (cons 1 nil))) \
  (ite (and (<= 2 (|cata_min@Lst| (cons 1 nil))) (= (|cata_sorted@Lst| (cons 1 nil)) 1)) 1 0)))
; ¬θ# where θ# is the FALSE claim sorted([2,1]) = 1
(assert (not (= (|cata_sorted@Lst| (cons 2 (cons 1 nil))) 1)))
(check-sat)
";
    assert!(
        !run_obligation_expect_unsat(script, Duration::from_secs(6)),
        "an unsorted list must NEVER certify sorted=1 (fold semantics pin)"
    );
}

/// CATA v2 depth-1 GUARDED families: `column_tags` derives the per-column
/// semantic tags purely from the layout + pool. For the ISortSorts
/// `insert_17(list, Int, list)` shape under the sortedness pool
/// `[Size, RootDisc, Min, Sorted]` the tags are
/// `[g0:Size,RootDisc,Min,Sorted | scalar F | g2:Size,RootDisc,Min,Sorted]`.
#[test]
fn column_tags_match_insert_layout() {
    let mut problem = ChcProblem::new();
    let insert = problem.declare_predicate("insert", vec![list_sort(), ChcSort::Int, list_sort()]);
    let b = ChcVar::new("b", ChcSort::Int);
    // A trivial fact so the abstraction has a clause to translate.
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(
            insert,
            vec![cons(ChcExpr::var(b.clone()), nil()), ChcExpr::var(b), nil()],
        ),
    ));

    let pool = vec![
        CataKind::Size,
        CataKind::RootDisc,
        CataKind::Min,
        CataKind::Sorted,
    ];
    let abstraction = CataAbstraction::build(&problem, &pool).expect("abstraction applies");
    let tags = abstraction.column_tags(insert);

    let cata = |k: CataKind, group: usize| ColumnTag {
        kind: Some(k),
        group,
        scalar_int: false,
    };
    let expected = vec![
        cata(CataKind::Size, 0),
        cata(CataKind::RootDisc, 0),
        cata(CataKind::Min, 0),
        cata(CataKind::Sorted, 0),
        ColumnTag {
            kind: None,
            group: 1,
            scalar_int: true,
        },
        cata(CataKind::Size, 2),
        cata(CataKind::RootDisc, 2),
        cata(CataKind::Min, 2),
        cata(CataKind::Sorted, 2),
    ];
    assert_eq!(tags, expected, "insert_17 column tags");

    // The abstract signature is index-aligned with the tags (9 columns).
    assert_eq!(
        abstraction.abstract_problem.predicates()[insert.index()].arity(),
        tags.len()
    );
}

#[test]
fn compose_model_fails_closed_on_missing_interpretation() {
    let problem = equal_shape_problem();
    let pool = vec![CataKind::Size, CataKind::RootDisc];
    let abstraction = CataAbstraction::build(&problem, &pool).expect("abstraction applies");
    // Empty abstract model: composition must refuse (fail-closed), not invent.
    assert!(abstraction.compose_model(&InvariantModel::new()).is_none());
}

#[test]
fn transformer_reports_original_validation_obligations() {
    let problem = equal_shape_problem();
    let result = Box::new(CataAbstractor::new(vec![
        CataKind::Size,
        CataKind::RootDisc,
    ]))
    .transform(problem);
    let memory = result.back_translator.transform_memory();
    assert!(memory.has_obligation("cata_clause_implication_0"));
    assert!(!memory.unsafe_backtranslation_complete());
    assert!(!memory.is_identity_grade());
}

#[test]
fn tester_and_disequality_conjuncts_are_abstracted() {
    // P(x) with a fact guarded by `x ≠ nil` (two-ctor sort → cons
    // consequences) and a query guarded by a tester.
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![list_sort()]);
    let x = lst_var("x");
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::ne(ChcExpr::var(x.clone()), nil())),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::FuncApp(
                "is-nil".to_string(),
                ChcSort::Bool,
                vec![Arc::new(ChcExpr::var(x.clone()))],
            )),
        ),
        ClauseHead::False,
    ));

    let pool = vec![CataKind::Size, CataKind::RootDisc];
    let abstraction = CataAbstraction::build(&problem, &pool).expect("abstraction applies");
    assert!(
        abstraction.discharge_obligations(Duration::from_secs(5), None),
        "tester/disequality obligations must discharge"
    );
    // `x ≠ nil` on a two-constructor sort is NOT dropped — it becomes cons
    // consequences (size ≥ 2 …), so nothing should be counted as weakened.
    assert_eq!(abstraction.dropped_conjuncts, 0);

    // The abstract fact clause must constrain size ≥ 2 (cons consequence):
    // the abstract system with query `is-nil` (size = 1) must be SAFE, which
    // PDR-level tests cover; here we just check the constraint text.
    let fact = &abstraction.abstract_problem.clauses()[0];
    let constraint = fact.body.constraint.as_ref().expect("has constraint");
    let smt = InvariantModel::expr_to_smtlib(constraint);
    assert!(smt.contains(">= "), "cons consequence missing: {smt}");
}

#[test]
fn general_adt_disequality_is_weakened_not_rejected() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![list_sort(), list_sort()]);
    let x = lst_var("x");
    let y = lst_var("y");
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::ne(
            ChcExpr::var(x.clone()),
            ChcExpr::var(y.clone()),
        )),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x), ChcExpr::var(y)]),
    ));

    let pool = vec![CataKind::Size, CataKind::RootDisc];
    let abstraction = CataAbstraction::build(&problem, &pool).expect("abstraction applies");
    assert_eq!(abstraction.dropped_conjuncts, 1, "diseq weakened to true");
    assert!(
        abstraction.discharge_obligations(Duration::from_secs(5), None),
        "weakened clause obligation still discharges (theta# is weaker)"
    );
}

#[test]
fn unsupported_argument_sort_is_skipped() {
    let mut problem = ChcProblem::new();
    problem.declare_predicate(
        "P",
        vec![ChcSort::Array(
            Box::new(ChcSort::Int),
            Box::new(list_sort()),
        )],
    );
    let x = ChcVar::new(
        "x",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(list_sort())),
    );
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(
            ChcExpr::var(x.clone()),
            ChcExpr::var(x.clone()),
        )),
        ClauseHead::Predicate(PredicateId::new(0), vec![ChcExpr::var(x)]),
    ));
    assert!(matches!(
        CataAbstraction::build(&problem, &[CataKind::Size, CataKind::RootDisc]),
        Err(CataSkip::UnsupportedArgumentSort(_))
    ));
}

#[test]
fn nested_constructor_terms_get_exact_recurrences() {
    // Head uses a nested constructor term: P(cons(a, cons(b, nil))).
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![list_sort()]);
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(p, vec![cons(ChcExpr::var(a), cons(ChcExpr::var(b), nil()))]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(lst_var("x"))])], None),
        ClauseHead::False,
    ));

    let pool = vec![CataKind::Size, CataKind::RootDisc, CataKind::IntSum];
    let abstraction = CataAbstraction::build(&problem, &pool).expect("abstraction applies");
    assert!(
        abstraction.discharge_obligations(Duration::from_secs(5), None),
        "nested constructor obligations must discharge"
    );
    // The fact clause pins the tuple exactly: size = 3 must be derivable, so
    // the constraint mentions the recurrence chain (three tuples).
    let fact = &abstraction.abstract_problem.clauses()[0];
    let constraint = fact.body.constraint.as_ref().expect("has constraint");
    let smt = InvariantModel::expr_to_smtlib(constraint);
    assert!(smt.contains("__cata"), "recurrence chain missing: {smt}");
}

/// The disjunctive (exact predicate-abstraction) ICE learner finds a genuinely
/// DISJUNCTIVE invariant that the conjunctive affine Houdini provably cannot.
///
/// `P(a, b)` with two `{0,1}` flag columns, facts pinning it to `(0,0)` and
/// `(1,1)`, and error clauses on `(0,1)` and `(1,0)`. The only safety invariant
/// is `(a=0 ∧ b=0) ∨ (a=1 ∧ b=1)` — a disjunction of two minterms. A single
/// conjunction of the flag atoms cannot represent it (any atom true in one fact
/// is false in the other, so Houdini's greatest fixpoint collapses to `true`,
/// which does not exclude the errors).
#[test]
fn disjunctive_learner_solves_two_minterm_invariant() {
    use ay_core::kani_compat::DetHashMap;

    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);
    let va = || ChcExpr::var(a.clone());
    let vb = || ChcExpr::var(b.clone());
    let eq0 = |v: ChcExpr| ChcExpr::eq(v, ChcExpr::int(0));
    let eq1 = |v: ChcExpr| ChcExpr::eq(v, ChcExpr::int(1));

    // Facts: (a=0 ∧ b=0) ⇒ P ; (a=1 ∧ b=1) ⇒ P.
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(eq0(va()), eq0(vb()))),
        ClauseHead::Predicate(p, vec![va(), vb()]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(eq1(va()), eq1(vb()))),
        ClauseHead::Predicate(p, vec![va(), vb()]),
    ));
    // Errors: P ∧ a=0 ∧ b=1 ⇒ false ; P ∧ a=1 ∧ b=0 ⇒ false.
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![va(), vb()])],
            Some(ChcExpr::and(eq0(va()), eq1(vb()))),
        ),
        ClauseHead::False,
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![va(), vb()])],
            Some(ChcExpr::and(eq1(va()), eq0(vb()))),
        ),
        ClauseHead::False,
    ));

    // Tag both columns as flags so the learner mines `= 0` / `= 1` atoms.
    let tags: DetHashMap<crate::PredicateId, Vec<ColumnTag>> = [(
        p,
        vec![
            ColumnTag {
                kind: Some(CataKind::RootDisc),
                group: 0,
                scalar_int: false,
            },
            ColumnTag {
                kind: Some(CataKind::RootDisc),
                group: 1,
                scalar_int: false,
            },
        ],
    )]
    .into_iter()
    .collect();

    // The disjunctive learner finds a certifying invariant.
    let model = super::disj_abstract::solve_abstract_disjunctive(
        &problem,
        &tags,
        ay_core::time::Instant::now() + Duration::from_secs(10),
    )
    .expect("disjunctive learner must find the two-minterm invariant");

    let smt = InvariantModel::expr_to_smtlib(&model.get(&p).expect("P interpreted").formula);
    assert!(smt.contains("(or"), "invariant must be disjunctive: {smt}");

    // Re-certify inductive + query-excluding via a fresh verifier (the same
    // fail-closed gate the route uses).
    let cfg = crate::PdrConfig {
        strict_proofs: true,
        solve_timeout: Some(Duration::from_secs(10)),
        ..crate::PdrConfig::default()
    };
    assert!(
        matches!(
            crate::engines::validate_external_invariant_model(&problem, &model, &cfg),
            Ok(true)
        ),
        "learned disjunctive invariant must re-certify"
    );
}
