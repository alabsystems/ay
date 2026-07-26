// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tests for the FORALL-ARR ghost-pair transformer and its quantified
//! certification (agenda #16).

use std::time::Duration;

use super::{
    collect_index_terms, instantiation_tuples, ArrayGhostPairTransformer, GhostPairCertificate,
    GhostPairSpec,
};
use crate::pdr::{InvariantModel, PredicateInterpretation};
use crate::transform::{recheck_ghost_pair_certificate, Transformer};
use crate::{
    ChcExpr, ChcProblem, ChcReplayObligationKind, ChcSort, ChcVar, ClauseBody, ClauseHead,
    HornClause, PredicateId,
};

fn int_array_sort() -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int))
}

fn var(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, sort))
}

/// `P(a : Array Int Int, n : Int)` with:
/// - init:  `P(const0, 0)`
/// - trans: `P(a, n) /\ a' = store(a, n, 0)  =>  P(a', n + 1)`
/// - query: `P(a, n) /\ 0 <= q /\ select(a, q) != 0  =>  false`
///
/// Safe; the (necessarily quantified) invariant is `forall i. a[i] = 0`.
fn const_zero_array_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![int_array_sort(), ChcSort::Int]);

    // init: true => P(const0, 0)
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(
            p,
            vec![
                ChcExpr::const_array(ChcSort::Int, ChcExpr::Int(0)),
                ChcExpr::Int(0),
            ],
        ),
    ));

    // trans: P(a, n) /\ a2 = store(a, n, 0) => P(a2, n + 1)
    let a = var("a", int_array_sort());
    let a2 = var("a2", int_array_sort());
    let n = var("n", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![a.clone(), n.clone()])],
            Some(ChcExpr::eq(
                a2.clone(),
                ChcExpr::store(a.clone(), n.clone(), ChcExpr::Int(0)),
            )),
        ),
        ClauseHead::Predicate(p, vec![a2, ChcExpr::add(n, ChcExpr::Int(1))]),
    ));

    // query: P(a, n) /\ 0 <= q /\ select(a, q) != 0 => false
    let a = var("a", int_array_sort());
    let n = var("n", ChcSort::Int);
    let q = var("q", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![a.clone(), n])],
            Some(ChcExpr::and(
                ChcExpr::le(ChcExpr::Int(0), q.clone()),
                ChcExpr::ne(ChcExpr::select(a, q), ChcExpr::Int(0)),
            )),
        ),
        ClauseHead::False,
    ));

    problem
}

/// The quantified model `forall i. a[i] = 0`, expressed as the ghost model
/// `I'(a, n, idx, val) := val = 0` over the n=1 transformed signature.
fn val_is_zero_ghost_model(p: PredicateId) -> InvariantModel {
    let vars = vec![
        ChcVar::new(format!("__p{}_a0", p.index()), int_array_sort()),
        ChcVar::new(format!("__p{}_a1", p.index()), ChcSort::Int),
        ChcVar::new(format!("__p{}_a2", p.index()), ChcSort::Int),
        ChcVar::new(format!("__p{}_a3", p.index()), ChcSort::Int),
    ];
    let formula = ChcExpr::eq(ChcExpr::var(vars[3].clone()), ChcExpr::Int(0));
    let mut model = InvariantModel::new();
    model.set(p, PredicateInterpretation::new(vars, formula));
    model
}

#[test]
fn spec_analyzes_int_indexed_array_arguments_only() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![int_array_sort(), ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int, ChcSort::Bool]);
    let r = problem.declare_predicate(
        "R",
        vec![ChcSort::Array(
            Box::new(ChcSort::Bool),
            Box::new(ChcSort::Int),
        )],
    );

    let spec = GhostPairSpec::analyze(&problem, 1);
    assert_eq!(spec.preds.get(&p).unwrap().array_positions, vec![0]);
    assert!(!spec.preds.contains_key(&q), "no array args");
    assert!(
        !spec.preds.contains_key(&r),
        "Bool-indexed arrays are not instrumented"
    );
}

#[test]
fn spec_instruments_five_arrays_at_n1_but_skips_ten_slots_at_n2() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![int_array_sort(); 5]);

    let one_pair = GhostPairSpec::analyze(&problem, 1);
    assert_eq!(
        one_pair.preds.get(&p).unwrap().array_positions,
        vec![0, 1, 2, 3, 4],
        "five-array invariants need one independently indexed value per array"
    );

    let two_pairs = GhostPairSpec::analyze(&problem, 2);
    assert!(
        !two_pairs.preds.contains_key(&p),
        "ten ghost slots exceed the bounded abstraction budget"
    );
}

#[test]
fn transformer_extends_signatures_and_preserves_predicate_ids() {
    let problem = const_zero_array_problem();
    let original_pred = problem.predicates()[0].clone();

    let result = Box::new(ArrayGhostPairTransformer::new(1)).transform(problem);
    let transformed = &result.problem;

    let pred = &transformed.predicates()[0];
    assert_eq!(pred.id, original_pred.id, "predicate ids preserved");
    assert_eq!(
        pred.arg_sorts,
        vec![int_array_sort(), ChcSort::Int, ChcSort::Int, ChcSort::Int],
        "one (idx, val) ghost pair appended"
    );

    // Every head occurrence carries fresh ghost variables coupled to the
    // array through a `val = select(arr, idx)` conjunct in the constraint.
    for clause in transformed.clauses() {
        if let ClauseHead::Predicate(_, args) = &clause.head {
            assert_eq!(args.len(), 4);
            let idx = &args[2];
            let val = &args[3];
            assert!(matches!(idx, ChcExpr::Var(v) if v.name.starts_with("__gpi")));
            assert!(matches!(val, ChcExpr::Var(v) if v.name.starts_with("__gpv")));
            let expected_coupling =
                ChcExpr::eq(val.clone(), ChcExpr::select(args[0].clone(), idx.clone()));
            let constraint = clause
                .body
                .constraint
                .as_ref()
                .expect("ghost head clause must carry a coupling constraint");
            assert!(
                constraint
                    .conjuncts()
                    .iter()
                    .any(|c| **c == expected_coupling),
                "coupling conjunct `val = select(arr, idx)` missing from {constraint}"
            );
        }
        // Body atoms are instantiated copies with full ghost arity.
        for (_, args) in &clause.body.predicates {
            assert_eq!(args.len(), 4);
        }
    }

    // LINEARITY PIN: each original body atom maps to exactly ONE instantiated
    // copy — multiple copies of the same predicate would make the clause
    // nonlinear, which the PDR core cannot push lemmas through (it stalls at
    // frame 1 and the lane never fires).
    let transition = &transformed.clauses()[1];
    assert_eq!(
        transition.body.predicates.len(),
        1,
        "expected exactly one (pass-through) body instantiation, got {}",
        transition.body.predicates.len()
    );
    // The pass-through instance probes the head's fresh ghost index.
    if let ClauseHead::Predicate(_, head_args) = &transition.head {
        let (_, body_args) = &transition.body.predicates[0];
        assert_eq!(
            body_args[2], head_args[2],
            "body ghost index must pass through to the head ghost index"
        );
    }
}

#[test]
fn transformer_is_identity_without_int_indexed_arrays() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(p, vec![ChcExpr::Int(0)]),
    ));

    let result = Box::new(ArrayGhostPairTransformer::new(1)).transform(problem);
    assert_eq!(result.problem.predicates()[0].arity(), 1);
    assert!(result
        .back_translator
        .transform_memory()
        .is_identity_grade());
}

#[test]
fn index_terms_are_collected_from_selects_and_stores() {
    let problem = const_zero_array_problem();
    let transition = &problem.clauses()[1];
    let terms = collect_index_terms(transition, 6);
    // store(a, n, 0) contributes `n`.
    assert!(terms.contains(&var("n", ChcSort::Int)));

    let query = &problem.clauses()[2];
    let terms = collect_index_terms(query, 6);
    assert!(terms.contains(&var("q", ChcSort::Int)));
}

#[test]
fn instantiation_tuples_cover_identity_diagonal_and_pairs() {
    let f0 = var("f0", ChcSort::Int);
    let f1 = var("f1", ChcSort::Int);
    let t = var("t", ChcSort::Int);

    // slots=1: identity == diagonal over the fresh var, plus candidates.
    let tuples = instantiation_tuples(1, &[f0.clone()], &[t.clone()], 8);
    assert!(tuples.contains(&vec![f0.clone()]));
    assert!(tuples.contains(&vec![t.clone()]));

    // slots=2: identity tuple, diagonals, and ordered pairs.
    let tuples = instantiation_tuples(2, &[f0.clone(), f1.clone()], &[t.clone()], 12);
    assert!(tuples.contains(&vec![f0.clone(), f1.clone()]), "identity");
    assert!(tuples.contains(&vec![t.clone(), t.clone()]), "diagonal");
    assert!(
        tuples.contains(&vec![f0.clone(), t.clone()])
            || tuples.contains(&vec![t.clone(), f0.clone()]),
        "ordered pairs"
    );

    // Cap is respected and a fallback tuple exists without any triggers.
    assert!(instantiation_tuples(2, &[], &[], 4).len() <= 4);
    assert_eq!(
        instantiation_tuples(1, &[], &[], 4),
        vec![vec![ChcExpr::Int(0)]]
    );
}

#[test]
fn false_query_uses_array_specific_cross_array_triggers() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate(
        "P",
        vec![int_array_sort(), int_array_sort(), int_array_sort()],
    );
    let a = var("a", int_array_sort());
    let b = var("b", int_array_sort());
    let c = var("c", int_array_sort());
    let ia = var("ia", ChcSort::Int);
    let ib = var("ib", ChcSort::Int);
    let ic = var("ic", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![a.clone(), b.clone(), c.clone()])],
        Some(ChcExpr::ne(
            ChcExpr::select(c, ic.clone()),
            ChcExpr::add(
                ChcExpr::select(a, ia.clone()),
                ChcExpr::select(b, ib.clone()),
            ),
        )),
    )));

    let transformed = Box::new(ArrayGhostPairTransformer::new(1)).transform(problem);
    let (_, args) = &transformed.problem.clauses()[0].body.predicates[0];
    assert_eq!(args[3], ia, "first array must use its own observed address");
    assert_eq!(
        args[5], ib,
        "second array must use its own observed address"
    );
    assert_eq!(args[7], ic, "third array must use its own observed address");
}

#[test]
fn false_query_n2_uses_two_observed_indices_of_one_array() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![int_array_sort()]);
    let a = var("a", int_array_sort());
    let k = var("k", ChcSort::Int);
    let previous = ChcExpr::add(k.clone(), ChcExpr::Int(-1));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![a.clone()])],
        Some(ChcExpr::not(ChcExpr::le(
            ChcExpr::select(a.clone(), previous.clone()),
            ChcExpr::select(a, k.clone()),
        ))),
    )));

    let transformed = Box::new(ArrayGhostPairTransformer::new(2)).transform(problem);
    let (_, args) = &transformed.problem.clauses()[0].body.predicates[0];
    assert_eq!(args[1], previous, "first pair must probe k - 1");
    assert_eq!(args[3], k, "second pair must probe k");
}

#[test]
fn certify_seals_a_valid_quantified_ghost_model() {
    let problem = const_zero_array_problem();
    let p = problem.predicates()[0].id;
    let spec = GhostPairSpec::analyze(&problem, 1);
    let model = val_is_zero_ghost_model(p);

    let certificate = GhostPairCertificate::certify_and_seal(
        &problem,
        spec,
        model,
        Some(Duration::from_secs(30)),
    );
    let certificate = certificate.expect("val=0 ghost model must certify on the original clauses");
    assert_eq!(certificate.ghost_pairs_per_array(), 1);

    // Re-checks (finalize boundary: all clauses; runner gate: query clauses).
    assert!(recheck_ghost_pair_certificate(
        &problem,
        &certificate,
        Some(Duration::from_secs(30)),
        false,
    ));
    assert!(recheck_ghost_pair_certificate(
        &problem,
        &certificate,
        Some(Duration::from_secs(30)),
        true,
    ));
}

/// SOUNDNESS PIN: a ghost model that is NOT a solution of the original system
/// must never seal. A naive lane that trusted the transformed-problem verdict
/// without the original-clause quantified discharge would emit a wrong `sat`
/// here; the certification gate forces unknown instead.
#[test]
fn certify_rejects_a_non_solution_ghost_model() {
    let problem = const_zero_array_problem();
    let p = problem.predicates()[0].id;
    let spec = GhostPairSpec::analyze(&problem, 1);

    // `true` is inductive for init/transition clauses but does NOT discharge
    // the query clause — accepting it would be a false SAFE.
    let vars = vec![
        ChcVar::new("__p0_a0", int_array_sort()),
        ChcVar::new("__p0_a1", ChcSort::Int),
        ChcVar::new("__p0_a2", ChcSort::Int),
        ChcVar::new("__p0_a3", ChcSort::Int),
    ];
    let mut model = InvariantModel::new();
    model.set(p, PredicateInterpretation::new(vars, ChcExpr::Bool(true)));

    assert!(
        GhostPairCertificate::certify_and_seal(
            &problem,
            spec,
            model,
            Some(Duration::from_secs(30)),
        )
        .is_none(),
        "non-solution ghost model must fail certification (fail-closed)"
    );
}

/// Regression pin for the #8734-class CLI aborts on ghost-pair SAFEs: the
/// Safe model carried by a sealed certificate has an EMPTY per-predicate
/// interpretation map, so the standard invariant replay exporter used to fail
/// with "missing invariant interpretation" and the CLI exited 1 on genuinely
/// SAFE array CHCs. `chc_safe_replay_obligations` must instead export the
/// certificate's own per-clause quantified discharge queries, each of which
/// is independently UNSAT.
#[test]
fn ghost_pair_certificate_exports_unsat_replay_obligations() {
    let problem = const_zero_array_problem();
    let p = problem.predicates()[0].id;
    let spec = GhostPairSpec::analyze(&problem, 1);
    let certificate = GhostPairCertificate::certify_and_seal(
        &problem,
        spec,
        val_is_zero_ghost_model(p),
        Some(Duration::from_secs(30)),
    )
    .expect("val=0 ghost model must certify on the original clauses");

    let mut model = InvariantModel::new();
    model.set_ghost_pair_certificate(certificate);

    let obligations = crate::engines::chc_safe_replay_obligations(&problem, &model)
        .expect("ghost-pair Safe must export replay obligations, not a hard error");

    assert_eq!(
        obligations.len(),
        problem.clauses().len(),
        "one obligation per original clause"
    );
    assert_eq!(
        obligations
            .iter()
            .map(|o| o.kind)
            .collect::<Vec<ChcReplayObligationKind>>(),
        vec![
            ChcReplayObligationKind::Initiation,
            ChcReplayObligationKind::Consecution,
            ChcReplayObligationKind::Safety,
        ],
    );
    for (clause_index, obligation) in obligations.iter().enumerate() {
        assert_eq!(obligation.clause_index, clause_index);
        assert!(obligation.smtlib.contains("(check-sat)"));
        assert!(
            !obligation.smtlib.contains(":timeout"),
            "replay artifacts must not embed solver-local timeouts"
        );
        assert!(
            crate::smt::executor_adapter::check_unsat_smtlib_via_executor(&obligation.smtlib),
            "obligation {} must be independently UNSAT; got sat/unknown for:\n{}",
            obligation.name,
            obligation.smtlib,
        );
    }
    // The quantified body hypothesis appears wherever a ghost-carrying
    // predicate occurs in the clause body (consecution + safety).
    assert!(obligations[1].smtlib.contains("(forall ("));
    assert!(obligations[2].smtlib.contains("(forall ("));
}

/// Structural fail-closed pins: missing interpretations, arity mismatches, and
/// free non-parameter variables are all rejected before any SMT runs.
#[test]
fn certify_rejects_structurally_broken_models() {
    let problem = const_zero_array_problem();
    let p = problem.predicates()[0].id;
    let spec = GhostPairSpec::analyze(&problem, 1);

    // Missing interpretation.
    assert!(GhostPairCertificate::certify_and_seal(
        &problem,
        spec.clone(),
        InvariantModel::new(),
        Some(Duration::from_secs(5)),
    )
    .is_none());

    // Arity mismatch (original arity, no ghost slots).
    let mut short_model = InvariantModel::new();
    short_model.set(
        p,
        PredicateInterpretation::new(
            vec![
                ChcVar::new("__p0_a0", int_array_sort()),
                ChcVar::new("__p0_a1", ChcSort::Int),
            ],
            ChcExpr::Bool(true),
        ),
    );
    assert!(GhostPairCertificate::certify_and_seal(
        &problem,
        spec.clone(),
        short_model,
        Some(Duration::from_secs(5)),
    )
    .is_none());

    // Free non-parameter variable in the formula.
    let mut free_var_model = val_is_zero_ghost_model(p);
    let interp = free_var_model.get(&p).unwrap().clone();
    free_var_model.set(
        p,
        PredicateInterpretation::new(
            interp.vars,
            ChcExpr::eq(var("stray", ChcSort::Int), ChcExpr::Int(0)),
        ),
    );
    assert!(GhostPairCertificate::certify_and_seal(
        &problem,
        spec,
        free_var_model,
        Some(Duration::from_secs(5)),
    )
    .is_none());
}

#[test]
fn certified_model_passes_external_validation_gates() {
    let problem = const_zero_array_problem();
    let p = problem.predicates()[0].id;
    let spec = GhostPairSpec::analyze(&problem, 1);
    let certificate = GhostPairCertificate::certify_and_seal(
        &problem,
        spec,
        val_is_zero_ghost_model(p),
        Some(Duration::from_secs(30)),
    )
    .expect("model must certify");

    let mut model = InvariantModel::new();
    model.set_ghost_pair_certificate(certificate);
    assert!(model.has_quantified_array_certificate());

    let config = crate::PdrConfig {
        solve_timeout: Some(Duration::from_secs(30)),
        ..crate::PdrConfig::default()
    };
    assert!(
        crate::engines::validate_external_invariant_model(&problem, &model, &config).unwrap(),
        "full validation gate must accept the sealed certificate"
    );
    assert!(
        crate::engines::external_invariant_model_excludes_error(&problem, &model, &config).unwrap(),
        "excludes-error gate must accept the sealed certificate"
    );
}

#[test]
fn invalidity_backtranslation_strips_ghost_assignments() {
    use crate::pdr::counterexample::{Counterexample, CounterexampleStep};
    use ay_core::kani_compat::DetHashMap as FxHashMap;

    let problem = const_zero_array_problem();
    let p = problem.predicates()[0].id;
    let result = Box::new(ArrayGhostPairTransformer::new(1)).transform(problem);

    let mut assignments = FxHashMap::default();
    assignments.insert(format!("__p{}_a1", p.index()), 3i64);
    assignments.insert(format!("__p{}_a2", p.index()), 7i64); // ghost idx
    assignments.insert(format!("__p{}_a3", p.index()), 9i64); // ghost val
    let cex = Counterexample {
        steps: vec![CounterexampleStep::new(p, assignments)],
        witness: None,
        ground_derivation: None,
    };

    let translated = result.back_translator.translate_invalidity(cex);
    let step = &translated.steps[0];
    assert!(step
        .assignments
        .contains_key(&format!("__p{}_a1", p.index())));
    assert!(!step
        .assignments
        .contains_key(&format!("__p{}_a2", p.index())));
    assert!(!step
        .assignments
        .contains_key(&format!("__p{}_a3", p.index())));
}
