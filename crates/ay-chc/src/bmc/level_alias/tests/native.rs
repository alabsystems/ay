// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use crate::smt::SmtValue;

fn original_replayed_diamond(problem: ChcProblem) -> crate::ground_derivation::GroundDerivation {
    let _terms = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(256 * 1024 * 1024));
    let solver = fixtures::solver(problem);
    assert!(!solver.prefer_exact_acyclic_executor_first());
    assert_eq!(solver.level_flat_may_alias_ancestry(), Some(true));
    let result = solver.solve();
    let ChcEngineResult::Unsafe(cex) = result else {
        panic!(
            "the reachable shared-ancestor diamond must recover an original-replayed refutation; \
             result={result:?}; stats={:?}",
            solver.stats()
        );
    };
    assert!(solver.stats().used_executor_path);
    assert!(!solver.stats().used_legacy_fallback);
    assert!(
        !solver.stats().exhausted_search,
        "rejected flat UNSAT cannot retain exhaustive proof status"
    );
    let derivation = cex
        .ground_derivation
        .expect("native ground evidence is required");
    crate::ground_derivation::validate_ground_derivation(&solver.problem, &derivation).unwrap();
    let query = &derivation.steps[derivation.query_step];
    assert_eq!(query.premises.len(), 2);
    assert_ne!(
        query.premises[0], query.premises[1],
        "distinct query roots remain independent"
    );
    derivation
}

#[test]
#[ntest::timeout(30_000)]
fn scalar_shared_ancestor_diamond_is_unsafe_with_original_replay() {
    original_replayed_diamond(fixtures::scalar_diamond(1));
}

#[test]
#[ntest::timeout(30_000)]
fn array_and_bv129_shared_ancestor_diamond_preserves_native_values() {
    let derivation = original_replayed_diamond(fixtures::wide_array_diamond());
    let query = &derivation.steps[derivation.query_step];
    let high = num_bigint::BigUint::from(1u8) << 128usize;
    let wide_words: Vec<_> = query
        .env
        .values()
        .filter_map(|value| value.bitvec_to_biguint())
        .filter(|(_, width)| *width == 129)
        .map(|(bits, _)| bits)
        .collect();
    assert_eq!(wide_words.len(), 2);
    assert!(wide_words.iter().all(|bits| bits >= &high));
    assert_ne!(wide_words[0], wide_words[1]);
    assert_eq!(
        query
            .env
            .values()
            .filter(|value| matches!(value, SmtValue::ArrayMap { .. } | SmtValue::ConstArray(_)))
            .count(),
        2
    );
}

#[test]
#[ntest::timeout(30_000)]
fn array_and_bv129_exact_tree_stages_preserve_original_ground_evidence() {
    use crate::bmc::{DerivationWitness, LevelDerivationWitness, TreeBuildOpts};
    use ay_core::kani_compat::DetHashMap;

    let _terms = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(256 * 1024 * 1024));
    let budget = std::time::Duration::from_secs(10);
    let _deadline = crate::smt::ScopedSmtDeadline::install(budget);
    let solver = fixtures::solver(fixtures::wide_array_diamond());
    let query = solver.problem.queries().next().expect("source query");
    let substitutions: DetHashMap<_, _> = query
        .vars()
        .into_iter()
        .map(|var| {
            (
                var.name.clone(),
                ChcExpr::Var(crate::ChcVar::new(
                    format!("__tree_q_{}", var.name),
                    var.sort.clone(),
                )),
            )
        })
        .collect();
    let options = TreeBuildOpts {
        node_cap: crate::bmc::TREE_REFUTATION_NODE_CAP,
        linear_only: false,
        committed: None,
        root_choice: None,
    };
    let mut nodes = Vec::new();
    let mut fresh = 0;
    let mut conjuncts = Vec::new();
    let mut roots = Vec::new();
    // Reproduce the first exact-tree attempt independently of the flat
    // solver's exit. Keep both roots and every alternative source fact.
    for (predicate, args) in &query.body.predicates {
        let args: Vec<_> = args
            .iter()
            .map(|arg| arg.substitute_name_map(&substitutions))
            .collect();
        let (root, derivable) = solver
            .build_tree_node(
                *predicate,
                &args,
                2,
                &options,
                &mut nodes,
                &mut fresh,
                &mut conjuncts,
            )
            .expect("stage 1: the bounded exact tree must fit");
        roots.push(root);
        conjuncts.push(derivable);
    }
    conjuncts.push(
        query
            .body
            .constraint
            .as_ref()
            .expect("original disequality and array reads")
            .substitute_name_map(&substitutions),
    );
    let formula = ChcExpr::and_all(conjuncts);
    let mut smt = solver.problem.make_smt_context();
    let result = smt.check_sat_with_timeout(&formula, budget);
    let crate::smt::SmtResult::Sat(model) = result else {
        panic!("stage 2: the exact wide-array tree needs a complete SAT model; got {result:?}");
    };
    let mut entries = Vec::new();
    let query_roots: Vec<_> = roots
        .into_iter()
        .map(|root| {
            solver
                .tree_reconstruct(root, &nodes, &model, &mut entries)
                .expect("stage 3: native values must reconstruct every root")
        })
        .collect();
    for &root in &query_roots {
        BmcSolver::assign_derivation_levels(&mut entries, root);
    }
    let witness = LevelDerivationWitness {
        witness: DerivationWitness {
            query_clause: solver.query_clause_index(query),
            root: query_roots[0],
            entries,
        },
        query_roots,
    };
    let derivation = solver
        .ground_derivation_from_witness_with(&witness, |clause| {
            BmcSolver::tree_query_clause_instances(clause, &model, "__tree_q_")
        })
        .expect("stage 4: native query and rule assignments must form ground evidence");
    crate::ground_derivation::validate_ground_derivation(&solver.problem, &derivation)
        .expect("stage 5: all original clauses and ordered premises must replay");
}

#[test]
#[ntest::timeout(30_000)]
fn disjoint_ancestry_safe_control_retains_exhaustive_safety() {
    let _terms = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(256 * 1024 * 1024));
    let problem = crate::parser::ChcParser::parse(
        r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun S (Int) Bool)
(declare-fun Q (Int) Bool)
(declare-fun R (Int) Bool)
(assert (P 0))
(assert (S 0))
(assert (forall ((x Int)) (=> (P x) (Q x))))
(assert (forall ((y Int)) (=> (S y) (R y))))
(assert (forall ((x Int) (y Int)) (=> (and (Q x) (R y) (not (= x y))) false)))
(check-sat)
"#,
    )
    .unwrap();
    let solver = fixtures::solver(problem);
    assert_eq!(solver.level_flat_may_alias_ancestry(), Some(false));
    assert!(matches!(solver.solve(), ChcEngineResult::Safe(_)));
    assert!(solver.stats().exhausted_search);
}

#[test]
#[ntest::timeout(30_000)]
fn shared_ancestry_safe_twin_never_fabricates_an_unsafe_witness() {
    let _terms = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(256 * 1024 * 1024));
    let solver = fixtures::solver(fixtures::scalar_diamond(0));
    assert_eq!(solver.level_flat_may_alias_ancestry(), Some(true));
    assert!(
        matches!(solver.solve(), ChcEngineResult::Unknown),
        "the conservative shared-ancestry guard may decline this safe twin, never fabricate Unsafe"
    );
    assert!(!solver.stats().exhausted_search);
}

#[test]
fn flattened_diamond_really_reuses_the_common_ancestor_argument() {
    let solver = fixtures::solver(fixtures::scalar_diamond(1));
    let p = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "P")
        .unwrap()
        .id;
    let q = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "Q")
        .unwrap()
        .id;
    let r = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "R")
        .unwrap()
        .id;
    let shared = solver.level_arg(p, 0, 0);
    let expected = [
        ChcExpr::eq(shared.clone(), solver.level_arg(q, 0, 1)),
        ChcExpr::eq(shared, solver.level_arg(r, 0, 1)),
    ];
    let mut level = Vec::new();
    solver.compile_level_flat(1, &mut level);
    let mut pending: Vec<_> = level.iter().collect();
    let mut found = [false; 2];
    while let Some(expr) = pending.pop() {
        for (index, expected) in expected.iter().enumerate() {
            found[index] |= expr == expected;
        }
        if let ChcExpr::Op(_, args) = expr {
            pending.extend(args.iter().map(AsRef::as_ref));
        }
    }
    assert_eq!(
        found,
        [true, true],
        "the regression must exercise the two aliased argument links"
    );
    assert_eq!(solver.level_flat_may_alias_ancestry(), Some(true));
}
