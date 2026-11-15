// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ChcParser;
use ntest::timeout;

/// `p0 -> p1 -> err` over 8-bit `x`, with a stutter rule on `p1`, the
/// predicate the query reads. The transition defines `o` by a 6-deep chain,
/// `min(x, 6)` under `x <= 5`, which the parser inlines into `p1`'s argument.
fn stutter_on_the_query_predicate(innermost_else: &str) -> ChcProblem {
    let chain = "(ite (not (bvuge #x00 x)) (ite (not (bvuge #x01 x)) \
                 (ite (not (bvuge #x02 x)) (ite (not (bvuge #x03 x)) \
                 (ite (not (bvuge #x04 x)) (ite (not (bvuge #x05 x)) #x06 INNER) \
                 #x04) #x03) #x02) #x01) #x00)"
        .replace("INNER", innermost_else);
    let source = format!(
        "(set-logic HORN)\n\
         (declare-var x (_ BitVec 8))\n(declare-var y (_ BitVec 8))\n(declare-var o (_ BitVec 8))\n\
         (declare-rel p0 ((_ BitVec 8) (_ BitVec 8)))\n\
         (declare-rel p1 ((_ BitVec 8) (_ BitVec 8)))\n(declare-rel err ())\n\
         (rule (=> true (p0 x y)))\n\
         (rule (=> (and (p0 x y) (bvule x #x05) (= o {chain})) (p1 x o)))\n\
         (rule (=> (p1 x y) (p1 x y)))\n\
         (rule (=> (and (p1 x y) (not (= y x))) err))\n(query err)\n"
    );
    let problem = ChcParser::parse(&source).expect("chain parses");
    problem.validate().expect("well-typed chain");
    assert!(
        !crate::classifier::ProblemClassifier::classify(&problem).has_cycles,
        "the classifier ignores the stutter rule, so the adaptive probes run exact acyclic BMC"
    );
    problem
}

/// The exact acyclic mode the adaptive acyclic probes run.
fn exact_acyclic(problem: ChcProblem) -> ChcEngineResult {
    let budget = std::time::Duration::from_secs(20);
    BmcSolver::new(
        problem,
        BmcConfig {
            max_depth: 3,
            acyclic_safe: true,
            prefer_exact_acyclic_first: true,
            per_depth_timeout: None,
            time_budget: Some(budget),
            enable_k_induction: false,
            enable_adaptive_stepping: false,
            sweep_past_spurious_sat: true,
            ..BmcConfig::default()
        },
    )
    .solve()
}

/// The stutter rule is the one defining clause the exact encodings drop.
#[test]
fn stutter_rules_define_nothing() {
    let solver = BmcSolver::new(stutter_on_the_query_predicate("#x05"), BmcConfig::default());
    let stutter: Vec<usize> = (0..solver.problem.clauses().len())
        .filter(|idx| ChcProblem::is_tautological_self_loop_clause(&solver.problem.clauses()[*idx]))
        .collect();
    assert_eq!(stutter.len(), 1);
    let flat = |defs: FxHashMap<PredicateId, Vec<usize>>| {
        let mut flat: Vec<usize> = defs.into_values().flatten().collect();
        flat.sort_unstable();
        flat
    };
    let all = flat(solver.defs_by_head());
    let acyclic = flat(solver.acyclic_defs_by_head());
    assert!(all.contains(&stutter[0]));
    assert_eq!(
        acyclic,
        all.into_iter()
            .filter(|idx| *idx != stutter[0])
            .collect::<Vec<_>>()
    );
}

/// Before, the stutter rule made `p1`'s DAG definition justify itself and the
/// exact pass answered Unknown on this safe system.
#[test]
#[timeout(60_000)]
fn a_stutter_rule_on_the_query_predicate_keeps_the_exact_acyclic_proof() {
    let result = exact_acyclic(stutter_on_the_query_predicate("#x05"));
    assert!(
        matches!(result, ChcEngineResult::Safe(_)),
        "x <= 5 makes the chain x, so err is unreachable (z3: unsat); got {result:?}"
    );
}

/// Negative twin: `x = 5` mapped to 4 reaches `err`, through a derivation of
/// the original clauses.
#[test]
#[timeout(60_000)]
fn a_stutter_rule_on_the_query_predicate_with_a_wrong_link_is_unsafe() {
    let result = exact_acyclic(stutter_on_the_query_predicate("#x04"));
    let ChcEngineResult::Unsafe(counterexample) = result else {
        panic!("x = 5 yields 4 != 5, so err is reachable (z3: sat); got {result:?}");
    };
    assert!(counterexample.has_ground_derivation());
}
