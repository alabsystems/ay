// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::*;
use ay_core::kani_compat::DetHashMap as HashMap;

#[test]
fn parser_rejects_zero_width_bitvectors() {
    for input in [
        "(declare-var x (_ BitVec 0))",
        "(declare-rel P ((_ BitVec 1))) (rule (P (_ bv0 0)))",
    ] {
        let error = ChcParser::parse(input).expect_err("zero-width BV must be rejected");
        assert!(error.to_string().contains("outside the supported range"));
    }
}

struct PanicOnInductiveTs {
    init_bounds_map: HashMap<String, generalize::InitBounds>,
}

impl PanicOnInductiveTs {
    fn new(init_bounds_map: HashMap<String, generalize::InitBounds>) -> Self {
        Self { init_bounds_map }
    }
}

impl generalize::TransitionSystemRef for PanicOnInductiveTs {
    fn check_inductive(&mut self, formula: &ChcExpr, level: u32) -> bool {
        panic!("unexpected inductiveness query at level {level}: {formula:?}");
    }

    fn check_inductive_with_core(
        &mut self,
        conjuncts: &[ChcExpr],
        level: u32,
    ) -> Option<Vec<ChcExpr>> {
        panic!("unexpected inductiveness+core query at level {level}: {conjuncts:?}");
    }

    fn init_bounds(&self) -> HashMap<String, generalize::InitBounds> {
        self.init_bounds_map.clone()
    }
}

#[test]
fn test_problem_construction() {
    // Test basic problem construction
    let mut problem = ChcProblem::new();

    // Declare Inv : Int -> Bool
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    assert_eq!(problem.predicates().len(), 1);

    // x = 0 => Inv(x)
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) /\ x < 10 => Inv(x + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) /\ x > 10 => false (query)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    assert_eq!(problem.clauses().len(), 3);
    assert_eq!(problem.queries().count(), 1);
    assert_eq!(problem.facts().count(), 1);
    assert_eq!(problem.transitions().count(), 1);
    assert!(problem.validate().is_ok());
}

fn build_deep_problem(depth: usize) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("P", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let arg = ChcExpr::var(x);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(pred, vec![ChcExpr::int(0)]),
    ));

    let mut deep = ChcExpr::Int(0);
    for _ in 0..depth {
        deep = ChcExpr::add(arg.clone(), deep);
    }

    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(pred, vec![arg])], Some(deep)),
        ClauseHead::False,
    ));
    problem
}

#[test]
fn direct_engine_drop_deep_problem_small_stack_6847() {
    const DEPTH: usize = 20_000;
    // 8MB matches default production stack. The test verifies iterative Drop
    // (#6847) doesn't overflow — not that constructors are iterative.
    // PdrSolver::new() has recursive preprocessing (try_split_ors, eliminate_mod)
    // that needs >2MB for 20K-deep expressions. See #7415.
    const STACK_BYTES: usize = 8 * 1024 * 1024;

    let handle = std::thread::Builder::new()
        .name("direct-engine-drop-small-stack".to_string())
        .stack_size(STACK_BYTES)
        .spawn(|| {
            drop(PdrSolver::new(
                build_deep_problem(DEPTH),
                PdrConfig::default(),
            ));
            drop(BmcSolver::new(
                build_deep_problem(DEPTH),
                BmcConfig::default(),
            ));
            drop(KindSolver::new(
                build_deep_problem(DEPTH),
                KindConfig::default(),
            ));
            drop(PdkindSolver::new(
                build_deep_problem(DEPTH),
                PdkindConfig::default(),
            ));
            drop(tpa::TpaSolver::new(
                build_deep_problem(DEPTH),
                tpa::TpaConfig::default(),
            ));
        })
        .expect("small-stack regression thread should spawn");

    handle
        .join()
        .expect("direct engine drop should not overflow on deep ChcProblem");
}

#[test]
fn test_pdr_solver_terminates() {
    // Test that PDR solver terminates on a simple problem
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) /\ x < 5 => Inv(x+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(5))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) /\ x > 5 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    let config = PdrConfig {
        max_frames: 4,
        max_iterations: 20,
        max_obligations: 10_000,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);
    let result = solver.solve();

    // This small safety problem should be solved definitively.
    match result {
        PdrResult::Safe(_) => {
            // Expected: found invariant
        }
        PdrResult::Unknown | PdrResult::NotApplicable => panic!(
            "PDR returned Unknown/NotApplicable on a trivial safe problem.\n\
             This test is a canary for silent solver regressions."
        ),
        PdrResult::Unsafe(_) => {
            panic!("BUG: PDR returned Unsafe for a known-safe problem");
        }
    }
}

/// i128-lockstep: init sums of (i64-backed) InitBounds are now computed
/// exactly in i128 — the old i64 init-sum overflow skip is unreachable, and
/// the generalizer proposes the EXACT candidate (never a wrapped constant).
/// A stub TS that records the query verifies both exactness and that a
/// `false` verdict leaves the lemma unchanged (fail-closed).
#[test]
fn test_constant_sum_overflow_init_sum_skips_inductiveness_check() {
    struct RecordingTs {
        init_bounds_map: HashMap<String, generalize::InitBounds>,
        queries: Vec<ChcExpr>,
    }
    impl generalize::TransitionSystemRef for RecordingTs {
        fn check_inductive(&mut self, formula: &ChcExpr, _level: u32) -> bool {
            self.queries.push(formula.clone());
            false
        }
        fn check_inductive_with_core(
            &mut self,
            _conjuncts: &[ChcExpr],
            _level: u32,
        ) -> Option<Vec<ChcExpr>> {
            None
        }
        fn init_bounds(&self) -> HashMap<String, generalize::InitBounds> {
            self.init_bounds_map.clone()
        }
    }

    let g = generalize::ConstantSumGeneralizer::new();

    let mut bounds = HashMap::default();
    bounds.insert("x".to_string(), generalize::InitBounds::exact(i64::MAX));
    bounds.insert("y".to_string(), generalize::InitBounds::exact(1));
    let mut ts = RecordingTs {
        init_bounds_map: bounds,
        queries: Vec::new(),
    };

    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    let lemma = ChcExpr::and(
        ChcExpr::eq(x, ChcExpr::int(0)),
        ChcExpr::eq(y, ChcExpr::int(0)),
    );

    let result = generalize::LemmaGeneralizer::generalize(&g, &lemma, 1, &mut ts);
    // Verdict false → lemma unchanged (fail-closed).
    assert_eq!(result, lemma);
    // The candidate carried the EXACT i128 init sum (2^63), not a wrap/clamp.
    assert_eq!(ts.queries.len(), 1);
    let expected_sum = i128::from(i64::MAX) + 1;
    let formula_str = format!("{:?}", ts.queries[0]);
    assert!(
        formula_str.contains(&expected_sum.to_string()),
        "candidate must carry the exact init sum {expected_sum}, got {formula_str}"
    );
}

/// i128-lockstep: the state-sum overflow skip now sits at the i128 boundary —
/// a lemma whose constants sum beyond i128 must skip the pair (no
/// inductiveness query, no wrapped candidate).
#[test]
fn test_constant_sum_overflow_state_sum_skips_inductiveness_check() {
    let g = generalize::ConstantSumGeneralizer::new();

    let mut bounds = HashMap::default();
    bounds.insert("x".to_string(), generalize::InitBounds::exact(i64::MAX - 1));
    bounds.insert("y".to_string(), generalize::InitBounds::exact(0));
    let mut ts = PanicOnInductiveTs::new(bounds);

    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    let lemma = ChcExpr::and(
        ChcExpr::eq(x, ChcExpr::int(i128::MAX)),
        ChcExpr::eq(y, ChcExpr::int(1)),
    );

    let result = generalize::LemmaGeneralizer::generalize(&g, &lemma, 1, &mut ts);
    assert_eq!(result, lemma);
}

#[test]
fn test_propagate_constants_with_mod() {
    use std::sync::Arc;

    // Test: (= A 0) ∧ (not (= (mod A 2) 0))
    // After propagation: (= 0 0) ∧ (not (= (mod 0 2) 0))
    // After simplification: true ∧ (not (= 0 0)) = true ∧ false = false
    let a_var = ChcVar::new("A", ChcSort::Int);

    // (= A 0)
    let a_eq_0 = ChcExpr::eq(ChcExpr::Var(a_var.clone()), ChcExpr::Int(0));

    // (mod A 2)
    let mod_a_2 = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::Var(a_var)), Arc::new(ChcExpr::Int(2))],
    );

    // (= (mod A 2) 0)
    let mod_eq_0 = ChcExpr::eq(mod_a_2, ChcExpr::Int(0));

    // (not (= (mod A 2) 0))
    let not_mod_eq_0 = ChcExpr::not(mod_eq_0);

    // (and (= A 0) (not (= (mod A 2) 0)))
    let conjunction = ChcExpr::and(a_eq_0, not_mod_eq_0);

    let propagated = conjunction.propagate_constants();

    // Should simplify to false since 0 mod 2 = 0, so (= 0 0) is true,
    // (not true) is false, and (true ∧ false) is false
    assert_eq!(propagated, ChcExpr::Bool(false));
}

#[test]
fn test_simplify_mod_constants() {
    use std::sync::Arc;

    // Test (mod 7 3) should simplify to 1
    let mod_expr = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::Int(7)), Arc::new(ChcExpr::Int(3))],
    );
    let simplified = mod_expr.simplify_constants();
    assert_eq!(simplified, ChcExpr::Int(1));

    // Test (mod 6 3) should simplify to 0
    let mod_expr = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::Int(6)), Arc::new(ChcExpr::Int(3))],
    );
    let simplified = mod_expr.simplify_constants();
    assert_eq!(simplified, ChcExpr::Int(0));

    // Test (mod 0 2) should simplify to 0
    let mod_expr = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::Int(0)), Arc::new(ChcExpr::Int(2))],
    );
    let simplified = mod_expr.simplify_constants();
    assert_eq!(simplified, ChcExpr::Int(0));
}

#[test]
fn test_simplify_and_contradiction() {
    use std::sync::Arc;

    // Test P AND NOT P should simplify to false
    let x = ChcVar::new("x", ChcSort::Int);
    let eq = ChcExpr::eq(
        ChcExpr::Op(
            ChcOp::Mod,
            vec![Arc::new(ChcExpr::var(x.clone())), Arc::new(ChcExpr::Int(6))],
        ),
        ChcExpr::Int(0),
    );
    let not_eq = ChcExpr::not(eq.clone());

    // Direct contradiction: (P AND NOT P)
    let and_expr = ChcExpr::and(eq.clone(), not_eq.clone());
    let simplified = and_expr.simplify_constants();
    assert_eq!(simplified, ChcExpr::Bool(false));

    // Nested contradiction: ((A AND P) AND NOT P)
    let a = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0));
    let nested = ChcExpr::and(ChcExpr::and(a, eq), not_eq);
    let simplified = nested.simplify_constants();
    assert_eq!(simplified, ChcExpr::Bool(false));
}

#[test]
fn test_simplify_bool_ite_contradiction() {
    use std::sync::Arc;

    let c = ChcExpr::var(ChcVar::new("c", ChcSort::Bool));
    let discr = ChcExpr::Op(
        ChcOp::Ite,
        vec![
            Arc::new(c),
            Arc::new(ChcExpr::BitVec(1, 32)),
            Arc::new(ChcExpr::BitVec(0, 32)),
        ],
    );
    let body = ChcExpr::and_all([
        ChcExpr::not(ChcExpr::eq(discr.clone(), ChcExpr::BitVec(0, 32))),
        ChcExpr::not(ChcExpr::eq(discr, ChcExpr::BitVec(1, 32))),
    ]);

    assert_eq!(body.simplify_constants(), ChcExpr::Bool(false));
}

#[test]
fn test_deep_expr_traversals_do_not_overflow() {
    // Deeply nested expressions can be created by malicious or accidental input. Traversals
    // should not stack overflow.
    let depth = 50_000;

    let mut expr = ChcExpr::Bool(true);
    for _ in 0..depth {
        expr = ChcExpr::not(expr);
    }

    // Exercise multiple traversals that historically used direct recursion.
    assert_eq!(expr.simplify_constants(), ChcExpr::Bool(true));
    assert_eq!(expr.normalize_negations(), ChcExpr::Bool(true));
    assert!(expr.vars().is_empty());
    assert_eq!(expr.substitute(&[]), expr);

    let eliminated = expr.eliminate_mod().eliminate_ite();
    assert_eq!(eliminated, expr);
}

/// #2389 #2495: Verify that deeply-nested expression trees do not overflow
/// the stack during variable collection (exercises maybe_grow_expr_stack).
///
/// Uses `ChcExpr::add` (not `ChcExpr::and`) because `and_all` flattens
/// nested And nodes into a single flat node, defeating the depth test.
/// Add/Sub/Mul/Implies constructors do NOT flatten, producing genuinely
/// deep trees.
///
/// Depth must stay under MAX_EXPR_RECURSION_DEPTH (500) so that
/// collect_vars_dedupe traverses the full tree. Previous depth of 10_000
/// caused SIGABRT: the depth guard truncated vars() to 500, the assertion
/// panicked, and recursive Arc drop during unwinding overflowed the stack.
#[test]
fn test_deep_add_tree_traversals_do_not_overflow() {
    let depth = 400;

    // Build a right-skewed Add tree: (+ x0 (+ x1 (+ x2 ... 0)))
    // Each add creates a 2-child node without flattening.
    let mut expr = ChcExpr::Int(0);
    for i in 0..depth {
        let var = ChcExpr::var(ChcVar::new(format!("x{i}"), ChcSort::Int));
        expr = ChcExpr::add(var, expr);
    }

    // vars() exercises maybe_grow_expr_stack in collect_vars_dedupe.
    let v = expr.vars();
    assert_eq!(v.len(), depth);

    // Leak to avoid recursive Drop overflow (#2495): the default Rust Drop
    // for deeply-nested Arc<ChcExpr> recurses through the tree.
    std::mem::forget(expr);
}

/// Test BMC-only API finds counterexample in unsafe problem (#8412).
#[test]
fn test_solve_bmc_only_finds_unsafe() {
    // Unsafe problem: x=0, x'=x+1, x>=5 => false
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    let config = BmcConfig::default().with_max_depth(10);
    let result = engines::solve_bmc_only(problem, config);
    assert!(
        result.is_unsafe(),
        "BMC-only should find counterexample: got {result}"
    );
}

/// Item 4 lanes wiring: BMC-only forwards clause-local array store/select
/// chains ahead of the solver, and the back-translated counterexample must
/// still replay on the ORIGINAL clauses (verified Unsafe, no verdict flip).
#[test]
fn test_solve_bmc_only_forwards_array_stores_and_validates_unsafe() {
    let problem = threaded_memory_two_hop_problem(42);

    // Precondition: the forwarding-only combination actually rewrites this
    // threaded-memory shape (otherwise the test exercises nothing new).
    let summary =
        crate::portfolio::PreprocessSummary::build_array_forwarding_only(problem.clone(), false);
    assert!(
        !summary.transform_memory.is_identity_grade(),
        "forwarding should rewrite the threaded-memory clause"
    );

    let config = BmcConfig::default().with_max_depth(10);
    let result = engines::solve_bmc_only(problem, config);
    assert!(
        result.is_unsafe(),
        "BMC-only should find and validate the forwarded counterexample: got {result}"
    );
}

/// Safe-side non-flip guard for the forwarded BMC-only lane: the unreachable
/// query stays non-Unsafe, and the array-carrying signature keeps the
/// empty-model exhaustive Safe demoted (fail-closed Unknown, never a false
/// proof).
#[test]
fn test_solve_bmc_only_forwarded_array_safe_side_does_not_flip() {
    let problem = threaded_memory_two_hop_problem(43);

    let config = BmcConfig::default().with_max_depth(10);
    let result = engines::solve_bmc_only(problem, config);
    assert!(
        !result.is_unsafe(),
        "query x=43 is unreachable (x is 42): got {result}"
    );
    assert!(
        !result.is_safe(),
        "array-carrying acyclic BMC Safe must stay demoted to Unknown: got {result}"
    );
}

/// Two-hop acyclic chain threading a memory array through every relation:
/// each hop writes a cell through a clause-local temporary and reads it back
/// (`t = store(m, 7, 41)`, `y = select(t, 7) + 1`), so x is 42 at the query.
/// The query fires iff `x = query_val`.
fn threaded_memory_two_hop_problem(query_val: i128) -> ChcProblem {
    let arr = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let mut problem = ChcProblem::new();
    let p0 = problem.declare_predicate("P0", vec![ChcSort::Int, arr.clone()]);
    let p1 = problem.declare_predicate("P1", vec![ChcSort::Int, arr.clone()]);

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let m = ChcVar::new("m", arr.clone());
    let t = ChcVar::new("t", arr);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p0, vec![ChcExpr::var(x.clone()), ChcExpr::var(m.clone())]),
    ));
    let constraint = ChcExpr::and(
        ChcExpr::eq(
            ChcExpr::var(t.clone()),
            ChcExpr::store(ChcExpr::var(m.clone()), ChcExpr::int(7), ChcExpr::int(41)),
        ),
        ChcExpr::eq(
            ChcExpr::var(y.clone()),
            ChcExpr::add(
                ChcExpr::select(ChcExpr::var(t.clone()), ChcExpr::int(7)),
                ChcExpr::int(1),
            ),
        ),
    );
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p0, vec![ChcExpr::var(x.clone()), ChcExpr::var(m.clone())])],
            Some(constraint),
        ),
        ClauseHead::Predicate(p1, vec![ChcExpr::var(y.clone()), ChcExpr::var(m.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p1, vec![ChcExpr::var(x.clone()), ChcExpr::var(m.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(query_val))),
        ),
        ClauseHead::False,
    ));

    problem
}

/// Test BMC evidence facade exposes solver-owned typed consumer evidence.
#[test]
fn test_solve_bmc_proof_from_str_unsafe_consumer_evidence_has_assignment_contract() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (= x 1)) false)))
(check-sat)
"#;

    let run = engines::solve_bmc_proof_from_str(smt2, BmcConfig::default().with_max_depth(2))
        .expect("valid CHC should parse and run BMC evidence mode");
    let problem = ChcParser::parse(smt2).expect("fixture should parse for evidence");

    assert!(
        run.result.is_unsafe(),
        "BMC proof facade should find Unsafe"
    );
    assert!(run.accepted_as_proof());
    assert_eq!(run.metadata.engine, "bmc");

    let evidence = run.consumer_evidence(&problem);
    assert_eq!(evidence.verdict_code, "unsafe");
    assert_eq!(evidence.backend_code, "ay_chc_bmc");
    assert!(evidence.accepted_for_consumer);
    assert!(evidence.model_validated);
    assert_eq!(
        evidence.verification_level_code,
        "ay_chc_verified_counterexample"
    );

    let trace = evidence
        .unsafe_trace
        .as_ref()
        .expect("validated unsafe evidence should carry trace material");
    assert_eq!(trace.status, "validated_counterexample");
    assert_eq!(trace.step_count, 2);
    for step in &trace.steps {
        assert_eq!(step.predicate_name.as_deref(), Some("Inv"));
        assert_eq!(step.assignments.len(), 1);
        assert_eq!(step.assignments[0].name, "__p0_a0");
        assert_eq!(step.assignments[0].predicate_argument_index, Some(0));
        assert_eq!(step.assignments[0].sort.as_deref(), Some("Int"));
    }

    let json = evidence.to_json_value();
    assert_eq!(
        json["unsafe_trace_assignment_contract"]["schema"],
        CHC_BMC_UNSAFE_TRACE_ASSIGNMENT_CONTRACT_SCHEMA
    );
    assert_eq!(
        json["unsafe_trace_assignment_contract"]["schema_version"],
        1
    );
    assert_eq!(
        json["unsafe_trace"]["steps"][0]["assignments"][0]["predicate_argument_index"],
        0
    );
}

/// Test sealed BMC proof runs emit first-class model/replay artifacts.
#[test]
fn test_solve_bmc_proof_from_str_emits_model_replay_artifacts() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (= x 1)) false)))
(check-sat)
"#;

    let run = engines::solve_bmc_proof_from_str(smt2, BmcConfig::default().with_max_depth(2))
        .expect("valid CHC should parse and run BMC evidence mode");
    let problem = ChcParser::parse(smt2).expect("fixture should parse for artifacts");

    let artifacts = run.proof_run_artifacts(&problem);
    assert!(
        artifacts.quantifier_free_invariant_model.is_none(),
        "an Unsafe BMC counterexample is not a QF invariant artifact"
    );
    let qf_error = run
        .quantifier_free_invariant_model_artifact(&problem)
        .expect_err("an Unsafe run must not serialize as a QF invariant");
    assert_eq!(
        qf_error.reason,
        ChcQfInvariantModelArtifactErrorReason::ResultNotSafe
    );
    assert_eq!(artifacts.model.schema, CHC_PROOF_RUN_MODEL_ARTIFACT_SCHEMA);
    assert_eq!(artifacts.model.role, CHC_PROOF_RUN_MODEL_ARTIFACT_ROLE);
    assert_eq!(
        artifacts.replay_transcript.schema,
        CHC_PROOF_RUN_REPLAY_TRANSCRIPT_ARTIFACT_SCHEMA
    );
    assert_eq!(
        artifacts.replay_transcript.role,
        CHC_PROOF_RUN_REPLAY_TRANSCRIPT_ARTIFACT_ROLE
    );
    assert!(!artifacts.model.sha256().is_empty());
    assert!(!artifacts.replay_transcript.sha256().is_empty());

    let model_json: serde_json::Value =
        serde_json::from_slice(artifacts.model.bytes()).expect("model artifact JSON envelope");
    assert_eq!(
        model_json["schema"],
        serde_json::json!(CHC_PROOF_RUN_MODEL_ARTIFACT_SCHEMA)
    );
    assert_eq!(model_json["role"], CHC_PROOF_RUN_MODEL_ARTIFACT_ROLE);
    assert_eq!(
        model_json["consumer_evidence"]["accepted_for_consumer"],
        true
    );
    assert_eq!(model_json["consumer_evidence"]["model_validated"], true);

    let replay_json: serde_json::Value =
        serde_json::from_slice(artifacts.replay_transcript.bytes())
            .expect("replay transcript artifact JSON envelope");
    assert_eq!(
        replay_json["schema"],
        serde_json::json!(CHC_PROOF_RUN_REPLAY_TRANSCRIPT_ARTIFACT_SCHEMA)
    );
    assert_eq!(
        replay_json["transcript_metadata"]["accepted_as_proof"],
        true
    );

    let validated_model = run
        .validate_model_artifact_bytes(&problem, artifacts.model.bytes())
        .expect("emitted model artifact should validate");
    let validated_replay = run
        .validate_replay_transcript_artifact_bytes(artifacts.replay_transcript.bytes())
        .expect("emitted replay transcript artifact should validate");
    assert_eq!(validated_model.sha256(), artifacts.model.sha256());
    assert_eq!(
        validated_replay.sha256(),
        artifacts.replay_transcript.sha256()
    );
    let validated_pair = run
        .validate_model_replay_artifact_bytes(
            &problem,
            Some(artifacts.model_bytes()),
            Some(artifacts.replay_transcript_bytes()),
        )
        .expect("emitted model/replay artifact pair should validate");
    assert_eq!(validated_pair.model.sha256(), artifacts.model.sha256());
    assert_eq!(
        validated_pair.replay_transcript.sha256(),
        artifacts.replay_transcript.sha256()
    );

    let mut tampered_model = artifacts.model.bytes().to_vec();
    tampered_model.push(b'\n');
    let error = run
        .validate_model_artifact_bytes(&problem, &tampered_model)
        .expect_err("tampered model artifact must fail closed");
    assert_eq!(
        error.reason,
        ChcProofRunArtifactValidationErrorReason::ArtifactDigestMismatch
    );
    assert_eq!(error.reason_code, "artifact_digest_mismatch");
    assert_eq!(error.role, CHC_PROOF_RUN_MODEL_ARTIFACT_ROLE);

    let missing_model = run
        .validate_model_replay_artifact_bytes(
            &problem,
            None,
            Some(artifacts.replay_transcript_bytes()),
        )
        .expect_err("missing model artifact bytes must fail closed");
    assert_eq!(
        missing_model.reason,
        ChcProofRunArtifactBundleValidationErrorReason::MissingModelArtifactBytes
    );
    assert_eq!(missing_model.reason_code, "missing_model_artifact_bytes");
    assert!(missing_model.fail_closed);
    assert!(!missing_model.accepted_for_consumer);

    let mut tampered_replay = artifacts.replay_transcript.bytes().to_vec();
    tampered_replay.push(b'\n');
    let replay_error = run
        .validate_model_replay_artifact_bytes(
            &problem,
            Some(artifacts.model_bytes()),
            Some(&tampered_replay),
        )
        .expect_err("tampered replay artifact bytes must fail closed");
    assert_eq!(
        replay_error.reason,
        ChcProofRunArtifactBundleValidationErrorReason::ReplayTranscriptArtifactMismatch
    );
    assert_eq!(
        replay_error.reason_code,
        "replay_transcript_artifact_mismatch"
    );
    assert_eq!(
        replay_error.artifact_error.as_ref().map(|error| error.role),
        Some(CHC_PROOF_RUN_REPLAY_TRANSCRIPT_ARTIFACT_ROLE)
    );
}

/// Test BMC evidence facade preserves fail-closed consumer semantics for Unknown.
#[test]
fn test_solve_bmc_proof_from_str_unknown_is_not_consumer_accepted() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;

    let run = engines::solve_bmc_proof_from_str(smt2, BmcConfig::default().with_max_depth(1))
        .expect("valid CHC should parse and run BMC evidence mode");
    let problem = ChcParser::parse(smt2).expect("fixture should parse for evidence");

    assert!(
        run.result.is_unknown(),
        "bounded BMC search should be Unknown"
    );
    assert!(!run.accepted_as_proof());
    assert_eq!(run.metadata.engine, "bmc");

    let evidence = run.consumer_evidence(&problem);
    assert_eq!(evidence.verdict_code, "unknown");
    assert_eq!(evidence.backend_code, "ay_chc_bmc");
    assert!(!evidence.accepted_for_consumer);
    assert_eq!(
        evidence.consumer_rejection_code.as_deref(),
        Some("ay_chc_unknown_bmc_exhausted_search")
    );
    assert!(!evidence.model_validated);
    assert_eq!(evidence.verification_level_code, "ay_chc_non_proof");
    assert_eq!(
        evidence.unknown_limit_code.as_deref(),
        Some("bmc_max_depth_reached")
    );
    assert!(evidence.unsafe_trace.is_none());

    let json = evidence.to_json_value();
    assert_eq!(json["accepted_for_consumer"], false);
    assert_eq!(json["unsafe_trace"]["status"], "not_applicable");
}

/// Test proof-grade PDR API returns sealed proof evidence and transcript metadata.
#[test]
fn test_solve_pdr_proof_from_str_safe_metadata() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (x1 Int))
  (=> (and (Inv x) (= x1 (+ x 1)))
      (Inv x1))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;

    let run = engines::solve_pdr_proof_from_str(
        smt2,
        PdrConfig::default()
            .with_max_frames(8)
            .with_max_iterations(100),
    )
    .expect("valid CHC should parse and solve");

    assert!(
        run.result.is_safe(),
        "PDR proof should prove safety: {run:?}"
    );
    assert!(run.accepted_as_proof());
    assert_eq!(run.metadata.engine, "pdr");
    assert_eq!(run.metadata.result, "safe");
    assert_eq!(run.metadata.proof_status, "verified-invariant");
    assert_eq!(run.metadata.pdr_input_sha256().len(), 64);
    assert!(run.metadata.normalized_input_bytes > 0);

    let problem = ChcParser::parse(smt2).expect("fixture should parse for evidence");
    let evidence = run.consumer_evidence(&problem);
    assert_eq!(evidence.verdict_code, "safe");
    assert_eq!(evidence.backend_code, "ay_chc_pdr");
    assert!(evidence.accepted_for_consumer);
    assert!(evidence.model_validated);
    assert_eq!(
        evidence.verification_level_code,
        "ay_chc_verified_invariant"
    );
    assert_eq!(
        evidence.normalized_input_sha256,
        run.metadata.normalized_input_sha256
    );

    let artifacts = run.proof_run_artifacts(&problem);
    let invariant = artifacts
        .quantifier_free_invariant_model
        .as_ref()
        .expect("a complete Safe PDR run must carry its actual QF invariant");
    assert_eq!(invariant.schema, CHC_QF_INVARIANT_MODEL_ARTIFACT_SCHEMA);
    assert_ne!(
        invariant.bytes(),
        artifacts.model.bytes(),
        "the replayable invariant must be distinct from diagnostic consumer metadata"
    );
    let reparsed = parse_qf_invariant_model_artifact(&problem, invariant.bytes())
        .expect("the solver-owned QF invariant must pass strict canonical parsing");
    assert_eq!(
        reparsed.to_smtlib(&problem),
        run.result
            .safe_invariant()
            .expect("Safe run")
            .model()
            .to_smtlib(&problem)
    );
}

/// G2 real-call Step 0: `prove_external_invariant_model` re-validates an
/// externally-produced candidate invariant and, on success, emits an ACCEPTED
/// proof-grade run. This proves the accepted path: a genuinely-valid invariant
/// (here `Inv(x) == (x >= 0)`, obtained from a PDR solve of a trivially-safe
/// counter, standing in for an ic3_lane candidate) is re-validated and wrapped
/// as proof-grade `Safe`.
#[test]
fn prove_external_invariant_model_accepts_validated_model() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (x1 Int))
  (=> (and (Inv x) (= x1 (+ x 1)))
      (Inv x1))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).expect("fixture should parse");
    let config = PdrConfig::default()
        .with_max_frames(8)
        .with_max_iterations(100);

    // Produce a genuine invariant model via PDR, standing in for an
    // externally-produced candidate.
    let model = match PdrSolver::solve_problem(&problem, config.clone()) {
        PdrResult::Safe(model) => model,
        other => panic!("expected PDR to prove the counter safe, got {other:?}"),
    };

    // Gate sanity: this model genuinely re-validates for this problem, so
    // emitting FullVerification evidence is honest.
    assert!(
        engines::validate_external_invariant_model(&problem, &model, &config)
            .expect("validation should not panic"),
        "the invariant must re-validate for the emission to be honest"
    );

    let run = engines::prove_external_invariant_model(problem.clone(), model, config)
        .expect("emission should not error on a validated model");

    assert!(
        run.accepted_as_proof(),
        "a re-validated invariant must yield an accepted proof run: {run:?}"
    );
    assert!(run.result.is_safe(), "accepted run must be Safe: {run:?}");
    assert_eq!(run.metadata.engine, "pdr");
    assert_eq!(run.metadata.result, "safe");
}

/// G2 real-call Step 0 negative control: the re-validation gate is LOAD-BEARING.
/// The SAME invariant model that is accepted for the safe counter above is
/// REJECTED when applied to a problem whose bad state it does not exclude, so
/// `prove_external_invariant_model` must return a NON-accepted run and NEVER a
/// Safe-accepted proof. An external candidate is never trusted without full
/// re-validation.
#[test]
fn prove_external_invariant_model_rejects_invalid_model() {
    // A model claiming `Inv(x) == (x >= 0)` — valid against the `x < 0` bad
    // state — obtained by solving that safe counter.
    let safe_smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (x1 Int))
  (=> (and (Inv x) (= x1 (+ x 1)))
      (Inv x1))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
    let safe_problem = ChcParser::parse(safe_smt2).expect("safe fixture should parse");
    let config = PdrConfig::default()
        .with_max_frames(8)
        .with_max_iterations(100);
    let model = match PdrSolver::solve_problem(&safe_problem, config.clone()) {
        PdrResult::Safe(model) => model,
        other => panic!("expected PDR to prove the counter safe, got {other:?}"),
    };

    // A DIFFERENT problem (identical `Inv (Int)` signature) whose bad state is
    // `x >= 0` — which the `x >= 0` invariant plainly does NOT exclude (the
    // initial state x = 0 is already bad). Re-validation MUST reject the model.
    let bad_smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (x1 Int))
  (=> (and (Inv x) (= x1 (+ x 1)))
      (Inv x1))))
(assert (forall ((x Int)) (=> (and (Inv x) (>= x 0)) false)))
(check-sat)
"#;
    let bad_problem = ChcParser::parse(bad_smt2).expect("bad fixture should parse");

    // Gate is load-bearing: the same model does NOT validate for this problem.
    assert!(
        !engines::validate_external_invariant_model(&bad_problem, &model, &config)
            .expect("validation should not panic"),
        "the invariant must NOT re-validate against a bad state it permits"
    );

    let run = engines::prove_external_invariant_model(bad_problem, model, config)
        .expect("emission should return a non-accepted run, not an error");

    assert!(
        !run.accepted_as_proof(),
        "an unvalidated candidate must NEVER yield an accepted proof run: {run:?}"
    );
    assert!(
        !run.result.is_safe(),
        "a rejected candidate must never be emitted as Safe: {run:?}"
    );
    assert!(
        run.result.is_unknown(),
        "a rejected run should be Unknown: {run:?}"
    );
}

/// External proof admission must validate the exact original nullary query.
///
/// The solve-time nullary-fail rewrite turns `error_p0 => error; query error`
/// into a direct `query error_p0`. That rewrite is equisatisfiable for solving,
/// but it is not a valid consumer-side model check: it erases the interpretation
/// of `error` itself. A transported model with `error = true` must therefore be
/// rejected even when `error_p0 = false` makes the rewritten query unreachable.
#[test]
fn external_model_validation_preserves_nullary_query_predicate() {
    let smt2 = r#"
(set-logic HORN)
(declare-rel State (Int))
(declare-rel error_p0 ())
(declare-rel error ())
(declare-var x Int)
(declare-var xp Int)
(rule (=> (= x 0) (State x)))
(rule (=> (and (State x) (= xp (+ x 1))) (State xp)))
(rule (=> (and (State x) (< x 0)) error_p0))
(rule (=> error_p0 error))
(query error)
"#;
    let problem = ChcParser::parse(smt2).expect("nullary-query fixture should parse");
    let state = problem.lookup_predicate("State").expect("State predicate");
    let error_p0 = problem
        .lookup_predicate("error_p0")
        .expect("error_p0 predicate");
    let error = problem.lookup_predicate("error").expect("error predicate");
    let state_var = ChcVar::new("x", ChcSort::Int);

    let mut invalid = InvariantModel::new();
    invalid.set(
        state,
        PredicateInterpretation::new(
            vec![state_var.clone()],
            ChcExpr::ge(ChcExpr::var(state_var.clone()), ChcExpr::int(0)),
        ),
    );
    invalid.set(
        error_p0,
        PredicateInterpretation::new(Vec::new(), ChcExpr::Bool(false)),
    );
    invalid.set(
        error,
        PredicateInterpretation::new(Vec::new(), ChcExpr::Bool(true)),
    );

    let config = PdrConfig::default();
    assert!(
        !engines::validate_external_invariant_model(&problem, &invalid, &config)
            .expect("validation should not panic"),
        "a model permitting the exact nullary query predicate must be rejected"
    );
    let rejected =
        engines::prove_external_invariant_model(problem.clone(), invalid, config.clone())
            .expect("invalid candidate should demote rather than error");
    assert!(!rejected.accepted_as_proof());
    assert!(rejected.result.is_unknown());

    let mut valid = InvariantModel::new();
    valid.set(
        state,
        PredicateInterpretation::new(
            vec![state_var.clone()],
            ChcExpr::ge(ChcExpr::var(state_var), ChcExpr::int(0)),
        ),
    );
    valid.set(
        error_p0,
        PredicateInterpretation::new(Vec::new(), ChcExpr::Bool(false)),
    );
    valid.set(
        error,
        PredicateInterpretation::new(Vec::new(), ChcExpr::Bool(false)),
    );
    assert!(
        engines::validate_external_invariant_model(&problem, &valid, &config)
            .expect("valid nullary-query model should verify"),
        "preserving original clauses must still admit a genuinely valid model"
    );

    let run = engines::solve_pdr_proof(problem.clone(), config)
        .expect("proof-grade nullary-query solve should not error");
    assert!(
        run.accepted_as_proof(),
        "proof-grade PDR must construct an exact-clause model: {run:?}"
    );
    let solved = run
        .result
        .safe_invariant()
        .expect("accepted proof must carry a Safe invariant")
        .model();
    assert!(
        !solved.convergence_proven,
        "nullary candidate completion must not inherit frame-convergence authority"
    );
    for predicate in problem.predicates() {
        assert!(
            solved.get(&predicate.id).is_some(),
            "proof-grade model must be total for original predicate {}",
            predicate.name
        );
    }
    assert!(
        engines::validate_external_invariant_model(&problem, solved, &PdrConfig::default())
            .expect("the proof-grade model should validate without panicking"),
        "the proof-grade model must satisfy every exact original clause"
    );
    let checked = run
        .run_checked_replay(&problem, std::time::Duration::from_secs(10))
        .expect("strict replay should discharge the exact nullary-query model");
    assert!(checked.proof_run.accepted_as_proof());
    assert!(
        checked
            .summary
            .obligations
            .iter()
            .all(|obligation| obligation.strict_cert.is_some()),
        "every UNSAT exact-clause obligation must carry a strict certificate"
    );
}

/// Default-false completion of the nullary query slice is only a candidate.
///
/// If a defining body is reachable, exact original-clause validation must keep
/// the result out of Safe even though the nullary predicates have no facts of
/// their own.
#[test]
fn nullary_query_candidate_completion_rejects_reachable_body() {
    let problem = ChcParser::parse(
        r#"
(set-logic HORN)
(declare-rel State (Int))
(declare-rel error_p0 ())
(declare-rel error ())
(declare-var x Int)
(declare-var xp Int)
(rule (=> (= x 0) (State x)))
(rule (=> (and (State x) (= xp (+ x 1))) (State xp)))
(rule (=> (and (State x) (= x 0)) error_p0))
(rule (=> error_p0 error))
(query error)
"#,
    )
    .expect("reachable-body fixture should parse");

    let run = engines::solve_pdr_proof(problem, PdrConfig::default())
        .expect("reachable-body solve should not error");
    assert!(
        !run.result.is_safe(),
        "candidate nullary completion must not mint Safe for a reachable body: {run:?}"
    );
}

/// A queried nullary predicate with its own fact can never be completed false.
#[test]
fn nullary_query_candidate_completion_rejects_nullary_fact() {
    let problem = ChcParser::parse(
        r#"
(set-logic HORN)
(declare-rel State (Int))
(declare-rel error ())
(declare-var x Int)
(declare-var xp Int)
(rule (=> (= x 0) (State x)))
(rule (=> (and (State x) (= xp (+ x 1))) (State xp)))
(rule (=> true error))
(query error)
"#,
    )
    .expect("nullary-fact fixture should parse");

    let run = engines::solve_pdr_proof(problem, PdrConfig::default())
        .expect("nullary-fact solve should not error");
    assert!(
        !run.result.is_safe(),
        "a nullary fact must prevent false candidate completion: {run:?}"
    );
}

/// A constraint-only nullary definition is not necessarily a reachable fact.
///
/// This mirrors the typed abs-neg bridge shape: its defining constraint is
/// contradictory, so exact validation can safely accept the false candidate.
#[test]
fn nullary_query_candidate_completion_accepts_unsat_constraint_fact() {
    let problem = ChcParser::parse(
        r#"
(set-logic HORN)
(declare-rel error ())
(declare-var x Int)
(rule (=> (and (= x 0) (< x 0)) error))
(query error)
"#,
    )
    .expect("UNSAT constraint-fact fixture should parse");

    let run = engines::solve_pdr_proof(problem.clone(), PdrConfig::default())
        .expect("UNSAT constraint-fact solve should not error");
    assert!(
        run.result.is_safe() && run.accepted_as_proof(),
        "an UNSAT constraint-only definition should validate Safe: {run:?}"
    );
    run.run_checked_replay(&problem, std::time::Duration::from_secs(10))
        .expect("strict replay should certify the UNSAT constraint-only definition");
}

/// Test proof-grade PDR API fails closed: cancellation yields Unknown/non-proof.
#[test]
fn test_solve_pdr_proof_cancelled_is_non_proof() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int)) (=> (Inv x) (Inv (+ x 1)))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
    let token = CancellationToken::new();
    token.cancel();

    let run = engines::solve_pdr_proof_from_str(
        smt2,
        PdrConfig::default().with_cancellation_token(Some(token)),
    )
    .expect("valid CHC should parse even when solving is cancelled");

    assert!(run.result.is_unknown(), "cancelled PDR should be Unknown");
    assert!(!run.accepted_as_proof());
    assert_eq!(run.metadata.result, "unknown");
    assert_eq!(run.metadata.proof_status, "non-proof");
    assert_eq!(run.metadata.unknown_reason.as_deref(), Some("inconclusive"));
}

/// Test proof-grade PDR acceptance is derived from the sealed result, not
/// mutable metadata fields that downstream reporting code may copy around.
#[test]
fn test_solve_pdr_proof_acceptance_ignores_tampered_metadata() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int)) (=> (Inv x) (Inv (+ x 1)))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
    let token = CancellationToken::new();
    token.cancel();

    let mut run = engines::solve_pdr_proof_from_str(
        smt2,
        PdrConfig::default().with_cancellation_token(Some(token)),
    )
    .expect("valid CHC should parse even when solving is cancelled");

    assert!(run.result.is_unknown(), "cancelled PDR should be Unknown");
    assert!(!run.accepted_as_proof());

    run.metadata.accepted_as_proof = true;
    run.metadata.proof_status = "verified-invariant".to_string();

    assert!(
        !run.accepted_as_proof(),
        "Unknown proof runs must remain fail-closed even if metadata is tampered"
    );
}

/// Test proof-grade PDR API does not turn parse failures into proof-shaped results.
#[test]
fn test_solve_pdr_proof_parse_error_is_error() {
    let err = engines::solve_pdr_proof_from_str(
        "(set-logic HORN)\n(declare-fun Inv (Int) Bool",
        PdrConfig::default(),
    )
    .expect_err("malformed CHC input must fail before evidence construction");

    assert!(matches!(err, ChcError::Parse(_)));
}

/// Test BMC-only API returns Unknown for safe problem (#8412).
#[test]
fn test_solve_bmc_only_returns_unknown_for_safe() {
    // Safe problem: x=0, x<3 => x'=x+1, x>=10 => false
    // x never exceeds 3, so BMC will exhaust depth without counterexample
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(3))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    // Use a small max_depth to make the test fast
    let config = BmcConfig::default().with_max_depth(20);
    let result = engines::solve_bmc_only(problem, config);
    assert!(
        result.is_unknown(),
        "BMC-only should return Unknown for safe problem: got {result}"
    );
}

/// Test BMC-only via AdaptivePortfolio::solve_bmc_only (#8412).
#[test]
fn test_adaptive_solve_bmc_only() {
    // Same unsafe problem via the AdaptivePortfolio method directly
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let bmc_config = BmcConfig::default()
        .with_max_depth(10)
        .with_time_budget(std::time::Duration::from_secs(10));
    let result = adaptive.solve_bmc_only(bmc_config);
    assert!(
        result.is_unsafe(),
        "AdaptivePortfolio::solve_bmc_only should find counterexample: got {result}"
    );
}

/// Test BMC-only from SMT-LIB string with cross_check() preset (#8412).
#[test]
fn test_solve_bmc_only_from_str_cross_check() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int)) (=> (Inv x) (Inv (+ x 1)))))
(assert (forall ((x Int)) (=> (and (Inv x) (>= x 5)) false)))
(check-sat)
"#;
    // Use a small max_depth for test speed
    let config = BmcConfig::cross_check().with_max_depth(10);
    let result = engines::solve_bmc_only_from_str(smt2, config).expect("should parse valid CHC");
    assert!(
        result.is_unsafe(),
        "BMC cross_check should find counterexample in unsafe problem: got {result}"
    );
}

/// Test BmcConfig::with_cancellation builder (#8412).
#[test]
fn test_bmc_config_with_cancellation() {
    let token = CancellationToken::new();
    // Cancel immediately to verify the token is wired through
    token.cancel();

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    let config = BmcConfig::default()
        .with_max_depth(100)
        .with_cancellation(token);
    let result = engines::solve_bmc_only(problem, config);
    // With immediate cancellation, BMC should return Unknown (not Unsafe)
    // because it's cancelled before it can find the counterexample at depth 5.
    assert!(
        result.is_unknown(),
        "BMC with pre-cancelled token should return Unknown: got {result}"
    );
}

/// Test BMC-only with a real unsafe SMT-LIB benchmark (two_phase_unsafe).
///
/// This is the cross-checking use case: model-checker-consumer has a CHC problem as an SMT-LIB
/// string and wants to run BMC-only to search for counterexamples. The
/// two_phase_unsafe benchmark counts x up from 0 to 10 (phase 0), then
/// counts x down in phase 1 until x < 0. The counterexample is at depth
/// ~22. Part of #8412.
#[test]
fn test_solve_bmc_only_from_str_real_unsafe_benchmark() {
    // Simple unsafe problem: x starts at 0, increments each step.
    // Query: x >= 5 => false. Counterexample at depth 5.
    // This uses the same pattern as model-checker-consumer's cross-check: parse SMT-LIB and run BMC.
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int))
  (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (x1 Int))
  (=> (and (Inv x) (= x1 (+ x 1)))
      (Inv x1))))
(assert (forall ((x Int))
  (=> (and (Inv x) (>= x 10))
      false)))
(check-sat)
"#;
    let config = BmcConfig::cross_check().with_max_depth(20);
    let result =
        engines::solve_bmc_only_from_str(smt2, config).expect("should parse valid CHC benchmark");
    assert!(
        result.is_unsafe(),
        "BMC should find counterexample in unsafe benchmark: got {result}"
    );
}

/// Test BMC-only returns Unknown on a safe benchmark (bouncy_one_counter).
///
/// This is the expected behavior for cross-checking: if the problem is safe,
/// BMC cannot prove it (BMC only finds counterexamples). It should return
/// Unknown, not Safe (since cross_check disables k-induction). Part of #8412.
#[test]
#[ntest::timeout(15_000)]
fn test_solve_bmc_only_from_str_real_safe_benchmark() {
    // bouncy_one_counter: a safe CHC problem with two predicates
    let smt2 = r#"
(set-logic HORN)
(declare-fun |itp2| ( Int Int Int ) Bool)
(declare-fun |itp1| ( Int Int Int ) Bool)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=> (and (= B 0) (= A 0) (= C 0))
        (itp1 A B C))))
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) )
    (=> (and (itp1 A B C)
             (= E (+ 1 B)) (= D (+ 1 A)) (= F (+ (- 2) C)))
        (itp1 D E F))))
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=> (and (itp1 A B C) true)
        (itp2 A B C))))
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) )
    (=> (and (itp2 A B C)
             (= E (+ (- 3) B)) (= D (+ (- 1) A)) (= F (+ 2 C)))
        (itp2 D E F))))
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=> (and (itp2 A C B)
             (and (or (not (<= C 0)) (not (>= B 0))) (<= A 0)))
        false)))
(check-sat)
"#;
    // Keep this as a bounded smoke test: the real benchmark exercises parsing
    // and no-false-Unsafe behavior, while the production-depth preset is
    // covered by `test_cross_check_preset_matches_model_checker_consumer_requirements`.
    let config = BmcConfig::cross_check()
        .with_max_depth(2)
        .with_time_budget(std::time::Duration::from_secs(2))
        .with_per_depth_timeout(std::time::Duration::from_millis(100));
    let result =
        engines::solve_bmc_only_from_str(smt2, config).expect("should parse valid CHC benchmark");
    // BMC without k-induction cannot prove safety, so Unknown is expected
    assert!(
        result.is_unknown(),
        "BMC cross_check on safe benchmark should return Unknown, got {result}"
    );
}

/// #9185: model-checker-consumer uses BMC-only as a fail-closed proof cross-check. A false
/// `Unsafe` from this API demotes a valid `PROOF` to `UNKNOWN`.
#[test]
fn test_bmc_cross_check_array_store_safe_9185() {
    let mut smt2 = String::from(
        "(set-logic HORN)\n\
         (declare-var a (Array (_ BitVec 32) (_ BitVec 32)))\n\
         (declare-var b (Array (_ BitVec 32) (_ BitVec 32)))\n",
    );
    for idx in 0..=25 {
        smt2.push_str(&format!(
            "(declare-rel S{idx} ((Array (_ BitVec 32) (_ BitVec 32))))\n"
        ));
    }
    smt2.push_str(
        "(declare-rel Bad ())\n\
         (rule (=> (= (select a #x00000000) #x00000000) (S0 a)))\n\
         (rule (=> (and (S0 a) (= b (store a #x00000026 #x00000001))) (S1 b)))\n",
    );
    for idx in 1..25 {
        smt2.push_str(&format!("(rule (=> (S{idx} a) (S{} a)))\n", idx + 1));
    }
    smt2.push_str(
        "(rule (=> (and (S25 a)\n\
                        (not (or (= (select a #x00000026) #x00000000)\n\
                                 (= (select a #x00000026) #x00000001))))\n\
                   Bad))\n\
         (query Bad)\n",
    );

    let config = BmcConfig::cross_check()
        .with_max_depth(30)
        .with_time_budget(std::time::Duration::from_secs(2));
    let result =
        engines::solve_bmc_only_from_str(&smt2, config).expect("should parse valid CHC benchmark");
    assert!(
        result.is_unknown(),
        "safe array-store cross-check must not produce false Unsafe: got {result}"
    );
}

#[test]
fn test_bmc_cross_check_model_checker_consumer_box_bool_stays_unknown_9185() {
    let smt2 = include_str!("../tests/fixtures/model_checker_consumer_9185_box_bool.smt2");

    let config = BmcConfig::cross_check()
        .with_max_depth(200)
        .with_time_budget(std::time::Duration::from_secs(2));
    let result =
        engines::solve_bmc_only_from_str(smt2, config).expect("should parse valid CHC benchmark");
    assert!(
        result.is_unknown(),
        "array proof cross-check must not use untrusted BMC SAT to contradict a proof: got {result}"
    );
}

fn is_bv32_to_bv32_array(sort: &ChcSort) -> bool {
    match sort {
        ChcSort::Array(key, value) => {
            matches!(
                (&**key, &**value),
                (ChcSort::BitVec(32), ChcSort::BitVec(32))
            )
        }
        _ => false,
    }
}

fn select_26_is_one(var: &ChcVar) -> ChcExpr {
    ChcExpr::eq(
        ChcExpr::select(ChcExpr::var(var.clone()), ChcExpr::BitVec(0x26, 32)),
        ChcExpr::BitVec(1, 32),
    )
}

fn model_checker_consumer_box_bool_original_signature_model(
    problem: &ChcProblem,
) -> InvariantModel {
    let mut model = InvariantModel::new();
    for pred in problem.predicates() {
        let vars = canonical_vars_for_pred(problem, pred.id).expect("predicate vars");
        let formula = if pred.name == "error" {
            ChcExpr::Bool(false)
        } else if pred.name == "test_box_bool__bb0" {
            ChcExpr::Bool(true)
        } else if let Some(array_var) = vars
            .iter()
            .rev()
            .find(|var| is_bv32_to_bv32_array(&var.sort))
        {
            select_26_is_one(array_var)
        } else {
            ChcExpr::Bool(true)
        };
        model.set(pred.id, PredicateInterpretation::new(vars, formula));
    }
    model
}

#[test]
fn test_external_model_validation_preserves_array_signature_model_checker_consumer_box_bool_8578() {
    let smt2 = include_str!("../tests/fixtures/model_checker_consumer_9185_box_bool.smt2");
    let problem =
        ChcParser::parse(smt2).expect("model-checker-consumer box_bool fixture should parse");
    let model = model_checker_consumer_box_bool_original_signature_model(&problem);

    let default_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut verifier = engines::new_pdr_solver(problem.clone(), PdrConfig::default());
        verifier.verify_model(&model)
    }));
    assert!(
        matches!(default_result, Ok(false)),
        "default PDR verifier should reject this original-signature Array model after \
         scalarizing predicate arguments; got {default_result:?}"
    );

    let validated =
        engines::validate_external_invariant_model(&problem, &model, &PdrConfig::default())
            .expect("external model validation should not panic");
    assert!(
        validated,
        "external invariant validation must preserve Array predicate arguments"
    );
}

#[test]
fn test_external_model_validation_always_preserves_original_clauses() {
    let src = include_str!("lib.rs");
    let fn_start = src
        .find("fn external_model_validation_config(base: &PdrConfig) -> PdrConfig")
        .expect("lib.rs should define external model validation config");
    let fn_body = &src[fn_start..];
    let fn_end = fn_body
        .find("/// Validate a caller-provided invariant model")
        .expect("external model validation config should precede public validation API");
    let fn_body = &fn_body[..fn_end];

    assert!(
        fn_body.contains("preserve_original_clauses: true"),
        "external model validation must always preserve the exact caller clauses"
    );
    assert!(
        !fn_body.contains("preserve_original_clauses: base.preserve_original_clauses"),
        "a caller must not be able to re-enable solve-time nullary query rewriting during validation"
    );
}

#[test]
fn test_external_model_validation_tiny_budget_fails_closed_before_query_only_acceptance_9413() {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pred, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let mut model = InvariantModel::new();
    model.set(
        pred,
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::le(ChcExpr::var(x), ChcExpr::int(0)),
        ),
    );

    assert!(
        engines::validate_external_invariant_model(&problem, &model, &PdrConfig::default())
            .expect("unbudgeted external model validation should not error"),
        "the query-only model is valid without deadline pressure"
    );

    for budget in [
        std::time::Duration::ZERO,
        std::time::Duration::from_nanos(1),
    ] {
        let accepted = engines::validate_external_invariant_model(
            &problem,
            &model,
            &PdrConfig {
                solve_timeout: Some(budget),
                ..PdrConfig::default()
            },
        )
        .expect("budgeted external model validation should fail closed, not error");
        assert!(
            !accepted,
            "external validation must not accept after an exhausted {budget:?} deadline"
        );
    }
}

#[test]
fn test_bmc_regular_array_real_unsafe_stays_unsafe_9185() {
    let smt2 = r#"
(set-logic HORN)
(declare-var a (Array (_ BitVec 32) (_ BitVec 32)))
(declare-rel Init ((Array (_ BitVec 32) (_ BitVec 32))))
(declare-rel Bad ())
(rule (=> (= (select a #x00000000) #x00000000) (Init a)))
(rule (=> (and (Init a) (not (= (select a #x00000026) #x00000001))) Bad))
(query Bad)
"#;

    let config = BmcConfig::default()
        .with_max_depth(3)
        .with_time_budget(std::time::Duration::from_secs(2));
    let result =
        engines::solve_bmc_only_from_str(smt2, config).expect("should parse valid CHC benchmark");
    assert!(
        result.is_unsafe(),
        "normal BMC must keep reporting genuine array counterexamples: got {result}"
    );
}

/// Test that cross_check() preset has the correct parameters for model-checker-consumer (#8412).
///
/// model-checker-consumer's cross-check use case requires:
/// - 30s timeout (matching the adaptive solver's total budget)
/// - Depth 200 (sufficient for program verification counterexamples)
/// - No k-induction (pure counterexample search)
/// - acyclic_safe=false (BMC returns Unknown, not Safe, when depth exhausted)
#[test]
fn test_cross_check_preset_matches_model_checker_consumer_requirements() {
    let config = BmcConfig::cross_check();
    assert_eq!(
        config.time_budget,
        Some(std::time::Duration::from_secs(30)),
        "cross_check should have 30s time budget"
    );
    assert_eq!(config.max_depth, 200, "cross_check should have depth 200");
    assert!(
        !config.enable_k_induction,
        "cross_check should NOT enable k-induction (pure counterexample search)"
    );
    assert!(
        !config.acyclic_safe,
        "cross_check should NOT set acyclic_safe (returns Unknown, not Safe)"
    );
    assert!(
        config.enable_adaptive_stepping,
        "cross_check should enable adaptive stepping for fast depth traversal"
    );
    assert!(
        config.proof_cross_check,
        "cross_check should enable proof-cross-check safety guards"
    );
}

/// Diagnostic: the exact horn clauses produced by the Trust compiler's
/// `guarded(a: u32) -> u32 { if a < 100 { assert!(a < 100); a } else { 0 } }`
/// after external-codegen-ir lowering + CHC translation. The property is TRUE (the assert
/// can never fail), so a sound proof engine must prove it Safe.
///
/// This test documents the root-cause gap: proof-grade PDR returns
/// Inconclusive on this acyclic/scalar/BitVec/multi-predicate problem, while
/// the exact acyclic BMC machinery (acyclic_safe) discharges it as Safe.
const GUARDED_COMPILER_HORN: &str = "\
(declare-rel bb0 ((_ BitVec 32)))
(declare-rel bb1 ((_ BitVec 32)))
(declare-rel bb2 ())
(declare-rel bb3 ())
(declare-rel bb4 ())
(declare-rel error ())
(declare-var bb0_v0 (_ BitVec 32))
(declare-var bb1_v3 (_ BitVec 32))
(rule (=> true (bb0 bb0_v0)))
(rule (=> (and (bb0 bb0_v0) (bvult bb0_v0 #x00000064)) (bb1 bb0_v0)))
(rule (=> (and (bb0 bb0_v0) (not (bvult bb0_v0 #x00000064))) bb4))
(rule (=> (and (bb1 bb1_v3) (bvult bb1_v3 #x00000064)) bb3))
(rule (=> (and (bb1 bb1_v3) (not (bvult bb1_v3 #x00000064))) bb2))
(rule (=> (and bb2 (not false)) error))
(rule (=> (and bb2 true) error))
(query error)
";

#[test]
fn diag_guarded_compiler_horn_acyclic_bmc_proves() {
    let problem = ChcParser::parse(GUARDED_COMPILER_HORN).expect("parse guarded horn");

    let features = crate::classifier::ProblemClassifier::classify(&problem);
    eprintln!(
        "classify: has_cycles={} num_predicates={} has_bv={} uses_arrays={} dag_depth={}",
        features.has_cycles,
        features.num_predicates,
        problem.has_bv_sorts(),
        features.uses_arrays,
        features.dag_depth,
    );

    // 1) Proof-grade path must now accept this via the exact acyclic prepass.
    let pdr = engines::solve_pdr_proof(
        problem.clone(),
        PdrConfig::production(false).with_strict_proofs(true),
    )
    .expect("pdr run");
    eprintln!(
        "PDR proof-grade accepted_as_proof={}",
        pdr.accepted_as_proof()
    );
    assert!(
        pdr.accepted_as_proof(),
        "proof-grade solve_pdr_proof must prove the guarded property via the \
         exact acyclic BMC certificate prepass"
    );

    // 2) Candidate fix: exact acyclic BMC must discharge it as Safe.
    let depth = features.dag_depth.max(features.num_predicates).max(1);
    let bmc_config = BmcConfig {
        base: crate::engine_config::ChcEngineConfig {
            verbose: false,
            cancellation_token: None,
        },
        max_depth: depth,
        acyclic_safe: true,
        prefer_exact_acyclic_first: true,
        per_depth_timeout: None,
        time_budget: Some(std::time::Duration::from_secs(30)),
        enable_k_induction: false,
        enable_adaptive_stepping: false,
        proof_cross_check: false,
        ts_probe_clamp: None,
        sweep_past_spurious_sat: true,
    };
    let bmc = BmcSolver::new(problem.clone(), bmc_config).solve();
    eprintln!("direct acyclic BmcSolver: {bmc:?}");

    assert!(
        matches!(bmc, PortfolioResult::Safe(_)),
        "exact acyclic BMC must prove the guarded property Safe, got {bmc:?}"
    );
}

/// Soundness guard for the acyclic-BMC proof path: the UNGUARDED property
/// `unguarded(a: u32) -> u32 { assert!(a < 100); a }` is FALSE (a >= 100
/// reaches the panic). The exact acyclic BMC must return Unsafe — never a
/// spurious Safe from `acyclic_safe` exhaustion.
const UNGUARDED_COMPILER_HORN: &str = "\
(declare-rel bb0 ((_ BitVec 32)))
(declare-rel cont ())
(declare-rel panic ())
(declare-rel error ())
(declare-var a (_ BitVec 32))
(rule (=> true (bb0 a)))
(rule (=> (and (bb0 a) (bvult a #x00000064)) cont))
(rule (=> (and (bb0 a) (not (bvult a #x00000064))) panic))
(rule (=> (and panic (not false)) error))
(rule (=> (and panic true) error))
(query error)
";

#[test]
fn diag_unguarded_compiler_horn_acyclic_bmc_refutes() {
    let problem = ChcParser::parse(UNGUARDED_COMPILER_HORN).expect("parse unguarded horn");
    let features = crate::classifier::ProblemClassifier::classify(&problem);
    let depth = features.dag_depth.max(features.num_predicates).max(1);
    let bmc_config = BmcConfig {
        base: crate::engine_config::ChcEngineConfig {
            verbose: false,
            cancellation_token: None,
        },
        max_depth: depth,
        acyclic_safe: true,
        prefer_exact_acyclic_first: true,
        per_depth_timeout: None,
        time_budget: Some(std::time::Duration::from_secs(30)),
        enable_k_induction: false,
        enable_adaptive_stepping: false,
        proof_cross_check: false,
        ts_probe_clamp: None,
        sweep_past_spurious_sat: true,
    };
    let bmc = BmcSolver::new(problem.clone(), bmc_config).solve();
    eprintln!("direct acyclic BmcSolver (unguarded): {bmc:?}");
    assert!(
        !matches!(bmc, PortfolioResult::Safe(_)),
        "acyclic BMC must NOT prove the false unguarded property Safe, got {bmc:?}"
    );

    // Soundness at the proof-grade boundary: the exact acyclic prepass must
    // not turn the FALSE property into an accepted SAFE proof. A verified
    // UNSAFE refutation is the CORRECT settled verdict here (the property is
    // false): since inc-9 the bounded-BMC cex replay can confirm PDR's
    // counterexample against the original clauses, so this run may now be
    // accepted as Unsafe proof evidence — only Safe remains forbidden.
    let pdr = engines::solve_pdr_proof(
        problem.clone(),
        PdrConfig::production(false).with_strict_proofs(true),
    )
    .expect("pdr run");
    eprintln!(
        "PDR proof-grade (unguarded) accepted_as_proof={} result_is_safe={}",
        pdr.accepted_as_proof(),
        matches!(pdr.result, VerifiedChcResult::Safe(_)),
    );
    assert!(
        !matches!(pdr.result, VerifiedChcResult::Safe(_)),
        "proof-grade solve_pdr_proof must NOT prove the false unguarded property Safe"
    );
}

/// model-checker-consumer overlap_copy: an ACYCLIC linear system whose error is plainly
/// reachable — a violated `copy_nonoverlapping` disjointness obligation
/// folds to an unconditional `bb -> error` rule. The exact acyclic BMC
/// probe finds the SAT branch; converting it into an Unsafe verdict
/// requires witness extraction to cover systems that merely DECLARE
/// datatype sorts (`model_derivation_witness` bails on
/// `has_datatype_sorts` today, and model-checker-consumer systems always declare them).
///
/// Pin: the solver must never claim Safe here — the error IS derivable.
#[test]
fn test_bmc_acyclic_model_checker_consumer_overlap_copy_never_safe() {
    let smt2 =
        include_str!("../tests/fixtures/model_checker_consumer_overlap_copy_acyclic_unsafe.smt2");
    let config = BmcConfig::default()
        .with_max_depth(64)
        .with_time_budget(std::time::Duration::from_secs(5));
    let result = engines::solve_bmc_only_from_str(smt2, config).expect("fixture should parse");
    assert!(
        !result.is_safe(),
        "error is reachable; Safe would be a false proof: got {result}"
    );
}

/// The SAT branch of an exact acyclic expansion is a genuine counterexample
/// and becomes a replay-validated Unsafe now that the safe-first sites route
/// SAT through `bmc_sat_result` -> `verified_unsafe_from_witness` (the
/// datatype declaration in the fixture is unused in predicate signatures, so
/// witness extraction proceeds).
#[test]
fn test_bmc_acyclic_model_checker_consumer_overlap_copy_reports_unsafe() {
    let smt2 =
        include_str!("../tests/fixtures/model_checker_consumer_overlap_copy_acyclic_unsafe.smt2");
    // The exact-acyclic route is what this test is about, and
    // `prefer_exact_acyclic_executor_first` only takes it when BOTH flags are
    // set (or the problem has >128 predicates, which this fixture does not).
    // With a plain `BmcConfig::default()` the run fell back to incremental
    // deepening, whose per-depth cost on this fixture grows quadratically
    // (~5s/depth by depth 14) while the counterexample is at depth 31 — so the
    // budget always expired mid-search, which is not what the assertion is
    // meant to be measuring. Matches the sibling `vec13` / `fib_fail` cases.
    let config = BmcConfig {
        max_depth: 64,
        acyclic_safe: true,
        prefer_exact_acyclic_first: true,
        time_budget: Some(std::time::Duration::from_mins(1)),
        ..BmcConfig::default()
    };
    let result = engines::solve_bmc_only_from_str(smt2, config).expect("fixture should parse");
    assert!(
        result.is_unsafe(),
        "exact acyclic SAT branch is a genuine counterexample: got {result}"
    );
}

/// model-checker-consumer fib_fail (smack recursion/fib benchmark, bug genuinely
/// reachable): an ACYCLIC linear BV64 system (the encoder unrolls the
/// nonlinear recursion into an acyclic clause DAG, depth 73) whose exact
/// acyclic SAT branch previously degraded to Unknown: witness-path
/// variables (`__bmc_dag_e*_v*` don't-cares plus clause_var_renaming
/// values) were never grounded, so `acyclic_branch_witness` failed closed
/// with "arg N ... not evaluable", and BV64 values >= 2^63 were dropped by
/// the i64 witness-value funnel.
///
/// Pin: the solver must never claim Safe here — the error IS derivable.
#[test]
fn test_bmc_acyclic_model_checker_consumer_fib_fail_never_safe() {
    let smt2 = include_str!(
        "../tests/fixtures/model_checker_consumer_fib_fail_nonlinear_recursion_unsafe.smt2"
    );
    let config = BmcConfig::default()
        .with_max_depth(96)
        .with_time_budget(std::time::Duration::from_secs(10));
    let result = engines::solve_bmc_only_from_str(smt2, config).expect("fixture should parse");
    assert!(
        !result.is_safe(),
        "error is reachable; Safe would be a false proof: got {result}"
    );
}

/// Companion to `test_bmc_acyclic_model_checker_consumer_fib_fail_never_safe`: with
/// witness-path grounding and the SmtValue-native BV64 value path, the
/// exact acyclic SAT branch (the lane the adaptive acyclic probe uses)
/// becomes a replay-validated Unsafe.
#[test]
fn test_bmc_acyclic_model_checker_consumer_fib_fail_reports_unsafe() {
    let smt2 = include_str!(
        "../tests/fixtures/model_checker_consumer_fib_fail_nonlinear_recursion_unsafe.smt2"
    );
    let config = BmcConfig {
        max_depth: 96,
        acyclic_safe: true,
        prefer_exact_acyclic_first: true,
        time_budget: Some(std::time::Duration::from_mins(1)),
        ..BmcConfig::default()
    };
    let result = engines::solve_bmc_only_from_str(smt2, config).expect("fixture should parse");
    assert!(
        result.is_unsafe(),
        "exact acyclic SAT branch is a genuine counterexample: got {result}"
    );
}

/// model-checker-consumer test1 (deep replay): a CYCLIC linear BV32 system whose
/// counterexample lives at depth ~43 — deeper than the transformed-witness
/// depth hint (which clamped the bounded cex replay to 18 before iterative
/// deepening). The verdict was computed by TRL and then discarded when the
/// under-shot replay failed to confirm.
///
/// Pin: the solver must never claim Safe here — the error IS derivable.
#[test]
fn test_bmc_model_checker_consumer_test1_deep_replay_never_safe() {
    let smt2 =
        include_str!("../tests/fixtures/model_checker_consumer_test1_deep_replay_unsafe.smt2");
    let config = BmcConfig::default()
        .with_max_depth(64)
        .with_time_budget(std::time::Duration::from_secs(10));
    let result = engines::solve_bmc_only_from_str(smt2, config).expect("fixture should parse");
    assert!(
        !result.is_safe(),
        "error is reachable; Safe would be a false proof: got {result}"
    );
}

/// model-checker-consumer vec13 (smack vector benchmark): an ACYCLIC linear BV64 system,
/// genuinely sat at the CHC level (encoder over-approximation). Same
/// witness-grounding / BV64-value-funnel failure class as fib_fail.
///
/// Pin: the solver must never claim Safe here — the error IS derivable.
#[test]
fn test_bmc_acyclic_model_checker_consumer_vec13_never_safe() {
    let smt2 = include_str!("../tests/fixtures/model_checker_consumer_vec13_acyclic_unsafe.smt2");
    let config = BmcConfig::default()
        .with_max_depth(64)
        .with_time_budget(std::time::Duration::from_secs(10));
    let result = engines::solve_bmc_only_from_str(smt2, config).expect("fixture should parse");
    assert!(
        !result.is_safe(),
        "error is reachable; Safe would be a false proof: got {result}"
    );
}

/// model-checker-consumer gauss_sum_nondet (smack loops benchmark, bug genuinely
/// reachable): with witness-path grounding and the SmtValue-native BV64
/// value path the solver reports a replay-validated Unsafe.
///
/// Pin: the solver must never claim Safe here — the error IS derivable.
#[test]
fn test_bmc_model_checker_consumer_gauss_sum_nondet_never_safe() {
    let smt2 =
        include_str!("../tests/fixtures/model_checker_consumer_gauss_sum_nondet_unsafe.smt2");
    let config = BmcConfig::default()
        .with_max_depth(64)
        .with_time_budget(std::time::Duration::from_secs(10));
    let result = engines::solve_bmc_only_from_str(smt2, config).expect("fixture should parse");
    assert!(
        !result.is_safe(),
        "error is reachable; Safe would be a false proof: got {result}"
    );
}

/// Companion to `test_bmc_model_checker_consumer_gauss_sum_nondet_never_safe`: the exact
/// acyclic SAT branch (dag_depth 46) becomes a replay-validated Unsafe with
/// the witness-grounding and BV64 value fixes.
#[test]
fn test_bmc_acyclic_model_checker_consumer_gauss_sum_nondet_reports_unsafe() {
    let smt2 =
        include_str!("../tests/fixtures/model_checker_consumer_gauss_sum_nondet_unsafe.smt2");
    let config = BmcConfig {
        max_depth: 64,
        acyclic_safe: true,
        prefer_exact_acyclic_first: true,
        time_budget: Some(std::time::Duration::from_mins(1)),
        ..BmcConfig::default()
    };
    let result = engines::solve_bmc_only_from_str(smt2, config).expect("fixture should parse");
    assert!(
        result.is_unsafe(),
        "exact acyclic SAT branch is a genuine counterexample: got {result}"
    );
}

/// Companion to `test_bmc_acyclic_model_checker_consumer_vec13_never_safe`: with nested
/// clause-constraint conjuncts flattened for the branch-model equality
/// propagation (plus witness-path grounding and the SmtValue-native BV64
/// value path), the exact acyclic SAT branch becomes a replay-validated
/// Unsafe instead of a spurious rejection.
#[test]
fn test_bmc_acyclic_model_checker_consumer_vec13_reports_unsafe() {
    let smt2 = include_str!("../tests/fixtures/model_checker_consumer_vec13_acyclic_unsafe.smt2");
    let config = BmcConfig {
        max_depth: 64,
        acyclic_safe: true,
        prefer_exact_acyclic_first: true,
        time_budget: Some(std::time::Duration::from_mins(1)),
        ..BmcConfig::default()
    };
    let result = engines::solve_bmc_only_from_str(smt2, config).expect("fixture should parse");
    assert!(
        result.is_unsafe(),
        "exact acyclic SAT branch is a genuine counterexample: got {result}"
    );
}

// --- Phase-2 BigInt escape: end-to-end PDR verdicts with beyond-i128 constants ---
//
// Measured baseline (2026-07, wishlist rank 6 follow-up): CHC UNSAFE verdicts
// whose counterexample witness exceeds i128 degraded to Unknown ("CHC
// portfolio exhausted") because model extraction skipped beyond-i128 LIA
// values and the missing-var gate demoted verified Sat to Unknown. These
// probes pin the flip unknown→unsat and the negative controls.

/// `2^128 + 1` as an SMT-LIB decimal literal.
const BIG_PROBE_DEC: &str = "340282366920938463463374607431768211457";

fn solve_probe(smt2: &str) -> PdrResult {
    let problem = ChcParser::parse(smt2).expect("probe must parse");
    let config = PdrConfig {
        max_frames: 8,
        max_iterations: 100,
        max_obligations: 10_000,
        ..PdrConfig::default()
    };
    PdrSolver::new(problem, config).solve()
}

/// horn_unsafe_big: P(x) ⟸ x = 2^128+1; P(x) ∧ x > 0 ⟹ false.
/// Reachable only through the beyond-i128 witness — must be Unsafe (was
/// Unknown). This trivial 2-clause shape resolves through PDR's
/// init-violation lane (empty-steps counterexample by invariant #3095);
/// witness content is pinned by the 3-clause variant below.
#[test]
fn test_pdr_unsafe_with_beyond_i128_witness() {
    let smt2 = format!(
        "(set-logic HORN)\n\
         (declare-fun P (Int) Bool)\n\
         (assert (forall ((x Int)) (=> (= x {BIG_PROBE_DEC}) (P x))))\n\
         (assert (forall ((x Int)) (=> (and (P x) (> x 0)) false)))\n\
         (check-sat)"
    );
    assert!(
        matches!(solve_probe(&smt2), PdrResult::Unsafe(_)),
        "beyond-i128 equality probe must yield Unsafe"
    );
}

/// A 2-predicate chain (P → Q) forces a real derivation instead of the
/// trivial init-violation lane: the counterexample must carry the exact
/// beyond-i128 value in its derivation witness (via SmtValue's derived
/// Debug — this also guards the witness printing path).
#[test]
fn test_pdr_unsafe_beyond_i128_derivation_witness_carries_value() {
    let smt2 = format!(
        "(set-logic HORN)\n\
         (declare-fun P (Int) Bool)\n\
         (declare-fun Q (Int) Bool)\n\
         (assert (forall ((x Int)) (=> (= x {BIG_PROBE_DEC}) (P x))))\n\
         (assert (forall ((x Int)) (=> (P x) (Q x))))\n\
         (assert (forall ((x Int)) (=> (and (Q x) (> x 0)) false)))\n\
         (check-sat)"
    );
    match solve_probe(&smt2) {
        PdrResult::Unsafe(cex) => {
            let printed = format!("{cex:?}");
            assert!(
                printed.contains(BIG_PROBE_DEC),
                "derivation witness must carry the exact BigInt value; got {printed}"
            );
        }
        other => panic!("expected Unsafe with a beyond-i128 witness, got {other:?}"),
    }
}

/// horn_unsafe_cmp_big: P(x) ⟸ x > 2^128+1; P(x) ∧ x > 5 ⟹ false.
/// The comparison feeder shape — must be Unsafe (was Unknown).
#[test]
fn test_pdr_unsafe_with_beyond_i128_comparison_feeder() {
    let smt2 = format!(
        "(set-logic HORN)\n\
         (declare-fun P (Int) Bool)\n\
         (assert (forall ((x Int)) (=> (> x {BIG_PROBE_DEC}) (P x))))\n\
         (assert (forall ((x Int)) (=> (and (P x) (> x 5)) false)))\n\
         (check-sat)"
    );
    assert!(
        matches!(solve_probe(&smt2), PdrResult::Unsafe(_)),
        "beyond-i128 comparison feeder must yield Unsafe"
    );
}

/// Negative control (horn_safe_big): P(x) ⟸ x = 2^128+1; P(x) ∧ x < 0 ⟹
/// false is SAFE — the escape opens no fail-open channel on the safe side.
#[test]
fn test_pdr_safe_with_beyond_i128_constant_stays_safe() {
    let smt2 = format!(
        "(set-logic HORN)\n\
         (declare-fun P (Int) Bool)\n\
         (assert (forall ((x Int)) (=> (= x {BIG_PROBE_DEC}) (P x))))\n\
         (assert (forall ((x Int)) (=> (and (P x) (< x 0)) false)))\n\
         (check-sat)"
    );
    match solve_probe(&smt2) {
        PdrResult::Safe(_) => {}
        PdrResult::Unsafe(cex) => {
            panic!("BUG (fail-open): safe beyond-i128 probe reported Unsafe: {cex:?}")
        }
        other => panic!("safe beyond-i128 probe must stay Safe, got {other:?}"),
    }
}

/// Negative control at exactly i128::MAX (in-range lane unchanged): still
/// Unsafe, with the witness carried as a plain Int in the derivation
/// (same 2-predicate chain shape as the BigInt witness test above).
#[test]
fn test_pdr_unsafe_at_i128_max_control() {
    let smt2 = format!(
        "(set-logic HORN)\n\
         (declare-fun P (Int) Bool)\n\
         (declare-fun Q (Int) Bool)\n\
         (assert (forall ((x Int)) (=> (= x {max}) (P x))))\n\
         (assert (forall ((x Int)) (=> (P x) (Q x))))\n\
         (assert (forall ((x Int)) (=> (and (Q x) (> x 0)) false)))\n\
         (check-sat)",
        max = i128::MAX
    );
    match solve_probe(&smt2) {
        PdrResult::Unsafe(cex) => {
            let printed = format!("{cex:?}");
            assert!(
                printed.contains(&i128::MAX.to_string()),
                "i128::MAX witness must survive in the counterexample; got {printed}"
            );
        }
        other => panic!("expected Unsafe at the i128 boundary control, got {other:?}"),
    }
}

/// Multi-pred acyclic-exhaustive (empty-model) SAFE: the replay-obligation
/// helper re-validates via the deterministic exhaustive re-run and returns
/// an EMPTY obligation set instead of the historical hard error
/// "missing invariant interpretation for predicate ..." (multi-pred
/// replay-exporter gap: the acyclic BMC lane's proof has no invariants).
#[test]
fn chc_safe_replay_obligations_empty_model_acyclic_safe_is_empty_set() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("p", vec![ChcSort::Int]);
    let q = problem.declare_predicate("q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    // x = 0 -> P(x)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![],
            Some(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));
    // P(x) /\ y = x + 1 -> Q(y)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(y.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            )),
        ),
        ClauseHead::Predicate(q, vec![ChcExpr::var(y.clone())]),
    ));
    // Q(y) /\ y < 0 -> false   (unreachable: y is exactly 1)
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(q, vec![ChcExpr::var(y.clone())])],
        Some(ChcExpr::lt(ChcExpr::var(y.clone()), ChcExpr::int(0))),
    )));

    let model = InvariantModel::new();
    let obligations = engines::chc_safe_replay_obligations(&problem, &model)
        .expect("acyclic-exhaustive empty-model SAFE must export (empty) obligations");
    assert!(
        obligations.is_empty(),
        "exhaustion proofs have no invariant obligations; got {}",
        obligations.len()
    );
}

/// Fail-closed control: an empty model on an acyclic problem whose error IS
/// reachable must NOT get the empty-obligation shortcut — the exhaustive
/// re-run refuses to confirm, and the standard exporter's
/// missing-interpretation error is preserved.
#[test]
fn chc_safe_replay_obligations_empty_model_unsafe_problem_keeps_error() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("p", vec![ChcSort::Int]);
    let q = problem.declare_predicate("q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![],
            Some(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(y.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            )),
        ),
        ClauseHead::Predicate(q, vec![ChcExpr::var(y.clone())]),
    ));
    // Q(y) /\ y > 0 -> false   (REACHABLE: y = 1)
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(q, vec![ChcExpr::var(y.clone())])],
        Some(ChcExpr::gt(ChcExpr::var(y.clone()), ChcExpr::int(0))),
    )));

    let model = InvariantModel::new();
    let error = engines::chc_safe_replay_obligations(&problem, &model)
        .expect_err("unsafe problem must not receive the empty-obligation shortcut");
    assert!(
        error
            .to_string()
            .contains("missing invariant interpretation"),
        "fail-closed error must be preserved; got: {error}"
    );
}

/// Non-empty models bypass the acyclic-exhaustive branch entirely: behavior
/// identical to `InvariantModel::replay_obligations` (here: hard error on the
/// predicate the model does not cover).
#[test]
fn chc_safe_replay_obligations_non_empty_model_unchanged() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("p", vec![ChcSort::Int]);
    let q = problem.declare_predicate("q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![],
            Some(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
    ));

    let mut model = InvariantModel::new();
    let param = ChcVar::new("x", ChcSort::Int);
    model.set(
        p,
        PredicateInterpretation::new(
            vec![param.clone()],
            ChcExpr::ge(ChcExpr::var(param), ChcExpr::int(0)),
        ),
    );
    // q has no interpretation and the model is non-empty -> standard error.
    let error = engines::chc_safe_replay_obligations(&problem, &model)
        .expect_err("partial non-empty model keeps the standard exporter error");
    assert!(error
        .to_string()
        .contains("missing invariant interpretation"));
}

/// A model that is NOT inductive must never be certified as a proof.
///
/// The transition system below is genuinely UNSAFE — 0 -> 1 -> 2 reaches `error`:
///     x = 0                        => Inv(x)
///     Inv(x) ∧ x ≤ 0 ∧ x' = x + 1  => Inv(x')
///     Inv(x) ∧ x ≥ 1 ∧ x' = x + 1  => Inv(x')
///     Inv(x) ∧ x = 2               => error
/// so NO invariant model is valid, and `I(x) := x ≤ 1 ∧ ¬(x = 1)` in particular is
/// not inductive: from `x = 0` the first transition reaches `x' = 1`, where
/// `¬(x' = 1)` fails. Any certification here would be a false PROOF.
///
/// SCOPE — measured, so nobody over-reads this test: it was written to try to
/// exercise a specific hole (the "best-effort longer timeout" arm of
/// `pdr/verification/model_inductive_unknown.rs` accepts a discharge of the
/// WEAKENED `query_filtered` without setting `used_filtered_invariant`, so the #73
/// query re-check is skipped). It does NOT discriminate that hole: the model is
/// rejected both with and without that flag set, i.e. some other backstop catches
/// this shape first. Keep it as a general non-inductive-rejection guard; do NOT
/// cite it as evidence about the filtered-head path.
#[test]
fn filtered_head_must_not_certify_a_non_inductive_model() {
    let smt2 = r#"
(declare-rel Inv (Int))
(declare-rel error ())
(declare-var x Int)
(declare-var xp Int)
(rule (=> (= x 0) (Inv x)))
(rule (=> (and (Inv x) (<= x 0) (= xp (+ x 1))) (Inv xp)))
(rule (=> (and (Inv x) (>= x 1) (= xp (+ x 1))) (Inv xp)))
(rule (=> (and (Inv x) (= x 2)) error))
(query error)
"#;
    let problem = ChcParser::parse(smt2).expect("witness fixture should parse");
    let inv = problem.lookup_predicate("Inv").expect("Inv predicate");
    let error = problem.lookup_predicate("error").expect("error predicate");
    let x = ChcVar::new("x", ChcSort::Int);

    // I(x) := (x <= 1) AND NOT(x = 1) — the point-blocking conjunct is exactly
    // what `filter_blocking_lemmas` throws away.
    let candidate = ChcExpr::and(
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ChcExpr::not(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(1))),
    );

    let mut model = InvariantModel::new();
    model.set(inv, PredicateInterpretation::new(vec![x], candidate));
    model.set(
        error,
        PredicateInterpretation::new(Vec::new(), ChcExpr::Bool(false)),
    );

    let config = PdrConfig::default();
    let certified = engines::validate_external_invariant_model(&problem, &model, &config)
        .expect("validation should not panic");
    assert!(
        !certified,
        "FALSE PROOF: a model that is not inductive on the real head was certified. \
         The transition system reaches `error` via 0 -> 1 -> 2, so no invariant model \
         can be valid here; acceptance means a weakened head was used as a certificate."
    );
}
