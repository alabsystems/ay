//! Unit tests for `super` (optimize/mod.rs).
//! Extracted verbatim to keep the production module readable.

use std::cell::Cell;

use super::*;
use crate::parse_opb;

fn engine_from_opb(input: &str) -> OptimizationEngine<'static> {
    let instance = parse_opb(input).expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);
    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    let objective = instance.objective.as_ref().expect("has objective");
    OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || false,
    )
}

fn engine_from_manual_base(
    num_pb_vars: u32,
    base_cnf: EncodedCnf,
    objective: PbObjective,
) -> OptimizationEngine<'static> {
    let mut base_solver = SatSolver::new(base_cnf.num_vars as usize);
    for clause in &base_cnf.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    OptimizationEngine::new(base_solver, objective, base_cnf, num_pb_vars, || false)
}

fn forced_zero_cost_engine(stop: &Cell<bool>) -> OptimizationEngine<'_> {
    let base_cnf = EncodedCnf {
        num_vars: 1,
        clauses: vec![vec![-1]],
    };
    let mut base_solver = SatSolver::new(base_cnf.num_vars as usize);
    base_solver.add_clause(vec![Literal::negative(Variable::new(0))]);

    OptimizationEngine::new(
        base_solver,
        PbObjective {
            terms: vec![PbTerm {
                coeff: 1,
                lits: vec![PbLit {
                    var: 1,
                    negated: false,
                }],
            }],
        },
        base_cnf,
        1,
        || stop.get(),
    )
}

fn free_positive_literal_engine(stop: &Cell<bool>) -> OptimizationEngine<'_> {
    let base_cnf = EncodedCnf {
        num_vars: 1,
        clauses: Vec::new(),
    };
    let base_solver = SatSolver::new(base_cnf.num_vars as usize);

    OptimizationEngine::new(
        base_solver,
        PbObjective {
            terms: vec![PbTerm {
                coeff: 1,
                lits: vec![PbLit {
                    var: 1,
                    negated: false,
                }],
            }],
        },
        base_cnf,
        1,
        || stop.get(),
    )
}

fn choice_positive_literal_engine(stop: &Cell<bool>) -> OptimizationEngine<'_> {
    let base_cnf = EncodedCnf {
        num_vars: 2,
        clauses: vec![vec![1, 2]],
    };
    let mut base_solver = SatSolver::new(base_cnf.num_vars as usize);
    base_solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);

    OptimizationEngine::new(
        base_solver,
        PbObjective {
            terms: vec![PbTerm {
                coeff: 1,
                lits: vec![PbLit {
                    var: 1,
                    negated: false,
                }],
            }],
        },
        base_cnf,
        2,
        || stop.get(),
    )
}

#[test]
fn test_engine_respects_constraints() {
    // min: +1 x1 +1 x2 subject to: +1 x1 +1 x2 >= 1
    // Optimal: exactly one true, cost = 1
    let input = "* #variable= 2 #constraint= 1\nmin: +1 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);

    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    let objective = instance.objective.as_ref().expect("has objective");
    let mut engine = OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || false,
    );

    let result = engine.solve();
    match result {
        OptResult::Optimal(assignment, obj_value) => {
            assert_eq!(obj_value, 1, "optimal cost should be 1");
            // Verify constraint is satisfied
            let satisfied = crate::eval_constraint(&instance.constraints[0], &assignment);
            assert!(satisfied, "constraint must be satisfied");
        }
        other => panic!("expected Optimal, got: {other:?}"),
    }
}

#[test]
fn test_engine_pre_clone_memory_guard_declines_to_unknown() {
    // Under memory pressure (current usage already past the pre-clone
    // fraction of the limit), `solve` must decline BEFORE its first
    // `clone_for_incremental`, returning `Unknown` — never a fabricated
    // verdict. With the limit cleared the very same engine solves normally,
    // proving the guard is a strict no-op when there is budget.
    let input = "* #variable= 2 #constraint= 1\nmin: +1 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n";

    // A 1 KB limit makes the running test process exceed any nonzero
    // percentage, so the predictive pre-clone probe trips immediately.
    let old_limit = ay_sys::get_process_memory_limit();
    ay_sys::set_process_memory_limit(1024);
    let mut engine = engine_from_opb(input);
    let guarded = engine.solve();
    // Restore the global limit before asserting so a failure cannot leak the
    // tiny limit into other tests running concurrently.
    ay_sys::set_process_memory_limit(old_limit);
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    assert_eq!(
        guarded,
        OptResult::Unknown,
        "pre-clone memory guard must decline to Unknown under pressure"
    );

    // No-op when there is budget: same instance now solves to the optimum.
    let mut engine = engine_from_opb(input);
    match engine.solve() {
        OptResult::Optimal(_, obj_value) => {
            assert_eq!(obj_value, 1, "unpressured solve must find the optimum");
        }
        other => panic!("expected Optimal with budget, got: {other:?}"),
    }
}

#[test]
fn test_engine_infeasible() {
    // Contradictory constraints: +1 x1 >= 1 AND -1 x1 >= 0
    let input = "* #variable= 1 #constraint= 2\nmin: +1 x1 ;\n+1 x1 >= 1 ;\n-1 x1 >= 0 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);

    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    let objective = instance.objective.as_ref().expect("has objective");
    let mut engine = OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || false,
    );

    let result = engine.solve();
    assert_eq!(result, OptResult::Infeasible);
}

#[test]
fn test_engine_zero_cost_optimal() {
    // min: +1 x2 subject to: +1 x1 >= 1
    // x1 must be true, x2 can be false -> cost 0
    let input = "* #variable= 2 #constraint= 1\nmin: +1 x2 ;\n+1 x1 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);

    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    let objective = instance.objective.as_ref().expect("has objective");
    let mut engine = OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || false,
    );

    let result = engine.solve();
    match result {
        OptResult::Optimal(assignment, obj_value) => {
            assert_eq!(obj_value, 0, "optimal cost should be 0");
            assert!(assignment[0], "x1 must be true");
            assert!(!assignment[1], "x2 should be false for cost 0");
        }
        other => panic!("expected Optimal, got: {other:?}"),
    }
}

#[test]
fn test_initial_structural_optimum_survives_interrupt_after_incumbent() {
    for strategy in [
        OptStrategy::Linear,
        OptStrategy::BinarySearch,
        OptStrategy::CoreGuided,
    ] {
        let stop = Cell::new(false);
        let mut engine = forced_zero_cost_engine(&stop);
        engine.set_on_improve(|_| stop.set(true));

        let result = match strategy {
            OptStrategy::Linear => linear::solve(&mut engine),
            OptStrategy::BinarySearch => binary_search::solve(&mut engine),
            OptStrategy::CoreGuided => core_guided::solve(&mut engine),
        };

        match result {
            OptResult::Optimal(assignment, obj_value) => {
                assert_eq!(obj_value, 0, "{strategy:?} should keep the proven optimum");
                assert_eq!(
                    assignment,
                    vec![false],
                    "{strategy:?} should keep the valid incumbent assignment"
                );
            }
            other => panic!("{strategy:?} downgraded a structural optimum to {other:?}"),
        }
    }
}

#[test]
fn test_binary_refine_closes_lower_bound_before_interrupt_after_improvement() {
    let stop = Cell::new(false);
    let mut engine = free_positive_literal_engine(&stop);
    engine.set_on_improve(|_| stop.set(true));

    let result = engine.binary_refine(vec![true], 1, 0);
    match result {
        OptResult::Optimal(assignment, obj_value) => {
            assert_eq!(
                obj_value, 0,
                "refined incumbent reaches the proven lower bound"
            );
            assert_eq!(
                assignment,
                vec![false],
                "returned incumbent should satisfy the closed lower-bound optimum"
            );
        }
        other => panic!("lower-bound closure was downgraded to {other:?}"),
    }
    assert!(
        stop.get(),
        "interrupt predicate should be armed by the improvement"
    );
}

#[test]
fn test_linear_refine_closes_lower_bound_before_interrupt_after_improvement() {
    let stop = Cell::new(false);
    let improvements = Cell::new(0usize);
    let mut engine = choice_positive_literal_engine(&stop);

    match engine.solve_base_query() {
        QueryOutcome::Sat { obj_value, .. } => {
            assert_eq!(obj_value, 1, "test must start above the lower bound");
        }
        other => panic!("expected initial SAT incumbent, got: {other:?}"),
    }

    engine.set_on_improve(|obj_value| {
        improvements.set(improvements.get() + 1);
        if obj_value == 0 {
            stop.set(true);
        }
    });

    let result = linear::solve(&mut engine);
    match result {
        OptResult::Optimal(assignment, obj_value) => {
            assert_eq!(
                obj_value, 0,
                "refined incumbent reaches the proven lower bound"
            );
            assert_eq!(
                assignment,
                vec![false, true],
                "returned incumbent should satisfy the closed lower-bound optimum"
            );
        }
        other => panic!("lower-bound closure was downgraded to {other:?}"),
    }
    assert_eq!(
        improvements.get(),
        2,
        "linear regression must exercise the post-query improvement path"
    );
    assert!(
        stop.get(),
        "interrupt predicate should be armed by the improvement"
    );
}

#[test]
fn test_objective_lower_bound_uses_complementary_cost_normalization() {
    let mut input = String::from("* #variable= 20 #constraint= 0\nmin:");
    for var in 1..=20u32 {
        input.push_str(&format!(" +1000 x{var} +999 ~x{var}"));
    }
    input.push_str(" ;\n");

    let engine = engine_from_opb(&input);
    let stats = engine.objective_stats();
    assert_eq!(stats.lower_bound, 0);
    assert_eq!(
        engine.objective_lower_bound(),
        19_980,
        "complementary OPT-LIN costs should expose the normalized residual lower bound"
    );
}

#[test]
fn test_engine_solve_returns_unknown_when_objective_range_overflows_i64() {
    let mut engine = engine_from_manual_base(
        2,
        EncodedCnf {
            num_vars: 2,
            clauses: vec![vec![1], vec![2]],
        },
        PbObjective {
            terms: vec![
                PbTerm {
                    coeff: i128::MAX,
                    lits: vec![PbLit {
                        var: 1,
                        negated: false,
                    }],
                },
                PbTerm {
                    coeff: 1,
                    lits: vec![PbLit {
                        var: 2,
                        negated: false,
                    }],
                },
            ],
        },
    );

    assert_eq!(engine.solve(), OptResult::Unknown);
    assert_eq!(engine.last_reported_obj, None);
}

#[test]
fn test_select_strategy_prefers_core_guided_for_signed_unit_objectives() {
    let mut input = String::from("* #variable= 64 #constraint= 2\nmin:");
    for i in 1..=64 {
        input.push_str(&format!(" -1 x{i}"));
    }
    input.push_str(" ;\n");
    for i in 1..=64 {
        input.push_str(&format!(" +1 x{i}"));
    }
    input.push_str(" >= 1 ;\n");
    for i in 1..=64 {
        input.push_str(&format!(" -1 x{i}"));
    }
    input.push_str(" >= -1 ;\n");

    let instance = parse_opb(&input).expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);
    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    let objective = instance.objective.as_ref().expect("has objective");
    let engine = OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || false,
    );

    let stats = engine.objective_stats();
    assert_eq!(stats.term_count, 64);
    assert_eq!(stats.single_lit_terms, 64);
    assert_eq!(stats.unit_weight_terms, 64);
    assert_eq!(stats.lower_bound, -64);
    assert_eq!(stats.upper_bound, 0);
    assert_eq!(engine.select_strategy(), OptStrategy::CoreGuided);
}

#[test]
fn test_select_strategy_prefers_core_guided_for_weighted_single_literal_objectives() {
    let mut input = String::from("* #variable= 64 #constraint= 2\nmin:");
    for i in 1..=64 {
        let weight = if i % 2 == 0 { 2 } else { 3 };
        input.push_str(&format!(" +{weight} x{i}"));
    }
    input.push_str(" ;\n");
    for i in 1..=64 {
        input.push_str(&format!(" +1 x{i}"));
    }
    input.push_str(" >= 1 ;\n");
    for i in 1..=64 {
        input.push_str(&format!(" -1 x{i}"));
    }
    input.push_str(" >= -1 ;\n");

    let instance = parse_opb(&input).expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);
    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    let objective = instance.objective.as_ref().expect("has objective");
    let engine = OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || false,
    );

    let stats = engine.objective_stats();
    assert_eq!(stats.term_count, 64);
    assert_eq!(stats.single_lit_terms, 64);
    assert_eq!(stats.unit_weight_terms, 0);
    assert_eq!(engine.select_strategy(), OptStrategy::CoreGuided);
}

#[test]
fn test_select_strategy_uses_normalized_gap_for_complementary_costs() {
    let mut input = String::from("* #variable= 20 #constraint= 0\nmin:");
    for i in 1..=20 {
        input.push_str(&format!(" +1000 x{i} +999 ~x{i}"));
    }
    input.push_str(" ;\n");

    let engine = engine_from_opb(&input);
    let stats = engine.objective_stats();
    assert_eq!(stats.term_count, 40);
    assert_eq!(stats.gap, 39_980);

    let bounds = engine
        .normalized_objective_bounds()
        .expect("complementary single-literal costs should normalize");
    assert_eq!(bounds.lower, 19_980);
    assert_eq!(bounds.upper, 20_000);
    assert_eq!(
        engine.select_strategy(),
        OptStrategy::Linear,
        "strategy selection should use the normalized residual gap"
    );
}

#[test]
fn test_select_strategy_uses_residual_soft_count_after_complementary_cancellation() {
    let mut input = String::from("* #variable= 32 #constraint= 0\nmin:");
    for i in 1..=32 {
        input.push_str(&format!(" +5 x{i} +3 ~x{i}"));
    }
    input.push_str(" ;\n");

    let engine = engine_from_opb(&input);
    let stats = engine.objective_stats();
    assert_eq!(stats.term_count, 64);
    assert_eq!(stats.single_lit_terms, 64);

    let (weighted, offset) = engine
        .normalized_weighted_literals()
        .expect("complementary single-literal costs should normalize");
    assert_eq!(offset, 96);
    assert_eq!(weighted.len(), 32);
    // 32 residual weighted soft literals (down from 64 raw terms) exceed the
    // OLL routing threshold, so core-guided is selected after cancellation.
    assert_eq!(
        engine.select_strategy(),
        OptStrategy::CoreGuided,
        "core-guided strategy selection should use residual soft literals after cancellation"
    );
}

#[test]
fn test_select_strategy_prefers_core_guided_for_mapped_product_objectives() {
    let mut input = String::from("* #variable= 128 #constraint= 1\nmin:");
    for pair in 0..64u32 {
        let left = pair * 2 + 1;
        let right = left + 1;
        input.push_str(&format!(" +1 x{left} x{right}"));
    }
    input.push_str(" ;\n");
    for pair in 0..64u32 {
        let left = pair * 2 + 1;
        let right = left + 1;
        input.push_str(&format!(" +1 x{left} x{right}"));
    }
    input.push_str(" >= 0 ;\n");

    let engine = engine_from_opb(&input);
    let stats = engine.objective_stats();
    assert_eq!(stats.term_count, 64);
    assert_eq!(stats.single_lit_terms, 0);

    let (weighted, offset) = engine
        .normalized_weighted_literals()
        .expect("base-CNF AND evidence should normalize product objective terms");
    assert_eq!(offset, 0);
    assert_eq!(weighted.len(), 64);
    assert_eq!(
        engine.select_strategy(),
        OptStrategy::CoreGuided,
        "mapped product objectives should enter the core-guided optimizer path"
    );
}

#[test]
fn test_normalized_unit_cost_literals_support_negative_terms() {
    let instance =
        parse_opb("* #variable= 2 #constraint= 1\nmin: -1 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n")
            .expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);
    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    let objective = instance.objective.as_ref().expect("has objective");
    let engine = OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || false,
    );

    let (literals, offset) = engine
        .normalized_unit_cost_literals()
        .expect("signed unit objective should normalize");
    assert_eq!(offset, -1);
    assert_eq!(literals.len(), 2);
    assert_eq!(literals[0], Literal::negative(Variable::new(0)));
    assert_eq!(literals[1], Literal::positive(Variable::new(1)));
}

#[test]
fn test_engine_handles_negative_unit_objective() {
    let mut input = String::from("* #variable= 64 #constraint= 2\nmin:");
    for i in 1..=64 {
        input.push_str(&format!(" -1 x{i}"));
    }
    input.push_str(" ;\n");
    for i in 1..=64 {
        input.push_str(&format!(" +1 x{i}"));
    }
    input.push_str(" >= 1 ;\n");
    for i in 1..=64 {
        input.push_str(&format!(" -1 x{i}"));
    }
    input.push_str(" >= -1 ;\n");

    let instance = parse_opb(&input).expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);
    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    let objective = instance.objective.as_ref().expect("has objective");
    let mut engine = OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || false,
    );
    let (active_softs, offset) = engine
        .normalized_weighted_literals()
        .expect("negative unit objective should normalize");
    assert!(
        active_softs.iter().all(|soft| !soft.literal.is_positive()),
        "negative unit terms normalize to negative cost literals"
    );
    let seed = engine
        .extract_native_core_guided_seed(&active_softs, offset)
        .expect("validated native PB assumptions should expose lower-bound progress");
    // The contract is "AT LEAST one soft must be paid", so assert that — not an
    // exact value. `extract_native_core_guided_seed` runs a CDCL probe whose
    // effort is not deterministic (restarts, clause-DB state), so it sometimes
    // proves two or more softs must be paid. That is a STRICTLY BETTER lower
    // bound and equally sound, but `assert_eq!(.., offset + 1)` failed on it —
    // an intermittent ~10-20% failure in full-suite runs that passed 5/5 in
    // isolation, because the shared solver state differs. Pin both real
    // invariants instead: progress, and soundness.
    //
    // The instance forces `sum x >= 1` and `sum x <= 1`, so exactly one variable
    // is true and the true optimum is -1. A lower bound may never exceed it.
    assert!(
        seed.lower_bound > offset,
        "native seed should prove at least one normalized soft must be paid: \
         lower_bound {} < offset {} + 1",
        seed.lower_bound,
        offset
    );
    assert!(
        seed.lower_bound <= -1,
        "SOUNDNESS: seed lower_bound {} exceeds the true optimum -1",
        seed.lower_bound
    );
    assert!(
        seed.learned_clause
            .iter()
            .all(|literal| !literal.is_positive()),
        "negative objective costs should learn a clause over normalized negative literals"
    );

    let result = engine.solve();
    match result {
        OptResult::Optimal(assignment, obj_value) => {
            assert_eq!(obj_value, -1, "exactly-one optimum should be -1");
            assert_eq!(
                assignment.iter().filter(|&&bit| bit).count(),
                1,
                "exactly-one constraints should force a single true variable"
            );
        }
        other => panic!("expected Optimal, got: {other:?}"),
    }
}

#[test]
fn test_normalized_weighted_literals_merge_duplicates_and_negative_terms() {
    let instance =
        parse_opb("* #variable= 2 #constraint= 1\nmin: +2 x1 +3 x1 -1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n")
            .expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);
    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    let objective = instance.objective.as_ref().expect("has objective");
    let engine = OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || false,
    );

    let (weighted, offset) = engine
        .normalized_weighted_literals()
        .expect("single-literal weighted objective should normalize");
    assert_eq!(offset, -1);
    assert_eq!(weighted.len(), 2);
    assert!(weighted
        .iter()
        .any(|soft| { soft.literal == Literal::positive(Variable::new(0)) && soft.weight == 5 }));
    assert!(weighted
        .iter()
        .any(|soft| { soft.literal == Literal::negative(Variable::new(1)) && soft.weight == 1 }));
}

#[test]
fn test_normalized_weighted_literals_cancel_complementary_costs() {
    let instance = parse_opb("* #variable= 2 #constraint= 0\nmin: +5 x1 +3 ~x1 +4 ~x2 +1 x2 ;\n")
        .expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);
    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    let objective = instance.objective.as_ref().expect("has objective");
    let engine = OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || false,
    );

    let (weighted, offset) = engine
        .normalized_weighted_literals()
        .expect("single-literal weighted objective should normalize");
    assert_eq!(offset, 4);
    assert_eq!(weighted.len(), 2);
    assert!(weighted
        .iter()
        .any(|soft| { soft.literal == Literal::positive(Variable::new(0)) && soft.weight == 2 }));
    assert!(weighted
        .iter()
        .any(|soft| { soft.literal == Literal::negative(Variable::new(1)) && soft.weight == 3 }));
}

#[test]
fn test_normalized_weighted_literals_map_existing_and_for_nonlinear_objective() {
    let engine = engine_from_opb(
        "* #variable= 4 #constraint= 1\n\
         min: +5 x1 x2 -2 ~x3 x4 +7 x1 ~x1 ;\n\
         +1 x1 x2 +1 ~x3 x4 >= 0 ;\n",
    );

    let (weighted, offset) = engine
        .normalized_weighted_literals()
        .expect("objective products with existing AND literals should normalize");
    assert_eq!(offset, -2);
    assert_eq!(weighted.len(), 2);
    assert!(weighted
        .iter()
        .any(|soft| { soft.literal == Literal::positive(Variable::new(4)) && soft.weight == 5 }));
    assert!(weighted
        .iter()
        .any(|soft| { soft.literal == Literal::negative(Variable::new(5)) && soft.weight == 2 }));
}

#[test]
fn test_normalized_weighted_literals_fail_closed_without_existing_and_literal() {
    let engine = engine_from_opb("* #variable= 2 #constraint= 0\nmin: +5 x1 x2 ;\n");

    assert!(
        engine.normalized_weighted_literals().is_none(),
        "nonlinear objective products without a base CNF definition should stay unsupported"
    );
}

#[test]
fn test_normalized_weighted_literals_fail_closed_with_only_forward_and_evidence() {
    let engine = engine_from_manual_base(
        2,
        EncodedCnf {
            num_vars: 3,
            clauses: vec![vec![-3, 1], vec![-3, 2]],
        },
        PbObjective {
            terms: vec![PbTerm {
                coeff: 5,
                lits: vec![
                    PbLit {
                        var: 1,
                        negated: false,
                    },
                    PbLit {
                        var: 2,
                        negated: false,
                    },
                ],
            }],
        },
    );

    assert!(
        engine.normalized_weighted_literals().is_none(),
        "one-way z => x1,x2 evidence must not map a product objective"
    );
    assert!(
        engine.extract_weighted_core_guided_state().is_none(),
        "core-guided extraction must fail closed without reverse AND evidence"
    );
}

#[test]
fn test_normalized_weighted_literals_fail_closed_with_only_reverse_and_evidence() {
    let engine = engine_from_manual_base(
        2,
        EncodedCnf {
            num_vars: 3,
            clauses: vec![vec![3, -1, -2]],
        },
        PbObjective {
            terms: vec![PbTerm {
                coeff: 5,
                lits: vec![
                    PbLit {
                        var: 1,
                        negated: false,
                    },
                    PbLit {
                        var: 2,
                        negated: false,
                    },
                ],
            }],
        },
    );

    assert!(
        engine.normalized_weighted_literals().is_none(),
        "one-way x1 & x2 => z evidence must not map a product objective"
    );
    assert!(
        engine.extract_weighted_core_guided_state().is_none(),
        "core-guided extraction must fail closed without forward AND evidence"
    );
}

#[test]
fn test_normalized_weighted_literals_fail_closed_when_mapped_product_weight_overflows() {
    let input = format!(
        "* #variable= 2 #constraint= 1\n\
         min: +{} x1 x2 +1 x1 x2 ;\n\
         +1 x1 x2 >= 0 ;\n",
        i128::MAX
    );
    let engine = engine_from_opb(&input);

    assert!(
        engine.normalized_weighted_literals().is_none(),
        "mapped nonlinear objective weights that overflow i128 should stay unsupported"
    );
    assert!(
        engine.extract_weighted_core_guided_state().is_none(),
        "core-guided extraction must not consume saturated mapped-product weights"
    );
}

#[test]
fn test_normalized_weighted_literals_fail_closed_when_mapped_negative_product_overflows() {
    let input = format!(
        "* #variable= 2 #constraint= 1\n\
         min: -{} x1 x2 -1 x1 x2 ;\n\
         +1 x1 x2 >= 0 ;\n",
        i128::MAX
    );
    let engine = engine_from_opb(&input);

    assert!(
        engine.normalized_weighted_literals().is_none(),
        "mapped nonlinear objective offsets that overflow i128 should stay unsupported"
    );
    assert!(
        engine.extract_weighted_core_guided_state().is_none(),
        "core-guided extraction must not consume saturated mapped-product offsets"
    );
}

#[test]
fn test_extract_core_guided_state_retains_disjoint_core_clauses() {
    let instance = parse_opb(
        "* #variable= 4 #constraint= 2\nmin: +1 x1 +1 x2 +1 x3 +1 x4 ;\n+1 x1 +1 x2 >= 1 ;\n+1 x3 +1 x4 >= 1 ;\n",
    )
    .expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);
    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    let objective = instance.objective.as_ref().expect("has objective");
    let engine = OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || false,
    );

    let extracted = engine.extract_core_guided_state();
    assert_eq!(extracted.status, LowerBoundStatus::Complete(2));
    assert_eq!(extracted.learned_clauses.len(), 2);
    assert!(extracted
        .learned_clauses
        .iter()
        .all(|clause| clause.len() == 2));
}

#[test]
fn test_extract_weighted_core_guided_state_accumulates_disjoint_core_weights() {
    let instance = parse_opb(
        "* #variable= 4 #constraint= 2\nmin: +2 x1 +3 x2 +5 x3 +7 x4 ;\n+1 x1 +1 x2 >= 1 ;\n+1 x3 +1 x4 >= 1 ;\n",
    )
    .expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);
    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    let objective = instance.objective.as_ref().expect("has objective");
    let engine = OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || false,
    );

    let extracted = engine
        .extract_weighted_core_guided_state()
        .expect("weighted single-literal objective should support weighted cores");
    assert_eq!(extracted.status, LowerBoundStatus::Complete(7));
    assert_eq!(extracted.learned_clauses.len(), 2);
    assert!(extracted.learned_clauses.iter().any(|clause| {
        clause.contains(&Literal::positive(Variable::new(0)))
            && clause.contains(&Literal::positive(Variable::new(1)))
    }));
    assert!(extracted.learned_clauses.iter().any(|clause| {
        clause.contains(&Literal::positive(Variable::new(2)))
            && clause.contains(&Literal::positive(Variable::new(3)))
    }));
}

#[test]
fn test_extract_weighted_core_guided_state_uses_existing_and_literals() {
    let engine = engine_from_opb(
        "* #variable= 4 #constraint= 1\n\
         min: +2 x1 x2 +3 x3 x4 ;\n\
         +1 x1 x2 +1 x3 x4 >= 1 ;\n",
    );

    let extracted = engine
        .extract_weighted_core_guided_state()
        .expect("mapped nonlinear objective terms should support weighted cores");
    assert_eq!(extracted.status, LowerBoundStatus::Complete(2));
    assert_eq!(extracted.learned_clauses.len(), 1);
    assert!(extracted.learned_clauses.iter().any(|clause| {
        clause.contains(&Literal::positive(Variable::new(4)))
            && clause.contains(&Literal::positive(Variable::new(5)))
    }));
}

#[test]
fn test_native_core_guided_seed_consumes_accepted_single_literal_evidence() {
    let engine = engine_from_opb(
        "* #variable= 3 #constraint= 1\n\
         min: +9 x1 +4 x2 +6 x3 ;\n\
         +1 x1 +1 x2 +1 x3 >= 1 ;\n",
    );
    let (active_softs, offset) = engine
        .normalized_weighted_literals()
        .expect("single-literal objective should normalize");

    let seed = engine
        .extract_native_core_guided_seed(&active_softs, offset)
        .expect("native PB-CDCL should expose accepted UNSAT core evidence");
    assert_eq!(seed.lower_bound, 4);
    assert_eq!(seed.core_weight, 4);
    assert_eq!(
        seed.learned_clause,
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
            Literal::positive(Variable::new(2)),
        ]
    );

    let extracted = engine
        .extract_weighted_core_guided_state()
        .expect("native-seeded extraction should stay supported");
    assert_eq!(extracted.status, LowerBoundStatus::Complete(4));
    assert_eq!(extracted.learned_clauses.len(), 1);
    assert_eq!(extracted.learned_clauses[0], seed.learned_clause);
}

#[test]
fn test_native_core_guided_seeding_iterates_on_residual_softs() {
    let engine = engine_from_opb(
        "* #variable= 4 #constraint= 2\n\
         min: +2 x1 +2 x2 +5 x3 +5 x4 ;\n\
         +1 x1 +1 x2 >= 1 ;\n\
         +1 x3 +1 x4 >= 1 ;\n",
    );
    let (mut active_softs, mut lower_bound) = engine
        .normalized_weighted_literals()
        .expect("single-literal objective should normalize");
    let mut solver = engine.base_solver.clone_for_incremental();
    let mut learned_clauses = Vec::new();

    let status = engine.extract_native_core_guided_seeds(
        &mut active_softs,
        &mut lower_bound,
        &mut solver,
        &mut learned_clauses,
    );

    assert_eq!(status, Some(LowerBoundStatus::Complete(7)));
    assert_eq!(lower_bound, 7);
    assert!(active_softs.is_empty());
    assert_eq!(learned_clauses.len(), 2);
    assert!(learned_clauses.iter().any(|clause| {
        clause.len() == 2
            && clause.contains(&Literal::positive(Variable::new(0)))
            && clause.contains(&Literal::positive(Variable::new(1)))
    }));
    assert!(learned_clauses.iter().any(|clause| {
        clause.len() == 2
            && clause.contains(&Literal::positive(Variable::new(2)))
            && clause.contains(&Literal::positive(Variable::new(3)))
    }));
}

#[test]
fn test_native_core_guided_seed_fails_closed_when_probe_is_satisfiable() {
    let engine = engine_from_opb("* #variable= 1 #constraint= 0\nmin: +2 x1 ;\n");
    let (active_softs, offset) = engine
        .normalized_weighted_literals()
        .expect("single-literal objective should normalize");

    assert_eq!(
        engine.extract_native_core_guided_seed(&active_softs, offset),
        None,
        "SAT native probes must not expose UNSAT-core lower-bound evidence"
    );

    let extracted = engine
        .extract_weighted_core_guided_state()
        .expect("SAT-assumption fallback should still complete");
    assert_eq!(extracted.status, LowerBoundStatus::Complete(0));
    assert!(extracted.learned_clauses.is_empty());
}

#[test]
fn test_native_core_guided_seed_disabled_for_proof_mode_falls_back() {
    let mut engine = engine_from_opb(
        "* #variable= 2 #constraint= 1\n\
         min: +3 x1 +5 x2 ;\n\
         +1 x1 +1 x2 >= 1 ;\n",
    );
    let (active_softs, offset) = engine
        .normalized_weighted_literals()
        .expect("single-literal objective should normalize");
    engine.disable_native_core_evidence_for_proof_mode();

    assert_eq!(
        engine.extract_native_core_guided_seed(&active_softs, offset),
        None,
        "proof-mode guard must fail closed before native evidence probing"
    );

    let extracted = engine
        .extract_weighted_core_guided_state()
        .expect("disabled native core probing should fall back to SAT assumptions");
    assert_eq!(extracted.status, LowerBoundStatus::Complete(3));
    assert_eq!(extracted.learned_clauses.len(), 1);
    assert!(extracted.learned_clauses[0].contains(&Literal::positive(Variable::new(0))));
    assert!(extracted.learned_clauses[0].contains(&Literal::positive(Variable::new(1))));
}

#[test]
fn test_extract_weighted_core_guided_state_fails_closed_on_lower_bound_overflow() {
    let engine = engine_from_manual_base(
        2,
        EncodedCnf {
            num_vars: 2,
            clauses: vec![vec![1], vec![2]],
        },
        PbObjective {
            terms: vec![
                PbTerm {
                    coeff: i128::MAX,
                    lits: vec![PbLit {
                        var: 1,
                        negated: false,
                    }],
                },
                PbTerm {
                    coeff: i128::MAX,
                    lits: vec![PbLit {
                        var: 2,
                        negated: false,
                    }],
                },
            ],
        },
    );

    assert!(
        engine.normalized_objective_bounds().is_none(),
        "exact normalized upper bound exceeds i128 and must not be saturated"
    );
    assert!(
        engine.extract_weighted_core_guided_state().is_none(),
        "core-guided extraction must fail closed instead of saturating lower-bound evidence"
    );

    let extracted = engine.extract_core_guided_state();
    assert_eq!(extracted.status, LowerBoundStatus::Interrupted(0));
    assert!(
        extracted.learned_clauses.is_empty(),
        "fallback state must not expose partially accumulated overflow-prone clauses"
    );
}

#[test]
fn test_trim_assumption_core_removes_redundant_literals() {
    let instance = parse_opb(
        "* #variable= 4 #constraint= 1\nmin: +1 x1 +1 x2 +1 x3 +1 x4 ;\n+1 x1 +1 x2 +1 x3 >= 2 ;\n",
    )
    .expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);
    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    let objective = instance.objective.as_ref().expect("has objective");
    let engine = OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || false,
    );
    let mut solver = engine.base_solver.clone_for_incremental();
    let trimmed = engine.trim_assumption_core(
        &mut solver,
        vec![
            Literal::negative(Variable::new(0)),
            Literal::negative(Variable::new(1)),
            Literal::negative(Variable::new(3)),
        ],
    );

    assert_eq!(trimmed.len(), 2);
    assert!(trimmed.contains(&Literal::negative(Variable::new(0))));
    assert!(trimmed.contains(&Literal::negative(Variable::new(1))));
    assert!(
        !trimmed.contains(&Literal::negative(Variable::new(3))),
        "the unconstrained x4 assumption should be removed"
    );
}

#[test]
fn test_binary_search_weighted_cores_can_close_disjoint_pair_family() {
    let mut input = String::from("* #variable= 32 #constraint= 16\nmin:");
    for pair in 0..16u32 {
        let left = pair * 2 + 1;
        let right = left + 1;
        input.push_str(&format!(" +2 x{left} +3 x{right}"));
    }
    input.push_str(" ;\n");
    for pair in 0..16u32 {
        let left = pair * 2 + 1;
        let right = left + 1;
        input.push_str(&format!(" +1 x{left} +1 x{right} >= 1 ;\n"));
    }

    let instance = parse_opb(&input).expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);
    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    let objective = instance.objective.as_ref().expect("has objective");
    let mut engine = OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || false,
    );

    let extracted = engine
        .extract_weighted_core_guided_state()
        .expect("weighted single-literal objective should support weighted cores");
    assert_eq!(extracted.status, LowerBoundStatus::Complete(32));

    let result = binary_search::solve(&mut engine);
    match result {
        OptResult::Optimal(_, obj_value) => assert_eq!(obj_value, 32),
        other => panic!("expected weighted binary-search optimum, got: {other:?}"),
    }
}

#[test]
fn test_upper_bound_query_session_handles_nonmonotone_bounds() {
    let instance = parse_opb("* #variable= 4 #constraint= 0\nmin: -1 x1 -1 x2 -1 x3 -1 x4 ;\n")
        .expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);
    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    let objective = instance.objective.as_ref().expect("has objective");
    let engine = OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || false,
    );
    let mut session = engine.upper_bound_query_session(&[]);

    match session.solve(&engine, -4) {
        QueryOutcome::Sat { obj_value, .. } => {
            assert!(
                obj_value <= -4,
                "expected a model meeting the tighter bound"
            );
        }
        other => panic!("expected SAT at bound -4, got: {other:?}"),
    }

    assert!(
        matches!(session.solve(&engine, -5), QueryOutcome::Unsat),
        "bound below the optimum should be UNSAT"
    );

    match session.solve(&engine, -1) {
        QueryOutcome::Sat { obj_value, .. } => {
            assert!(
                obj_value <= -1,
                "later looser queries must stay satisfiable after a tighter UNSAT probe"
            );
        }
        other => panic!("expected SAT at bound -1 after prior probes, got: {other:?}"),
    }
}

#[test]
fn test_upper_bound_query_session_skips_vacuous_bound_cnf_growth() {
    let instance = parse_opb(
        "* #variable= 8 #constraint= 0\nmin: +1 x1 +1 x2 +1 x3 +1 x4 +1 x5 +1 x6 +1 x7 +1 x8 ;\n",
    )
    .expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);
    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    let objective = instance.objective.as_ref().expect("has objective");
    let engine = OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || false,
    );
    let mut session = engine.upper_bound_query_session(&[]);
    assert!(
        !session.uses_persistent_bounds(),
        "small objectives should stay on per-probe bound encodings"
    );

    match session.solve(&engine, 3) {
        QueryOutcome::Sat { obj_value, .. } => assert!(obj_value <= 3),
        other => panic!("expected SAT for tightening probe, got: {other:?}"),
    }
    let growth_after_tight_probe = session.bound_clause_growth_since_construction();
    assert!(
        growth_after_tight_probe > 0,
        "tightening probes should add guarded bound CNF on the fallback path"
    );

    match session.solve(&engine, 8) {
        QueryOutcome::Sat { obj_value, .. } => assert!(obj_value <= 8),
        other => panic!("expected SAT for vacuous upper bound, got: {other:?}"),
    }
    assert_eq!(
        session.bound_clause_growth_since_construction(),
        growth_after_tight_probe,
        "vacuous upper-bound probes should not append per-probe CNF"
    );
}

#[test]
fn test_dense_weight_probe_growth_stays_adder_sized_once_session_gap_pool_is_spent() {
    // Dense-weight objective: 40 varied medium coefficients (2003..7814,
    // total ~196k). The persistent weighted totalizer declines (total weight
    // >> 4096), so every probe takes the per-probe bound-CNF path, and every
    // bound row is a gap row (coeffs <= 10_000, normalized rhs > 10_000) —
    // the exact shape where a fresh per-probe BDD pool used to append a
    // BDD-sized bound CNF PER PROBE into the persistent session solver
    // (measured here: ~32k BDD clauses vs ~4.6k adder clauses per probe).
    let mut input = String::from("* #variable= 40 #constraint= 0\nmin:");
    for i in 0..40u32 {
        input.push_str(&format!(" +{} x{}", 2003 + 149 * i, i + 1));
    }
    input.push_str(" ;\n");
    let engine = engine_from_opb(&input);
    let total: i128 = (0..40).map(|i| 2003 + 149 * i as i128).sum();

    let mut session = engine.upper_bound_query_session(&[]);
    assert!(
        !session.uses_persistent_bounds(),
        "dense weights must decline the persistent bound encoding"
    );

    // Small session pool (two BDD poll intervals): the first probe's BDD
    // attempt spends it, and — because the pool is SESSION-level, never
    // reset per probe — every later probe must keep the compact adder
    // routing instead of re-attempting (and re-appending) a fresh BDD.
    session.set_bound_bdd_gap_pool(2 * 4096);

    // Adder yardstick: the forced-adder encoding of a representative probe's
    // bound row. Per-probe growth must stay within a small multiple of it.
    let yardstick = {
        let constraint = objective_at_most_constraint(&engine.objective, total - 60_003)
            .expect("bound row encodes");
        let mut enc = CnfEncoder::with_strategy(40, crate::encoding::EncodingStrategy::Adder);
        enc.encode_constraint(&constraint);
        enc.clauses().len()
    };
    assert!(yardstick > 0);

    let mut prev_growth = 0usize;
    for k in 0..5i128 {
        // Tightening probes whose normalized bound rows all have
        // rhs > 10_000 (the gap-row threshold).
        let bound = total - 60_001 - k;
        match session.solve(&engine, bound) {
            QueryOutcome::Sat { obj_value, .. } => assert!(obj_value <= bound),
            other => panic!("expected SAT at bound {bound}, got: {other:?}"),
        }
        let growth = session.bound_clause_growth_since_construction();
        let delta = growth - prev_growth;
        prev_growth = growth;
        assert!(delta > 0, "tightening probe {k} must append bound CNF");
        assert!(
            delta <= 4 * yardstick,
            "probe {k} appended {delta} clauses, more than a small multiple of the \
             adder size {yardstick}: the session gap pool must not reset per probe"
        );
    }
    assert_eq!(
        session.bound_bdd_gap_pool(),
        0,
        "the probes' BDD attempts must spend the session-level pool"
    );
}

#[test]
fn test_session_gap_pool_persists_across_probes() {
    // Small gap objective (6 medium terms, total 36_001): each probe's
    // bound row is a tiny gap row whose budgeted BDD succeeds and is charged
    // at least one poll interval (4096 fresh states) to the SESSION pool.
    // With a pool of two poll intervals, probes 1-2 take the BDD and probes
    // 3+ must decline to the adder: the pool never resets between probes, so
    // the total BDD volume of the whole session is bounded by ONE pool.
    let mut input = String::from("* #variable= 6 #constraint= 0\nmin:");
    for v in 1..=5u32 {
        input.push_str(&format!(" +6000 x{v}"));
    }
    input.push_str(" +6001 x6 ;\n");
    let engine = engine_from_opb(&input);

    let mut session = engine.upper_bound_query_session(&[]);
    assert!(!session.uses_persistent_bounds());
    session.set_bound_bdd_gap_pool(2 * 4096);

    // Normalized bound rows have rhs = 36_001 - bound > 10_000: gap rows.
    let bounds = [26_000i128, 25_999, 25_998, 25_997];
    let mut pools = Vec::new();
    for &bound in &bounds {
        match session.solve(&engine, bound) {
            QueryOutcome::Sat { obj_value, .. } => assert!(obj_value <= bound),
            other => panic!("expected SAT at bound {bound}, got: {other:?}"),
        }
        pools.push(session.bound_bdd_gap_pool());
    }
    assert!(
        pools[0] > 0 && pools[0] < 2 * 4096,
        "probe 1's BDD must be charged to the session pool, got {}",
        pools[0]
    );
    assert_eq!(pools[1], 0, "probe 2 must finish draining the session pool");
    assert_eq!(pools[2], 0, "a spent session pool must stay spent");
    assert_eq!(pools[3], 0, "the pool must never reset between probes");
}

#[test]
fn test_upper_bound_query_session_vacuous_bound_skips_unsupported_coefficients() {
    let engine = engine_from_manual_base(
        1,
        EncodedCnf {
            num_vars: 1,
            clauses: Vec::new(),
        },
        PbObjective {
            terms: vec![PbTerm {
                coeff: i128::MIN,
                lits: vec![PbLit {
                    var: 1,
                    negated: false,
                }],
            }],
        },
    );
    let mut session = engine.upper_bound_query_session(&[]);

    match session.solve(&engine, 0) {
        QueryOutcome::Sat { obj_value, .. } => assert!(obj_value <= 0),
        other => {
            panic!("expected SAT for vacuous bound despite unnegatable coefficient, got: {other:?}")
        }
    }
    assert_eq!(
        session.bound_clause_growth_since_construction(),
        0,
        "vacuous upper-bound probes should not build unsupported bound CNF"
    );
}

#[test]
fn test_upper_bound_query_session_prunes_below_structural_lower_bound_before_cnf_build() {
    let engine = engine_from_manual_base(
        1,
        EncodedCnf {
            num_vars: 1,
            clauses: Vec::new(),
        },
        PbObjective {
            terms: vec![PbTerm {
                coeff: i128::MIN + 1,
                lits: vec![PbLit {
                    var: 1,
                    negated: false,
                }],
            }],
        },
    );
    let mut session = engine.upper_bound_query_session(&[]);

    assert!(
        matches!(session.solve(&engine, i128::MIN), QueryOutcome::Unsat),
        "bounds below the structural objective minimum should be UNSAT"
    );
    assert_eq!(
        session.bound_clause_growth_since_construction(),
        0,
        "structurally impossible probes should not build unsupported bound CNF"
    );
}

#[test]
fn test_upper_bound_query_session_uses_normalized_constant_bounds_before_cnf_build() {
    let engine = engine_from_manual_base(
        1,
        EncodedCnf {
            num_vars: 1,
            clauses: Vec::new(),
        },
        PbObjective {
            terms: vec![PbTerm {
                coeff: i128::MIN,
                lits: Vec::new(),
            }],
        },
    );
    let mut session = engine.upper_bound_query_session(&[]);
    assert!(
        !session.uses_persistent_bounds(),
        "constant-only objectives should stay on the lightweight fallback path"
    );

    match session.solve(&engine, i128::MIN) {
        QueryOutcome::Sat { obj_value, .. } => assert_eq!(obj_value, i128::MIN),
        other => panic!("expected SAT for the exact constant bound, got: {other:?}"),
    }
    assert_eq!(
        session.bound_clause_growth_since_construction(),
        0,
        "exact normalized bounds should avoid unsupported per-probe CNF construction"
    );
}

#[test]
fn test_upper_bound_query_session_uses_persistent_bounds_for_large_single_literal_objective() {
    let mut input = String::from("* #variable= 64 #constraint= 0\nmin:");
    for var in 1..=64u32 {
        input.push_str(&format!(" -1 x{var}"));
    }
    input.push_str(" ;\n");

    let instance = parse_opb(&input).expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);
    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    let objective = instance.objective.as_ref().expect("has objective");
    let engine = OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || false,
    );
    let mut session = engine.upper_bound_query_session(&[]);
    assert!(
        session.uses_persistent_bounds(),
        "large normalized single-literal objectives should reuse one persistent bound encoding"
    );
    assert_eq!(
        session.persistent_bound_kind(),
        Some(PersistentBoundKind::UnitCardinality),
        "unit objectives should use the reusable cardinality path"
    );

    match session.solve(&engine, -64) {
        QueryOutcome::Sat { obj_value, .. } => assert_eq!(obj_value, -64),
        other => panic!("expected SAT at the optimum bound, got: {other:?}"),
    }
    assert!(
        matches!(session.solve(&engine, -65), QueryOutcome::Unsat),
        "bound below the optimum should be UNSAT"
    );
    match session.solve(&engine, -1) {
        QueryOutcome::Sat { obj_value, .. } => assert!(obj_value <= -1),
        other => panic!("expected SAT after a tighter UNSAT probe, got: {other:?}"),
    }
}

#[test]
fn test_upper_bound_query_session_reuses_unit_cardinality_without_clause_growth() {
    let mut input = String::from("* #variable= 160 #constraint= 0\nmin:");
    for var in 1..=160u32 {
        input.push_str(&format!(" -1 x{var}"));
    }
    input.push_str(" ;\n");

    let instance = parse_opb(&input).expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);
    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    let objective = instance.objective.as_ref().expect("has objective");
    let engine = OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || false,
    );
    let mut session = engine.upper_bound_query_session(&[]);
    assert!(
        session.uses_persistent_bounds(),
        "plain large unit objectives should install one persistent cardinality encoding"
    );
    assert_eq!(
        session.persistent_bound_kind(),
        Some(PersistentBoundKind::UnitCardinality),
        "all-unit objectives above the old cutoff should use the cardinality fast path"
    );
    match session.solve(&engine, -160) {
        QueryOutcome::Sat { obj_value, .. } => assert_eq!(obj_value, -160),
        other => panic!("expected SAT at the optimum bound, got: {other:?}"),
    }
    assert_eq!(
        session.bound_clause_growth_since_construction(),
        0,
        "persistent cardinality probes should not append CNF after session setup"
    );

    match session.solve(&engine, -1) {
        QueryOutcome::Sat { obj_value, .. } => assert!(obj_value <= -1),
        other => panic!("expected SAT at a looser bound, got: {other:?}"),
    }
    assert_eq!(
        session.bound_clause_growth_since_construction(),
        0,
        "looser reusable bound probes should not grow the clause database"
    );

    assert!(
        matches!(session.solve(&engine, -161), QueryOutcome::Unsat),
        "bound below the optimum should be UNSAT"
    );
    assert_eq!(
        session.bound_clause_growth_since_construction(),
        0,
        "direct UNSAT reusable bound probes should not grow the clause database"
    );

    match session.solve(&engine, -32) {
        QueryOutcome::Sat { obj_value, .. } => assert!(obj_value <= -32),
        other => panic!("expected SAT after a prior UNSAT probe, got: {other:?}"),
    }
    assert_eq!(
        session.bound_clause_growth_since_construction(),
        0,
        "non-monotone reusable cardinality probes should stay clause-stable"
    );
}

#[test]
fn test_upper_bound_query_session_reuses_existing_and_objective_literals() {
    let mut input = String::from("* #variable= 64 #constraint= 1\nmin:");
    for pair in 0..32u32 {
        let left = pair * 2 + 1;
        let right = left + 1;
        input.push_str(&format!(" +1 x{left} x{right}"));
    }
    input.push_str(" ;\n");
    for pair in 0..32u32 {
        let left = pair * 2 + 1;
        let right = left + 1;
        input.push_str(&format!(" +1 x{left} x{right}"));
    }
    input.push_str(" >= 0 ;\n");

    let engine = engine_from_opb(&input);
    let mut session = engine.upper_bound_query_session(&[]);
    assert!(
        session.uses_persistent_bounds(),
        "large nonlinear objectives with mapped AND literals should reuse one bound encoding"
    );
    assert_eq!(
        session.persistent_bound_kind(),
        Some(PersistentBoundKind::UnitCardinality)
    );

    match session.solve(&engine, 0) {
        QueryOutcome::Sat { obj_value, .. } => assert_eq!(obj_value, 0),
        other => panic!("expected SAT at the nonlinear optimum bound, got: {other:?}"),
    }
    assert!(
        matches!(session.solve(&engine, -1), QueryOutcome::Unsat),
        "bound below the nonlinear optimum should be UNSAT"
    );
    assert_eq!(
        session.bound_clause_growth_since_construction(),
        0,
        "mapped-product persistent bound probes should not append per-probe CNF"
    );
}

#[test]
fn test_upper_bound_query_session_reuses_weighted_existing_and_with_base_auxiliaries() {
    let mut input = String::from("* #variable= 64 #constraint= 1\nmin:");
    for pair in 0..32u32 {
        let left = pair * 2 + 1;
        let right = left + 1;
        let weight = if pair % 2 == 0 { 2 } else { 3 };
        input.push_str(&format!(" +{weight} x{left} x{right}"));
    }
    input.push_str(" ;\n");
    for pair in 0..32u32 {
        let left = pair * 2 + 1;
        let right = left + 1;
        input.push_str(&format!(" +1 x{left} x{right}"));
    }
    input.push_str(" >= 0 ;\n");

    let engine = engine_from_opb(&input);
    assert!(
        engine.base_cnf.num_vars > engine.num_pb_vars,
        "nonlinear base constraints should leave fixed AND auxiliaries in the base CNF"
    );

    let mut session = engine.upper_bound_query_session(&[]);
    assert!(
        session.uses_persistent_bounds(),
        "weighted nonlinear objectives with mapped AND literals should reuse one bound encoding"
    );
    assert_eq!(
        session.persistent_bound_kind(),
        Some(PersistentBoundKind::WeightedTotalizer)
    );

    match session.solve(&engine, 0) {
        QueryOutcome::Sat { obj_value, .. } => assert_eq!(obj_value, 0),
        other => panic!("expected SAT at the weighted nonlinear optimum, got: {other:?}"),
    }
    assert!(
        matches!(session.solve(&engine, -1), QueryOutcome::Unsat),
        "bound below the weighted nonlinear optimum should be UNSAT"
    );
    match session.solve(&engine, 5) {
        QueryOutcome::Sat { obj_value, .. } => assert!(obj_value <= 5),
        other => panic!("expected SAT for a looser weighted nonlinear bound, got: {other:?}"),
    }
    assert_eq!(
        session.bound_clause_growth_since_construction(),
        0,
        "weighted mapped-product persistent probes should not append per-probe CNF"
    );
}

#[test]
fn test_upper_bound_query_session_reuses_negative_existing_and_objective_offsets() {
    let mut input = String::from("* #variable= 64 #constraint= 1\nmin:");
    for pair in 0..32u32 {
        let left = pair * 2 + 1;
        let right = left + 1;
        input.push_str(&format!(" -1 x{left} x{right}"));
    }
    input.push_str(" ;\n");
    for pair in 0..32u32 {
        let left = pair * 2 + 1;
        let right = left + 1;
        input.push_str(&format!(" +1 x{left} x{right}"));
    }
    input.push_str(" >= 0 ;\n");

    let mut engine = engine_from_opb(&input);
    let (weighted, offset) = engine
        .normalized_weighted_literals()
        .expect("negative mapped nonlinear objective terms should normalize");
    assert_eq!(offset, -32);
    assert_eq!(weighted.len(), 32);
    assert!(weighted
        .iter()
        .all(|soft| !soft.literal.is_positive() && soft.weight == 1));

    let mut session = engine.upper_bound_query_session(&[]);
    assert!(
        session.uses_persistent_bounds(),
        "negative mapped-product objectives should reuse one offset-aware bound encoding"
    );
    assert_eq!(
        session.persistent_bound_kind(),
        Some(PersistentBoundKind::UnitCardinality)
    );

    match session.solve(&engine, -32) {
        QueryOutcome::Sat { obj_value, .. } => assert_eq!(obj_value, -32),
        other => panic!("expected SAT at the negative nonlinear optimum, got: {other:?}"),
    }
    assert!(
        matches!(session.solve(&engine, -33), QueryOutcome::Unsat),
        "bound below the negative nonlinear optimum should be UNSAT"
    );
    match session.solve(&engine, 0) {
        QueryOutcome::Sat { obj_value, .. } => assert!(obj_value <= 0),
        other => {
            panic!("expected SAT for a looser negative nonlinear bound, got: {other:?}")
        }
    }
    assert_eq!(
        session.bound_clause_growth_since_construction(),
        0,
        "negative mapped-product persistent probes should not append per-probe CNF"
    );

    match engine.solve() {
        OptResult::Optimal(_, obj_value) => assert_eq!(obj_value, -32),
        other => panic!("expected optimal negative mapped-product result, got: {other:?}"),
    }
}

#[test]
fn test_upper_bound_query_session_skips_large_unit_cardinality_past_work_limit() {
    let mut input = String::from("* #variable= 193 #constraint= 0\nmin:");
    for var in 1..=193u32 {
        input.push_str(&format!(" -1 x{var}"));
    }
    input.push_str(" ;\n");

    let instance = parse_opb(&input).expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);
    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    let objective = instance.objective.as_ref().expect("has objective");
    let engine = OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || false,
    );
    let session = engine.upper_bound_query_session(&[]);
    assert!(
        !session.uses_persistent_bounds(),
        "plain unit objectives past the cardinality work limit should stay on per-probe encodings"
    );
}

#[test]
fn test_upper_bound_query_session_skips_persistent_bounds_with_learned_core_clauses() {
    let mut input = String::from("* #variable= 64 #constraint= 0\nmin:");
    for var in 1..=64u32 {
        input.push_str(&format!(" -1 x{var}"));
    }
    input.push_str(" ;\n");

    let instance = parse_opb(&input).expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);
    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    let objective = instance.objective.as_ref().expect("has objective");
    let engine = OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || false,
    );
    let learned_clauses = vec![vec![Literal::positive(Variable::new(0))]];
    let session = engine.upper_bound_query_session(&learned_clauses);
    assert!(
        !session.uses_persistent_bounds(),
        "core-guided refinement sessions should use per-probe bound encodings"
    );
}

#[test]
fn test_upper_bound_query_session_persistent_bounds_handle_objective_offsets() {
    let mut input = String::from("* #variable= 32 #constraint= 0\nmin:");
    for var in 1..=16u32 {
        input.push_str(&format!(" -1 x{var}"));
    }
    for var in 17..=32u32 {
        input.push_str(&format!(" +2 x{var}"));
    }
    input.push_str(" ;\n");

    let instance = parse_opb(&input).expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);
    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    let objective = instance.objective.as_ref().expect("has objective");
    let engine = OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || false,
    );
    let mut session = engine.upper_bound_query_session(&[]);
    assert!(
        session.uses_persistent_bounds(),
        "mixed-sign single-literal objectives should still normalize to persistent bounds"
    );

    match session.solve(&engine, -16) {
        QueryOutcome::Sat { obj_value, .. } => assert_eq!(obj_value, -16),
        other => panic!("expected SAT at the normalized optimum, got: {other:?}"),
    }
    assert!(
        matches!(session.solve(&engine, -17), QueryOutcome::Unsat),
        "offset-aware bound below the optimum should be UNSAT"
    );
    match session.solve(&engine, 0) {
        QueryOutcome::Sat { obj_value, .. } => assert!(obj_value <= 0),
        other => panic!("expected SAT for a looser offset-aware bound, got: {other:?}"),
    }
}

#[test]
fn test_complementary_cost_objective_solves_with_canonicalized_bounds() {
    let mut input = String::from("* #variable= 32 #constraint= 0\nmin:");
    for var in 1..=32u32 {
        input.push_str(&format!(" +5 x{var} +3 ~x{var}"));
    }
    input.push_str(" ;\n");

    let instance = parse_opb(&input).expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);
    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    let objective = instance.objective.as_ref().expect("has objective");
    let mut engine = OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || false,
    );

    let (weighted, offset) = engine
        .normalized_weighted_literals()
        .expect("complementary single-literal objective should normalize");
    assert_eq!(offset, 96);
    assert_eq!(weighted.len(), 32);
    assert!(weighted
        .iter()
        .all(|soft| soft.literal.is_positive() && soft.weight == 2));

    let mut session = engine.upper_bound_query_session(&[]);
    assert!(
        session.uses_persistent_bounds(),
        "canonicalized residual objective should still use persistent bounds"
    );
    assert_eq!(
        session.persistent_bound_kind(),
        Some(PersistentBoundKind::WeightedTotalizer)
    );
    assert!(
        matches!(session.solve(&engine, 95), QueryOutcome::Unsat),
        "bound below the constant-offset optimum should be UNSAT"
    );
    match session.solve(&engine, 96) {
        QueryOutcome::Sat { obj_value, .. } => assert_eq!(obj_value, 96),
        other => panic!("expected SAT at the constant-offset optimum, got: {other:?}"),
    }

    match engine.solve() {
        OptResult::Optimal(_, obj_value) => assert_eq!(obj_value, 96),
        other => panic!("expected optimal complementary-cost result, got: {other:?}"),
    }
}

#[test]
fn test_upper_bound_query_returns_unknown_when_bound_build_is_interrupted() {
    let mut input = String::from("* #variable= 256 #constraint= 0\nmin:");
    for var in 1..=256u32 {
        input.push_str(&format!(" +1 x{var}"));
    }
    input.push_str(" ;\n");

    let instance = parse_opb(&input).expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);
    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }

    let objective = instance.objective.as_ref().expect("has objective");
    let stop_checks = Cell::new(0usize);
    let engine = OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || {
            let next = stop_checks.get() + 1;
            stop_checks.set(next);
            next >= 2
        },
    );

    assert!(
        matches!(engine.solve_upper_bound_query(128), QueryOutcome::Unknown),
        "interruptible bound encoding should surface as Unknown"
    );
}

// ---- OLL (core-guided RC2-style) tests ----

fn engine_with_constraints_from_opb(input: &str) -> OptimizationEngine<'static> {
    let instance = parse_opb(input).expect("parse should succeed");
    let encoded = CnfEncoder::encode_instance(&instance);
    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }
    let objective = instance.objective.as_ref().expect("has objective");
    let mut engine = OptimizationEngine::new(
        base_solver,
        objective.clone(),
        encoded,
        instance.num_vars,
        || false,
    );
    engine.set_original_constraints(instance.constraints.clone());
    engine
}

/// Runs the OLL core-guided loop after the initial base solve, exactly as
/// `core_guided::solve` does, and returns its result. Used to exercise the
/// OLL path directly regardless of `select_strategy`.
fn run_oll(engine: &mut OptimizationEngine<'_>) -> OptResult {
    let (best_assignment, best_value) = match engine.solve_base_query() {
        QueryOutcome::Sat {
            assignment,
            obj_value,
        } => (assignment, obj_value),
        QueryOutcome::Unsat => return OptResult::Infeasible,
        QueryOutcome::Unknown | QueryOutcome::Unsupported => return OptResult::Unknown,
    };
    let stats = engine.objective_stats();
    let structural_lower_bound = engine
        .objective_lower_bound_from_stats(stats)
        .min(best_value);
    engine
        .solve_oll(best_assignment, best_value, structural_lower_bound)
        .expect("OLL should apply to weighted-soft objectives")
}

fn optimum_value(result: &OptResult) -> Option<i128> {
    match result {
        OptResult::Optimal(_, value) => Some(*value),
        _ => None,
    }
}

#[test]
fn test_oll_solves_unit_vertex_cover_to_known_optimum() {
    // Vertex cover on a 6-cycle plus chord 1-4. Minimum cover has size 3.
    let input = "* #variable= 6 #constraint= 7\n\
        min: +1 x1 +1 x2 +1 x3 +1 x4 +1 x5 +1 x6 ;\n\
        +1 x1 +1 x2 >= 1 ;\n\
        +1 x2 +1 x3 >= 1 ;\n\
        +1 x3 +1 x4 >= 1 ;\n\
        +1 x4 +1 x5 >= 1 ;\n\
        +1 x5 +1 x6 >= 1 ;\n\
        +1 x6 +1 x1 >= 1 ;\n\
        +1 x1 +1 x4 >= 1 ;\n";
    let mut engine = engine_with_constraints_from_opb(input);
    let result = run_oll(&mut engine);
    assert_eq!(
        optimum_value(&result),
        Some(3),
        "OLL must prove the vertex-cover optimum (3); got {result:?}"
    );
}

#[test]
fn test_oll_solves_weighted_objective_to_known_optimum() {
    // min: +1 x1 +2 x2 +3 x3 +4 x4 subject to coverage; optimum is x1+x2 = 3.
    let input = "* #variable= 4 #constraint= 3\n\
        min: +1 x1 +2 x2 +3 x3 +4 x4 ;\n\
        +1 x1 +1 x2 +1 x3 +1 x4 >= 2 ;\n\
        +1 x1 +1 x3 >= 1 ;\n\
        +1 x2 +1 x4 >= 1 ;\n";
    let mut engine = engine_with_constraints_from_opb(input);
    let result = run_oll(&mut engine);
    assert_eq!(optimum_value(&result), Some(3), "got {result:?}");
}

#[test]
fn test_oll_solves_weighted_opt_fixture_to_known_optimum() {
    // min: +2 x1 +3 x2 +5 x3 +7 x4 with exactly-two coverage; optimum 5.
    let input = "* #variable= 4 #constraint= 2\n\
        min: +2 x1 +3 x2 +5 x3 +7 x4 ;\n\
        +1 x1 +1 x2 +1 x3 +1 x4 >= 2 ;\n\
        +1 ~x1 +1 ~x2 +1 ~x3 +1 ~x4 >= 2 ;\n";
    let mut engine = engine_with_constraints_from_opb(input);
    let result = run_oll(&mut engine);
    assert_eq!(optimum_value(&result), Some(5), "got {result:?}");
}

#[test]
fn test_oll_disjoint_weighted_cores_accumulate_lower_bound() {
    // Two independent at-least-one pairs with distinct weights. Each pair
    // forces one paid literal: min cost = min(3,4) + min(5,6) = 3 + 5 = 8.
    let input = "* #variable= 4 #constraint= 2\n\
        min: +3 x1 +4 x2 +5 x3 +6 x4 ;\n\
        +1 x1 +1 x2 >= 1 ;\n\
        +1 x3 +1 x4 >= 1 ;\n";
    let mut engine = engine_with_constraints_from_opb(input);
    let result = run_oll(&mut engine);
    assert_eq!(optimum_value(&result), Some(8), "got {result:?}");
}

#[test]
fn test_oll_at_least_two_in_single_core_uses_totalizer_relaxation() {
    // A single core that must pay for TWO selectors exercises the totalizer
    // output o_2 path: at least 2 of {x1,x2,x3} true, all unit cost -> 2.
    let input = "* #variable= 3 #constraint= 1\n\
        min: +1 x1 +1 x2 +1 x3 ;\n\
        +1 x1 +1 x2 +1 x3 >= 2 ;\n";
    let mut engine = engine_with_constraints_from_opb(input);
    let result = run_oll(&mut engine);
    assert_eq!(optimum_value(&result), Some(2), "got {result:?}");
}

#[test]
fn test_oll_weighted_at_least_two_uses_totalizer_relaxation() {
    // Weighted variant: pick the two cheapest of {2,3,4} -> 5, via totalizer
    // o_2 / o_3 relaxation thresholds.
    let input = "* #variable= 3 #constraint= 1\n\
        min: +2 x1 +3 x2 +4 x3 ;\n\
        +1 x1 +1 x2 +1 x3 >= 2 ;\n";
    let mut engine = engine_with_constraints_from_opb(input);
    let result = run_oll(&mut engine);
    assert_eq!(optimum_value(&result), Some(5), "got {result:?}");
}

#[test]
fn test_oll_infeasible_subproblem_after_paying_all_is_handled() {
    // Hard contradiction independent of softs: x1 and ~x1 both required.
    // Base solve is UNSAT, so OLL is never entered; the engine reports
    // infeasible via the linear/core driver.
    let input = "* #variable= 2 #constraint= 2\n\
        min: +1 x1 +1 x2 ;\n\
        +1 x2 >= 1 ;\n\
        +1 ~x2 >= 1 ;\n";
    let mut engine = engine_with_constraints_from_opb(input);
    assert_eq!(run_oll(&mut engine), OptResult::Infeasible);
}

// A tiny deterministic LCG so the differential test is reproducible without a
// dependency on an external RNG crate.
struct Lcg(u64);
impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }
    fn below(&mut self, bound: u64) -> u64 {
        self.next_u64() % bound.max(1)
    }
}

fn random_weighted_covering_opb(rng: &mut Lcg) -> String {
    let num_vars = 3 + rng.below(4) as u32; // 3..=6 variables
    let num_constraints = 1 + rng.below(4); // 1..=4 constraints
    let mut input = format!("* #variable= {num_vars} #constraint= {num_constraints}\nmin:");
    for v in 1..=num_vars {
        let weight = 1 + rng.below(5); // 1..=5
        input.push_str(&format!(" +{weight} x{v}"));
    }
    input.push_str(" ;\n");
    for _ in 0..num_constraints {
        // A coverage clause "at least 1 of a random non-empty subset".
        let mut terms = String::new();
        let mut count = 0;
        for v in 1..=num_vars {
            if rng.below(2) == 1 {
                terms.push_str(&format!(" +1 x{v}"));
                count += 1;
            }
        }
        if count == 0 {
            terms.push_str(" +1 x1");
        }
        input.push_str(&terms);
        input.push_str(" >= 1 ;\n");
    }
    input
}

#[test]
fn test_oll_agrees_with_linear_on_random_small_instances() {
    // Differential test: OLL must agree on the optimum value with the
    // independently implemented linear-search path on many random instances.
    let mut rng = Lcg(0x9E3779B97F4A7C15);
    let mut checked = 0usize;
    for _ in 0..400 {
        let input = random_weighted_covering_opb(&mut rng);

        let mut oll_engine = engine_with_constraints_from_opb(&input);
        let oll_result = run_oll(&mut oll_engine);

        let mut linear_engine = engine_with_constraints_from_opb(&input);
        let linear_result = linear::solve(&mut linear_engine);

        match (&oll_result, &linear_result) {
            (OptResult::Optimal(_, a), OptResult::Optimal(_, b)) => {
                assert_eq!(
                    a, b,
                    "OLL and linear disagree on optimum for instance:\n{input}\n\
                     OLL={oll_result:?} LINEAR={linear_result:?}"
                );
                checked += 1;
            }
            (OptResult::Infeasible, OptResult::Infeasible) => {
                checked += 1;
            }
            other => {
                panic!("OLL/linear result-kind mismatch for instance:\n{input}\n{other:?}")
            }
        }
    }
    assert!(checked >= 400, "expected all random instances classified");
}

/// Env-gated harness: runs the OLL path on a real instance file and asserts
/// the optimum (when proven) matches `--oll-expect`. Skipped unless
/// `--oll-file` is set. Used to verify OLL on real OPT-LIN/PARTIAL/SOFT
/// instances against Exact-derived reference values.
#[test]
fn test_oll_matches_reference_on_real_instance_when_requested() {
    let Some(path) = ay_core::misc_cli_flags().oll_file.clone() else {
        return;
    };
    let text = std::fs::read_to_string(&path).expect("read instance file");
    let instance = if std::path::Path::new(&path)
        .extension()
        .is_some_and(|extension| extension.eq_ignore_ascii_case("wbo"))
    {
        let wbo = crate::parse_wbo(&text).expect("parse wbo");
        wbo::wbo_to_pbo(&wbo)
    } else {
        parse_opb(&text).expect("parse opb")
    };
    let objective = instance.objective.clone().expect("has objective");
    let encoded = CnfEncoder::encode_instance(&instance);
    let mut base_solver = SatSolver::new(encoded.num_vars as usize);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        base_solver.add_clause(lits);
    }
    let mut engine =
        OptimizationEngine::new(base_solver, objective, encoded, instance.num_vars, || false);
    engine.set_original_constraints(instance.constraints.clone());

    let result = core_guided::solve(&mut engine);
    eprintln!("OLL result for {path}: {result:?}");
    if let Some(expected) = ay_core::misc_cli_flags().oll_expect.clone() {
        let expected: i128 = expected.parse().expect("parse expected");
        match result {
            OptResult::Optimal(_, value) => assert_eq!(
                value, expected,
                "OLL optimum {value} != reference {expected} for {path}"
            ),
            other => panic!("expected OLL to prove optimum {expected}, got {other:?}"),
        }
    }
}

#[test]
fn test_oll_optimal_results_pass_soundness_verification() {
    // Every OLL optimum on the fixtures must independently satisfy all
    // original constraints and re-evaluate to the claimed value.
    for input in [
        "* #variable= 4 #constraint= 3\n\
         min: +1 x1 +2 x2 +3 x3 +4 x4 ;\n\
         +1 x1 +1 x2 +1 x3 +1 x4 >= 2 ;\n\
         +1 x1 +1 x3 >= 1 ;\n\
         +1 x2 +1 x4 >= 1 ;\n",
        "* #variable= 3 #constraint= 1\n\
         min: +2 x1 +3 x2 +4 x3 ;\n\
         +1 x1 +1 x2 +1 x3 >= 2 ;\n",
    ] {
        let mut engine = engine_with_constraints_from_opb(input);
        let result = run_oll(&mut engine);
        let OptResult::Optimal(assignment, value) = result else {
            panic!("expected optimal for instance:\n{input}\n got {result:?}");
        };
        assert!(
            engine.verify_optimum(&assignment, value, value, value),
            "claimed optimum {value} failed soundness verification for:\n{input}"
        );
    }
}

// ---- Stratification + hardening tests ----

#[test]
fn test_oll_high_dispersion_weights_reaches_known_optimum() {
    // Widely varied soft weights with multiple disjoint cores -- exactly the
    // shape stratification targets. Three independent at-least-one pairs:
    //   {x1:100, x2:1}, {x3:50, x4:2}, {x5:25, x6:3}
    // Each pair forces the cheaper literal: 1 + 2 + 3 = 6.
    let input = "* #variable= 6 #constraint= 3\n\
        min: +100 x1 +1 x2 +50 x3 +2 x4 +25 x5 +3 x6 ;\n\
        +1 x1 +1 x2 >= 1 ;\n\
        +1 x3 +1 x4 >= 1 ;\n\
        +1 x5 +1 x6 >= 1 ;\n";
    let mut engine = engine_with_constraints_from_opb(input);
    let result = run_oll(&mut engine);
    assert_eq!(optimum_value(&result), Some(6), "got {result:?}");
}

#[test]
fn test_oll_hardening_does_not_lose_optimum() {
    // A dominating high-weight soft (x1:1000) whose at-least-one partner is
    // cheap (x2:1) forces paying x2; meanwhile a separate large soft (x3:500)
    // is free to be unpaid. Hardening must fix the unpayable-in-better-solution
    // softs without discarding the true optimum (1).
    let input = "* #variable= 4 #constraint= 2\n\
        min: +1000 x1 +1 x2 +500 x3 +1 x4 ;\n\
        +1 x1 +1 x2 >= 1 ;\n\
        +1 x3 +1 x4 >= 0 ;\n";
    let mut engine = engine_with_constraints_from_opb(input);
    let result = run_oll(&mut engine);
    // x2 must be paid (cost 1); x1,x3,x4 can all be unpaid -> optimum 1.
    assert_eq!(optimum_value(&result), Some(1), "got {result:?}");
    if let OptResult::Optimal(assignment, value) = &result {
        assert!(
            engine.verify_optimum(assignment, *value, *value, *value),
            "hardened optimum failed soundness verification"
        );
    }
}

#[test]
fn test_oll_uniform_weights_disables_stratification_but_still_optimal() {
    // Uniform weights: dispersion 0, stratification must collapse to a single
    // stratum (classic OLL). Vertex cover of a triangle -> optimum 2.
    let input = "* #variable= 3 #constraint= 3\n\
        min: +1 x1 +1 x2 +1 x3 ;\n\
        +1 x1 +1 x2 >= 1 ;\n\
        +1 x2 +1 x3 >= 1 ;\n\
        +1 x1 +1 x3 >= 1 ;\n";
    let mut engine = engine_with_constraints_from_opb(input);
    let result = run_oll(&mut engine);
    assert_eq!(optimum_value(&result), Some(2), "got {result:?}");
}

fn random_high_dispersion_weighted_opb(rng: &mut Lcg) -> String {
    let num_vars = 3 + rng.below(4) as u32; // 3..=6 variables
    let num_constraints = 1 + rng.below(4); // 1..=4 constraints
    let mut input = format!("* #variable= {num_vars} #constraint= {num_constraints}\nmin:");
    for v in 1..=num_vars {
        // Wide weight spread (1..=200) so stratification has many buckets.
        let weight = 1 + rng.below(200);
        input.push_str(&format!(" +{weight} x{v}"));
    }
    input.push_str(" ;\n");
    for _ in 0..num_constraints {
        let mut terms = String::new();
        let mut count = 0;
        for v in 1..=num_vars {
            if rng.below(2) == 1 {
                terms.push_str(&format!(" +1 x{v}"));
                count += 1;
            }
        }
        if count == 0 {
            terms.push_str(" +1 x1");
        }
        input.push_str(&terms);
        input.push_str(" >= 1 ;\n");
    }
    input
}

#[test]
fn test_stratified_oll_agrees_with_linear_on_random_high_dispersion() {
    // Differential test specific to stratification: on instances with widely
    // dispersed weights (where stratification is active), the stratified OLL
    // optimum must equal the independently-implemented linear-search optimum.
    let mut rng = Lcg(0xD1B54A32D192ED03);
    let mut checked = 0usize;
    for _ in 0..400 {
        let input = random_high_dispersion_weighted_opb(&mut rng);

        let mut oll_engine = engine_with_constraints_from_opb(&input);
        let oll_result = run_oll(&mut oll_engine);

        let mut linear_engine = engine_with_constraints_from_opb(&input);
        let linear_result = linear::solve(&mut linear_engine);

        match (&oll_result, &linear_result) {
            (OptResult::Optimal(_, a), OptResult::Optimal(_, b)) => {
                assert_eq!(
                    a, b,
                    "stratified OLL and linear disagree for instance:\n{input}\n\
                     OLL={oll_result:?} LINEAR={linear_result:?}"
                );
                checked += 1;
            }
            (OptResult::Infeasible, OptResult::Infeasible) => {
                checked += 1;
            }
            other => {
                panic!("OLL/linear result-kind mismatch for instance:\n{input}\n{other:?}")
            }
        }
    }
    assert!(checked >= 400, "expected all random instances classified");
}

#[test]
fn test_threshold_descent_strictly_decreases_and_floors_at_min() {
    // Unit test of the CASHWMaxSAT diminishing schedule: each lowering must
    // strictly decrease the threshold and never drop below the minimum weight.
    let solver = SatSolver::new(4);
    let softs = vec![
        WeightedSoftLiteral {
            literal: Literal::positive(Variable::new(0)),
            weight: 100,
        },
        WeightedSoftLiteral {
            literal: Literal::positive(Variable::new(1)),
            weight: 40,
        },
        WeightedSoftLiteral {
            literal: Literal::positive(Variable::new(2)),
            weight: 7,
        },
        WeightedSoftLiteral {
            literal: Literal::positive(Variable::new(3)),
            weight: 2,
        },
    ];
    let min_w = 2;
    let mut state = OllState {
        solver,
        softs,
        lower_bound: 0,
        best_assignment: Vec::new(),
        best_value: i128::MAX,
        threshold: i128::MAX,
        assumptions: Vec::new(),
    };
    state.initialize_threshold();
    assert_eq!(state.threshold, 100, "initial threshold = max weight");
    assert!(state.stratification_enabled());

    let mut prev = state.threshold;
    for _ in 0..10 {
        state.lower_threshold();
        assert!(
            state.threshold < prev || state.threshold == min_w,
            "threshold must strictly decrease until it reaches the minimum: \
             prev={prev} now={}",
            state.threshold
        );
        assert!(
            state.threshold >= min_w,
            "threshold must never drop below min weight {min_w}, got {}",
            state.threshold
        );
        prev = state.threshold;
    }
    assert_eq!(
        state.threshold, min_w,
        "descent must bottom out at min weight"
    );
}

#[test]
fn test_uniform_weights_collapse_threshold_to_minimum() {
    // With a single distinct weight, stratification is disabled and the initial
    // threshold collapses to the minimum so all softs are always assumed.
    let solver = SatSolver::new(3);
    let softs = (0..3)
        .map(|v| WeightedSoftLiteral {
            literal: Literal::positive(Variable::new(v)),
            weight: 5,
        })
        .collect();
    let mut state = OllState {
        solver,
        softs,
        lower_bound: 0,
        best_assignment: Vec::new(),
        best_value: i128::MAX,
        threshold: i128::MAX,
        assumptions: Vec::new(),
    };
    assert!(
        !state.stratification_enabled(),
        "uniform weights -> no stratification"
    );
    state.initialize_threshold();
    assert_eq!(state.threshold, 5);
    let full = state.collect_stratum_assumptions();
    assert!(full, "all softs must be in the single stratum");
    assert_eq!(state.assumptions.len(), 3);
}
