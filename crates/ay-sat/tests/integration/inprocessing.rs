// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::common::{assert_model_satisfies, generate_test_clauses, verify_model};
use ay_sat::{Literal, SatResult, Solver, Variable};
use ntest::timeout;

macro_rules! inprocessing_test_triad {
    (
        $name_c:ident, $name_s:ident, $name_d:ident,
        label: $label:expr,
        set_enabled: $enable:ident,
        get_stats: $stats:ident,
        zero_field: $zero:ident,
        seeds: [$seed_c:expr, $seed_s:expr, $seed_d:expr],
        stats_check: |$sv:ident| { $($sc:tt)* }
    ) => {
        #[test]
        #[timeout(2_000)]
        fn $name_c() {
            let mut solver = Solver::new(15);
            let clauses = generate_test_clauses(15, 60, $seed_c);
            for clause in &clauses {
                solver.add_clause(clause.clone());
            }
            let result = solver.solve().into_inner();
            if let SatResult::Sat(model) = &result {
                assert_model_satisfies(&clauses, model, $label);
            }
        }

        #[test]
        #[timeout(2_000)]
        fn $name_s() {
            let mut solver = Solver::new(10);
            let clauses = generate_test_clauses(10, 40, $seed_s);
            for clause in &clauses {
                solver.add_clause(clause.clone());
            }
            let _ = solver.solve().into_inner();
            let $sv = solver.$stats();
            $($sc)*
        }

        #[test]
        #[timeout(2_000)]
        fn $name_d() {
            let mut solver = Solver::new(10);
            solver.$enable(false);
            let clauses = generate_test_clauses(10, 40, $seed_d);
            for clause in &clauses {
                solver.add_clause(clause.clone());
            }
            let result = solver.solve().into_inner();
            if let SatResult::Sat(model) = &result {
                assert_model_satisfies(&clauses, model, concat!("Disabled ", $label));
            }
            let stats = solver.$stats();
            assert_eq!(stats.$zero, 0, concat!($label, " ran despite being disabled"));
        }
    };
}

inprocessing_test_triad! {
    test_vivification_correctness, test_vivification_stats, test_vivification_disabled,
    label: "Vivification",
    set_enabled: set_vivify_enabled,
    get_stats: vivify_stats,
    zero_field: clauses_examined,
    seeds: [42, 123, 456],
    stats_check: |stats| {
        assert!(
            stats.clauses_strengthened <= stats.clauses_examined,
            "strengthened ({}) should not exceed examined ({})",
            stats.clauses_strengthened,
            stats.clauses_examined
        );
    }
}

inprocessing_test_triad! {
    test_subsumption_correctness, test_subsumption_stats, test_subsumption_disabled,
    label: "Subsumption",
    set_enabled: set_subsume_enabled,
    get_stats: subsume_stats,
    zero_field: checks,
    seeds: [789, 321, 654],
    stats_check: |stats| {
        assert!(
            stats.checks >= stats.forward_subsumed,
            "checks ({}) must be >= forward_subsumed ({})",
            stats.checks,
            stats.forward_subsumed,
        );
    }
}

inprocessing_test_triad! {
    test_probing_correctness, test_probing_stats, test_probing_disabled,
    label: "Probing",
    set_enabled: set_probe_enabled,
    get_stats: probe_stats,
    zero_field: rounds,
    seeds: [789, 321, 987],
    stats_check: |stats| {
        assert!(
            stats.probed >= stats.failed,
            "probed ({}) must be >= failed ({})",
            stats.probed,
            stats.failed
        );
    }
}

#[test]
#[timeout(2_000)]
fn test_probing_with_failed_literals() {
    let mut solver = Solver::new(4);

    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::negative(Variable::new(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable::new(2)),
        Literal::positive(Variable::new(3)),
    ]);

    let result = solver.solve().into_inner();

    match result {
        SatResult::Sat(model) => assert!(model[0], "x0 should be true (forced by failed literal)"),
        SatResult::Unsat(_) => panic!("Formula should be SAT"),
        SatResult::Unknown => panic!("Got Unknown"),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

inprocessing_test_triad! {
    test_bve_correctness, test_bve_stats, test_bve_disabled,
    label: "BVE",
    set_enabled: set_bve_enabled,
    get_stats: bve_stats,
    zero_field: rounds,
    seeds: [111, 222, 333],
    stats_check: |stats| {
        if stats.vars_eliminated > 0 {
            assert!(
                stats.clauses_removed > 0,
                "vars_eliminated ({}) > 0 but clauses_removed is 0",
                stats.vars_eliminated
            );
        }
    }
}

#[test]
#[timeout(2_000)]
fn test_bve_with_eliminable_variable() {
    let mut solver = Solver::new(5);

    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable::new(0)),
        Literal::positive(Variable::new(2)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable::new(3)),
        Literal::positive(Variable::new(4)),
    ]);

    let result = solver.solve().into_inner();

    match result {
        SatResult::Sat(model) => {
            assert!(model[0] || model[1]);
            assert!(!model[0] || model[2]);
            assert!(model[3] || model[4]);
        }
        SatResult::Unsat(_) => panic!("Formula should be SAT"),
        SatResult::Unknown => panic!("Got Unknown"),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

#[test]
#[timeout(2_000)]
fn test_bve_pure_literal() {
    let mut solver = Solver::new(5);

    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(2)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable::new(3)),
        Literal::positive(Variable::new(4)),
    ]);

    let result = solver.solve().into_inner();

    match result {
        SatResult::Sat(model) => {
            assert!(model[0] || model[1]);
            assert!(model[0] || model[2]);
            assert!(model[3] || model[4]);
        }
        SatResult::Unsat(_) => panic!("Formula should be SAT"),
        SatResult::Unknown => panic!("Got Unknown"),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

inprocessing_test_triad! {
    test_htr_correctness, test_htr_stats, test_htr_disabled,
    label: "HTR",
    set_enabled: set_htr_enabled,
    get_stats: htr_stats,
    zero_field: rounds,
    seeds: [444, 555, 666],
    stats_check: |stats| {
        assert!(
            stats.pairs_checked >= stats.ternary_resolvents + stats.binary_resolvents,
            "pairs_checked ({}) must be >= ternary ({}) + binary ({})",
            stats.pairs_checked,
            stats.ternary_resolvents,
            stats.binary_resolvents
        );
    }
}

#[test]
#[timeout(5_000)]
fn test_gate_correctness() {
    for seed in [777u64, 888, 999] {
        let mut solver = Solver::new(20);
        solver.set_gate_enabled(true);
        let clauses = generate_test_clauses(20, 80, seed);
        for clause in &clauses {
            solver.add_clause(clause.clone());
        }
        let result = solver.solve().into_inner();
        if let SatResult::Sat(model) = &result {
            assert!(
                verify_model(&clauses, model),
                "Gate extraction produced invalid model (seed={seed})"
            );
        }
    }
}

#[test]
#[timeout(2_000)]
fn test_gate_stats() {
    let mut solver = Solver::new(10);
    let clauses = generate_test_clauses(10, 40, 777);

    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let _ = solver.solve().into_inner();

    let stats = solver.gate_stats();
    let computed_total = stats.and_gates + stats.xor_gates + stats.ite_gates + stats.equivalences;
    assert_eq!(
        stats.total_gates(),
        computed_total,
        "total_gates() should equal sum of individual counts"
    );
}

#[test]
#[timeout(2_000)]
fn test_gate_disabled() {
    let mut solver = Solver::new(10);
    solver.set_gate_enabled(false);

    let clauses = generate_test_clauses(10, 40, 888);
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();
    if let SatResult::Sat(model) = &result {
        assert!(
            verify_model(&clauses, model),
            "Disabled gate extraction produced invalid model"
        );
    }

    let stats = solver.gate_stats();
    assert_eq!(
        stats.total_gates(),
        0,
        "gate extraction was disabled but total_gates() is {}",
        stats.total_gates()
    );
}
