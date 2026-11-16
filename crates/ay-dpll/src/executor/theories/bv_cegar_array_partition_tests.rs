// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{CegarArrayBuild, CegarArrayCheck, Executor, FcAuditLits, FcConcreteSelect};
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, TermId};
use ay_sat::{SatResult, Solver as SatSolver};
use num_bigint::BigInt;
use std::collections::BTreeMap;

/// Four reads of one 1-bit array at index 0 with values 0, 0, 1, 1,
/// term bits numbered so index read `i` is lit `i+1` and its value
/// read is lit `i+5`.
fn partition_fixture() -> (Executor, Vec<FcConcreteSelect>, HashMap<TermId, Vec<i32>>) {
    let mut executor = Executor::new();
    let array = executor.ctx.terms.mk_var(
        "partition_array",
        Sort::array(Sort::bitvec(1), Sort::bitvec(1)),
    );
    let mut term_bits = HashMap::default();
    let mut group = Vec::new();
    for i in 0..4 {
        let index = executor
            .ctx
            .terms
            .mk_var(format!("partition_index_{i}"), Sort::bitvec(1));
        let select = executor.ctx.terms.mk_select(array, index);
        let witness = executor
            .ctx
            .terms
            .mk_var(format!("partition_value_{i}"), Sort::bitvec(1));
        let assertion = executor.ctx.terms.mk_eq(select, witness);
        executor.ctx.assertions.push(assertion);
        term_bits.insert(index, vec![i + 1]);
        term_bits.insert(select, vec![i + 5]);
        group.push(FcConcreteSelect {
            select,
            index_lits: vec![i + 1],
            value_lits: vec![i + 5],
            index_value: BigInt::from(0u8),
            value: BigInt::from(u8::from(i >= 2)),
        });
    }
    (executor, group, term_bits)
}

#[test]
fn changed_index_partition_is_audited_again() {
    let (mut executor, group, term_bits) = partition_fixture();
    let bool_lits = HashMap::default();
    let tseitin_lits = BTreeMap::new();
    let lits = FcAuditLits::new(&term_bits, &bool_lits, &tseitin_lits, 0);

    // The first SAT assignment has one index bucket and values 0, 0, 1, 1.
    let mut first_solver = SatSolver::new(8);
    for literal in [-1, -2, -3, -4, -5, -6, 7, 8] {
        assert!(first_solver.add_clause(vec![crate::cnf_lit_to_sat(literal)]));
    }
    let SatResult::Sat(first_model) = first_solver.solve().into_inner() else {
        panic!("first fixed assignment must be satisfiable");
    };
    assert!(matches!(
        executor.check_array_fc_violations(&first_model, &lits, &[], 8, &mut HashSet::default()),
        CegarArrayCheck::Refinement(_)
    ));

    // Build the initial violated tree in a known order: (0,2), (2,1), (0,3).
    let mut build = CegarArrayBuild {
        clauses: Vec::new(),
        next_var: 9,
        new_vars: 0,
        inspected_bits: 0,
        pair_attempts: 0,
        newly_covered: HashSet::default(),
        budget_exhausted: false,
    };
    assert!(executor.append_fc_group_refinement(&group, &HashSet::default(), &mut build));
    assert_eq!(build.newly_covered.len(), 3);
    assert!(build.newly_covered.contains(&(
        group[0].select,
        group[2].select,
        Vec::new(),
        Vec::new()
    )));
    assert!(build.newly_covered.contains(&(
        group[1].select,
        group[2].select,
        Vec::new(),
        Vec::new()
    )));
    assert!(build.newly_covered.contains(&(
        group[0].select,
        group[3].select,
        Vec::new(),
        Vec::new()
    )));

    // Indices now split into {0,2} and {1,3}. Old guards are satisfied,
    // but reads 1 and 3 alias with values 0 and 1, requiring a fresh FC edge.
    let next_var_offset = 8 + build.new_vars;
    let mut covered = build.newly_covered;
    let mut second_solver = SatSolver::new(next_var_offset);
    for clause in build.clauses {
        assert!(second_solver.add_clause(clause));
    }
    for literal in [-1, 2, -3, 4, -5, -6, -7, 8] {
        assert!(second_solver.add_clause(vec![crate::cnf_lit_to_sat(literal)]));
    }
    let SatResult::Sat(second_model) = second_solver.solve().into_inner() else {
        panic!("old guarded edges must permit the changed index partition");
    };
    let CegarArrayCheck::Refinement(next_batch) = executor.check_array_fc_violations(
        &second_model,
        &lits,
        &[],
        next_var_offset,
        &mut covered,
    ) else {
        panic!("final audit must find the new alias violation");
    };
    assert_eq!(next_batch.clauses.len(), 8);
    assert_eq!(covered.len(), 4);
    second_solver.ensure_num_vars(next_var_offset + next_batch.num_new_vars);
    for clause in next_batch.clauses {
        assert!(second_solver.add_clause(clause));
    }
    assert!(matches!(
        second_solver.solve().into_inner(),
        SatResult::Unsat(_)
    ));
}
