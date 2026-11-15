// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::{CegarArrayCheck, FcAuditLits, NestedReadPaths};
use crate::executor::Executor;
use ay_bv::BvBits;
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, TermId};
use ay_sat::{SatResult, Solver as SatSolver};
use std::collections::BTreeMap;

/// `m : (Array (_ BitVec 1) (Array (_ BitVec 1) (_ BitVec 1)))` read as
/// `m[i][j]` (bits 1, 2; value bit 5) and `m[k][l]` (bits 3, 4; value bit 6):
/// the two reads go through different row terms, `(select m i)` and
/// `(select m k)`, which have no bits of their own.
fn row_reads() -> (Executor, HashMap<TermId, BvBits>) {
    let mut executor = Executor::new();
    let row = Sort::array(Sort::bitvec(1), Sort::bitvec(1));
    let m = executor
        .ctx
        .terms
        .mk_var("m", Sort::array(Sort::bitvec(1), row));
    let mut term_bits = HashMap::default();
    for (n, (row_index, cell_index)) in [("i", "j"), ("k", "l")].into_iter().enumerate() {
        let n = n as i32;
        let row_index = executor.ctx.terms.mk_var(row_index, Sort::bitvec(1));
        let cell_index = executor.ctx.terms.mk_var(cell_index, Sort::bitvec(1));
        let row_term = executor.ctx.terms.mk_select(m, row_index);
        let read = executor.ctx.terms.mk_select(row_term, cell_index);
        let witness = executor.ctx.terms.mk_var(format!("w{n}"), Sort::bitvec(1));
        let assertion = executor.ctx.terms.mk_eq(read, witness);
        executor.ctx.assertions.push(assertion);
        term_bits.insert(row_index, vec![2 * n + 1]);
        term_bits.insert(cell_index, vec![2 * n + 2]);
        term_bits.insert(read, vec![n + 5]);
    }
    (executor, term_bits)
}

/// The SAT model fixing every bit to `units` (literals over vars 1..=6).
fn fixed_model(units: &[i32]) -> Vec<bool> {
    let mut solver = SatSolver::new(6);
    for &unit in units {
        assert!(solver.add_clause(vec![crate::cnf_lit_to_sat(unit)]));
    }
    let SatResult::Sat(model) = solver.solve().into_inner() else {
        panic!("fixed unit assignment must be satisfiable");
    };
    model
}

/// One cell, two values: `i = k = 1`, `j = l = 0`, `m[i][j] = 0`,
/// `m[k][l] = 1`. The direct-operand audit never compares the two reads;
/// the read-path pass refines them, and the lemma excludes the assignment.
#[test]
fn one_cell_read_through_two_row_terms_is_refined() {
    let (mut executor, term_bits) = row_reads();
    let (bool_lits, tseitin_lits) = (HashMap::default(), BTreeMap::new());
    let lits = FcAuditLits::new(&term_bits, &bool_lits, &tseitin_lits, 0);
    let units = [1, -2, 3, -4, -5, 6];
    let model = fixed_model(&units);

    assert!(matches!(
        executor.check_array_fc_violations_with(
            &model,
            &lits,
            &[],
            6,
            &mut HashSet::default(),
            NestedReadPaths::Skip,
        ),
        CegarArrayCheck::Consistent
    ));
    let mut covered = HashSet::default();
    let CegarArrayCheck::Refinement(batch) =
        executor.check_array_fc_violations(&model, &lits, &[], 6, &mut covered)
    else {
        panic!("the read path m[1][0] holds two values");
    };
    assert_eq!(covered.len(), 1);

    let mut solver = SatSolver::new(6 + batch.num_new_vars);
    for clause in batch.clauses {
        assert!(solver.add_clause(clause));
    }
    for unit in units {
        assert!(solver.add_clause(vec![crate::cnf_lit_to_sat(unit)]));
    }
    assert!(matches!(solver.solve().into_inner(), SatResult::Unsat(_)));
}

/// Negative twin: `i = 1`, `k = 0` read different rows, so their cells may
/// differ and nothing is refined.
#[test]
fn reads_of_different_rows_are_not_refined() {
    let (mut executor, term_bits) = row_reads();
    let (bool_lits, tseitin_lits) = (HashMap::default(), BTreeMap::new());
    let lits = FcAuditLits::new(&term_bits, &bool_lits, &tseitin_lits, 0);
    let model = fixed_model(&[1, -2, -3, -4, -5, 6]);

    assert!(matches!(
        executor.check_array_fc_violations(&model, &lits, &[], 6, &mut HashSet::default()),
        CegarArrayCheck::Consistent
    ));
}

/// The refinement stays valid once the indices move: with the lemma in
/// place, `i = k` and `j = l` still admit any value both reads share, and a
/// different row still admits different values.
#[test]
fn the_read_path_lemma_keeps_every_array_model() {
    let (mut executor, term_bits) = row_reads();
    let (bool_lits, tseitin_lits) = (HashMap::default(), BTreeMap::new());
    let lits = FcAuditLits::new(&term_bits, &bool_lits, &tseitin_lits, 0);
    let model = fixed_model(&[1, -2, 3, -4, -5, 6]);
    let CegarArrayCheck::Refinement(batch) =
        executor.check_array_fc_violations(&model, &lits, &[], 6, &mut HashSet::default())
    else {
        panic!("the read path m[1][0] holds two values");
    };
    for units in [[1, -2, 3, -4, 5, 6], [1, -2, -3, -4, -5, 6]] {
        let mut solver = SatSolver::new(6 + batch.num_new_vars);
        for clause in &batch.clauses {
            assert!(solver.add_clause(clause.clone()));
        }
        for unit in units {
            assert!(solver.add_clause(vec![crate::cnf_lit_to_sat(unit)]));
        }
        assert!(
            matches!(solver.solve().into_inner(), SatResult::Sat(_)),
            "{units:?} is an array model"
        );
    }
}
