// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]
use super::*;
use crate::counted_storage::test_owner;
use ay_core::original_query::FiniteAdmissionGrant;
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};

mod replay;
mod resources;
mod unwind;

fn pos(v: u32) -> Literal {
    Literal::positive(Variable(v))
}
fn neg(v: u32) -> Literal {
    pos(v).negated()
}

pub(super) fn materializer() -> Solver {
    let mut s = Solver::new(4);
    s.enable_clause_trace();
    s.set_unsat_certificate_enabled(false);
    assert!(!s.veripb_hints_active()); // caller captures configuration before owner
    let support = s.add_clause_db(&[pos(0)], false);
    let first = s.add_clause_db(&[pos(1), neg(0)], false);
    let second = s.add_clause_db(&[pos(2), neg(1)], false);
    let last = s.add_clause_db(&[pos(3)], false);
    s.trail = (0..4).map(pos).collect();
    for var in 0..4 {
        s.var_data[var].level = 0;
        s.var_data[var].trail_pos = var as u32;
        s.var_data[var].reason = [NO_REASON, first as u32, second as u32, last as u32][var];
        s.vals[pos(var as u32).index()] = 1;
        s.vals[neg(var as u32).index()] = -1;
    }
    let id = s.clause_id(ClauseRef(support as u32));
    s.record_unit_proof_id_for_lit(pos(0), id);
    s
}

pub(super) fn rows(s: &Solver) -> Vec<(u64, Vec<Literal>, bool, Vec<u64>)> {
    s.cold
        .clause_trace
        .as_ref()
        .unwrap()
        .entries()
        .iter()
        .map(|e| {
            (
                e.id,
                e.clause.to_vec(),
                e.is_original,
                e.resolution_hints.to_vec(),
            )
        })
        .collect()
}

#[test]
fn real_materialization_and_pinned_retry_preserve_ordinary_ids_rows_and_counters() {
    let mut ordinary = materializer();
    let mut counted = materializer();
    let owner = test_owner(1_000_000, 1_000_000);
    let before = rows(&counted);
    for pass in 0..3 {
        ordinary.materialize_level0_unit_proofs();
        counted
            .materialize_level0_unit_proofs_impl(false, &Counted(&owner))
            .unwrap();
        assert_eq!(
            counted.lrat_materialization_stats(),
            ordinary.lrat_materialization_stats()
        );
        assert_eq!(rows(&counted), before);
        assert_eq!(rows(&counted), rows(&ordinary));
        assert_eq!(counted.unit_proof_id, ordinary.unit_proof_id);
        assert_eq!(counted.cold.level0_proof_id, ordinary.cold.level0_proof_id);
        assert_eq!(counted.cold.lrat_level0_unit_materialize_pinned, [1, 2]);
        assert_eq!(counted.cold.lrat_level0_unit_materialize_cursor, 4);
        assert_eq!(
            counted.stats.lrat_materialize_root_trail_entries,
            4 + pass * 2
        );
        assert_eq!(counted.stats.lrat_materialize_emitted_unit_lines, 0);
        assert_eq!(counted.stats.lrat_materialize_hidden_trusted_units, 0);
        assert_eq!(counted.cold.lrat_materialize_hints_buf.len(), 0);
        assert_eq!(
            counted.cold.lrat_materialize_hints_buf.capacity(),
            ordinary.cold.lrat_materialize_hints_buf.capacity()
        );
    }
    assert!(owner.usage().unwrap().storage_admitted > 0);
}

#[derive(Clone, Copy)]
enum Roots {
    Input,
    Implied,
}

fn analysis_fixture(kind: Roots) -> (Solver, ClauseRef, Vec<Vec<Literal>>) {
    let mut s = Solver::new(5);
    s.enable_clause_trace();
    s.set_unsat_certificate_enabled(false);
    s.set_preprocess_enabled(false);
    let root = match kind {
        Roots::Input => 0,
        Roots::Implied => 1,
    };
    let mut cnf = vec![vec![pos(0)]];
    if matches!(kind, Roots::Implied) {
        cnf.push(vec![neg(0), pos(1)]);
    }
    cnf.extend([
        vec![neg(2), pos(3), neg(root)],
        vec![neg(2), pos(4), neg(root)],
        vec![neg(3), neg(4), neg(root)],
    ]);
    for clause in &cnf {
        assert!(s.add_clause(clause.clone()));
    }
    s.initialize_watches();
    assert!(s.process_initial_clauses().is_none());
    assert!(s.search_propagate().is_none());
    assert_eq!(s.lit_val(pos(root)), 1);
    assert_eq!(s.var_data[root as usize].level, 0);
    s.decide(pos(2));
    let conflict = s.search_propagate().unwrap();
    (s, conflict, cnf)
}

#[derive(Debug, PartialEq, Eq)]
struct Learned {
    clause: Vec<Literal>,
    chain: Vec<u64>,
    backtrack: u32,
    lbd: u32,
}

fn run(s: &mut Solver, conflict: ClauseRef) -> Result<Learned, SatUnknownReason> {
    let scope = s.begin_counted_standard_analysis(conflict)?.unwrap();
    let result = Learned {
        clause: scope.learned_clause().to_vec(),
        chain: scope.resolution_chain().to_vec(),
        backtrack: scope.backtrack_level(),
        lbd: scope.lbd(),
    };
    scope.finish()?;
    Ok(result)
}

fn clean(s: &Solver) {
    assert_eq!(s.min.lrat_to_clear.len(), 0);
    assert!(s.min.minimize_flags.iter().all(|&v| v == 0));
    assert!(s.var_data.iter().all(|v| !v.is_seen()));
    assert_eq!(s.cold.lrat_materialize_hints_buf.len(), 0);
    assert_eq!(s.conflict.analyzed_vars().len(), 0);
    assert_eq!(s.conflict.learned_count(), 0);
}

#[test]
fn actual_root_conflict_analysis_matches_ordinary_and_truth_table_entailment() {
    for kind in [Roots::Input, Roots::Implied] {
        let (mut expected, conflict, cnf) = analysis_fixture(kind);
        let result = expected.analyze_conflict(conflict).unwrap();
        let wanted = Learned {
            clause: result.learned_clause,
            chain: result.resolution_chain,
            backtrack: result.backtrack_level,
            lbd: result.lbd,
        };
        let (mut actual, conflict, _) = analysis_fixture(kind);
        let owner = test_owner(1_000_000, 1_000_000);
        assert!(actual.attach_counted_admission(owner.clone()).is_ok());
        let learned = run(&mut actual, conflict).unwrap();
        assert_eq!(learned, wanted);
        assert_eq!(
            actual.lrat_materialization_stats(),
            expected.lrat_materialization_stats()
        );
        assert_eq!(rows(&actual), rows(&expected));
        assert!(actual.stats.lrat_unit_chain_hints > 0);
        if matches!(kind, Roots::Implied) {
            assert!(actual.stats.lrat_unit_chain_missing_hints > 0);
        }
        for mask in 0..32 {
            let eval =
                |lit: &Literal| ((mask >> lit.variable().index()) & 1 != 0) == lit.is_positive();
            if cnf.iter().all(|clause| clause.iter().any(eval)) {
                assert!(learned.clause.iter().any(eval), "mask {mask}");
            }
        }
        clean(&actual);
    }
}
