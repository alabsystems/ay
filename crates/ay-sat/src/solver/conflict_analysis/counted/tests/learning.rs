// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

mod controls;
mod eager_unlink;
mod selected;
mod semantics;
mod trace;

fn fork(guards: u32, gap: u32) -> (Solver, ClauseRef, Vec<Vec<Literal>>) {
    let decision = guards + gap;
    let mut s = Solver::new((decision + 3) as usize);
    s.enable_clause_trace();
    s.set_unsat_certificate_enabled(false);
    s.set_preprocess_enabled(false);
    let mut source = Vec::new();
    for next in [decision + 1, decision + 2] {
        let mut clause = vec![neg(decision), pos(next)];
        clause.extend((0..guards).map(neg));
        source.push(clause);
    }
    source.push(vec![neg(decision + 1), neg(decision + 2)]);
    for clause in &source {
        assert!(s.add_clause(clause.clone()));
    }
    s.initialize_watches();
    for var in 0..decision {
        s.decide(pos(var));
        assert!(s.search_propagate().is_none());
    }
    s.decide(pos(decision));
    let reference = s.search_propagate().expect("genuine fork conflict");
    assert!(s.chrono_enabled && s.cold.lrat_enabled && !s.cold.ic3_mode);
    (s, reference, source)
}

fn learn(s: &mut Solver, reference: ClauseRef) -> Result<CountedLearnedStep, SatUnknownReason> {
    s.begin_counted_standard_analysis(reference)?
        .expect("real conflict must produce an asserting clause")
        .learn_and_assert()
}

fn trace_rows(s: &Solver) -> Vec<(u64, Vec<Literal>, bool, Vec<u64>)> {
    s.clause_trace()
        .unwrap()
        .entries()
        .iter()
        .map(|row| {
            (
                row.id,
                row.clause.to_vec(),
                row.is_original,
                row.resolution_hints.to_vec(),
            )
        })
        .collect()
}

fn parity(s: &Solver, expected: &Solver) {
    assert_eq!(s.trail, expected.trail);
    assert_eq!(s.trail_lim, expected.trail_lim);
    assert_eq!(s.vals, expected.vals);
    assert_eq!(s.phase, expected.phase);
    assert_eq!(s.qhead, expected.qhead);
    assert_eq!(s.decision_level, expected.decision_level);
    assert_eq!(s.fixed_count, expected.fixed_count);
    assert_eq!(clauses(s), clauses(expected));
    assert_eq!(s.cold.clause_ids, expected.cold.clause_ids);
    assert_eq!(
        s.cold.learned_clause_trail,
        expected.cold.learned_clause_trail
    );
    assert_eq!(s.dirty_watch_list, expected.dirty_watch_list);
    assert_eq!(s.dirty_watches, expected.dirty_watches);
    assert_eq!(trace_rows(s), trace_rows(expected));
    assert_eq!(
        s.cold.num_eager_subsumptions,
        expected.cold.num_eager_subsumptions
    );
    assert_eq!(
        s.cold.num_eager_subsumed_duplicate_binaries,
        expected.cold.num_eager_subsumed_duplicate_binaries
    );
    assert_eq!(s.stats.lbd_sum, expected.stats.lbd_sum);
    assert_eq!(s.stats.lbd_count, expected.stats.lbd_count);
    assert_eq!(
        s.cold.lbd_ema_fast.to_bits(),
        expected.cold.lbd_ema_fast.to_bits()
    );
    assert_eq!(
        s.cold.lbd_ema_slow.to_bits(),
        expected.cold.lbd_ema_slow.to_bits()
    );
    assert_eq!(s.vsids.buffer_bytes(), expected.vsids.buffer_bytes());
    for var in 0..s.num_vars {
        for literal in [pos(var as u32), neg(var as u32)] {
            assert_eq!(
                s.watches.entry_slice(literal),
                expected.watches.entry_slice(literal)
            );
            assert_eq!(
                s.watches.binary_count_of(literal),
                expected.watches.binary_count_of(literal)
            );
            assert_eq!(
                s.watches.capacity_of(literal),
                expected.watches.capacity_of(literal)
            );
        }
        let a = s.var_data[var];
        let b = expected.var_data[var];
        assert_eq!(
            (a.level, a.trail_pos, a.reason, a.is_binary_reason()),
            (b.level, b.trail_pos, b.reason, b.is_binary_reason())
        );
        assert_eq!(
            s.vsids.activity(Variable(var as u32)).to_bits(),
            expected.vsids.activity(Variable(var as u32)).to_bits()
        );
        assert_eq!(
            s.vsids.bump_order(Variable(var as u32)),
            expected.vsids.bump_order(Variable(var as u32))
        );
    }
    assert_eq!(
        s.clause_db_memory_bytes(),
        expected.clause_db_memory_bytes()
    );
}
