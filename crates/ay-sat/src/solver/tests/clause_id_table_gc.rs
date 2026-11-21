// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! AY-SAT-1: the clause-id table keeps every live clause's proof id through
//! the solver's own add, delete, arena garbage collection
//! (`compact_arena_locality`) and append rollback (`rollback_appends`, as
//! congruence's ladder rungs use it), on a seeded random sequence.

use super::*;
use std::collections::BTreeMap;

/// A small deterministic generator (no test may depend on the clock).
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 33
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// A clause of 2..=6 distinct variables out of `num_vars`.
fn random_clause(rng: &mut Lcg, num_vars: u32) -> Vec<Literal> {
    let len = 2 + rng.below(5) as usize;
    let mut vars: Vec<u32> = Vec::with_capacity(len);
    while vars.len() < len {
        let var = rng.below(u64::from(num_vars)) as u32;
        if !vars.contains(&var) {
            vars.push(var);
        }
    }
    vars.into_iter()
        .map(|var| {
            if rng.below(2) == 0 {
                Literal::positive(Variable(var))
            } else {
                Literal::negative(Variable(var))
            }
        })
        .collect()
}

fn sorted(lits: &[Literal]) -> Vec<Literal> {
    let mut lits = lits.to_vec();
    lits.sort_by_key(|lit| lit.index());
    lits
}

/// Every active clause reads the non-zero id it was given, and the ids of
/// the active clauses are exactly the live ones.
fn assert_live_ids(solver: &Solver, live: &BTreeMap<u64, Vec<Literal>>, when: &str) {
    let mut seen = BTreeMap::new();
    for idx in solver.arena.active_indices() {
        let id = solver.clause_id(ClauseRef(idx as u32));
        assert_ne!(id, 0, "{when}: active clause at {idx} lost its id");
        let expected = live
            .get(&id)
            .unwrap_or_else(|| panic!("{when}: clause at {idx} reads id {id}, not a live id"));
        assert_eq!(
            &sorted(solver.arena.literals(idx)),
            expected,
            "{when}: id {id} reads at a clause with other literals"
        );
        assert!(
            seen.insert(id, idx).is_none(),
            "{when}: id {id} read at two clauses"
        );
    }
    assert_eq!(
        seen.keys().collect::<Vec<_>>(),
        live.keys().collect::<Vec<_>>(),
        "{when}: live ids and active clauses differ"
    );
}

#[test]
fn clause_id_table_keeps_live_ids_through_gc_and_rollback() {
    const NUM_VARS: u32 = 48;
    let mut rng = Lcg(0x5eed_a5a7_0001);
    let mut solver = Solver::new(NUM_VARS as usize);
    let mut live: BTreeMap<u64, Vec<Literal>> = BTreeMap::new();
    let mut offsets: Vec<usize> = Vec::new();
    let mut next_rung_id = 1_000_000_000_u64;

    for round in 0..12 {
        // Add a batch, learned and irredundant mixed.
        for _ in 0..40 {
            let lits = random_clause(&mut rng, NUM_VARS);
            let learned = rng.below(3) == 0;
            let idx = solver.add_clause_db(&lits, learned);
            let id = solver.clause_id(ClauseRef(idx as u32));
            assert_ne!(id, 0, "round {round}: a new clause has an id");
            assert!(live.insert(id, sorted(&lits)).is_none());
            offsets.push(idx);
        }
        assert_live_ids(&solver, &live, "after adds");

        // Rungs: append irredundant clauses with ids, take the ids, roll
        // the arena back; the next adds reuse those offsets.
        let mark = solver.arena.append_mark();
        let mut rungs = Vec::new();
        for _ in 0..(1 + rng.below(6)) {
            let lits = random_clause(&mut rng, NUM_VARS);
            let idx = solver.arena.add(&lits, false);
            solver.cold.record_clause_id(idx, next_rung_id);
            next_rung_id += 1;
            rungs.push(idx);
        }
        for &idx in &rungs {
            let id = solver
                .cold
                .clause_ids
                .get_mut(idx)
                .map_or(0, std::mem::take);
            assert_ne!(id, 0, "round {round}: a rung had its id");
        }
        solver.arena.rollback_appends(mark);
        assert_live_ids(&solver, &live, "after rollback");
        for _ in 0..10 {
            let lits = random_clause(&mut rng, NUM_VARS);
            let idx = solver.add_clause_db(&lits, false);
            let id = solver.clause_id(ClauseRef(idx as u32));
            assert!(live.insert(id, sorted(&lits)).is_none());
            offsets.push(idx);
        }
        assert_live_ids(&solver, &live, "after adds over rolled-back rungs");

        // Delete about a third of the live clauses, then collect.
        for idx in offsets.drain(..) {
            if rng.below(3) == 0 {
                let id = solver.clause_id(ClauseRef(idx as u32));
                live.remove(&id);
                solver.arena.delete(idx);
            }
        }
        assert_live_ids(&solver, &live, "after deletes");
        solver.compact_arena_locality();
        assert_live_ids(&solver, &live, "after arena GC");
        offsets = solver.arena.active_indices().collect();
    }
    assert!(!live.is_empty());
}
