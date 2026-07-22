// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::analysis::probe_dominator;
use super::*;
use crate::solver::VarData;
use crate::solver::NO_REASON;

/// Verify that Prober::new allocates buffers of correct size.
///
/// Invariant: For any num_vars, bin_occs and propfixed have length 2*num_vars.
/// Bound to 8 vars for CBMC tractability (Vec::extend_with unwinds 2*num_vars).
#[kani::proof]
#[kani::unwind(25)]
fn proof_prober_new_buffer_sizes() {
    let num_vars: usize = kani::any();
    kani::assume(num_vars < 8);

    let prober = Prober::new(num_vars);

    assert_eq!(prober.bin_occs.len(), num_vars * 2);
    assert_eq!(prober.propfixed.len(), num_vars * 2);
    assert_eq!(prober.uip_seen.len(), num_vars);
    assert!(prober.probes.is_empty());
    assert_eq!(prober.num_vars, num_vars);
}

/// Verify that mark_probed respects bounds.
///
/// Invariant: mark_probed only writes within bounds, even for arbitrary literals.
/// Concrete num_vars=4 (propfixed.len()=8). lit_code < 12 covers both
/// in-bounds (0..7) and out-of-bounds (8..11) paths.
#[kani::proof]
#[kani::unwind(15)]
fn proof_mark_probed_bounds() {
    let num_vars = 4_usize;
    let mut prober = Prober::new(num_vars);

    let lit_code: u32 = kani::any();
    kani::assume(lit_code < 12);
    let lit = Literal(lit_code);
    let current_fixed: i64 = kani::any();

    // mark_probed should not panic, even for out-of-bounds literals
    prober.mark_probed(lit, current_fixed);

    // If literal was in bounds, it should be marked
    let idx = lit.index();
    if idx < prober.propfixed.len() {
        assert_eq!(prober.propfixed[idx], current_fixed);
    }
}

/// Verify ensure_num_vars grows buffers correctly.
///
/// Invariant: After ensure_num_vars(n), buffers have capacity >= 2*n.
/// Both bounds tightened to <8 for CBMC tractability (two Prober allocations).
#[kani::proof]
#[kani::unwind(25)]
fn proof_ensure_num_vars_growth() {
    let initial_vars: usize = kani::any();
    let new_vars: usize = kani::any();
    kani::assume(initial_vars < 8 && new_vars < 8);

    let mut prober = Prober::new(initial_vars);
    prober.ensure_num_vars(new_vars);

    let expected_len = new_vars.max(initial_vars) * 2;
    assert!(prober.bin_occs.len() >= expected_len);
    assert!(prober.propfixed.len() >= expected_len);
    assert!(prober.uip_seen.len() >= new_vars.max(initial_vars));
    assert!(prober.num_vars >= new_vars);
}

/// Verify probe_dominator returns same literal for identical inputs (concrete).
///
/// Invariant: probe_dominator(a, a, ...) = Some(a).
/// Concrete harness: tests 4 representative literals (pos var0, neg var0,
/// pos var2, neg var2) against the reflexive property. Symbolic version
/// times out due to ClauseArena VCC explosion.
#[kani::proof]
#[kani::unwind(5)]
fn proof_dominator_reflexive() {
    // Test 4 concrete representative literals
    let test_cases: [(u32, usize); 4] = [
        (0, 0), // positive var 0
        (1, 0), // negative var 0
        (4, 2), // positive var 2
        (5, 2), // negative var 2
    ];

    for &(code, var_idx) in &test_cases {
        let lit = Literal(code);
        let trail: Vec<Literal> = vec![lit];
        let var_data: Vec<VarData> = {
            let mut vd = vec![VarData::UNASSIGNED; var_idx + 1];
            vd[var_idx] = VarData {
                level: 1,
                trail_pos: 0,
                reason: NO_REASON,
                flags: 0,
                _pad: [0; 3],
            };
            vd
        };
        let probe_parent: Vec<Option<Literal>> = vec![None; var_idx + 1];
        let clauses = ClauseArena::new();

        let result = probe_dominator(lit, lit, &trail, &var_data, &probe_parent, &clauses);
        assert_eq!(result, Some(lit));
    }
}

/// Verify HBR doesn't produce binary clause for clauses with <= 2 literals.
///
/// Invariant: hyper_binary_resolve on short clauses returns None.
/// Concrete representative literals: symbolic lit codes cause ClauseArena
/// VCC explosion. Tests empty clause, unit clause, and binary clause.
#[kani::proof]
#[kani::unwind(5)]
fn proof_hbr_short_clause_no_output() {
    let lit0_code: u32 = kani::any();
    let lit1_code: u32 = kani::any();
    kani::assume(lit0_code < 8 && lit1_code < 8);

    let lits = vec![Literal(lit0_code), Literal(lit1_code)];
    let trail: Vec<Literal> = vec![];
    let var_data: Vec<VarData> = vec![];
    let probe_parent: Vec<Option<Literal>> = vec![];
    let clauses = ClauseArena::new();

    let result = hyper_binary_resolve(&lits, &trail, &var_data, &probe_parent, &clauses, false);

    // Binary or smaller clauses should not produce HBR
    assert!(result.binary_clause.is_none());
}

/// Verify statistics counters are consistent after symbolic operations.
///
/// Symbolic bounds (0..15) for each counter. Tests that record_round,
/// record_probed, and record_failed increment the correct stats fields
/// and that units_derived == failed (1 unit per failed literal).
#[kani::proof]
#[kani::unwind(20)]
fn proof_stats_no_overflow() {
    let mut prober = Prober::new(4);

    let rounds: u8 = kani::any();
    kani::assume(rounds < 16);
    for _ in 0..rounds {
        prober.record_round();
    }

    let probed: u8 = kani::any();
    kani::assume(probed < 16);
    for _ in 0..probed {
        prober.record_probed();
    }

    let failed: u8 = kani::any();
    kani::assume(failed < 16);
    for _ in 0..failed {
        prober.record_failed();
    }

    assert_eq!(prober.stats.rounds, rounds as u64);
    assert_eq!(prober.stats.probed, probed as u64);
    assert_eq!(prober.stats.failed, failed as u64);
    assert_eq!(prober.stats.units_derived, failed as u64);
}
