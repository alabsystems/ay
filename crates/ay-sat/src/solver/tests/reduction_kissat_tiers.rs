// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-reduce-kissat-tiers`: Kissat 4.0.4's tier rule (`tier_state.rs`).

use super::*;

/// A used-glue histogram with 56 percent of its uses at glue 1, as E00X23's
/// focused mode has. CaDiCaL's scan counts the glue-1 bucket twice and stops
/// at once (tier2 = 2 after the floor); Kissat's starts past it and reaches
/// 90 percent at glue 7.
#[test]
fn kissat_tier_scan_starts_past_the_tier1_glue() {
    for (kissat_rule, tier2) in [(false, 2), (true, 7)] {
        let mut solver = Solver::new(4);
        solver.tiers.kissat_rule = kissat_rule;
        let mode = usize::from(solver.stable_mode);
        for (glue, uses) in [
            (1, 56),
            (2, 6),
            (3, 6),
            (4, 6),
            (5, 6),
            (6, 6),
            (7, 6),
            (8, 8),
        ] {
            solver.tiers.tier_usage[mode][glue] = uses;
        }
        solver.tiers.tier_bump_total[mode] = 100;
        solver.recompute_tier();
        assert_eq!(solver.tiers.tier1_lbd[mode], 1);
        assert_eq!(
            solver.tiers.tier2_lbd[mode], tier2,
            "kissat_rule = {kissat_rule}"
        );
    }
}

/// Under Kissat's rule reduction reads tier2 from stable mode, so a glue-10
/// clause is tier1 (kept when recently used) where CaDiCaL's rule makes it
/// tier2 (always a candidate).
#[test]
fn kissat_rule_reduces_against_the_stable_tier2() {
    let lit = |v: u32| Literal::positive(Variable(v));
    for (kissat_rule, tier) in [(false, ClauseTier::Tier2), (true, ClauseTier::Tier1)] {
        let mut solver = Solver::new(4);
        solver.tiers.kissat_rule = kissat_rule;
        solver.tiers.tier1_lbd = [1, 4];
        solver.tiers.tier2_lbd = [2, 19];
        let idx = solver.add_clause_db(&[lit(0), lit(1), lit(2)], true);
        solver.arena.set_lbd(idx, 10);
        assert_eq!(solver.clause_tier(idx), tier, "kissat_rule = {kissat_rule}");
        assert_eq!(solver.likely_to_be_kept(idx), kissat_rule);
    }
}

/// Kissat's histogram tells glues apart up to 127 (its stable tier2 reaches
/// 127 on cabp-V-nos6); CaDiCaL's rule keeps the old 63-bucket clamp. With
/// half the uses at glue 100 the Kissat scan puts tier2 there.
#[test]
fn kissat_rule_counts_glue_up_to_127() {
    let mut solver = Solver::new(4);
    assert_eq!(solver.tiers.max_glue_used(), 63);
    solver.tiers.kissat_rule = true;
    assert_eq!(solver.tiers.max_glue_used(), 127);
    let mode = usize::from(solver.stable_mode);
    solver.tiers.tier_usage[mode][1] = 50;
    solver.tiers.tier_usage[mode][100] = 50;
    solver.tiers.tier_bump_total[mode] = 100;
    solver.recompute_tier();
    assert_eq!(solver.tiers.tier1_lbd[mode], 1);
    assert_eq!(solver.tiers.tier2_lbd[mode], 100);
}
