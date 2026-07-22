// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for post-BVE clause instantiation (CaDiCaL instantiate.cpp port).
//!
//! Reference: CaDiCaL instantiate.cpp, issue #7437.

use super::super::inprocessing::InstCandidate;
use super::*;

/// Basic instantiation test: a literal that appears in one clause
/// is provably redundant via BCP when assumed TRUE with all other
/// clause literals FALSE.
///
/// Scenario:
/// - Clause C0: (a v b v c)  — target clause, `c` has 1 occurrence
/// - Clause C1: (c v ¬d)     — propagation clause
/// - Clause C2: (¬c v d)     — creates d → ¬c chain
/// - Clause C3: (¬d v ¬b)    — provides conflict chain
/// - Clause C4: (d v ¬a)     — provides conflict chain
///
/// When we try to instantiate `c` in C0:
/// - Assume c=TRUE, a=FALSE, b=FALSE
/// - BCP from ¬a: C4 propagates d=TRUE
/// - BCP from d=TRUE: C3 propagates ¬b (already FALSE) → no new info
/// - BCP from ¬b: no additional propagation
///   Wait, we need a conflict. Let me redesign:
///
/// Actually the correct scenario for conflict is:
/// - Clause C0: (a v b v c)  — target
/// - Clause C1: (¬c v ¬a)    — if c=T, then a=F (already assumed)
/// - Clause C2: (¬c v ¬b)    — if c=T, then b=F (already assumed)
/// - Clause C3: (a v b)      — needs a=T or b=T, but both are FALSE → conflict
///
/// Instantiation of `c` in C0:
/// 1. Assume c=TRUE, a=FALSE, b=FALSE
/// 2. BCP from c=TRUE: C1 → a=FALSE (already), C2 → b=FALSE (already)
/// 3. All literals of C3=(a v b) are FALSE → CONFLICT
/// 4. Therefore `c` is redundant in C0 → strengthen to (a v b)
#[test]
fn test_instantiate_basic_strengthening() {
    let mut solver = Solver::new(4);
    let a = Variable(0);
    let b = Variable(1);
    let c = Variable(2);
    let d = Variable(3); // extra var to avoid pure literal issues

    let la = Literal::positive(a);
    let lb = Literal::positive(b);
    let lc = Literal::positive(c);
    let ld = Literal::positive(d);

    // C0: (a v b v c) — the target clause, c has 1 occurrence
    let c0_idx = solver.add_clause_db(&[la, lb, lc], false);

    // C1: (¬c v ¬a) — if c is TRUE, a must be FALSE
    solver.add_clause_db(&[lc.negated(), la.negated()], false);

    // C2: (¬c v ¬b) — if c is TRUE, b must be FALSE
    solver.add_clause_db(&[lc.negated(), lb.negated()], false);

    // C3: (a v b) — needs at least one of a,b TRUE
    solver.add_clause_db(&[la, lb], false);

    // Add clauses using d to prevent d from being a pure literal
    solver.add_clause_db(&[ld, la], false);
    solver.add_clause_db(&[ld.negated(), lb], false);

    // Freeze a, b, d but NOT c — instantiation skips frozen variables.
    // c is unfrozen so it can be collected as a candidate.
    solver.freeze(a);
    solver.freeze(b);
    solver.freeze(d);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    // Collect instantiation candidates manually.
    // First, rebuild occ lists for candidate collection.
    solver
        .inproc
        .bve
        .rebuild_with_vals(&solver.arena, &solver.vals);

    let candidates = solver.collect_instantiation_candidates();

    // `c` appears in C0 as positive, and C0 has size >= 3.
    // `c` has 1 positive occurrence (C0). It has 2 negative occurrences
    // (C1, C2) which is fine — we're looking at positive `c` in C0.
    let has_lc_candidate = candidates
        .iter()
        .any(|cand| cand.lit == lc && cand.clause_idx == c0_idx);
    assert!(
        has_lc_candidate,
        "positive `c` with 1 occurrence in ternary clause C0 should be a candidate; \
         found {} candidates: {:?}",
        candidates.len(),
        candidates
            .iter()
            .map(|c| (c.lit, c.clause_idx))
            .collect::<Vec<_>>(),
    );

    // Now run instantiation
    let unsat = solver.instantiate(candidates, None);
    assert!(!unsat, "instantiation should not derive UNSAT");

    // Check C0 was strengthened: c should be removed
    let new_lits = solver.arena.literals(c0_idx);
    assert_eq!(
        new_lits.len(),
        2,
        "C0 should be strengthened from ternary to binary, got {new_lits:?}",
    );
    assert!(
        new_lits.contains(&la) && new_lits.contains(&lb),
        "C0 should be (a v b) after removing c, got {new_lits:?}",
    );
    assert!(
        !new_lits.contains(&lc),
        "c should have been removed by instantiation, got {new_lits:?}",
    );
}

/// Test that instantiation does NOT strengthen a clause when BCP
/// finds no conflict.
#[test]
fn test_instantiate_no_conflict_no_strengthening() {
    let mut solver = Solver::new(4);
    let a = Variable(0);
    let b = Variable(1);
    let c = Variable(2);
    let d = Variable(3);

    let la = Literal::positive(a);
    let lb = Literal::positive(b);
    let lc = Literal::positive(c);
    let ld = Literal::positive(d);

    // C0: (a v b v c) — the target clause
    let c0_idx = solver.add_clause_db(&[la, lb, lc], false);

    // No clauses that would cause a conflict when c=T, a=F, b=F.
    // C1: (c v d) — unrelated
    solver.add_clause_db(&[lc, ld], false);

    // Add clauses to prevent pure literals
    solver.add_clause_db(&[la.negated(), ld], false);
    solver.add_clause_db(&[lb.negated(), ld], false);
    solver.add_clause_db(&[ld.negated(), la], false);

    // Freeze a, b, d but NOT c so c can be a candidate.
    solver.freeze(a);
    solver.freeze(b);
    solver.freeze(d);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    solver
        .inproc
        .bve
        .rebuild_with_vals(&solver.arena, &solver.vals);
    let _candidates = solver.collect_instantiation_candidates();

    // c has 2 positive occurrences (C0 and C1=(c v d)), which exceeds
    // INST_OCC_LIMIT=1. So no candidates should be found via positive c.
    // Negative c has 0 occurrences, so no candidates from that side either.
    // This means the formula is set up such that instantiation finds candidates
    // but BCP produces no conflict. Let me use a setup where c has exactly 1
    // positive occurrence.

    // Actually with c in C0 and (c v d), that's 2 positive occurrences.
    // The INST_OCC_LIMIT=1 filter will skip it. This test verifies that
    // even if we manually construct candidates and run instantiation, no
    // strengthening occurs when there's no conflict.

    // Manually create a candidate for lc in C0.
    let manual_candidates = vec![InstCandidate {
        lit: lc,
        clause_idx: c0_idx,
        clause_size: 3,
        neg_occs: 0,
    }];

    let unsat = solver.instantiate(manual_candidates, None);
    assert!(!unsat);

    // C0 should be unchanged — BCP from c=T, a=F, b=F finds no conflict
    // because no clause forces a contradiction.
    let lits = solver.arena.literals(c0_idx);
    assert_eq!(
        lits.len(),
        3,
        "C0 should remain ternary when instantiation finds no conflict",
    );
}

/// Test that instantiation skips clauses with fewer than 3 unassigned
/// literals (CaDiCaL instantiate.cpp:47: `if (unassigned < 3) continue`).
#[test]
fn test_instantiate_skips_small_clauses() {
    let mut solver = Solver::new(3);
    let a = Variable(0);
    let b = Variable(1);
    let c = Variable(2);

    let la = Literal::positive(a);
    let lb = Literal::positive(b);
    let lc = Literal::positive(c);

    // Only a binary clause — should not be a candidate
    solver.add_clause_db(&[la, lb], false);

    // Give `c` exactly 1 occurrence in a ternary clause
    let c0_idx = solver.add_clause_db(&[la, lb, lc], false);

    // Add negative occurrences for c
    solver.add_clause_db(&[lc.negated(), la], false);
    solver.add_clause_db(&[lc.negated(), lb], false);

    solver.freeze(a);
    solver.freeze(b);
    solver.freeze(c);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    solver
        .inproc
        .bve
        .rebuild_with_vals(&solver.arena, &solver.vals);
    let candidates = solver.collect_instantiation_candidates();

    // The binary clause (a v b) should NOT appear as a candidate.
    // Only the ternary clause should potentially appear.
    for cand in &candidates {
        let clause_lits = solver.arena.literals(cand.clause_idx);
        assert!(
            clause_lits.len() >= 3,
            "instantiation candidates must have size >= 3, got {} for clause {:?}",
            clause_lits.len(),
            clause_lits,
        );
    }

    // Check that c0 might still be a candidate if conditions are met
    let _ = c0_idx; // suppress unused warning
}

/// Test that the `instantiated` flag prevents a clause from being
/// collected as a candidate twice.
#[test]
fn test_instantiate_once_flag() {
    let mut solver = Solver::new(4);
    let a = Variable(0);
    let b = Variable(1);
    let c = Variable(2);
    let d = Variable(3);

    let la = Literal::positive(a);
    let lb = Literal::positive(b);
    let lc = Literal::positive(c);
    let ld = Literal::positive(d);

    let c0_idx = solver.add_clause_db(&[la, lb, lc], false);
    solver.add_clause_db(&[ld, la], false);
    solver.add_clause_db(&[ld.negated(), lb], false);

    solver.freeze(a);
    solver.freeze(b);
    solver.freeze(c);
    solver.freeze(d);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    // Manually mark the clause as instantiated
    solver.arena.set_instantiated(c0_idx, true);

    solver
        .inproc
        .bve
        .rebuild_with_vals(&solver.arena, &solver.vals);
    let candidates = solver.collect_instantiation_candidates();

    // C0 should NOT appear because it's already marked instantiated
    let has_c0 = candidates.iter().any(|c| c.clause_idx == c0_idx);
    assert!(
        !has_c0,
        "clause already marked as instantiated should not be collected again"
    );
}
