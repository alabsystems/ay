// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Per-candidate conditioning regressions.

use super::*;

/// Per-candidate refinement eliminates clauses the global fixpoint misses.
///
/// Formula: C1=(¬1), C2=(1 ∨ ¬2), C3=(¬1 ∨ 2). Assignment: 1=T, 2=T.
///
/// Global fixpoint: C1 makes var 1 conditional. C2=(1 ∨ ¬2) has all
/// positive lits (var 1) conditional → promotes var 2. After fixpoint:
/// both vars conditional → C3 has no autarky → NOT eliminated.
///
/// Per-candidate refinement for C3=(¬1 ∨ 2): var 1 is conditional, but
/// lit(¬1) IS in C3 → var 1 is NOT unassigned → C2 never triggers →
/// var 2 stays autarky → C3 HAS autarky literal lit(2) → eliminated.
///
/// Reference: CaDiCaL condition.cpp:565-705 (per-candidate refinement).
#[test]
fn test_conditioning_per_candidate_refinement() {
    let mut db = ClauseArena::new();
    let _c1 = db.add(&[lit(-1)], false); // (¬1)
    let _c2 = db.add(&[lit(1), lit(-2)], false); // (1 ∨ ¬2)
    let c3 = db.add(&[lit(-1), lit(2)], false); // (¬1 ∨ 2) — candidate

    let vals = make_vals(2, &[(1, true), (2, true)]);
    let frozen = vec![0u32; 2];
    let reason_marks = vec![0u32; db.len()];

    let mut cond = Conditioning::new(2);
    cond.ensure_num_vars(2);
    let result = cond.condition_round(
        &mut db,
        &vals,
        &vals,
        &frozen,
        &reason_marks,
        1,
        1000,
        100_000,
    );

    // Per-candidate refinement: C3 contains lit(¬1), so the conditional
    // literal (var 1) is NOT unassigned for this candidate. The promotion
    // chain (var 1 → var 2) never triggers. var 2 stays autarky →
    // C3 has autarky literal (var 2) → eliminated.
    assert_eq!(
        result.eliminated.len(),
        1,
        "Per-candidate refinement should eliminate C3. Got {} eliminations.",
        result.eliminated.len()
    );
    assert_eq!(
        result.eliminated[0].clause_idx, c3,
        "Eliminated clause should be C3"
    );

    // Witness should include var 2 (autarky).
    assert!(
        result.eliminated[0]
            .witnesses
            .iter()
            .any(|w| w.variable().index() == 1), // var 2 = internal index 1
        "Witness should include var 2 (internal index 1)"
    );
}

/// Regression test: per-candidate refinement must check the NEGATION of
/// the conditional literal against the candidate clause, not the variable.
///
/// CaDiCaL condition.cpp:574: `is_in_candidate_clause(-conditional_lit)`
/// checks the negated literal. Previously AY checked CANDIDATE_BIT on the
/// variable, which conflated `lit` with `~lit`. This caused unsound GBCE
/// on UNSAT formulas where a conditional literal appeared POSITIVELY in
/// the candidate clause.
///
/// Formula: C1=(¬1 ∨ ¬2 ∨ ¬4), C2=(1 ∨ 3), C3=(1 ∨ ¬3), C4=(¬1 ∨ ¬2 ∨ 4)
/// Root assignment: var 2 = true (at level 0, excluded from total_vals)
/// Total assignment: var 1=T, var 3=T, var 4=T (var 2 unassigned)
///
/// This is UNSAT. Conditioning must NOT eliminate C2=(1 ∨ 3).
#[test]
fn test_conditioning_literal_polarity_candidate_check() {
    // 4 variables: var 0 (DIMACS 1), var 1 (DIMACS 2), var 2 (DIMACS 3), var 3 (DIMACS 4)
    let mut db = ClauseArena::new();
    let _c1 = db.add(&[lit(-1), lit(-2), lit(-4)], false); // (¬1 ∨ ¬2 ∨ ¬4)
    let c2 = db.add(&[lit(1), lit(3)], false); // (1 ∨ 3)
    let _c3 = db.add(&[lit(1), lit(-3)], false); // (1 ∨ ¬3)
    let _c4 = db.add(&[lit(-1), lit(-2), lit(4)], false); // (¬1 ∨ ¬2 ∨ 4)

    // Root: var 1 (DIMACS 2) assigned true → unassigned in total_vals.
    // Total_vals: var 0 (1)=T, var 2 (3)=T, var 3 (4)=T, var 1 (2)=unassigned.
    let vals = make_vals(4, &[(1, true), (3, true), (4, true)]);
    // Root_vals includes var 1 (DIMACS 2).
    let root_vals = make_vals(4, &[(1, true), (2, true), (3, true), (4, true)]);
    let frozen = vec![0u32; 4];
    let reason_marks = vec![0u32; 20]; // enough for any clause index

    let mut cond = Conditioning::new(4);
    cond.ensure_num_vars(4);
    let result = cond.condition_round(
        &mut db,
        &vals,
        &root_vals,
        &frozen,
        &reason_marks,
        1,
        1000,
        100_000,
    );

    // The formula is UNSAT. Conditioning must NOT eliminate any clause.
    assert!(
        !result.eliminated.iter().any(|e| e.clause_idx == c2),
        "BUG: C2=(1 ∨ 3) was eliminated by conditioning on an UNSAT formula. \
         This is the literal-polarity candidate check regression. \
         Eliminated {} clauses: {:?}",
        result.eliminated.len(),
        result
            .eliminated
            .iter()
            .map(|e| e.clause_idx)
            .collect::<Vec<_>>()
    );
}
