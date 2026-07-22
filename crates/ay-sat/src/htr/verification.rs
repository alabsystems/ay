// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kani verification harnesses for HTR.

use super::*;

/// Verify that normalize_binary is commutative and produces ordered output.
/// Bounds: Literal values bounded to < 100 for tractable verification.
#[kani::proof]
#[kani::unwind(3)]
fn proof_normalize_binary_commutative() {
    let a_raw: u32 = kani::any();
    let b_raw: u32 = kani::any();
    kani::assume(a_raw < 100); // Bounded for tractability
    kani::assume(b_raw < 100);

    let a = Literal(a_raw);
    let b = Literal(b_raw);

    let (x1, y1) = HTR::normalize_binary(a, b);
    let (x2, y2) = HTR::normalize_binary(b, a);

    // Commutativity
    assert_eq!(x1, x2);
    assert_eq!(y1, y2);

    // Ordering
    assert!(x1 <= y1);
}

/// Verify that normalize_ternary is commutative and produces sorted output.
/// Bounds: Literal values bounded to < 100 for tractable verification.
#[kani::proof]
#[kani::unwind(4)]
fn proof_normalize_ternary_commutative() {
    let a_raw: u32 = kani::any();
    let b_raw: u32 = kani::any();
    let c_raw: u32 = kani::any();
    kani::assume(a_raw < 100);
    kani::assume(b_raw < 100);
    kani::assume(c_raw < 100);

    let a = Literal(a_raw);
    let b = Literal(b_raw);
    let c = Literal(c_raw);

    let t1 = HTR::normalize_ternary(a, b, c);
    let t2 = HTR::normalize_ternary(b, c, a);
    let t3 = HTR::normalize_ternary(c, a, b);
    let t4 = HTR::normalize_ternary(a, c, b);
    let t5 = HTR::normalize_ternary(b, a, c);
    let t6 = HTR::normalize_ternary(c, b, a);

    // All permutations produce the same result
    assert_eq!(t1, t2);
    assert_eq!(t2, t3);
    assert_eq!(t3, t4);
    assert_eq!(t4, t5);
    assert_eq!(t5, t6);

    // Result is sorted
    assert!(t1.0 <= t1.1);
    assert!(t1.1 <= t1.2);
}

/// Verify that HTROccList correctly tracks clause memberships.
/// Bounds: NUM_VARS=2, clause_idx < 100 for tractable verification.
/// Note: Unwind must be >= 2*NUM_VARS+4 for Vec::extend_with + clear() loops.
#[kani::proof]
#[kani::unwind(8)]
fn proof_occ_list_membership() {
    const NUM_VARS: usize = 2;
    let mut occ = HTROccList::new(NUM_VARS);

    let var: u32 = kani::any();
    kani::assume(var < NUM_VARS as u32);

    let lit = Literal::positive(Variable(var));
    let clause = vec![lit];
    let clause_idx: usize = kani::any();
    kani::assume(clause_idx < 100);

    // Initially empty
    assert_eq!(occ.count(lit), 0);

    // Add clause
    occ.add_clause(clause_idx, &clause);

    // Now contains it
    assert_eq!(occ.count(lit), 1);
    assert!(occ.get(lit).contains(&clause_idx));

    // Clear resets
    occ.clear();
    assert_eq!(occ.count(lit), 0);
}

/// Verify that binary_exists correctly detects existing clauses.
/// Bounds: NUM_VARS=2, literal values bounded.
/// Note: Unwind must be >= 2*NUM_VARS+4 for Vec::extend_with + HashSet loops.
#[kani::proof]
#[kani::unwind(8)]
fn proof_binary_exists_detection() {
    let mut htr = HTR::new(2);

    let a_raw: u32 = kani::any();
    let b_raw: u32 = kani::any();
    kani::assume(a_raw < 4); // 2*NUM_VARS = 4 literal indices
    kani::assume(b_raw < 4);
    kani::assume(a_raw != b_raw);

    let a = Literal(a_raw);
    let b = Literal(b_raw);

    // Initially doesn't exist
    assert!(!htr.binary_exists(a, b));

    // Insert
    let key = HTR::normalize_binary(a, b);
    htr.existing_binary.insert(key);

    // Now exists (both orderings)
    assert!(htr.binary_exists(a, b));
    assert!(htr.binary_exists(b, a));
}

/// Verify that try_resolve produces no duplicate literals in resolvent.
/// Uses symbolic inputs for bounded exploration of the resolution space.
/// Note: Unwind must be >= 2*NUM_VARS+4 for Vec::extend_with + resolution loops.
#[kani::proof]
#[kani::unwind(14)]
fn proof_htr_no_duplicate_literals() {
    const NUM_VARS: usize = 5; // Need 5 distinct vars for ternary resolution
    let mut htr = HTR::new(NUM_VARS);

    // Create symbolic ternary clauses with bounded variables
    // C1 = {v0, v1, v2}, C2 = {~v0, v3, v4}
    // where v0 is the pivot variable
    let v0: u32 = kani::any();
    let v1: u32 = kani::any();
    let v2: u32 = kani::any();
    let v3: u32 = kani::any();
    let v4: u32 = kani::any();

    kani::assume(v0 < NUM_VARS as u32);
    kani::assume(v1 < NUM_VARS as u32);
    kani::assume(v2 < NUM_VARS as u32);
    kani::assume(v3 < NUM_VARS as u32);
    kani::assume(v4 < NUM_VARS as u32);

    // Ensure distinct variables within each clause
    kani::assume(v0 != v1 && v0 != v2 && v1 != v2);
    kani::assume(v0 != v3 && v0 != v4 && v3 != v4);

    // Clause 1: {v0, v1, v2}
    let c1 = vec![
        Literal::positive(Variable(v0)),
        Literal::positive(Variable(v1)),
        Literal::positive(Variable(v2)),
    ];

    // Clause 2: {~v0, v3, v4} (negated pivot)
    let c2 = vec![
        Literal::negative(Variable(v0)),
        Literal::positive(Variable(v3)),
        Literal::positive(Variable(v4)),
    ];

    let result = htr.try_resolve(&c1, &c2, Literal::positive(Variable(v0)));

    if let Some(resolvent) = result {
        // Check no duplicates by verifying all literals have unique variables
        let len = resolvent.len();
        for i in 0..len {
            for j in (i + 1)..len {
                assert!(
                    resolvent[i].variable() != resolvent[j].variable(),
                    "Resolvent should not contain duplicate variables"
                );
            }
        }
    }
}

/// Verify that resolving tautologies are correctly rejected.
/// A tautology occurs when resolvent contains both L and ~L for some variable.
/// Note: Unwind must be >= 2*NUM_VARS+4 for Vec::extend_with + resolution loops.
#[kani::proof]
#[kani::unwind(12)]
fn proof_htr_tautology_rejected() {
    const NUM_VARS: usize = 4; // Need 4 distinct vars for tautology test
    let mut htr = HTR::new(NUM_VARS);

    // Force a tautology: C1 = {v0, v1, v2}, C2 = {~v0, ~v1, v3}
    // Resolvent would be {v1, ~v1, v2, v3} - tautology due to v1
    let v0: u32 = kani::any();
    let v1: u32 = kani::any();
    let v2: u32 = kani::any();
    let v3: u32 = kani::any();

    kani::assume(v0 < NUM_VARS as u32);
    kani::assume(v1 < NUM_VARS as u32);
    kani::assume(v2 < NUM_VARS as u32);
    kani::assume(v3 < NUM_VARS as u32);

    // Variables must be distinct
    kani::assume(v0 != v1 && v0 != v2 && v1 != v2);
    kani::assume(v0 != v3 && v1 != v3);
    // v2 and v3 can be equal - doesn't affect the tautology

    // C1 = {v0, v1, v2}
    let c1 = vec![
        Literal::positive(Variable(v0)),
        Literal::positive(Variable(v1)),
        Literal::positive(Variable(v2)),
    ];

    // C2 = {~v0, ~v1, v3} - creates tautology via v1
    let c2 = vec![
        Literal::negative(Variable(v0)),
        Literal::negative(Variable(v1)),
        Literal::positive(Variable(v3)),
    ];

    let result = htr.try_resolve(&c1, &c2, Literal::positive(Variable(v0)));

    // Should be rejected as tautology
    assert!(
        result.is_none(),
        "Tautological resolvent should be rejected"
    );
}

/// Verify resolution soundness: if both parent clauses are satisfied,
/// the resolvent is also satisfied.
///
/// Resolution rule: (C ∨ p) ∧ (D ∨ ¬p) ⊨ (C ∨ D)
///
/// This proves that the resolvent follows from the parent clauses.
/// Note: Unwind must be >= 2*NUM_VARS+4 for Vec::extend_with + resolution loops.
#[kani::proof]
#[kani::unwind(14)]
fn proof_htr_resolution_valid() {
    const NUM_VARS: usize = 5;
    let mut htr = HTR::new(NUM_VARS);

    // Symbolic variable indices for clause construction
    let v0: u32 = kani::any();
    let v1: u32 = kani::any();
    let v2: u32 = kani::any();
    let v3: u32 = kani::any();
    let v4: u32 = kani::any();

    kani::assume(v0 < NUM_VARS as u32);
    kani::assume(v1 < NUM_VARS as u32);
    kani::assume(v2 < NUM_VARS as u32);
    kani::assume(v3 < NUM_VARS as u32);
    kani::assume(v4 < NUM_VARS as u32);

    // Variables must be distinct within each clause
    kani::assume(v0 != v1 && v0 != v2 && v1 != v2);
    kani::assume(v0 != v3 && v0 != v4 && v3 != v4);

    // Symbolic polarities for non-pivot literals (better coverage)
    let pol1: bool = kani::any();
    let pol2: bool = kani::any();
    let pol3: bool = kani::any();
    let pol4: bool = kani::any();

    // v0 is the pivot variable
    // C1 = {p, ±l1, ±l2} where p = v0
    // C2 = {¬p, ±l3, ±l4}
    let c1 = vec![
        Literal::positive(Variable(v0)),
        if pol1 {
            Literal::positive(Variable(v1))
        } else {
            Literal::negative(Variable(v1))
        },
        if pol2 {
            Literal::positive(Variable(v2))
        } else {
            Literal::negative(Variable(v2))
        },
    ];

    let c2 = vec![
        Literal::negative(Variable(v0)),
        if pol3 {
            Literal::positive(Variable(v3))
        } else {
            Literal::negative(Variable(v3))
        },
        if pol4 {
            Literal::positive(Variable(v4))
        } else {
            Literal::negative(Variable(v4))
        },
    ];

    let result = htr.try_resolve(&c1, &c2, Literal::positive(Variable(v0)));

    // Only verify when resolution succeeds (non-tautology, size <= 3)
    if let Some(resolvent) = result {
        // Symbolic assignment for each variable
        let a0: bool = kani::any();
        let a1: bool = kani::any();
        let a2: bool = kani::any();
        let a3: bool = kani::any();
        let a4: bool = kani::any();

        // Helper: evaluate literal under assignment
        let eval_lit = |lit: &Literal, assignment: &[bool; 5]| -> bool {
            let var_idx = lit.variable().0 as usize;
            let val = assignment[var_idx];
            if lit.is_positive() {
                val
            } else {
                !val
            }
        };

        let assignment = [a0, a1, a2, a3, a4];

        // Evaluate C1
        let c1_sat = eval_lit(&c1[0], &assignment)
            || eval_lit(&c1[1], &assignment)
            || eval_lit(&c1[2], &assignment);

        // Evaluate C2
        let c2_sat = eval_lit(&c2[0], &assignment)
            || eval_lit(&c2[1], &assignment)
            || eval_lit(&c2[2], &assignment);

        // Evaluate resolvent
        let mut res_sat = false;
        for lit in &resolvent {
            res_sat = res_sat || eval_lit(lit, &assignment);
        }

        // Resolution soundness: if both parents are satisfied, resolvent is satisfied
        if c1_sat && c2_sat {
            assert!(res_sat, "Resolution soundness: (C1 ∧ C2) ⊨ resolvent");
        }
    }
}
