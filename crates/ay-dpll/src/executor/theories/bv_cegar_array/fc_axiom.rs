// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Generate FC axiom clauses for a single pair of selects.
///
/// Encodes: `(idx_a == idx_b) -> (sel_a == sel_b)` as a bit-level diff-XOR
/// encoding over literals already in final CNF numbering, producing SAT-level
/// literals. Fresh diff/eq variables are drawn from `next_var`.
///
/// `stored_idx_bits` are store-chain index bit vectors the lemma
/// must additionally avoid: each contributes its own diff/eq
/// definition and a positive `idx_a == stored` literal on every
/// value clause, restricting the lemma to indices a definition
/// path does not store to.
pub(super) fn generate_fc_axiom_clauses(
    idx_a_bits: &[CnfLit],
    idx_b_bits: &[CnfLit],
    sel_a_bits: &[CnfLit],
    sel_b_bits: &[CnfLit],
    guards: &[i32],
    stored_idx_bits: &[BvBits],
    next_var: &mut u32,
) -> Vec<Vec<SatLiteral>> {
    let mut clauses: Vec<Vec<SatLiteral>> = Vec::new();

    if idx_a_bits.len() != idx_b_bits.len() || idx_a_bits.is_empty() {
        return clauses;
    }
    if sel_a_bits.len() != sel_b_bits.len() || sel_a_bits.is_empty() {
        return clauses;
    }

    let to_sat = |cnf_lit: i32| -> SatLiteral { crate::cnf_lit_to_sat(cnf_lit) };

    // Create diff variables for index bits: diff_k <-> (idx_a_k XOR idx_b_k)
    let diff_vars = diff_vars_for(idx_a_bits, idx_b_bits, next_var, &mut clauses);

    // Stored-index disequalities: eq_s <-> (idx_a == stored_s),
    // built with the same diff/eq pattern; `+eq_s` joins the value
    // clauses below so each reads `(idx == stored_s) ∨ ...` —
    // vacuous exactly at a stored index, forcing elsewhere (the
    // polarity is opposite to the path guards, which enter
    // negated). Definitions stay unguarded.
    let Some(stored_guard_lits) =
        stored_guard_lits_for(idx_a_bits, stored_idx_bits, next_var, &mut clauses)
    else {
        return Vec::new();
    };

    // Value-implication clauses carry the guard literals (negated):
    // with guards the lemma is conditional congruence under the
    // guard atoms (array equalities along a path in the
    // candidate-true equality graph); the diff/eq definitions
    // below define fresh variables and stay unguarded.
    let mut guard_lits: Vec<SatLiteral> = guards.iter().map(|&g| to_sat(-g)).collect();
    guard_lits.extend(stored_guard_lits);
    if diff_vars.is_empty() {
        // Indices are syntactically identical - FC requires values equal.
        for (&os1, &os2) in sel_a_bits.iter().zip(sel_b_bits.iter()) {
            if os1 == os2 {
                continue;
            }
            let mut c1 = guard_lits.clone();
            c1.extend([to_sat(-os1), to_sat(os2)]);
            let mut c2 = guard_lits.clone();
            c2.extend([to_sat(os1), to_sat(-os2)]);
            clauses.push(c1);
            clauses.push(c2);
        }
        return clauses;
    }

    // eq_idx <-> NOT(OR(diff_vars))
    let eq_idx = eq_var_for(&diff_vars, next_var, &mut clauses);

    // FC: eq_idx -> (sel_a_k == sel_b_k)
    for (&os1, &os2) in sel_a_bits.iter().zip(sel_b_bits.iter()) {
        if os1 == os2 {
            continue;
        }
        let mut c1 = guard_lits.clone();
        c1.extend([to_sat(-eq_idx), to_sat(-os1), to_sat(os2)]);
        let mut c2 = guard_lits.clone();
        c2.extend([to_sat(-eq_idx), to_sat(os1), to_sat(-os2)]);
        clauses.push(c1);
        clauses.push(c2);
    }

    clauses
}

/// Fresh diff variables `diff_k <-> (a_k XOR b_k)` for the bit
/// positions whose literals differ, with their defining clauses.
fn diff_vars_for(
    a_bits: &[CnfLit],
    b_bits: &[CnfLit],
    next_var: &mut u32,
    clauses: &mut Vec<Vec<SatLiteral>>,
) -> Vec<i32> {
    let to_sat = |cnf_lit: i32| -> SatLiteral { crate::cnf_lit_to_sat(cnf_lit) };
    let mut diff_vars: Vec<i32> = Vec::with_capacity(a_bits.len());
    for (&ob1, &ob2) in a_bits.iter().zip(b_bits.iter()) {
        // If both bits are the same literal, they're identical - skip
        if ob1 == ob2 {
            continue;
        }
        let diff_var = *next_var as i32;
        *next_var += 1;
        diff_vars.push(diff_var);
        clauses.push(vec![to_sat(-diff_var), to_sat(ob1), to_sat(ob2)]);
        clauses.push(vec![to_sat(-diff_var), to_sat(-ob1), to_sat(-ob2)]);
        clauses.push(vec![to_sat(-ob1), to_sat(ob2), to_sat(diff_var)]);
        clauses.push(vec![to_sat(ob1), to_sat(-ob2), to_sat(diff_var)]);
    }
    diff_vars
}

/// Fresh `eq <-> NOT(OR(diff_vars))` variable with its defining
/// clauses.
fn eq_var_for(diff_vars: &[i32], next_var: &mut u32, clauses: &mut Vec<Vec<SatLiteral>>) -> i32 {
    let to_sat = |cnf_lit: i32| -> SatLiteral { crate::cnf_lit_to_sat(cnf_lit) };
    let eq = *next_var as i32;
    *next_var += 1;
    for &diff_var in diff_vars {
        clauses.push(vec![to_sat(-eq), to_sat(-diff_var)]);
    }
    let mut eq_def: Vec<SatLiteral> = diff_vars.iter().map(|&d| to_sat(d)).collect();
    eq_def.push(to_sat(eq));
    clauses.push(eq_def);
    eq
}

/// One positive `idx_a == stored` literal per avoided stored
/// index (with diff/eq definitions), or `None` on a width
/// mismatch.
fn stored_guard_lits_for(
    idx_a_bits: &[CnfLit],
    stored_idx_bits: &[BvBits],
    next_var: &mut u32,
    clauses: &mut Vec<Vec<SatLiteral>>,
) -> Option<Vec<SatLiteral>> {
    let mut lits = Vec::new();
    for stored in stored_idx_bits {
        if stored.len() != idx_a_bits.len() {
            return None;
        }
        let s_diff_vars = diff_vars_for(idx_a_bits, stored, next_var, clauses);
        let eq_s = eq_var_for(&s_diff_vars, next_var, clauses);
        lits.push(crate::cnf_lit_to_sat(eq_s));
    }
    Some(lits)
}
