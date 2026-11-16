// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Gaussian-elimination free-variable basis over the recovered XOR gates
//! (DR-AY-SAT-GE-SUPPORT-20261111).
//!
//! The gate-closure greedy (`closure::greedy_support`) drops a variable only
//! when one gate defines it from variables still in the set, so an XOR cycle
//! (every variable definable from the others, none first) blocks it: on
//! `7db30d12` it computes a 395-variable support where the XOR system — 857
//! equations of rank 857 over 1023 variables — has 166 free variables. This
//! module computes that free set directly: dedupe the clause-driven XOR
//! groups into GF(2) equations, Gauss–Jordan them to reduced row echelon
//! form, and read off each pivot variable's basis expression over the free
//! variables. The expressions re-enter the closure as ordinary definitions
//! (pivot := XOR of its expression variables), so the existing closure
//! verification covers the composed candidate unchanged in shape.
//!
//! The basis feeds a decision-order restriction only (`indep_support.rs`
//! module docs): nothing here can change a verdict or a proof. An
//! inconsistent XOR subsystem (a derived `0 = 1` row) refuses the candidate
//! rather than concluding UNSAT — refutation is the search's job, with its
//! proof obligations intact.
//!
//! References: Soos, Nohl, Castelluccia, "Extending SAT Solvers to
//! Cryptographic Problems" (SAT 2009) for XOR recovery + Gaussian
//! elimination in SAT; the equation semantics are the clause-driven XOR
//! group invariant of `gates/xor.rs` (`⊕ vars = t`, `t = 1` iff the group's
//! gates carry `negated_output`).

use std::collections::BTreeSet;

use super::Definition;
use crate::gates::{Gate, GateType};

/// Largest XOR system (distinct variables) the basis builder will eliminate.
/// The matrix is dense bitsets: memory is rows × ceil(vars/64) words.
const GE_MAX_VARS: usize = 16_384;
/// Largest XOR system (equations after dedupe) the basis builder accepts.
const GE_MAX_EQUATIONS: usize = 32_768;
/// Gauss–Jordan work ceiling in 64-bit word operations (rows² × words is
/// the dense worst case); past it the candidate is refused, not truncated.
const GE_WORK_BUDGET: u128 = 1 << 28;

/// The eliminated basis: free variables, plus one definition per pivot
/// variable expressing it as an XOR of free variables (inputs are variable
/// indices, matching `Definition`'s sign-free reduction — determination is
/// what the closure checks; the parity constant does not affect it).
pub(super) struct GeBasis {
    pub free: Vec<u32>,
    pub exprs: Vec<Definition>,
}

/// Build the GF(2) basis from the recovered gates, or `None` when there is
/// no usable XOR system (no groups, over a size/work cap, or inconsistent).
///
/// Only clause-driven XOR gates are consumed: their inputs are positive
/// literals and the group equation is `⊕ (output, inputs…) = t` with
/// `t = u8::from(negated_output)` (`gates/xor.rs`). A gate with a negated
/// input literal does not have that invariant and is skipped. Equations
/// touching an eliminated variable are dropped (that variable is not
/// decided, so it can neither be free nor be determined at decision time);
/// fixed variables are substituted with `fixed_value` into the right-hand
/// side.
pub(super) fn build_ge_basis(
    gates: &[Gate],
    decidable: &[bool],
    fixed: &[bool],
    fixed_value: impl Fn(u32) -> Option<bool>,
) -> Option<GeBasis> {
    let equations = collect_equations(gates, decidable, fixed, &fixed_value)?;
    if equations.is_empty() || equations.len() > GE_MAX_EQUATIONS {
        return None;
    }
    let mut var_set: BTreeSet<u32> = BTreeSet::new();
    for (vars, _) in &equations {
        var_set.extend(vars.iter().copied());
    }
    if var_set.len() > GE_MAX_VARS {
        return None;
    }
    let cols: Vec<u32> = var_set.into_iter().collect();
    let words = cols.len().div_ceil(64);
    let work = (equations.len() as u128)
        .checked_mul(equations.len() as u128)?
        .checked_mul(words as u128)?;
    if work > GE_WORK_BUDGET {
        return None;
    }
    let mut rows: Vec<Vec<u64>> = Vec::with_capacity(equations.len());
    let mut rhs: Vec<bool> = Vec::with_capacity(equations.len());
    for (vars, r) in &equations {
        let mut row = vec![0u64; words];
        for v in vars {
            let c = cols.binary_search(v).ok()?;
            row[c / 64] |= 1u64 << (c % 64);
        }
        rows.push(row);
        rhs.push(*r);
    }
    let pivot_of_col = gauss_jordan(&mut rows, &mut rhs, cols.len())?;
    read_basis(&rows, &pivot_of_col, &cols)
}

/// Dedupe XOR gates into `(sorted variables, rhs)` equations over decidable
/// variables, substituting fixed variables. `None` on an equation reduced
/// to `0 = 1` (inconsistent subsystem).
fn collect_equations(
    gates: &[Gate],
    decidable: &[bool],
    fixed: &[bool],
    fixed_value: &impl Fn(u32) -> Option<bool>,
) -> Option<Vec<(Vec<u32>, bool)>> {
    let mut set: BTreeSet<(Vec<u32>, bool)> = BTreeSet::new();
    for gate in gates {
        if gate.gate_type != GateType::Xor || gate.inputs.iter().any(|l| !l.is_positive()) {
            continue;
        }
        let mut vars: Vec<u32> = Vec::with_capacity(gate.inputs.len() + 1);
        vars.push(gate.output.0);
        vars.extend(gate.inputs.iter().map(|l| l.variable().0));
        vars.sort_unstable();
        vars.dedup();
        // A variable listed twice in a malformed gate would cancel in GF(2);
        // the extractor emits distinct variables, so treat a repeated
        // variable as a reason to skip rather than to model cancellation.
        if vars.len() != gate.inputs.len() + 1 {
            continue;
        }
        let mut rhs = gate.negated_output;
        let mut live: Vec<u32> = Vec::with_capacity(vars.len());
        let mut usable = true;
        for v in vars {
            let vi = v as usize;
            if fixed.get(vi) == Some(&true) {
                match fixed_value(v) {
                    Some(true) => rhs = !rhs,
                    Some(false) => {}
                    None => {
                        usable = false;
                        break;
                    }
                }
            } else if decidable.get(vi) == Some(&true) {
                live.push(v);
            } else {
                usable = false;
                break;
            }
        }
        if !usable {
            continue;
        }
        if live.is_empty() {
            if rhs {
                return None;
            }
            continue;
        }
        set.insert((live, rhs));
    }
    Some(set.into_iter().collect())
}

/// In-place Gauss–Jordan to reduced row echelon form. Returns the pivot row
/// per column (`None` for free columns), or `None` if a row reduces to the
/// inconsistent `0 = 1`.
fn gauss_jordan(
    rows: &mut [Vec<u64>],
    rhs: &mut [bool],
    ncols: usize,
) -> Option<Vec<Option<usize>>> {
    let mut pivot_of_col: Vec<Option<usize>> = vec![None; ncols];
    let mut r = 0usize;
    for (col, pivot_slot) in pivot_of_col.iter_mut().enumerate() {
        if r >= rows.len() {
            break;
        }
        let word = col / 64;
        let bit = 1u64 << (col % 64);
        let Some(piv) = (r..rows.len()).find(|&i| rows[i][word] & bit != 0) else {
            continue;
        };
        rows.swap(r, piv);
        rhs.swap(r, piv);
        for i in 0..rows.len() {
            if i != r && rows[i][word] & bit != 0 {
                let (lo, hi) = if i < r { (i, r) } else { (r, i) };
                let (left, right) = rows.split_at_mut(hi);
                let (src, dst) = if i < r {
                    (&right[0], &mut left[lo])
                } else {
                    (&left[lo], &mut right[0])
                };
                for (d, s) in dst.iter_mut().zip(src.iter()) {
                    *d ^= *s;
                }
                rhs[i] ^= rhs[r];
            }
        }
        *pivot_slot = Some(r);
        r += 1;
    }
    for (row, &b) in rows.iter().zip(rhs.iter()) {
        if b && row.iter().all(|&w| w == 0) {
            return None;
        }
    }
    Some(pivot_of_col)
}

/// Read free variables and pivot expressions out of the RREF matrix. In
/// RREF a pivot row's set bits are its pivot column plus free columns only,
/// so the expression is the row's bit set minus the pivot.
fn read_basis(rows: &[Vec<u64>], pivot_of_col: &[Option<usize>], cols: &[u32]) -> Option<GeBasis> {
    let mut free: Vec<u32> = Vec::new();
    let mut exprs: Vec<Definition> = Vec::new();
    for (col, piv) in pivot_of_col.iter().enumerate() {
        let var = *cols.get(col)?;
        match *piv {
            None => free.push(var),
            Some(row_idx) => {
                let row = rows.get(row_idx)?;
                let mut inputs: Vec<u32> = Vec::new();
                for (c, &v) in cols.iter().enumerate() {
                    if c != col && row[c / 64] >> (c % 64) & 1 == 1 {
                        inputs.push(v);
                    }
                }
                exprs.push(Definition {
                    output: var,
                    inputs,
                });
            }
        }
    }
    // Determination needs at least one pivot; a rank-0 basis buys nothing.
    if exprs.is_empty() {
        return None;
    }
    Some(GeBasis { free, exprs })
}
