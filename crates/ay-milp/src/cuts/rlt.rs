// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Level-1 RLT separation with binary bound factors.

use super::*;

mod plan;
mod support;

use plan::*;
use support::*;

// =============================================================================================
// RLT — REFORMULATION-LINEARIZATION TECHNIQUE, LEVEL 1, WITH A BINARY BOUND FACTOR.
// =============================================================================================

/// The most columns an RLT-eligible row may carry.
///
/// A level-1 RLT cut has at most one term per row column plus the multiplier, so this is the
/// pool's [`crate::bab::MAX_CUT_NNZ`] (200) with headroom. A wider row would separate a cut the
/// pool discards whole, which is separation time spent on nothing.
const RLT_MAX_SUPPORT: usize = 150;

/// The most bound factors one separation pass will try.
///
/// The pass is `O(multipliers × candidate rows × row support)` in exact rationals, so both this
/// and [`RLT_MAX_ROWS_PER_MULT`] are there to keep a set-partitioning model — where the conflict
/// neighbourhood of a binary can be thousands of columns — from turning a cut round into a
/// quadratic scan. Multipliers are taken MOST-FRACTIONAL first, which is where the violation is.
const RLT_MAX_MULTIPLIERS: usize = 96;

/// The most candidate rows one bound factor will be multiplied into.
const RLT_MAX_ROWS_PER_MULT: usize = 64;

/// A bound factor must be fractional by at least this much at `x*` for the product statement to
/// be able to separate. At an integral `x*_i` every RLT cut below degenerates to the row it came
/// from: at `x*_i = 1` the tightest McCormick face reproduces `x_j` exactly and the cut collapses
/// to the row; at `x*_i = 0` it collapses to `0 ≤ 0`. Both are satisfied by `x*`, so the
/// admission floor would drop them anyway — this just avoids deriving them.
const RLT_MIN_FRACTIONALITY: f64 = 1e-6;

type RowsByColumn = Vec<Vec<u32>>;
type VubsBySwitch = std::collections::BTreeMap<usize, Vec<usize>>;

/// Index original rows by column, preserving row and coefficient scan order.
fn rlt_rows_by_column(model: &Model, n_rows: usize) -> RowsByColumn {
    let mut rows_of = vec![Vec::new(); model.num_cols()];
    for r in 0..n_rows {
        for &(c, a) in model.row(Row(r as u32)).0 {
            if a != 0.0 {
                rows_of[c as usize].push(r as u32);
            }
        }
    }
    rows_of
}

/// Fractional free-binary multipliers, most fractional first with a deterministic tie break.
fn rlt_multipliers(model: &Model, x: &[f64], ncols: usize) -> Vec<usize> {
    let mut mults: Vec<_> = (0..ncols)
        .filter(|&i| {
            rlt_free_binary(model, i)
                && x[i] > RLT_MIN_FRACTIONALITY
                && x[i] < 1.0 - RLT_MIN_FRACTIONALITY
        })
        .collect();
    mults.sort_by(|&a, &b| {
        let fa = (x[a] - 0.5).abs();
        let fb = (x[b] - 0.5).abs();
        fa.partial_cmp(&fb)
            .unwrap_or(std::cmp::Ordering::Equal)
            .then(a.cmp(&b))
    });
    mults.truncate(RLT_MAX_MULTIPLIERS);
    mults
}

/// Sorted original rows containing an exact-substitution support for this multiplier.
fn rlt_candidate_rows(
    rows_of: &RowsByColumn,
    vubs: &std::collections::BTreeSet<usize>,
    conflicts: &std::collections::BTreeSet<usize>,
) -> Vec<u32> {
    let mut rows = Vec::new();
    for &j in vubs.iter().chain(conflicts.iter()) {
        if let Some(rs) = rows_of.get(j) {
            rows.extend_from_slice(rs);
        }
    }
    rows.sort_unstable();
    rows.dedup();
    rows.truncate(RLT_MAX_ROWS_PER_MULT);
    rows
}

/// Derive all candidates for one binary bound factor in the original nested-loop order.
fn rlt_for_multiplier(
    model: &Model,
    x: &[f64],
    n_rows: usize,
    rows_of: &RowsByColumn,
    vub_by_switch: &VubsBySwitch,
    multiplier: usize,
    plan: &mut Vec<(usize, f64, RltFace)>,
    candidates: &mut Vec<Cut>,
) {
    let vubs: std::collections::BTreeSet<_> = vub_by_switch
        .get(&multiplier)
        .map(|v| v.iter().copied().collect())
        .unwrap_or_default();
    let conflicts = rlt_conflicts(model, n_rows, rows_of, multiplier);
    if vubs.is_empty() && conflicts.is_empty() {
        return;
    }
    let exact_support = |j: usize| {
        if conflicts.contains(&j) {
            Some(RltExact::Zero)
        } else if vubs.contains(&j) {
            Some(RltExact::Equal)
        } else {
            None
        }
    };
    for row in rlt_candidate_rows(rows_of, &vubs, &conflicts) {
        if sep_wall_expired() {
            break;
        }
        let (coeffs, lb, ub) = model.row(Row(row));
        if coeffs.len() < 2 || coeffs.len() > RLT_MAX_SUPPORT {
            continue;
        }
        for (sign, rhs) in [(1.0f64, ub), (-1.0, lb)] {
            if !rhs.is_finite() {
                continue;
            }
            for branch_one in [true, false] {
                let Some(v) = rlt_plan(
                    model,
                    x,
                    coeffs,
                    sign,
                    rhs,
                    multiplier,
                    branch_one,
                    &exact_support,
                    plan,
                ) else {
                    continue;
                };
                if v <= min_violation() * 0.5 {
                    continue;
                }
                if let Some(cut) =
                    rlt_cut_from_row(model, x, plan, sign, rhs, multiplier, branch_one)
                {
                    candidates.push(cut);
                }
            }
        }
    }
}

/// Separate LEVEL-1 RLT cuts — products of a binary bound factor with a constraint row.
///
/// # What the family says that nothing else here can
///
/// AY's MIR/GMI/cover families all read ONE row at a time and round it. RLT reads a row TOGETHER
/// with a 0/1 switch and says what the row means WHEN THE SWITCH IS ON. On a fixed-charge network
/// that is nominally the whole model: qnet1 has 168 rows of the shape `56·x_j − 56·y ≤ 0`, and
/// multiplying a capacity row by `y` collapses every one of those flows onto `y` with NO
/// relaxation.
///
/// # Measured attribution, before any of this was written (2026-08-04)
///
/// Gurobi at `NodeLimit=1`, `Threads=1`, `Seed=0` on qnet1 (root LP after its presolve 14285.10,
/// optimum 16029.69):
///
/// ```text
///   all cuts on        ObjBound 16028.14   (solved at the root)
///   RelaxLiftCuts=0    ObjBound 16029.69   (solved at the root — relax-and-lift is worth ~0)
///   RLTCuts=0          ObjBound 15552.34   (node limit)
///   Cuts=0             ObjBound 14285.10
/// ```
///
/// Turning RLT OFF costs 476 of root bound out of the 1743 Gurobi's cut loop closes — 27% of it,
/// from 2 cuts of 33. Turning relax-and-lift off costs nothing. That is the measurement that
/// picked this family over the other one the campaign brief named, and it is worth keeping: the
/// brief's own attribution ("RLT + relax-and-lift, 4 cuts of 33") would have justified neither.
///
/// # AND THE MEASURED RESULT: LEVEL-1 RLT DOES NOT REACH qnet1. IT IS TIGHT THERE.
///
/// This family separates NOTHING on qnet1, in every round, and the reason is not a gate, a budget
/// or a bug — it is that every level-1 RLT statement derivable from a single original row and a
/// binary bound factor is SATISFIED AT qnet1's ROOT VERTEX. Instrumented over a full cut loop:
/// (six rounds) ~6,800 candidates were collected and priced, and the LARGEST violation among all
/// of them is `5.4e-13`. Not "small" — zero to within the LP's own residual.
///
/// Two things were ruled out before concluding that.
///
/// * NOT the matrix. Run against Gurobi's OWN presolved qnet1 (360r/1417c, written out and read
///   back) the family still separates nothing, with the root LP identical to eight digits.
/// * NOT the vertex. The loop runs six rounds on qnet1 and the other families move the bound
///   646.8 across them; RLT separates nothing from ANY of the six vertices.
///
/// So whatever Gurobi's `RLTCuts` is worth 476 of bound with, it is not this object. The
/// candidates left, in the order I would try them: products against AGGREGATED rows rather than
/// single rows (which is what `separate_mir_agg` does for the MIR family, and its docstring
/// records the same "single rows saturate" shape), and products of two rows. Level-1 against
/// single rows is now MEASURED to be the wrong one, which is a result worth having written down.
///
/// # What it DOES buy (2026-08-04, `diag root-closure`, 30s, one rep, screen in place)
///
/// ```text
///   p0201      gain 73.073 -> 78.132   (+6.9% of the cut-closed bound), 4 -> 6 cuts
///   khb05250   gain 10816177 -> 10827499  (+0.10%),                    85 -> 107 cuts
///   blend2     gain 0.1107 -> 0.1567   (+41%, of a very small gain)
///   dcmulti    gain 541.100 -> 526.692 (−2.7%: the one root-bound REGRESSION; RLT rows
///              displace better ones in a 400-row pool)
///   13 others  bit-identical
/// ```
///
/// # THE SEEDED CONTROL KILLED THE BEST-LOOKING NUMBER. READ THIS BEFORE QUOTING p0201.
///
/// Unseeded, p0201 goes 394 -> 164 nodes with the family on, which looks like a 2.4x tree. It is
/// not. Handed the optimum (`--emit-witness` then `--seed-solution`, 2 reps, deterministic):
///
/// ```text
///   p0201   seeded  OFF 162 nodes / 0.65s     ON 164 nodes / 0.89s
///   blend2  seeded  OFF 3824 nodes / 1.343s   ON 3354 nodes / 1.326s
/// ```
///
/// p0201's arms CONVERGE, so the 394 -> 164 was incumbent LUCK and the family's real effect
/// there is +2 nodes and +0.22s. blend2 SURVIVES the control at −12% nodes, and is the only
/// genuine tree improvement this family has on the corpus. Do not quote p0201's node ratio.
///
/// # Total wall, which is the verdict
///
/// Net NEGATIVE. blend2 −0.02s (the one real gain), against p0201 +0.22s (seeded), dcmulti
/// +0.09s, khb05250 +0.07s at identical nodes, and pk1 +0.7s of separation across ~30 rounds for
/// ZERO cuts emitted. Everything else is inside the noise with node counts identical. So the
/// honest summary is: correct, tested, cheap enough, one real win, and NOT worth its place by
/// default — which is why it ships OPT-IN, exactly as `separate_lifted_cover` and
/// `separate_lift_project` did before it.
///
/// # Scope of v1
///
/// Bound factors are free binaries that `x*` leaves fractional; rows are ORIGINAL rows (`< n_rows`)
/// in both orientations; products are linearised by the tightest valid McCormick face at `x*`
/// except where the model proves an exact substitution — a conflict (`y = 0`) or a variable upper
/// bound switched by the multiplier (`y = x_j`). At least one exact substitution is required, both
/// because that is where the strength is and because a fully-relaxed product statement is
/// dominated by its own row.
///
/// # `x*` is advice
///
/// The point steers WHICH bound factors are tried, which rows are looked at, and which face each
/// product takes. Validity depends on none of it: every emitted cut is valid for the integer hull
/// at every point of the model. The one thing `x*` decides that matters downstream is ADMISSION,
/// and that is exactly the screen that makes this family self-limiting — a cut implied by the LP
/// relaxation cannot be violated at an `x*` that satisfies the relaxation, so `clears_min_violation`
/// is a complete dominance filter here and no separate subsumption test is needed.
pub(crate) fn separate_rlt(model: &Model, x: &[f64], n_rows: usize, budget: usize) -> Vec<Cut> {
    if budget == 0 || model.has_inexact_coeffs() {
        // The f64 matrix is only a proxy for the exact side store on such a model; the derivation
        // reads the f64s, so it must decline rather than optimise the wrong matrix.
        return Vec::new();
    }
    // SELF-GATE: A WIDE SET-PARTITION MODEL IS THE CLIQUE FAMILY'S, AND THIS ONE IS A TAX ON IT.
    //
    // Measured (2026-08-04, `diag root-closure`, 30s): air03 610.61 -> 395.75, air05 76.29 -> 0
    // (a second rep gave 63.31 — the loop is deadline-driven, so the arm is noisy, but it is
    // never BETTER), mod010 3.167 -> 1.017. `is_wide_set_partition` is true on exactly those three
    // of the corpus's nineteen and false on every instance where the family gains, which is not a
    // coincidence: on a `Σ_{j∈S} x_j = 1` row every pair of members conflicts, so the conflict
    // neighbourhood of a bound factor is thousands of columns, the exact-rational derivation runs
    // over rows hundreds wide, and what comes out is the clique inequality the clique separator
    // already emits — which owns those instances outright (air03's whole 338864.25 -> 340160 root
    // gap is cliques). The 2.0s per round it spent on air05 came straight out of the 15% cut
    // share, so the loop simply ran fewer rounds. Declining is not a heuristic here; it is the
    // family admitting it has nothing to say that is not already said better.
    if is_wide_set_partition(model) {
        return Vec::new();
    }
    let n_rows = n_rows.min(model.num_rows());
    let ncols = model.num_cols().min(x.len());
    if n_rows == 0 || ncols == 0 {
        return Vec::new();
    }

    // Column → the original rows that contain it. Needed both to find candidate rows and to bound
    // the conflict scan.
    let rows_of = rlt_rows_by_column(model, n_rows);
    let vub_by_switch = rlt_vub_by_switch(model, n_rows);
    let mults = rlt_multipliers(model, x, ncols);
    if mults.is_empty() {
        return Vec::new();
    }

    let mut cand: Vec<Cut> = Vec::new();
    let mut plan: Vec<(usize, f64, RltFace)> = Vec::new();
    for &i in &mults {
        // The round's shared wall budget, if the caller armed one. Checked per bound factor and
        // per candidate row: an unbudgeted family pushes the round past the clamp GMI's own
        // deadline is computed from, and GMI then gets a deadline already in the past and returns
        // nothing — the failure `sep_wall_scope` exists to document.
        if sep_wall_expired() {
            break;
        }
        rlt_for_multiplier(
            model,
            x,
            n_rows,
            &rows_of,
            &vub_by_switch,
            i,
            &mut plan,
            &mut cand,
        );
    }

    // Rank by EFFICACY, not raw violation — a cut multiplied through by ten says the same thing —
    // and cap inside the separator: `select_cuts` is the identity at the shipped defaults, so
    // nothing downstream will do it, and a family that floods the pool evicts the rows that were
    // carrying the bound.
    cand.sort_by(|a, b| {
        efficacy(b, x)
            .partial_cmp(&efficacy(a, x))
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    cand.truncate(budget);
    cand
}

#[cfg(test)]
mod tests;
