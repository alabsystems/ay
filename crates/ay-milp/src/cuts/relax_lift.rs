// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact mixed-row relax-and-lift cover separation.

use super::*;

// ---------------------------------------------------------------------------------------------
// RELAX-AND-LIFT — a mixed-row cover separated on a FACE and lifted off it, in exact rationals.
// ---------------------------------------------------------------------------------------------

/// The widest range `U_k = u_k − l_k` a general integer may have and still be LIFTED rather than
/// dropped. The lifting loop evaluates `Φ` once per value of `k`, so the cost is linear in this;
/// the odometer inside `Φ` is what actually explodes and [`RL_LIFT_SPACE_CAP`] governs that.
const RL_MAX_GEN_RANGE: i64 = 16;

/// The most general integers a single row may carry into the lifting. `Φ` enumerates every
/// multiplicity vector of the already-lifted set, so this bounds the odometer's DEPTH.
const RL_MAX_GENS: usize = 6;

/// `Π(U_k + 1)` over the lifted general integers — the odometer's SIZE — refused above this.
/// Sound either way: refusing a row only forgoes a cut.
const RL_LIFT_SPACE_CAP: u128 = 256;

/// The most cover members a relax-and-lift cut may carry. Keeps the emitted row well inside
/// [`crate::bab::MAX_CUT_NNZ`] and keeps `Φ`'s prefix scan cheap.
const RL_MAX_COVER: usize = 64;

/// The most `Φ` evaluations one row may spend before the derivation is abandoned.
const RL_WORK_CAP: u64 = 20_000;

/// Whether the relax-and-lift family is armed. DEFAULT OFF — see the measurement note on
/// [`separate_relax_lift`].
///
/// CACHED, and registered in [`prime_env`], because `the_live_env_read_surface_does_not_grow`
/// ratchets on uncached `getenv` calls reachable from the solve path: a lazy read races a
/// concurrent `set_var`, which is why `set_var` is `unsafe` in edition 2024. Caching is safe for
/// THIS name specifically — it is a family gate, not an arm selector, and nothing flips it inside
/// one process (the family's own tests call [`separate_relax_lift`] directly and never touch the
/// gate), so there is no `OnceLock`-latching hazard of the kind the ledger's arm-selector list
/// documents.
pub(crate) fn relax_lift_enabled() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| crate::tune::caller_flag(crate::tune::Knob::RelaxLift) == Some(true))
}

/// RELAX-AND-LIFT: fix the columns a 0/1 cover cannot talk about, separate a cover on the residual
/// knapsack, then LIFT the fixed columns back until the inequality is valid off its face.
///
/// # Why this exists when [`separate_lifted_cover`] already lifts general integers
///
/// [`lifted_cover_from_row`] implements the same *lifting kernel* and then declines almost every
/// real row before reaching it. Its guards are, verbatim: `if a <= 0.0 { return None }`, then
/// `if lo != 0.0 || !up.is_finite() { return None }`, then `ColKind::Continuous => return None`.
/// Measured on the four instances the 2026-08-04 report calls root-bound-bound — qnet1, gt2,
/// p0201, khb05250 — `--lifted-cover` changes `diag root-closure` by NOTHING: identical
/// `bound_cut` and identical `cuts=` to the digit on all four. Every row is refused at a guard.
/// qnet1's characteristic rows are `56·x_i − 56·x_j ≤ 0` (negative coefficient); khb05250 is 1326
/// continuous columns against 24 binaries; p0201 is pure binary.
///
/// This separator is the same derivation with the guards replaced by a VIEW TRANSFORM:
///
/// 1. **View.** Put the row as `Σ_j w_j·v_j ≤ c` with every `w_j > 0` and every `v_j ≥ 0`, by
///    shifting `v_j = x_j − l_j` where `a_j > 0` and COMPLEMENTING `v_j = u_j − x_j` where
///    `a_j < 0`. Both need the relevant bound finite; a column that has neither is refused.
/// 2. **Classify.** `v_j ∈ {0,1}` (integral column, *integral* bounds, range exactly 1) is a cover
///    candidate; an integral column with integral bounds and range `2..=`[`RL_MAX_GEN_RANGE`] is a
///    general integer to be lifted; EVERYTHING ELSE — continuous, wide, fractional-bounded,
///    negative-lower-bounded — is DROPPED at `v = 0`, which is free because `w_j·v_j ≥ 0`.
/// 3. **Relax.** Fix each general integer at the face the LP point stands on,
///    `t*_k = clamp(⌊v*_k⌋, 0, U_k)`, leaving residual capacity `c' = c − Σ_k w_k·t*_k ≥ 0`.
///    Fixing at ZERO instead is what makes the plain-cover families slack here: it hands the
///    integers' share of the capacity back to the binaries and nothing violates a cover
///    (`separate_cover_view`'s rout note records the same trap).
/// 4. **Separate.** Greedy cover `C` against `c'`, cheapest `1 − v*` PER UNIT WEIGHT first (the
///    ranking `separate_lifted_cover` paid for), re-verified `Σ_C w_j > c'` in `BigRational`.
///    On the face, `Σ_{j∈C} v_j ≤ |C| − 1 =: ρ`.
/// 5. **Lift.** Sequentially, in a deterministic order, give each general integer the coefficient
///    that makes the inequality valid off the face.
///
/// # The lifting, and why it is valid
///
/// Write `Φ_L(s)` for the most `Σ_{j∈C} v_j + Σ_{i∈L} γ_i·(v_i − t*_i)` can be worth when the
/// cover members and the already-lifted integers `L` together have budget `s`:
///
/// ```text
/// Φ_L(s) = max { Σ_C v_j + Σ_L γ_i·(v_i − t*_i) : Σ_C w_j·v_j + Σ_L w_i·v_i ≤ s,
///                v_C ∈ {0,1}^C, v_i ∈ {0..U_i} }        (−∞ when s < 0)
/// ```
///
/// The invariant carried through the induction is `Φ_L(S_L) ≤ ρ`, where
/// `S_L = c − Σ_{m ∉ L} w_m·t*_m` is the budget on the face that still fixes the UNLIFTED
/// integers. The base case is the cover: `Φ_∅(c')` is a max-CARDINALITY knapsack, and `C`
/// overflows `c'`, so it is at most `|C| − 1 = ρ`.
///
/// Lifting `k` means choosing `γ_k` with, for every `t ∈ {0..U_k}`,
///
/// ```text
/// Φ_L(S_L + w_k·(t*_k − t)) + γ_k·(t − t*_k) ≤ ρ
/// ```
///
/// which is exactly `Φ_{L∪{k}}(S_{L∪{k}}) ≤ ρ`, the invariant one step on. At `t = t*_k` it is the
/// invariant itself. Otherwise it is a two-sided WINDOW on `γ_k`:
///
/// ```text
/// t > t*_k  (eats capacity)      γ_k ≤ (ρ − Φ_L(S_L − w_k·z)) / z,   z = t − t*_k   [UPPER]
/// t < t*_k  (hands capacity back) γ_k ≥ (Φ_L(S_L + w_k·z) − ρ) / z,  z = t*_k − t   [LOWER]
/// ```
///
/// Take the largest admissible `γ_k` — at the LP point `v*_k − t*_k ≥ 0`, so larger is deeper —
/// and if the window is EMPTY, ABANDON the cut. A cut valid only on its face is not valid, and
/// that check is the one an over-eager implementation drops. After the last lift `L = G` and the
/// face is the whole model, so the inequality
///
/// ```text
/// Σ_{j∈C} v_j + Σ_{k∈G} γ_k·(v_k − t*_k) ≤ ρ
/// ```
///
/// is valid for the model, and un-complementing gives the emitted row.
///
/// # Exactness
///
/// Every weight, capacity, reference product, `Φ` value and `γ` is a `BigRational`. The `Φ` inner
/// maximum is EXACT, not an upper bound: over `C` the coefficients are all 1, so the most items
/// that fit is the ascending-weight prefix (`rl_max_cardinality`, a binary search on a prefix-sum
/// table), and over `L` every multiplicity vector is enumerated. `rl_phi_matches_full_enumeration`
/// pins that against brute force. Emission is [`emit_le_cut`], which rounds coefficients DOWN and
/// the right-hand side UP — a relaxation on `x ≥ 0`, and it refuses any column with `lo < 0`, so a
/// complemented column whose model bound is negative fails closed rather than shipping.
///
/// # Guard
///
/// `relax_lift_cuts_never_remove_an_integer_point` builds single-row mixed models — both
/// orientations, both coefficient signs, general integers, continuous columns, and DELIBERATELY
/// FRACTIONAL bounds — enumerates every integer point of the integral box, admits a point when a
/// feasible continuous completion exists (exact on one row: the activity sweeps an interval), and
/// asserts every emitted cut holds. It has the mandatory `fired > 0` positive control.
///
/// ⚠ MUTATION-CHECKED, four ways. A guard that cannot fail is not a guard, so each of the four
/// steps the validity actually rests on was deliberately broken and the guard re-run. All four
/// FAIL, each with a concrete counterexample from the seeded stream; the shipped code passes.
///
/// | mutation | first failing case | the point it deleted |
/// |---|---|---|
/// | `γ_k` → `γ_k + 1` (lift one step too greedy) | 9 | `[1,0,0,1]`, activity `0.5` > ub `0` |
/// | empty-window abandon (`gamma < lo_g`) removed | 4 | activity `5` > ub `4` |
/// | ship the face seed UNLIFTED (`γ_k := 0`, hazard H11) | 4 | activity `3` > ub `2` |
/// | integrality read off the column KIND, not the BOUND | 134 | an `Integer` column boxed `[1/2, 5/2]`, activity `5` > ub `4.5` |
///
/// The last one is the bug this campaign already shipped once in MIR's `Sub`, reproduced here on
/// a different family: it is caught ONLY because the generator draws fractional bounds.
///
/// # ⚠⚠ MEASURED NEGATIVE. The family is correct, it reaches the rows the old one refused, and it
/// # separates almost nothing — and the census says why, which is the part worth keeping.
///
/// `diag root-closure`, 60s, one thread, `the root-closure-presolve knob`, armed vs not:
///
/// | instance | `bound_cut` off | `bound_cut` on | cuts off → on |
/// |---|---|---|---|
/// | qnet1 | 14920.917796016 | **14850.053779304** | 19 → 19 |
/// | gen | 112302.74294762 | 112302.74294762 | 22 → 26 |
/// | gt2, p0201, khb05250, rout, blend2, dcmulti, misc07, mas76, pk1, flugpl | — | IDENTICAL to the digit | unchanged |
///
/// It fires ONCE on qnet1 (round 0) and four times on gen. gen's four cuts move the bound by
/// ZERO. qnet1's single cut moves it by −70.86 — and that is NOT the cut being invalid or weak:
/// the arms agree to the digit at rounds 0, 1 and 3, and diverge at 2, 4 and 5, because one extra
/// row in round 0 changes the LP VERTEX and every subsequent Gomory cut is read off a different
/// tableau. The root loop is deterministic (the unarmed arm reproduces to the digit), so this is a
/// deterministic CHAOTIC trajectory difference on one instance, not a measurement of the family.
///
/// # Why it separates nothing — the decline census, 10 instances, every row-orientation of every
/// # round
///
/// | instance | reached | `bins < 2` | no cover | face cover NOT violated | **no general integer** | violated |
/// |---|---|---|---|---|---|---|
/// | qnet1 | 3480 | 552 | 253 | 2625 | **2520** | 2 |
/// | p0201 | 266 | 0 | 0 | 260 | **266** | 6 |
/// | misc07 | 494 | 0 | 4 | 490 | **494** | 0 |
/// | khb05250 | 1078 | **1078** | 0 | 0 | 0 | 0 |
/// | gt2 | 174 | 90 | 0 | 12 | 12 | 0 |
/// | gen | 984 | 722 | 238 | 11 | 262 | 13 |
/// | rout | 164 | 0 | 60 | 98 | 28 | 0 |
/// | blend2 | 338 | 118 | 216 | 4 | 220 | 0 |
/// | dcmulti | 486 | 444 | 0 | 42 | 42 | 0 |
/// | mas76 | 24 | 0 | 22 | 2 | 24 | 0 |
///
/// Two walls, and NEITHER is a tuning knob:
///
///   * **NO GENERAL INTEGER TO LIFT.** On qnet1 2520 of 3480 row-orientations, on p0201 and
///     misc07 ALL of them. With `G = ∅` the derivation degenerates to a plain cover over the
///     binaries with the continuous columns dropped — there is no lifting step, and
///     `separate_cover_view` already owns that inequality on the rows it accepts. The
///     relax-and-lift-specific content only exists on a MIXED binary + small-general-integer
///     knapsack row, and this corpus barely has one.
///   * **THE FACE COVER IS NOT VIOLATED.** Where the structure IS present the LP point still does
///     not break a cover on it: qnet1 2625, misc07 490, p0201 260. This is the SAME wall
///     `separate_cover_view`'s rout note and `separate_lifted_cover`'s rout note each recorded on
///     one instance. It now has ten.
///
/// **The caps are not what binds, and that was checked rather than assumed.** Re-running the whole
/// census with [`RL_MAX_GEN_RANGE`] 16 → 200, [`RL_LIFT_SPACE_CAP`] 256 → 200 000 and
/// [`RL_WORK_CAP`] 20 000 → 50 000 000 — 12× to 800× — leaves qnet1 at 2 violated, gt2 at 0 and
/// every other instance's census unchanged to the unit. Only the `liftspace` refusals move (qnet1
/// 48 → 12), and they turn into `no cover`, not into cuts.
///
/// # The full-solve corpus, and the node claim the SEEDED CONTROL took away from me
///
/// 17 instances, `examples/mps_solve`, 60s, one thread, arms INTERLEAVED, 3 reps, medians:
/// **2 better / 10 neutral / 5 worse, TOTAL WALL +10.585s (155.731 → 166.315)**. But the
/// distribution is almost entirely noise, and the node column says so: khb05250, misc07, pk1 and
/// flugpl are all "worse" on wall with BYTE-IDENTICAL node counts, i.e. the search never changed
/// and the box was loaded (30 concurrent worktrees, load average 14–42 during this run). blend2
/// and misc07 move run-to-run in BOTH arms (blend2 8230 nodes in rep 1, 13891 in rep 2, same arm),
/// so neither can carry a claim. qiu times out in both arms.
///
/// qnet1 is the only instance where anything real happens, and it is deterministic: **850 nodes
/// OFF and 2898 nodes ON in all three reps**, wall 4.87 → 8.61s.
///
/// ⚠ AND THE 3.4× NODE BLOW-UP IS INCUMBENT LUCK, NOT THE FAMILY. Per the mandatory seeded
/// control — `--emit-witness w.sol --witness-format sol`, then both arms re-run with
/// `--seed-solution w.sol`:
///
/// | qnet1 | nodes | wall |
/// |---|---|---|
/// | unseeded OFF | 850 | 4.87 s |
/// | unseeded ON | 2898 | 8.61 s |
/// | **seeded OFF** | **1467** | **6.02 s** |
/// | **seeded ON** | **1381** | **7.10 s** |
///
/// With the incumbent handed to both arms the node gap does not merely shrink, it INVERTS: the
/// armed arm explores 5.9% FEWER nodes. So the family's cut does not make qnet1's tree worse —
/// the unarmed run simply got luckier with its first incumbent, which is the same trap gt2's
/// 56 670-vs-46 nodes turned out to be. What the seeded arms DO show is a real and reproducible
/// **wall** cost of +18% on FEWER nodes (2 reps each, 6.02/6.01 vs 7.07/7.13): one extra row is
/// carried by every node LP for the whole solve, and on qnet1 that outweighs the nodes it saves.
/// That is the family's honest price, and it is charged for a root bound that got WORSE.
///
/// So the family ships DEFAULT-OFF (`the relax-lift knob`), like `separate_lifted_cover` and
/// `separate_implied_bound` before it, and for the same reason: it is a correct, guarded,
/// exactly-derived separator whose value is that the negative is now re-derivable in one command.
/// Anyone tempted to build a mixed-row cover family again should read the census first.
pub(crate) fn separate_relax_lift(
    model: &Model,
    x: &[f64],
    n_rows: usize,
    budget: usize,
) -> Vec<Cut> {
    // An inexact model's f64 matrix is a PROXY for the exact side store; deriving from it would be
    // deriving from the wrong row (`separate_covering_modk` and `root_probe` decline the same way).
    if model.has_inexact_coeffs() {
        return Vec::new();
    }
    let mut cand: Vec<(f64, Cut)> = Vec::new();
    for r in 0..n_rows.min(model.num_rows()) {
        let (coeffs, lb, ub) = model.row(Row(r as u32));
        if coeffs.len() < 3 {
            continue;
        }
        // BOTH ORIENTATIONS. `Σ a·x ≥ lb` is the row `Σ (−a)·x ≤ −lb`; derive once for `≤` and
        // negate the ROW, never the finished cut.
        if ub.is_finite() {
            if let Some(c) = relax_lift_from_row(model, x, coeffs, ub, false) {
                cand.push((efficacy(&c, x), c));
            }
        }
        if lb.is_finite() {
            if let Some(c) = relax_lift_from_row(model, x, coeffs, -lb, true) {
                cand.push((efficacy(&c, x), c));
            }
        }
    }
    // `select_cuts` is the identity at the shipped defaults, so the family caps ITSELF.
    cand.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap_or(std::cmp::Ordering::Equal));
    cand.truncate(budget);
    cand.into_iter().map(|(_, c)| c).collect()
}

mod row;

use row::relax_lift_from_row;
#[cfg(test)]
use row::{rl_phi, RlLifted};

#[cfg(test)]
mod tests;
