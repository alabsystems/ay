// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! OPT-LIN optimality certificates for the LAYERED GROUP-DIVISION family —
//! the `linearized_pebbling_opt_layeredfan_{down,up}` CoreGuidedPB instances —
//! where a per-group DIVISION floor propagates through a DAG of groups and
//! `ceil(LP*) < optimum` throughout the corpus family.
//!
//! # The family
//!
//! The declared variables are PARTITIONED into groups `G_r`, one per row, and
//! every row reads
//!
//! ```text
//! 2·Σ(G_r) - Σ_{p ∈ preds(r)} Σ(G_p)  >=  d_r        (Σ(G) = Σ_{v∈G} x_v)
//! min  Σ_v x_v                                        (unit, every variable)
//! ```
//!
//! with each row's negative side the EXACT disjoint union of other rows'
//! groups (`preds`), acyclically. In `linearized_pebbling` the groups are the
//! `a`-bit unary registers of one pebble each, sources carry `d = a - 1` (odd),
//! and internal rows carry `d = 0` with exactly two predecessor pebbles.
//!
//! # Why no LP-dual floor can ever fire here
//!
//! Per group the LP can only support `Σ(G_r) >= g(r)` with
//! `g(r) = (d_r + Σ_p g(p)) / 2` — no rounding anywhere. On
//! `layeredfan_down_r7_c14_a4` that is `g = 3/2` for every one of the 189
//! groups: sources from `2Σ >= 3`, internal rows by induction, and the uniform
//! point `x = 3/8` is FEASIBLE and makes every row tight, so
//! `LP* = 189 · 3/2 = 567/2` exactly, pinned from both sides with no float in
//! the loop. `ceil(LP*) = 284` against optimum `378`: weak duality caps every
//! dual floor `94` short, permanently. This is the SEVENTH family to die on
//! that inference.
//!
//! # The mathematics, in one paragraph
//!
//! Integrally, each group's floor rounds: `f(r) = ceil((d_r + Σ_p f(p)) / 2)`.
//! One `pol` line per group, in topological order, derives `Σ(G_r) >= f(r)` —
//! add the (already derived) predecessor floors to the row, then divide by 2:
//!
//! ```text
//! pol  c_{p1} c_{p2} + … + row_r + 2 d ;
//! ```
//!
//! The predecessor sums cancel EXACTLY (their union is the row's negative side,
//! coefficient `-1` each), leaving `2·Σ(G_r) >= d_r + Σ_p f(p)`, and `d`
//! rounds the degree up — the half the LP must carry forever is re-rounded at
//! EVERY group, so the gap grows with depth instead of averaging away. The
//! final `pol` adds the group floors; the groups partition the variables, so
//! the sum IS the unit objective row at degree `Σ_r f(r)`:
//!
//! ```text
//! pol  c_1 c_2 + c_3 + … + ;      ->   Σ_v x_v  >=  Σ_r f(r)
//! ```
//!
//! Prototype, measured against the PINNED checker before this port existed:
//! all TEN corpus family members (`down` r7..r26, `up` r17..r33, arities 4, 5
//! and 6) emit `s VERIFIED BOUNDS f <= obj <= f` with `f` = the incumbent the
//! search already held at the census budget (378 and 722 on the two census
//! misses), and seven adversarial mutations of the prototype emission (wrong
//! divisor, floor+1, dropped group, wrong predecessor, flipped witness
//! literal, understated upper bound, raw-row-for-derived swap) are all
//! REJECTED, exit 1.
//!
//! # Fail-closed, in four independent layers
//!
//! 1. **O(1) pre-gate** ([`header_candidate`]): the objective must have
//!    exactly one term per declared variable (three integer comparisons —
//!    the same gate as `odd_cycle_cover`, whose family this one can never
//!    collide with because its rows carry coefficient `2`), plus an O(1)
//!    first-row probe: a leading coefficient that is not `+2` declines before
//!    the row-id map is built.
//! 2. **Total structural recovery** ([`recover`]): EVERY row must be
//!    `+2` over its group and `-1` over an exact disjoint union of other
//!    groups, EVERY declared variable must be in exactly one group and carry
//!    exactly one unit objective term, the predecessor graph must be acyclic,
//!    and a deterministic row budget caps the work. Anything else declines;
//!    there is deliberately no "mostly matched" path.
//! 3. **Independent incumbent re-verification**: feasible against the
//!    ORIGINAL rows, objective exactly `optimum`, and the derived floor
//!    `Σ_r f(r)` must EQUAL `optimum` — a genuine but weaker floor is
//!    withheld rather than published, because this rung's contract is
//!    OPTIMALITY.
//! 4. **Self-check of the emitted BYTES**
//!    ([`super::cp_replay::self_check_pol_only_objective_floor`]): the
//!    finished text is parsed back and replayed under VeriPB's
//!    normalized-literal semantics for `d`. The replay rebuilds every row from
//!    the instance, so a mis-cited id, a mis-ordered operand or a wrong
//!    divisor cannot survive it.
//!
//! SOUNDNESS: this module returns proof *text* only, and it is not trusted
//! until the external PINNED VeriPB re-checks it (verify-before-claim). A
//! `None` is a withheld certificate and never changes the reported status.

#[cfg(test)]
mod tests;

use std::fmt::Write as _;

use super::cp_replay::{ceil_div, self_check_pol_only_objective_floor as self_check};
use super::{evaluate_linear_objective, format_assignment, incumbent_is_feasible};
use crate::proof::steps::{ConstraintId, ProofStep};
use crate::proof::veripb::{veripb_input_constraint_count, veripb_input_row_ids, VeriPbWriter};
use crate::types::{PbInstance, PbRel};

/// Deterministic count budget: more rows than this declines rather than emit
/// an unbounded proof. The corpus family tops out at 2,678 rows; the cap is
/// generous, not a tuning knob, and it bounds the emitted bytes by a constant
/// multiple of the input (each group appears in at most one `pol` per user
/// plus the final sum).
const MAX_ROWS: usize = 1 << 20;

// ---------------------------------------------------------------------------
// Layer 1: the O(1) pre-gate.
// ---------------------------------------------------------------------------

/// Candidacy from the header integers alone: a unit objective term for every
/// declared variable (checked structurally in layer 2) and at least one row.
///
/// Three comparisons, no loop, no allocation. This is intentionally the SAME
/// gate as `odd_cycle_cover`'s: the families cannot collide (its rows are
/// `+1 x_u +1 x_v >= 1`; ours open with a `+2`), and each module's O(1)
/// first-constraint probe is what separates them before any O(n) work.
fn header_candidate(num_vars: u64, num_constraints: u64, num_objective: u64) -> bool {
    num_vars >= 1 && num_constraints >= 1 && num_objective == num_vars
}

// ---------------------------------------------------------------------------
// Layer 2: total, fail-closed structure recovery.
// ---------------------------------------------------------------------------

/// The recovered DAG of groups, with everything the emitter cites.
struct GroupDag {
    /// `group_vars[r]` — the variables (1-based OPB ids) with coefficient `+2`
    /// in row `r`, i.e. group `G_r`. The groups partition all declared vars.
    group_vars: Vec<Vec<u32>>,
    /// `preds[r]` — the rows whose groups' disjoint union is row `r`'s
    /// negative side, in first-appearance order (deterministic emission).
    preds: Vec<Vec<u32>>,
    /// VeriPB input row id of row `r`, from the shared id map.
    row_ids: Vec<u64>,
    /// The integral floor `f(r) = ceil((d_r + Σ_p f(p)) / 2)`, exact `i128`.
    floors: Vec<i128>,
    /// Rows in the topological order the floors were computed in.
    topo: Vec<u32>,
}

impl GroupDag {
    fn total_floor(&self) -> Option<i128> {
        let mut total: i128 = 0;
        for &f in &self.floors {
            total = total.checked_add(f)?;
        }
        Some(total)
    }
}

/// Recovers the group DAG, accounting for EVERY row and EVERY variable.
///
/// Declines on the first thing it cannot explain. There is deliberately no
/// "mostly matched" path: a partial match is exactly the state in which an
/// emitter would write a derivation over rows it has misread.
fn recover(instance: &PbInstance) -> Option<GroupDag> {
    let objective = instance.objective.as_ref()?;
    if !header_candidate(
        u64::from(instance.num_vars),
        instance.constraints.len() as u64,
        objective.terms.len() as u64,
    ) {
        return None;
    }
    let order = usize::try_from(instance.num_vars).ok()?;
    let num_rows = instance.constraints.len();
    if num_rows > MAX_ROWS {
        return None;
    }

    // O(1) first-row probe BEFORE the O(#constraint) row-id map is built,
    // for `odd_cycle_cover`'s measured reason: the header gate is not very
    // selective, and the first coefficient is the cheapest disambiguator.
    // Every row of this family leads with a `+2` group term (the normalized
    // printer emits positive terms first); anything else declines here.
    {
        let first = instance.constraints.first()?;
        if first.rel != PbRel::Ge {
            return None;
        }
        let lead = first.terms.first()?;
        if lead.coeff != 2 {
            return None;
        }
    }

    // Pass 1: split every row into its `+2` group and `-1` negative side,
    // and assign every variable its owning group. VeriPB row ids come from
    // the shared map, never from `index + 1` (an `=` row shifts every id
    // after it; this family has none, but the map is still what is used).
    let ids = veripb_input_row_ids(instance).ok()?;
    let mut group_vars: Vec<Vec<u32>> = Vec::with_capacity(num_rows);
    let mut neg_vars: Vec<Vec<u32>> = Vec::with_capacity(num_rows);
    let mut row_ids: Vec<u64> = Vec::with_capacity(num_rows);
    let mut owner: Vec<Option<u32>> = vec![None; order];
    for (index, constraint) in instance.constraints.iter().enumerate() {
        if constraint.rel != PbRel::Ge {
            return None;
        }
        let mut group = Vec::new();
        let mut neg = Vec::new();
        for term in &constraint.terms {
            let [lit] = term.lits.as_slice() else {
                return None;
            };
            if lit.negated {
                return None;
            }
            let slot = usize::try_from(lit.var.checked_sub(1)?).ok()?;
            if slot >= order {
                return None;
            }
            match term.coeff {
                2 => {
                    if owner[slot].is_some() {
                        return None; // in two groups: not a partition
                    }
                    owner[slot] = Some(u32::try_from(index).ok()?);
                    group.push(lit.var);
                }
                -1 => neg.push(lit.var),
                _ => return None,
            }
        }
        if group.is_empty() {
            return None;
        }
        group_vars.push(group);
        neg_vars.push(neg);
        row_ids.push(ids.get(index)?.get());
    }
    if owner.iter().any(Option::is_none) {
        return None; // a declared variable in no group: not a partition
    }

    // The objective is a unit payment on every variable, each exactly once —
    // this is what makes the final combination the OBJECTIVE row.
    let mut paid = vec![false; order];
    for term in &objective.terms {
        let [lit] = term.lits.as_slice() else {
            return None;
        };
        if lit.negated || term.coeff != 1 {
            return None;
        }
        let slot = usize::try_from(lit.var.checked_sub(1)?).ok()?;
        if slot >= order || paid[slot] {
            return None;
        }
        paid[slot] = true;
    }
    if paid.iter().any(|&seen| !seen) {
        return None;
    }

    // Pass 2: each row's negative side must be the EXACT disjoint union of
    // other rows' groups — that is what makes the predecessor sums cancel to
    // nothing in the emitted `pol`, so a partial overlap would emit a row
    // WEAKER than the self-check expects. `counted` tracks how many of each
    // candidate predecessor's variables actually appeared; anything short,
    // repeated, unowned or self-referential declines.
    let mut preds: Vec<Vec<u32>> = Vec::with_capacity(num_rows);
    let mut counted: Vec<u32> = vec![0; num_rows];
    let mut seen_var: Vec<bool> = vec![false; order];
    for (index, neg) in neg_vars.iter().enumerate() {
        let mut local: Vec<u32> = Vec::new();
        for &var in neg {
            let slot = usize::try_from(var - 1).ok()?;
            if seen_var[slot] {
                // A duplicated `-1 x_v` would let the occurrence COUNT match a
                // predecessor's size while the union is wrong — the row would
                // really carry `-2·x_v` and the predecessor sum would not
                // cancel. Refuse at recovery, not at replay.
                for &v in neg {
                    seen_var[usize::try_from(v - 1).ok()?] = false;
                }
                return None;
            }
            seen_var[slot] = true;
            let p = owner[slot]?; // checked total above
            if p as usize == index {
                return None; // self-loop
            }
            if counted[p as usize] == 0 {
                local.push(p);
            }
            counted[p as usize] = counted[p as usize].checked_add(1)?;
        }
        for &var in neg {
            seen_var[usize::try_from(var - 1).ok()?] = false;
        }
        for &p in &local {
            // Exactness: every variable of the predecessor group, exactly once.
            if counted[p as usize] as usize != group_vars[p as usize].len() {
                return None;
            }
            counted[p as usize] = 0;
        }
        preds.push(local);
    }

    // Topological order over `preds` (Kahn); a cycle declines. The floor
    // recurrence is only sound on a DAG.
    let mut remaining: Vec<u32> = preds
        .iter()
        .map(|p| u32::try_from(p.len()).unwrap_or(u32::MAX))
        .collect();
    let mut users: Vec<Vec<u32>> = vec![Vec::new(); num_rows];
    for (index, ps) in preds.iter().enumerate() {
        for &p in ps {
            users[p as usize].push(u32::try_from(index).ok()?);
        }
    }
    let mut topo: Vec<u32> = (0..num_rows as u32)
        .filter(|&r| remaining[r as usize] == 0)
        .collect();
    let mut head = 0;
    while head < topo.len() {
        let g = topo[head];
        head += 1;
        for &u in &users[g as usize] {
            remaining[u as usize] -= 1;
            if remaining[u as usize] == 0 {
                topo.push(u);
            }
        }
    }
    if topo.len() != num_rows {
        return None; // cycle
    }

    // The floors, exact `i128` with checked arithmetic throughout: overflow
    // declines rather than wraps (a wrapped floor is a forged bound).
    let mut floors: Vec<i128> = vec![0; num_rows];
    for &r in &topo {
        let mut sum = instance.constraints[r as usize].rhs;
        for &p in &preds[r as usize] {
            sum = sum.checked_add(floors[p as usize])?;
        }
        floors[r as usize] = ceil_div(sum, 2)?;
    }

    Some(GroupDag {
        group_vars,
        preds,
        row_ids,
        floors,
        topo,
    })
}

// ---------------------------------------------------------------------------
// Emission.
// ---------------------------------------------------------------------------

fn emit(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
    dag: &GroupDag,
) -> Option<(String, u64)> {
    let input_count = veripb_input_constraint_count(instance).ok()?;
    let mut writer = VeriPbWriter::new(Vec::<u8>::new(), input_count).ok()?;

    // One `pol` per group, in topological order: predecessor floors, the
    // row, divide by 2. The division is the whole trick (see module docs).
    let num_rows = dag.group_vars.len();
    let mut derived: Vec<Option<ConstraintId>> = vec![None; num_rows];
    for &r in &dag.topo {
        let mut expression = String::new();
        for (slot, &p) in dag.preds[r as usize].iter().enumerate() {
            let id = derived[p as usize]?; // topo order guarantees Some
            if slot == 0 {
                write!(expression, "{id}").ok()?;
            } else {
                write!(expression, " {id} +").ok()?;
            }
        }
        if expression.is_empty() {
            write!(expression, "{}", dag.row_ids[r as usize]).ok()?;
        } else {
            write!(expression, " {} +", dag.row_ids[r as usize]).ok()?;
        }
        expression.push_str(" 2 d ;");
        derived[r as usize] = Some(writer.log_step(ProofStep::Polynomial(expression)).ok()?);
    }

    // The final `pol`: every group floor, once. The groups partition the
    // declared variables, so the sum is the unit objective row at degree
    // `Σ f(r)` — no literal-axiom fill is ever needed.
    let mut expression = String::new();
    for (slot, cid) in derived.iter().enumerate() {
        let id = (*cid)?;
        if slot == 0 {
            write!(expression, "{id}").ok()?;
        } else {
            write!(expression, " {id} +").ok()?;
        }
    }
    expression.push_str(" ;");
    let floor = writer.log_step(ProofStep::Polynomial(expression)).ok()?;

    writer.set_opt_bounds(optimum, optimum).ok()?;
    writer
        .conclude_opt_hinted(Some(floor), Some(&format_assignment(incumbent)))
        .ok()?;
    let text = String::from_utf8(writer.into_inner()).ok()?;
    Some((text, floor.get()))
}

// ---------------------------------------------------------------------------
// Entry point.
// ---------------------------------------------------------------------------

/// Certifies an OPT-LIN optimum for the layered group-division family.
///
/// Returns proof text, or `None` for any instance that is not exactly this
/// family, any incumbent that does not re-verify, and any floor that does not
/// EQUAL `optimum` — this rung's contract is OPTIMALITY, so a genuine but
/// weaker certified lower bound is withheld rather than published as one.
pub fn certify_opt_lin_layered_pebbling(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
) -> Option<String> {
    if optimum <= 0 {
        return None;
    }
    let dag = recover(instance)?;
    // Layer 3, BEFORE any emission: the upper bound must be real.
    if !incumbent_is_feasible(instance, incumbent) {
        return None;
    }
    let objective = instance.objective.as_ref()?;
    if evaluate_linear_objective(objective, incumbent)? != optimum {
        return None;
    }
    if dag.total_floor()? != optimum {
        return None;
    }
    let (text, floor_id) = emit(instance, incumbent, optimum, &dag)?;
    if !self_check(&text, instance, incumbent, optimum, floor_id) {
        return None;
    }
    Some(text)
}

/// FLOORS AS BOUNDS: the DAG floor as a PRE-SEARCH dual bound, computed by
/// exactly the recovery the certificate route re-runs at emission — no
/// incumbent, no optimum, no proof text.
///
/// # Soundness (this value licenses an OPTIMUM verdict, so the argument is
/// spelled out rather than referenced)
///
/// [`recover`] fails closed unless the instance is EXACTLY the layered
/// group-division family: every row `2·Σ(G_r) - Σ_{p} Σ(G_p) >= d_r` with the
/// groups a partition of the declared variables, the negative sides exact
/// disjoint unions of groups, the predecessor relation acyclic, and the
/// objective a unit payment on every variable. Under those (checked)
/// premises, for ANY feasible 0/1 point `x`, by induction over the
/// topological order:
///
/// * if every predecessor satisfies `Σ(G_p) >= f(p)`, then row `r` gives
///   `2·Σ(G_r) >= d_r + Σ_p Σ(G_p) >= d_r + Σ_p f(p)`, and `Σ(G_r)` is an
///   integer, so `Σ(G_r) >= ceil((d_r + Σ_p f(p)) / 2) = f(r)`;
/// * the groups are disjoint, so the floors add:
///   `Σ_v x_v = Σ_r Σ(G_r) >= Σ_r f(r)`.
///
/// This is the same inequality the emitted certificate derives in VeriPB
/// `pol` steps, minus the text; the arithmetic here is exact `i128` with
/// checked overflow (a wrapped floor would be a forged bound, so overflow
/// declines). The census misses this floor converts are exactly the ones
/// where the search holds the optimal incumbent within the budget and its
/// own dual bound is stuck at the LP value (`layeredfan_down_r7_c14_a4`:
/// incumbent 378 at 5 s, search dual ~284, floor 378).
///
/// Off-family cost: the layer-1 header gate is three integer comparisons,
/// and a header-accepting near-miss is refused by the O(1) first-row
/// coefficient probe before the O(#constraint) row-id build.
pub(super) fn recovered_floor(instance: &PbInstance) -> Option<i128> {
    let dag = recover(instance)?;
    let floor = dag.total_floor()?;
    (floor > 0).then_some(floor)
}

/// CONSTRUCTED WITNESS: an optimal incumbent built from the recovered DAG,
/// for the family members where the floor is PROVEN before the search
/// (floors-as-bounds) but the search cannot FIND an incumbent that meets it
/// within budget — at the 5 s census protocol four members hold incumbents
/// far above the installed floor (`down_r20_c39_a6`: 9126 against floor 4563;
/// `down_r26_c52_a5`: 13390 against 8034; `up_r22_c44_a5`: 9570 against 5742;
/// `up_r31_c62_a6`: 22878 against 11439), so the `floor == incumbent` verdict
/// flip never happens and the known optimum goes unreported.
///
/// # Construction
///
/// Set exactly `f(r)` variables of group `G_r` true — the group's first
/// `f(r)` in row term order, deterministic from the instance bytes. That this
/// is feasible is arithmetic, not luck: row `r` reads
/// `2·Σ(G_r) - Σ_p Σ(G_p) >= d_r`, the construction gives `Σ(G_r) = f(r)`
/// and `Σ(G_p) = f(p)`, and `2·f(r) - Σ_p f(p) >= d_r` IS the definition
/// `f(r) = ceil((d_r + Σ_p f(p)) / 2)`. The groups partition the declared
/// variables under a unit objective, so the witness's objective is exactly
/// `Σ_r f(r)` — the same total [`recovered_floor`] proves as a lower bound,
/// hence the point is optimal and `floor == incumbent` upgrades the verdict
/// the moment the caller installs both.
///
/// # Fail-closed
///
/// The argument above is a reason to EXPECT verification to succeed, never a
/// substitute for it. The constructed point passes the same re-verification
/// every incumbent passes before it can carry a verdict or reach the
/// certificate chain: feasibility against EVERY original row
/// ([`incumbent_is_feasible`]) and an exact objective recomputation that must
/// EQUAL the recovered floor. Any mismatch withholds the witness:
/// `f(r) < 0` fails the `usize` conversion, and `f(r) > |G_r|` — which by the
/// floor's soundness argument proves the instance INFEASIBLE — declines
/// before any row is touched.
pub(super) fn constructed_optimum_witness(instance: &PbInstance) -> Option<(Vec<bool>, i128)> {
    let dag = recover(instance)?;
    let floor = dag.total_floor()?;
    if floor <= 0 {
        return None;
    }
    let order = usize::try_from(instance.num_vars).ok()?;
    let mut witness = vec![false; order];
    for (group, &group_floor) in dag.group_vars.iter().zip(&dag.floors) {
        // A negative per-group floor fails this conversion: the group's sum
        // would exceed its floor and the objective could no longer equal the
        // total, so there is deliberately no clamp-to-zero path.
        let need = usize::try_from(group_floor).ok()?;
        if need > group.len() {
            return None;
        }
        for &var in group.iter().take(need) {
            witness[usize::try_from(var.checked_sub(1)?).ok()?] = true;
        }
    }
    // The same layer-3 re-verification the certificate entry point applies to
    // a search incumbent; a constructed point earns no shortcut past it.
    if !incumbent_is_feasible(instance, &witness) {
        return None;
    }
    let objective = instance.objective.as_ref()?;
    if evaluate_linear_objective(objective, &witness)? != floor {
        return None;
    }
    Some((witness, floor))
}
