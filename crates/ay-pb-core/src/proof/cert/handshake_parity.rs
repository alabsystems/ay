// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! OPT-LIN optimality certificates for the EQUALITY-HANDSHAKE PARITY family —
//! the `evencolouring` CoreGuidedPB instances — whose LP relaxation optimum is
//! exactly `0` against an integer optimum of `1`.
//!
//! # The family
//!
//! Every constraint is an all-unit equality with exactly one objective
//! ("slack") variable, and every non-objective ("edge") variable appears in
//! exactly two rows:
//!
//! ```text
//! s_v + Σ_{e ∋ v} x_e  =  d_v          (one row per v, all coefficients +1)
//! min  Σ_v w_v s_v                     (all w_v >= 1)
//! ```
//!
//! In `evencolouring`, `v` ranges over the vertices of a 6-regular graph,
//! `x_e` two-colours the edges, `d_v = 3` asks for an even split at every
//! vertex, and `s_v` buys one unit of imbalance at cost `w_v`.
//!
//! # Why no LP-dual floor can ever fire here
//!
//! Set every edge variable to `d_v / deg(v)` (in `evencolouring`, `1/2`) and
//! every slack to `0`: each row holds with equality and the objective is `0`.
//! Every objective coefficient is positive over `s >= 0`, so `LP* >= 0` too.
//! `LP*` is therefore exactly `0`, pinned from both sides with no float in the
//! loop, and weak duality caps EVERY dual floor at `ceil(0) = 0`. The relaxation
//! cannot see the problem; the six previous families all died on this exact
//! inference and so does this one.
//!
//! # The mathematics, in one paragraph
//!
//! Sum all the rows: each edge variable appears in exactly two, so
//!
//! ```text
//! Σ_v s_v + 2 Σ_e x_e  =  D,   where D = Σ_v d_v .
//! ```
//!
//! When `D` is ODD this is a handshake-lemma contradiction at `Σ s = 0`: the
//! left side would be even. Hence `Σ_v s_v` is odd, so `Σ_v s_v >= 1` and
//! `obj >= min_v w_v`. The LP cannot express "odd"; cutting-planes DIVISION
//! extracts it in three `pol` lines over the VeriPB `=`-split halves
//! (`G`, `F`, then the floor):
//!
//! ```text
//! G = (Σ >=-halves) / 2                        :  Σ s + Σ x  >= (D+1)/2
//! F = (Σ <=-halves + Σ_v 2·[s_v >= 0]) / 2     :  Σ s + Σ ~x >= E - (D-1)/2
//! P = (F + G) / 2                              :  Σ s        >= 1
//! ```
//!
//! In `F + G` every `x_e + ~x_e` collapses into the constant `E`, leaving
//! `2 Σ s >= 1`, and the final division rounds up — the same one-character
//! ending as `frustrated_cycle`, driven by the same phenomenon: the parity
//! residue an LP must carry as `1/2` is exactly what `d` rounds away. A last
//! optional line lifts `Σ s >= 1` to the weighted objective row by adding
//! `(w_v - w_min) · [s_v >= 0]` axioms and multiplying by `w_min`.
//!
//! Measured on the ten-instance corpus family (`nvert_021` … `nvert_501`,
//! `unit` and `linear`): certificates of 1.1 KB to 24 KB, each
//! `s VERIFIED BOUNDS 1 <= obj <= 1` under the pinned checker — including
//! `nvert_451` and `nvert_501`, where the SEARCH cannot prove optimality at the
//! census budget at all (5 s incumbent `1`, no proof; the 60 s search proof of
//! `nvert_071` alone is 6.6 MB).
//!
//! # Fail-closed, in four independent layers
//!
//! 1. **O(1) pre-gate** ([`header_candidate`]): `|objective| == #constraint`
//!    and `#variable > |objective|` — two integer comparisons the parser has
//!    already paid for. Off-family instances essentially never have exactly one
//!    objective variable per row.
//! 2. **Total structural recovery** ([`recover`]): EVERY row and EVERY variable
//!    is accounted for against the template, or the module declines — including
//!    the parity condition itself (`D` odd) and a deterministic row-count
//!    budget. There is no "mostly matched" path.
//! 3. **Independent incumbent re-verification**: feasible against the ORIGINAL
//!    rows, objective exactly `optimum`, and the derived floor `min_v w_v` must
//!    EQUAL `optimum` — a genuine but weaker parity floor is withheld rather
//!    than published, because this rung's contract is OPTIMALITY.
//! 4. **Self-check of the emitted BYTES**: the finished text is parsed back and
//!    replayed through the shared cutting-planes interpreter
//!    ([`super::cp_replay`]) under VeriPB's normalized-literal semantics, with
//!    the input `=` rows seeded at VeriPB's two-id split. The proof must be
//!    `pol`-only, every replayed row must hold at the (feasible) incumbent, and
//!    the cited row must be EXACTLY the weighted objective at degree `optimum`.
//!
//! SOUNDNESS: this module returns proof *text* only, and it is not trusted
//! until the external PINNED VeriPB re-checks it (verify-before-claim). A
//! `None` is a withheld certificate and never changes the reported status.

#[cfg(test)]
mod tests;

use std::collections::BTreeMap;
use std::fmt::Write as _;

use super::cp_replay::self_check_pol_only_weighted_objective_floor as self_check;
use super::{evaluate_linear_objective, format_assignment, incumbent_is_feasible};
use crate::proof::steps::ProofStep;
use crate::proof::veripb::{veripb_input_constraint_count, veripb_input_row_ids, VeriPbWriter};
use crate::types::{PbInstance, PbRel};

/// Deterministic count budget: rows above this decline rather than emit an
/// unbounded proof. The corpus family tops out at 501 rows; the cap is
/// generous, not a tuning knob, and it bounds the emitted bytes by a constant
/// multiple of the input either way (the proof cites each input id once).
const MAX_ROWS: usize = 1 << 20;

// ---------------------------------------------------------------------------
// Layer 1: the O(1) pre-gate.
// ---------------------------------------------------------------------------

/// Candidacy from the header integers alone: one objective (slack) variable
/// per row and at least one non-objective (edge) variable to carry the parity.
///
/// Two comparisons, no loop, no allocation: an off-family instance pays for
/// this and nothing else.
fn header_candidate(num_vars: u64, num_constraints: u64, num_objective: u64) -> bool {
    num_constraints >= 1 && num_objective == num_constraints && num_vars > num_objective
}

// ---------------------------------------------------------------------------
// Layer 2: total, fail-closed structure recovery.
// ---------------------------------------------------------------------------

/// One recovered row: its slack variable, the slack's objective weight, and the
/// VeriPB input id of the row's `>=` half (the `<=` half is at `ge_id + 1`).
struct Row {
    slack: u32,
    weight: i128,
    ge_id: u64,
}

/// The recovered family instance.
struct Handshake {
    rows: Vec<Row>,
    /// Number of distinct edge variables (each in exactly two rows).
    edges: u64,
    /// `Σ_v d_v`, exact; ODD or `recover` declined.
    rhs_total: i128,
    /// `min_v w_v` — the derived floor.
    w_min: i128,
}

/// Recovers the handshake structure, accounting for EVERY row and EVERY
/// variable, or declines. The parity condition (`Σ d_v` odd) is part of the
/// structure: an even total has no argument and MUST decline here, not emit.
fn recover(instance: &PbInstance) -> Option<Handshake> {
    let objective = instance.objective.as_ref()?;
    if !header_candidate(
        u64::from(instance.num_vars),
        instance.constraints.len() as u64,
        objective.terms.len() as u64,
    ) {
        return None;
    }
    if instance.constraints.len() > MAX_ROWS {
        return None;
    }

    // The objective: positive weights over distinct positive literals.
    let mut weight_of: BTreeMap<u32, i128> = BTreeMap::new();
    for term in &objective.terms {
        let [lit] = term.lits.as_slice() else {
            return None;
        };
        if lit.negated || term.coeff < 1 {
            return None;
        }
        if weight_of.insert(lit.var, term.coeff).is_some() {
            return None;
        }
    }

    let ids = veripb_input_row_ids(instance).ok()?;
    let mut rows: Vec<Row> = Vec::with_capacity(instance.constraints.len());
    let mut edge_uses: BTreeMap<u32, u32> = BTreeMap::new();
    let mut slack_seen: BTreeMap<u32, ()> = BTreeMap::new();
    let mut rhs_total: i128 = 0;
    for (index, constraint) in instance.constraints.iter().enumerate() {
        if constraint.rel != PbRel::Eq || constraint.rhs < 0 {
            return None;
        }
        let mut slack: Option<u32> = None;
        for term in &constraint.terms {
            let [lit] = term.lits.as_slice() else {
                return None;
            };
            if lit.negated || term.coeff != 1 {
                return None;
            }
            if weight_of.contains_key(&lit.var) {
                if slack.is_some() {
                    return None;
                }
                slack = Some(lit.var);
            } else {
                let uses = edge_uses.entry(lit.var).or_insert(0);
                *uses = uses.checked_add(1)?;
                if *uses > 2 {
                    return None;
                }
            }
        }
        let slack = slack?;
        if slack_seen.insert(slack, ()).is_some() {
            return None;
        }
        rhs_total = rhs_total.checked_add(constraint.rhs)?;
        rows.push(Row {
            slack,
            weight: *weight_of.get(&slack)?,
            ge_id: ids.get(index)?.get(),
        });
    }
    // Total accounting: every objective variable is some row's slack, every
    // edge variable is in exactly two rows, and nothing else is declared.
    if slack_seen.len() != weight_of.len() {
        return None;
    }
    if edge_uses.values().any(|&uses| uses != 2) {
        return None;
    }
    let edges = edge_uses.len() as u64;
    if edges == 0 {
        return None;
    }
    let declared = (rows.len() as u64).checked_add(edges)?;
    if declared != u64::from(instance.num_vars) {
        return None;
    }
    // THE PARITY. An even RHS total has no handshake contradiction: decline.
    if rhs_total.rem_euclid(2) != 1 {
        return None;
    }
    let w_min = rows.iter().map(|row| row.weight).min()?;
    let family = Handshake {
        rows,
        edges,
        rhs_total,
        w_min,
    };
    // The derivation's own arithmetic, replayed exactly: `F + G` must leave
    // `2 Σ s >= 1`. `G` has degree `ceil(D/2)` and `F` has degree
    // `E - (D-1)/2`; their sum minus the collapsed edge constant `E` is `1`
    // precisely because `D` is odd. For odd `D` this is an identity, but it is
    // checked (with overflow-checked arithmetic) rather than assumed: declining
    // is the only safe response to a logic error, and this same recovery now
    // also backs a verdict-bearing pre-search floor.
    let d = family.rhs_total;
    let g_degree = d.checked_add(1)?.checked_div(2)?;
    let f_degree = i128::try_from(family.edges)
        .ok()?
        .checked_sub(d.checked_sub(1)?.checked_div(2)?)?;
    let residue = g_degree
        .checked_add(f_degree)?
        .checked_sub(i128::try_from(family.edges).ok()?)?;
    if residue != 1 {
        return None;
    }
    Some(family)
}

/// FLOORS AS BOUNDS: the parity floor from recovery alone — no incumbent, no
/// optimum, no proof text. `Some(min_v w_v)` iff the instance IS the family
/// and the handshake total is odd. The argument is pure integer counting over
/// the fail-closed recovery above: summing every row gives each edge variable
/// an even coefficient against an odd right-hand side, so the slack sum is odd,
/// hence at least `1`, hence the objective is at least `min_v w_v`. No float,
/// no search, no separation — the same bar `odd_cycle_cover::recovered_floor`
/// meets.
pub(super) fn recovered_floor(instance: &PbInstance) -> Option<i128> {
    Some(recover(instance)?.w_min)
}

// ---------------------------------------------------------------------------
// Emission.
// ---------------------------------------------------------------------------

/// `id1 id2 + id3 + …` over the given ids, or `None` when empty.
fn summed(ids: impl IntoIterator<Item = u64>) -> Option<String> {
    let mut ids = ids.into_iter();
    let mut expression = ids.next()?.to_string();
    for id in ids {
        write!(expression, " {id} +").ok()?;
    }
    Some(expression)
}

fn emit(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
    family: &Handshake,
) -> Option<(String, u64)> {
    let input_count = veripb_input_constraint_count(instance).ok()?;
    let mut writer = VeriPbWriter::new(Vec::<u8>::new(), input_count).ok()?;

    // G: (sum of `>=` halves) / 2.
    let mut expression = summed(family.rows.iter().map(|row| row.ge_id))?;
    expression.push_str(" 2 d ;");
    let g = writer.log_step(ProofStep::Polynomial(expression)).ok()?;

    // F: (sum of `<=` halves, plus 2·[s_v >= 0] per row) / 2. The literal
    // axioms convert each `~s_v` into `s_v` plus a constant, so F and G carry
    // the slacks with the SAME sign and the edges with opposite ones.
    let mut expression = summed(
        family
            .rows
            .iter()
            .map(|row| row.ge_id.checked_add(1))
            .collect::<Option<Vec<_>>>()?,
    )?;
    for row in &family.rows {
        write!(expression, " x{} 2 * +", row.slack).ok()?;
    }
    expression.push_str(" 2 d ;");
    let f = writer.log_step(ProofStep::Polynomial(expression)).ok()?;

    // P: (F + G) / 2 — every `x_e + ~x_e` collapses to a constant, leaving
    // `2 Σ s >= 1`, and the division rounds the parity residue up.
    let p = writer
        .log_step(ProofStep::Polynomial(format!("{g} {f} + 2 d ;")))
        .ok()?;

    // The floor the conclusion cites must be EXACTLY the weighted objective
    // row at degree `optimum == w_min`. `P` already is it when every weight is
    // `1`; otherwise lift with literal axioms, then scale.
    let uniform_unit = family.rows.iter().all(|row| row.weight == 1);
    let floor = if uniform_unit {
        p
    } else {
        let mut expression = p.to_string();
        if family.w_min != 1 {
            write!(expression, " {} *", family.w_min).ok()?;
        }
        for row in &family.rows {
            let lift = row.weight.checked_sub(family.w_min)?;
            if lift > 0 {
                write!(expression, " x{} {lift} * +", row.slack).ok()?;
            }
        }
        expression.push_str(" ;");
        writer.log_step(ProofStep::Polynomial(expression)).ok()?
    };

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

/// Certifies an OPT-LIN optimum for the equality-handshake parity family.
///
/// Returns proof text, or `None` for any instance that is not exactly this
/// family, any incumbent that does not re-verify, and any optimum other than
/// the parity floor `min_v w_v` — this rung's contract is OPTIMALITY, so a
/// genuine but weaker certified lower bound is withheld rather than published
/// as one.
pub fn certify_opt_lin_handshake_parity(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
) -> Option<String> {
    if optimum <= 0 {
        return None;
    }
    let family = recover(instance)?;
    // Layer 3, BEFORE any emission: the upper bound must be real and the floor
    // must reach it exactly.
    if family.w_min != optimum {
        return None;
    }
    if !incumbent_is_feasible(instance, incumbent) {
        return None;
    }
    let objective = instance.objective.as_ref()?;
    if evaluate_linear_objective(objective, incumbent)? != optimum {
        return None;
    }
    let (text, floor_id) = emit(instance, incumbent, optimum, &family)?;
    if !self_check(&text, instance, incumbent, optimum, floor_id) {
        return None;
    }
    Some(text)
}
