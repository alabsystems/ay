// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! OPT-LIN optimality certificates for PURE MINIMUM VERTEX COVER — the
//! `vertexcover_opt_grid_*` toroidal-grid family, every row `x_u + x_v >= 1`
//! and the objective a unit `min` over every variable.
//!
//! # Why no LP-dual floor can ever fire here, and why that never bounded the
//! # question
//!
//! Set every variable to `1/2`. Every row reads `1/2 + 1/2 >= 1`: feasible, with
//! equality, at objective `V/2`. So `LP* <= V/2` — and on this family that is
//! strictly below the optimum. Measured, by this module, on the corpus in
//! `benchmarks/pb-comp`:
//!
//! ```text
//! oddrowevencol_dim_022   V = 506     LP* <= 253     optimum 264
//! oddrowevencol_dim_042   V = 1806    LP* <= 903     optimum 924
//! evenrowoddcol_dim_160   V = 25760   LP* <= 12880   optimum 12960
//! ```
//!
//! `ceil(LP*) < opt`, so weak duality caps EVERY dual floor strictly below the
//! optimum, permanently. This module does not touch that. It is the FIFTH time a
//! family's LP-dual route has been arithmetically dead, and — like the four
//! before it — the family is certified anyway, because cutting planes has
//! DIVISION and division has no LP dual.
//!
//! # The mathematics, in one paragraph
//!
//! For any ODD cycle `C`, sum the `|C|` edge rows around it. Every vertex of `C`
//! is an endpoint of exactly two of them, so the sum is `2·Σ_{v∈C} x_v >= |C|`,
//! and one division rounds it up:
//!
//! ```text
//! pol e1 e2 + e3 + … + eL + 2 d ;    ->    Σ_{v∈C} x_v >= (|C|+1)/2
//! ```
//!
//! THE DIVISION IS THE WHOLE TRICK. `2·Σ >= L` gives an LP only `Σ >= L/2`; the
//! `d` rule rounds the DEGREE up, which is precisely the step the half-integral
//! point survives and no dual multiplier can imitate. Packing the cuts over
//! VERTEX-DISJOINT odd cycles, adding one input row per matched residual edge,
//! and filling the untouched vertices with LITERAL AXIOMS (`xN` as a `pol`
//! operand is the constraint `xN >= 0`) lifts every objective coefficient to
//! exactly `1`:
//!
//! ```text
//! pol c1 c2 + … + m1 + … + xj + … ;  ->    Σ_{v} x_v >= Σ_C (|C|+1)/2 + |M|
//! ```
//!
//! Each disjoint odd cycle buys exactly `+1/2` over the `V/2` the relaxation is
//! stuck at, and this family's graphs decompose PERFECTLY: the `dim_022` torus
//! is 22 vertex-disjoint 23-cycles, so the packing is `22 · 12 = 264`, the
//! optimum, with no slack anywhere. A family that buys **0 %** of the gap in the
//! original variable space buys **100 %** of it as a proof.
//!
//! The bipartite members (`evenrowevencol_*`) contain no odd cycle at all and
//! are closed by the residual matching alone — `V/2` matched edge rows, which is
//! König's theorem written as a `pol` line.
//!
//! # Fail-closed, in four independent layers
//!
//! A certificate the checker accepts that does NOT establish the bound is the
//! worst defect this repository can ship, so nothing is emitted until all four
//! pass:
//!
//! 1. **O(1) pre-gate** ([`header_candidate`]). Three header integers decide
//!    candidacy before a single constraint is touched: the objective must have
//!    exactly one term per declared variable. Nothing is allocated and there is
//!    no loop, so an off-family instance pays for this and nothing else.
//! 2. **Total structural recovery** ([`recover`]). EVERY row must be
//!    `+1 x_u +1 x_v >= 1` over two distinct un-negated variables, and EVERY
//!    declared variable must carry exactly one unit objective term. Anything
//!    else declines. There is deliberately no "mostly matched" path.
//! 3. **Independent incumbent re-verification.** The incumbent is checked
//!    feasible against the ORIGINAL rows and equal to `optimum`, and the derived
//!    floor must equal `optimum` exactly — a packing that falls short is declined
//!    rather than published as a weaker bound, because this rung's contract is
//!    OPTIMALITY.
//! 4. **Self-check of the emitted BYTES**
//!    ([`super::cp_replay::self_check_pol_only_objective_floor`]). The finished
//!    text is PARSED BACK and replayed under VeriPB's normalized-literal
//!    semantics for `d`. The replay rebuilds every row from the instance, so a
//!    mis-cited id, a mis-ordered operand or a wrong divisor cannot survive it.
//!
//! SOUNDNESS: this module returns proof *text* only, and it is not trusted until
//! the external PINNED VeriPB re-checks it (verify-before-claim). A `None` is a
//! withheld certificate and never changes the reported status.

mod packing;
#[cfg(test)]
mod tests;

use std::fmt::Write as _;

use self::packing::{Limits, Packing};
use super::cp_replay::self_check_pol_only_objective_floor as self_check;
use super::{evaluate_linear_objective, format_assignment, incumbent_is_feasible};
use crate::proof::steps::{ConstraintId, ProofStep};
use crate::proof::veripb::{veripb_input_constraint_count, veripb_input_row_ids, VeriPbWriter};
use crate::types::{PbInstance, PbRel};

// ---------------------------------------------------------------------------
// Layer 1: the O(1) pre-gate.
// ---------------------------------------------------------------------------

/// `true` when an instance's three header integers are consistent with pure
/// minimum vertex cover.
///
/// The family's shape fixes the objective exactly: minimum vertex cover pays
/// `1` for EVERY vertex, so there is one objective term per declared variable
/// and `|objective| == #variable`. That single equality is what does the work —
/// an optimization instance whose objective mentions every variable it declares,
/// with no repetition, is already unusual — and it is three integer comparisons
/// with no loop and no allocation.
///
/// Deliberately NOT tested here: any relationship between `#constraint` and
/// `#variable`. A graph may legitimately contain isolated vertices (paid `0` by
/// the optimum and filled by a literal axiom in the derivation), so a bound like
/// `2·#constraint >= #variable` would be a FALSE decline, and this gate is meant
/// to be cheap, not clever. Everything structural is layer 2's job.
fn header_candidate(num_vars: u64, num_constraints: u64, num_objective: u64) -> bool {
    num_vars >= 3 && num_constraints >= 1 && num_objective == num_vars
}

// ---------------------------------------------------------------------------
// Layer 2: total, fail-closed structure recovery.
// ---------------------------------------------------------------------------

/// A recovered graph in CSR form. Construction accounts for every row and every
/// variable of the instance or fails.
///
/// Vertex `v` is 0-indexed and denotes the OPB variable `v + 1`.
pub(super) struct CoverGraph {
    /// `adjacency[start[v] .. start[v+1]]` are `v`'s incident `(other, edge)`.
    start: Vec<u32>,
    adjacency: Vec<(u32, u32)>,
    /// Edge index -> the VeriPB input row id of the row that declared it.
    edge_row: Vec<u64>,
}

impl CoverGraph {
    pub(super) fn order(&self) -> usize {
        self.start.len() - 1
    }

    pub(super) fn neighbours(&self, v: u32) -> &[(u32, u32)] {
        let lo = self.start[v as usize] as usize;
        let hi = self.start[v as usize + 1] as usize;
        &self.adjacency[lo..hi]
    }

    pub(super) fn adjacency_start(&self, v: u32) -> u32 {
        self.start[v as usize]
    }

    pub(super) fn adjacency_end(&self, v: u32) -> u32 {
        self.start[v as usize + 1]
    }

    pub(super) fn adjacency_at(&self, cursor: u32) -> (u32, u32) {
        self.adjacency[cursor as usize]
    }

    /// The VeriPB input row id of the edge `u—w`, or `None` if there is none.
    pub(super) fn edge_row_between(&self, u: u32, w: u32) -> Option<u64> {
        self.neighbours(u)
            .iter()
            .find(|&&(other, _)| other == w)
            .map(|&(_, edge)| self.edge_row[edge as usize])
    }

    /// Row ids of the edges of a CLOSED walk, in walk order.
    ///
    /// Returns `None` unless every consecutive pair (including the wrap from the
    /// last vertex back to the first) is a real edge and the row ids are
    /// pairwise distinct — a repeated row would double-count a constraint and
    /// break the "each vertex appears exactly twice" arithmetic the `2 d` step
    /// depends on.
    pub(super) fn walk_row_ids(&self, walk: &[u32]) -> Option<Vec<u64>> {
        if walk.len() < 3 {
            return None;
        }
        let mut ids = Vec::with_capacity(walk.len());
        for (index, &from) in walk.iter().enumerate() {
            let to = walk[(index + 1) % walk.len()];
            ids.push(self.edge_row_between(from, to)?);
        }
        let mut sorted = ids.clone();
        sorted.sort_unstable();
        sorted.dedup();
        if sorted.len() != ids.len() {
            return None;
        }
        Some(ids)
    }
}

/// Recovers the graph, accounting for EVERY row and EVERY variable.
///
/// Declines on the first thing it cannot explain. There is deliberately no
/// "mostly matched" path: a partial match is exactly the state in which an
/// emitter would write a derivation over rows it has misread.
fn recover(instance: &PbInstance) -> Option<CoverGraph> {
    let objective = instance.objective.as_ref()?;
    let num_vars = u64::from(instance.num_vars);
    if !header_candidate(
        num_vars,
        instance.constraints.len() as u64,
        objective.terms.len() as u64,
    ) {
        return None;
    }
    let order = usize::try_from(instance.num_vars).ok()?;

    // THE ROW SHAPE IS CHECKED BEFORE THE OBJECTIVE, and that ordering is the
    // whole cost story for an off-family instance. The header gate is three
    // integer comparisons but it is not very selective: `|objective| ==
    // #variable` holds for 366 of the 2,068 parseable instances in
    // `benchmarks/pb-comp`, of which only 16 are actually this family. Walking
    // the objective first would charge every one of those 350 near-misses
    // `O(#variable)`; probing `constraints[0]` first charges them `O(1)`,
    // because a row that is not `+1 x_u +1 x_v >= 1` is the first thing almost
    // every non-vertex-cover instance has. The probe must come BEFORE
    // `veripb_input_row_ids`, which walks every row to build the id map — an
    // audit measured 1.3-3.2 ms on a 656,900-row near-miss when the map was
    // built first. This matters doubly now that `recovered_floor` runs this
    // recovery at the START of every optimization solve, not only at
    // certificate time. Nothing about fail-closedness changes: both loops
    // below still have to pass in full.
    {
        let first = instance.constraints.first()?;
        if first.rel != PbRel::Ge || first.rhs != 1 || first.terms.len() != 2 {
            return None;
        }
    }

    // Every row is `+1 x_u +1 x_v >= 1` over two DISTINCT un-negated variables.
    // VeriPB row ids come from the shared map, never from `index + 1`: an `=`
    // row shifts every id after it, and citing `index + 1` past one is exactly
    // how this repository shipped four uncheckable proofs. A non-`Ge` row is
    // refused outright below, so the two can never disagree here — but the map
    // is still what is used, because the next family may not be so lucky.
    let ids = veripb_input_row_ids(instance).ok()?;
    let mut ends: Vec<(u32, u32)> = Vec::with_capacity(instance.constraints.len());
    let mut edge_row: Vec<u64> = Vec::with_capacity(instance.constraints.len());
    let mut degree = vec![0u32; order];
    for (index, constraint) in instance.constraints.iter().enumerate() {
        if constraint.rel != PbRel::Ge || constraint.rhs != 1 || constraint.terms.len() != 2 {
            return None;
        }
        let mut pair = [0u32; 2];
        for (slot, term) in constraint.terms.iter().enumerate() {
            let [lit] = term.lits.as_slice() else {
                return None;
            };
            if lit.negated || term.coeff != 1 {
                return None;
            }
            let vertex = lit.var.checked_sub(1)?;
            if usize::try_from(vertex).ok()? >= order {
                return None;
            }
            pair[slot] = vertex;
        }
        if pair[0] == pair[1] {
            return None;
        }
        degree[pair[0] as usize] = degree[pair[0] as usize].checked_add(1)?;
        degree[pair[1] as usize] = degree[pair[1] as usize].checked_add(1)?;
        ends.push((pair[0], pair[1]));
        edge_row.push(ids.get(index)?.get());
    }

    // The objective is a unit payment on every variable, each exactly once.
    // This is what makes the floor row the OBJECTIVE row: every declared
    // variable gets coefficient 1 in the final combination, so the derived row
    // and `min: Σ x_v` have the same support with the same coefficients.
    let mut paid = vec![false; order];
    for term in &objective.terms {
        let [lit] = term.lits.as_slice() else {
            return None;
        };
        if lit.negated || term.coeff != 1 {
            return None;
        }
        let index = usize::try_from(lit.var.checked_sub(1)?).ok()?;
        if index >= order || paid[index] {
            return None;
        }
        paid[index] = true;
    }
    if paid.iter().any(|&seen| !seen) {
        return None;
    }

    // CSR build, in ascending vertex order and then in row order within a
    // vertex, so every downstream scan is deterministic.
    let mut start = vec![0u32; order + 1];
    for v in 0..order {
        start[v + 1] = start[v].checked_add(degree[v])?;
    }
    let total = usize::try_from(start[order]).ok()?;
    let mut cursor = start.clone();
    let mut adjacency = vec![(0u32, 0u32); total];
    for (edge, &(u, w)) in ends.iter().enumerate() {
        let edge = u32::try_from(edge).ok()?;
        adjacency[cursor[u as usize] as usize] = (w, edge);
        cursor[u as usize] += 1;
        adjacency[cursor[w as usize] as usize] = (u, edge);
        cursor[w as usize] += 1;
    }
    let graph = CoverGraph {
        start,
        adjacency,
        edge_row,
    };
    // A PARALLEL EDGE would make `edge_row_between` ambiguous and would break the
    // "each cycle vertex is an endpoint of exactly two of the summed rows"
    // arithmetic the `2 d` step depends on: a duplicated `x_u + x_v >= 1` row
    // summed twice puts coefficient 4, not 2, on those vertices, and the divided
    // row would then be weaker than the one the self-check expects. Refuse.
    let mut seen: Vec<u32> = Vec::new();
    for v in 0..graph.order() as u32 {
        seen.clear();
        seen.extend(graph.neighbours(v).iter().map(|&(other, _)| other));
        seen.sort_unstable();
        let before = seen.len();
        seen.dedup();
        if seen.len() != before {
            return None;
        }
    }

    Some(graph)
}

// ---------------------------------------------------------------------------
// Emission.
// ---------------------------------------------------------------------------

/// `e1 e2 + e3 + … + eL + 2 d ;` — the summed cycle, halved and rounded up.
fn cycle_expression(ids: &[u64]) -> Option<String> {
    let (first, rest) = ids.split_first()?;
    let mut expression = first.to_string();
    for id in rest {
        write!(expression, " {id} +").ok()?;
    }
    expression.push_str(" 2 d ;");
    Some(expression)
}

fn emit(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
    pack: &Packing,
) -> Option<(String, u64)> {
    let input_count = veripb_input_constraint_count(instance).ok()?;
    let mut writer = VeriPbWriter::new(Vec::<u8>::new(), input_count).ok()?;

    let mut cuts: Vec<ConstraintId> = Vec::with_capacity(pack.cycles.len());
    for ids in &pack.cycles {
        let cut = writer
            .log_step(ProofStep::Polynomial(cycle_expression(ids)?))
            .ok()?;
        cuts.push(cut);
    }

    // One `pol` expression: every cut, every matched input row, and a LITERAL
    // AXIOM for every vertex the packing did not load. `xN` as a `pol` operand
    // is the constraint `xN >= 0`, so the fill raises the coefficient of an
    // untouched vertex from 0 to 1 without moving the degree. No `rup` and no
    // `red` appears anywhere in this proof.
    let mut expression = String::new();
    let push = |token: &str, expression: &mut String| {
        if expression.is_empty() {
            expression.push_str(token);
        } else {
            expression.push(' ');
            expression.push_str(token);
            expression.push_str(" +");
        }
    };
    for cut in &cuts {
        push(&cut.to_string(), &mut expression);
    }
    for id in &pack.matched {
        push(&id.to_string(), &mut expression);
    }
    for (index, &loaded) in pack.loaded.iter().enumerate() {
        if !loaded {
            push(&format!("x{}", index + 1), &mut expression);
        }
    }
    if expression.is_empty() {
        return None;
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

/// Certifies an OPT-LIN optimum for pure minimum vertex cover by odd-cycle cuts.
///
/// Returns proof text, or `None` for any instance that is not exactly this
/// family, any incumbent that does not re-verify, and any packing whose floor
/// falls short of `optimum` — this rung's contract is OPTIMALITY, so a genuine
/// but weaker certified lower bound is withheld rather than published as one.
pub fn certify_opt_lin_odd_cycle_cover(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
) -> Option<String> {
    certify_with_limits(instance, incumbent, optimum, Limits::production())
}

fn certify_with_limits(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
    limits: Limits,
) -> Option<String> {
    if optimum <= 0 {
        return None;
    }
    let graph = recover(instance)?;
    // Layer 3, BEFORE any search: the upper bound must be real.
    if !incumbent_is_feasible(instance, incumbent) {
        return None;
    }
    let objective = instance.objective.as_ref()?;
    if evaluate_linear_objective(objective, incumbent)? != optimum {
        return None;
    }

    let pack = packing::build(&graph, limits)?;
    if pack.bound != optimum {
        return None;
    }
    let (text, floor_id) = emit(instance, incumbent, optimum, &pack)?;
    if !self_check(&text, instance, incumbent, optimum, floor_id) {
        return None;
    }
    Some(text)
}

/// FLOORS AS BOUNDS: the packing bound as a PRE-SEARCH dual floor, computed by
/// exactly the recovery + packing the certificate route re-runs at emission —
/// no incumbent, no optimum, no proof text.
///
/// # Soundness (this value licenses an OPTIMUM verdict, so the argument is
/// spelled out rather than referenced)
///
/// [`recover`] fails closed unless the instance is EXACTLY pure minimum vertex
/// cover: every constraint is `+1 x_u +1 x_v >= 1` over two distinct
/// un-negated variables with no parallel edges, and the objective pays `+1`
/// for every declared variable exactly once. Under those (checked) premises,
/// for ANY feasible 0/1 point `x`:
///
/// * an odd cycle `C` of length `L` with distinct vertices contributes
///   `Σ_{v∈C} x_v >= ceil(L/2)` — summing its `L` edge rows gives
///   `2·Σ_{v∈C} x_v >= L` (each cycle vertex is an endpoint of exactly two of
///   the summed rows), and the left side is even;
/// * a matched edge contributes `x_u + x_w >= 1` (its own input row);
/// * the cycles are vertex-disjoint by construction (each accepted cycle
///   deletes its vertices from `alive` before the next search) and the
///   matching lives in the residual, so the contributions are on DISJOINT
///   variable sets and add;
/// * every remaining variable contributes `x_v >= 0`.
///
/// Hence `Σ_v x_v >= Σ_C ceil(L_C/2) + |matching| == pack.bound` — the same
/// inequality the emitted certificate derives in VeriPB `pol` steps, minus the
/// text. `packing` itself is deterministic (count-bounded, no wall clock) and
/// re-checks cycle simplicity and edge existence before accepting a walk; a
/// packing defect can only WEAKEN the bound, never inflate it, because the
/// bound is recomputed here from the accepted cycles' lengths and the matched
/// edge count alone. Audit trail: the certifier built on this recovery was
/// fuzzed against brute-force optima on 1,282 random graphs (incl. 271 with
/// isolated vertices) with zero overshoots, and its 14/14 corpus emissions are
/// byte-identical to an independent implementation (tasks/wtz5bzztq T1 +
/// auditT1).
///
/// Off-family cost: the layer-1 header gate is three integer comparisons, and
/// a header-accepting near-miss is refused by the O(1) first-row shape check
/// before the O(#constraint) row-id build.
pub(super) fn recovered_floor(instance: &PbInstance) -> Option<i128> {
    let graph = recover(instance)?;
    let pack = packing::build(&graph, Limits::production())?;
    (pack.bound > 0).then_some(pack.bound)
}
