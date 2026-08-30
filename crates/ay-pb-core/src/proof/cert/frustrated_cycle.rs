// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! OPT-LIN optimality certificates for the SIGNED GRAPH / FRUSTRATION INDEX
//! family — `macrophage` and `methanosarcina`, the Heinz sign-consistency
//! instances — whose LP relaxation optimum is exactly `0` against optima of
//! `374` and `2730`.
//!
//! # Why no LP-dual floor can ever fire here, and why that never bounded the
//! # question
//!
//! Set every SIGN variable to `1/2` and every ERROR variable to `0`. Every
//! `EQUAL` row reads `0 - 1/2 + 1/2 >= 0` and every `DIFFER` row reads
//! `0 + 1/2 + 1/2 >= 1`: both hold, with equality, and the objective is `0`.
//! Every objective coefficient is `+1` over `x >= 0`, so `LP* >= 0` too. `LP*`
//! is therefore exactly `0`, pinned from both sides with no float in the loop,
//! and weak duality caps EVERY dual floor at `ceil(0) = 0`. That is permanent
//! and this module does not touch it.
//!
//! The reason is a SYMMETRY: the instance is invariant under the global sign
//! flip `s -> 1 - s`, and `s = 1/2` is that involution's fixed point. It is
//! feasible for every parity row at zero cost, so the relaxation cannot see the
//! problem at all.
//!
//! `macrophage` was the named exemplar of the class this project recorded as
//! "genuine converged integrality gaps" and treated as uncertifiable. The
//! inference from "no LP bound reaches the optimum" to "no certificate exists"
//! is the error that has now failed four times, and it fails here too: cutting
//! planes has SATURATION and DIVISION, and neither has an LP dual.
//!
//! # The mathematics, in one paragraph
//!
//! Each error variable `e` sits over a node pair `(u, v)` in exactly two rows:
//!
//! ```text
//! EQUAL    e - u + v >= 0   and   e + u - v >=  0     =>  e >= XOR(u, v)
//! DIFFER   e + u + v >= 1   and   e - u - v >= -1     =>  e >= XNOR(u, v)
//! ```
//!
//! So the instance is a SIGNED GRAPH and the objective is its FRUSTRATION INDEX.
//! A cycle is FRUSTRATED when it has an odd number of `DIFFER` edges; no sign
//! assignment satisfies all of its edges, so at least one must be paid, and
//! `Σ_{e ∈ C} x_e >= 1` is valid. Walk the cycle and take, per edge, whichever
//! of its two rows has coefficient `s_i` at the entering node, propagating
//! `s_{i+1} = s_i` across `EQUAL` and `s_{i+1} = -s_i` across `DIFFER`. Every
//! interior node cancels; at the start node the coefficients REINFORCE to `±2`,
//! and they do so precisely because the cycle is frustrated. Three `pol` lines
//! finish it:
//!
//! ```text
//! A = Σ chosen rows          ->  Σ_C e + 2·v1  >= 1   --s-->  Σ_C e +  v1 >= 1
//! B = the mirrored sum       ->  Σ_C e + 2·~v1 >= 1   --s-->  Σ_C e + ~v1 >= 1
//! pol A B + 2 d ;            ->  2·Σ_C e >= 1         --d-->  Σ_C e >= 1
//! ```
//!
//! SATURATION IS THE WHOLE TRICK. The `+2` is the residue of a cycle whose sign
//! product is `-1`; an LP cannot drop it, because dropping a non-negative term
//! STRENGTHENS an inequality, which is exactly why the relaxation is stuck at the
//! half-integral point. Saturation caps it in one character, the mirrored pair
//! cancels `v1 + ~v1` into the constant `1`, and one division rounds `>= 1/2` up
//! to `>= 1`. The RHS of the un-saturated sum is `+1` for EVERY frustrated
//! cycle, whatever its length and wherever the `DIFFER` edges sit — the
//! alternating signs telescope — so the derivation is uniform and needs no case
//! analysis.
//!
//! Measured on `macrophage`: the cycle relaxation converges at `1120/3 =
//! 373.333…` and `ceil(1120/3) = 374` is the optimum. A family that buys
//! **0.0 %** of the gap in the original variable space buys **100 %** of it as a
//! proof.
//!
//! # Fail-closed, in four independent layers
//!
//! A certificate the checker accepts that does NOT establish the bound is the
//! worst defect this repository can ship, so nothing is emitted until all four
//! pass:
//!
//! 1. **O(1) pre-gate** ([`header_candidate`]). Three header integers — the
//!    variable count, the constraint count and the objective LENGTH — decide
//!    candidacy before a single constraint is touched. `#constraint` must be
//!    exactly twice `|objective|`, which off-family instances essentially never
//!    satisfy.
//! 2. **Total structural recovery** ([`recover`]). EVERY row and EVERY variable
//!    is accounted for against the two templates, or the module declines. A
//!    partially matched instance emits nothing.
//! 3. **Independent incumbent re-verification.** The incumbent is checked
//!    feasible against the ORIGINAL rows and equal to `optimum`, and the derived
//!    floor must equal `optimum` exactly — a packing that falls short is
//!    declined rather than published as a weaker bound, because this rung's
//!    contract is OPTIMALITY.
//! 4. **Self-check of the emitted BYTES** ([`self_check`]). The finished text is
//!    PARSED BACK and replayed through the shared cutting-planes interpreter
//!    ([`super::cp_replay`]) under VeriPB's normalized-literal semantics for `s`
//!    and `d`. The replay rebuilds every row from the instance, so a mis-cited
//!    id, a mis-ordered operand or a wrong multiplier cannot survive it. It then
//!    requires the cited row to be EXACTLY `Σ_e x_e >= optimum` over exactly the
//!    objective variables, requires the proof to contain no rule other than
//!    `pol` (so there is no extension variable and no assumption anywhere in
//!    it), and evaluates every replayed row at the incumbent, which is feasible:
//!    a feasible point falsifying a derived row would mean the derivation is
//!    unsound.
//!
//! Layers 2 and 4 together are a soundness argument that does not trust the
//! emitter: the proof is `pol`-only, so every line is a checked cutting-planes
//! inference from the instance's own rows, and the row it reaches mentions no
//! variable outside the objective.
//!
//! SOUNDNESS: this module returns proof *text* only, and it is not trusted until
//! the external PINNED VeriPB re-checks it (verify-before-claim). A `None` is a
//! withheld certificate and never changes the reported status.

mod packing;
#[cfg(test)]
mod tests;

use std::collections::BTreeMap;
use std::fmt::Write as _;

use self::packing::{floor_of, Limits, Packing, Walk};
use super::cp_replay::{eval_pol, CpRow};
use super::{evaluate_linear_objective, format_assignment};
use crate::proof::steps::{ConstraintId, ProofStep};
use crate::proof::veripb::{veripb_input_constraint_count, veripb_input_row_ids, VeriPbWriter};
use crate::types::{PbInstance, PbRel};

// ---------------------------------------------------------------------------
// Layer 1: the O(1) pre-gate.
// ---------------------------------------------------------------------------

/// The `(edges, nodes)` consistent with an instance's three header integers, or
/// `None`.
///
/// The family's shape fixes all three exactly: one error variable per edge and
/// one sign variable per node, one objective term per error variable, and two
/// rows per error variable.
///
/// ```text
/// |objective|  = E
/// #constraint  = 2E
/// #variable    = E + N
/// ```
///
/// so `E = #constraint / 2` must equal `|objective|` and `N = #variable - E`.
/// The last condition is that the signed graph can contain a cycle at all:
/// every node is an endpoint of some edge, so `E >= N` forces one (a forest on
/// `N` nodes has at most `N - 1` edges), and without a cycle there is no cut and
/// nothing to prove.
///
/// This is five integer operations on values the parser already has. There is no
/// loop and nothing is allocated, so an off-family instance pays for the gate
/// and nothing else.
fn header_candidate(num_vars: u64, num_constraints: u64, num_objective: u64) -> Option<(u64, u64)> {
    if !num_constraints.is_multiple_of(2) {
        return None;
    }
    let edges = num_constraints / 2;
    if edges < 2 || edges != num_objective {
        return None;
    }
    let nodes = num_vars.checked_sub(edges)?;
    if nodes < 2 || edges < nodes {
        return None;
    }
    Some((edges, nodes))
}

// ---------------------------------------------------------------------------
// Layer 2: total, fail-closed structure recovery.
// ---------------------------------------------------------------------------

/// One error variable and the two rows that define it.
pub(super) struct Edge {
    /// The error variable (an objective variable).
    var: u32,
    /// Endpoint node indices into [`SignedGraph::nodes`].
    u: usize,
    v: usize,
    /// `true` for the `DIFFER` template (`e >= XNOR(u, v)`), `false` for `EQUAL`.
    differ: bool,
    /// VeriPB input id of the row whose coefficient at `u` is `+1`.
    positive_row: u64,
    /// VeriPB input id of the row whose coefficient at `u` is `-1`.
    negative_row: u64,
}

/// A recovered signed graph. Construction accounts for every row and every
/// variable of the instance or fails.
pub(super) struct SignedGraph {
    /// Sign-variable ids, ascending. Index into this is a node index.
    nodes: Vec<u32>,
    /// Error variables in objective order.
    edges: Vec<Edge>,
}

impl SignedGraph {
    /// The input row to cite when the walk enters `node` wanting coefficient
    /// `sign` there.
    ///
    /// `EQUAL` rows have opposite coefficients at the two endpoints and `DIFFER`
    /// rows have equal ones, which is the entire content of the sign
    /// propagation: entering at `v` with sign `s` means the row's coefficient at
    /// `u` is `-s` across `EQUAL` and `+s` across `DIFFER`.
    fn row_for(&self, edge: usize, node: usize, sign: i8) -> Option<u64> {
        let e = self.edges.get(edge)?;
        let sign_at_u = if node == e.u {
            sign
        } else if node == e.v {
            if e.differ {
                sign
            } else {
                -sign
            }
        } else {
            return None;
        };
        Some(if sign_at_u > 0 {
            e.positive_row
        } else {
            e.negative_row
        })
    }
}

/// A single row reduced to `(error variable, [(node variable, coefficient); 2], rhs)`.
struct RowShape {
    error: u32,
    ends: [(u32, i128); 2],
    rhs: i128,
    id: u64,
}

/// Reduces one constraint to the family's row shape, or declines.
fn row_shape(
    constraint: &crate::types::PbConstraint,
    id: u64,
    is_objective_var: &dyn Fn(u32) -> bool,
) -> Option<RowShape> {
    if constraint.rel != PbRel::Ge || constraint.terms.len() != 3 {
        return None;
    }
    let mut error: Option<u32> = None;
    let mut ends: Vec<(u32, i128)> = Vec::with_capacity(2);
    for term in &constraint.terms {
        let [lit] = term.lits.as_slice() else {
            return None;
        };
        if lit.negated {
            return None;
        }
        if is_objective_var(lit.var) {
            if error.is_some() || term.coeff != 1 {
                return None;
            }
            error = Some(lit.var);
        } else {
            if term.coeff != 1 && term.coeff != -1 {
                return None;
            }
            ends.push((lit.var, term.coeff));
        }
    }
    let error = error?;
    let [a, b] = ends.as_slice() else {
        return None;
    };
    if a.0 == b.0 {
        return None;
    }
    let ends = if a.0 < b.0 { [*a, *b] } else { [*b, *a] };
    Some(RowShape {
        error,
        ends,
        rhs: constraint.rhs,
        id,
    })
}

/// Recovers the signed graph, accounting for EVERY row and EVERY variable.
///
/// Declines on the first thing it cannot explain. There is deliberately no
/// "mostly matched" path: a partial match is exactly the state in which an
/// emitter would write a derivation over rows it has misread.
fn recover(instance: &PbInstance) -> Option<SignedGraph> {
    let objective = instance.objective.as_ref()?;
    let (expected_edges, expected_nodes) = header_candidate(
        u64::from(instance.num_vars),
        instance.constraints.len() as u64,
        objective.terms.len() as u64,
    )?;

    // The objective must be a plain sum of unit payments over distinct variables.
    let mut error_vars: Vec<u32> = Vec::with_capacity(objective.terms.len());
    for term in &objective.terms {
        let [lit] = term.lits.as_slice() else {
            return None;
        };
        if lit.negated || term.coeff != 1 {
            return None;
        }
        error_vars.push(lit.var);
    }
    let mut sorted_errors = error_vars.clone();
    sorted_errors.sort_unstable();
    sorted_errors.dedup();
    if sorted_errors.len() != error_vars.len() {
        return None;
    }
    let is_error = |var: u32| sorted_errors.binary_search(&var).is_ok();

    // Every row, grouped by its error variable, in VeriPB input-id order.
    let ids = veripb_input_row_ids(instance).ok()?;
    let mut by_error: BTreeMap<u32, Vec<RowShape>> = BTreeMap::new();
    for (index, constraint) in instance.constraints.iter().enumerate() {
        let id = ids.get(index)?.get();
        let shape = row_shape(constraint, id, &is_error)?;
        let slot = by_error.entry(shape.error).or_default();
        if slot.len() == 2 {
            return None;
        }
        slot.push(shape);
    }
    if by_error.len() != error_vars.len() {
        return None;
    }

    // Node ids, in ascending order; index into this vector is the node index.
    let mut nodes: Vec<u32> = Vec::new();
    for shapes in by_error.values() {
        for shape in shapes {
            for (var, _) in shape.ends {
                nodes.push(var);
            }
        }
    }
    nodes.sort_unstable();
    nodes.dedup();
    if nodes.len() as u64 != expected_nodes {
        return None;
    }
    if nodes.iter().any(|&var| is_error(var)) {
        return None;
    }
    // Total accounting: every declared variable is a node or an edge, nothing
    // is declared twice and nothing is left over.
    if (nodes.len() + error_vars.len()) as u64 != u64::from(instance.num_vars) {
        return None;
    }
    if error_vars.len() as u64 != expected_edges {
        return None;
    }
    let node_index = |var: u32| nodes.binary_search(&var).ok();

    let mut edges: Vec<Edge> = Vec::with_capacity(error_vars.len());
    for &error in &error_vars {
        let shapes = by_error.get(&error)?;
        let [first, second] = shapes.as_slice() else {
            return None;
        };
        if first.ends[0].0 != second.ends[0].0 || first.ends[1].0 != second.ends[1].0 {
            return None;
        }
        let u_var = first.ends[0].0;
        let v_var = first.ends[1].0;
        let signature = {
            let mut pair = [
                (first.ends[0].1, first.ends[1].1, first.rhs, first.id),
                (second.ends[0].1, second.ends[1].1, second.rhs, second.id),
            ];
            pair.sort_by_key(|entry| (entry.0, entry.1, entry.2));
            pair
        };
        // EQUAL: (-1,+1,0) and (+1,-1,0).  DIFFER: (-1,-1,-1) and (+1,+1,+1).
        let (differ, negative_row, positive_row) = match signature {
            [(-1, 1, 0, low), (1, -1, 0, high)] => (false, low, high),
            [(-1, -1, -1, low), (1, 1, 1, high)] => (true, low, high),
            _ => return None,
        };
        edges.push(Edge {
            var: error,
            u: node_index(u_var)?,
            v: node_index(v_var)?,
            differ,
            positive_row,
            negative_row,
        });
    }

    Some(SignedGraph { nodes, edges })
}

// ---------------------------------------------------------------------------
// Layer 3: the incumbent, re-verified against the ORIGINAL rows.
// ---------------------------------------------------------------------------

/// `true` iff `assignment` is complete for the instance and satisfies every row.
fn incumbent_is_feasible(instance: &PbInstance, assignment: &[bool]) -> bool {
    if assignment.len() < instance.num_vars as usize {
        return false;
    }
    instance.constraints.iter().all(|constraint| {
        let mut total: i128 = 0;
        for term in &constraint.terms {
            let mut satisfied = true;
            for lit in &term.lits {
                let Some(&value) = assignment.get((lit.var as usize).wrapping_sub(1)) else {
                    return false;
                };
                if !(value ^ lit.negated) {
                    satisfied = false;
                    break;
                }
            }
            if satisfied {
                total += term.coeff;
            }
        }
        match constraint.rel {
            PbRel::Ge => total >= constraint.rhs,
            PbRel::Eq => total == constraint.rhs,
        }
    })
}

// ---------------------------------------------------------------------------
// Emission.
// ---------------------------------------------------------------------------

/// The rows to sum for one polarity of one cycle, as VeriPB input ids.
fn chain(graph: &SignedGraph, walk: &Walk, polarity: i8) -> Option<Vec<u64>> {
    let mut sign = polarity;
    let mut ids = Vec::with_capacity(walk.len());
    for &(edge, from) in walk {
        ids.push(graph.row_for(edge, from, sign)?);
        if graph.edges.get(edge)?.differ {
            sign = -sign;
        }
    }
    Some(ids)
}

/// `r1 r2 + r3 + … + s ;` — the summed chain, saturated.
fn chain_expression(ids: &[u64]) -> Option<String> {
    let (first, rest) = ids.split_first()?;
    let mut expression = first.to_string();
    for id in rest {
        write!(expression, " {id} +").ok()?;
    }
    expression.push_str(" s ;");
    Some(expression)
}

fn emit(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
    graph: &SignedGraph,
    packing: &Packing,
) -> Option<(String, u64)> {
    let input_count = veripb_input_constraint_count(instance).ok()?;
    let mut writer = VeriPbWriter::new(Vec::<u8>::new(), input_count).ok()?;

    let mut cuts: Vec<(ConstraintId, i128)> = Vec::new();
    for (index, walk) in packing.walks.iter().enumerate() {
        let multiplier = *packing.numerators.get(index)?;
        if multiplier <= 0 {
            continue;
        }
        let forward = chain(graph, walk, 1)?;
        let mirrored = chain(graph, walk, -1)?;
        let a = writer
            .log_step(ProofStep::Polynomial(chain_expression(&forward)?))
            .ok()?;
        let b = writer
            .log_step(ProofStep::Polynomial(chain_expression(&mirrored)?))
            .ok()?;
        let cut = writer
            .log_step(ProofStep::Polynomial(format!("{a} {b} + 2 d ;")))
            .ok()?;
        cuts.push((cut, multiplier));
    }
    let ((first_cut, first_multiplier), rest) = cuts.split_first()?;
    let mut expression = format!("{first_cut} {first_multiplier} *");
    for (cut, multiplier) in rest {
        write!(expression, " {cut} {multiplier} * +").ok()?;
    }
    // Slack fill with LITERAL AXIOMS (`xN` as a `pol` operand is the constraint
    // `xN >= 0`), lifting every objective coefficient to the denominator so the
    // single final division yields the objective row itself. No `rup` and no
    // `red` appears anywhere in this proof.
    for (index, edge) in graph.edges.iter().enumerate() {
        let missing = packing.denominator.checked_sub(*packing.load.get(index)?)?;
        if missing < 0 {
            return None;
        }
        if missing > 0 {
            write!(expression, " x{} {missing} * +", edge.var).ok()?;
        }
    }
    expression.push_str(" ;");
    let summed = writer.log_step(ProofStep::Polynomial(expression)).ok()?;
    let floor = writer
        .log_step(ProofStep::Polynomial(format!(
            "{summed} {} d ;",
            packing.denominator
        )))
        .ok()?;

    writer.set_opt_bounds(optimum, optimum).ok()?;
    writer
        .conclude_opt_hinted(Some(floor), Some(&format_assignment(incumbent)))
        .ok()?;
    let text = String::from_utf8(writer.into_inner()).ok()?;
    Some((text, floor.get()))
}

// ---------------------------------------------------------------------------
// Layer 4: parse the emitted bytes back and replay them.
// ---------------------------------------------------------------------------

// `DECLINE` records the first refusal site under test so a failure is
// diagnosable instead of a bare `false`; production reads only success/failure.
#[cfg(test)]
thread_local! {
    static DECLINE: std::cell::RefCell<Option<&'static str>> =
        const { std::cell::RefCell::new(None) };
}

fn decline<T>(_site: &'static str) -> Option<T> {
    #[cfg(test)]
    DECLINE.with(|slot| {
        let mut slot = slot.borrow_mut();
        if slot.is_none() {
            *slot = Some(_site);
        }
    });
    None
}

/// Replays the emitted proof text and returns `true` only if those BYTES
/// establish `Σ_e x_e >= optimum` for THIS instance.
fn self_check(
    text: &str,
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
    floor_id: u64,
) -> bool {
    self_check_inner(text, instance, incumbent, optimum, floor_id).is_some()
}

#[allow(clippy::too_many_lines)]
fn self_check_inner(
    text: &str,
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
    floor_id: u64,
) -> Option<()> {
    let mut lines = text.lines();
    if lines.next()? != "pseudo-Boolean proof version 3.0" {
        return decline("header");
    }
    let f_line: Vec<&str> = lines.next()?.split_whitespace().collect();
    if f_line.first()? != &"f" {
        return decline("f-line");
    }
    let declared: u64 = f_line.get(1)?.parse().ok()?;
    if declared != veripb_input_constraint_count(instance).ok()? {
        return decline("f-count");
    }

    // Seed the database with the input rows at the ids VeriPB gives them. Every
    // row of this family is a `>=` row, so the `=` split cannot arise; refuse
    // rather than assume if one ever does.
    let ids = veripb_input_row_ids(instance).ok()?;
    let mut db: BTreeMap<u64, CpRow> = BTreeMap::new();
    for (index, constraint) in instance.constraints.iter().enumerate() {
        if constraint.rel != PbRel::Ge {
            return decline("input-row-not-ge");
        }
        let mut row = CpRow {
            coeff: BTreeMap::new(),
            rhs: constraint.rhs,
        };
        for term in &constraint.terms {
            let [lit] = term.lits.as_slice() else {
                return decline("input-row-nonlinear");
            };
            if lit.negated {
                row.add_coeff(lit.var, term.coeff.checked_neg()?)?;
                row.rhs = row.rhs.checked_sub(term.coeff)?;
            } else {
                row.add_coeff(lit.var, term.coeff)?;
            }
        }
        db.insert(ids.get(index)?.get(), row);
    }

    let mut next_id = declared.checked_add(1)?;
    let mut conclusion: Option<String> = None;
    let mut saw_end = false;
    for line in lines {
        let line = line.trim_end();
        if line == "output NONE;" {
            continue;
        }
        if line == "end pseudo-Boolean proof;" {
            saw_end = true;
            break;
        }
        if let Some(rest) = line.strip_prefix("conclusion ") {
            if conclusion.is_some() {
                return decline("second-conclusion");
            }
            conclusion = Some(rest.to_string());
            continue;
        }
        // `pol` ONLY. No `red`, no `rup`, no `soli`, no `del`: every derived row
        // is then a checked cutting-planes inference from the instance's own
        // rows, there is no extension variable anywhere, and nothing in the
        // proof is an assumption. Anything else is refused rather than modelled.
        let Some(expression) = line.strip_prefix("pol ") else {
            return decline("non-pol-rule");
        };
        if conclusion.is_some() {
            return decline("rule-after-conclusion");
        }
        let body = expression.strip_suffix(';')?.trim_end();
        let (row, _used) = eval_pol(body, &db)?;
        // A feasible point must satisfy every row a sound derivation produces.
        if !row.holds(incumbent) {
            return decline("derived-row-false-at-incumbent");
        }
        db.insert(next_id, row);
        next_id = next_id.checked_add(1)?;
    }
    if !saw_end {
        return decline("missing-end");
    }

    // The row the conclusion cites must be the objective floor itself: unit
    // coefficient on every objective variable, nothing else, degree `optimum`.
    let floor = db.get(&floor_id)?;
    if floor.rhs != optimum {
        return decline("floor-degree");
    }
    let objective = instance.objective.as_ref()?;
    if floor.coeff.len() != objective.terms.len() {
        return decline("floor-support");
    }
    for term in &objective.terms {
        let [lit] = term.lits.as_slice() else {
            return decline("objective-nonlinear");
        };
        if lit.negated || term.coeff != 1 {
            return decline("objective-not-unit");
        }
        if floor.coeff.get(&lit.var) != Some(&1) {
            return decline("floor-coefficient");
        }
    }

    // `BOUNDS <lb> : <id> <ub> : <witness>;`
    let conclusion = conclusion?;
    let rest = conclusion.strip_prefix("BOUNDS ")?;
    let body = rest.strip_suffix(';')?;
    let (lower_part, upper_part) = body.split_once(" : ")?;
    let lower: i128 = lower_part.trim().parse().ok()?;
    if lower != optimum {
        return decline("conclusion-lower");
    }
    let (hint, upper_rest) = upper_part.split_once(' ')?;
    if hint.trim().parse::<u64>().ok()? != floor_id {
        return decline("conclusion-hint");
    }
    let (upper, witness) = upper_rest.split_once(" : ")?;
    if upper.trim().parse::<i128>().ok()? != optimum {
        return decline("conclusion-upper");
    }
    if witness.trim() != format_assignment(incumbent) {
        return decline("conclusion-witness");
    }
    Some(())
}

// ---------------------------------------------------------------------------
// Entry point.
// ---------------------------------------------------------------------------

/// Certifies an OPT-LIN optimum for the signed-graph frustration-index family.
///
/// Returns proof text, or `None` for any instance that is not exactly this
/// family, any incumbent that does not re-verify, and any packing whose floor
/// falls short of `optimum` — this rung's contract is OPTIMALITY, so a genuine
/// but weaker certified lower bound is withheld rather than published as one.
pub fn certify_opt_lin_frustrated_cycle(
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

    let packing = packing::build(&graph, optimum, limits)?;
    if floor_of(&packing) != optimum {
        return None;
    }
    let (text, floor_id) = emit(instance, incumbent, optimum, &graph, &packing)?;
    if !self_check(&text, instance, incumbent, optimum, floor_id) {
        return None;
    }
    Some(text)
}
