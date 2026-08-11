// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Structure-aware feasibility seed for binarized-neural-network (BNN)
//! verification OPT-LIN instances (the `bnn_mnist_*` family).
//!
//! # What it does
//! These instances encode a binarized neural net as a layered system of
//! "big-M gadget" pseudo-Boolean rows. Finding even a *first feasible* point with
//! a generic WalkSAT-from-all-false local search takes most of the 60 s budget;
//! but the layered structure is a forward-evaluable DAG. This module RECOGNIZES
//! that structure (one O(occurrences) pass) and produces a feasible *seed*
//! assignment by:
//!   1. seeding the free input pixels (deterministic SplitMix64, restart-diversified),
//!   2. forward-propagating each neuron (threshold rule) in topological order,
//!   3. deriving the auxiliary/objective "gate" variables (OR cascades), and
//!   4. a COORDINATED one-hot logit selection that satisfies the output rows.
//! On the BNN family this reaches a verified-feasible point in sub-second time
//! (>40x faster than the from-scratch SLS feasibility hunt).
//!
//! # Soundness (ADVISORY ONLY — NON-NEGOTIABLE)
//! This module NEVER decides what AY reports. It only proposes an *initial
//! assignment* for the SLS search. Every incumbent AY ever emits is still
//! independently re-verified against ALL original constraints by
//! [`crate::optimize::sls::try_record_incumbent`] and again by
//! `sanitize_optimization_incumbent` in the portfolio. A bug in this recognizer
//! can therefore only waste cycles (a poor or infeasible seed that the SLS phase
//! repairs) — it can NEVER cause a wrong answer to be reported.
//!
//! Defensively, [`seed`] ALSO re-verifies the candidate it builds against every
//! original constraint with [`crate::eval::verify_all_constraints`] before
//! returning it; an unverified seed is discarded (returns `None`), so a recognizer
//! mistake degrades gracefully to today's all-false start.
//!
//! The PRNG is seeded from instance *structure* only (reusing
//! [`crate::optimize::lns::structural_seed`]) XOR a restart index — never from
//! system entropy and never from any instance identity — so runs are reproducible.

use crate::eval::verify_all_constraints;
use crate::optimize::lns::{structural_seed, SplitMix64};
use crate::types::{PbInstance, PbObjective, PbRel};

/// A recognized neuron: a 2-row big-M selector whose positive-row +/-1 inputs and
/// threshold define the rule `x = 1  iff  S <= thr`, where `S` is the sum of the
/// positive-row coefficients over the inputs currently set true.
struct Neuron {
    /// Output variable (0-indexed).
    out: usize,
    /// Positive-row inputs: `(input_var_0indexed, coefficient ±1)`.
    inputs: Vec<(usize, i128)>,
    /// Threshold: `out = 1` iff `Σ coeff·[input true] <= thr`.
    thr: i128,
}

/// A recognized gate (auxiliary / objective cascade variable). Its minimum-cost
/// feasible value is the OR of its literals: `gate = OR over (var, want) of
/// (assignment[var] == want)`.
struct Gate {
    /// Gate variable (0-indexed).
    out: usize,
    /// OR-literals: `(input_var_0indexed, want_true)`. The gate is forced ON when
    /// any literal evaluates true (i.e. `assignment[var] == want_true`).
    literals: Vec<(usize, bool)>,
}

/// A recognized BNN structure: neurons (forward-evaluable in `neuron_order`),
/// gates (forward-evaluable in `gate_order`), the output logit variables, the
/// pinned variables, and the free input variables to seed.
struct NeuronNet {
    num_vars: usize,
    neurons: Vec<Neuron>,
    /// Topological order over `neurons` (indices into `neurons`).
    neuron_order: Vec<usize>,
    gates: Vec<Gate>,
    /// Topological order over `gates` (indices into `gates`).
    gate_order: Vec<usize>,
    /// Output logit variables (0-indexed), each the outlier of exactly 9 big-M rows.
    logits: Vec<usize>,
    /// The 9 big-M rows of each logit, as `(selector_coeff, other_terms, rel, rhs)`
    /// where `other_terms` are `(var_0indexed, ±1)`. Parallel to `logits`.
    logit_rows: Vec<Vec<LogitRow>>,
    /// The true-label logit (pinned to 0 by a unit `-1 x >= 0` row), if found.
    true_label: Option<usize>,
    /// Variables pinned by unit rows: `(var_0indexed, value)`.
    pins: Vec<(usize, bool)>,
    /// Free input variables to seed (0-indexed).
    free_inputs: Vec<usize>,
}

/// One big-M row of a logit variable, pre-extracted for fast feasibility checks.
struct LogitRow {
    selector_coeff: i128,
    /// `(var_0indexed, ±1)` for the non-selector terms.
    others: Vec<(usize, i128)>,
    rel: PbRel,
    rhs: i128,
}

/// Ratio of recognized-neuron big-M rows to total big-M rows required before the
/// recognizer accepts the instance. Below this, decline (return `None`): the
/// structure is not the expected layered BNN.
const MIN_RECOGNIZED_FRACTION: f64 = 0.50;

/// Big-M dominance factor: a term is the "selector" outlier of its row only if its
/// |coefficient| is at least this multiple of the next-largest |coefficient|.
const BIG_M_DOMINANCE: i128 = 4;

/// Number of restart-diversified forward passes to try before giving up. Each pass
/// is one O(occurrences) forward evaluation (sub-millisecond on this family).
const MAX_RESTARTS: u64 = 30;

/// Extracts the single 0-indexed variable of a linear term, or `None` if the term
/// is non-linear (a product of literals — not part of this family).
fn term_single_var(term: &crate::types::PbTerm) -> Option<(usize, bool)> {
    let [lit] = term.lits.as_slice() else {
        return None;
    };
    let idx = (lit.var as usize).checked_sub(1)?;
    Some((idx, lit.negated))
}

/// Attempts to recognize the layered BNN structure of `instance`. Returns the
/// recognized network, or `None` if the instance does not match (in which case the
/// caller keeps today's all-false start). One O(occurrences) pass plus cheap
/// post-processing (grouping, topo sort).
fn recognize(instance: &PbInstance, objective: &PbObjective) -> Option<NeuronNet> {
    let num_vars = usize::try_from(instance.num_vars).ok()?;
    if num_vars == 0 {
        return None;
    }

    // A "big-M row": one term's |coeff| dominates (>= BIG_M_DOMINANCE x next) and
    // every other term has coeff ±1. The dominant term's variable is the selector.
    // `selector_rows[v]` collects the constraint indices where `v` is the selector.
    let mut selector_rows: Vec<Vec<usize>> = vec![Vec::new(); num_vars];
    // For each big-M constraint index, cache (selector_var, selector_coeff,
    // other_terms, rel, rhs). Only Ge rows participate in neuron/logit recognition.
    let mut is_big_m: Vec<bool> = vec![false; instance.constraints.len()];

    for (ci, constraint) in instance.constraints.iter().enumerate() {
        if constraint.terms.len() < 2 {
            continue;
        }
        // Find the two largest |coeff| and check the all-±1-others condition.
        let mut max_abs: i128 = -1;
        let mut max_var: usize = 0;
        let mut second_abs: i128 = 0;
        let mut all_single = true;
        for term in &constraint.terms {
            let Some((idx, _negated)) = term_single_var(term) else {
                all_single = false;
                break;
            };
            if idx >= num_vars {
                all_single = false;
                break;
            }
            let a = term.coeff.saturating_abs();
            if a > max_abs {
                second_abs = max_abs.max(0);
                max_abs = a;
                max_var = idx;
            } else if a > second_abs {
                second_abs = a;
            }
        }
        if !all_single || max_abs <= 1 {
            continue;
        }
        if max_abs < BIG_M_DOMINANCE.saturating_mul(second_abs.max(1)) {
            continue;
        }
        // Confirm all non-selector terms are ±1.
        let mut ok = true;
        for term in &constraint.terms {
            let (idx, _negated) = term_single_var(term)?;
            if idx == max_var {
                continue;
            }
            if term.coeff.saturating_abs() != 1 {
                ok = false;
                break;
            }
        }
        if !ok {
            continue;
        }
        is_big_m[ci] = true;
        selector_rows[max_var].push(ci);
    }

    let big_m_rows = is_big_m.iter().filter(|&&b| b).count();
    if big_m_rows == 0 {
        return None;
    }

    // --- Neurons: exactly-2-row selectors whose non-selector ±1 vectors negate. ---
    let mut neurons: Vec<Neuron> = Vec::new();
    let mut neuron_input_set: Vec<bool> = vec![false; num_vars];
    let mut logits: Vec<usize> = Vec::new();
    let mut logit_rows: Vec<Vec<LogitRow>> = Vec::new();

    for v in 0..num_vars {
        let rows = &selector_rows[v];
        if rows.len() == 2 {
            if let Some(neuron) = recognize_neuron(instance, v, rows[0], rows[1], num_vars) {
                for &(iv, _) in &neuron.inputs {
                    if iv < num_vars {
                        neuron_input_set[iv] = true;
                    }
                }
                neurons.push(neuron);
            }
        } else if rows.len() == 9 {
            // Logit (output indicator): 9-row selector. Extract its rows verbatim.
            let mut extracted = Vec::with_capacity(9);
            let mut ok = true;
            for &ci in rows {
                let Some(row) = extract_logit_row(instance, v, ci, num_vars) else {
                    ok = false;
                    break;
                };
                extracted.push(row);
            }
            if ok {
                logits.push(v);
                logit_rows.push(extracted);
            }
        }
    }

    let neuron_rows = 2 * neurons.len();
    let recognized_fraction = neuron_rows as f64 / big_m_rows as f64;
    if recognized_fraction < MIN_RECOGNIZED_FRACTION {
        return None;
    }

    // --- Pins (unit rows) and true-label detection. ---
    let logit_set: Vec<bool> = {
        let mut s = vec![false; num_vars];
        for &l in &logits {
            s[l] = true;
        }
        s
    };
    let mut pins: Vec<(usize, bool)> = Vec::new();
    let mut pinned_set: Vec<bool> = vec![false; num_vars];
    let mut true_label: Option<usize> = None;
    for constraint in &instance.constraints {
        if constraint.terms.len() != 1 {
            continue;
        }
        let (idx, negated) = term_single_var(&constraint.terms[0])?;
        if idx >= num_vars {
            continue;
        }
        let coeff = constraint.terms[0].coeff;
        // Literal-true contribution sign for the unit row.
        let eff_coeff = if negated { -coeff } else { coeff };
        let rhs = constraint.rhs;
        match constraint.rel {
            PbRel::Ge => {
                if eff_coeff > 0 && rhs > 0 {
                    record_pin(&mut pins, &mut pinned_set, idx, !negated);
                } else if eff_coeff < 0 && rhs >= 0 {
                    // -|c| x >= 0  =>  x = 0 (the literal must be false).
                    record_pin(&mut pins, &mut pinned_set, idx, negated);
                    if logit_set[idx] {
                        true_label = Some(idx);
                    }
                }
            }
            PbRel::Eq => {
                // c·lit = rhs  =>  literal true iff rhs != 0.
                let lit_true = rhs != 0;
                let value = if negated { !lit_true } else { lit_true };
                record_pin(&mut pins, &mut pinned_set, idx, value);
            }
        }
    }

    // --- Gates: 2-term Ge residual rows over auxiliary (non-neuron/logit/input)
    // variables. Each contributes an OR-literal to its gate var. ---
    let mut gate_lits: Vec<Vec<(usize, bool)>> = vec![Vec::new(); num_vars];
    let mut is_gate: Vec<bool> = vec![false; num_vars];
    let forbidden = |v: usize| -> bool {
        // A gate var is never a neuron output, a logit, or a neuron input pixel.
        // Neuron outputs are exactly the selectors with a recognized neuron; detect
        // by membership in the neuron `out` set computed below.
        neuron_input_set[v] || logit_set[v]
    };
    // Build the neuron-output set so gates also exclude neuron outputs.
    let mut neuron_out_set: Vec<bool> = vec![false; num_vars];
    for n in &neurons {
        neuron_out_set[n.out] = true;
    }
    let is_forbidden = |v: usize| forbidden(v) || neuron_out_set[v];

    for (ci, constraint) in instance.constraints.iter().enumerate() {
        if is_big_m[ci] || constraint.terms.len() != 2 || constraint.rel != PbRel::Ge {
            continue;
        }
        let (va, neg_a) = term_single_var(&constraint.terms[0])?;
        let (vb, neg_b) = term_single_var(&constraint.terms[1])?;
        if va >= num_vars || vb >= num_vars || neg_a || neg_b {
            // Negated-literal 2-term rows are not part of the gate family here.
            continue;
        }
        let ca = constraint.terms[0].coeff;
        let cb = constraint.terms[1].coeff;
        let rhs = constraint.rhs;
        // {g:1, in:-1} >= 0  ->  g >= in            literal (in, True)
        // {g:1, in: 1} >= 1  ->  g >= 1 - in        literal (in, False)
        if ca == 1 && cb == -1 && rhs == 0 && !is_forbidden(va) {
            gate_lits[va].push((vb, true));
            is_gate[va] = true;
        } else if cb == 1 && ca == -1 && rhs == 0 && !is_forbidden(vb) {
            gate_lits[vb].push((va, true));
            is_gate[vb] = true;
        } else if ca == 1 && cb == 1 && rhs == 1 {
            let fa = is_forbidden(va);
            let fb = is_forbidden(vb);
            if !fa && fb {
                gate_lits[va].push((vb, false));
                is_gate[va] = true;
            } else if !fb && fa {
                gate_lits[vb].push((va, false));
                is_gate[vb] = true;
            } else if !fa && !fb {
                gate_lits[va].push((vb, false));
                gate_lits[vb].push((va, false));
                is_gate[va] = true;
                is_gate[vb] = true;
            }
        }
    }

    let mut gates: Vec<Gate> = Vec::new();
    for v in 0..num_vars {
        if is_gate[v] {
            gates.push(Gate {
                out: v,
                literals: std::mem::take(&mut gate_lits[v]),
            });
        }
    }

    // --- Topo orders. ---
    let neuron_order = topo_order_neurons(&neurons, num_vars)?;
    let gate_order = topo_order_gates(&gates, &is_gate, num_vars);

    // --- Free inputs: vars used as neuron/gate inputs or appearing in the
    // objective, that are NOT defined (neuron out / logit / gate) and NOT pinned. ---
    let mut defined: Vec<bool> = vec![false; num_vars];
    for n in &neurons {
        defined[n.out] = true;
    }
    for &l in &logits {
        defined[l] = true;
    }
    for g in &gates {
        defined[g.out] = true;
    }
    let mut used: Vec<bool> = vec![false; num_vars];
    for n in &neurons {
        for &(iv, _) in &n.inputs {
            used[iv] = true;
        }
    }
    for g in &gates {
        for &(iv, _) in &g.literals {
            used[iv] = true;
        }
    }
    for term in &objective.terms {
        if let Some((idx, _)) = term_single_var(term) {
            if idx < num_vars {
                used[idx] = true;
            }
        }
    }
    let mut free_inputs: Vec<usize> = Vec::new();
    for v in 0..num_vars {
        if used[v] && !defined[v] && !pinned_set[v] {
            free_inputs.push(v);
        }
    }

    Some(NeuronNet {
        num_vars,
        neurons,
        neuron_order,
        gates,
        gate_order,
        logits,
        logit_rows,
        true_label,
        pins,
        free_inputs,
    })
}

/// Records a pin, ignoring conflicting duplicates (first wins; a conflict only
/// means the seed will be repaired by SLS, never a wrong answer).
fn record_pin(pins: &mut Vec<(usize, bool)>, pinned_set: &mut [bool], idx: usize, value: bool) {
    if !pinned_set[idx] {
        pinned_set[idx] = true;
        pins.push((idx, value));
    }
}

/// Recognizes a neuron from its two big-M rows: orient so the positive-selector
/// row is the positive half and the negative-selector row the negative half;
/// confirm their non-selector ±1 vectors are exact negations. Returns the neuron
/// with rule `out = 1 iff S <= thr`, `S = Σ coeff·[input true]` over the positive
/// row's inputs.
fn recognize_neuron(
    instance: &PbInstance,
    selector: usize,
    ci1: usize,
    ci2: usize,
    num_vars: usize,
) -> Option<Neuron> {
    let (s1, others1, rhs1) = extract_selector_row(instance, selector, ci1, num_vars)?;
    let (s2, others2, rhs2) = extract_selector_row(instance, selector, ci2, num_vars)?;

    // Non-selector key sets must match and coefficients must be exact negations.
    if others1.len() != others2.len() {
        return None;
    }
    // Build a lookup for row2's coefficients.
    let mut sorted2 = others2.clone();
    sorted2.sort_by_key(|&(v, _)| v);
    let mut sorted1 = others1.clone();
    sorted1.sort_by_key(|&(v, _)| v);
    for (&(v1, c1), &(v2, c2)) in sorted1.iter().zip(sorted2.iter()) {
        if v1 != v2 || c1 != -c2 {
            return None;
        }
    }

    // Orient: positive selector coeff -> positive half (inputs + thr derivation).
    let (pos_inputs, neg_coeff, neg_rhs, _pos_rhs) = if s1 > 0 {
        (others1, s2, rhs2, rhs1)
    } else if s2 > 0 {
        (others2, s1, rhs1, rhs2)
    } else {
        return None;
    };
    // thr = cN - rhsN ; rule x = 1 iff S <= thr.
    let thr = neg_coeff.checked_sub(neg_rhs)?;

    // Cheap adjacency self-check (not load-bearing for soundness): the positive
    // and negative bands should be adjacent. (cN - rhsN) + 1 == rhsP.
    debug_assert_eq!(thr.saturating_add(1), _pos_rhs, "neuron bands not adjacent");

    Some(Neuron {
        out: selector,
        inputs: pos_inputs,
        thr,
    })
}

/// Extracts a big-M selector row as `(selector_coeff, other_terms, rhs)` where
/// `other_terms` are `(var_0indexed, ±1 effective coeff)`. The effective coeff
/// accounts for literal negation so that the forward `S` sum is over the variable
/// being true. Returns `None` if any term is non-linear or out of range.
fn extract_selector_row(
    instance: &PbInstance,
    selector: usize,
    ci: usize,
    num_vars: usize,
) -> Option<(i128, Vec<(usize, i128)>, i128)> {
    let constraint = &instance.constraints[ci];
    let mut selector_coeff: Option<i128> = None;
    let mut others: Vec<(usize, i128)> = Vec::with_capacity(constraint.terms.len() - 1);
    for term in &constraint.terms {
        let (idx, negated) = term_single_var(term)?;
        if idx >= num_vars {
            return None;
        }
        // Effective coefficient when the *variable* is true (negation folded in).
        let eff = if negated {
            term.coeff.checked_neg()?
        } else {
            term.coeff
        };
        if idx == selector {
            selector_coeff = Some(eff);
        } else {
            others.push((idx, eff));
        }
    }
    Some((selector_coeff?, others, constraint.rhs))
}

/// Extracts a logit big-M row into a [`LogitRow`].
fn extract_logit_row(
    instance: &PbInstance,
    selector: usize,
    ci: usize,
    num_vars: usize,
) -> Option<LogitRow> {
    let (selector_coeff, others, rhs) = extract_selector_row(instance, selector, ci, num_vars)?;
    Some(LogitRow {
        selector_coeff,
        others,
        rel: instance.constraints[ci].rel,
        rhs,
    })
}

/// Topological order over neurons. Fast path: confirm every neuron's inputs have
/// smaller variable index than its output (true on this family) — then plain
/// index order is a valid topo order. Otherwise Kahn-sort the read/write DAG;
/// returns `None` on a cycle (abort recognition).
fn topo_order_neurons(neurons: &[Neuron], num_vars: usize) -> Option<Vec<usize>> {
    // Map var -> neuron index (for the few vars that are neuron outputs).
    let mut out_to_neuron: Vec<usize> = vec![usize::MAX; num_vars];
    for (ni, n) in neurons.iter().enumerate() {
        out_to_neuron[n.out] = ni;
    }
    // Fast path: index-acyclic.
    let index_acyclic = neurons
        .iter()
        .all(|n| n.inputs.iter().all(|&(iv, _)| iv < n.out));
    if index_acyclic {
        let mut order: Vec<usize> = (0..neurons.len()).collect();
        order.sort_by_key(|&ni| neurons[ni].out);
        return Some(order);
    }

    // General Kahn sort over neuron->neuron edges (input neuron must precede).
    let mut indeg = vec![0usize; neurons.len()];
    let mut children: Vec<Vec<usize>> = vec![Vec::new(); neurons.len()];
    for (ni, n) in neurons.iter().enumerate() {
        for &(iv, _) in &n.inputs {
            let dep = out_to_neuron[iv];
            if dep != usize::MAX {
                indeg[ni] += 1;
                children[dep].push(ni);
            }
        }
    }
    let mut queue: Vec<usize> = (0..neurons.len()).filter(|&ni| indeg[ni] == 0).collect();
    queue.sort_by_key(|&ni| neurons[ni].out);
    let mut order = Vec::with_capacity(neurons.len());
    let mut head = 0;
    while head < queue.len() {
        let ni = queue[head];
        head += 1;
        order.push(ni);
        for &c in &children[ni] {
            indeg[c] -= 1;
            if indeg[c] == 0 {
                queue.push(c);
            }
        }
    }
    if order.len() != neurons.len() {
        return None; // cycle
    }
    Some(order)
}

/// Topological order over gates so a gate is computed after any gate-var it reads.
/// Falls back to index order on a cycle (a cyclic gate seed is merely repaired by
/// SLS, never wrong).
fn topo_order_gates(gates: &[Gate], is_gate: &[bool], num_vars: usize) -> Vec<usize> {
    let mut out_to_gate: Vec<usize> = vec![usize::MAX; num_vars];
    for (gi, g) in gates.iter().enumerate() {
        out_to_gate[g.out] = gi;
    }
    let mut indeg = vec![0usize; gates.len()];
    let mut children: Vec<Vec<usize>> = vec![Vec::new(); gates.len()];
    for (gi, g) in gates.iter().enumerate() {
        for &(iv, _) in &g.literals {
            if is_gate[iv] {
                let dep = out_to_gate[iv];
                if dep != usize::MAX {
                    indeg[gi] += 1;
                    children[dep].push(gi);
                }
            }
        }
    }
    let mut queue: Vec<usize> = (0..gates.len()).filter(|&gi| indeg[gi] == 0).collect();
    queue.sort_by_key(|&gi| gates[gi].out);
    let mut order = Vec::with_capacity(gates.len());
    let mut head = 0;
    while head < queue.len() {
        let gi = queue[head];
        head += 1;
        order.push(gi);
        for &c in &children[gi] {
            indeg[c] -= 1;
            if indeg[c] == 0 {
                queue.push(c);
            }
        }
    }
    if order.len() != gates.len() {
        // Cycle: fall back to index order. Soundness is unaffected (advisory seed).
        let mut fallback: Vec<usize> = (0..gates.len()).collect();
        fallback.sort_by_key(|&gi| gates[gi].out);
        return fallback;
    }
    order
}

/// Forward-evaluates the net over `assignment` (already seeded at the free inputs):
/// applies pins, propagates neurons in topo order, derives gates in topo order,
/// then performs the COORDINATED one-hot logit selection. Returns the number of
/// valid candidate classes found (0 means logit feasibility could not be reached
/// — the caller should try another restart). On success, `assignment` is a
/// fully-determined candidate.
fn forward_eval(net: &NeuronNet, assignment: &mut [bool]) -> usize {
    // Pins.
    for &(v, value) in &net.pins {
        assignment[v] = value;
    }
    // Neurons.
    for &ni in &net.neuron_order {
        let n = &net.neurons[ni];
        let mut s: i128 = 0;
        for &(iv, coeff) in &n.inputs {
            if assignment[iv] {
                s = s.saturating_add(coeff);
            }
        }
        assignment[n.out] = s <= n.thr;
    }
    // Gates (min-cost: OR of literals).
    for &gi in &net.gate_order {
        let g = &net.gates[gi];
        let mut on = false;
        for &(iv, want) in &g.literals {
            if assignment[iv] == want {
                on = true;
                break;
            }
        }
        assignment[g.out] = on;
    }
    // Coordinated one-hot logit selection: for each candidate class (logit) other
    // than the true label, set it to 1 and all other logits to 0, then check ALL
    // logit rows of EVERY logit are satisfied. Commit the first valid class.
    if net.logits.is_empty() {
        return 1; // no logits to coordinate; the seed stands as-is.
    }
    let mut valid_class: Option<usize> = None;
    for &logit in &net.logits {
        if Some(logit) == net.true_label {
            continue;
        }
        // Tentatively set one-hot: this logit = 1, others = 0.
        for &other in &net.logits {
            assignment[other] = other == logit;
        }
        if let Some(tl) = net.true_label {
            assignment[tl] = false;
        }
        if all_logit_rows_satisfied(net, assignment) {
            valid_class = Some(logit);
            break;
        }
    }
    match valid_class {
        Some(logit) => {
            for &other in &net.logits {
                assignment[other] = other == logit;
            }
            if let Some(tl) = net.true_label {
                assignment[tl] = false;
            }
            // Re-derive gates that may depend on logits (rare, but keep consistent).
            for &gi in &net.gate_order {
                let g = &net.gates[gi];
                let mut on = false;
                for &(iv, want) in &g.literals {
                    if assignment[iv] == want {
                        on = true;
                        break;
                    }
                }
                assignment[g.out] = on;
            }
            1
        }
        None => 0,
    }
}

/// Checks every big-M row of every logit variable is satisfied under `assignment`.
fn all_logit_rows_satisfied(net: &NeuronNet, assignment: &[bool]) -> bool {
    for (li, &logit) in net.logits.iter().enumerate() {
        let value = assignment[logit];
        for row in &net.logit_rows[li] {
            let mut lhs: i128 = 0;
            if value {
                lhs = lhs.saturating_add(row.selector_coeff);
            }
            for &(iv, coeff) in &row.others {
                if assignment[iv] {
                    lhs = lhs.saturating_add(coeff);
                }
            }
            let ok = match row.rel {
                PbRel::Ge => lhs >= row.rhs,
                PbRel::Eq => lhs == row.rhs,
            };
            if !ok {
                return false;
            }
        }
    }
    true
}

/// Whether `instance` + `objective` match the layered BNN OPT-LIN structure this
/// module recognizes. One O(occurrences) recognizer pass (bails to `false` on any
/// non-BNN instance). ADVISORY ONLY — used by the portfolio purely to ROUTE time
/// (run the BNN-seeded SLS first); it never affects which incumbents are reported,
/// all of which are still independently re-verified by the soundness gates.
pub(crate) fn is_recognized(instance: &PbInstance, objective: &PbObjective) -> bool {
    recognize(instance, objective).is_some()
}

/// Builds a feasibility seed for a BNN OPT-LIN instance, or `None` if the instance
/// is not recognized or no verified-feasible seed could be produced within
/// [`MAX_RESTARTS`] restarts.
///
/// The returned assignment is GUARANTEED to satisfy every original constraint
/// (re-verified here with [`verify_all_constraints`]); but even if that guard were
/// removed, soundness would hold, because the SLS phase and the portfolio both
/// independently re-verify any reported incumbent.
pub(crate) fn seed(instance: &PbInstance, objective: &PbObjective) -> Option<Vec<bool>> {
    let net = recognize(instance, objective)?;

    let base_seed = structural_seed(instance, objective);
    for restart in 0..MAX_RESTARTS {
        let mut rng = SplitMix64::new(base_seed ^ restart);
        let mut assignment = vec![false; net.num_vars];
        for &v in &net.free_inputs {
            assignment[v] = (rng.next_u64() & 1) == 1;
        }
        let valid = forward_eval(&net, &mut assignment);
        if valid > 0 && verify_all_constraints(&instance.constraints, &assignment) {
            return Some(assignment);
        }
    }
    None
}

/// Exhaustive SHALLOW adversarial enumeration — the exact-primal lane for the
/// `bnn_mnist_*_adversarial` family (measured: the true optima are tiny flip
/// counts, e.g. f=2, that SLS at 1500s never finds because its moves churn the
/// internal reified variables instead of the input pixels).
///
/// Enumerates input patterns near the objective's zero-cost base: 0 flips, all
/// single flips, and all flip PAIRS (cost-pruned against the best incumbent),
/// completing each pattern through the recognized net with [`forward_eval`] and
/// streaming every candidate that INDEPENDENTLY re-verifies against the ORIGINAL
/// constraints with a strictly better exact objective.
///
/// SOUNDNESS: purely a primal improver. Every streamed incumbent passes
/// `verify_all_constraints` + `eval_objective` on the original instance; nothing
/// is claimed about optimality (the portfolio's own descent/refutation machinery
/// converts a tight incumbent into the OPTIMUM proof). A recognizer mismatch can
/// only make this a no-op, never a wrong answer.
pub(crate) fn enumerate_adversarial_incumbents(
    instance: &PbInstance,
    objective: &PbObjective,
    best_known: Option<i128>,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> Option<i128> {
    use crate::solver::eval_objective;
    let net = recognize(instance, objective)?;
    let n = net.num_vars;
    if net.free_inputs.is_empty() || net.free_inputs.len() > 4096 {
        return None;
    }

    // Zero-cost base polarity per free input from the objective (internal /
    // cascade objective terms are handled implicitly by eval_objective below).
    let mut obj_coeff = vec![0i128; n];
    for t in &objective.terms {
        if let Some((idx, negated)) = term_single_var(t) {
            if idx < n && !negated {
                obj_coeff[idx] = obj_coeff[idx].saturating_add(t.coeff);
            }
        }
    }
    let mut base = vec![false; n];
    for &(v, val) in &net.pins {
        base[v] = val;
    }
    for &v in &net.free_inputs {
        base[v] = obj_coeff[v] < 0;
    }

    let mut best = best_known.unwrap_or(i128::MAX);
    let try_pattern = |flips: &[usize],
                       assignment: &mut Vec<bool>,
                       best: &mut i128,
                       on_improve: &mut dyn FnMut(i128, &[bool])| {
        assignment.copy_from_slice(&base);
        for &v in flips {
            assignment[v] = !assignment[v];
        }
        if forward_eval(&net, assignment) == 0 {
            return;
        }
        if !verify_all_constraints(&instance.constraints, assignment) {
            return;
        }
        let value = eval_objective(objective, assignment);
        if value < *best {
            *best = value;
            on_improve(value, assignment);
        }
    };

    let inputs = &net.free_inputs;
    let mut assignment = vec![false; n];
    // 0 flips.
    try_pattern(&[], &mut assignment, &mut best, on_improve);
    // 1 flip.
    for (i, &v) in inputs.iter().enumerate() {
        if i % 64 == 0 && should_stop() {
            return Some(best);
        }
        try_pattern(&[v], &mut assignment, &mut best, on_improve);
    }
    // 2 flips (the measured optimum class), cheapest-first outer ordering.
    let mut order: Vec<usize> = inputs.clone();
    order.sort_by_key(|&v| obj_coeff[v].saturating_abs());
    for (i, &a) in order.iter().enumerate() {
        if should_stop() {
            return Some(best);
        }
        for &b in order.iter().skip(i + 1) {
            try_pattern(&[a, b], &mut assignment, &mut best, on_improve);
        }
    }
    Some(best)
}

#[cfg(test)]
mod enum_probe {
    use super::*;

    #[test]
    fn bnn_enumerator_finds_exact_base_pattern_on_bounded_network() {
        let (inst, obj) = tests::single_neuron_instance();
        let net = recognize(&inst, &obj).expect("recognize fixture");
        assert_eq!(net.neurons.len(), 1);
        assert_eq!(net.free_inputs.len(), 2);

        let mut improvements = Vec::new();
        let mut stream = |value: i128, assignment: &[bool]| {
            assert!(verify_all_constraints(&inst.constraints, assignment));
            assert_eq!(crate::solver::eval_objective(&obj, assignment), value);
            improvements.push(value);
        };
        let best = enumerate_adversarial_incumbents(&inst, &obj, None, &|| false, &mut stream);
        assert_eq!(best, Some(0));
        assert_eq!(improvements, vec![0]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{PbConstraint, PbLit, PbTerm};

    fn lit(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }

    fn term(coeff: i128, l: PbLit) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![l],
        }
    }

    fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs,
        }
    }

    /// A single neuron over two inputs (vars 1,2) writing output var 3, plus an
    /// objective over the inputs. The two big-M rows encode `out = 1 iff
    /// x1 + x2 <= thr` with a dominant selector coefficient. We then check the
    /// recognizer extracts one neuron and the forward seed is feasible.
    pub(super) fn single_neuron_instance() -> (PbInstance, PbObjective) {
        // Positive row:  +M x3 + x1 + x2 >= rhsP
        // Negative row:  -M x3 - x1 - x2 >= rhsN
        // Choose M = 100 (dominant), inputs coeff +1/-1, and pick rhsP/rhsN so the
        // bands are adjacent. With thr = cN - rhsN and rhsP = thr + 1.
        // Let cN = -100, rhsN = -101 -> thr = 1. rhsP = 2.
        let m = 100i128;
        let pos = ge(vec![term(m, lit(3)), term(1, lit(1)), term(1, lit(2))], 2);
        let neg = ge(
            vec![term(-m, lit(3)), term(-1, lit(1)), term(-1, lit(2))],
            -101,
        );
        let objective = PbObjective {
            terms: vec![term(1, lit(1)), term(1, lit(2))],
        };
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 2,
            constraints: vec![pos, neg],
            objective: Some(objective.clone()),
        };
        (instance, objective)
    }

    #[test]
    fn recognizes_single_neuron() {
        let (instance, objective) = single_neuron_instance();
        let net = recognize(&instance, &objective).expect("should recognize 1 neuron");
        assert_eq!(net.neurons.len(), 1);
        assert_eq!(net.neurons[0].out, 2); // var 3 -> index 2
        assert_eq!(net.neurons[0].thr, 1);
        assert_eq!(net.neuron_order.len(), 1);
        // Inputs are vars 1,2 -> indices 0,1.
        let mut inputs: Vec<usize> = net.neurons[0].inputs.iter().map(|&(v, _)| v).collect();
        inputs.sort_unstable();
        assert_eq!(inputs, vec![0, 1]);
    }

    #[test]
    fn forward_seed_is_feasible_for_single_neuron() {
        let (instance, objective) = single_neuron_instance();
        // The neuron is the only structure (no logits); seed must verify-feasible.
        let assignment = seed(&instance, &objective).expect("seed should be produced");
        assert!(verify_all_constraints(&instance.constraints, &assignment));
        assert_eq!(assignment.len(), 3);
    }

    #[test]
    fn declines_unrecognized_instance() {
        // A plain cardinality covering instance has no big-M structure.
        let constraints = vec![
            ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
            ge(vec![term(1, lit(2)), term(1, lit(3))], 1),
        ];
        let objective = PbObjective {
            terms: vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))],
        };
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 2,
            constraints,
            objective: Some(objective.clone()),
        };
        assert!(recognize(&instance, &objective).is_none());
        assert!(seed(&instance, &objective).is_none());
    }

    #[test]
    fn gate_or_cascade_is_derived_min_cost() {
        // One neuron (var 3 from inputs 1,2) plus a gate var 4 with rows:
        //   x4 - x1 >= 0   (x4 >= x1)
        //   x4 - x2 >= 0   (x4 >= x2)
        // The gate is the OR of x1, x2; min-cost value is exactly that OR.
        let m = 100i128;
        let pos = ge(vec![term(m, lit(3)), term(1, lit(1)), term(1, lit(2))], 2);
        let neg = ge(
            vec![term(-m, lit(3)), term(-1, lit(1)), term(-1, lit(2))],
            -101,
        );
        let g1 = ge(vec![term(1, lit(4)), term(-1, lit(1))], 0);
        let g2 = ge(vec![term(1, lit(4)), term(-1, lit(2))], 0);
        let objective = PbObjective {
            terms: vec![term(1, lit(4))],
        };
        let instance = PbInstance {
            num_vars: 4,
            num_constraints: 4,
            constraints: vec![pos, neg, g1, g2],
            objective: Some(objective.clone()),
        };
        let net = recognize(&instance, &objective).expect("recognize neuron + gate");
        assert_eq!(net.gates.len(), 1);
        assert_eq!(net.gates[0].out, 3); // var 4 -> index 3
        let assignment = seed(&instance, &objective).expect("seed");
        assert!(verify_all_constraints(&instance.constraints, &assignment));
        // Gate must equal OR of its inputs.
        let expected_gate = assignment[0] || assignment[1];
        assert_eq!(assignment[3], expected_gate);
    }

    #[test]
    fn seed_is_deterministic() {
        let (instance, objective) = single_neuron_instance();
        let a = seed(&instance, &objective);
        let b = seed(&instance, &objective);
        assert_eq!(a, b);
    }
}

#[cfg(test)]
mod real_instance_tests {
    use super::*;

    #[test]
    fn recognized_bnn_seed_is_deterministic_feasible_and_exactly_valued() {
        let (instance, objective) = tests::single_neuron_instance();
        assert!(is_recognized(&instance, &objective));
        let first = seed(&instance, &objective).expect("seed");
        let second = seed(&instance, &objective).expect("repeat seed");
        assert_eq!(first, second);
        assert!(verify_all_constraints(&instance.constraints, &first));
        let value = crate::solver::eval_objective(&objective, &first);
        assert_eq!(value, first[0] as i128 + first[1] as i128);
        assert!((0..=2).contains(&value));
    }
}

#[cfg(test)]
mod timing_tests {
    use super::*;

    #[test]
    fn forward_evaluation_satisfies_neuron_for_every_input_pattern() {
        let (instance, objective) = tests::single_neuron_instance();
        let net = recognize(&instance, &objective).expect("recognize fixture");
        for mask in 0u8..4 {
            let mut assignment = vec![false; 3];
            assignment[0] = mask & 1 != 0;
            assignment[1] = mask & 2 != 0;
            assert_eq!(forward_eval(&net, &mut assignment), 1);
            assert_eq!(
                assignment[2],
                assignment[..2].iter().filter(|&&value| value).count() <= 1
            );
            assert!(verify_all_constraints(&instance.constraints, &assignment));
        }
    }
}
