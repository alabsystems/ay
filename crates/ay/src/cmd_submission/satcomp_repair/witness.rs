// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Witness-gate recovery, replay classification, and materialization-plan audit
//! for satcomp_repair (the `witness-audit` subcommand + its gate helpers).
//! Extracted from satcomp_repair.rs; `lit_var` stays in the parent (crate-shared).

use super::*;
use std::collections::{BTreeMap, BTreeSet};

use anyhow::Result;
use serde_json::{json, Value as JsonValue};

pub(super) fn run_witness_audit(opts: WitnessAuditOptions) -> Result<()> {
    let root = repo_root()?;
    let common = opts.common;
    let target_cnf = resolve_path(&root, &common.target_cnf);
    let formula = parse_dimacs_path(&target_cnf)?;
    let gates = recover_witness_gates(&formula);
    let gate_counts = witness_gate_counts(&gates);
    let exact = validate_witness_exact_clauses(formula.clauses.len(), &gates);
    let replay = classify_witness_replay(formula.num_vars, &gates);
    let materialization_plan = compute_witness_materialization_plan(formula.num_vars, &gates);
    let payload = json!({
        "schema": "ay.satcomp-circuit-witness-audit/v1",
        "issue": 9424,
        "scoreboard_row": "Circuit_multiplier22",
        "source": diagnostic_source_json(
            git_head(&root),
            "Diagnostic-only Rust SAT-COMP submission/preflight CLI circuit witness audit. No route, SAT stdout, model-output, proof, solved-count, PAR-2, or SAT-COMP authority is granted.",
        ),
        "input": {
            "path": display_path_for_report(&target_cnf, &root),
            "sha256": sha256_file(&target_cnf)?,
            "num_vars": formula.num_vars,
            "num_clauses": formula.clauses.len(),
        },
        "gate_counts": gate_counts,
        "gate_output_samples": witness_gate_output_samples(&gates, 64),
        "gates_total": gates.len(),
        "exact_clause_validation": exact,
        "reconstruction": replay,
        "materialization_plan": materialization_plan,
        "verdict": {
            "route_admitted": false,
            "sat_output_authority": false,
            "model_output_authority": false,
            "proof_output_authority": false,
            "sat_comp_progress_claim": false,
            "blocker": "Witness recovery is diagnostic only; a future route still needs a complete original-DIMACS-valid model or externally checked proof.",
        },
    });
    write_payload(&root, &common, "witness-audit", &payload)
}

fn recover_witness_gates(formula: &RawFormula) -> Vec<WitnessGate> {
    let (pos, neg, by_clause) = build_witness_occurrences(formula);
    let mut gates = Vec::new();
    for pivot in 1..=formula.num_vars {
        if pos[pivot].is_empty() && neg[pivot].is_empty() {
            continue;
        }
        let gate = find_witness_equiv(pivot, &formula.clauses, &pos, &neg)
            .or_else(|| find_witness_and(pivot, &formula.clauses, &pos, &neg))
            .or_else(|| find_witness_xor(pivot, &formula.clauses, &pos, &neg, &by_clause))
            .or_else(|| find_witness_ite(pivot, &formula.clauses, &pos, &neg));
        if let Some(gate) = gate {
            gates.push(gate);
        }
    }
    gates
}

fn build_witness_occurrences(
    formula: &RawFormula,
) -> (
    Vec<Vec<usize>>,
    Vec<Vec<usize>>,
    BTreeMap<Vec<i32>, Vec<usize>>,
) {
    let mut pos = vec![Vec::new(); formula.num_vars + 1];
    let mut neg = vec![Vec::new(); formula.num_vars + 1];
    let mut by_clause: BTreeMap<Vec<i32>, Vec<usize>> = BTreeMap::new();
    for (idx, clause) in formula.clauses.iter().enumerate() {
        by_clause
            .entry(normalize_witness_clause(clause))
            .or_default()
            .push(idx);
        for &lit in clause {
            let var = lit_var(lit);
            if (1..=formula.num_vars).contains(&var) {
                if lit > 0 {
                    pos[var].push(idx);
                } else {
                    neg[var].push(idx);
                }
            }
        }
    }
    (pos, neg, by_clause)
}

fn normalize_witness_clause(lits: &[i32]) -> Vec<i32> {
    let mut normalized = lits.to_vec();
    normalized.sort_by_key(|lit| (lit.unsigned_abs(), *lit < 0));
    normalized
}

fn binary_other(clause: &[i32], exclude: i32) -> Option<i32> {
    if clause.len() != 2 || !clause.contains(&exclude) {
        return None;
    }
    if clause[0] == exclude {
        Some(clause[1])
    } else {
        Some(clause[0])
    }
}

fn ternary_others(clause: &[i32], exclude: i32) -> Option<(i32, i32)> {
    if clause.len() != 3 || !clause.contains(&exclude) {
        return None;
    }
    let mut others = clause.iter().copied().filter(|&lit| lit != exclude);
    let first = others.next()?;
    let second = others.next()?;
    if others.next().is_some() {
        return None;
    }
    Some((first, second))
}

fn find_witness_clause(
    by_clause: &BTreeMap<Vec<i32>, Vec<usize>>,
    used: &BTreeSet<usize>,
    lits: &[i32],
) -> Option<usize> {
    by_clause
        .get(&normalize_witness_clause(lits))
        .and_then(|indices| indices.iter().copied().find(|idx| !used.contains(idx)))
}

fn find_witness_equiv(
    pivot: usize,
    clauses: &[Vec<i32>],
    pos: &[Vec<usize>],
    neg: &[Vec<usize>],
) -> Option<WitnessGate> {
    let pivot_lit = pivot as i32;
    let mut pos_other_to_idx = BTreeMap::new();
    for &idx in &pos[pivot] {
        if let Some(other) = binary_other(&clauses[idx], pivot_lit) {
            pos_other_to_idx.entry(other).or_insert(idx);
        }
    }
    for &idx in &neg[pivot] {
        let Some(other) = binary_other(&clauses[idx], -pivot_lit) else {
            continue;
        };
        if let Some(&pos_idx) = pos_other_to_idx.get(&-other) {
            return Some(WitnessGate {
                kind: "equiv",
                output: pivot,
                inputs: vec![other],
                defining_clauses: vec![pos_idx, idx],
                negated_output: false,
            });
        }
    }
    None
}

fn find_witness_and(
    pivot: usize,
    clauses: &[Vec<i32>],
    pos: &[Vec<usize>],
    neg: &[Vec<usize>],
) -> Option<WitnessGate> {
    let pivot_lit = pivot as i32;
    find_witness_and_oriented(pivot, pivot_lit, &pos[pivot], &neg[pivot], clauses)
        .or_else(|| find_witness_and_oriented(pivot, -pivot_lit, &neg[pivot], &pos[pivot], clauses))
}

fn find_witness_and_oriented(
    pivot: usize,
    output_lit: i32,
    base_occs: &[usize],
    side_occs: &[usize],
    clauses: &[Vec<i32>],
) -> Option<WitnessGate> {
    let neg_output = -output_lit;
    let mut side_by_other: BTreeMap<i32, Vec<usize>> = BTreeMap::new();
    for &idx in side_occs {
        if let Some(other) = binary_other(&clauses[idx], neg_output) {
            side_by_other.entry(other).or_default().push(idx);
        }
    }
    if side_by_other.is_empty() {
        return None;
    }
    for &base_idx in base_occs {
        let base = &clauses[base_idx];
        if !base.contains(&output_lit) || base.len() < 2 {
            continue;
        }
        let mut inputs = Vec::new();
        let mut defining = vec![base_idx];
        let mut used_sides = BTreeSet::new();
        let mut ok = true;
        for &lit in base {
            if lit == output_lit {
                continue;
            }
            let needed = -lit;
            let Some(side_idx) = side_by_other.get(&needed).and_then(|candidates| {
                candidates
                    .iter()
                    .copied()
                    .find(|idx| !used_sides.contains(idx))
            }) else {
                ok = false;
                break;
            };
            used_sides.insert(side_idx);
            defining.push(side_idx);
            inputs.push(needed);
        }
        if ok && !inputs.is_empty() {
            return Some(WitnessGate {
                kind: "and",
                output: pivot,
                inputs,
                defining_clauses: defining,
                negated_output: output_lit < 0,
            });
        }
    }
    None
}

fn sorted_witness_pair(a: i32, b: i32) -> [i32; 2] {
    let mut pair = [a, b];
    pair.sort_by_key(|lit| (lit.unsigned_abs(), *lit < 0));
    pair
}

fn find_witness_xor(
    pivot: usize,
    clauses: &[Vec<i32>],
    pos: &[Vec<usize>],
    neg: &[Vec<usize>],
    by_clause: &BTreeMap<Vec<i32>, Vec<usize>>,
) -> Option<WitnessGate> {
    find_witness_xor2(pivot, clauses, pos, neg)
        .or_else(|| find_witness_xor_higher(pivot, clauses, pos, by_clause))
}

fn find_witness_xor2(
    pivot: usize,
    clauses: &[Vec<i32>],
    pos: &[Vec<usize>],
    neg: &[Vec<usize>],
) -> Option<WitnessGate> {
    let pivot_lit = pivot as i32;
    for &clause_idx in &pos[pivot] {
        let Some((a, b)) = ternary_others(&clauses[clause_idx], pivot_lit) else {
            continue;
        };
        if lit_var(a) == lit_var(b) {
            continue;
        }
        let needed_pos = sorted_witness_pair(-a, -b);
        let needed_neg1 = sorted_witness_pair(-a, b);
        let needed_neg2 = sorted_witness_pair(a, -b);
        let pos2 = pos[pivot]
            .iter()
            .copied()
            .filter(|idx| *idx != clause_idx)
            .find(|idx| {
                ternary_others(&clauses[*idx], pivot_lit)
                    .is_some_and(|(x, y)| sorted_witness_pair(x, y) == needed_pos)
            });
        let Some(pos2) = pos2 else {
            continue;
        };
        let mut neg1 = None;
        let mut neg2 = None;
        for &idx in &neg[pivot] {
            let Some((x, y)) = ternary_others(&clauses[idx], -pivot_lit) else {
                continue;
            };
            let candidate = sorted_witness_pair(x, y);
            if candidate == needed_neg1 {
                neg1 = Some(idx);
            } else if candidate == needed_neg2 {
                neg2 = Some(idx);
            }
        }
        let (Some(neg1), Some(neg2)) = (neg1, neg2) else {
            continue;
        };
        let unique: BTreeSet<_> = [clause_idx, pos2, neg1, neg2].into_iter().collect();
        if unique.len() == 4 {
            let neg_inputs = usize::from(a < 0) + usize::from(b < 0);
            return Some(WitnessGate {
                kind: "xor",
                output: pivot,
                inputs: vec![lit_var(a) as i32, lit_var(b) as i32],
                defining_clauses: vec![clause_idx, pos2, neg1, neg2],
                negated_output: neg_inputs % 2 == 0,
            });
        }
    }
    None
}

fn find_witness_xor_higher(
    pivot: usize,
    clauses: &[Vec<i32>],
    pos: &[Vec<usize>],
    by_clause: &BTreeMap<Vec<i32>, Vec<usize>>,
) -> Option<WitnessGate> {
    let pivot_lit = pivot as i32;
    for &clause_idx in &pos[pivot] {
        let clause = &clauses[clause_idx];
        if !clause.contains(&pivot_lit) || clause.len() < 4 {
            continue;
        }
        let arity = clause.len() - 1;
        if arity > MAX_WITNESS_XOR_ARITY {
            continue;
        }
        let raw_inputs: Vec<_> = clause
            .iter()
            .copied()
            .filter(|&lit| lit_var(lit) != pivot)
            .collect();
        if raw_inputs.len() != arity {
            continue;
        }
        let mut lits = Vec::with_capacity(arity + 1);
        lits.push(pivot_lit);
        lits.extend(raw_inputs.iter().copied());
        let mut signs = 0usize;
        let mut used = BTreeSet::from([clause_idx]);
        let mut defining = Vec::new();
        let mut found_all = true;
        for _ in 0..((1usize << arity) - 1) {
            let prev = signs;
            signs += 1;
            while signs.count_ones() % 2 == 1 {
                signs += 1;
            }
            for (j, lit) in lits.iter_mut().enumerate() {
                let bit = 1usize << j;
                if (prev & bit) != (signs & bit) {
                    *lit = -*lit;
                }
            }
            let Some(idx) = find_witness_clause(by_clause, &used, &lits) else {
                found_all = false;
                break;
            };
            used.insert(idx);
            defining.push(idx);
        }
        if found_all {
            defining.push(clause_idx);
            let neg_inputs = raw_inputs.iter().filter(|&&lit| lit < 0).count();
            return Some(WitnessGate {
                kind: "xor",
                output: pivot,
                inputs: raw_inputs.iter().map(|&lit| lit_var(lit) as i32).collect(),
                defining_clauses: defining,
                negated_output: neg_inputs % 2 == 0,
            });
        }
    }
    None
}

fn find_witness_ite(
    pivot: usize,
    clauses: &[Vec<i32>],
    pos: &[Vec<usize>],
    neg: &[Vec<usize>],
) -> Option<WitnessGate> {
    let pivot_lit = pivot as i32;
    for (pos_offset, &ci) in pos[pivot].iter().enumerate() {
        let Some((a1, b1)) = ternary_others(&clauses[ci], pivot_lit) else {
            continue;
        };
        for &cj in &pos[pivot][pos_offset + 1..] {
            let Some((a2, b2)) = ternary_others(&clauses[cj], pivot_lit) else {
                continue;
            };
            let patterns = [
                (a1, b2, b1, a1 == -a2),
                (a1, a2, b1, a1 == -b2),
                (b1, b2, a1, b1 == -a2),
                (b1, a2, a1, b1 == -b2),
            ];
            for (cond, then_neg, else_neg, enabled) in patterns {
                if !enabled {
                    continue;
                }
                let then_lit = -then_neg;
                let else_lit = -else_neg;
                let mut neg_else = None;
                let mut neg_then = None;
                for &nk in &neg[pivot] {
                    let Some((x, y)) = ternary_others(&clauses[nk], -pivot_lit) else {
                        continue;
                    };
                    let pair = sorted_witness_pair(x, y);
                    if pair == sorted_witness_pair(cond, else_lit) {
                        neg_else = Some(nk);
                    } else if pair == sorted_witness_pair(-cond, then_lit) {
                        neg_then = Some(nk);
                    }
                }
                let (Some(neg_else), Some(neg_then)) = (neg_else, neg_then) else {
                    continue;
                };
                let unique: BTreeSet<_> = [ci, cj, neg_else, neg_then].into_iter().collect();
                if unique.len() == 4 {
                    return Some(WitnessGate {
                        kind: "ite",
                        output: pivot,
                        inputs: vec![cond, then_lit, else_lit],
                        defining_clauses: vec![ci, cj, neg_else, neg_then],
                        negated_output: false,
                    });
                }
            }
        }
    }
    None
}

fn witness_gate_counts(gates: &[WitnessGate]) -> JsonValue {
    let mut counts: BTreeMap<&'static str, usize> = BTreeMap::new();
    for gate in gates {
        *counts.entry(gate.kind).or_default() += 1;
    }
    json!(counts)
}

fn witness_gate_output_samples(gates: &[WitnessGate], limit_per_kind: usize) -> JsonValue {
    let mut samples: BTreeMap<&'static str, Vec<usize>> = BTreeMap::new();
    for gate in gates {
        let outputs = samples.entry(gate.kind).or_default();
        if outputs.len() < limit_per_kind {
            outputs.push(gate.output);
        }
    }
    json!(samples)
}

fn validate_witness_exact_clauses(num_clauses: usize, gates: &[WitnessGate]) -> JsonValue {
    let mut by_kind: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut rejected: BTreeMap<&'static str, usize> = BTreeMap::new();
    for gate in gates {
        if gate.defining_clauses.is_empty() {
            *rejected.entry("missing_clause").or_default() += 1;
            continue;
        }
        let unique: BTreeSet<_> = gate.defining_clauses.iter().copied().collect();
        if unique.len() != gate.defining_clauses.len() {
            *rejected.entry("duplicate_clause").or_default() += 1;
            continue;
        }
        if gate.defining_clauses.iter().any(|&idx| idx >= num_clauses) {
            *rejected.entry("clause_out_of_range").or_default() += 1;
            continue;
        }
        *by_kind.entry(gate.kind).or_default() += 1;
    }
    json!({
        "validated_total": by_kind.values().sum::<usize>(),
        "validated_by_kind": by_kind,
        "rejected_total": rejected.values().sum::<usize>(),
        "rejected_by_reason": rejected,
    })
}

fn classify_witness_replay(num_vars: usize, gates: &[WitnessGate]) -> JsonValue {
    let mut output_counts: BTreeMap<usize, usize> = BTreeMap::new();
    for gate in gates {
        *output_counts.entry(gate.output).or_default() += 1;
    }
    let gate_outputs: BTreeSet<_> = gates
        .iter()
        .filter(|gate| (1..=num_vars).contains(&gate.output))
        .map(|gate| gate.output)
        .collect();
    let mut assigned: BTreeSet<_> = (1..=num_vars)
        .filter(|var| !gate_outputs.contains(var))
        .collect();
    let mut derivable = BTreeSet::new();
    let mut progress = true;
    while progress {
        progress = false;
        for gate in gates {
            if assigned.contains(&gate.output)
                || output_counts.get(&gate.output).copied().unwrap_or_default() != 1
            {
                continue;
            }
            if gate
                .inputs
                .iter()
                .all(|&lit| assigned.contains(&lit_var(lit)))
            {
                assigned.insert(gate.output);
                derivable.insert(gate.output);
                progress = true;
            }
        }
    }
    let blocked: Vec<_> = gate_outputs.difference(&assigned).copied().collect();
    let blocked_set: BTreeSet<_> = blocked.iter().copied().collect();
    let mut blocked_kinds: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut negated_outputs = 0usize;
    for gate in gates {
        if gate.negated_output {
            negated_outputs += 1;
        }
        if blocked_set.contains(&gate.output) {
            *blocked_kinds.entry(gate.kind).or_default() += 1;
        }
    }
    let duplicate_defs = output_counts
        .values()
        .filter(|&&count| count > 1)
        .map(|count| count - 1)
        .sum::<usize>();
    json!({
        "frontier_vars": num_vars - gate_outputs.len() + blocked.len(),
        "derivable_gate_output_vars": derivable.len(),
        "blocked_gate_output_vars": blocked.len(),
        "duplicate_gate_output_defs": duplicate_defs,
        "negated_output_witnesses": negated_outputs,
        "complete_original_model_vars": assigned.len() + blocked.len(),
        "blocker_class": if blocked.is_empty() { "none" } else { "direct_assignment" },
        "blocked_gate_kinds": blocked_kinds,
        "blocked_sample": blocked.iter().take(20).copied().collect::<Vec<_>>(),
    })
}

fn compute_witness_materialization_plan(num_vars: usize, gates: &[WitnessGate]) -> JsonValue {
    let mut output_counts: BTreeMap<usize, usize> = BTreeMap::new();
    for gate in gates {
        *output_counts.entry(gate.output).or_default() += 1;
    }
    let gates_by_output: BTreeMap<usize, &WitnessGate> = gates
        .iter()
        .filter(|gate| output_counts.get(&gate.output).copied().unwrap_or_default() == 1)
        .map(|gate| (gate.output, gate))
        .collect();
    let gate_outputs: BTreeSet<_> = gates_by_output
        .keys()
        .copied()
        .filter(|output| (1..=num_vars).contains(output))
        .collect();
    let duplicate_outputs: Vec<_> = output_counts
        .iter()
        .filter_map(|(&output, &count)| (count > 1).then_some(output))
        .collect();
    let malformed_outputs: BTreeSet<_> = output_counts
        .keys()
        .copied()
        .filter(|output| !(1..=num_vars).contains(output))
        .collect();

    let mut dependencies: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    let mut malformed_dependency_outputs = malformed_outputs.clone();
    for &output in &gate_outputs {
        let gate = gates_by_output[&output];
        let mut deps = BTreeSet::new();
        for &lit in &gate.inputs {
            let var = lit_var(lit);
            if !(1..=num_vars).contains(&var) {
                malformed_dependency_outputs.insert(output);
            } else if gate_outputs.contains(&var) {
                deps.insert(var);
            }
        }
        dependencies.insert(output, deps);
    }

    let mut assigned: BTreeSet<_> = (1..=num_vars)
        .filter(|var| !gate_outputs.contains(var))
        .collect();
    let mut remaining = gate_outputs.clone();
    let mut replay_layers: Vec<Vec<usize>> = Vec::new();
    loop {
        let ready: Vec<_> = remaining
            .iter()
            .copied()
            .filter(|output| !malformed_dependency_outputs.contains(output))
            .filter(|output| {
                gates_by_output[output]
                    .inputs
                    .iter()
                    .all(|&lit| assigned.contains(&lit_var(lit)))
            })
            .collect();
        if ready.is_empty() {
            break;
        }
        for output in &ready {
            assigned.insert(*output);
            remaining.remove(output);
        }
        replay_layers.push(ready);
    }

    let blocked: Vec<_> = remaining.iter().copied().collect();
    let blocked_set: BTreeSet<_> = blocked.iter().copied().collect();
    let blocked_edges: BTreeMap<usize, BTreeSet<usize>> = blocked
        .iter()
        .copied()
        .map(|output| {
            let deps = dependencies
                .get(&output)
                .cloned()
                .unwrap_or_default()
                .intersection(&blocked_set)
                .copied()
                .collect();
            (output, deps)
        })
        .collect();
    let blocked_dependency_edges = blocked_edges.values().map(BTreeSet::len).sum::<usize>();
    let components = tarjan_witness_sccs(&blocked, &blocked_edges);
    let cyclic_components: Vec<Vec<usize>> = components
        .into_iter()
        .filter(|component| {
            component.len() > 1
                || component.first().is_some_and(|node| {
                    blocked_edges
                        .get(node)
                        .is_some_and(|deps| deps.contains(node))
                })
        })
        .collect();
    let cyclic_outputs: BTreeSet<_> = cyclic_components
        .iter()
        .flat_map(|component| component.iter().copied())
        .collect();
    let unresolved_outputs: Vec<_> = blocked
        .iter()
        .copied()
        .filter(|output| !cyclic_outputs.contains(output))
        .collect();

    let mut reverse_blocked_edges: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    for (&output, deps) in &blocked_edges {
        for &dep in deps {
            reverse_blocked_edges.entry(dep).or_default().insert(output);
        }
    }
    let distance_from_cycle = witness_distances_from_cycle(&cyclic_outputs, &reverse_blocked_edges);
    let mut unresolved_depth_hist: BTreeMap<String, usize> = BTreeMap::new();
    for output in &unresolved_outputs {
        let depth = distance_from_cycle
            .get(output)
            .map(|value| value.to_string())
            .unwrap_or_else(|| "-1".to_string());
        *unresolved_depth_hist.entry(depth).or_default() += 1;
    }

    let mut blocked_kind_counts: BTreeMap<&'static str, usize> = BTreeMap::new();
    for output in &blocked {
        if let Some(gate) = gates_by_output.get(output) {
            *blocked_kind_counts.entry(gate.kind).or_default() += 1;
        }
    }
    let mut replay_kind_counts: BTreeMap<&'static str, usize> = BTreeMap::new();
    for output in replay_layers.iter().flatten() {
        if let Some(gate) = gates_by_output.get(output) {
            *replay_kind_counts.entry(gate.kind).or_default() += 1;
        }
    }
    let mut scc_size_hist: BTreeMap<String, usize> = BTreeMap::new();
    for component in &cyclic_components {
        *scc_size_hist
            .entry(component.len().to_string())
            .or_default() += 1;
    }

    json!({
        "num_vars": num_vars,
        "gate_output_witnesses": gate_outputs.len(),
        "duplicate_gate_output_defs": output_counts.values().filter(|&&count| count > 1).map(|count| count - 1).sum::<usize>(),
        "duplicate_output_vars": duplicate_outputs.len(),
        "malformed_dependency_output_vars": malformed_dependency_outputs.len(),
        "direct_frontier_vars": num_vars - gate_outputs.len(),
        "direct_assignment_vars_required_before_replay": num_vars - gate_outputs.len() + blocked.len(),
        "direct_input_ready_output_vars": replay_layers.first().map(Vec::len).unwrap_or_default(),
        "acyclic_replay_order_len": replay_layers.iter().map(Vec::len).sum::<usize>(),
        "acyclic_replay_layers": replay_layers.len(),
        "replay_layer_sizes": replay_layers.iter().map(Vec::len).collect::<Vec<_>>(),
        "replay_layer_outputs": replay_layers,
        "replay_kind_counts": replay_kind_counts,
        "blocked_gate_output_vars": blocked.len(),
        "blocked_by_cycle_output_vars": cyclic_outputs.len(),
        "blocked_by_unresolved_dependency_output_vars": unresolved_outputs.len(),
        "blocked_by_duplicate_output_vars": duplicate_outputs.len(),
        "blocked_by_malformed_dependency_output_vars": malformed_dependency_outputs.len(),
        "blocked_output_dependency_edges": blocked_dependency_edges,
        "blocked_gate_kinds": blocked_kind_counts,
        "cyclic_scc_count": cyclic_components.len(),
        "cyclic_scc_size_histogram": scc_size_hist,
        "largest_cyclic_scc_size": cyclic_components.iter().map(Vec::len).max().unwrap_or_default(),
        "unresolved_distance_from_cycle_histogram": unresolved_depth_hist,
        "blocked_sample": blocked.iter().take(40).copied().collect::<Vec<_>>(),
        "cycle_output_sample": cyclic_outputs.iter().take(40).copied().collect::<Vec<_>>(),
        "unresolved_output_sample": unresolved_outputs.iter().take(40).copied().collect::<Vec<_>>(),
        "complete_original_model_vars_after_direct_blocked_assignment": assigned.len() + blocked.len(),
    })
}

fn tarjan_witness_sccs(
    nodes: &[usize],
    edges: &BTreeMap<usize, BTreeSet<usize>>,
) -> Vec<Vec<usize>> {
    struct Tarjan<'a> {
        index: usize,
        stack: Vec<usize>,
        on_stack: BTreeSet<usize>,
        indices: BTreeMap<usize, usize>,
        lowlink: BTreeMap<usize, usize>,
        components: Vec<Vec<usize>>,
        edges: &'a BTreeMap<usize, BTreeSet<usize>>,
    }

    impl Tarjan<'_> {
        fn visit(&mut self, node: usize) {
            self.indices.insert(node, self.index);
            self.lowlink.insert(node, self.index);
            self.index += 1;
            self.stack.push(node);
            self.on_stack.insert(node);

            for &dep in self.edges.get(&node).into_iter().flatten() {
                if !self.indices.contains_key(&dep) {
                    self.visit(dep);
                    let dep_low = self.lowlink[&dep];
                    let node_low = self.lowlink[&node].min(dep_low);
                    self.lowlink.insert(node, node_low);
                } else if self.on_stack.contains(&dep) {
                    let dep_index = self.indices[&dep];
                    let node_low = self.lowlink[&node].min(dep_index);
                    self.lowlink.insert(node, node_low);
                }
            }

            if self.lowlink[&node] == self.indices[&node] {
                let mut component = Vec::new();
                loop {
                    let member = self
                        .stack
                        .pop()
                        .expect("Tarjan stack contains the current SCC root");
                    self.on_stack.remove(&member);
                    component.push(member);
                    if member == node {
                        break;
                    }
                }
                component.sort_unstable();
                self.components.push(component);
            }
        }
    }

    let mut tarjan = Tarjan {
        index: 0,
        stack: Vec::new(),
        on_stack: BTreeSet::new(),
        indices: BTreeMap::new(),
        lowlink: BTreeMap::new(),
        components: Vec::new(),
        edges,
    };
    for &node in nodes {
        if !tarjan.indices.contains_key(&node) {
            tarjan.visit(node);
        }
    }
    tarjan.components
}

fn witness_distances_from_cycle(
    cyclic_outputs: &BTreeSet<usize>,
    reverse_blocked_edges: &BTreeMap<usize, BTreeSet<usize>>,
) -> BTreeMap<usize, usize> {
    let mut distances = BTreeMap::new();
    let mut queue: Vec<usize> = Vec::new();
    for &output in cyclic_outputs {
        distances.insert(output, 0);
        queue.push(output);
    }
    let mut cursor = 0usize;
    while let Some(&current) = queue.get(cursor) {
        cursor += 1;
        let current_distance = distances[&current];
        for &parent in reverse_blocked_edges.get(&current).into_iter().flatten() {
            if let std::collections::btree_map::Entry::Vacant(entry) = distances.entry(parent) {
                entry.insert(current_distance + 1);
                queue.push(parent);
            }
        }
    }
    distances
}
