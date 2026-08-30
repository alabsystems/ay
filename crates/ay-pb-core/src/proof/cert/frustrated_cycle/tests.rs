// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the signed-graph frustration-index certifier.
//!
//! Every instance here is SYNTHESIZED in this file, so the gate needs no
//! external corpus and cannot silently pass because a benchmark went missing —
//! the failure mode recorded in `vacuous-harness-window`, where a gate selected
//! zero instances and reported green.

use super::packing::{floor_of, two_core, Limits};
use super::*;
use crate::types::{PbConstraint, PbLit, PbObjective, PbTerm};

/// Which template an edge follows.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Equal,
    Differ,
}

/// Builds a signed-graph OPT-LIN instance in the family's exact layout: error
/// variables `x1..xE` in objective order, then sign variables `x(E+1)..x(E+N)`.
///
/// `edges` is `(u, v, kind)` over 0-based node indices.
fn signed_instance(nodes: usize, edges: &[(usize, usize, Kind)]) -> PbInstance {
    let count = edges.len();
    let term = |coeff: i128, var: u32| PbTerm {
        coeff,
        lits: vec![PbLit {
            var,
            negated: false,
        }],
    };
    let mut constraints = Vec::new();
    for (index, &(u, v, kind)) in edges.iter().enumerate() {
        let e = (index + 1) as u32;
        let a = (count + 1 + u) as u32;
        let b = (count + 1 + v) as u32;
        let rows: [(i128, i128, i128); 2] = match kind {
            Kind::Equal => [(-1, 1, 0), (1, -1, 0)],
            Kind::Differ => [(1, 1, 1), (-1, -1, -1)],
        };
        for (ca, cb, rhs) in rows {
            constraints.push(PbConstraint {
                terms: vec![term(1, e), term(ca, a), term(cb, b)],
                rel: PbRel::Ge,
                rhs,
            });
        }
    }
    PbInstance {
        num_vars: (count + nodes) as u32,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: Some(PbObjective {
            terms: (1..=count).map(|i| term(1, i as u32)).collect(),
        }),
    }
}

/// The frustration index of an assignment of node signs: pay one per edge whose
/// endpoints disagree with the edge's own sign. Also builds the incumbent.
fn incumbent_for(
    nodes: usize,
    edges: &[(usize, usize, Kind)],
    signs: &[bool],
) -> (Vec<bool>, i128) {
    let mut values = vec![false; edges.len() + nodes];
    let mut cost = 0;
    for (index, &(u, v, kind)) in edges.iter().enumerate() {
        let agree = signs[u] == signs[v];
        let satisfied = match kind {
            Kind::Equal => agree,
            Kind::Differ => !agree,
        };
        if !satisfied {
            values[index] = true;
            cost += 1;
        }
    }
    for (node, &sign) in signs.iter().enumerate() {
        values[edges.len() + node] = sign;
    }
    (values, cost)
}

/// One frustrated triangle: two `EQUAL` edges and one `DIFFER`. Optimum 1.
fn triangle() -> (PbInstance, Vec<bool>, i128) {
    let edges = [
        (0usize, 1usize, Kind::Equal),
        (1, 2, Kind::Equal),
        (2, 0, Kind::Differ),
    ];
    let instance = signed_instance(3, &edges);
    let (incumbent, cost) = incumbent_for(3, &edges, &[true, true, true]);
    (instance, incumbent, cost)
}

/// Two vertex-disjoint frustrated triangles. Optimum 2, and the packing needs
/// two independent cuts rather than one.
fn two_triangles() -> (PbInstance, Vec<bool>, i128) {
    let edges = [
        (0usize, 1usize, Kind::Equal),
        (1, 2, Kind::Equal),
        (2, 0, Kind::Differ),
        (3, 4, Kind::Equal),
        (4, 5, Kind::Differ),
        (5, 3, Kind::Equal),
    ];
    let instance = signed_instance(6, &edges);
    let (incumbent, cost) = incumbent_for(6, &edges, &[true, true, true, true, true, true]);
    (instance, incumbent, cost)
}

/// A frustrated 5-cycle with a long tail hanging off it. Exercises the walk over
/// more than three edges, the `DIFFER` sign flip mid-walk, and the 2-core
/// reduction (the tail is a bridge and must be dropped from the LP but still
/// carry its slack fill in the final line).
fn five_cycle_with_tail() -> (PbInstance, Vec<bool>, i128) {
    let edges = [
        (0usize, 1usize, Kind::Equal),
        (1, 2, Kind::Differ),
        (2, 3, Kind::Equal),
        (3, 4, Kind::Differ),
        (4, 0, Kind::Differ),
        (0, 5, Kind::Equal),
        (5, 6, Kind::Differ),
    ];
    let instance = signed_instance(7, &edges);
    // Signs chosen so only the cycle pays: the tail is satisfiable on its own.
    let (incumbent, cost) =
        incumbent_for(7, &edges, &[true, true, false, false, true, true, false]);
    (instance, incumbent, cost)
}

fn certify(instance: &PbInstance, incumbent: &[bool], optimum: i128) -> Option<String> {
    certify_opt_lin_frustrated_cycle(instance, incumbent, optimum)
}

// ---------------------------------------------------------------------------
// Layer 1: the pre-gate.
// ---------------------------------------------------------------------------

#[test]
fn header_gate_accepts_the_family_shape() {
    // `macrophage`: 2260 variables, 3164 constraints, 1582 objective terms.
    assert_eq!(header_candidate(2260, 3164, 1582), Some((1582, 678)));
    // `methanosarcina`: 7930 / 14604 / 7302.
    assert_eq!(header_candidate(7930, 14604, 7302), Some((7302, 628)));
}

#[test]
fn header_gate_rejects_off_family_headers() {
    // Odd constraint count.
    assert_eq!(header_candidate(2260, 3163, 1581), None);
    // Objective length does not match half the constraint count. This is the
    // discriminator that does the work: it is a coincidence off-family
    // instances essentially never produce.
    assert_eq!(header_candidate(2260, 3164, 1581), None);
    // More sign variables than the variable count leaves room for.
    assert_eq!(header_candidate(1582, 3164, 1582), None);
    // A forest: `E < N`, so there is no cycle and nothing to cut.
    assert_eq!(header_candidate(2000, 1000, 500), None);
    // Degenerate sizes.
    assert_eq!(header_candidate(0, 0, 0), None);
    assert_eq!(header_candidate(3, 2, 1), None);
}

/// The gate must not depend on instance SIZE — that is the whole point of an
/// O(1) screen. Nothing here allocates or loops, so this is a shape lock.
#[test]
fn header_gate_is_size_independent() {
    for scale in [10u64, 1_000, 1_000_000, 1_000_000_000] {
        // A "square" instance where nothing lines up.
        assert_eq!(header_candidate(scale, scale, scale), None);
        // And one that does, at every scale.
        let edges = scale;
        let nodes = scale / 2;
        assert_eq!(
            header_candidate(edges + nodes, 2 * edges, edges),
            Some((edges, nodes))
        );
    }
}

// ---------------------------------------------------------------------------
// Layer 2: structure recovery is TOTAL or it declines.
// ---------------------------------------------------------------------------

#[test]
fn recovery_accounts_for_every_row_and_variable() {
    let (instance, _, _) = five_cycle_with_tail();
    let graph = recover(&instance).expect("the synthesized signed graph must recover");
    assert_eq!(graph.edges.len(), 7);
    assert_eq!(graph.nodes.len(), 7);
    assert_eq!(graph.edges.iter().filter(|e| e.differ).count(), 4);
}

#[test]
fn recovery_declines_when_one_row_is_perturbed() {
    let (mut instance, _, _) = triangle();
    // Change one coefficient so the row matches neither template. Every row must
    // be explained, so a single unexplained row must sink the whole recovery.
    instance.constraints[0].terms[1].coeff = 2;
    assert!(recover(&instance).is_none());
}

#[test]
fn recovery_declines_on_a_mixed_template_pair() {
    let (mut instance, _, _) = triangle();
    // Give edge 1 one EQUAL half and one DIFFER half. Both halves are legal rows
    // in isolation; only the PAIR is nonsense, which is exactly what a
    // per-row-only recognizer would miss.
    instance.constraints[1].terms[1].coeff = 1;
    instance.constraints[1].terms[2].coeff = 1;
    instance.constraints[1].rhs = 1;
    assert!(recover(&instance).is_none());
}

#[test]
fn recovery_declines_when_a_variable_is_unaccounted_for() {
    let (mut instance, _, _) = triangle();
    // Declare a variable that appears nowhere: the family has exactly `E + N`.
    instance.num_vars += 1;
    assert!(recover(&instance).is_none());
}

#[test]
fn recovery_declines_on_an_equality_row() {
    let (mut instance, _, _) = triangle();
    instance.constraints[0].rel = PbRel::Eq;
    assert!(recover(&instance).is_none());
}

#[test]
fn recovery_declines_on_a_non_unit_objective() {
    let (mut instance, _, _) = triangle();
    if let Some(objective) = instance.objective.as_mut() {
        objective.terms[0].coeff = 2;
    }
    assert!(recover(&instance).is_none());
}

#[test]
fn two_core_drops_the_bridges_and_keeps_the_cycle() {
    let (instance, _, _) = five_cycle_with_tail();
    let graph = recover(&instance).expect("recovery");
    let alive = two_core(&graph);
    assert_eq!(alive.iter().filter(|&&a| a).count(), 5);
    assert!(
        !alive[5],
        "the tail edges are bridges and cannot carry a cycle"
    );
    assert!(!alive[6]);
}

// ---------------------------------------------------------------------------
// Emission.
// ---------------------------------------------------------------------------

#[test]
fn certifies_a_single_frustrated_triangle() {
    let (instance, incumbent, optimum) = triangle();
    assert_eq!(optimum, 1);
    let proof = certify(&instance, &incumbent, optimum).expect("the triangle must certify");
    assert!(proof.starts_with("pseudo-Boolean proof version 3.0\nf 6 ;\n"));
    assert!(
        proof.contains("conclusion BOUNDS 1 : "),
        "must conclude an equal-bounds optimality claim, got:\n{proof}"
    );
    assert!(proof.ends_with("end pseudo-Boolean proof;\n"));
    // `pol` and nothing else: no `red`, no `rup`, no `soli`, no extension
    // variable anywhere in the derivation.
    for line in proof.lines().skip(2) {
        assert!(
            line.starts_with("pol ")
                || line.starts_with("output ")
                || line.starts_with("conclusion ")
                || line.starts_with("end "),
            "unexpected rule in a pol-only proof: {line}"
        );
    }
    // Three lines per cut, one combine, one divide.
    assert_eq!(proof.lines().filter(|l| l.starts_with("pol ")).count(), 5);
}

#[test]
fn certifies_two_disjoint_triangles() {
    let (instance, incumbent, optimum) = two_triangles();
    assert_eq!(optimum, 2);
    let proof = certify(&instance, &incumbent, optimum).expect("two triangles must certify");
    assert!(proof.contains("conclusion BOUNDS 2 : "));
    // Two cuts: six derivation lines plus the combine and the divide.
    assert_eq!(proof.lines().filter(|l| l.starts_with("pol ")).count(), 8);
}

#[test]
fn certifies_a_five_cycle_with_a_tail() {
    let (instance, incumbent, optimum) = five_cycle_with_tail();
    assert_eq!(optimum, 1);
    let proof = certify(&instance, &incumbent, optimum).expect("the 5-cycle must certify");
    assert!(proof.contains("conclusion BOUNDS 1 : "));
    // The bridge edges carry no cut but must still be lifted to the denominator
    // in the combine line, or the final division would not reach the objective.
    let combine = proof
        .lines()
        .rev()
        .find(|l| l.starts_with("pol ") && l.contains(" x"))
        .expect("a combine line with literal axioms");
    assert!(
        combine.contains("x6 "),
        "bridge edge x6 must be slack-filled"
    );
    assert!(
        combine.contains("x7 "),
        "bridge edge x7 must be slack-filled"
    );
}

/// The emitted bytes must not depend on anything outside the instance.
#[test]
fn emission_is_byte_deterministic() {
    let (instance, incumbent, optimum) = five_cycle_with_tail();
    let first = certify(&instance, &incumbent, optimum).expect("first run");
    let second = certify(&instance, &incumbent, optimum).expect("second run");
    assert_eq!(first, second);
}

// ---------------------------------------------------------------------------
// Layer 3: the incumbent and the bound.
// ---------------------------------------------------------------------------

#[test]
fn declines_an_infeasible_incumbent() {
    let (instance, mut incumbent, optimum) = triangle();
    // Turn off the error variable the frustrated triangle forces on.
    incumbent[2] = false;
    assert!(!incumbent_is_feasible(&instance, &incumbent));
    assert!(certify(&instance, &incumbent, optimum).is_none());
}

#[test]
fn declines_when_the_incumbent_does_not_achieve_the_claimed_optimum() {
    let (instance, incumbent, _) = triangle();
    assert!(certify(&instance, &incumbent, 2).is_none());
}

#[test]
fn declines_a_claimed_optimum_the_packing_cannot_reach() {
    // A frustrated triangle plus a balanced (EQUAL-only) triangle sharing no
    // vertex: the true optimum is 1, so claiming 2 must be refused even though
    // the instance is squarely in the family.
    let edges = [
        (0usize, 1usize, Kind::Equal),
        (1, 2, Kind::Equal),
        (2, 0, Kind::Differ),
        (3, 4, Kind::Equal),
        (4, 5, Kind::Equal),
        (5, 3, Kind::Equal),
    ];
    let instance = signed_instance(6, &edges);
    let (mut incumbent, cost) = incumbent_for(6, &edges, &[true, true, true, true, true, true]);
    assert_eq!(cost, 1);
    // Pay for an extra edge that did not need paying: still feasible, value 2.
    incumbent[3] = true;
    assert!(incumbent_is_feasible(&instance, &incumbent));
    assert!(
        certify(&instance, &incumbent, 2).is_none(),
        "the cut family reaches 1 here; a claim of 2 must be withheld, not emitted weaker"
    );
}

#[test]
fn declines_a_balanced_graph() {
    // No frustrated cycle at all: every edge is satisfiable, optimum 0.
    let edges = [
        (0usize, 1usize, Kind::Equal),
        (1, 2, Kind::Equal),
        (2, 0, Kind::Equal),
    ];
    let instance = signed_instance(3, &edges);
    let (incumbent, cost) = incumbent_for(3, &edges, &[true, true, true]);
    assert_eq!(cost, 0);
    assert!(certify(&instance, &incumbent, 0).is_none());
    assert!(certify(&instance, &incumbent, 1).is_none());
}

#[test]
fn declines_when_the_row_cap_is_exceeded() {
    let (instance, incumbent, optimum) = triangle();
    let tiny = Limits {
        max_rows: 2,
        ..Limits::production()
    };
    assert!(certify_with_limits(&instance, &incumbent, optimum, tiny).is_none());
    // ... and the same instance certifies at the production cap, so the decline
    // above is the cap and not a latent failure.
    assert!(certify(&instance, &incumbent, optimum).is_some());
}

// ---------------------------------------------------------------------------
// Layer 4: the self-check, against mutations of the emitter's OWN output.
// ---------------------------------------------------------------------------

/// Re-runs the self-check against a mutated copy of a genuine proof.
fn self_check_mutant(mutate: impl Fn(&str) -> String) -> bool {
    let (instance, incumbent, optimum) = two_triangles();
    let proof = certify(&instance, &incumbent, optimum).expect("baseline proof");
    let floor_id = proof
        .lines()
        .find_map(|l| l.strip_prefix("conclusion BOUNDS "))
        .and_then(|rest| rest.split(" : ").nth(1))
        .and_then(|part| part.split_whitespace().next())
        .and_then(|id| id.parse::<u64>().ok())
        .expect("the conclusion must carry a hint id");
    let mutant = mutate(&proof);
    assert_ne!(mutant, proof, "the mutation must change the proof");
    self_check(&mutant, &instance, &incumbent, optimum, floor_id)
}

#[test]
fn self_check_accepts_the_genuine_proof() {
    let (instance, incumbent, optimum) = two_triangles();
    let proof = certify(&instance, &incumbent, optimum).expect("baseline proof");
    let floor_id = proof
        .lines()
        .find_map(|l| l.strip_prefix("conclusion BOUNDS "))
        .and_then(|rest| rest.split(" : ").nth(1))
        .and_then(|part| part.split_whitespace().next())
        .and_then(|id| id.parse::<u64>().ok())
        .expect("hint id");
    assert!(self_check(&proof, &instance, &incumbent, optimum, floor_id));
}

#[test]
fn self_check_rejects_an_inflated_lower_bound() {
    assert!(!self_check_mutant(
        |p| p.replace("conclusion BOUNDS 2 : ", "conclusion BOUNDS 3 : ")
    ));
}

#[test]
fn self_check_rejects_a_dropped_saturation() {
    assert!(!self_check_mutant(|p| p.replacen(" s ;", " ;", 1)));
}

#[test]
fn self_check_rejects_a_final_divisor_that_changes_the_derived_row() {
    // The combine row is `12·Σ x_e >= 24` here. Dividing by 25 rounds the degree
    // down to 1, so the cited row no longer carries the claimed bound of 2.
    assert!(!self_check_mutant(|p| replace_final_divisor(p, 25)));
}

/// A DOCUMENTED MAY-ACCEPT, recorded rather than deleted.
///
/// Raising the final divisor from 12 to 13 on `12·Σ x_e >= 24` yields
/// `ceil(12/13) = 1` and `ceil(24/13) = 2` — the SAME row. It is a different but
/// entirely legal derivation of the true bound, so accepting it is correct, and
/// a battery that filed it as must-reject would be testing the emitter's habits
/// instead of the proof's soundness. This is the same negative the
/// clique-coloring battery already records for `cycle-divisor-2to3`.
#[test]
fn a_divisor_that_derives_the_same_row_is_correctly_accepted() {
    assert!(self_check_mutant(|p| replace_final_divisor(p, 13)));
}

/// Rewrites the divisor of the LAST `pol … d ;` line (the objective division).
fn replace_final_divisor(proof: &str, divisor: i128) -> String {
    let lines: Vec<&str> = proof.lines().collect();
    let index = lines
        .iter()
        .rposition(|l| l.starts_with("pol ") && l.ends_with(" d ;"))
        .expect("a final division");
    // `pol <id> <divisor> d ;`
    let tokens: Vec<&str> = lines[index].split_whitespace().collect();
    assert_eq!(
        tokens.len(),
        5,
        "unexpected division line: {}",
        lines[index]
    );
    let replaced = format!("pol {} {divisor} d ;", tokens[1]);
    let mut out = lines.clone();
    out[index] = &replaced;
    format!("{}\n", out.join("\n"))
}

#[test]
fn self_check_rejects_a_dropped_summand() {
    assert!(!self_check_mutant(|p| {
        // Drop the last cut from the combine line: the derived floor then falls
        // below the claimed bound.
        let lines: Vec<&str> = p.lines().collect();
        let index = lines
            .iter()
            .rposition(|l| l.starts_with("pol ") && l.contains(" * +"))
            .expect("a combine line");
        let body = lines[index];
        let cut = body.find(" * +").expect("a summand");
        let trimmed = format!("{} ;", &body[..cut - 2].trim_end());
        let mut out = lines.clone();
        out[index] = &trimmed;
        format!("{}\n", out.join("\n"))
    }));
}

#[test]
fn self_check_rejects_a_pol_operand_that_was_never_derived() {
    assert!(!self_check_mutant(|p| p.replacen("pol 1 ", "pol 9999 ", 1)));
}

#[test]
fn self_check_rejects_truncation_before_the_conclusion() {
    assert!(!self_check_mutant(|p| {
        let index = p.find("output NONE;").expect("an output line");
        p[..index].to_string()
    }));
}

#[test]
fn self_check_rejects_a_witness_that_is_not_the_incumbent() {
    assert!(!self_check_mutant(|p| {
        let (head, witness) = p.rsplit_once(" : ").expect("a witness");
        let flipped: Vec<String> = witness
            .trim_end()
            .trim_end_matches(";\nend pseudo-Boolean proof;")
            .split_whitespace()
            .enumerate()
            .map(|(index, literal)| {
                if index == 0 {
                    literal
                        .strip_prefix('~')
                        .map_or_else(|| format!("~{literal}"), ToString::to_string)
                } else {
                    literal.to_string()
                }
            })
            .collect();
        format!(
            "{head} : {};\nend pseudo-Boolean proof;\n",
            flipped.join(" ")
        )
    }));
}

#[test]
fn self_check_rejects_a_witness_with_a_literal_dropped() {
    assert!(!self_check_mutant(|p| {
        let (head, witness) = p.rsplit_once(" : ").expect("a witness");
        let kept: Vec<&str> = witness
            .trim_end()
            .trim_end_matches(";\nend pseudo-Boolean proof;")
            .split_whitespace()
            .skip(1)
            .collect();
        format!("{head} : {};\nend pseudo-Boolean proof;\n", kept.join(" "))
    }));
}

#[test]
fn self_check_rejects_an_injected_rup() {
    assert!(!self_check_mutant(|p| p.replacen(
        "output NONE;",
        "rup >= 1 ;\noutput NONE;",
        1
    )));
}

#[test]
fn self_check_rejects_a_cross_instance_proof() {
    // A proof for the two-triangle instance, replayed against the five-cycle
    // instance: the row ids resolve to different constraints entirely.
    let (source, source_incumbent, source_optimum) = two_triangles();
    let proof = certify(&source, &source_incumbent, source_optimum).expect("baseline");
    let floor_id = proof
        .lines()
        .find_map(|l| l.strip_prefix("conclusion BOUNDS "))
        .and_then(|rest| rest.split(" : ").nth(1))
        .and_then(|part| part.split_whitespace().next())
        .and_then(|id| id.parse::<u64>().ok())
        .expect("hint id");
    let (other, other_incumbent, other_optimum) = five_cycle_with_tail();
    assert!(!self_check(
        &proof,
        &other,
        &other_incumbent,
        other_optimum,
        floor_id
    ));
}

// ---------------------------------------------------------------------------
// The packing itself.
// ---------------------------------------------------------------------------

#[test]
fn packing_reaches_the_optimum_on_a_shared_edge_pair() {
    // Two frustrated triangles sharing one edge. The optimum is 1 (paying the
    // shared edge kills both), so a packing that double-counted would overshoot
    // and one that stopped at a maximal integral packing would still reach it.
    let edges = [
        (0usize, 1usize, Kind::Equal),
        (1, 2, Kind::Equal),
        (2, 0, Kind::Differ),
        (1, 3, Kind::Equal),
        (3, 0, Kind::Equal),
    ];
    let instance = signed_instance(4, &edges);
    let graph = recover(&instance).expect("recovery");
    let packing = packing::build(&graph, 1, Limits::production()).expect("a packing");
    assert_eq!(floor_of(&packing), 1);
    // No edge may be loaded above the denominator; that is what makes the
    // combine line's slack fill non-negative and the proof valid.
    assert!(packing
        .load
        .iter()
        .all(|&value| value <= packing.denominator));
}

#[test]
fn packing_load_never_exceeds_the_denominator() {
    for (instance, _, _) in [triangle(), two_triangles(), five_cycle_with_tail()] {
        let graph = recover(&instance).expect("recovery");
        let packing = packing::build(&graph, 1, Limits::production()).expect("a packing");
        assert!(packing
            .load
            .iter()
            .all(|&value| value <= packing.denominator));
        let mut recomputed = vec![0i128; graph.edges.len()];
        for (index, walk) in packing.walks.iter().enumerate() {
            let multiplier = packing.numerators[index];
            for &(edge, _) in walk {
                recomputed[edge] += multiplier;
            }
        }
        assert_eq!(recomputed, packing.load);
    }
}
