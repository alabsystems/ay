// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the odd-cycle minimum-vertex-cover certifier.
//!
//! Every instance here is SYNTHESIZED in this file, so the gate needs no
//! external corpus and cannot silently pass because a benchmark went missing —
//! the failure mode recorded in `vacuous-harness-window`, where a gate selected
//! zero instances and reported green.

use super::packing::Limits;
use super::*;
use crate::types::{PbConstraint, PbLit, PbObjective, PbTerm};

fn term(coeff: i128, var: u32) -> PbTerm {
    PbTerm {
        coeff,
        lits: vec![PbLit {
            var,
            negated: false,
        }],
    }
}

/// Builds a pure minimum-vertex-cover instance on `n` vertices (`x1..xn`).
///
/// `edges` is `(u, v)` over 1-based variable numbers.
fn vc_instance(n: u32, edges: &[(u32, u32)]) -> PbInstance {
    let constraints: Vec<PbConstraint> = edges
        .iter()
        .map(|&(u, v)| PbConstraint {
            terms: vec![term(1, u), term(1, v)],
            rel: PbRel::Ge,
            rhs: 1,
        })
        .collect();
    PbInstance {
        num_vars: n,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: Some(PbObjective {
            terms: (1..=n).map(|i| term(1, i)).collect(),
        }),
    }
}

/// A cover as a `num_vars`-long assignment.
fn cover(n: u32, chosen: &[u32]) -> Vec<bool> {
    let mut out = vec![false; n as usize];
    for &v in chosen {
        out[(v - 1) as usize] = true;
    }
    out
}

/// The 5-cycle `x1..x5`. `LP* = 2.5`, optimum `3`, so the LP-dual route is dead
/// and one odd-cycle cut closes it exactly.
fn five_cycle() -> (PbInstance, Vec<bool>, i128) {
    let instance = vc_instance(5, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 1)]);
    (instance, cover(5, &[1, 2, 4]), 3)
}

/// Two vertex-disjoint triangles: `x1x2x3` and `x4x5x6`. Optimum `4`.
fn two_triangles() -> (PbInstance, Vec<bool>, i128) {
    let instance = vc_instance(6, &[(1, 2), (2, 3), (3, 1), (4, 5), (5, 6), (6, 4)]);
    (instance, cover(6, &[1, 2, 4, 5]), 4)
}

/// A path `x1-x2-x3-x4` — BIPARTITE, so the odd-cycle phase finds nothing and
/// the residual matching alone must reach the optimum of `2`.
fn bipartite_path() -> (PbInstance, Vec<bool>, i128) {
    let instance = vc_instance(4, &[(1, 2), (2, 3), (3, 4)]);
    (instance, cover(4, &[2, 3]), 2)
}

fn certify(instance: &PbInstance, incumbent: &[bool], optimum: i128) -> Option<String> {
    certify_opt_lin_odd_cycle_cover(instance, incumbent, optimum)
}

fn floor_id_of(proof: &str) -> u64 {
    proof
        .lines()
        .find_map(|l| l.strip_prefix("conclusion BOUNDS "))
        .and_then(|rest| rest.split(" : ").nth(1))
        .and_then(|part| part.split_whitespace().next())
        .and_then(|id| id.parse::<u64>().ok())
        .expect("the conclusion must carry a hint id")
}

// ---------------------------------------------------------------------------
// Layer 1: the O(1) pre-gate.
// ---------------------------------------------------------------------------

#[test]
fn pre_gate_accepts_the_family_shape() {
    assert!(header_candidate(5, 5, 5));
}

#[test]
fn pre_gate_rejects_an_objective_that_does_not_pay_every_variable() {
    assert!(!header_candidate(5, 5, 4));
    assert!(!header_candidate(5, 5, 6));
}

#[test]
fn pre_gate_rejects_a_constraintless_or_tiny_instance() {
    assert!(!header_candidate(5, 0, 5));
    assert!(!header_candidate(2, 1, 2));
}

// ---------------------------------------------------------------------------
// Layer 2: structure recovery is TOTAL or it declines.
// ---------------------------------------------------------------------------

#[test]
fn recovers_the_five_cycle() {
    let (instance, _, _) = five_cycle();
    let graph = recover(&instance).expect("the 5-cycle is in the family");
    assert_eq!(graph.order(), 5);
    for v in 0..5u32 {
        assert_eq!(graph.neighbours(v).len(), 2);
    }
}

#[test]
fn recovery_declines_a_row_with_three_literals() {
    let (mut instance, _, _) = five_cycle();
    instance.constraints[0].terms.push(term(1, 3));
    assert!(recover(&instance).is_none());
}

#[test]
fn recovery_declines_a_row_whose_rhs_is_not_one() {
    let (mut instance, _, _) = five_cycle();
    instance.constraints[0].rhs = 2;
    assert!(recover(&instance).is_none());
}

#[test]
fn recovery_declines_a_negated_literal() {
    let (mut instance, _, _) = five_cycle();
    instance.constraints[0].terms[0].lits[0].negated = true;
    assert!(recover(&instance).is_none());
}

#[test]
fn recovery_declines_a_non_unit_coefficient() {
    let (mut instance, _, _) = five_cycle();
    instance.constraints[0].terms[0].coeff = 2;
    assert!(recover(&instance).is_none());
}

#[test]
fn recovery_declines_an_equality_row() {
    let (mut instance, _, _) = five_cycle();
    instance.constraints[0].rel = PbRel::Eq;
    assert!(recover(&instance).is_none());
}

#[test]
fn recovery_declines_a_self_loop() {
    let (mut instance, _, _) = five_cycle();
    instance.constraints[0].terms[1] = term(1, 1);
    assert!(recover(&instance).is_none());
}

#[test]
fn recovery_declines_a_parallel_edge() {
    // `x1 + x2 >= 1` twice: summing a cycle through it would put coefficient 4,
    // not 2, on those vertices and the `2 d` arithmetic would not hold.
    let instance = vc_instance(5, &[(1, 2), (1, 2), (2, 3), (3, 4), (4, 5), (5, 1)]);
    assert!(recover(&instance).is_none());
}

#[test]
fn recovery_declines_an_objective_that_pays_a_variable_twice() {
    let (mut instance, _, _) = five_cycle();
    instance.objective.as_mut().unwrap().terms[4] = term(1, 1);
    assert!(recover(&instance).is_none());
}

#[test]
fn recovery_declines_a_weighted_objective() {
    let (mut instance, _, _) = five_cycle();
    instance.objective.as_mut().unwrap().terms[0].coeff = 2;
    assert!(recover(&instance).is_none());
}

#[test]
fn recovery_declines_when_there_is_no_objective() {
    let (mut instance, _, _) = five_cycle();
    instance.objective = None;
    assert!(recover(&instance).is_none());
}

// ---------------------------------------------------------------------------
// Layer 3: the incumbent, and the OPTIMALITY contract.
// ---------------------------------------------------------------------------

#[test]
fn certifies_the_five_cycle() {
    let (instance, incumbent, optimum) = five_cycle();
    let proof = certify(&instance, &incumbent, optimum).expect("one odd-cycle cut closes C5");
    assert!(proof.contains("pol 1 2 + 3 + 4 + 5 + 2 d ;"));
    assert!(proof.contains("conclusion BOUNDS 3 : "));
}

#[test]
fn certifies_two_disjoint_triangles() {
    let (instance, incumbent, optimum) = two_triangles();
    assert!(certify(&instance, &incumbent, optimum).is_some());
}

#[test]
fn certifies_a_bipartite_instance_by_the_residual_matching_alone() {
    let (instance, incumbent, optimum) = bipartite_path();
    let proof = certify(&instance, &incumbent, optimum).expect("Koenig closes a path");
    // No cycle cut: the only `pol` line is the combine.
    assert_eq!(proof.lines().filter(|l| l.starts_with("pol ")).count(), 1);
}

#[test]
fn declines_an_infeasible_incumbent() {
    let (instance, _, optimum) = five_cycle();
    // `x1 x2 x3` leaves the edge `x4-x5` uncovered.
    let bogus = cover(5, &[1, 2, 3]);
    assert!(certify(&instance, &bogus, optimum).is_none());
}

#[test]
fn declines_when_the_incumbent_does_not_achieve_the_claimed_optimum() {
    let (instance, incumbent, _) = five_cycle();
    assert!(certify(&instance, &incumbent, 2).is_none());
    assert!(certify(&instance, &incumbent, 4).is_none());
}

#[test]
fn declines_a_claimed_optimum_the_packing_cannot_reach() {
    // K4: optimum 3, but the odd-cycle packing finds ONE triangle (bound 2) and
    // the leftover single vertex matches nothing, so the floor is 2 < 3.
    // The rung's contract is OPTIMALITY, so a genuine but weaker bound is
    // withheld rather than published.
    let instance = vc_instance(4, &[(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]);
    let incumbent = cover(4, &[1, 2, 3]);
    assert!(certify(&instance, &incumbent, 3).is_none());
}

#[test]
fn declines_a_non_positive_optimum() {
    let (instance, incumbent, _) = five_cycle();
    assert!(certify(&instance, &incumbent, 0).is_none());
}

#[test]
fn declines_when_the_vertex_cap_is_exceeded() {
    let (instance, incumbent, optimum) = five_cycle();
    let tight = Limits {
        max_vertices: 4,
        ..Limits::production()
    };
    assert!(certify_with_limits(&instance, &incumbent, optimum, tight).is_none());
    // ... and the same instance certifies at the production cap, so the decline
    // is the cap and not the instance.
    assert!(certify(&instance, &incumbent, optimum).is_some());
}

#[test]
fn the_relaxation_budget_is_the_currency_the_search_actually_spends() {
    // The cap is documented as sized from measurement; this pins the other end
    // of that claim, that a family instance spends a tiny fraction of it.
    let (instance, _, _) = two_triangles();
    let graph = recover(&instance).expect("in family");
    let pack = packing::build(&graph, Limits::production()).expect("packing");
    assert_eq!(pack.bound, 4);
    assert!(pack.relaxations > 0, "the search must have done work");
    assert!(
        pack.relaxations < Limits::production().max_relaxations / 1000,
        "two triangles spent {} relaxations",
        pack.relaxations
    );
}

#[test]
fn declines_when_the_relaxation_budget_is_exhausted() {
    let (instance, incumbent, optimum) = five_cycle();
    let starved = Limits {
        max_relaxations: 1,
        ..Limits::production()
    };
    assert!(certify_with_limits(&instance, &incumbent, optimum, starved).is_none());
}

// ---------------------------------------------------------------------------
// Determinism: the emitted bytes must not depend on anything but the instance.
// ---------------------------------------------------------------------------

#[test]
fn emission_is_byte_identical_across_runs() {
    let (instance, incumbent, optimum) = two_triangles();
    let first = certify(&instance, &incumbent, optimum).expect("proof");
    for _ in 0..8 {
        assert_eq!(
            certify(&instance, &incumbent, optimum).as_deref(),
            Some(&*first)
        );
    }
}

// ---------------------------------------------------------------------------
// Layer 4: the adversarial battery against the emitted BYTES.
// ---------------------------------------------------------------------------

/// Re-runs the self-check against a mutated copy of a genuine proof.
fn self_check_mutant(mutate: impl Fn(&str) -> String) -> bool {
    let (instance, incumbent, optimum) = two_triangles();
    let proof = certify(&instance, &incumbent, optimum).expect("baseline proof");
    let floor_id = floor_id_of(&proof);
    let mutant = mutate(&proof);
    assert_ne!(mutant, proof, "the mutation must change the proof");
    self_check(&mutant, &instance, &incumbent, optimum, floor_id)
}

#[test]
fn self_check_accepts_the_genuine_proof() {
    let (instance, incumbent, optimum) = two_triangles();
    let proof = certify(&instance, &incumbent, optimum).expect("baseline proof");
    let floor_id = floor_id_of(&proof);
    assert!(self_check(&proof, &instance, &incumbent, optimum, floor_id));
}

#[test]
fn self_check_rejects_an_inflated_lower_bound() {
    assert!(!self_check_mutant(
        |p| p.replace("conclusion BOUNDS 4 : ", "conclusion BOUNDS 5 : ")
    ));
}

#[test]
fn self_check_rejects_a_dropped_division() {
    // Without `2 d` the cited row is `2·Σ_C x_v >= 3`, not `Σ_C x_v >= 2`.
    assert!(!self_check_mutant(|p| p.replacen(" 2 d ;", " ;", 1)));
}

#[test]
fn self_check_rejects_a_divisor_of_three() {
    // `2·Σ x >= 3` divided by 3 is `Σ x >= 1`, so the packing no longer reaches 4.
    assert!(!self_check_mutant(|p| p.replacen(" 2 d ;", " 3 d ;", 1)));
}

#[test]
fn self_check_rejects_a_dropped_cycle_row() {
    // A triangle summed from two rows instead of three.
    assert!(!self_check_mutant(|p| p.replacen(
        "pol 1 2 + 3 + 2 d ;",
        "pol 1 2 + 2 d ;",
        1
    )));
}

#[test]
fn self_check_rejects_a_repeated_cycle_row() {
    assert!(!self_check_mutant(|p| p.replacen(
        "pol 1 2 + 3 + 2 d ;",
        "pol 1 2 + 2 + 2 d ;",
        1
    )));
}

#[test]
fn self_check_rejects_a_cycle_over_the_wrong_rows() {
    // Rows 1,2,4 are not a cycle: the sum is not `2·Σ` over any vertex set.
    assert!(!self_check_mutant(|p| p.replacen(
        "pol 1 2 + 3 + 2 d ;",
        "pol 1 2 + 4 + 2 d ;",
        1
    )));
}

#[test]
fn self_check_rejects_a_shifted_row_id() {
    assert!(!self_check_mutant(|p| p.replacen(
        "pol 1 2 + 3 + 2 d ;",
        "pol 2 3 + 4 + 2 d ;",
        1
    )));
}

#[test]
fn self_check_rejects_a_wrong_f_count() {
    assert!(!self_check_mutant(|p| p.replacen("f 6 ;", "f 7 ;", 1)));
}

#[test]
fn self_check_rejects_a_truncated_proof() {
    assert!(!self_check_mutant(|p| {
        let mut lines: Vec<&str> = p.lines().collect();
        lines.remove(2);
        format!("{}\n", lines.join("\n"))
    }));
}

#[test]
fn self_check_rejects_a_missing_end_line() {
    assert!(!self_check_mutant(
        |p| p.replace("end pseudo-Boolean proof;\n", "")
    ));
}

#[test]
fn self_check_rejects_a_wrong_header() {
    assert!(!self_check_mutant(|p| p.replacen(
        "pseudo-Boolean proof version 3.0",
        "pseudo-Boolean proof version 2.0",
        1
    )));
}

#[test]
fn self_check_rejects_a_rup_rule() {
    // Nothing but `pol` may appear: a `rup` line is an assumption this module
    // has no way to model, so it is refused rather than replayed.
    assert!(!self_check_mutant(|p| p.replacen("pol ", "rup ", 1)));
}

#[test]
fn self_check_rejects_a_hint_at_the_wrong_row() {
    assert!(!self_check_mutant(|p| {
        let id = floor_id_of(p);
        p.replace(&format!(" : {id} "), &format!(" : {} ", id - 1))
    }));
}

#[test]
fn self_check_rejects_a_mismatched_upper_bound() {
    assert!(!self_check_mutant(|p| p.replace(" 4 : x1", " 5 : x1")));
}

#[test]
fn self_check_rejects_a_tampered_witness() {
    assert!(!self_check_mutant(
        |p| p.replace(" : x1 x2 ~x3", " : ~x1 x2 ~x3")
    ));
}

#[test]
fn self_check_rejects_a_dropped_literal_axiom_fill() {
    // Vertex 6 is isolated: the packing never loads it, so the combine fills
    // its objective coefficient with the literal axiom `x6 >= 0`. Dropping that
    // operand leaves a floor row whose support misses `x6` — a TRUE but weaker
    // bound (`x6 >= 0` re-implies it), which the floor-support check must
    // refuse to publish as the optimum.
    let instance = vc_instance(6, &[(1, 2), (2, 3), (3, 1), (4, 5)]);
    let incumbent = cover(6, &[1, 2, 4]);
    let proof =
        certify(&instance, &incumbent, 3).expect("triangle + one matched edge + axiom fill");
    assert!(
        proof.contains(" x6 +"),
        "the literal-axiom fill must actually appear in the combine"
    );
    let floor_id = floor_id_of(&proof);
    let mutant = proof.replacen(" x6 +", "", 1);
    assert_ne!(mutant, proof, "the mutation must change the proof");
    assert!(!self_check(&mutant, &instance, &incumbent, 3, floor_id));
}

#[test]
fn self_check_rejects_a_cross_instance_proof() {
    // The 5-cycle's proof replayed against the two-triangle instance.
    let (five, five_inc, five_opt) = five_cycle();
    let proof = certify(&five, &five_inc, five_opt).expect("C5 proof");
    let floor_id = floor_id_of(&proof);
    let (six, six_inc, six_opt) = two_triangles();
    assert!(!self_check(&proof, &six, &six_inc, six_opt, floor_id));
    // ... and the mirror image.
    let other = certify(&six, &six_inc, six_opt).expect("two-triangle proof");
    let other_floor = floor_id_of(&other);
    assert!(!self_check(&other, &five, &five_inc, five_opt, other_floor));
}

#[test]
fn self_check_rejects_a_combine_that_drops_a_cut() {
    assert!(!self_check_mutant(|p| {
        let lines: Vec<&str> = p.lines().collect();
        let index = lines
            .iter()
            .rposition(|l| l.starts_with("pol ") && !l.ends_with(" d ;"))
            .expect("a combine line");
        let mut out = lines.clone();
        let replaced = "pol 7 ;".to_string();
        out[index] = &replaced;
        format!("{}\n", out.join("\n"))
    }));
}

#[test]
fn self_check_rejects_a_combine_that_scales_a_cut() {
    assert!(!self_check_mutant(|p| {
        let lines: Vec<&str> = p.lines().collect();
        let index = lines
            .iter()
            .rposition(|l| l.starts_with("pol ") && !l.ends_with(" d ;"))
            .expect("a combine line");
        let mut out = lines.clone();
        let replaced = "pol 7 2 * 8 + ;".to_string();
        out[index] = &replaced;
        format!("{}\n", out.join("\n"))
    }));
}

// ---------------------------------------------------------------------------
// The pre-gate, measured against the repository's own OPB corpus.
// ---------------------------------------------------------------------------

/// Scans every TRACKED `.opb` in the repository and reports what the O(1) header
/// gate costs and how often it lets an off-family instance through to the
/// (fail-closed, `O(rows)`) recovery.
///
/// The scan's corpus-presence assertion and fail-closed traversal are part of
/// the test contract; the printed timing and family counts are measurements.
/// The numbers in this module's documentation can be reproduced with:
///
/// ```text
/// cargo test --release -p ay-pb-core --lib gate_scan -- --nocapture
/// ```
///
/// It PANICS when the corpus is missing rather than skipping. A gate scan that
/// silently selects zero files is exactly the vacuous-green failure recorded in
/// `vacuous-harness-window`, and a measurement that cannot fail is not one.
#[test]
fn gate_scan_over_the_tracked_opb_fixtures() {
    use std::path::{Path, PathBuf};
    use std::time::Instant;

    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        let mut items: Vec<PathBuf> = entries.filter_map(|e| e.ok().map(|e| e.path())).collect();
        items.sort();
        for path in items {
            if path.is_dir() {
                walk(&path, out);
            } else if path.extension().is_some_and(|e| e == "opb") {
                out.push(path);
            }
        }
    }

    // The repository ROOT, not `benchmarks/pb-comp`: the competition corpus is
    // not tracked, and a scan pointed at an untracked directory is the vacuous
    // harness this project has already been bitten by once. Everything scanned
    // here is committed, so the number is reproducible from a fresh clone.
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("the repository root must exist");
    let mut files = Vec::new();
    walk(&root.join("crates"), &mut files);
    walk(&root.join("ci"), &mut files);
    walk(&root.join("proofs"), &mut files);
    walk(&root.join("benchmarks"), &mut files);
    walk(&root.join("tests"), &mut files);
    assert!(
        files.len() > 50,
        "expected the tracked .opb fixtures, found {} under {}",
        files.len(),
        root.display()
    );

    let mut parsed = 0usize;
    let mut gate_accept = 0usize;
    let mut recover_accept = 0usize;
    let mut gate_ns: Vec<u128> = Vec::new();
    let mut false_accepts: Vec<String> = Vec::new();
    for path in &files {
        let Ok(text) = std::fs::read_to_string(path) else {
            continue;
        };
        let Ok(instance) = crate::parse_opb(&text) else {
            continue;
        };
        parsed += 1;
        let objective_len = instance.objective.as_ref().map_or(0, |o| o.terms.len()) as u64;
        let num_vars = u64::from(instance.num_vars);
        let num_cons = instance.constraints.len() as u64;
        let start = Instant::now();
        let mut sink = 0u64;
        for _ in 0..1000 {
            sink += u64::from(header_candidate(
                std::hint::black_box(num_vars),
                std::hint::black_box(num_cons),
                std::hint::black_box(objective_len),
            ));
        }
        std::hint::black_box(sink);
        gate_ns.push(start.elapsed().as_nanos() / 1000);
        if header_candidate(num_vars, num_cons, objective_len) {
            gate_accept += 1;
            if recover(&instance).is_some() {
                recover_accept += 1;
            } else {
                false_accepts.push(
                    path.file_name()
                        .map(|n| n.to_string_lossy().into_owned())
                        .unwrap_or_default(),
                );
            }
        }
    }
    gate_ns.sort_unstable();
    let median = gate_ns[gate_ns.len() / 2];
    println!("files={} parsed={parsed}", files.len());
    println!("gate_accept={gate_accept} recover_accept={recover_accept}");
    println!("gate_false_accept={}", false_accepts.len());
    for name in false_accepts.iter().take(40) {
        println!("  false-accept: {name}");
    }
    println!(
        "gate_ns_median={median} gate_ns_max={}",
        gate_ns[gate_ns.len() - 1]
    );
}

// ---------------------------------------------------------------------------
// FLOORS AS BOUNDS: `recovered_floor` — the pre-search dual floor.
// ---------------------------------------------------------------------------

/// The exact minimum vertex cover by exhaustive enumeration. Only callable on
/// instances `vc_instance` built, so the objective is `Σ x_v`.
fn brute_force_min_cover(n: u32, edges: &[(u32, u32)]) -> i128 {
    let n = n as usize;
    let mut best = n as i128;
    for mask in 0u32..(1 << n) {
        if edges
            .iter()
            .all(|&(u, v)| mask & (1 << (u - 1)) != 0 || mask & (1 << (v - 1)) != 0)
        {
            best = best.min(i128::from(mask.count_ones()));
        }
    }
    best
}

#[test]
fn recovered_floor_is_exact_on_the_odd_cycle() {
    let (instance, _, optimum) = five_cycle();
    assert_eq!(recovered_floor(&instance), Some(optimum));
}

#[test]
fn recovered_floor_is_exact_on_disjoint_triangles() {
    let (instance, _, optimum) = two_triangles();
    assert_eq!(recovered_floor(&instance), Some(optimum));
}

#[test]
fn recovered_floor_matches_koenig_on_the_bipartite_path() {
    let (instance, _, optimum) = bipartite_path();
    assert_eq!(recovered_floor(&instance), Some(optimum));
}

#[test]
fn recovered_floor_survives_isolated_vertices() {
    // C5 plus two isolated vertices: the optimum pays the cycle only.
    let instance = vc_instance(7, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 1)]);
    assert_eq!(recovered_floor(&instance), Some(3));
}

#[test]
fn recovered_floor_declines_off_family_rows() {
    // First row is a cardinality-3 row, not an edge row: the O(1) first-row
    // check must refuse before any per-row work.
    let mut instance = vc_instance(5, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 1)]);
    instance.constraints[0].terms.push(term(1, 3));
    assert_eq!(recovered_floor(&instance), None);
    // A weighted objective term breaks the unit-payment premise.
    let mut instance = vc_instance(5, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 1)]);
    instance.objective.as_mut().unwrap().terms[0].coeff = 2;
    assert_eq!(recovered_floor(&instance), None);
}

#[test]
fn chain_floor_refuses_a_mismatched_search_objective() {
    // The verdict-bearing entry point must refuse a caller whose SEARCH
    // objective is not literally the instance objective the recovery bounded.
    let (instance, _, optimum) = five_cycle();
    let same = instance.objective.clone().unwrap();
    assert_eq!(
        crate::proof::recovered_structural_search_floor(&instance, &same),
        Some(optimum)
    );
    let mut other = same.clone();
    other.terms[0].coeff = 2;
    assert_eq!(
        crate::proof::recovered_structural_search_floor(&instance, &other),
        None
    );
    let mut shorter = same;
    shorter.terms.pop();
    assert_eq!(
        crate::proof::recovered_structural_search_floor(&instance, &shorter),
        None
    );
}

/// THE soundness property the pre-search floor rests on: on random graphs the
/// packing bound NEVER exceeds the brute-force minimum vertex cover. 400
/// deterministic cases (fixed LCG), n in 3..=12, densities from tree-sparse to
/// near-complete, isolated vertices included — the same shape space as the
/// external 1,282-case fuzz that backs the certifier, reproduced in-tree so a
/// future packing edit cannot regress the FLOOR without failing here.
#[test]
fn recovered_floor_never_overshoots_brute_force() {
    let mut lcg: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut next = move || {
        lcg = lcg.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        lcg >> 33
    };
    let mut nontrivial = 0u32;
    for case in 0..400u32 {
        let n = 3 + (next() % 10) as u32; // 3..=12
        let density = 1 + next() % 100;
        let mut edges: Vec<(u32, u32)> = Vec::new();
        for u in 1..=n {
            for v in (u + 1)..=n {
                if next() % 100 < density {
                    edges.push((u, v));
                }
            }
        }
        if edges.is_empty() {
            continue;
        }
        let instance = vc_instance(n, &edges);
        let optimum = brute_force_min_cover(n, &edges);
        let Some(floor) = recovered_floor(&instance) else {
            panic!("case {case}: recovery declined a genuine family member");
        };
        assert!(
            floor <= optimum,
            "case {case} (n={n}, m={}): floor {floor} OVERSHOOTS optimum {optimum}",
            edges.len()
        );
        assert!(floor >= 1);
        if floor == optimum {
            nontrivial += 1;
        }
    }
    // The fuzz must not pass vacuously on a packing that always answers 1.
    assert!(nontrivial >= 100, "only {nontrivial} tight cases");
}
