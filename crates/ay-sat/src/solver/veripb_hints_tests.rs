// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-veripb-hints`: every annotated `rup <C> : <ids> ;` the solver writes
//! must be derivable by unit propagation over the listed constraints alone.
//! A small replay checker below verifies that independently of VeriPB.

use super::*;
use std::collections::HashMap;

fn switched(value: Option<bool>) -> ay_core::sat_ab_test_override::Guard {
    ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        veripb_hints: value,
        ..Default::default()
    })
}

/// Pigeonhole: `pigeons` pigeons, `pigeons - 1` holes (UNSAT). Variables are
/// numbered pigeon-major from 0.
fn pigeonhole(pigeons: u32) -> (usize, Vec<Vec<Literal>>) {
    let holes = pigeons - 1;
    let var = |p: u32, h: u32| Variable(p * holes + h);
    let mut clauses = Vec::new();
    for p in 0..pigeons {
        clauses.push((0..holes).map(|h| Literal::positive(var(p, h))).collect());
    }
    for h in 0..holes {
        for p in 0..pigeons {
            for q in (p + 1)..pigeons {
                clauses.push(vec![
                    Literal::negative(var(p, h)),
                    Literal::negative(var(q, h)),
                ]);
            }
        }
    }
    ((pigeons * holes) as usize, clauses)
}

/// Solve `clauses` on a VeriPB proof with the originals noted as the DIMACS
/// reader does; returns the proof text.
fn solve_with_veripb_proof(num_vars: usize, clauses: &[Vec<Literal>]) -> String {
    solve_on_veripb(num_vars, clauses, |_| {}).0
}

/// As `solve_with_veripb_proof`, configuring the solver first; returns the
/// solver too.
fn solve_on_veripb(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    configure: impl FnOnce(&mut Solver),
) -> (String, Solver) {
    let proof = ProofOutput::veripb_with_original_clauses(Vec::new(), clauses.len() as u64);
    let mut solver: Solver = Solver::with_proof_output(num_vars, proof);
    configure(&mut solver);
    for (i, clause) in clauses.iter().enumerate() {
        solver.note_veripb_original(clause, i as u64 + 1);
        solver.add_clause(clause.clone());
    }
    assert!(matches!(solver.solve().into_inner(), SatResult::Unsat(_)));
    let writer = solver.take_proof_writer().expect("proof writer");
    let text = String::from_utf8(writer.into_vec().expect("flush")).expect("utf8");
    (text, solver)
}

/// DIMACS-style signed literal of a proof term (`x3` is 3, `~x3` is -3).
fn term(token: &str) -> i64 {
    match token.strip_prefix('~') {
        Some(rest) => -rest[1..].parse::<i64>().expect("var"),
        None => token[1..].parse::<i64>().expect("var"),
    }
}

/// A pseudo-Boolean constraint `Σ coef·lit >= degree` (a clause has every
/// coefficient and the degree 1).
#[derive(Clone, PartialEq)]
struct Pb {
    terms: Vec<(i64, i64)>,
    degree: i64,
}

/// Parse `1 x1 1 ~x2 >= 1` (possibly empty before `>=`; any coefficients and
/// degree, as factoring's definitions have them); returns the constraint and
/// the tokens after the degree.
fn parse_constraint<'a>(tokens: &[&'a str]) -> (Pb, Vec<&'a str>) {
    let ge = tokens.iter().position(|t| *t == ">=").expect(">=");
    let terms = tokens[..ge]
        .chunks(2)
        .map(|pair| (pair[0].parse().expect("coefficient"), term(pair[1])))
        .collect();
    let degree = tokens[ge + 1].parse().expect("degree");
    (Pb { terms, degree }, tokens[ge + 2..].to_vec())
}

/// Replay every line, checking each annotated `rup` by propagation on its
/// hints alone as VeriPB does (a constraint whose slack is negative is a
/// conflict; a literal whose coefficient exceeds the slack is propagated);
/// returns (annotated lines checked, all lines).
fn replay(original: &[Vec<Literal>], proof: &str) -> (usize, usize) {
    let (annotated, lines, _) = replay_passes(original, proof);
    (annotated, lines)
}

/// `replay`, also counting the annotated steps whose hints reach their
/// conflict only in a second or later pass over the list (VeriPB checks
/// `rup C : ids` by propagating the ids in order, pass after pass).
fn replay_passes(original: &[Vec<Literal>], proof: &str) -> (usize, usize, usize) {
    let dimacs = |lit: &Literal| -> i64 {
        let v = i64::from(lit.variable().0) + 1;
        if lit.is_positive() {
            v
        } else {
            -v
        }
    };
    let mut live: HashMap<u64, Pb> = HashMap::new();
    for (i, clause) in original.iter().enumerate() {
        let terms = clause.iter().map(|l| (1, dimacs(l))).collect();
        live.insert(i as u64 + 1, Pb { terms, degree: 1 });
    }
    let mut next = original.len() as u64 + 1;
    let (mut annotated, mut lines, mut multi_pass) = (0, 0, 0);
    for line in proof.lines() {
        let tokens: Vec<&str> = line.trim_end_matches(';').split_whitespace().collect();
        match tokens.first().copied() {
            Some("rup") | Some("red") => {
                lines += 1;
                let (constraint, rest) = parse_constraint(&tokens[1..]);
                if tokens[0] == "rup" && rest.first() == Some(&":") {
                    let hints: Vec<u64> =
                        rest[1..].iter().map(|t| t.parse().expect("id")).collect();
                    assert_ne!(hints.len(), 0, "empty annotation in {line}");
                    // Assume the negation of C (a clause); propagate on the
                    // hints only.
                    let mut val: HashMap<i64, bool> = constraint
                        .terms
                        .iter()
                        .map(|&(_, l)| (l.abs(), l < 0))
                        .collect();
                    let mut conflict = false;
                    let mut passes = 0;
                    // Each round that makes progress assigns a new variable.
                    loop {
                        passes += 1;
                        let mut progress = false;
                        for id in &hints {
                            let c = live
                                .get(id)
                                .unwrap_or_else(|| panic!("hint {id} not live in {line}"));
                            let not_false: i64 = c
                                .terms
                                .iter()
                                .filter(|&&(_, l)| val.get(&l.abs()).is_none_or(|&b| b == (l > 0)))
                                .map(|&(a, _)| a)
                                .sum();
                            let slack = not_false - c.degree;
                            if slack < 0 {
                                conflict = true;
                                break;
                            }
                            for &(a, l) in &c.terms {
                                if a > slack && !val.contains_key(&l.abs()) {
                                    val.insert(l.abs(), l > 0);
                                    progress = true;
                                }
                            }
                        }
                        if conflict || !progress {
                            break;
                        }
                    }
                    assert!(conflict, "hints do not refute the negation of: {line}");
                    annotated += 1;
                    if passes > 1 {
                        multi_pass += 1;
                    }
                }
                live.insert(next, constraint);
                next += 1;
            }
            Some("del") if tokens.get(1) == Some(&"id") => {
                live.remove(&tokens[2].parse::<u64>().expect("id"));
            }
            Some("del") if tokens.get(1) == Some(&"spec") => {
                let (mut spec, _) = parse_constraint(&tokens[2..]);
                spec.terms.sort_unstable();
                let found = live
                    .iter()
                    .filter(|(_, c)| {
                        let mut c = (*c).clone();
                        c.terms.sort_unstable();
                        c == spec
                    })
                    .map(|(&id, _)| id)
                    .min();
                if let Some(id) = found {
                    live.remove(&id);
                }
            }
            _ => {}
        }
    }
    (annotated, lines, multi_pass)
}

#[test]
fn every_annotated_step_is_implied_by_its_hints() {
    let _guard = switched(Some(true));
    let (num_vars, clauses) = pigeonhole(6);
    let proof = solve_with_veripb_proof(num_vars, &clauses);
    let (annotated, lines, multi_pass) = replay_passes(&clauses, &proof);
    assert!(
        annotated > 0,
        "no annotated step in a proof of {lines} lines:\n{proof}"
    );
    // The hints list each reason after its antecedents: one pass checks them.
    assert_eq!(multi_pass, 0, "{proof}");
    assert!(proof.contains("conclusion UNSAT"), "{proof}");
}

#[test]
fn root_units_join_the_hints() {
    let _guard = switched(Some(true));
    // A pigeonhole with one extra pigeon forced into a hole by a unit: the
    // level-0 literals must be explained by unit constraints in the hints.
    let (num_vars, mut clauses) = pigeonhole(5);
    clauses.push(vec![Literal::positive(Variable(0))]);
    let proof = solve_with_veripb_proof(num_vars, &clauses);
    let (annotated, _) = replay(&clauses, &proof);
    assert!(annotated > 0, "{proof}");
}

#[test]
fn switched_off_writes_no_annotation() {
    let _guard = switched(None);
    let (num_vars, clauses) = pigeonhole(5);
    let proof = solve_with_veripb_proof(num_vars, &clauses);
    assert!(
        !proof
            .lines()
            .any(|l| l.starts_with("rup") && l.contains(" : ")),
        "{proof}"
    );
}

/// Pigeonhole whose at-most-one constraints are binary implication chains
/// p -> a1 -> ... -> a7 -> ~q: over 99 percent of the clauses are binary, so
/// binary propagation stores jump reasons, clauses no proof line holds.
fn pigeonhole_through_chains(pigeons: u32) -> (usize, Vec<Vec<Literal>>) {
    let (mut next, php) = pigeonhole(pigeons);
    let mut clauses = Vec::new();
    for clause in php {
        if clause.len() != 2 {
            clauses.push(clause);
            continue;
        }
        let mut from = clause[0].negated();
        for _ in 0..7 {
            let link = Literal::positive(Variable(next as u32));
            next += 1;
            clauses.push(vec![from.negated(), link]);
            from = link;
        }
        clauses.push(vec![from.negated(), clause[1]]);
    }
    (next, clauses)
}

#[test]
fn jump_reasons_are_hinted_through_their_real_binary() {
    let _guard = switched(Some(true));
    let (num_vars, clauses) = pigeonhole_through_chains(6);
    let binary = clauses.iter().filter(|c| c.len() == 2).count();
    assert!(
        binary * 100 >= clauses.len() * 99,
        "{binary} of {}",
        clauses.len()
    );
    let (proof, solver) = solve_on_veripb(num_vars, &clauses, |solver| {
        solver.set_preprocess_enabled(false);
    });
    let (annotated, lines, multi_pass) = replay_passes(&clauses, &proof);
    let st = &solver.cold.veripb_hints;
    assert!(
        solver.stats.jumped_reasons > 0,
        "no jump reason in {lines} lines"
    );
    assert!(
        st.jumps_resolved > 0,
        "{:?}",
        solver.veripb_hint_fail_profile()
    );
    assert_eq!(st.fallbacks, 0, "{:?}", solver.veripb_hint_fail_profile());
    assert!(annotated > 0);
    assert_eq!(multi_pass, 0, "{proof}");
}

#[test]
fn proof_add_passes_are_indexed_by_their_trace_code() {
    use crate::diagnostic_trace::DiagnosticPass;
    for (code, pass) in DiagnosticPass::BY_CODE.iter().enumerate() {
        assert_eq!(
            Solver::diagnostic_pass_code(*pass) as usize,
            code,
            "{pass:?}"
        );
    }
}

/// Simplification steps name their antecedents (`veripb_derived.rs`): after
/// preprocessing merges two copies of g = AND(a, b) (congruence, then
/// decompose's substitution) and eliminates variables (BVE), derived steps go
/// out as annotated RUP and every annotated line replays from its hints alone.
#[test]
fn simplification_steps_replay_from_their_hints() {
    let _guard = switched(Some(true));
    let v = |i: u32| Variable(i);
    let (a, b, g1, g2, c, d, e) = (v(0), v(1), v(2), v(3), v(4), v(5), v(6));
    let mut clauses = Vec::new();
    for g in [g1, g2] {
        clauses.push(vec![
            Literal::negative(a),
            Literal::negative(b),
            Literal::positive(g),
        ]);
        clauses.push(vec![Literal::positive(a), Literal::negative(g)]);
        clauses.push(vec![Literal::positive(b), Literal::negative(g)]);
    }
    clauses.push(vec![
        Literal::positive(g1),
        Literal::positive(c),
        Literal::positive(d),
    ]);
    clauses.push(vec![
        Literal::negative(g2),
        Literal::positive(c),
        Literal::positive(e),
    ]);
    clauses.push(vec![
        Literal::negative(c),
        Literal::positive(d),
        Literal::positive(e),
    ]);
    let proof = ProofOutput::veripb_with_original_clauses(Vec::new(), clauses.len() as u64);
    let mut solver: Solver = Solver::with_proof_output(7, proof);
    for (i, clause) in clauses.iter().enumerate() {
        solver.note_veripb_original(clause, i as u64 + 1);
        solver.add_clause(clause.clone());
    }
    solver.set_gate_enabled(true);
    solver.set_congruence_enabled(true);
    solver.set_decompose_enabled(true);
    solver.set_sweep_enabled(true);
    solver.set_backbone_enabled(true);
    solver.set_bve_enabled(true);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert!(!solver.preprocess(), "the formula is satisfiable");
    assert!(
        solver.congruence_stats().equivalences_found > 0,
        "congruence merges the gates"
    );
    assert!(solver.bve_stats().vars_eliminated > 0, "BVE eliminates");
    let derived = &solver.cold.veripb_hints.derived;
    assert!(
        derived.hinted > 0,
        "hinted {} plain {}",
        derived.hinted,
        derived.plain
    );
    let writer = solver.take_proof_writer().expect("proof writer");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("utf8");
    let (annotated, _) = replay(&clauses, &proof);
    assert!(annotated > 0, "{proof}");
}
