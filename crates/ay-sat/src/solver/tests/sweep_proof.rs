// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! proof-posture-parity: the three UNSAT outcomes of sweep that used to fall
//! back to search under a proof surface (an environment kitten refutes
//! outright, a rewrite that yields the empty clause, a contradicting unit)
//! now certify UNSAT in the proof, or fall back with the reason logged.
//!
//! Every certified path is checked twice: online by the forward DRUP checker
//! (no derived step may need trust) and offline by the crate's DRAT checker
//! on the emitted proof text, the same checker `ay check drat` runs.

use super::*;
use crate::ProofOutput;

/// Verify `proof` (DRAT text) against `clauses` with the standalone checker.
fn verify_drat(num_vars: usize, clauses: &[Vec<Literal>], proof: &[u8]) -> Result<(), String> {
    let mut cnf = format!("p cnf {num_vars} {}\n", clauses.len());
    for clause in clauses {
        for lit in clause {
            cnf.push_str(&lit.to_dimacs().to_string());
            cnf.push(' ');
        }
        cnf.push_str("0\n");
    }
    let parsed = ay_drat_check::cnf_parser::parse_cnf(cnf.as_bytes()).map_err(|e| e.to_string())?;
    let steps = ay_drat_check::drat_parser::parse_drat(proof).map_err(|e| e.to_string())?;
    let mut checker = ay_drat_check::checker::DratChecker::new(parsed.num_vars, true);
    checker
        .verify(&parsed.clauses, &steps)
        .map_err(|e| e.to_string())
}

/// A solver with a DRAT text proof surface and the online forward checker.
fn drat_solver(num_vars: usize, clauses: &[Vec<Literal>]) -> Solver {
    let mut solver: Solver =
        Solver::with_proof_output(num_vars, ProofOutput::drat_text(Vec::<u8>::new()));
    solver.enable_forward_checker();
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    solver
}

fn proof_text(solver: &mut Solver) -> String {
    let writer = solver
        .take_proof_writer()
        .expect("proof writer should exist with DRAT output");
    String::from_utf8(writer.into_vec().expect("flush")).expect("utf8")
}

fn has_empty_clause_line(text: &str) -> bool {
    text.lines()
        .any(|line| line.split_whitespace().collect::<Vec<_>>() == ["0"])
}

fn pos(v: u32) -> Literal {
    Literal::positive(Variable(v))
}

fn neg(v: u32) -> Literal {
    Literal::negative(Variable(v))
}

/// Give sweep a proportional budget large enough to probe every variable
/// (the first-call budget alone is `vars * 10` kitten ticks).
fn fund_sweep(solver: &mut Solver) {
    solver.search_ticks = [100_000_000, 0];
}

/// Site U: kitten refutes a COI environment outright. The whole 3-variable
/// formula (all eight sign patterns) is one environment; it is UNSAT but not
/// by unit propagation, so nothing before sweep sees it. Under DRAT the
/// kitten core lemmas are replayed and the empty clause is the terminal RUP
/// step; both checkers accept the proof.
#[test]
fn test_sweep_unsat_environment_is_certified_under_drat() {
    let mut clauses = Vec::new();
    for pattern in 0..8u32 {
        clauses.push(
            (0..3u32)
                .map(|v| {
                    if pattern & (1 << v) != 0 {
                        pos(v)
                    } else {
                        neg(v)
                    }
                })
                .collect::<Vec<_>>(),
        );
    }
    let mut solver = drat_solver(3, &clauses);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    fund_sweep(&mut solver);

    assert!(solver.sweep(), "sweep must report UNSAT");
    assert!(solver.has_empty_clause);
    let stats = solver.inproc.sweeper.stats().clone();
    assert_eq!(
        stats.unsat_environments, 1,
        "kitten must have refuted the environment"
    );
    assert_eq!(
        stats.unsat_uncertified_fallbacks, 0,
        "the core must certify it, not search"
    );
    assert_eq!(
        solver.forward_checker_rup_failures(),
        Some(0),
        "every replayed core lemma and the empty clause must be RUP for the forward checker"
    );

    let text = proof_text(&mut solver);
    assert!(
        has_empty_clause_line(&text),
        "proof must end in the empty clause:\n{text}"
    );
    verify_drat(3, &clauses, text.as_bytes()).expect("standalone DRAT checker must accept");
}

/// Site U, no certificate: with no `Unsat` fact recorded the handler must
/// not claim UNSAT under a proof surface. It hands the formula back to
/// search (return false, no empty clause, nothing written) and counts the
/// fallback, so the reason is observable.
#[test]
fn test_sweep_unsat_environment_without_core_falls_back_to_search() {
    let clauses = vec![vec![pos(0), pos(1)], vec![neg(0), pos(2)]];
    let mut solver = drat_solver(3, &clauses);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    assert!(
        !solver.sweep_environment_unsat(Vec::new()),
        "without a core the proof posture must fall back to search"
    );
    assert!(!solver.has_empty_clause);
    assert_eq!(solver.inproc.sweeper.stats().unsat_uncertified_fallbacks, 1);
    assert_eq!(
        solver.forward_checker_derived_count(),
        Some(0),
        "nothing may be emitted"
    );
    let text = proof_text(&mut solver);
    assert!(
        !has_empty_clause_line(&text),
        "no empty clause may be written:\n{text}"
    );
}

/// Site R: a clause rewrites to the empty clause because every literal maps
/// to a representative false at level 0. The sweeper never builds such a
/// map (classes hold unassigned variables only), so the state is set up
/// directly: `a` false at level 0, `b ≡ a` and `c ≡ a` with their binaries
/// in the proof exactly as `emit_sweep_proof_facts` leaves them, and the
/// clause `(b ∨ c)` whose rewrite is empty. The handler's empty clause must
/// be RUP for both checkers.
#[test]
fn test_sweep_rewrite_empty_clause_is_certified_under_drat() {
    let (a, b, c) = (0u32, 1u32, 2u32);
    let clauses = vec![
        vec![neg(b), pos(a)],
        vec![pos(b), neg(a)],
        vec![neg(c), pos(a)],
        vec![pos(c), neg(a)],
        vec![pos(b), pos(c)],
        vec![neg(a)],
    ];
    let mut solver = drat_solver(3, &clauses);
    solver.initialize_watches();
    // The input unit waits for `process_initial_clauses`, which would also
    // propagate it into the level-0 conflict BCP finds on its own; assign it
    // directly so the state is the one sweep's rewrite sees: `a` false,
    // `b` and `c` unassigned.
    if solver.get_var_assignment(a as usize).is_none() {
        solver.enqueue(neg(a), None);
    }
    assert_eq!(solver.lit_val(neg(a)), 1, "a must be false at level 0");
    assert!(
        solver.get_var_assignment(b as usize).is_none()
            && solver.get_var_assignment(c as usize).is_none(),
        "b and c must still be unassigned so the rewrite, not BCP, finds the contradiction"
    );
    // The equivalence binaries sweep leaves in the proof before rewriting.
    for binary in [
        vec![neg(b), pos(a)],
        vec![pos(b), neg(a)],
        vec![neg(c), pos(a)],
        vec![pos(c), neg(a)],
    ] {
        solver
            .proof_emit_add(&binary, &[], ProofAddKind::Derived)
            .expect("binary emission");
    }

    assert!(
        solver.sweep_rewrite_empty_clause(),
        "the handler must report UNSAT"
    );
    assert!(solver.has_empty_clause);
    assert_eq!(solver.inproc.sweeper.stats().unsat_rewrite_empty, 1);
    assert_eq!(solver.forward_checker_rup_failures(), Some(0));

    let text = proof_text(&mut solver);
    assert!(
        has_empty_clause_line(&text),
        "proof must end in the empty clause:\n{text}"
    );
    verify_drat(3, &clauses, text.as_bytes()).expect("standalone DRAT checker must accept");
}

/// Site C: a rewrite-derived unit contradicts the level-0 assignment. A
/// 30-variable equivalence chain is closed by `(x0 ∨ x29)` and
/// `(¬x15 ∨ ¬x29)`. No COI environment (depth 4) holds the whole chain, so
/// kitten refutes none of them and finds only local equivalences; their
/// union maps every variable to `x0`, the two closing clauses rewrite to
/// the units `x0` and `¬x0`, and the second contradicts the first. Under
/// DRAT the units are already in the proof, so the empty clause is RUP.
#[test]
fn test_sweep_contradicting_unit_is_certified_under_drat() {
    const N: u32 = 30;
    let mut clauses = Vec::new();
    for i in 0..N - 1 {
        clauses.push(vec![neg(i), pos(i + 1)]);
        clauses.push(vec![pos(i), neg(i + 1)]);
    }
    clauses.push(vec![pos(0), pos(N - 1)]);
    clauses.push(vec![neg(N / 2), neg(N - 1)]);
    let mut solver = drat_solver(N as usize, &clauses);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    fund_sweep(&mut solver);

    assert!(solver.sweep(), "sweep must report UNSAT");
    assert!(solver.has_empty_clause);
    let stats = solver.inproc.sweeper.stats().clone();
    assert_eq!(
        stats.unsat_environments, 0,
        "no single environment may be UNSAT, the contradiction must come from the rewrite"
    );
    assert_eq!(
        stats.unsat_contradicting_units, 1,
        "the contradicting-unit path must fire"
    );
    assert_eq!(solver.forward_checker_rup_failures(), Some(0));

    let text = proof_text(&mut solver);
    assert!(
        has_empty_clause_line(&text),
        "proof must end in the empty clause:\n{text}"
    );
    verify_drat(N as usize, &clauses, text.as_bytes())
        .expect("standalone DRAT checker must accept");
}

/// A backbone candidate that kitten reports fixed at its root is not RUP over
/// the environment clauses by itself: kitten is reused across the probes of an
/// environment, so the fixing may rest on learned clauses of earlier probes,
/// whose lifted lemmas the proof deleted again. Under a proof surface the
/// candidate goes through the assumption solve, whose core names the lemmas.
/// VeriPB rejected exactly such a bare unit on oski15a01b15s_opt (2026-09-16).
/// Two candidates on a chain: the first probe's refutation learns clauses
/// that fix the second at kitten's root.
#[test]
fn a_root_fixed_backbone_candidate_is_certified_through_its_core() {
    // x0 is forced by the pair (x0 ∨ x1), (x0 ∨ ¬x1) only after resolution;
    // x2 follows from x0 through (¬x0 ∨ x2). Neither is a unit of the
    // environment, and neither is reachable by root propagation.
    let clauses = vec![
        vec![pos(0), pos(1)],
        vec![pos(0), neg(1)],
        vec![neg(0), pos(2)],
        vec![neg(2), pos(3), pos(4)],
        vec![neg(2), neg(3), pos(4)],
        vec![neg(2), pos(3), neg(4)],
        vec![neg(2), neg(3), neg(4)],
    ];
    let mut solver = drat_solver(5, &clauses);
    assert!(solver.process_initial_clauses().is_none());
    fund_sweep(&mut solver);
    let unsat = solver.sweep();
    let text = proof_text(&mut solver);
    assert!(
        unsat || has_empty_clause_line(&text) || !text.is_empty(),
        "proof\n{text}"
    );
    verify_drat(5, &clauses, text.as_bytes()).unwrap_or_else(|e| {
        panic!("the standalone DRAT checker must accept every step: {e}\nproof\n{text}")
    });
}

/// `--sat-sweep-env-kissat`: `x0 ≡ x1` needs x0's 61 clauses and the long
/// clause `(a_1 ∧ … ∧ a_60) → x1` in one environment, more than AY's
/// 48-variable one holds. Kissat's environment proves it, and every step the
/// sweep then writes is RUP for the forward checker: the kitten core lemmas,
/// both equivalence binaries and the rewritten clauses.
#[test]
fn a_kissat_environment_equivalence_is_certified_under_drat() {
    const AUX: u32 = 60;
    let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        sweep_env_kissat: Some(true),
        ..Default::default()
    });
    let mut clauses = vec![vec![pos(0), neg(1)]];
    for a in 2..2 + AUX {
        clauses.push(vec![neg(0), pos(a)]);
    }
    let mut long: Vec<Literal> = (2..2 + AUX).map(neg).collect();
    long.push(pos(1));
    clauses.push(long);
    let num_vars = (2 + AUX) as usize;
    let mut solver = drat_solver(num_vars, &clauses);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    fund_sweep(&mut solver);

    assert!(!solver.sweep(), "the formula is satisfiable");
    let stats = solver.inproc.sweeper.stats().clone();
    assert!(
        stats.kitten_equivalences >= 1,
        "x0 ≡ x1 must be found: {stats:?}"
    );
    assert_eq!(solver.forward_checker_rup_failures(), Some(0));
    let derived = solver.forward_checker_derived_count().unwrap_or(0);
    assert!(derived > 0, "the sweep must have written proof steps");
}
