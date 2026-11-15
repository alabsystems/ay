// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_drat_check::drat_parser::ProofStep;
use ay_lrat_check::lrat_parser::LratStep;

#[derive(Clone, Copy, Debug)]
pub(super) enum Format {
    DratText,
    DratBinary,
    LratText,
    LratBinary,
}

impl Format {
    pub(super) fn output(self, originals: u64) -> ProofOutput {
        match self {
            Self::DratText => ProofOutput::drat_text(Vec::<u8>::new()),
            Self::DratBinary => ProofOutput::drat_binary(Vec::<u8>::new()),
            Self::LratText => ProofOutput::lrat_text(Vec::<u8>::new(), originals),
            Self::LratBinary => ProofOutput::lrat_binary(Vec::<u8>::new(), originals),
        }
    }

    pub(super) fn is_lrat(self) -> bool {
        matches!(self, Self::LratText | Self::LratBinary)
    }
}

pub(super) fn p(var: u32) -> Literal {
    Literal::positive(Variable::new(var))
}

pub(super) fn n(var: u32) -> Literal {
    Literal::negative(Variable::new(var))
}

pub(super) fn solver(format: Format, clauses: &[Vec<Literal>]) -> Solver {
    let mut solver = Solver::with_proof_output(3, format.output(clauses.len() as u64));
    solver.disable_all_inprocessing();
    solver.set_preprocess_enabled(false);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    solver
}

pub(super) fn proof_bytes(solver: &mut Solver) -> Vec<u8> {
    solver
        .take_proof_writer()
        .expect("attached writer")
        .into_vec()
        .expect("proof flush")
}

pub(super) fn drat_steps(format: Format, bytes: &[u8]) -> Vec<ProofStep> {
    match format {
        Format::DratText => ay_drat_check::drat_parser::parse_text_drat(bytes),
        Format::DratBinary => ay_drat_check::drat_parser::parse_binary_drat(bytes),
        Format::LratText | Format::LratBinary => panic!("expected DRAT format"),
    }
    .expect("DRAT parses")
}

pub(super) fn lrat_steps(format: Format, bytes: &[u8]) -> Vec<LratStep> {
    match format {
        Format::LratText => ay_lrat_check::lrat_parser::parse_text_lrat(
            std::str::from_utf8(bytes).expect("text proof is UTF-8"),
        ),
        Format::LratBinary => ay_lrat_check::lrat_parser::parse_binary_lrat(bytes),
        Format::DratText | Format::DratBinary => panic!("expected LRAT format"),
    }
    .expect("LRAT parses")
}

pub(super) fn assert_no_empty(format: Format, bytes: &[u8]) {
    if format.is_lrat() {
        assert!(lrat_steps(format, bytes)
            .iter()
            .all(|step| { !matches!(step, LratStep::Add { clause, .. } if clause.is_empty()) }));
    } else {
        assert!(drat_steps(format, bytes)
            .iter()
            .all(|step| { !matches!(step, ProofStep::Add(clause) if clause.is_empty()) }));
    }
}

pub(super) fn assert_empty(format: Format, bytes: &[u8]) {
    if format.is_lrat() {
        assert!(lrat_steps(format, bytes)
            .iter()
            .any(|step| { matches!(step, LratStep::Add { clause, .. } if clause.is_empty()) }));
    } else {
        assert!(drat_steps(format, bytes)
            .iter()
            .any(|step| { matches!(step, ProofStep::Add(clause) if clause.is_empty()) }));
    }
}

fn proof_literals(clause: &[Literal]) -> Vec<ay_proof_common::literal::Literal> {
    clause
        .iter()
        .map(|lit| ay_proof_common::literal::Literal::from_index(lit.index()))
        .collect()
}

/// Check every emitted step independently, without calling a complete-proof
/// routine that incorrectly interprets a valid prefix as a refutation.
pub(super) fn assert_valid_prefix(format: Format, original: &[Vec<Literal>], bytes: &[u8]) {
    assert_no_empty(format, bytes);
    if format.is_lrat() {
        let mut checker = ay_lrat_check::checker::LratChecker::new(3);
        for (index, clause) in original.iter().enumerate() {
            assert!(checker.add_original(index as u64 + 1, &proof_literals(clause)));
        }
        for step in lrat_steps(format, bytes) {
            match step {
                LratStep::Add { id, clause, hints } => {
                    assert!(checker.add_derived(id, &clause, &hints));
                }
                LratStep::Delete { ids } => {
                    for id in ids {
                        assert!(checker.delete(id));
                    }
                }
            }
        }
        assert_ne!(
            checker.conclude_unsat(),
            ay_lrat_check::checker::ConcludeResult::Verified,
        );
    } else {
        let mut checker = ay_drat_check::checker::DratChecker::new(3, true);
        for clause in original {
            checker.add_original(&proof_literals(clause));
        }
        for step in drat_steps(format, bytes) {
            match step {
                ProofStep::Add(clause) => {
                    assert!(checker.add_derived(&clause).is_ok());
                }
                ProofStep::Delete(clause) => checker.delete_clause(&clause),
                _ => panic!("fixture emitted an unsupported proof step"),
            }
        }
        assert_ne!(
            checker.conclude_unsat(),
            ay_drat_check::checker::ConcludeResult::Verified,
        );
    }
}

pub(super) fn assert_query_refutation_is_not_base(solver: &Solver, result: &SolverAssumeResult) {
    assert!(result.is_unsat(), "conditional result: {result:?}");
    assert!(result.proof_certificate().is_none());
    assert!(!solver.has_empty_clause, "query must not poison the base");
    assert!(!solver.cold.empty_clause_in_proof);
    assert_eq!(solver.cold.empty_clause_lrat_id, None);
}

pub(super) fn repeated_queries(format: Format) {
    let original = vec![vec![p(0), p(1)]];
    let mut solver = solver(format, &original);
    let result = solver.solve_with_assumptions(&[n(0), n(1)]);
    assert_query_refutation_is_not_base(&solver, &result);
    assert!(solver.solve_with_assumptions(&[p(0)]).is_sat());
    assert!(solver.solve().is_sat());
    let result = solver.solve_with_assumptions_interruptible(&[n(0), n(1)], || false);
    assert_query_refutation_is_not_base(&solver, &result);
    assert!(solver.solve().is_sat());
    let bytes = proof_bytes(&mut solver);
    assert_valid_prefix(format, &original, &bytes);
}

pub(super) fn pushed_query(format: Format) {
    let original = vec![vec![p(0), p(1)]];
    let mut solver = solver(format, &original);
    solver.push();
    let result = solver.solve_with_assumptions(&[n(0), n(1)]);
    assert_query_refutation_is_not_base(&solver, &result);
    assert!(solver.solve_with_assumptions(&[p(0)]).is_sat());
    assert!(solver.solve().is_sat());
    assert!(solver.pop());
    assert!(solver.solve().is_sat());
    assert_no_empty(format, &proof_bytes(&mut solver));
}

pub(super) fn scoped_formula(format: Format) {
    let mut solver = solver(format, &[]);
    solver.push();
    solver.add_clause(vec![p(0)]);
    solver.add_clause(vec![n(0)]);
    // Both conflicting units are guarded by the active selector. The
    // public core may be empty after filtering that INTERNAL assumption.
    let result = solver.solve_with_assumptions(&[]);
    assert_query_refutation_is_not_base(&solver, &result);
    assert!(result.unsat_core().is_some_and(|core| core.is_empty()));
    assert!(solver.pop());
    assert!(solver.solve().is_sat());
    assert_no_empty(format, &proof_bytes(&mut solver));
}

pub(super) fn root_refutation(format: Format) {
    let original = vec![vec![p(0)], vec![n(0)]];
    let mut solver = solver(format, &original);
    let result = solver.solve_with_assumptions(&[p(1)]);
    assert!(result.is_unsat());
    assert!(solver.has_empty_clause);
    assert!(solver.solve().is_unsat());
    assert_valid_refutation(format, &original, &proof_bytes(&mut solver));
}

pub(super) fn assert_valid_refutation(format: Format, original: &[Vec<Literal>], bytes: &[u8]) {
    assert_empty(format, bytes);
    if format.is_lrat() {
        let mut checker = ay_lrat_check::checker::LratChecker::new(3);
        for (index, clause) in original.iter().enumerate() {
            assert!(checker.add_original(index as u64 + 1, &proof_literals(clause)));
        }
        assert!(checker.verify_proof(&lrat_steps(format, bytes)));
    } else {
        let mut checker = ay_drat_check::checker::DratChecker::new(3, true);
        for clause in original {
            checker.add_original(&proof_literals(clause));
        }
        for step in drat_steps(format, bytes) {
            match step {
                ProofStep::Add(clause) => {
                    assert!(checker.add_derived(&clause).is_ok());
                }
                ProofStep::Delete(clause) => checker.delete_clause(&clause),
                _ => panic!("fixture emitted an unsupported proof step"),
            }
        }
        assert_eq!(
            checker.conclude_unsat(),
            ay_drat_check::checker::ConcludeResult::Verified,
        );
    }
}

pub(super) fn later_base_refutation(format: Format) {
    let original = vec![vec![p(0), p(1)], vec![n(0)], vec![n(1)]];
    let mut solver = Solver::with_proof_output(3, format.output(original.len() as u64));
    solver.disable_all_inprocessing();
    solver.set_preprocess_enabled(false);
    solver.add_clause(original[0].clone());
    let result = solver.solve_with_assumptions(&[n(0), n(1)]);
    assert_query_refutation_is_not_base(&solver, &result);
    assert!(solver.solve().is_sat());
    solver.add_clause(original[1].clone());
    solver.add_clause(original[2].clone());
    let result = solver.solve();
    assert!(
        result.is_unsat(),
        "later base refutation: {result:?}; reason={:?}; detail={:?}",
        solver.last_unknown_reason(),
        solver.last_unknown_detail(),
    );
    assert!(solver.has_empty_clause);
    assert_valid_refutation(format, &original, &proof_bytes(&mut solver));
}
