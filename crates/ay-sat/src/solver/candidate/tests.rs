// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::original_query::FiniteAdmissionGrant;
use std::collections::BTreeSet;

fn owner(work: u64, bytes: usize) -> CountedAdmission {
    let _ = ay_core::misc_cli_flags();
    CountedAdmission::new(
        FiniteAdmissionGrant::new(work, bytes),
        None,
        Arc::new(|| false),
    )
    .unwrap()
}
fn ample() -> CountedAdmission {
    owner(100_000_000, 1 << 30)
}
fn positive(id: u32) -> Literal {
    Literal::positive(Variable::new(id))
}

#[test]
fn persistent_candidates_enumerate_exact_models_without_checked_result_authority() {
    let mut solver = CandidateSolver::try_new(4, ample()).unwrap();
    solver.add_clause(vec![positive(0), positive(1)]).unwrap();
    for id in 0..4 {
        solver.freeze(Variable::new(id)).unwrap();
    }
    let mut models = BTreeSet::new();
    loop {
        match solver.search().unwrap() {
            CandidateSearchOutcome::Assignment(values) => {
                // An independent test-only original-formula check. The
                // candidate producer deliberately does not grant this fact.
                assert!(values[0] || values[1]);
                let mask = values
                    .iter()
                    .enumerate()
                    .fold(0u32, |m, (i, &value)| m | (u32::from(value) << i));
                assert!(models.insert(mask));
                assert!(solver.last_work().materialization > 0);
                solver
                    .add_clause(
                        values
                            .iter()
                            .enumerate()
                            .map(|(i, &value)| {
                                if value {
                                    positive(i as u32).negated()
                                } else {
                                    positive(i as u32)
                                }
                            })
                            .collect(),
                    )
                    .unwrap();
            }
            CandidateSearchOutcome::ExhaustionHint => break,
            other => panic!("candidate engine stopped: {other:?}"),
        }
    }
    assert_eq!(models, (0u32..16).filter(|mask| mask & 3 != 0).collect());
    #[cfg(any(
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    if let Some(oracle) = ay_test_support::z3::optional_z3("candidate-incremental-fixed-source") {
        use std::io::Write as _;
        let mut input = String::from("(set-logic QF_UF)\n");
        for id in 0..4 {
            input.push_str(&format!("(declare-const p{id} Bool)\n"));
        }
        input.push_str("(assert (or p0 p1))\n");
        for mask in &models {
            input.push_str("(assert (or");
            for id in 0..4 {
                input.push_str(&if mask & (1 << id) == 0 {
                    format!(" p{id}")
                } else {
                    format!(" (not p{id})")
                });
            }
            input.push_str("))\n");
        }
        input.push_str("(check-sat)\n");
        let mut file = tempfile::NamedTempFile::new().unwrap();
        file.write_all(input.as_bytes()).unwrap();
        file.flush().unwrap();
        let mut command = oracle.command();
        command.arg(file.path());
        let result = ay_sys::metadata_capture::capture(
            command,
            ay_sys::metadata_capture::CaptureLimits {
                timeout: std::time::Duration::from_secs(5),
                output_bytes: 4096,
                resident_bytes: Some(256 << 20),
            },
            "candidate-incremental-fixed-source",
        )
        .unwrap();
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(String::from_utf8(result.stdout).unwrap().trim(), "unsat");
    }
}

#[test]
fn untrusted_materialization_is_independent_of_an_expanding_original_ledger() {
    let mut solver = CandidateSolver::try_new(10, ample()).unwrap();
    solver.add_clause(vec![positive(0)]).unwrap();
    assert!(matches!(
        solver.search().unwrap(),
        CandidateSearchOutcome::Assignment(_)
    ));
    let first = solver.last_work().materialization;
    let clauses = solver.solver.cold.original_ledger.num_clauses();
    for _ in 0..800 {
        solver.add_clause(vec![positive(0), positive(1)]).unwrap();
    }
    assert!(solver.solver.cold.original_ledger.num_clauses() > clauses + 700);
    assert!(matches!(
        solver.search().unwrap(),
        CandidateSearchOutcome::Assignment(_)
    ));
    assert_eq!(solver.last_work().materialization, first);
    eprintln!(
        "candidate materialization work before={}, after800clauses={}",
        first,
        solver.last_work().materialization
    );
}

#[test]
fn data_completion_does_not_launder_a_false_assignment_through_checked_ic3() {
    let mut solver = Solver::new(1);
    solver.set_ic3_mode();
    solver.add_clause(vec![positive(0)]);
    solver.set_var_assignment(0, Some(false));
    let owner = ample();
    let work = Cell::new(0);
    // The intentionally false model is only DATA from the private candidate
    // completion, not a checked SAT capability.
    let data = IncrementalCompletion::UntrustedCandidate {
        owner: &owner,
        work: &work,
    }
    .current(&mut solver);
    assert!(matches!(data, AssumeResult::Sat(values) if values == vec![false]));
    assert!(matches!(
        IncrementalCompletion::Checked.current(&mut solver),
        AssumeResult::Unknown
    ));
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::InvalidSatModel)
    );
    assert!(solver.cold.finalize_sat_fail_count > 0);
}

#[test]
fn zero_grant_cancellation_deadline_and_budget_remain_incomplete_data() {
    assert!(matches!(
        CandidateSolver::try_new(1, owner(0, 1 << 20)),
        Err(CountedAdmissionError::WorkExhausted)
    ));
    let cancelled = Arc::new(AtomicBool::new(false));
    let flag = cancelled.clone();
    let owner = CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1 << 24),
        None,
        Arc::new(move || flag.load(Ordering::Relaxed)),
    )
    .unwrap();
    let mut solver = CandidateSolver::try_new(2, owner).unwrap();
    solver.add_clause(vec![positive(0), positive(1)]).unwrap();
    cancelled.store(true, Ordering::Relaxed);
    assert!(solver.search().is_err());
    cancelled.store(false, Ordering::Relaxed);
    assert!(
        solver.search().is_err(),
        "the same owner refusal must stay sticky"
    );
    let mut solver = CandidateSolver::try_new(2, ample()).unwrap();
    solver.add_clause(vec![positive(0), positive(1)]).unwrap();
    solver.set_decision_budget(Some(0));
    assert!(matches!(
        solver.search().unwrap(),
        CandidateSearchOutcome::Unknown(SatUnknownReason::ResourceBudget)
    ));
    let owner = CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1 << 24),
        Some(ay_core::time::Instant::now()),
        Arc::new(|| false),
    )
    .unwrap();
    assert!(matches!(
        CandidateSolver::try_new(2, owner),
        Err(CountedAdmissionError::Guard(
            ay_core::resource::Exhausted::Deadline
        )) | Err(CountedAdmissionError::Original(
            ay_core::original_query::OriginalAdmissionError::Query(QueryError::Interrupted(
                ay_core::original_query::StopReason::Deadline
            ))
        ))
    ));
}

#[test]
fn foreign_literals_refuse_before_changing_the_candidate_formula() {
    let mut solver = CandidateSolver::try_new(2, ample()).unwrap();
    assert!(solver.add_clause(vec![positive(2)]).is_err());
    assert_eq!(solver.solver.cold.original_ledger.num_clauses(), 0);
    assert!(solver.search().is_err());
}
