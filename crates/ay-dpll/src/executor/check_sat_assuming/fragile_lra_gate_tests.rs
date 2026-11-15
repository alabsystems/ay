// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The fragile gate decides publication from independent certification, not
//! from the provisional verdict: a FORGED fragile UNSAT (the defect class the
//! gate exists for, injected rather than waited for) must still fail closed in
//! both postures, and a forged proper-subset core must not survive.

use super::super::{AssumptionSatPublication, Executor, SolveResult, TermId};

/// Declarations and base assertions, then the assumption literals by name.
fn setup(script: &str, competition: bool, assumption_names: &[&str]) -> (Executor, Vec<TermId>) {
    let commands = ay_frontend::parse(script).expect("script parses");
    let mut exec = Executor::new();
    exec.set_competition_mode(competition);
    exec.execute_all(commands.as_slice())
        .expect("setup commands execute");
    let assumptions = assumption_names
        .iter()
        .map(|name| {
            exec.ctx
                .terms
                .find_var(name)
                .unwrap_or_else(|| panic!("declared Bool {name}"))
        })
        .collect::<Vec<_>>();
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&assumptions);
    exec.last_assumptions = Some(assumptions.clone());
    (exec, assumptions)
}

const HEADER: &str = "(set-logic QF_LRA)
(declare-const x Real)
(declare-const z Real)
(declare-const p Bool)
(declare-const q Bool)
";

const REFUTED_BY_P: &str = "(assert (=> p (= z x)))\n(assert (not (= z x)))\n";

/// `base ∧ p` is SATISFIABLE (p is unconstrained). A route that claimed
/// UNSAT here is exactly the historical false-UNSAT shape; the gate must
/// publish `unknown` whatever the posture.
#[test]
fn forged_fragile_unsat_fails_closed_in_both_postures() {
    for competition in [true, false] {
        let script = format!("{HEADER}(assert (not (= z x)))\n");
        let (mut exec, assumptions) = setup(&script, competition, &["p"]);
        exec.last_assumption_core = Some(assumptions.clone());
        let published = exec.finish_check_sat_assuming_result(
            &assumptions,
            SolveResult::unsat(),
            AssumptionSatPublication::EmitHere,
        );
        assert_eq!(
            published,
            SolveResult::Unknown,
            "forged fragile UNSAT published (competition={competition})"
        );
    }
}

/// A genuine refutation certifies and keeps its (full) core.
#[test]
fn genuine_fragile_unsat_certifies() {
    for competition in [true, false] {
        let script = format!("{HEADER}{REFUTED_BY_P}");
        let (mut exec, assumptions) = setup(&script, competition, &["p"]);
        exec.last_assumption_core = Some(assumptions.clone());
        assert!(
            !exec.fragile_lra_assumption_unsat_uncertified(&assumptions),
            "base ∧ p is unsat and must certify (competition={competition})"
        );
        assert_eq!(exec.last_assumption_core, Some(assumptions.clone()));
    }
}

/// The verdict is genuine (`base ∧ p ∧ q` is unsat through `p`), but the
/// harvested core `{q}` is forged: `base ∧ q` is satisfiable. The verdict may
/// publish; the core must widen to the full assumption set, which is what
/// the certificate actually covers.
#[test]
fn forged_proper_subset_core_widens_to_the_certified_set() {
    for competition in [true, false] {
        let script = format!("{HEADER}{REFUTED_BY_P}");
        let (mut exec, assumptions) = setup(&script, competition, &["p", "q"]);
        exec.last_assumption_core = Some(vec![assumptions[1]]);
        assert!(!exec.fragile_lra_assumption_unsat_uncertified(&assumptions));
        assert_eq!(
            exec.last_assumption_core,
            Some(assumptions.clone()),
            "an uncertified proper-subset core survived (competition={competition})"
        );
    }
}

/// A genuine proper-subset core is certified on its own and kept.
#[test]
fn genuine_proper_subset_core_is_kept() {
    let script = format!("{HEADER}{REFUTED_BY_P}");
    let (mut exec, assumptions) = setup(&script, true, &["p", "q"]);
    let p = assumptions[0];
    exec.last_assumption_core = Some(vec![p]);
    assert!(!exec.fragile_lra_assumption_unsat_uncertified(&assumptions));
    assert_eq!(exec.last_assumption_core, Some(vec![p]));
}
