// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::time::Duration;

use ay_dpll::api::{Logic, ModelValue, Solver, Term, TermKind};
use ay_dpll::CounterexampleStyle;

#[derive(Clone, Copy)]
pub(super) enum Binding {
    Original,
    Omitted,
}

pub(super) fn on_solver_stack(test: impl FnOnce() + Send + 'static) {
    let result = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(test)
        .expect("start solver test thread")
        .join();
    if let Err(panic) = result {
        std::panic::resume_unwind(panic);
    }
}

// Preserve the actual caller's option-setting order as well as its limits.
pub(super) fn solver() -> Solver {
    let mut solver = Solver::new(Logic::All);
    solver.set_counterexample_style(CounterexampleStyle::Readable);
    solver.set_produce_unsat_cores(true);
    solver.set_timeout(Some(Duration::from_secs(10)));
    solver.set_quantifier_deadline_backstop(false);
    solver.try_set_option("rlimit", "400000").expect("rlimit");
    solver.set_memory_limit(Some(512 * 1024 * 1024));
    solver
}

pub(super) fn assert_unsat(mut solver: Solver) {
    let original = solver.to_smtlib2();
    let details = solver.try_check_sat_with_details().expect("solve");
    let result = &details.result;
    assert!(result.is_unsat(), "{details:?}");
    assert!(result.has_unsat_emission_witness(), "{details:?}");
    assert!(result.unsat_evidence_level().is_some(), "{details:?}");
    // Default publication may carry E1 corroboration; do not mislabel that
    // class as strict/independent proof acceptance or accept status alone.
    assert!(
        result.was_unsat_strictly_verified()
            || result.was_unsat_independently_verified()
            || result.was_unsat_exact_semantically_verified()
            || result.was_unsat_corroborated(),
        "{details:?}"
    );
    let core = solver.try_get_unsat_core().expect("named core");
    assert_ne!(core, [] as [String; 0]);
    assert!(core.iter().all(|name| name.starts_with("qh")), "{core:?}");
    assert_eq!(
        original,
        solver.to_smtlib2(),
        "temporary theory clauses must not persist"
    );
}

pub(super) fn assert_sat(mut solver: Solver) {
    let original = solver.to_smtlib2();
    let roots = solver.assertions();
    let details = solver.try_check_sat_with_details().expect("solve twin");
    assert!(details.result.is_sat(), "{details:?}");
    assert!(details.result.was_model_validated(), "{details:?}");
    assert!(details.result.has_sat_emission_witness(), "{details:?}");
    let printed = solver.try_get_model_str().expect("published SAT model");
    assert_ne!(printed, "");
    for &root in &roots {
        assert!(
            matches!(solver.try_get_value(root), Ok(ModelValue::Bool(true))),
            "public model must satisfy {}",
            solver.format_term(root)
        );
    }
    assert_uf_getters_congruent(&solver, &roots);
    assert_eq!(printed, solver.try_get_model_str().expect("repeat model"));
    assert_eq!(
        original,
        solver.to_smtlib2(),
        "temporary SAT theory clauses must not persist"
    );
}

fn assert_uf_getters_congruent(solver: &Solver, roots: &[Term]) {
    let mut pending = roots.to_vec();
    let mut seen = BTreeSet::new();
    let mut points = BTreeMap::new();
    while let Some(term) = pending.pop() {
        if !seen.insert(solver.format_term(term)) {
            continue;
        }
        let children = solver.term_children(term);
        if let TermKind::App { name, .. } = solver.term_kind(term) {
            if matches!(name.as_str(), "clip_u32_oob" | "clip_nat_oob" | "sf0") {
                let arguments = children
                    .iter()
                    .map(|&arg| format!("{:?}", solver.try_get_value(arg).expect("UF argument")))
                    .collect::<Vec<_>>();
                let value = format!("{:?}", solver.try_get_value(term).expect("UF value"));
                if let Some(previous) = points.insert((name, arguments), value.clone()) {
                    assert_eq!(
                        previous, value,
                        "equal arguments must yield equal UF values"
                    );
                }
            }
        }
        pending.extend(children);
    }
}
