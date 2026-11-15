// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;

// Exact non-comment SMT source from MODEL_CHECKER_CONSUMER revision
// ddbfd260cc48eef296bf0492382122d5e3d896d4,
// tools/ay-ask/repro_dyn_struct.smt2 (Kani Drop/dyn_struct_member.rs,
// check_drop_dyn). Full retained file SHA-256, including its historical report:
// ebe66173d640ff7041230ed7a44f3e8fb2fe6be404d8ec968b5df5a03b8869e7.
// The old report is provenance, not a measurement of current AY.
pub(super) const ORIGINAL: &str = r#"(set-logic HORN)

(declare-var obj_valid       (Array (_ BitVec 32) Bool))
(declare-var obj_valid__out  (Array (_ BitVec 32) Bool))
(declare-var _check_drop_dyn_mem_Wrapper_DummyImpl_at_0x300000000_bv64__out (_ BitVec 256))

(declare-rel error ())
(declare-rel error_p5 ())

(rule (=> (and (= obj_valid__out (store obj_valid #x00000029 true))
               (= _check_drop_dyn_mem_Wrapper_DummyImpl_at_0x300000000_bv64__out
                  (concat #x00000000000000000000000000000000
                          #x00000000000000000000000000000001)))
          error_p5))

(rule (=> error_p5 error))

(query error)
"#;

pub(super) const WORD: &str = "_check_drop_dyn_mem_Wrapper_DummyImpl_at_0x300000000_bv64__out";

pub(super) fn high_half_source() -> String {
    let old = "(concat #x00000000000000000000000000000000";
    assert_eq!(ORIGINAL.matches(old).count(), 1);
    ORIGINAL.replace(old, "(concat #x00000000000000000000000000000001")
}

pub(super) fn run_exact(source: &str) -> (ChcProblem, Counterexample) {
    // This bounds SMT term storage, not whole-process RSS. The test runner
    // still needs its external process-group memory envelope.
    let _terms = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(256 * 1024 * 1024));
    let problem = ChcParser::parse(source).expect("retained or explicitly metamorphic source");
    problem.validate().expect("well-typed source");
    assert!(!problem.has_cycles());
    let budget = std::time::Duration::from_secs(10);
    let solver = BmcSolver::new(
        problem.clone(),
        BmcConfig {
            max_depth: 2,
            acyclic_safe: true,
            prefer_exact_acyclic_first: true,
            per_depth_timeout: Some(budget),
            time_budget: Some(budget),
            enable_k_induction: false,
            enable_adaptive_stepping: false,
            sweep_past_spurious_sat: false,
            ..BmcConfig::default()
        },
    );
    assert!(solver.prefer_exact_acyclic_executor_first());
    let result = solver.solve();
    let stats = solver.stats();
    assert!(stats.used_executor_path);
    assert!(!stats.used_legacy_fallback);
    let ChcEngineResult::Unsafe(counterexample) = result else {
        panic!("the satisfiable original-clause path must produce Unsafe, not a give-up");
    };
    assert!(counterexample.has_ground_derivation());
    (problem, counterexample)
}
