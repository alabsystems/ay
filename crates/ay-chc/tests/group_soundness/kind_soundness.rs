// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! Regression tests for K-Induction soundness bugs (#151, #152)
//!
//! ## Issue #151: K-Induction forward induction formula is wrong
//!
//! The K-Induction algorithm's forward induction check uses the wrong formula:
//! - **Wrong (AY)**: ¬Query(x0) ∧ Tr(x0,x1) ∧ ¬Query(x1) ∧ ... ∧ Query(x{k+1}) is UNSAT?
//! - **Correct (Golem)**: Query(x0) ∧ Tr^{-1}(x0,x1) ∧ ¬Query(x1) ∧ ... is UNSAT?
//!
//! AY's formula asks "can we reach bad from non-bad in k+1 steps?" but this is
//! not the correct k-induction check. The correct check uses backward transition
//! to verify "does every bad state have k non-bad predecessors?"
//!
//! ## Issue #152: PDKIND timeout handling is unsound
//!
//! When SMT queries timeout, PDKIND skips obligations with `continue`. If all
//! obligations timeout, the frame appears "stable" and returns false Safe.
//!
//! ## Mitigation
//!
//! The current fix (in main.rs) distrusts K-Induction and PDKIND Safe results,
//! falling through to PDR for verification. This is sound but loses performance.
//!
//! ## References
//!
//! - Golem: https://github.com/usi-verification-and-security/golem
//! - PDKIND paper: Kahsai et al. "Property-Directed K-Induction" (FMCAD 2017)
//! - Research: the development design notes

use ay_chc::ChcParser;
use ay_chc::PdkindResult;
use ay_chc::{testing, KindConfig, KindResult, PortfolioConfig, PortfolioResult};
use ay_chc::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};
use ntest::timeout;
use std::time::Duration;

fn assert_portfolio_benchmark_is_not_safe(content: &str, label: &str) {
    let problem = ChcParser::parse(content).expect("parse benchmark");
    let solver = testing::new_portfolio_solver(
        problem,
        PortfolioConfig::test_default().parallel_timeout(Some(Duration::from_secs(10))),
    );
    let result = solver.solve();

    match result {
        PortfolioResult::Unsafe(_) | PortfolioResult::Unknown | PortfolioResult::NotApplicable => {}
        PortfolioResult::Safe(_) => {
            panic!("CHC SOUNDNESS BUG (#6789): {label} is UNSAT in Z3, but the portfolio returned Safe.");
        }
        _ => panic!("unexpected variant"),
    }
}

#[allow(dead_code)] // helper retained for future regression tests
fn assert_kind_benchmark_is_not_safe(content: &str, label: &str) {
    let problem = ChcParser::parse(content).expect("parse benchmark");
    let config = KindConfig::with_engine_config(
        20,
        Duration::from_secs(2),
        Duration::from_secs(15),
        false,
        None,
    );
    let mut solver = testing::new_kind_solver(problem, config);
    let result = solver.solve();

    match result {
        KindResult::Unsafe(_) | KindResult::Unknown | KindResult::NotApplicable => {}
        KindResult::Safe(_) => {
            panic!(
                "KIND SOUNDNESS BUG: {label} is unsafe, but Kind returned Safe from deferred k-induction."
            );
        }
        _ => panic!("unexpected variant"),
    }
}

/// Create an UNSAFE problem that K-Induction incorrectly reports as SAFE.
///
/// This problem is a simple counter that can exceed its bound:
/// - Init: x = 0
/// - Trans: x' = x + 1 (unbounded increment)
/// - Query: x > 5 implies false
///
/// The system is UNSAFE because x can reach 6, 7, 8, ... without bound.
/// K-Induction incorrectly claims it's SAFE at k=1 because the forward
/// induction formula is wrong.
fn create_kind_soundness_bug_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Fact: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Transition: Inv(x) => Inv(x + 1) -- unbounded increment!
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Query: Inv(x) ∧ x > 5 => false
    // This is UNSAFE - x can reach 6, 7, 8, ...
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    problem
}

/// Regression test for #151: K-Induction must NOT return Safe on unsafe problems.
///
/// Before fix: K-Induction returns Safe at k=1 (forward induction succeeds incorrectly)
/// After fix: K-Induction returns Unsafe (finds counterexample).
///
/// Timeout: 10s (measured <100ms; internal timeout 5s)
#[test]
#[timeout(10_000)]
fn test_kind_soundness_issue_151() {
    let problem = create_kind_soundness_bug_problem();
    let config = KindConfig::with_engine_config(
        10,
        Duration::from_secs(1),
        Duration::from_secs(5),
        false,
        None,
    );
    let mut solver = testing::new_kind_solver(problem, config);
    let result = solver.solve();

    match result {
        KindResult::Unsafe(cex) => {
            // CORRECT: Found counterexample
            let k = cex.steps.len().saturating_sub(1);
            assert!(k <= 6, "Expected counterexample at k <= 6, got k={k}");
        }
        KindResult::Unknown | KindResult::NotApplicable => panic!(
            "K-Induction returned Unknown/NotApplicable on a small UNSAFE regression case.\n\
             This should produce a concrete counterexample."
        ),
        KindResult::Safe(_) => {
            // BUG: This problem is UNSAFE, K-Induction should not claim Safe
            panic!(
                "K-INDUCTION SOUNDNESS BUG (#151): Problem is UNSAFE,\n\
                 but K-Induction incorrectly returned Safe.\n\
                 Bug: Forward induction formula is incorrect.\n\
                 See the development design notes",
            );
        }
        _ => panic!("unexpected variant"),
    }
}

/// Regression test: K-Induction correctly handles genuinely safe problems.
///
/// This test ensures we don't break safe problems while fixing the bug.
///
/// Timeout: 10s (measured <100ms; internal timeout 5s)
#[test]
#[timeout(10_000)]
fn test_kind_correct_safe() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Fact: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Transition: Inv(x) ∧ x < 3 => Inv(x + 1) -- bounded increment
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(3))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Query: Inv(x) ∧ x > 10 => false
    // This is SAFE - x can only reach {0, 1, 2, 3}, never > 10
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    let config = KindConfig::with_engine_config(
        10,
        Duration::from_secs(1),
        Duration::from_secs(5),
        false,
        None,
    );
    let mut solver = testing::new_kind_solver(problem, config);
    let result = solver.solve();

    match result {
        KindResult::Safe(_) => {
            // Expected: this bounded system is safe.
        }
        KindResult::Unknown | KindResult::NotApplicable => {
            panic!("K-Induction returned Unknown/NotApplicable on a small SAFE regression case.")
        }
        KindResult::Unsafe(cex) => {
            let k = cex.steps.len().saturating_sub(1);
            panic!("K-Induction reported Unsafe at k={k} on a SAFE problem");
        }
        _ => panic!("unexpected variant"),
    }
}

/// Regression test for #152: PDKIND must NOT return Safe on unsafe problems.
///
/// This tests the PDKIND timeout handling soundness bug.
///
/// Timeout: 30s (measured 8-10s under load; per-obligation timeout is 5s)
#[test]
#[timeout(30_000)]
fn test_pdkind_soundness_issue_152() {
    let problem = create_kind_soundness_bug_problem();
    let solver = testing::pdkind_solver_defaults(problem);
    let result = solver.solve();

    match result {
        PdkindResult::Unsafe(cex) => {
            // CORRECT: Found counterexample
            // Step count varies slightly depending on push() strategy (#2690:
            // direct SmtContext vs IncrementalSatContext produces different models).
            assert!(
                cex.steps.len() <= 8,
                "Expected counterexample at steps <= 8, got {}",
                cex.steps.len()
            );
        }
        PdkindResult::Unknown => {
            // ACCEPTABLE: Conservative result — PDR couldn't determine in time
        }
        PdkindResult::Safe(_) => {
            // BUG: This problem is UNSAFE, PDKIND should not claim Safe
            panic!(
                "PDKIND SOUNDNESS BUG (#152): Problem is UNSAFE,\n\
                 but PDKIND incorrectly returned Safe.\n\
                 Bug: Timeout handling skips obligations unsoundly.\n\
                 See the development design notes"
            );
        }
        PdkindResult::NotApplicable => {
            panic!(
                "PDKIND returned NotApplicable on a single-predicate UNSAFE problem.\n\
                 This problem is in PDKIND's supported class — NotApplicable is a regression."
            );
        }
        _ => panic!("unexpected variant"),
    }
}

/// Test that PDKIND correctly handles safe problems.
///
/// Timeout: 60s (debug staging can spend ~30s in PDKIND on this case)
#[test]
#[timeout(60_000)]
fn test_pdkind_correct_safe() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Fact: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Transition: Inv(x) ∧ x < 3 => Inv(x + 1) -- bounded
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(3))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Query: Inv(x) ∧ x > 10 => false (SAFE)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    let solver = testing::pdkind_solver_defaults(problem);
    let result = solver.solve();

    match result {
        PdkindResult::Safe(_) => {
            // Expected: this bounded system is safe.
        }
        PdkindResult::Unknown => panic!("PDKIND returned Unknown on a small SAFE regression case."),
        PdkindResult::Unsafe(cex) => {
            panic!(
                "PDKIND reported Unsafe at steps={} on a SAFE problem",
                cex.steps.len()
            );
        }
        PdkindResult::NotApplicable => {
            panic!(
                "PDKIND returned NotApplicable on a trivial single-predicate SAFE problem.\n\
                 This problem is in PDKIND's supported class — NotApplicable is a regression."
            );
        }
        _ => panic!("unexpected variant"),
    }
}

/// Discriminator test: This test MUST FAIL if K-Induction is re-enabled
/// without fixing the forward induction formula.
///
/// This is a closure verification test for issue #151.
///
/// Timeout: 10s (measured <100ms; internal timeout 5s)
#[test]
#[timeout(10_000)]
fn test_kind_discriminator_issue_151() {
    // This problem is specifically designed to trigger the K-Induction bug:
    // - The forward induction formula becomes UNSAT at k=1
    // - But the problem is actually UNSAFE

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Init: x = 0
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Trans: x' = x + 1
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Query: x > 5 is bad
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    let config = KindConfig::with_engine_config(
        10,
        Duration::from_secs(1),
        Duration::from_secs(5),
        false,
        None,
    );
    let mut solver = testing::new_kind_solver(problem, config);
    let result = solver.solve();

    // The discriminator: K-Induction MUST NOT return Safe
    if let KindResult::Safe(_) = result {
        panic!(
            "DISCRIMINATOR FAILED: K-Induction returned Safe\n\
             This indicates issue #151 has regressed.\n\
             The forward induction formula bug causes false Safe on this problem.\n\
             \n\
             If you're re-enabling K-Induction Safe results, you MUST fix the\n\
             forward induction formula first. See:\n\
             - the development design notes\n\
            - reference/golem/src/engine/Kind.cc",
        );
    }
}

/// Regression test for #7371: KIND must still prove `const_mod_3` safe after
/// rejecting an incremental base-case SAT that a fresh SMT context cannot
/// confirm.
///
/// This benchmark is a real mod+ITE hard-tail case. The #7371 guard skips the
/// spurious base-case SAT, then accepts the deferred Safe only after forward
/// induction and extended BMC validation succeed.
#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_kind_issue_7371_const_mod_3_remains_safe() {
    let problem = ChcParser::parse(include_str!(
        "../../../../benchmarks/chc-comp/2025/extra-small-lia/const_mod_3_000.smt2"
    ))
    .expect("parse const_mod_3 benchmark");
    let config = KindConfig::with_engine_config(
        20,
        Duration::from_secs(2),
        Duration::from_secs(15),
        false,
        None,
    );
    let mut solver = testing::new_kind_solver(problem, config);
    let result = solver.solve();

    match result {
        KindResult::Safe(_) => {}
        KindResult::Unsafe(cex) => {
            panic!(
                "KIND SOUNDNESS BUG (#7371): const_mod_3 is SAT (safe), but KIND returned Unsafe at steps={}.",
                cex.steps.len()
            );
        }
        KindResult::Unknown => {
            panic!("KIND regression (#7371): const_mod_3 should remain Safe, got Unknown.");
        }
        KindResult::NotApplicable => {
            panic!("KIND regression (#7371): const_mod_3 is a single-predicate benchmark.");
        }
        _ => panic!("unexpected variant"),
    }
}

/// Soundness guard for #421: PDKIND must NOT return Unsafe on dillig01.c_000.smt2
///
/// Z3 returns sat (safe). PDKIND previously returned false Unsafe due to MBP
/// overgeneralization (#421). The Bool(true) guard (#4729) prevents this, but
/// also means PDKIND cannot currently converge on this benchmark — it returns
/// Unknown instead of Safe (#4823). The model-based fallback in push.rs helps
/// but the formula complexity (8 vars, 13-clause disjunctive transition) exceeds
/// what MBP can handle within PDKIND's convergence budget.
///
/// This test verifies the soundness property (no false Unsafe). The performance
/// regression (Unknown instead of Safe) is tracked separately in #4823.
#[test]
#[cfg_attr(debug_assertions, timeout(120_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_pdkind_soundness_issue_421_dillig01() {
    // Embedded benchmark: dillig01.c_000.smt2 (#981: hermetic tests)
    let content = r#"(set-logic HORN)


(declare-fun |state| ( Bool Bool Bool Bool Int Int Int Int ) Bool)

(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Bool) )
    (=>
      (and
        (and (not B) (= A true) (not H) (not C))
      )
      (state C A B H D E F G)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Bool) )
    (=>
      (and
        (state C A B Q I K M O)
        (let ((a!1 (and (not G)
                F
                E
                (not D)
                (= I H)
                (= K J)
                (= O N)
                (= (+ I K (* (- 1) L)) 0)))
      (a!2 (and (not G) F E D (= I H) (= K J) (= M L) (= (+ I K (* (- 1) N)) 0)))
      (a!3 (and G (not F) E D (= I H) (= K J) (= M L) (= O N)))
      (a!4 (and (not G) (not F) (not E) (not D) (= I H) (= K J) (= M L) (= O N))))
  (and (or A
           B
           C
           (not Q)
           (not (<= 1 O))
           (and G (not F) (not E) D (= I H) (= K J) (= M L) (= O N)))
       (or A
           B
           Q
           (not C)
           (= P 0)
           (and G (not F) (not E) (not D) (= I H) (= K J) (= M L) (= O N)))
       (or A
           B
           Q
           (not C)
           (not (= P 0))
           (and (not G) (not F) E D (= I H) (= K J) (= M L) (= O N)))
       (or C Q (not B) (not A) a!1)
       (or A Q (not B) (not C) a!2)
       (or B (not Q) (not C) (not A) a!3)
       (or B
           C
           (not Q)
           (not A)
           (and G (not F) E (not D) (= I H) (= K J) (= M L) (= O N)))
       (or Q
           (not B)
           (not C)
           (not A)
           (and (not G) (not F) E (not D) (= I H) (= K J) (= M L) (= O N)))
       (or A B C Q a!4)
       (or A B (not Q) (not C) a!4)
       (or B
           Q
           (not C)
           (not A)
           (and (not G) F (not E) (not D) (= H M) (= K J) (= M L) (= O N)))
       (or A
           C
           Q
           (not B)
           (and (not G) F (not E) D (= J O) (= I H) (= M L) (= O N)))
       (or B
           C
           Q
           (not A)
           (and (not G) (not F) E (not D) (= N 1) (= L 1) (= I H) (= K J)))
       (or A B C (not Q) (<= 1 O) a!3)))
      )
      (state E D F G H J L N)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Bool) )
    (=>
      (and
        (state C A B H D E F G)
        (and (not B) (= A true) (= H true) (= C true))
      )
      false
    )
  )
)

(check-sat)
(exit)
"#;
    let problem = ChcParser::parse(content).expect("parse benchmark");
    // Use limited budget: MBP overgeneralization on this benchmark means PDKIND
    // cannot converge with defaults (max_iterations=1000, max_n=100). A small
    // budget is sufficient to verify the soundness property (no false Unsafe).
    use ay_chc::PdkindConfig;
    let config = PdkindConfig {
        max_iterations: 5,
        max_n: 3,
        per_obligation_timeout_secs: 1,
        ..PdkindConfig::default()
    };
    let solver = testing::new_pdkind_solver(problem, config);
    let result = solver.solve();

    match result {
        PdkindResult::Safe(_) | PdkindResult::Unknown => {
            // Both acceptable: Safe means solved, Unknown means the
            // Bool(true) guard prevented convergence (#4823).
            // The critical property is: NO false Unsafe.
        }
        PdkindResult::Unsafe(cex) => {
            panic!(
                "PDKIND SOUNDNESS BUG (#421): Z3 says sat (safe),\n\
                 but PDKIND incorrectly returned Unsafe at steps={}.",
                cex.steps.len()
            );
        }
        PdkindResult::NotApplicable => {
            panic!("PDKIND returned NotApplicable on dillig01.c_000.smt2.");
        }
        _ => panic!("unexpected variant"),
    }
}

/// Regression test for #6824: PDR false-Safe on inlined multi-predicate hcai benchmark.
/// Z3 returns unsat. AY previously returned sat (false-Safe) because query-only
/// validation was insufficient — the invariant blocked bad states but was
/// non-inductive w.r.t. transition clauses after clause inlining.
#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_portfolio_issue_6824_hcai_o0_id_i10_o10_must_not_be_safe() {
    assert_portfolio_benchmark_is_not_safe(
        include_str!(
            "../fixtures/chc_comp/hcai/svcomp/O0/O0_id_i10_o10_false-unreach-call_true-termination_000.smt2"
        ),
        "O0_id_i10_o10_false-unreach-call_true-termination_000",
    );
}

/// Regression test for #6824: second hcai false-Safe benchmark.
#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_portfolio_issue_6824_hcai_o0_id_o20_must_not_be_safe() {
    assert_portfolio_benchmark_is_not_safe(
        include_str!("../fixtures/chc_comp/hcai/svcomp/O0/O0_id_o20_false-unreach-call_000.smt2"),
        "O0_id_o20_false-unreach-call_000",
    );
}

/// Regression test for #6824: third hcai false-Safe benchmark.
#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_portfolio_issue_6824_hcai_o0_sum_25x0_must_not_be_safe() {
    assert_portfolio_benchmark_is_not_safe(
        include_str!(
            "../fixtures/chc_comp/hcai/svcomp/O0/O0_sum_25x0_false-unreach-call_true-termination_000.smt2"
        ),
        "O0_sum_25x0_false-unreach-call_true-termination_000",
    );
}

/// Regression test for #7688: Kind must not accept deferred-safe `¬query`
/// models on unsafe non-BV benchmarks just because extended BMC/query-only
/// checks passed. The returned witness must still be 1-inductive.
#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_kind_issue_7688_accumulator_unsafe_must_not_be_safe() {
    assert_kind_benchmark_is_not_safe(
        include_str!(
            "../../../../benchmarks/chc-comp/2025/extra-small-lia/accumulator_unsafe_000.smt2"
        ),
        "accumulator_unsafe_000",
    );
}

/// Second regression guard for #7688 on another unsafe arithmetic benchmark
/// from the same deferred-safe family.
#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_kind_issue_7688_two_phase_unsafe_must_not_be_safe() {
    assert_kind_benchmark_is_not_safe(
        include_str!(
            "../../../../benchmarks/chc-comp/2025/extra-small-lia/two_phase_unsafe_000.smt2"
        ),
        "two_phase_unsafe_000",
    );
}

/// Regression test for #6789: the full portfolio must not return false Safe on
/// a kind2 benchmark that previously triggered Kind's local-variable collision.
///
/// The current `HEAD` capability is still weak here: a timeout/Unknown is
/// acceptable, but a Safe result would be a soundness regression.
#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_portfolio_issue_6789_synapse_benchmark_is_not_safe() {
    assert_portfolio_benchmark_is_not_safe(
        include_str!("../fixtures/chc_comp/kind2/SYNAPSE_5_e1_811_000.smt2"),
        "SYNAPSE_5_e1_811_000",
    );
}

/// Regression test for #6789: another kind2 benchmark from the same false-Safe
/// family must also never return Safe from the full portfolio.
#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_portfolio_issue_6789_dragon_benchmark_is_not_safe() {
    assert_portfolio_benchmark_is_not_safe(
        include_str!("../fixtures/chc_comp/kind2/DRAGON_13_e7_2336_000.smt2"),
        "DRAGON_13_e7_2336_000",
    );
}
