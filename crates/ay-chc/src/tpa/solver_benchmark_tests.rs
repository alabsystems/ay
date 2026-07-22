// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::TpaConfig;
use ntest::timeout;

// TPA benchmark integration tests

fn solve_with_tpa(input: &str) -> crate::portfolio::PortfolioResult {
    use crate::parser::ChcParser;
    use crate::portfolio::{PortfolioConfig, PortfolioSolver};
    let problem = ChcParser::parse(input).expect("valid SMT-LIB input");
    let tpa_config = TpaConfig::with_max_power(10);
    let config = PortfolioConfig::tpa_only(tpa_config);
    let solver = PortfolioSolver::new(problem, config);
    solver.solve()
}

/// TPA on dillig12_m_e1: 2-predicate problem requiring case-splitting (#1306).
/// TPA cannot solve it; verifies termination with Unknown. A 30s portfolio-level
/// timeout provides the cancellation token that bounds total wall-clock time.
/// Without it, tpa_only() has no cancellation and each power level can issue
/// many recursive reachability queries (up to 100 iterations each at 5s/query),
/// exceeding any reasonable ntest timeout (#5011).
#[test]
#[timeout(60_000)]
fn test_tpa_dillig12_m_e1() {
    use crate::parser::ChcParser;
    use crate::portfolio::{PortfolioConfig, PortfolioResult, PortfolioSolver};
    let input = r#"
(set-logic HORN)
(declare-fun |SAD| ( Int Int ) Bool)
(declare-fun |FUN| ( Int Int Int Int Int ) Bool)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and (and (= C 0) (= B 0) (= A 0) (= D 0) (= E 1)))
      (FUN A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) )
    (=>
      (and
        (FUN A B C D J)
        (and (= I (ite (= J 1) (+ E F) E))
     (= H (+ C F))
     (= G (+ 1 B))
     (= F (+ 1 A))
     (= E (+ D G)))
      )
      (FUN F G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) )
    (=>
      (and
        (FUN A B E D C)
        (let ((a!1 (= F (ite (= C 1) (+ 2 D (* (- 2) E)) 1))))
  (and a!1 (= G 0)))
      )
      (SAD F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (SAD B A)
        (and (or (= C (+ 1 A)) (= C (+ 2 A))) (<= A B))
      )
      (SAD B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and (SAD A B) (> B A))
      false
    )
  )
)
(check-sat)
"#;

    // Portfolio-level 30s timeout sets a cancellation token so TPA terminates
    // predictably. Without it, tpa_only() runs inline with no cancellation,
    // and recursive reachability queries can far exceed per-query timeouts.
    use std::time::Duration;
    let problem = ChcParser::parse(input).expect("valid SMT-LIB input");
    let tpa_config = TpaConfig {
        max_power: 2,
        timeout_per_power: Duration::from_secs(5),
        ..TpaConfig::default()
    };
    let config = PortfolioConfig::tpa_only(tpa_config).timeout(Some(Duration::from_secs(30)));
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();
    assert!(
        matches!(result, PortfolioResult::Safe(_) | PortfolioResult::Unknown),
        "Expected Safe or Unknown, got {result:?}"
    );
}

/// Simple test to verify TPA basic functionality.
#[test]
#[timeout(10_000)]
fn test_tpa_simple_counter() {
    use crate::portfolio::PortfolioResult;
    let input = r#"
(set-logic HORN)
(declare-fun |inv| ( Int ) Bool)
(assert
  (forall ( (x Int) )
    (=>
      (= x 0)
      (inv x)
    )
  )
)
(assert
  (forall ( (x Int) (xp Int) )
    (=>
      (and (inv x) (= xp (+ x 1)) (<= x 10))
      (inv xp)
    )
  )
)
(assert
  (forall ( (x Int) )
    (=>
      (and (inv x) (< x 0))
      false
    )
  )
)
(check-sat)
"#;

    let result = solve_with_tpa(input);
    assert!(
        matches!(result, PortfolioResult::Safe(_) | PortfolioResult::Unknown),
        "Expected Safe or Unknown for simple counter, got {result:?}"
    );
}
