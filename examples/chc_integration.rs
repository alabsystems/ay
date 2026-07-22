// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CHC Solver Integration Example for AY
//!
//! This example demonstrates how to use AY's CHC (Constrained Horn Clause)
//! solver for invariant synthesis and safety verification. The CHC solver
//! uses PDR (Property Directed Reachability) to prove safety or find
//! counterexamples.
//!
//! # Use Cases
//!
//! - **TLA2-compatible tools**: TLA+ model checking - translates TLA+ specs to CHC for verification
//! - **kani_fast**: Rust model checker - generates CHC from Rust programs
//! - **theorem-prover integration**: backend - CHC solving for decidable fragments
//! - **Program verification tools**: Safety checking for loops and recursion
//!
//! # API Patterns
//!
//! ## Verified solving (recommended)
//! ```text
//! let problem = ChcParser::parse(&smt_text)?;
//! let solver = AdaptivePortfolio::new(problem, AdaptiveConfig::default());
//! let result = solver.solve(); // returns VerifiedChcResult
//! ```
//!
//! ## Individual engine control (via stable `engines` module)
//! ```text
//! let problem = ChcParser::parse(&smt_text)?;
//! let mut solver = ay_chc::engines::new_pdr_solver(problem, config);
//! let result = solver.solve(); // returns raw PdrResult
//! ```

use ay_chc::{engines, ChcParser, PdrConfig, PdrResult};

fn main() {
    println!("AY CHC Solver - Integration Examples\n");

    scenario_1_safe_counter();
    scenario_2_unsafe_counter();
    scenario_3_invariant_extraction();
    scenario_4_custom_config();
    scenario_5_programmatic_chc();

    println!("\nAll CHC scenarios completed successfully!");
}

/// Scenario 1: Safe Counter - Proving Safety
///
/// A counter increments from 0 and stops at 10.
/// Safety property: counter never exceeds 10.
fn scenario_1_safe_counter() {
    println!("=== Scenario 1: Safe Counter ===");

    // SMT-LIB 2 format CHC problem:
    // - Predicate: inv(x)
    // - Init: x = 0 => inv(x)
    // - Transition: inv(x) AND x < 10 => inv(x + 1)
    // - Query: inv(x) AND x > 10 => false
    let chc_text = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
; Init: x starts at 0
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
; Transition: increment while x < 10
(assert (forall ((x Int) (xp Int)) (=> (and (inv x) (< x 10) (= xp (+ x 1))) (inv xp))))
; Safety: x never exceeds 10
(assert (forall ((x Int)) (=> (and (inv x) (> x 10)) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(chc_text).expect("parse failed");
    let config = default_config(false);
    let mut solver = engines::new_pdr_solver(problem, config);

    match solver.solve() {
        PdrResult::Safe(model) => {
            println!("  Result: SAFE");
            println!("  Inductive invariant found:");
            for (pred, interp) in model.iter() {
                println!("    Predicate {:?}: {}", pred, interp.formula);
            }
        }
        PdrResult::Unsafe(cex) => {
            println!("  Result: UNSAFE (unexpected!)");
            println!("  Counterexample has {} steps", cex.steps.len());
        }
        PdrResult::Unknown | PdrResult::NotApplicable | _ => {
            println!("  Result: Unknown (need more iterations or better config)");
        }
    }
    println!();
}

/// Scenario 2: Unsafe Counter - Finding Counterexamples
///
/// A counter decrements from 5 with no lower bound.
/// Safety property: counter never goes negative.
/// This is UNSAFE because the counter will eventually become negative.
fn scenario_2_unsafe_counter() {
    println!("=== Scenario 2: Unsafe Counter (Counterexample Detection) ===");

    let chc_text = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
; Init: x starts at 5
(assert (forall ((x Int)) (=> (= x 5) (inv x))))
; Transition: decrement unconditionally
(assert (forall ((x Int) (xp Int)) (=> (and (inv x) (= xp (- x 1))) (inv xp))))
; Safety: x should never be negative (but it will be!)
(assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(chc_text).expect("parse failed");
    let config = default_config(false);
    let mut solver = engines::new_pdr_solver(problem, config);

    match solver.solve() {
        PdrResult::Safe(_) => {
            println!("  Result: SAFE (unexpected!)");
        }
        PdrResult::Unsafe(cex) => {
            println!("  Result: UNSAFE");
            println!("  Counterexample path ({} steps):", cex.steps.len());
            for (i, step) in cex.steps.iter().enumerate() {
                print!("    Step {}: pred {:?}, values: ", i, step.predicate);
                let values: Vec<_> = step.assignments.iter().collect();
                tracing::info!("{values:?}");
            }
        }
        PdrResult::Unknown | PdrResult::NotApplicable | _ => {
            println!("  Result: Unknown");
        }
    }
    println!();
}

/// Scenario 3: Invariant Extraction
///
/// When PDR proves safety, it produces an inductive invariant.
/// This invariant can be used for:
/// - Verification certificates
/// - Documentation of program properties
/// - Further analysis in downstream tools
fn scenario_3_invariant_extraction() {
    println!("=== Scenario 3: Invariant Extraction ===");

    // Two counters with a relationship
    let chc_text = r#"
(set-logic HORN)
(declare-fun inv (Int Int) Bool)
; Init: x = 0, y = 0
(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 0)) (inv x y))))
; Transition: x' = x + 1, y' = y + 2
(assert (forall ((x Int) (y Int) (xp Int) (yp Int))
  (=> (and (inv x y) (= xp (+ x 1)) (= yp (+ y 2))) (inv xp yp))))
; Safety: y = 2*x always holds
(assert (forall ((x Int) (y Int)) (=> (and (inv x y) (not (= y (* 2 x)))) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(chc_text).expect("parse failed");
    let config = default_config(false);
    let mut solver = engines::new_pdr_solver(problem, config);

    match solver.solve() {
        PdrResult::Safe(model) => {
            println!("  Result: SAFE");
            println!("  Inductive invariant:");
            for (_pred, interp) in model.iter() {
                // The invariant formula is what PDR discovered
                println!("    inv(x, y) = {}", interp.formula);
            }
            println!("  (This invariant implies y = 2*x)");
        }
        PdrResult::Unsafe(_) => {
            println!("  Result: UNSAFE (unexpected!)");
        }
        PdrResult::Unknown | PdrResult::NotApplicable | _ => {
            println!("  Result: Unknown");
        }
    }
    println!();
}

/// Scenario 4: Custom PDR Configuration
///
/// The PDR solver has many tunable parameters.
/// Different problems may benefit from different configurations.
fn scenario_4_custom_config() {
    println!("=== Scenario 4: Custom PDR Configuration ===");

    let chc_text = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (inv x) (< x 100) (= xp (+ x 1))) (inv xp))))
(assert (forall ((x Int)) (=> (and (inv x) (> x 100)) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(chc_text).expect("parse failed");

    // Custom configuration for harder problems.
    // The public example stays on the supported builder surface rather than
    // relying on internal technique toggles.
    let config = PdrConfig::default()
        .with_max_frames(50)
        .with_max_iterations(500)
        .with_max_obligations(50_000)
        .with_verbose(false);

    let mut solver = engines::new_pdr_solver(problem, config);

    match solver.solve() {
        PdrResult::Safe(_) => println!("  Result: SAFE"),
        PdrResult::Unsafe(_) => println!("  Result: UNSAFE"),
        PdrResult::Unknown | PdrResult::NotApplicable => println!("  Result: Unknown"),
        _ => {}
    }
    println!();
}

/// Scenario 5: Programmatic CHC Construction
///
/// For deeper integration, you can construct CHC problems programmatically
/// instead of parsing SMT-LIB text. This is useful when:
/// - Generating CHC from another IR (e.g., Rust MIR, TLA+ specs)
/// - Building incremental CHC problems
/// - Avoiding parsing overhead
fn scenario_5_programmatic_chc() {
    println!("=== Scenario 5: Programmatic CHC Construction ===");

    // The ay-chc crate exposes ChcExpr, HornClause, etc. for direct construction.
    // This example still uses the parser for simplicity, but demonstrates
    // that the problem structure is accessible programmatically.

    let chc_text = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 5)) (inv (+ x 1)))))
(assert (forall ((x Int)) (=> (and (inv x) (>= x 5)) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(chc_text).expect("parse failed");

    // Access problem structure
    println!("  Problem structure:");
    println!("    Number of predicates: {}", problem.predicates().len());
    println!("    Number of clauses: {}", problem.clauses().len());

    // Classify clauses
    let facts = problem
        .clauses()
        .iter()
        .filter(|c| c.is_fact() && !c.is_query())
        .count();
    let rules = problem
        .clauses()
        .iter()
        .filter(|c| !c.is_fact() && !c.is_query())
        .count();
    let queries = problem.clauses().iter().filter(|c| c.is_query()).count();
    tracing::info!("    Facts (init): {facts}");
    tracing::info!("    Rules (transitions): {rules}");
    tracing::info!("    Queries (safety): {queries}");

    // Solve
    let config = default_config(false);
    let mut solver = engines::new_pdr_solver(problem, config);

    match solver.solve() {
        PdrResult::Safe(_) => println!("  Result: SAFE"),
        PdrResult::Unsafe(_) => println!("  Result: UNSAFE"),
        PdrResult::Unknown | PdrResult::NotApplicable => println!("  Result: Unknown"),
        _ => {}
    }
    println!();
}

/// Default configuration for examples
///
/// Uses struct update syntax for maintainability - new PdrConfig fields
/// automatically inherit sensible defaults without breaking this example.
fn default_config(verbose: bool) -> PdrConfig {
    PdrConfig::default()
        .with_max_frames(20)
        .with_max_iterations(500)
        .with_max_obligations(100_000)
        .with_verbose(verbose)
}

// =============================================================================
// Tests - run with `cargo test --example chc_integration`
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_safe_counter() {
        let chc_text = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (inv x) (< x 10) (= xp (+ x 1))) (inv xp))))
(assert (forall ((x Int)) (=> (and (inv x) (> x 10)) false)))
(check-sat)
"#;
        let problem = ChcParser::parse(chc_text).unwrap();
        let config = default_config(false);
        let mut solver = engines::new_pdr_solver(problem, config);
        let result = solver.solve();
        assert!(
            matches!(result, PdrResult::Safe(_)),
            "safe counter should be proven safe"
        );
    }

    #[test]
    fn test_unsafe_counter() {
        let chc_text = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 5) (inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (inv x) (= xp (- x 1))) (inv xp))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))
(check-sat)
"#;
        let problem = ChcParser::parse(chc_text).unwrap();
        let config = default_config(false);
        let mut solver = engines::new_pdr_solver(problem, config);
        let result = solver.solve();
        assert!(
            matches!(result, PdrResult::Unsafe(_)),
            "unsafe counter should produce counterexample"
        );
    }

    #[test]
    fn test_invariant_discovery() {
        let chc_text = r#"
(set-logic HORN)
(declare-fun inv (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 0)) (inv x y))))
(assert (forall ((x Int) (y Int) (xp Int) (yp Int))
  (=> (and (inv x y) (= xp (+ x 1)) (= yp (+ y 2))) (inv xp yp))))
(assert (forall ((x Int) (y Int)) (=> (and (inv x y) (not (= y (* 2 x)))) false)))
(check-sat)
"#;
        let problem = ChcParser::parse(chc_text).unwrap();
        let config = default_config(false);
        let mut solver = engines::new_pdr_solver(problem, config);
        let result = solver.solve();
        assert!(
            matches!(result, PdrResult::Safe(_)),
            "invariant y=2x should be discovered"
        );
    }

    #[test]
    fn test_problem_structure() {
        let chc_text = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 5)) (inv (+ x 1)))))
(assert (forall ((x Int)) (=> (and (inv x) (>= x 5)) false)))
(check-sat)
"#;
        let problem = ChcParser::parse(chc_text).unwrap();

        assert_eq!(problem.predicates().len(), 1, "should have 1 predicate");
        assert_eq!(problem.clauses().len(), 3, "should have 3 clauses");

        let facts = problem
            .clauses()
            .iter()
            .filter(|c| c.is_fact() && !c.is_query())
            .count();
        let rules = problem
            .clauses()
            .iter()
            .filter(|c| !c.is_fact() && !c.is_query())
            .count();
        let queries = problem.clauses().iter().filter(|c| c.is_query()).count();

        assert_eq!(facts, 1, "should have 1 fact");
        assert_eq!(rules, 1, "should have 1 transition rule");
        assert_eq!(queries, 1, "should have 1 query");
    }
}
