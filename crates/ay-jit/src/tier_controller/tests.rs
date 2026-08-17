// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn sat_profile(num_vars: usize, num_clauses: usize) -> FormulaProfile {
    FormulaProfile {
        num_vars,
        num_clauses,
        clause_var_ratio: if num_vars > 0 {
            num_clauses as f64 / num_vars as f64
        } else {
            0.0
        },
        has_theories: false,
    }
}

fn theory_profile(num_vars: usize, num_clauses: usize) -> FormulaProfile {
    FormulaProfile {
        num_vars,
        num_clauses,
        clause_var_ratio: if num_vars > 0 {
            num_clauses as f64 / num_vars as f64
        } else {
            0.0
        },
        has_theories: true,
    }
}

// ── max_tier_for_formula ──────────────────────────────────────────

#[test]
fn test_max_tier_tiny_formula() {
    let profile = sat_profile(50, 200);
    assert_eq!(
        max_tier_for_formula(&profile, true),
        CompilationTier::HotLoopJit,
    );
}

#[test]
fn test_max_tier_small_formula() {
    let profile = sat_profile(500, 2000);
    assert_eq!(
        max_tier_for_formula(&profile, true),
        CompilationTier::ComponentJit,
    );
}

#[test]
fn test_max_tier_medium_formula() {
    let profile = sat_profile(5000, 20_000);
    assert_eq!(
        max_tier_for_formula(&profile, true),
        CompilationTier::SolverJit,
    );
}

#[test]
fn test_max_tier_large_formula() {
    let profile = sat_profile(50_000, 200_000);
    assert_eq!(
        max_tier_for_formula(&profile, true),
        CompilationTier::WholeProgram,
    );
}

#[test]
fn test_max_tier_backend_unavailable() {
    let profile = sat_profile(50_000, 200_000);
    assert_eq!(
        max_tier_for_formula(&profile, false),
        CompilationTier::HotLoopJit,
    );
}

// ── TierController basics ─────────────────────────────────────────

#[test]
fn test_controller_starts_at_t0() {
    let ctrl = TierController::new(sat_profile(1000, 4000), true);
    assert_eq!(ctrl.current_tier(), CompilationTier::Interpret);
    assert_eq!(ctrl.target_tier(), CompilationTier::Interpret);
    assert!(!ctrl.is_compiling());
    assert!(ctrl.promotions().is_empty());
}

#[test]
fn test_immediate_t1_promotion() {
    let mut ctrl = TierController::new(sat_profile(1000, 4000), true);
    // T1 threshold is 0 conflicts — fires immediately.
    let tier = ctrl.on_conflict(0);
    assert_eq!(tier, Some(CompilationTier::HotLoopJit));
    assert!(ctrl.is_compiling());
    assert_eq!(ctrl.target_tier(), CompilationTier::HotLoopJit);
    // Current tier hasn't changed yet — waiting for restart.
    assert_eq!(ctrl.current_tier(), CompilationTier::Interpret);
}

#[test]
fn test_t1_swap_at_restart() {
    let mut ctrl = TierController::new(sat_profile(1000, 4000), true);
    ctrl.on_conflict(0); // Queue T1
    let swapped = ctrl.on_restart(5);
    assert_eq!(swapped, Some(CompilationTier::HotLoopJit));
    assert_eq!(ctrl.current_tier(), CompilationTier::HotLoopJit);
    assert!(!ctrl.is_compiling());
    assert_eq!(ctrl.promotions().len(), 1);
    assert_eq!(ctrl.promotions()[0].tier, CompilationTier::HotLoopJit);
    assert_eq!(ctrl.promotions()[0].conflict_count, 5);
}

#[test]
fn test_promote_immediate() {
    let mut ctrl = TierController::new(sat_profile(1000, 4000), true);
    ctrl.promote_immediate(CompilationTier::HotLoopJit, 0);
    assert_eq!(ctrl.current_tier(), CompilationTier::HotLoopJit);
    assert_eq!(ctrl.target_tier(), CompilationTier::HotLoopJit);
    assert!(!ctrl.is_compiling());
    assert_eq!(ctrl.promotions().len(), 1);
}

// ── Tier progression ─────────────────────────────────────────────

#[test]
fn test_t1_to_t2_promotion() {
    let mut ctrl = TierController::new(sat_profile(5000, 20_000), true);
    // Start at T0, promote to T1 immediately.
    ctrl.promote_immediate(CompilationTier::HotLoopJit, 0);

    // Not enough conflicts for T2 yet.
    assert_eq!(ctrl.on_conflict(500), None);

    // Reach T2 threshold (1000 conflicts for medium non-dense formula).
    let tier = ctrl.on_conflict(1000);
    assert_eq!(tier, Some(CompilationTier::ComponentJit));
}

#[test]
fn test_full_tier_progression() {
    // Use 100K vars (clearly > 50K threshold for large formula).
    let mut ctrl = TierController::new(sat_profile(100_000, 400_000), true);

    // T0 -> T1 (threshold 0)
    ctrl.promote_immediate(CompilationTier::HotLoopJit, 0);

    // T1 -> T2 (threshold 200 for large formula)
    let tier = ctrl.on_conflict(200);
    assert_eq!(tier, Some(CompilationTier::ComponentJit));
    ctrl.on_compilation_complete(CompilationTier::ComponentJit);
    ctrl.on_restart(250);
    assert_eq!(ctrl.current_tier(), CompilationTier::ComponentJit);

    // T2 -> T3 (threshold 2000 for large formula)
    let tier = ctrl.on_conflict(2000);
    assert_eq!(tier, Some(CompilationTier::SolverJit));
    ctrl.on_compilation_complete(CompilationTier::SolverJit);
    ctrl.on_restart(2500);
    assert_eq!(ctrl.current_tier(), CompilationTier::SolverJit);

    // T3 -> T4 (threshold 20000 for large formula)
    let tier = ctrl.on_conflict(20_000);
    assert_eq!(tier, Some(CompilationTier::WholeProgram));
    ctrl.on_compilation_complete(CompilationTier::WholeProgram);
    ctrl.on_restart(20_500);
    assert_eq!(ctrl.current_tier(), CompilationTier::WholeProgram);

    // At T4, no more promotions.
    assert_eq!(ctrl.on_conflict(1_000_000), None);

    // 4 promotions total.
    assert_eq!(ctrl.promotions().len(), 4);
}

// ── Tier cap by formula difficulty ────────────────────────────────

#[test]
fn test_tiny_formula_caps_at_t1() {
    let mut ctrl = TierController::new(sat_profile(50, 200), true);
    ctrl.promote_immediate(CompilationTier::HotLoopJit, 0);
    // Even with many conflicts, can't promote past T1 for tiny formula.
    assert_eq!(ctrl.on_conflict(1_000_000), None);
    assert_eq!(ctrl.max_tier(), CompilationTier::HotLoopJit);
}

#[test]
fn test_small_formula_caps_at_t2() {
    let mut ctrl = TierController::new(sat_profile(500, 2000), true);
    ctrl.promote_immediate(CompilationTier::HotLoopJit, 0);

    let tier = ctrl.on_conflict(1000);
    assert_eq!(tier, Some(CompilationTier::ComponentJit));
    ctrl.on_compilation_complete(CompilationTier::ComponentJit);
    ctrl.on_restart(1100);

    // Can't go past T2.
    assert_eq!(ctrl.on_conflict(100_000), None);
    assert_eq!(ctrl.max_tier(), CompilationTier::ComponentJit);
}

// ── No double-compile ────────────────────────────────────────────

#[test]
fn test_no_promotion_during_compilation() {
    // Use 100K vars (clearly > 50K threshold for large formula).
    let mut ctrl = TierController::new(sat_profile(100_000, 400_000), true);
    ctrl.promote_immediate(CompilationTier::HotLoopJit, 0);

    // Queue T2 (threshold 200 for large formula).
    assert_eq!(ctrl.on_conflict(200), Some(CompilationTier::ComponentJit));

    // While T2 is compiling, can't queue T3 even if threshold is reached.
    assert_eq!(ctrl.on_conflict(2000), None);
    assert!(ctrl.is_compiling());

    // Complete T2, then T3 becomes queueable.
    ctrl.on_compilation_complete(CompilationTier::ComponentJit);
    ctrl.on_restart(2500);
    assert_eq!(ctrl.on_conflict(2500), Some(CompilationTier::SolverJit));
}

// ── should_compile ───────────────────────────────────────────────

#[test]
fn test_should_compile() {
    let ctrl = TierController::new(sat_profile(5000, 20_000), true);
    assert!(ctrl.should_compile(CompilationTier::HotLoopJit));
    assert!(ctrl.should_compile(CompilationTier::ComponentJit));
    assert!(ctrl.should_compile(CompilationTier::SolverJit));
    // SolverJit is max for medium formula.
    assert!(!ctrl.should_compile(CompilationTier::WholeProgram));
}

#[test]
fn test_should_compile_backend_unavailable() {
    let ctrl = TierController::new(sat_profile(50_000, 200_000), false);
    assert!(ctrl.should_compile(CompilationTier::HotLoopJit));
    // Without the external code generation backend, T2+ are not available.
    assert!(!ctrl.should_compile(CompilationTier::ComponentJit));
    assert!(!ctrl.should_compile(CompilationTier::SolverJit));
}

#[test]
fn test_should_compile_already_at_tier() {
    let mut ctrl = TierController::new(sat_profile(5000, 20_000), true);
    ctrl.promote_immediate(CompilationTier::HotLoopJit, 0);
    assert!(!ctrl.should_compile(CompilationTier::HotLoopJit));
    assert!(!ctrl.should_compile(CompilationTier::Interpret));
}

// ── Theory formulas ──────────────────────────────────────────────

#[test]
fn test_theory_formula_delayed_thresholds() {
    let mut ctrl = TierController::new(theory_profile(5000, 20_000), true);
    ctrl.promote_immediate(CompilationTier::HotLoopJit, 0);

    // Theory formulas have 2x thresholds. Default T2 = 1000 => 2000.
    assert_eq!(ctrl.on_conflict(1000), None);
    assert_eq!(ctrl.on_conflict(2000), Some(CompilationTier::ComponentJit));
}

// ── Dense formula ────────────────────────────────────────────────

#[test]
fn test_dense_formula_earlier_thresholds() {
    let profile = FormulaProfile {
        num_vars: 5000,
        num_clauses: 100_000,
        clause_var_ratio: 20.0,
        has_theories: false,
    };
    let mut ctrl = TierController::new(profile, true);
    ctrl.promote_immediate(CompilationTier::HotLoopJit, 0);

    // Dense formulas have T2 at 500 instead of 1000.
    assert_eq!(ctrl.on_conflict(500), Some(CompilationTier::ComponentJit));
}

// ── Reset for incremental ────────────────────────────────────────

#[test]
fn test_reset_for_new_solve() {
    let mut ctrl = TierController::new(sat_profile(5000, 20_000), true);
    ctrl.promote_immediate(CompilationTier::HotLoopJit, 0);
    assert_eq!(ctrl.promotions().len(), 1);

    ctrl.reset_for_new_solve();
    assert_eq!(ctrl.current_tier(), CompilationTier::Interpret);
    assert_eq!(ctrl.target_tier(), CompilationTier::Interpret);
    assert!(!ctrl.is_compiling());
    // Promotions are preserved for cumulative stats.
    assert_eq!(ctrl.promotions().len(), 1);
}

// ── Default controller ───────────────────────────────────────────

#[test]
fn test_default_controller_with_backend_available() {
    let ctrl = TierController::default_controller(true);
    assert_eq!(ctrl.max_tier(), CompilationTier::WholeProgram);
}

#[test]
fn test_default_controller_with_backend_unavailable() {
    let ctrl = TierController::default_controller(false);
    assert_eq!(ctrl.max_tier(), CompilationTier::HotLoopJit);
}

// ── CompilationTier ordering ─────────────────────────────────────

#[test]
fn test_tier_ordering() {
    assert!(CompilationTier::Interpret < CompilationTier::HotLoopJit);
    assert!(CompilationTier::HotLoopJit < CompilationTier::ComponentJit);
    assert!(CompilationTier::ComponentJit < CompilationTier::SolverJit);
    assert!(CompilationTier::SolverJit < CompilationTier::WholeProgram);
}

#[test]
fn test_tier_display() {
    assert_eq!(CompilationTier::Interpret.to_string(), "T0:interpret");
    assert_eq!(CompilationTier::HotLoopJit.to_string(), "T1:hot-loop");
    assert_eq!(CompilationTier::ComponentJit.to_string(), "T2:component");
    assert_eq!(CompilationTier::SolverJit.to_string(), "T3:solver");
    assert_eq!(
        CompilationTier::WholeProgram.to_string(),
        "T4:whole-program"
    );
}
