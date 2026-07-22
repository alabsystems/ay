// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Focused tests for SAT phase-seed context handling.

use super::context::SmtContext;
use super::types::SmtValue;
use ay_core::kani_compat::DetHashMap as FxHashMap;

#[test]
fn test_with_phase_seed_model_restores_previous_seed() {
    let mut ctx = SmtContext::new();

    let mut baseline_seed = FxHashMap::default();
    baseline_seed.insert("x".to_string(), SmtValue::Int(7));
    ctx.phase_seed_model = Some(baseline_seed.clone());

    let mut temporary_seed = FxHashMap::default();
    temporary_seed.insert("x".to_string(), SmtValue::Int(1));

    let seen_inside = ctx.with_phase_seed_model(Some(&temporary_seed), |inner| {
        inner.phase_seed_model.clone()
    });
    assert_eq!(seen_inside, Some(temporary_seed.clone()));
    assert_eq!(ctx.phase_seed_model, Some(baseline_seed.clone()));

    ctx.with_phase_seed_model(None, |inner| {
        assert_eq!(inner.phase_seed_model, None);
    });
    assert_eq!(ctx.phase_seed_model, Some(baseline_seed));
}
