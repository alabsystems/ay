// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Proof, Sort, TheoryLemmaKind};

use super::ProvenanceSurfaceAudit;
use crate::executor::Executor;

#[test]
fn standalone_euf_plan_audits_boolean_equality_surface() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("late_euf_a", Sort::Int);
    let b = executor.ctx.terms.mk_var("late_euf_b", Sort::Int);
    let c = executor.ctx.terms.mk_var("late_euf_c", Sort::Int);
    let ab = executor.ctx.terms.mk_eq(a, b);
    let bc = executor.ctx.terms.mk_eq(b, c);
    let ac = executor.ctx.terms.mk_eq(a, c);
    let not_ab = executor.ctx.terms.mk_not_raw(ab);
    let not_bc = executor.ctx.terms.mk_not_raw(bc);
    let plan = executor
        .plan_euf_lemma(&[ac, not_ab, not_bc])
        .expect("transitivity fixture must plan");
    let mut audit = ProvenanceSurfaceAudit::default();
    plan.protect_surface_operands(&mut audit, &mut executor.ctx.terms);
    let mut active = HashMap::default();
    active.insert(not_ab, "(= (= late_euf_a late_euf_b) false)".to_string());
    assert!(!audit.validate_effective(&executor.ctx.terms, &active));
}

#[test]
fn generic_euf_surface_rejects_noncompositional_negation() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("generic_surface_a", Sort::Int);
    let b = executor.ctx.terms.mk_var("generic_surface_b", Sort::Int);
    let c = executor.ctx.terms.mk_var("generic_surface_c", Sort::Int);
    let ab = executor.ctx.terms.mk_eq(a, b);
    let bc = executor.ctx.terms.mk_eq(b, c);
    let ac = executor.ctx.terms.mk_eq(a, c);
    let not_ab = executor.ctx.terms.mk_not_raw(ab);
    let not_bc = executor.ctx.terms.mk_not_raw(bc);
    let clause = vec![ac, not_ab, not_bc];
    let plan = executor
        .plan_euf_lemma(&clause)
        .expect("bare transitivity fixture must plan");
    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("EUF", clause, TheoryLemmaKind::Generic);
    let plans = vec![Some(plan)];
    let mut active = HashMap::default();
    active.insert(
        not_ab,
        "(not (= generic_surface_a generic_surface_c))".to_string(),
    );
    executor.last_proof_term_overrides = Some(active);
    assert!(!executor.generic_euf_promotion_surface_is_safe(&proof, &plans));
}
