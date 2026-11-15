// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod fixtures;
use fixtures::{authenticate, Fixture};

fn allow(_: usize, _: usize) -> bool {
    true
}

#[test]
fn direct_derived_unit_is_replayed_without_any_rewrite_record() {
    let mut f = Fixture::new();
    let not_unit = f.exec.ctx.terms.mk_not_raw(f.term);
    f.roots.push(not_unit);
    let mut proof = Proof::new();
    let assumed = proof.add_assume(f.term, None);
    let contrary = proof.add_assume(not_unit, None);
    proof.add_resolution(Vec::new(), f.term, assumed, contrary);
    assert!(f.exec.propagated_value_provenance.rewrites.is_empty());
    f.exec
        .derive_propagated_value_assumptions(&mut proof, &f.roots);
    assert!(!proof.steps.contains(&ProofStep::Assume(f.term)));
    let checked = authenticate(&f.exec.ctx.terms, &f.roots, &proof);
    assert_eq!(
        checked.clause(ProofId(proof.steps.len() as u32 - 1)),
        Some([].as_slice())
    );
}

#[test]
fn changed_sources_and_empty_channel_cannot_license_a_stored_unit() {
    let mut f = Fixture::new();
    let original = Proof::from_steps(vec![ProofStep::Assume(f.term)]);
    let mut missing_source = original.clone();
    f.exec
        .derive_propagated_value_assumptions(&mut missing_source, &f.roots[..1]);
    assert_eq!(missing_source, original);
    f.exec.propagated_value_provenance.array_units.clear();
    let mut missing_channel = original.clone();
    f.exec
        .derive_propagated_value_assumptions(&mut missing_channel, &f.roots);
    assert_eq!(missing_channel, original);
}

#[test]
fn append_remaps_every_reference_after_a_nonempty_prefix() {
    let mut f = Fixture::new();
    let set = f.roots.iter().copied().collect();
    let records = HashMap::default();
    let entries = HashMap::default();
    let mut cx = PlanCx::new(&set, &f.roots, &records, &entries, &[], false)
        .with_array_units(&f.exec.propagated_value_provenance.array_units, &allow);
    cx.chain.add_assume(f.roots[0], None);
    let id = PropagationChainPlanner {
        terms: &mut f.exec.ctx.terms,
    }
    .plan_derive_clause(&mut cx, f.term)
    .expect("checked activated unit");
    assert!(id.0 > 1);
    assert_eq!(
        authenticate(&f.exec.ctx.terms, &f.roots, &cx.chain).clause(id),
        Some([f.term].as_slice())
    );
}

#[test]
fn derived_equality_licenses_a_later_rewrite_without_becoming_an_assumption() {
    let mut f = Fixture::new();
    let terms = &mut f.exec.ctx.terms;
    let other = terms.mk_var("other", Sort::bitvec(129));
    let before = terms.mk_app(Symbol::named("bvult"), [f.variable, other], Sort::Bool);
    let after = terms.mk_app(Symbol::named("bvult"), [f.value, other], Sort::Bool);
    f.roots.push(before);
    f.exec
        .propagated_value_provenance
        .entries
        .push(crate::preprocess::PropagatedEntrySource {
            expr: f.variable,
            value: f.value,
            source_assertion: f.term,
            stamp: 1,
        });
    f.exec
        .propagated_value_provenance
        .rewrites
        .push(crate::preprocess::PropagatedRewriteRecord {
            before,
            after,
            stamp: 1,
        });
    let mut proof = Proof::from_steps(vec![ProofStep::Assume(after)]);
    f.exec
        .derive_propagated_value_assumptions(&mut proof, &f.roots);
    assert!(!proof.steps.contains(&ProofStep::Assume(after)));
    assert!(!proof.steps.contains(&ProofStep::Assume(f.term)));
    assert_eq!(
        authenticate(&f.exec.ctx.terms, &f.roots, &proof)
            .clause(ProofId(proof.steps.len() as u32 - 1)),
        Some([after].as_slice())
    );
}

#[test]
fn copying_refuses_forward_self_and_missing_premises_without_remap_fallback() {
    let f = Fixture::new();
    let set = f.roots.iter().copied().collect();
    let records = HashMap::default();
    let entries = HashMap::default();
    for bad in [ProofId(1), ProofId(2), ProofId(u32::MAX)] {
        let mut cx = PlanCx::new(&set, &f.roots, &records, &entries, &[], false);
        let forged = Proof::from_steps(vec![
            ProofStep::Assume(f.roots[0]),
            ProofStep::Resolution {
                clause: vec![f.term],
                pivot: f.roots[0],
                clause1: ProofId(0),
                clause2: bad,
            },
        ]);
        assert!(append_unit_fragment(&mut cx, &forged, ProofId(1)).is_none());
        assert_eq!(cx.chain.steps.len(), 1, "no malformed step is appended");
    }
}

#[test]
fn plan_budget_is_exact_and_failure_does_not_refund_work_or_leave_steps() {
    let mut f = Fixture::new();
    let set = f.roots.iter().copied().collect();
    let records = HashMap::default();
    let entries = HashMap::default();
    let units = &f.exec.propagated_value_provenance.array_units;
    let mut cx =
        PlanCx::new(&set, &f.roots, &records, &entries, &[], false).with_array_units(units, &allow);
    let mut planner = PropagationChainPlanner {
        terms: &mut f.exec.ctx.terms,
    };
    planner
        .plan_array_unit_base(&mut cx, f.term)
        .expect("within historical plan envelope");
    let needed = PLAN_NODE_BUDGET - cx.budget;
    assert!(needed > 1);
    for budget in [0, 1, needed - 1, needed] {
        let mut cx = PlanCx::new(&set, &f.roots, &records, &entries, &[], false)
            .with_array_units(units, &allow);
        cx.budget = budget;
        let result = planner.plan_array_unit_base(&mut cx, f.term);
        assert_eq!(result.is_some(), budget == needed);
        if result.is_none() {
            assert!(cx.chain.steps.is_empty());
            assert!(cx.budget < budget || budget == 0);
        }
    }
}

#[test]
fn fresh_plan_without_array_channel_cannot_reuse_an_old_plan_memo() {
    let mut f = Fixture::new();
    let set = f.roots.iter().copied().collect();
    let records = HashMap::default();
    let entries = HashMap::default();
    let mut old = PlanCx::new(&set, &f.roots, &records, &entries, &[], false)
        .with_array_units(&f.exec.propagated_value_provenance.array_units, &allow);
    let mut planner = PropagationChainPlanner {
        terms: &mut f.exec.ctx.terms,
    };
    assert!(planner.plan_derive_clause(&mut old, f.term).is_some());
    // The c7 constructor does not install this L1-only evidence channel.
    let mut fresh = PlanCx::new(&set, &f.roots, &records, &entries, &[], true);
    assert!(planner.plan_derive_clause(&mut fresh, f.term).is_none());
    assert!(fresh.chain.steps.is_empty());
}

#[test]
fn public_replay_observes_a_fired_interrupt_and_can_retry_a_fresh_attempt() {
    use std::sync::atomic::{AtomicBool, Ordering};
    let mut f = Fixture::new();
    let interrupt = Arc::new(AtomicBool::new(true));
    f.exec.solve_interrupt = Some(Arc::clone(&interrupt));
    let original = Proof::from_steps(vec![ProofStep::Assume(f.term)]);
    let mut proof = original.clone();
    f.exec
        .derive_propagated_value_assumptions(&mut proof, &f.roots);
    assert_eq!(proof, original);
    interrupt.store(false, Ordering::Relaxed);
    f.exec
        .derive_propagated_value_assumptions(&mut proof, &f.roots);
    assert_ne!(proof, original);
    authenticate(&f.exec.ctx.terms, &f.roots, &proof);
}

#[test]
fn query_clear_removes_units_and_restored_records_still_require_current_sources() {
    let mut f = Fixture::new();
    let outer = f.exec.propagated_value_provenance.clone();
    f.exec.clear_preprocessing_proof_records();
    assert!(f.exec.propagated_value_provenance.array_units.is_empty());
    let original = Proof::from_steps(vec![ProofStep::Assume(f.term)]);
    let mut proof = original.clone();
    f.exec
        .derive_propagated_value_assumptions(&mut proof, &f.roots);
    assert_eq!(proof, original);
    f.exec.propagated_value_provenance = outer;
    f.exec.derive_propagated_value_assumptions(&mut proof, &[]);
    assert_eq!(proof, original);
    f.exec
        .derive_propagated_value_assumptions(&mut proof, &f.roots);
    authenticate(&f.exec.ctx.terms, &f.roots, &proof);
    assert_ne!(proof, original);
}
