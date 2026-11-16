// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::preprocess::{PropagatedEntrySource, PropagatedRewriteRecord};
use std::sync::atomic::{AtomicBool, Ordering};

use super::super::tests::fixtures::Fixture;

fn fixture() -> Fixture {
    let mut f = Fixture::new();
    f.exec.ctx.assertions = f.roots.clone();
    let records = &mut f.exec.propagated_value_provenance;
    // Bookkeeping sentinels, not additional proof or SAT authority.
    records.entries.push(PropagatedEntrySource {
        expr: f.variable,
        value: f.value,
        source_assertion: f.term,
        stamp: 17,
    });
    records.rewrites.push(PropagatedRewriteRecord {
        before: f.term,
        after: f.roots[0],
        stamp: 23,
    });
    records.eq_diffvar_rewrites.push(PropagatedRewriteRecord {
        before: f.roots[1],
        after: f.term,
        stamp: 31,
    });
    f
}

fn assert_other_state_unchanged(f: &Fixture) {
    assert_eq!(f.exec.ctx.assertions, f.roots);
    let records = &f.exec.propagated_value_provenance;
    assert_eq!(records.entries.len(), 1);
    let entry = &records.entries[0];
    assert_eq!(
        (entry.expr, entry.value, entry.source_assertion, entry.stamp),
        (f.variable, f.value, f.term, 17)
    );
    assert_eq!(records.rewrites.len(), 1);
    let rewrite = &records.rewrites[0];
    assert_eq!(
        (rewrite.before, rewrite.after, rewrite.stamp),
        (f.term, f.roots[0], 23)
    );
    assert_eq!(records.eq_diffvar_rewrites.len(), 1);
    let rewrite = &records.eq_diffvar_rewrites[0];
    assert_eq!(
        (rewrite.before, rewrite.after, rewrite.stamp),
        (f.roots[1], f.term, 31)
    );
}

#[test]
fn retention_moves_shared_proof_data_without_rewriting_sources_or_stamps() {
    let mut f = fixture();
    let unit = f.exec.propagated_value_provenance.array_units[0].clone();
    let (proof, _) = unit
        .reauthenticate(&f.exec.ctx.terms, &f.roots, &mut |_, _| true)
        .unwrap();
    let steps = proof.steps.as_ptr();
    let guard_proof = Proof::from_steps(vec![ProofStep::Assume(f.roots[0])]);
    let guard_steps = guard_proof.steps.as_ptr();
    let guard = ArrayUnitDerivation::checked(
        &f.exec.ctx.terms,
        &f.roots,
        Arc::new(guard_proof),
        ProofId(0),
        f.roots[0],
        &mut |_, _| true,
    )
    .unwrap();
    assert!(f
        .exec
        .retain_array_preprocessing_units(vec![guard, unit], &mut |_, _| true));
    assert_other_state_unchanged(&f);
    assert_eq!(f.exec.propagated_value_provenance.array_units.len(), 3);
    let expected = [(f.term, steps), (f.roots[0], guard_steps), (f.term, steps)];
    for (unit, (term, steps)) in f
        .exec
        .propagated_value_provenance
        .array_units
        .iter()
        .zip(expected)
    {
        assert_eq!(unit.term(), term);
        let (proof, _) = unit
            .reauthenticate(&f.exec.ctx.terms, &f.roots, &mut |_, _| true)
            .unwrap();
        assert_eq!(proof.steps.as_ptr(), steps);
        assert!(unit
            .reauthenticate(&f.exec.ctx.terms, &[], &mut |_, _| true)
            .is_none());
    }
}

#[test]
fn exact_retained_cap_succeeds_and_one_more_preserves_every_existing_record() {
    let mut f = fixture();
    let unit = f.exec.propagated_value_provenance.array_units[0].clone();
    let mut charges = Vec::new();
    assert!(f.exec.retain_array_preprocessing_units(
        vec![unit.clone(); MAX_STORED_PROPAGATION_RECORDS - 1],
        &mut |work, bytes| {
            charges.push((work, bytes));
            true
        },
    ));
    assert_eq!(
        charges,
        [
            (
                MAX_STORED_PROPAGATION_RECORDS,
                MAX_STORED_PROPAGATION_RECORDS * size_of::<ArrayUnitDerivation>(),
            ),
            (0, 0),
        ]
    );
    assert!(!f
        .exec
        .retain_array_preprocessing_units(vec![unit], &mut |_, _| {
            panic!("over-cap admission refuses before reserving or charging")
        }));
    assert_eq!(
        f.exec.propagated_value_provenance.array_units.len(),
        MAX_STORED_PROPAGATION_RECORDS
    );
    assert_other_state_unchanged(&f);
}

#[test]
fn work_byte_and_final_poll_refusals_leave_the_complete_old_state() {
    let needed = 2 * size_of::<ArrayUnitDerivation>();
    for (mut work, mut bytes, final_poll, success) in [
        (1usize, needed, true, false),
        (2, needed - 1, true, false),
        (2, needed, false, false),
        (2, needed, true, true),
    ] {
        let mut f = fixture();
        let unit = f.exec.propagated_value_provenance.array_units[0].clone();
        let admitted = f
            .exec
            .retain_array_preprocessing_units(vec![unit], &mut |dw, db| {
                if dw == 0 && db == 0 {
                    return final_poll;
                }
                let (Some(w), Some(b)) = (work.checked_sub(dw), bytes.checked_sub(db)) else {
                    return false;
                };
                (work, bytes) = (w, b);
                true
            });
        assert_eq!(admitted, success);
        assert_eq!(
            f.exec.propagated_value_provenance.array_units.len(),
            if success { 2 } else { 1 }
        );
        assert_other_state_unchanged(&f);
    }
}

#[test]
fn prior_phase_consumption_is_not_reset_when_the_owned_callback_moves_to_retention() {
    let max_work = PLAN_NODE_BUDGET * MAX_STORED_PROPAGATION_RECORDS;
    let max_bytes = 64 * 1024 * 1024;
    let needed_bytes = 2 * size_of::<ArrayUnitDerivation>();
    for (prior_work, prior_bytes, success) in [
        (max_work - 2, max_bytes - needed_bytes, true),
        (max_work - 1, max_bytes - needed_bytes, false),
        (max_work - 2, max_bytes - needed_bytes + 1, false),
    ] {
        let mut f = fixture();
        let mut prior_phase = f.exec.array_preprocessing_progress();
        assert!(prior_phase(prior_work, prior_bytes));
        let mut recording_phase = prior_phase;
        let unit = f.exec.propagated_value_provenance.array_units[0].clone();
        assert_eq!(
            f.exec
                .retain_array_preprocessing_units(vec![unit], recording_phase.as_mut()),
            success
        );
        assert!(!recording_phase(1, 1));
        assert!(!recording_phase(0, 0), "exhaustion is sticky across phases");
        assert_eq!(
            f.exec.propagated_value_provenance.array_units.len(),
            if success { 2 } else { 1 }
        );
        assert_other_state_unchanged(&f);
    }
}

#[test]
fn live_interrupt_or_deadline_cannot_be_cleared_to_resume_a_refused_retention() {
    for deadline in [false, true] {
        let mut f = fixture();
        let interrupt = Arc::new(AtomicBool::new(false));
        f.exec
            .set_solve_controls(Some(Arc::clone(&interrupt)), None);
        let mut progress = f.exec.array_preprocessing_progress();
        if deadline {
            f.exec
                .set_solve_controls(None, Some(ay_core::time::Instant::now()));
        } else {
            interrupt.store(true, Ordering::Relaxed);
        }
        let unit = f.exec.propagated_value_provenance.array_units[0].clone();
        assert!(!f
            .exec
            .retain_array_preprocessing_units(vec![unit.clone()], progress.as_mut()));
        assert_eq!(f.exec.propagated_value_provenance.array_units.len(), 1);
        assert_other_state_unchanged(&f);
        interrupt.store(false, Ordering::Relaxed);
        f.exec.set_solve_controls(None, None);
        assert!(!f
            .exec
            .retain_array_preprocessing_units(vec![unit.clone()], progress.as_mut()));
        let mut fresh = f.exec.array_preprocessing_progress();
        assert!(f
            .exec
            .retain_array_preprocessing_units(vec![unit], fresh.as_mut()));
        assert_eq!(f.exec.propagated_value_provenance.array_units.len(), 2);
        assert_other_state_unchanged(&f);
    }
}
