// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One explicit native-call owner; speculative/nested trees cannot commit cuts.

use std::ops::Range;
use std::sync::{Arc, Mutex};
use std::time::Instant;

use crate::integer_cut::{CertifiedIntegerCut, IntegerCutVerificationError};
use crate::model::{Model, Row};
use crate::outcome::Outcome;

/// Coverage of the last native tree's globally adopted root-cut sides.
///
/// Node-local cuts and unsupported root derivations confer no batch authority.
/// `unsupported_sides` makes the initial rank-one subset explicit.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CutHarvestSummary {
    /// A native tree finished with a terminal outcome in the caller frame.
    pub native_tree_finished: bool,
    /// Finite sides observed among actual adopted root rows. This is the
    /// exact total only when `adoption_scan_complete`; otherwise a lower bound.
    pub adopted_root_sides: usize,
    /// Every adopted root row was counted before the original deadline.
    pub adoption_scan_complete: bool,
    /// Independently replayed sides available before drain.
    pub certified_sides: usize,
    /// Actual adopted sides whose derivations are outside the current checker.
    pub unsupported_sides: usize,
    /// Counting, snapshotting or reconstruction reached the original deadline.
    pub interrupted: bool,
}

/// An actual adopted root-cut side, as the lower row `coeffs·x >= lb` in the
/// caller's column space. Retained only so an explicit, caller-budgeted proof
/// search can try it later; it confers no authority by itself.
pub(crate) type AdoptedSide = (
    Vec<(u32, num_rational::BigRational)>,
    num_rational::BigRational,
);

/// Result of [`crate::BabSession::certify_cuts_by_split`].
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct SplitCertificationReport {
    /// Retained unsupported sides whose proof search ran to an answer.
    pub attempted: usize,
    /// Of those, sides now exported as verified split cuts.
    pub certified: usize,
    /// Sides still retained for a later call (not reached before the deadline).
    pub remaining: usize,
    /// The deadline stopped the search before every retained side was tried.
    pub interrupted: bool,
}

#[derive(Debug, Default)]
pub(crate) struct CutBatch {
    pub(crate) cuts: Vec<CertifiedIntegerCut>,
    pub(crate) summary: CutHarvestSummary,
    /// Adopted sides the finish-time rank-one checker could not certify.
    pub(crate) unsupported: Vec<AdoptedSide>,
}

#[derive(Debug, Default)]
struct State {
    active: bool,
    finished: CutBatch,
}

/// This carrier is created only around one session's actual native call.
/// The address is an identity tag, never dereferenced or treated as proof data.
/// Rebuilt/reduced models must obtain a source-frame proof path before export.
#[derive(Debug, Clone)]
pub(crate) struct NativeCutCapture {
    source_address: usize,
    state: Arc<Mutex<State>>,
}

impl NativeCutCapture {
    pub(crate) fn new(source: &Model) -> Self {
        Self {
            source_address: std::ptr::from_ref(source) as usize,
            state: Arc::new(Mutex::new(State::default())),
        }
    }

    pub(crate) fn enter(&self, source: &Model) -> Option<NativeCutLease> {
        if self.source_address != std::ptr::from_ref(source) as usize {
            return None;
        }
        let mut state = self.state.lock().ok()?;
        if state.active {
            return None;
        }
        state.active = true;
        state.finished = CutBatch::default();
        Some(NativeCutLease {
            owner: self.clone(),
            pending: CutBatch::default(),
            root_prepared: false,
            adopted: Vec::new(),
        })
    }

    pub(crate) fn take(&self) -> CutBatch {
        self.state
            .lock()
            .map(|mut state| std::mem::take(&mut state.finished))
            .unwrap_or_default()
    }
}

pub(crate) fn finished(outcome: &Outcome) -> bool {
    matches!(
        outcome,
        Outcome::Optimal { .. }
            | Outcome::Infeasible { .. }
            | Outcome::Unbounded
            | Outcome::Feasible {
                incumbent_only: false,
                ..
            }
    )
}

pub(crate) struct NativeCutLease {
    owner: NativeCutCapture,
    pending: CutBatch,
    root_prepared: bool,
    adopted: Vec<(
        Vec<(u32, num_rational::BigRational)>,
        num_rational::BigRational,
    )>,
}

#[cfg(test)]
thread_local! {
    static TEST_CAPTURE_POLLS_LEFT: std::cell::Cell<Option<usize>> = const { std::cell::Cell::new(None) };
}

impl NativeCutLease {
    fn poll(&mut self, deadline: Option<Instant>) -> bool {
        #[cfg(test)]
        let test_expired = TEST_CAPTURE_POLLS_LEFT.with(|remaining| match remaining.get() {
            Some(0) => true,
            Some(left) => {
                remaining.set(Some(left - 1));
                false
            }
            None => false,
        });
        #[cfg(not(test))]
        let test_expired = false;
        if test_expired || deadline.is_some_and(|end| Instant::now() >= end) {
            self.pending.summary.interrupted = true;
            false
        } else {
            true
        }
    }

    pub(crate) fn record_root(
        &mut self,
        adopted: &Model,
        rows: Range<usize>,
        deadline: Option<Instant>,
    ) {
        self.root_prepared = true;
        self.adopted.clear();
        self.pending.summary.adopted_root_sides = 0;
        self.pending.summary.adoption_scan_complete = false;
        // Count actual final adoption, not offers or discarded pools. On
        // expiry retain only the observed count and mark its incompleteness.
        for index in rows.clone() {
            if !self.poll(deadline) {
                return;
            }
            let (_, lower, upper) = adopted.row(Row(index as u32));
            self.pending.summary.adopted_root_sides +=
                usize::from(adopted.row_lb_exact_cow(index, lower).is_some())
                    + usize::from(adopted.row_ub_exact_cow(index, upper).is_some());
        }
        self.pending.summary.adoption_scan_complete = true;
        for index in rows {
            if !self.poll(deadline) {
                return;
            }
            let (entries, lower, upper) = adopted.row(Row(index as u32));
            for (bound, side) in [
                (adopted.row_lb_exact(index, lower), crate::BoundSide::Lower),
                (adopted.row_ub_exact(index, upper), crate::BoundSide::Upper),
            ] {
                let Some(lb) = bound else {
                    continue;
                };
                if !self.poll(deadline) {
                    return;
                }
                let upper = matches!(side, crate::BoundSide::Upper);
                let lb = if upper { -lb } else { lb };
                let mut coeffs = Vec::with_capacity(entries.len());
                for (position, &(column, advice)) in entries.iter().enumerate() {
                    if position & 0xff == 0 && !self.poll(deadline) {
                        return;
                    }
                    let coefficient = adopted.row_coeff_exact(index, column, advice);
                    coeffs.push((column, if upper { -coefficient } else { coefficient }));
                }
                if !self.poll(deadline) {
                    return;
                }
                self.adopted.push((coeffs, lb));
            }
        }
    }

    pub(crate) fn finish(mut self, outcome: &Outcome, source: &Model, deadline: Option<Instant>) {
        if self.root_prepared
            && finished(outcome)
            && self.owner.source_address == std::ptr::from_ref(source) as usize
        {
            self.pending.summary.native_tree_finished = true;
            // Proof reconstruction consumes only the original remaining budget
            // after the search finishes; harvesting never launches a solve.
            for (coeffs, lb) in std::mem::take(&mut self.adopted) {
                match CertifiedIntegerCut::reconstruct(source, coeffs.clone(), lb.clone(), deadline)
                {
                    Ok(Some(cut)) => self.pending.cuts.push(cut),
                    Ok(None)
                    | Err(
                        IntegerCutVerificationError::SourceChanged
                        | IntegerCutVerificationError::NonIntegralPremise
                        | IntegerCutVerificationError::InvalidConclusion,
                    ) => {
                        self.pending.summary.unsupported_sides += 1;
                        self.pending.unsupported.push((coeffs, lb));
                    }
                    Err(IntegerCutVerificationError::Interrupted) => {
                        self.pending.summary.interrupted = true;
                        break;
                    }
                }
            }
            self.pending.summary.certified_sides = self.pending.cuts.len();
            if let Ok(mut state) = self.owner.state.lock() {
                state.finished = std::mem::take(&mut self.pending);
            }
        }
    }
}

impl Drop for NativeCutLease {
    fn drop(&mut self) {
        // An unwind or unfinished tree publishes nothing. Nested entry was
        // refused while this lease was active, so it cannot release this owner.
        if let Ok(mut state) = self.owner.state.lock() {
            state.active = false;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Sense;

    fn source() -> Model {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y = model.add_binary_col();
        model.add_row(f64::NEG_INFINITY, 3.0, &[(x, 2.0), (y, 2.0)]);
        model.set_objective(&[(x, 1.0), (y, 1.0)], Sense::Maximize);
        model
    }

    #[test]
    fn integer_cut_capture_count_interruption_reports_only_observed_adoption() {
        let source = source();
        let owner = NativeCutCapture::new(&source);
        let mut adopted = source.clone();
        let x = adopted.col_at(0).unwrap();
        for _ in 0..512 {
            adopted.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0)]);
        }
        let mut capture = owner.enter(&source).unwrap();
        TEST_CAPTURE_POLLS_LEFT.with(|remaining| remaining.set(Some(1)));
        capture.record_root(&adopted, source.num_rows()..adopted.num_rows(), None);
        TEST_CAPTURE_POLLS_LEFT.with(|remaining| remaining.set(None));
        assert_eq!(capture.pending.summary.adopted_root_sides, 1);
        assert!(!capture.pending.summary.adoption_scan_complete);
        assert!(capture.pending.summary.interrupted);
        assert_eq!(
            capture.adopted.as_slice(),
            &[] as &[(
                Vec<(u32, num_rational::BigRational)>,
                num_rational::BigRational
            )]
        );
        capture.finish(
            &Outcome::Feasible {
                model_values: vec![],
                incumbent_only: false,
                dual_bound: None,
            },
            &source,
            None,
        );
        let batch = owner.take();
        assert!(batch.summary.native_tree_finished);
        assert!(batch.summary.interrupted);
        assert!(!batch.summary.adoption_scan_complete);
        assert_eq!(batch.summary.adopted_root_sides, 1);
        assert_eq!(batch.cuts.as_slice(), &[] as &[CertifiedIntegerCut]);
    }

    #[test]
    fn integer_cut_capture_interrupts_inside_one_large_adopted_row() {
        let source = source();
        let owner = NativeCutCapture::new(&source);
        let mut adopted = source.clone();
        let columns: Vec<_> = (0..1024).map(|_| adopted.add_binary_col()).collect();
        let entries: Vec<_> = columns.into_iter().map(|column| (column, 1.0)).collect();
        adopted.add_row(f64::NEG_INFINITY, 1.0, &entries);
        let mut capture = owner.enter(&source).unwrap();
        // Count, row entry, side entry, coefficient zero. Expiry is then
        // observed inside the coefficient scan, before a whole row commits.
        TEST_CAPTURE_POLLS_LEFT.with(|remaining| remaining.set(Some(4)));
        capture.record_root(&adopted, source.num_rows()..adopted.num_rows(), None);
        TEST_CAPTURE_POLLS_LEFT.with(|remaining| remaining.set(None));
        assert!(capture.pending.summary.adoption_scan_complete);
        assert_eq!(capture.pending.summary.adopted_root_sides, 1);
        assert!(capture.pending.summary.interrupted);
        assert_eq!(
            capture.adopted.as_slice(),
            &[] as &[(
                Vec<(u32, num_rational::BigRational)>,
                num_rational::BigRational
            )]
        );
        // The same complete count succeeds without interruption; this pins
        // the actual upper-side negation rather than a row-size rejection.
        drop(capture);
        let mut control = owner.enter(&source).unwrap();
        control.record_root(&adopted, source.num_rows()..adopted.num_rows(), None);
        assert_eq!(control.adopted.len(), 1);
        let minus_one = num_rational::BigRational::from_integer((-1).into());
        assert!(control.adopted[0].0.iter().all(|(_, a)| *a == minus_one));
        assert_eq!(control.adopted[0].1, minus_one);
        assert!(!control.pending.summary.interrupted);
    }

    #[test]
    fn cut_capture_nested_unwind_and_unfinished_cannot_publish() {
        let source = source();
        let owner = NativeCutCapture::new(&source);
        let mut adopted = source.clone();
        let x = adopted.col_at(0).unwrap();
        let y = adopted.col_at(1).unwrap();
        adopted.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0), (y, 1.0)]);
        let rows = source.num_rows()..adopted.num_rows();
        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut outer = owner.enter(&source).unwrap();
            assert!(
                owner.enter(&source).is_none(),
                "nested tree cannot borrow capture ownership"
            );
            assert!(
                owner.enter(&source.clone()).is_none(),
                "rebuilt frame cannot borrow source ownership"
            );
            outer.record_root(&adopted, rows.clone(), None);
            assert_eq!(outer.adopted.len(), 1);
            panic!("unwind before native finish");
        }));
        assert!(panic.is_err());
        assert_eq!(owner.take().cuts.as_slice(), &[] as &[CertifiedIntegerCut]);
        let mut interrupted = owner.enter(&source).unwrap();
        interrupted.record_root(&adopted, rows.clone(), None);
        interrupted.finish(
            &Outcome::Unknown {
                reason: crate::UnknownReason::Timeout,
            },
            &source,
            None,
        );
        assert_eq!(owner.take().cuts.as_slice(), &[] as &[CertifiedIntegerCut]);
        let mut complete = owner.enter(&source).unwrap();
        complete.record_root(&adopted, rows, None);
        complete.finish(
            &Outcome::Feasible {
                model_values: vec![],
                incumbent_only: false,
                dual_bound: None,
            },
            &source,
            None,
        );
        assert_eq!(owner.take().cuts.len(), 1);
        assert_eq!(owner.take().cuts.as_slice(), &[] as &[CertifiedIntegerCut]);
    }

    #[test]
    fn finished_tree_reconstruction_keeps_the_original_deadline() {
        let source = source();
        let owner = NativeCutCapture::new(&source);
        let mut adopted = source.clone();
        adopted.add_row(
            f64::NEG_INFINITY,
            1.0,
            &[
                (adopted.col_at(0).unwrap(), 1.0),
                (adopted.col_at(1).unwrap(), 1.0),
            ],
        );
        let mut capture = owner.enter(&source).unwrap();
        capture.record_root(&adopted, source.num_rows()..adopted.num_rows(), None);
        capture.finish(
            &Outcome::Feasible {
                model_values: vec![],
                incumbent_only: false,
                dual_bound: None,
            },
            &source,
            Some(Instant::now()),
        );
        let batch = owner.take();
        assert!(batch.summary.native_tree_finished);
        assert!(batch.summary.interrupted);
        assert!(
            batch.cuts.is_empty(),
            "an expired proof budget grants no fresh allowance"
        );
    }

    #[test]
    fn unsupported_adopted_side_is_counted_without_authority() {
        let source = source();
        let owner = NativeCutCapture::new(&source);
        let mut adopted = source.clone();
        // The exact adopted side is authoritative. Its floating proxy would
        // look like a strong supported cut, but the real row is LP-redundant.
        let row = adopted.add_row(
            f64::NEG_INFINITY,
            1.0,
            &[
                (adopted.col_at(0).unwrap(), 1.0),
                (adopted.col_at(1).unwrap(), 1.0),
            ],
        );
        adopted.record_inexact_row_bound(
            row,
            false,
            num_rational::BigRational::from_integer(2.into()),
        );
        let mut capture = owner.enter(&source).unwrap();
        capture.record_root(&adopted, source.num_rows()..adopted.num_rows(), None);
        capture.finish(
            &Outcome::Feasible {
                model_values: vec![],
                incumbent_only: false,
                dual_bound: None,
            },
            &source,
            None,
        );
        let batch = owner.take();
        assert_eq!(batch.summary.adopted_root_sides, 1);
        assert_eq!(batch.summary.unsupported_sides, 1);
        assert_eq!(batch.cuts.as_slice(), &[] as &[CertifiedIntegerCut]);
    }
}
