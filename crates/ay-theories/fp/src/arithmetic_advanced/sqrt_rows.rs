// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private recurrence coverage; Operation itself does not label a sqrt row.

use super::*;
use crate::construction::FpBuildError;
use crate::{FpBuildProgress, TermStore};
use std::time::{Duration, Instant};

struct Trace {
    end: Instant,
    stop_at: Option<usize>,
    refused: bool,
    progress: Vec<FpBuildProgress>,
}

impl BuildControl for Trace {
    type Error = FpBuildError;

    fn checkpoint(&mut self, p: FpBuildProgress) -> Result<(), Self::Error> {
        if self.refused {
            return Err(FpBuildError::Interrupted);
        }
        self.progress.push(p);
        self.refused = Instant::now() >= self.end || self.stop_at == Some(self.progress.len());
        if self.refused {
            Err(FpBuildError::Interrupted)
        } else {
            Ok(())
        }
    }
}

#[test]
fn every_digit_row_has_original_control_before_and_after_real_frontier_growth() {
    let end = Instant::now() + Duration::from_secs(20);
    let terms = TermStore::new();
    for (width, rows) in [(8, 6), (16, 14), (29, 27), (58, 56)] {
        let mut solver = FpSolver::new(&terms);
        let input: Vec<_> = (0..width).map(|_| solver.fresh_var()).collect();
        let mut trace = Trace {
            end,
            stop_at: None,
            refused: false,
            progress: Vec::new(),
        };
        let (q, r) = solver
            .sqrt_digit_recurrence_with_control(&input, rows, &mut trace)
            .unwrap();
        assert_eq!((q.len(), r.len()), (width, width));
        assert_eq!(trace.progress.len(), 2 * rows + 2);
        assert!(trace
            .progress
            .iter()
            .all(|p| p.stage == FpBuildStage::Operation));
        for row in 0..rows {
            let before = trace.progress[1 + 2 * row];
            let after = trace.progress[2 + 2 * row];
            assert!(after.variables > before.variables);
            assert!(after.clauses > before.clauses);
        }
        assert_eq!(
            trace.progress.last().unwrap().clauses,
            solver.clauses().len()
        );
        assert!(Instant::now() < end);
    }
}

#[test]
fn private_row_refusal_follows_completed_rows_and_never_returns_partial_vectors() {
    let end = Instant::now() + Duration::from_secs(20);
    let terms = TermStore::new();
    for stop_at in [6, 7, 30] {
        let mut solver = FpSolver::new(&terms);
        let input: Vec<_> = (0..16).map(|_| solver.fresh_var()).collect();
        let mut trace = Trace {
            end,
            stop_at: Some(stop_at),
            refused: false,
            progress: Vec::new(),
        };
        assert!(matches!(
            solver.sqrt_digit_recurrence_with_control(&input, 14, &mut trace),
            Err(FpBuildError::Interrupted)
        ));
        assert_eq!(trace.progress.len(), stop_at);
        assert!(trace.progress[4].variables > trace.progress[1].variables);
        assert!(trace.progress[4].clauses > trace.progress[1].clauses);
        trace.stop_at = None;
        assert!(matches!(
            solver.sqrt_digit_recurrence_with_control(&input, 14, &mut trace),
            Err(FpBuildError::Interrupted)
        ));
        assert_eq!(trace.progress.len(), stop_at);
    }
}
