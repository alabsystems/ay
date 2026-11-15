// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::convert::Infallible;

use super::{FpBuildError, FpBuildProgress};

/// Shared control for the legacy and cooperative versions of each circuit.
pub(crate) trait BuildControl {
    type Error;

    fn checkpoint(&mut self, progress: FpBuildProgress) -> Result<(), Self::Error>;
}

pub(crate) struct Uninterrupted;

impl BuildControl for Uninterrupted {
    type Error = Infallible;

    #[inline]
    fn checkpoint(&mut self, _: FpBuildProgress) -> Result<(), Self::Error> {
        Ok(())
    }
}

/// Keep one circuit implementation without a panic-based cancellation path.
pub(crate) fn uninterrupted<T>(
    build: impl FnOnce(&mut Uninterrupted) -> Result<T, Infallible>,
) -> T {
    match build(&mut Uninterrupted) {
        Ok(value) => value,
        Err(never) => match never {},
    }
}

pub(super) struct Cooperative<'a> {
    should_stop: &'a mut dyn FnMut(FpBuildProgress) -> bool,
    refusal: Option<FpBuildError>,
}

impl<'a> Cooperative<'a> {
    pub(super) fn new(should_stop: &'a mut dyn FnMut(FpBuildProgress) -> bool) -> Self {
        Self {
            should_stop,
            refusal: None,
        }
    }

    pub(super) fn refusal(&self) -> Option<FpBuildError> {
        self.refusal
    }

    pub(super) fn interrupt(&mut self) -> FpBuildError {
        *self.refusal.get_or_insert(FpBuildError::Interrupted)
    }
}

impl BuildControl for Cooperative<'_> {
    type Error = FpBuildError;

    fn checkpoint(&mut self, progress: FpBuildProgress) -> Result<(), Self::Error> {
        if let Some(error) = self.refusal {
            return Err(error);
        }
        if progress.variables > i32::MAX as u32 {
            self.refusal = Some(FpBuildError::VariableLimit);
            return Err(FpBuildError::VariableLimit);
        }
        // Latch BEFORE invoking user code: a caught callback panic must never
        // allow an incomplete encoding to become exportable on a later call.
        self.refusal = Some(FpBuildError::Interrupted);
        if (self.should_stop)(progress) {
            return Err(FpBuildError::Interrupted);
        }
        self.refusal = None;
        Ok(())
    }
}
