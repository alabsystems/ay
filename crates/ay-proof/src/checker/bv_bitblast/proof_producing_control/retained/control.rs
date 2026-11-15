// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{BridgeError, Instant};

/// A typed extension may carry lower-level errors without changing the old
/// bridge's stop precedence or adding a second cleanup/control pipeline.
pub(super) trait ControlError: From<BridgeError> {
    fn bridge_error(&self) -> Option<&BridgeError>;
}

impl ControlError for BridgeError {
    fn bridge_error(&self) -> Option<&BridgeError> {
        Some(self)
    }
}

#[derive(Clone, Copy)]
enum Stop {
    Cancelled,
    Deadline,
}

impl Stop {
    fn error(self) -> BridgeError {
        match self {
            Self::Cancelled => BridgeError::Cancelled,
            Self::Deadline => BridgeError::Deadline,
        }
    }
}

pub(super) struct Control<'a> {
    deadline: Instant,
    keep_going: &'a mut dyn FnMut() -> bool,
    stopped: Option<Stop>,
}

impl<'a> Control<'a> {
    pub(super) fn new(deadline: Instant, keep_going: &'a mut dyn FnMut() -> bool) -> Self {
        Self {
            deadline,
            keep_going,
            stopped: None,
        }
    }

    pub(super) fn deadline(&self) -> Instant {
        self.deadline
    }

    pub(super) fn tighten(&mut self, deadline: Instant) -> Result<(), BridgeError> {
        self.deadline = self.deadline.min(deadline);
        self.poll()
    }

    pub(super) fn poll(&mut self) -> Result<(), BridgeError> {
        if let Some(stop) = self.stopped {
            return Err(stop.error());
        }
        if Instant::now() >= self.deadline {
            self.stopped = Some(Stop::Deadline);
            return Err(BridgeError::Deadline);
        }
        // Latch before entering caller code. A false return or a panic caught
        // by a nested guard cannot be undone by a later successful callback.
        self.stopped = Some(Stop::Cancelled);
        if !(self.keep_going)() {
            return Err(BridgeError::Cancelled);
        }
        self.stopped = None;
        if Instant::now() >= self.deadline {
            self.stopped = Some(Stop::Deadline);
            return Err(BridgeError::Deadline);
        }
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn run<T>(
        &mut self,
        operation: impl FnOnce(&mut Self) -> Result<T, BridgeError>,
    ) -> Result<T, BridgeError> {
        self.run_typed(operation)
    }

    pub(super) fn run_typed<T, E: ControlError>(
        &mut self,
        operation: impl FnOnce(&mut Self) -> Result<T, E>,
    ) -> Result<T, E> {
        self.poll()?;
        let result = operation(self);
        // An observed lower-level stop must stay terminal even if it did not
        // originate in this callback. Earlier observed stop identity wins.
        if self.stopped.is_none() {
            self.stopped = match result.as_ref().err().and_then(ControlError::bridge_error) {
                Some(BridgeError::Cancelled) => Some(Stop::Cancelled),
                Some(BridgeError::Deadline) => Some(Stop::Deadline),
                _ => None,
            };
        }
        match self.poll() {
            Ok(()) => result,
            Err(error) => {
                drop(result);
                // Dispose a cancelled candidate before the final boundary;
                // the sticky stop prevents any new user callback here.
                let _ = self.poll();
                Err(error.into())
            }
        }
    }
}
