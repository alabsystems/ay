// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{Instant, ProofCheckError};

#[derive(Clone, Copy)]
enum Stop {
    Resource,
    Cancelled,
}

impl Stop {
    fn error(self) -> ProofCheckError {
        match self {
            Self::Resource => ProofCheckError::ResourceLimit,
            Self::Cancelled => ProofCheckError::Cancelled,
        }
    }
}

pub(super) struct Control<'a> {
    deadline: Instant,
    progress: &'a mut dyn FnMut(usize, usize) -> bool,
    stopped: Option<Stop>,
}

impl<'a> Control<'a> {
    pub(super) fn new(
        deadline: Instant,
        progress: &'a mut dyn FnMut(usize, usize) -> bool,
    ) -> Self {
        Self {
            deadline,
            progress,
            stopped: None,
        }
    }

    pub(super) fn charge(&mut self, work: usize, bytes: usize) -> Result<(), ProofCheckError> {
        if let Some(stop) = self.stopped {
            return Err(stop.error());
        }
        if Instant::now() >= self.deadline {
            self.stopped = Some(Stop::Cancelled);
            return Err(ProofCheckError::Cancelled);
        }
        // A callback panic caught by a nested operation remains a refusal.
        self.stopped = Some(Stop::Resource);
        if !(self.progress)(work, bytes) {
            return Err(ProofCheckError::ResourceLimit);
        }
        self.stopped = None;
        if Instant::now() >= self.deadline {
            self.stopped = Some(Stop::Cancelled);
            return Err(ProofCheckError::Cancelled);
        }
        Ok(())
    }

    pub(super) fn poll(&mut self) -> Result<(), ProofCheckError> {
        self.charge(0, 0)
    }

    pub(super) fn finish<T>(
        &mut self,
        result: Result<T, ProofCheckError>,
    ) -> Result<T, ProofCheckError> {
        // Callers drop temporary owners before this boundary on both paths.
        match self.poll() {
            Ok(()) => result,
            Err(error) => {
                drop(result);
                let _ = self.poll();
                Err(error)
            }
        }
    }
}
