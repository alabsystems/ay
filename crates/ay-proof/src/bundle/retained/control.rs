// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) struct Control<'a> {
    deadline: Instant,
    progress: Progress<'a>,
    failure: Option<TransportError>,
    storage_limit: usize,
    work_limit: u64,
    pub(super) usage: TransportUsage,
}

impl Control<'_> {
    pub(super) fn fail<T>(&mut self, error: TransportError) -> Result<T, TransportError> {
        Err(*self.failure.get_or_insert(error))
    }

    pub(super) fn charge(&mut self, work: usize, bytes: usize) -> Result<(), TransportError> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        if Instant::now() >= self.deadline {
            return self.fail(TransportError::Deadline);
        }
        self.usage.charged_work = self
            .usage
            .charged_work
            .checked_add(work)
            .ok_or(TransportError::Overflow)
            .or_else(|e| self.fail(e))?;
        self.usage.charged_bytes = self
            .usage
            .charged_bytes
            .checked_add(bytes)
            .ok_or(TransportError::Overflow)
            .or_else(|e| self.fail(e))?;
        let work_limit = usize::try_from(self.work_limit).unwrap_or(usize::MAX);
        self.cap("transport work", self.usage.charged_work, work_limit)?;
        self.cap(
            "new transport bytes",
            self.usage.charged_bytes,
            self.storage_limit,
        )?;
        self.failure = Some(TransportError::Refused);
        if !(self.progress)(work, bytes) {
            return Err(TransportError::Refused);
        }
        self.failure = None;
        if Instant::now() >= self.deadline {
            return self.fail(TransportError::Deadline);
        }
        Ok(())
    }

    pub(super) fn finish(&mut self) -> Result<(), TransportError> {
        if let Some(error @ (TransportError::Refused | TransportError::Deadline)) = self.failure {
            return Err(error);
        }
        if Instant::now() >= self.deadline {
            self.failure = Some(TransportError::Deadline);
            return Err(TransportError::Deadline);
        }
        let prior = self.failure;
        self.failure = Some(TransportError::Refused);
        if !(self.progress)(0, 0) {
            return Err(TransportError::Refused);
        }
        self.failure = prior;
        if Instant::now() >= self.deadline {
            self.failure = Some(TransportError::Deadline);
        }
        self.failure.map_or(Ok(()), Err)
    }

    pub(super) fn cap(
        &mut self,
        resource: &'static str,
        actual: usize,
        limit: usize,
    ) -> Result<(), TransportError> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        if actual > limit {
            self.fail(TransportError::Limit {
                resource,
                limit,
                actual,
            })
        } else {
            Ok(())
        }
    }

    pub(super) fn constrain(&mut self, work: u64, bytes: usize) -> Result<(), TransportError> {
        self.work_limit = self.work_limit.min(work);
        self.storage_limit = self.storage_limit.min(bytes);
        self.cap(
            "new transport bytes",
            self.usage.charged_bytes,
            self.storage_limit,
        )
    }

    pub(super) fn product(&mut self, a: usize, b: usize) -> Result<usize, TransportError> {
        a.checked_mul(b)
            .ok_or(TransportError::Overflow)
            .or_else(|e| self.fail(e))
    }

    pub(super) fn add(&mut self, a: usize, b: usize) -> Result<usize, TransportError> {
        a.checked_add(b)
            .ok_or(TransportError::Overflow)
            .or_else(|e| self.fail(e))
    }

    /// The caller supplies an empty Vec: one allocation, no moving old buffer.
    pub(super) fn vector<T>(&mut self, count: usize) -> Result<Vec<T>, TransportError> {
        let bytes = self.product(count, size_of::<T>())?;
        self.charge(0, bytes)?;
        let mut out = Vec::new();
        out.try_reserve_exact(count)
            .map_err(|_| TransportError::Allocation)
            .or_else(|e| self.fail(e))?;
        let actual = self.product(out.capacity(), size_of::<T>())?;
        // Allocator excess is checked before publishing/copying. Like the
        // private codec, this is logical admission, not an allocator RSS bound.
        self.charge(0, actual - bytes)?;
        Ok(out)
    }

    pub(super) fn copied_bytes(&mut self, bytes: &[u8]) -> Result<Vec<u8>, TransportError> {
        let mut output = self.vector(bytes.len())?;
        for chunk in bytes.chunks(lexical::WINDOW) {
            self.charge(chunk.len(), 0)?;
            output.extend_from_slice(chunk);
        }
        Ok(output)
    }
}

pub(super) fn run<T>(
    deadline: Instant,
    progress: Progress<'_>,
    operation: impl FnOnce(&mut Control<'_>) -> Result<T, TransportError>,
) -> TransportOutcome<T> {
    run_observed(deadline, progress, &mut None, operation)
}

// Observe the existing first failure BEFORE unchanged terminal-error precedence.
pub(super) fn run_observed<T>(
    deadline: Instant,
    progress: Progress<'_>,
    first: &mut Option<TransportError>,
    operation: impl FnOnce(&mut Control<'_>) -> Result<T, TransportError>,
) -> TransportOutcome<T> {
    let mut control = Control {
        deadline,
        progress,
        failure: None,
        storage_limit: usize::MAX,
        work_limit: u64::MAX,
        usage: TransportUsage::default(),
    };
    let result = control.charge(0, 0).and_then(|()| operation(&mut control));
    if let Some(error) = control.failure.or_else(|| result.as_ref().err().copied()) {
        first.get_or_insert(error);
    }
    let result = match result {
        Err(error) => {
            let _ = control.fail::<()>(error);
            control.usage.returned_owned_bytes = 0;
            match control.finish() {
                Err(error) => Err(error),
                Ok(()) => Err(error),
            }
        }
        Ok(value) => match control.finish() {
            Ok(()) => Ok(value),
            Err(error) => {
                drop(value);
                control.usage.returned_owned_bytes = 0;
                let _ = control.finish();
                Err(error)
            }
        },
    };
    if let Err(error) = &result {
        first.get_or_insert(*error);
    }
    TransportOutcome {
        result,
        #[cfg(test)]
        usage: control.usage,
    }
}

#[cfg(test)]
mod tests;
