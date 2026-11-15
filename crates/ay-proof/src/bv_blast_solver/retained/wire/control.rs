// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy)]
pub(super) enum Item {
    Row,
    Literal,
    Hint,
}

pub(super) struct Control<'a> {
    pub(super) limits: WireLimits,
    pub(super) usage: WireUsage,
    pub(super) storage: usize,
    failure: Option<WireError>,
    counts: [usize; 3],
    poll: &'a mut dyn FnMut() -> bool,
}

impl<'a> Control<'a> {
    pub(super) fn new(limits: WireLimits, poll: &'a mut dyn FnMut() -> bool) -> Self {
        Self {
            limits,
            usage: WireUsage::default(),
            storage: 0,
            failure: None,
            counts: [0; 3],
            poll,
        }
    }

    pub(super) fn fail<T>(&mut self, error: WireError) -> Result<T, WireError> {
        Err(*self.failure.get_or_insert(error))
    }

    pub(super) fn status(&self) -> Result<(), WireError> {
        self.failure.map_or(Ok(()), Err)
    }

    pub(super) fn poll(&mut self) -> Result<(), WireError> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        if Instant::now() >= self.limits.deadline {
            return self.fail(WireError::Deadline);
        }
        // Pre-latch: even a caught callback panic cannot revive this control.
        self.failure = Some(WireError::Cancelled);
        if !(self.poll)() {
            return Err(WireError::Cancelled);
        }
        self.failure = None;
        if Instant::now() >= self.limits.deadline {
            return self.fail(WireError::Deadline);
        }
        Ok(())
    }

    /// Observe the caller after operation-owned cleanup, even if a non-stop
    /// refusal was already recorded. This never clears that refusal or grants
    /// more work; an external stop takes precedence over it. An observed stop
    /// is terminal and must not call a possibly reset callback again.
    pub(super) fn finish(&mut self) -> Result<(), WireError> {
        if matches!(
            self.failure,
            Some(WireError::Cancelled | WireError::Deadline)
        ) {
            return self.status();
        }
        if Instant::now() >= self.limits.deadline {
            self.failure = Some(WireError::Deadline);
            return self.status();
        }
        let prior = self.failure;
        // Keep caught callback unwinds terminal, just as at ordinary polls.
        self.failure = Some(WireError::Cancelled);
        if !(self.poll)() {
            return self.status();
        }
        self.failure = prior;
        if Instant::now() >= self.limits.deadline {
            self.failure = Some(WireError::Deadline);
        }
        self.status()
    }

    pub(super) fn charge(&mut self, work: usize) -> Result<(), WireError> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        self.usage.charged_work = match self.usage.charged_work.checked_add(work as u128) {
            Some(total) => total,
            None => return self.fail(WireError::Overflow),
        };
        self.cap(
            "work",
            self.usage.charged_work,
            self.limits.max_work as u128,
        )?;
        self.poll()
    }

    pub(super) fn cap(
        &mut self,
        resource: &'static str,
        actual: u128,
        limit: u128,
    ) -> Result<(), WireError> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        if actual > limit {
            self.fail(WireError::Limit {
                resource,
                limit,
                actual,
            })
        } else {
            Ok(())
        }
    }

    pub(super) fn item(&mut self, item: Item) -> Result<usize, WireError> {
        self.charge(1)?;
        let (index, name, limit) = match item {
            Item::Row => (0, "rows", self.limits.max_rows),
            Item::Literal => (1, "literals", self.limits.max_literals),
            Item::Hint => (2, "hints", self.limits.max_hints),
        };
        self.counts[index] = self.add(self.counts[index], 1)?;
        self.cap(name, self.counts[index] as u128, limit as u128)?;
        Ok(limit)
    }

    pub(super) fn add(&mut self, a: usize, b: usize) -> Result<usize, WireError> {
        a.checked_add(b)
            .ok_or(WireError::Overflow)
            .or_else(|e| self.fail(e))
    }

    pub(super) fn product(&mut self, a: usize, b: usize) -> Result<usize, WireError> {
        a.checked_mul(b)
            .ok_or(WireError::Overflow)
            .or_else(|e| self.fail(e))
    }

    fn peak(&mut self, bytes: usize) -> Result<(), WireError> {
        self.usage.peak_storage_bytes = self.usage.peak_storage_bytes.max(bytes);
        self.cap(
            "storage bytes",
            bytes as u128,
            self.limits.max_storage_bytes as u128,
        )
    }

    pub(super) fn retain(&mut self, bytes: usize) -> Result<(), WireError> {
        self.storage = self.add(self.storage, bytes)?;
        self.peak(self.storage)
    }

    pub(super) fn reserve<T>(
        &mut self,
        output: &mut Vec<T>,
        target: usize,
    ) -> Result<(), WireError> {
        if target <= output.capacity() {
            return self.poll();
        }
        // A moving reallocation may retain the complete old buffer while the
        // new buffer is allocated. Charge copies and admit that overlap first.
        self.charge(output.len())?;
        let requested = self.product(target, size_of::<T>())?;
        let peak = self.add(self.storage, requested)?;
        self.peak(peak)?;
        let old = self.product(output.capacity(), size_of::<T>())?;
        output
            .try_reserve_exact(target - output.len())
            .map_err(|_| WireError::Allocation)
            .or_else(|e| self.fail(e))?;
        let actual = self.product(output.capacity(), size_of::<T>())?;
        let actual_peak = self.add(self.storage, actual)?;
        self.peak(actual_peak)?;
        self.storage = self.add(self.storage - old, actual)?;
        self.poll()
    }

    pub(super) fn slot<T>(&mut self, output: &mut Vec<T>, limit: usize) -> Result<(), WireError> {
        if output.len() < output.capacity() {
            return Ok(());
        }
        let needed = self.add(output.len(), 1)?;
        let doubled = self.product(output.capacity(), 2)?;
        self.reserve(output, needed.max(doubled).min(limit))
    }

    pub(super) fn serde_error(&mut self) -> WireError {
        *self.failure.get_or_insert(WireError::InvalidJson)
    }
}

pub(super) fn de_result<T, E: serde::de::Error>(result: Result<T, WireError>) -> Result<T, E> {
    result.map_err(|_| E::custom("retained wire refused"))
}
