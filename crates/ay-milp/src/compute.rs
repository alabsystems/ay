// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared process-bank ownership for the native MILP worker groups.
//! Planning widths are caps; only the retained caller/extra units run work.

use std::io;
use std::panic::{catch_unwind, AssertUnwindSafe};

use ay_sys::compute_budget::{ComputeScope, ExtraPermit};

pub(crate) struct Workers {
    extras: Vec<ExtraPermit>,
    // Last: return reserved extras before the caller's original unit.
    _caller: ComputeScope,
}

pub(crate) struct Run<R> {
    pub results: Vec<R>,
    pub spawn_failures: usize,
    pub panics: usize,
}

#[derive(Clone, Copy)]
pub(crate) enum Failure {
    Spawn,
    Panic,
}

impl Workers {
    pub(crate) fn acquire(
        requested: usize,
        stopped: impl FnMut() -> bool,
    ) -> io::Result<Option<Self>> {
        if requested == 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "zero MILP workers",
            ));
        }
        let Some(caller) = ComputeScope::enter_until(stopped)? else {
            return Ok(None);
        };
        let mut extras = Vec::new();
        for _ in 1..requested {
            match caller.try_extra()? {
                Some(permit) => extras.push(permit),
                None => break,
            }
        }
        Ok(Some(Self {
            extras,
            _caller: caller,
        }))
    }

    pub(crate) fn count(&self) -> usize {
        1 + self.extras.len()
    }

    /// The caller keeps this set through result merging. A worker's actual
    /// unit covers its owned inputs and capture cleanup, not just its result.
    /// `failed` must be idempotent: unwind notifies peers immediately, and the
    /// join path may repeat that notification while recording the failure.
    pub(crate) fn run<T: Send, R: Send>(
        &mut self,
        inputs: Vec<T>,
        name: &str,
        stack: Option<usize>,
        work: impl Fn(T) -> R + Sync,
        failed: impl Fn(Failure) + Sync,
    ) -> io::Result<Run<R>> {
        if inputs.len() != self.count() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "MILP worker input count",
            ));
        }
        let mut inputs = inputs.into_iter();
        let inline = inputs
            .next()
            .ok_or_else(|| io::Error::other("MILP caller input absent"))?;
        let extras = std::mem::take(&mut self.extras);
        Ok(std::thread::scope(|scope| {
            let mut report = Run {
                results: Vec::new(),
                spawn_failures: 0,
                panics: 0,
            };
            let mut handles = Vec::new();
            for (index, (input, permit)) in inputs.zip(extras).enumerate() {
                let mut builder = std::thread::Builder::new().name(format!("{name}-{}", index + 1));
                if let Some(stack) = stack {
                    builder = builder.stack_size(stack);
                }
                let work = &work;
                let failed = &failed;
                match builder.spawn_scoped(scope, move || {
                    permit.run(|| {
                        let _notify = NotifyPanic(failed);
                        work(input)
                    })
                }) {
                    Ok(handle) => handles.push(handle),
                    Err(_) => {
                        report.spawn_failures += 1;
                        failed(Failure::Spawn);
                    }
                }
            }
            match catch_unwind(AssertUnwindSafe(|| work(inline))) {
                Ok(result) => report.results.push(result),
                Err(_) => {
                    report.panics += 1;
                    failed(Failure::Panic);
                }
            }
            for handle in handles {
                match handle.join() {
                    Ok(Ok(result)) => report.results.push(result),
                    Ok(Err(_)) => {
                        report.spawn_failures += 1;
                        failed(Failure::Spawn);
                    }
                    Err(_) => {
                        report.panics += 1;
                        failed(Failure::Panic);
                    }
                }
            }
            report
        }))
    }
}

struct NotifyPanic<'a, F: Fn(Failure)>(&'a F);
impl<F: Fn(Failure)> Drop for NotifyPanic<'_, F> {
    fn drop(&mut self) {
        if std::thread::panicking() {
            (self.0)(Failure::Panic);
        }
    }
}

#[cfg(test)]
mod tests;
