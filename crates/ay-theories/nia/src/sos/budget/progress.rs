// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One sticky caller stop shared by translation, search and independent replay.

use std::cell::Cell;
use std::fmt;

pub(crate) struct SosProgress<'a> {
    callback: &'a dyn Fn() -> bool,
    refused: Cell<bool>,
}

impl fmt::Debug for SosProgress<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SosProgress")
            .field("refused", &self.refused)
            .finish()
    }
}

impl<'a> SosProgress<'a> {
    pub(crate) fn new(callback: &'a dyn Fn() -> bool) -> Self {
        Self {
            callback,
            refused: Cell::new(false),
        }
    }

    pub(crate) fn poll(&self) -> bool {
        if !self.refused.get() && !(self.callback)() {
            self.refused.set(true);
        }
        !self.refused.get()
    }
}

trait ProgressSink: fmt::Debug {
    fn poll(&self) -> bool;
}

impl ProgressSink for SosProgress<'_> {
    fn poll(&self) -> bool {
        self.poll()
    }
}

/// Erase the callback lifetime while borrowing its one shared sticky state.
#[derive(Debug, Default)]
pub(super) struct ProgressHandle<'a>(Option<&'a dyn ProgressSink>);

impl<'a> ProgressHandle<'a> {
    pub(super) fn new(progress: &'a SosProgress<'_>) -> Self {
        Self(Some(progress))
    }

    pub(super) fn poll(&self) -> bool {
        self.0.is_none_or(|progress| progress.poll())
    }
}

#[cfg(test)]
mod tests;
