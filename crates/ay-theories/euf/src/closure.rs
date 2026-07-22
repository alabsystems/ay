// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EUF congruence closure rebuilding.
//!
//! Delegates to the incremental E-graph rebuild in `egraph.rs`.
//! The legacy full-rebuild path was removed in #7948.

use crate::solver::EufSolver;

impl EufSolver<'_> {
    pub(crate) fn rebuild_closure(&mut self) {
        self.incremental_rebuild();
    }
}
