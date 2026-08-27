// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Producer hints for context-dependent datatype clauses.

use ay_core::TermId;

use crate::executor::Executor;

impl Executor {
    /// Record that `premises` entail `clause` for independent reconstruction.
    /// The bounded sink silently declines overflow and degenerate records.
    pub(crate) fn record_dt_context_conflict(
        &mut self,
        clause: Vec<TermId>,
        premises: Vec<TermId>,
    ) {
        self.dt_context_conflict_records.record(clause, premises);
    }
}
