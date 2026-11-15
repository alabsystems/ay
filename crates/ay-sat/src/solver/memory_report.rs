// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-mem-probe`: the solver's largest structures by retained capacity.

use super::*;
use std::mem::size_of;

impl Solver {
    /// `--sat-mem-probe` diagnostic: the solver's largest structures by
    /// retained capacity (MiB), to set against the process's resident size.
    pub fn memory_report(&self) -> String {
        let mib = |bytes: usize| bytes >> 20;
        let var_arrays = self.vals.capacity()
            + self.var_data.capacity() * size_of::<VarData>()
            + self.phase.capacity()
            + self.target_phase.capacity()
            + self.best_phase.capacity();
        format!(
            "vars={} clauses={} arena={} watches={} ledger={} reason_marks={} clause_ids={} \
             ids_disabled={} var_arrays={} trail={}",
            self.num_vars,
            self.arena.num_clauses(),
            mib(self.arena.memory_bytes()),
            mib(self.watches.heap_bytes()),
            mib(self.cold.original_ledger.heap_bytes()),
            mib(self.reason_clause_marks.capacity() * size_of::<u32>()),
            mib(self.cold.clause_ids.capacity() * size_of::<u64>()),
            self.cold.clause_ids_disabled,
            mib(var_arrays),
            mib(self.trail.capacity() * size_of::<Literal>()),
        )
    }
}
