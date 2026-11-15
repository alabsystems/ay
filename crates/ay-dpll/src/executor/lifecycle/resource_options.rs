// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::time::Duration;

use super::Executor;

/// The value each resource option held before an SMT-LIB script first
/// overrode it, so `(reset)` can return it.
///
/// `:timeout`, `:rlimit`, `:max-memory` and `:random-seed` set the same
/// executor fields as the host's API setters and CLI flags. SMT-LIB `(reset)`
/// returns the solver to its INITIAL state, options included, and the initial
/// state is the host's configuration; `(reset)` used to keep every one of
/// these fields as host configuration, so a window's `(set-option :timeout 1)`
/// bounded every later window of a resident session. Measured on the round-4
/// build: `(set-option :timeout 1)`, `(reset)`, then a query a fresh process
/// answers `unsat` answered `unknown (timeout)`.
///
/// `None` in a slot means the script has not overridden that option since
/// the last reset, and the current value is the host's. Only the SMT-LIB
/// option paths write here; the host setters do not, so an API caller that
/// temporarily sets and restores a limit around one call never disturbs it.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(in crate::executor) struct ScriptOverriddenResourceOptions {
    timeout: Option<Option<Duration>>,
    resource_limit: Option<Option<u64>>,
    ground_budget_enabled: Option<bool>,
    memory_limit: Option<Option<usize>>,
    random_seed: Option<Option<u64>>,
}

impl ScriptOverriddenResourceOptions {
    /// Write the host values back over whatever the script left installed.
    pub(in crate::executor) fn restore_host_values(self, executor: &mut Executor) {
        let Self {
            timeout,
            resource_limit,
            ground_budget_enabled,
            memory_limit,
            random_seed,
        } = self;
        if let Some(timeout) = timeout {
            executor.timeout = timeout;
        }
        if let Some(resource_limit) = resource_limit {
            executor.resource_limit = resource_limit;
        }
        if let Some(ground_budget_enabled) = ground_budget_enabled {
            executor.ground_budget_enabled = ground_budget_enabled;
        }
        if let Some(memory_limit) = memory_limit {
            executor.memory_limit = memory_limit;
        }
        if let Some(random_seed) = random_seed {
            executor.random_seed = random_seed;
        }
    }
}

impl Executor {
    /// SMT-LIB `(set-option :timeout <ms>)`: a per-`check-sat` wall-clock
    /// deadline, `0` = none (Z3 convention). Script-set: `(reset)` restores the
    /// host's value.
    pub(in crate::executor) fn apply_timeout_option(&mut self, ms: u64) {
        let host = self.timeout;
        self.script_resource_options.timeout.get_or_insert(host);
        self.timeout = (ms != 0).then(|| Duration::from_millis(ms));
    }

    /// SMT-LIB `(set-option :max-memory <megabytes>)`, `0` = no limit.
    /// Script-set: `(reset)` restores the host's value.
    pub(in crate::executor) fn apply_max_memory_option(&mut self, megabytes: usize) {
        let host = self.memory_limit;
        self.script_resource_options
            .memory_limit
            .get_or_insert(host);
        let bytes = megabytes.saturating_mul(1024 * 1024);
        self.memory_limit = (bytes != 0).then_some(bytes);
    }

    /// SMT-LIB `(set-option :random-seed <n>)`. Script-set: `(reset)`
    /// restores the host's value.
    pub(in crate::executor) fn apply_random_seed_option(&mut self, seed: u64) {
        let host = self.random_seed;
        self.script_resource_options.random_seed.get_or_insert(host);
        self.random_seed = Some(seed);
    }

    /// Apply SMT-LIB `(set-option :rlimit <numeral>)` semantics (#8749):
    /// install the deterministic conflict budget. `0` means "no limit" per
    /// Z3 convention — and, since the default ground budget landed
    /// (#ground-determinism), `0` also disables that default so callers keep
    /// a true opt-out to unbounded solving. An unparseable numeral is
    /// ignored, matching the option handler's historical behaviour.
    ///
    /// This is the single source of truth for BOTH consumers of the option:
    /// the executor's own `SetOption` handler and the `ay` CLI transcript
    /// layer, which intercepts `:rlimit` for the z3-compat `get-option` echo
    /// and must forward the budget here (it used to parse-and-drop it —
    /// #8749 class). Keep them on this method; a hand-copied re-derivation
    /// of these semantics WILL drift.
    ///
    /// Script-set: `(reset)` restores the host's budget and ground-budget
    /// switch (see [`ScriptOverriddenResourceOptions`]).
    pub fn apply_rlimit_option(&mut self, numeral: &str) {
        if let Ok(budget) = numeral.parse::<u64>() {
            let host_limit = self.resource_limit;
            self.script_resource_options
                .resource_limit
                .get_or_insert(host_limit);
            self.resource_limit = (budget != 0).then_some(budget);
            if budget == 0 {
                let host_ground = self.ground_budget_enabled;
                self.script_resource_options
                    .ground_budget_enabled
                    .get_or_insert(host_ground);
                self.ground_budget_enabled = false;
            }
        }
    }
}
