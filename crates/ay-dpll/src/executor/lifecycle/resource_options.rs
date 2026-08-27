// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::Executor;

impl Executor {
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
    pub fn apply_rlimit_option(&mut self, numeral: &str) {
        if let Ok(budget) = numeral.parse::<u64>() {
            self.set_resource_limit((budget != 0).then_some(budget));
            if budget == 0 {
                self.set_ground_budget_enabled(false);
            }
        }
    }
}
