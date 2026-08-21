// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Textually included by `solve_ab_switches` to preserve method visibility.

#[cfg(test)]
impl SolveAbSwitches {
    pub(super) fn b33_opt_outs(&self) -> [bool; 6] {
        [
            self.chc_no_array_relational,
            self.chc_no_array_relational_v2,
            self.chc_no_dt_bmc,
            self.chc_no_qual_mine,
            self.chc_no_qual_mixed,
            self.sat_no_factor_dense_init,
        ]
    }
}
