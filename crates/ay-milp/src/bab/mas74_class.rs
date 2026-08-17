// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Measured two-instance class for the paired plunge and node-RC defaults.

use super::{mixed_model_gate, Model};

/// Whether `model` belongs to the measured mas74/mas76 class.
///
/// `!objective_is_integral` was the wrong exclusion: it armed gt2, which paid
/// 5,094 -> 45,535 nodes with these levers forced. `mixed_model_gate` excludes
/// gt2 (24 binary + 164 general integer) and flugpl while admitting mas76 (150
/// binary + one continuous). The 40-row cap completes the measured class.
///
/// Paired plunge and node reduced-cost fixing improved both members: mas76
/// fell from 808,361 to about 491,000 nodes, while mas74 improved its dual and
/// reached the exact known incumbent. Full DFS remains deliberately excluded:
/// it freezes mas74's global dual because both children leave the best-bound
/// heap; plunge instead parks one sibling and keeps the frontier honest.
pub(super) fn matches(model: &Model) -> bool {
    const ROW_CAP: usize = 40;
    !mixed_model_gate(model) && model.num_rows() <= ROW_CAP
}

/// Arm node-RC on the measured class unless the cheap route forbids it.
pub(super) fn node_rc_enabled(in_class: bool, cheap: bool) -> bool {
    // Plunge alone improved mas76 nodes by 24.1%; the paired RC fix reached
    // 39.3%. Outside this class it regressed blend2 and qnet1, so stay gated.
    super::node_rc_enabled() || (in_class && !cheap)
}
