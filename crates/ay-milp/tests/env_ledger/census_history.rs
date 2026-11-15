// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

pub(super) fn assert_census_matches_survey(total: usize, dead: usize) {
    // Count history: census_history.md, then `git log -p` for this file.
    assert_eq!(total, 19, "AY_* name count moved");
    assert_eq!(dead, 11, "dead-knob count moved");
}
