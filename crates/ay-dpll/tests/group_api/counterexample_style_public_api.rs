// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_dpll::{CounterexampleStyle, Executor};

#[test]
fn counterexample_style_is_publicly_importable() {
    let mut executor = Executor::new();
    executor.set_counterexample_style(CounterexampleStyle::Minimal);
}
