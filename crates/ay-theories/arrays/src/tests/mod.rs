// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::assert_conflict_soundness;
use ay_core::Sort;

mod core_solver;
mod store_chain;
mod store_target_8785;
mod verification;
mod weak_equiv;

fn make_array_sort() -> Sort {
    Sort::array(Sort::Int, Sort::Int)
}
