// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Advanced solver tests: differential soundness boundary, cycle detection
//! regression, int conversion, SMT-LIB 2.6 extensions (replace_re, to_lower,
//! to_upper, re.power, str ordering, str.is_digit).

use super::*;

mod algorithm_audit;
mod cycle_detection;
mod extf_and_int;
mod inequality_and_audit;
mod ordering_and_digit;
mod smtlib26_ops;
mod soundness_boundary;
