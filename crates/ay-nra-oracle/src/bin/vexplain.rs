// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adversarial verification harness: independent implication checks.
//!
//! Generates univariate conflicts, drives `oexplain_univariate`, and emits an
//! SMT2 script asking the reference z3 (nlsat, a completely different code path
//! from the `Z3_algebraic_*` C API the in-tree oracle uses) whether the cited
//! conjunction is unsatisfiable. A clause that is a theory consequence has an
//! unsatisfiable citation set; anything else is a wrong `unsat` in waiting.
//!
//! Root isolation here uses an independent square-free part, Sturm chain, and
//! exact-rational bisection. AY re-verifies the resulting root list.

use num_bigint::BigInt;
use num_rational::BigRational as Q;
use num_traits::{One, Signed, Zero};
use std::io::Write;

use ay_nra::oracle_api::{
    oexplain_clause_is_falsified, oexplain_clause_is_valid, oexplain_countermodel,
    oexplain_relevant_pairs, oexplain_univariate, OBq, OBqInterval, ODyadicAnum, OExplainLit,
    OISignCond,
};

include!("vexplain/polynomial.rs");
include!("vexplain/render.rs");
include!("vexplain/generator.rs");
include!("vexplain/runner.rs");
