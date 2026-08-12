// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Executor tests - split from executor.rs
//!
//! Module organization:
//! - `core`: Basic executor functionality (sat/unsat, push/pop)
//! - `model`: get-model, get-value, validate-model tests
//! - `commands`: SMT-LIB commands (info, options, assertions, proofs)
//! - `simplify`: Term simplification tests
//! - `smt`: SMT theory tests (arrays, LRA, LIA, UF)
//! - `strings`: String theory tests (QF_S, QF_SLIA) (#6356)
//! - `seq`: Sequence theory tests (QF_SEQ, QF_SEQLIA) (#6486)
//! - `bv`: Bitvector theory tests (QF_BV, QF_ABV, QF_UFBV, QF_AUFBV)
//! - `fp`: Floating-point theory tests (QF_FP, QF_FPLRA) (#8456)
//! - `incremental`: Incremental solving tests
//! - `quantifier`: Quantifier instantiation tests (CEGQI)
//! - `regression`: Soundness regression tests
//! - `array_soundness`: QF_AX wrong-answer regressions (#4304)
//! - `qflia_differential_fuzz`: single-shot QF_LIA differential fuzzer
//!   (seed-236 false-UNSAT family)
//! - `reserved_name_capture`: end-to-end verdict guards for the reserved-name
//!   gates (`map[...]` array-map capture, qualified-`(as …)` path spellings)

mod abvfp_flatten;
mod array_soundness;
mod bv;
mod commands;
mod core;
mod dt_ite_ctor_payload;
mod fp;
mod guarded_vacuous_array_reads;
mod incremental;
mod lra_assumption_tight_equality;
mod lra_inc_engine_soundness;
mod lra_lazy_session;
mod lra_opt_certificates;
mod map;
mod model;
mod model_roundtrip;
mod multiset;
mod mv_printer;
mod no_fabricated_values;
mod optimization;
mod partition_rescue;
mod qflia_differential_fuzz;
mod quantifier;
mod regression;
mod reserved_name_capture;
mod seq;
mod set;
mod simplify;
mod smt;
mod strings;
mod strings_word_eq;
