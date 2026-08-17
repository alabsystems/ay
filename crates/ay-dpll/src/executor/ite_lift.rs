// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kill-switch for eager linear definitional ITE lifting (#ite-lift).
//!
//! The default arithmetic ITE elimination is Shannon expansion
//! (`TermStore::lift_arithmetic_ite_all`): it distributes a predicate over its
//! ITE arguments, e.g. `(<= (ite c a b) x)` → `(ite c (<= a x) (<= b x))`. On
//! *chained* min-selection ITEs compared by ordering atoms
//! (`(<= min_i min_j)`, where each `min_k` is a depth-`k` ITE chain), Shannon
//! produces a deep Boolean-ITE tree with `k_i * k_j` leaf comparison atoms per
//! ordering atom; the DPLL(T) core then case-splits combinatorially over the
//! shared ITE conditions. Measured: the ADT-LIA wide-sortedness AllSAT queries
//! (`sort_BubSortSorts` &co.) explode to >60s with no verdict where z3 answers
//! in ~100ms via ITE-term lifting.
//!
//! When enabled, this switch instead applies the LINEAR definitional encoding
//! (`TermStore::name_non_bool_ites_all`): every distinct term-level ITE
//! `(ite c t e)` is named by a fresh variable `v` with guard clauses
//! `(or (not c) (= v t))` and `(or c (= v e))`, and every occurrence is
//! replaced by `v`. Each ITE condition becomes a SINGLE shared Boolean
//! decision variable (decided once by the SAT layer, propagated into the
//! theory through the guards) rather than being re-expanded inside every
//! ordering atom — exactly z3's ITE-lifting strategy. The encoding is
//! equisatisfiable (every model of the original extends to `v` by evaluating
//! its ITE; every model of the extension satisfies the original after
//! substituting the definitions back), so verdicts carry over in both
//! directions.
//!
//! Default OFF: with the switch off, no definitional naming runs here and all
//! preprocessing is byte-identical to the pre-feature behavior.

use std::sync::OnceLock;

/// True when `--dpll-ite-lift` (or `true`, case-insensitive).
pub(crate) fn ite_lift_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| ay_core::misc_cli_flags().dpll_ite_lift)
}
