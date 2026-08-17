// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! AY Core - Common types and traits for the AY SMT solver
//!
//! This crate provides the foundational types shared across all AY components:
//! - Term representation (hash-consed DAG)
//! - Sort system (type checking)
//! - Theory trait (interface for theory solvers)
//! - Proof types (resolution proofs, theory lemmas)
//! - Tseitin transformation (Boolean to CNF)
//!
//! # Type Hierarchy
//!
//! AY has multiple Sort types at different layers. This crate provides the
//! canonical internal representation:
//!
//! ```text
//! ay_core::Sort (canonical internal representation)
//!     ↕ From impls
//! ay_chc::ChcSort (CHC expression types — bidirectional From<CoreSort>)
//!
//! ay_dpll::api::Sort (re-export of ay_core::Sort — same type)
//!
//! ay_frontend::Sort (parser AST — separate, string-based, no From conversion)
//! ```
//!
//! When consuming AY:
//! - Use `ay::Sort` (re-exported from ay-dpll) for the native Rust API
//! - `ay_core::Sort` is the internal canonical type
//! - `ay_frontend::Sort` is only for parsing SMT-LIB files
//!
//! Bidirectional `From` implementations exist between `ay_core::Sort` and
//! `ay_chc::ChcSort`. The dpll Sort is a direct re-export (same type).

#![warn(missing_docs)]
#![warn(clippy::all)]

pub(crate) mod alethe;
pub mod debug_channel;
pub mod forgone;
pub mod kani_compat;
pub(crate) mod math;
pub mod memory_pressure;
pub mod nonlinear;
pub mod panic_utils;
pub(crate) mod proof;
pub mod proof_validation;
pub(crate) mod smtlib;
pub(crate) mod sort;
pub mod term;
pub(crate) mod theory;
pub mod time;
pub(crate) mod tseitin;
pub mod verification;

pub use debug_channel::{
    chc_debug_env_flags, claim_trace_file, debug_channel_active, misc_cli_flags,
    misc_test_override, release_trace_file, sat_ab_switches, sat_debug_env_flags,
    sat_disable_flags, set_global_chc_debug_env_flags, set_global_debug_config,
    set_global_misc_cli_flags, set_global_sat_ab_switches, set_global_sat_debug_env_flags,
    set_global_sat_disable_flags, set_global_theory_disable_flags, set_global_trace_config,
    set_global_trace_path_cache, theory_disable_flags, trace_config, trace_file_available,
    trace_path_cache, ChcDebugEnvFlags, DebugChannel, DebugConfig, MiscCliFlags, ProofFormat,
    SatAbSwitches, SatDebugEnvFlags, SatDisableFlags, TheoryDisableFlags, TraceConfig,
    TracePathCache,
};
pub use math::extended_gcd_bigint;
pub use memory_pressure::{
    Band, BandThresholds, MemoryPressure, MemorySource, MockSource, PressureObserver, SystemSource,
    UnknownReason,
};
pub use proof::{
    alethe_rule_requires_premises_or_args, is_checkable_alethe_rule, wire_rule_name, AletheRule,
    BvGateType, CuttingPlaneAnnotation, FarkasAnnotation, FpOp, LiaAnnotation, Proof, ProofId,
    ProofStep, TheoryLemmaKind, TheoryLemmaProof, CHECKABLE_ALETHE_RULES, UNPROVED_STEP_RULE,
};
pub use smtlib::{
    escape_string_contents, quote_symbol, string_literal, unescape_string_contents,
    StringDecodeError, SMTLIB_MAX_CODE_POINT,
};
pub use sort::{ArraySort, BitVecSort, DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
pub use term::{Constant, RationalWrapper, SkolemChoice, Symbol, TermData, TermId, TermStore};
pub use theory::{
    assert_conflict_soundness, BoundRefinementRequest, DiscoveredDisequality, DiscoveredEquality,
    DisequalitySplitRequest, EqualityPropagationResult, ExpressionSplitRequest,
    ModelEqualityRequest, NativeTheoryPropagationBackend, NativeTheoryPropagationProfile,
    SplitRequest, StringLemma, StringLemmaKind, TheoryConflict, TheoryLemma, TheoryLit,
    TheoryPropagation, TheoryResult, TheorySolver,
};
pub use tseitin::{
    ClausificationProof, CnfClause, CnfLit, Tseitin, TseitinEncodedAssertion, TseitinResult,
    TseitinState,
};
pub use verification::{
    VerificationBoundary, VerificationEvidenceKind, VerificationFailure, VerificationVerdict,
};

pub use panic_utils::{catch_ay_panics, is_ay_panic_reason, panic_payload_to_string};

/// Write to stderr without panicking on broken pipe.
///
/// Unlike `eprintln!`, this macro silently ignores write errors (e.g., broken
/// pipe when stderr is redirected). This is important for solver diagnostics
/// that should never cause a panic.
#[macro_export]
macro_rules! safe_eprintln {
    ($($arg:tt)*) => {{
        use std::io::Write;
        let _ = writeln!(std::io::stderr(), $($arg)*);
    }};
}

/// Create a cached environment-variable-based boolean flag.
///
/// The flag value is read once from the environment on first access and
/// cached for the process lifetime via `OnceLock`. Uses `var_os().is_some()`
/// for consistency: the flag is active when the env var is present,
/// regardless of its value or UTF-8 validity.
///
/// # Usage
///
/// ```rust
/// use ay_core::cached_env_flag;
///
/// // Private function (default)
/// cached_env_flag!(debug_foo, "AY_DEBUG_FOO");
///
/// // With explicit visibility
/// cached_env_flag!(pub(crate) debug_bar, "AY_DEBUG_BAR");
///
/// let _: fn() -> bool = debug_foo;
/// let _: fn() -> bool = debug_bar;
/// ```
///
/// Centralizes the pattern previously duplicated across ay-dpll and ay-chc
/// (see issue #3908).
#[macro_export]
macro_rules! cached_env_flag {
    ($vis:vis $name:ident, $env_var:literal) => {
        #[inline]
        $vis fn $name() -> bool {
            static CACHE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            *CACHE.get_or_init(|| std::env::var_os($env_var).is_some())
        }
    };
}

/// Create a cached [`DebugChannel`](crate::DebugChannel) activation check.
///
/// Resolves through [`debug_channel_active`](crate::debug_channel_active) (the
/// CLI-aware path that falls back to `AY_DEBUG_*` env vars) on first call and
/// caches the result in a process-local `OnceLock`. Subsequent calls return
/// the cached boolean with no global-config or env lookups.
///
/// Prefer this over `cached_env_flag!` for tracing flags so the CLI
/// `--debug <channel>` migration (#8506 / #8726) is honored. `cached_env_flag!`
/// remains for purely env-var-only toggles that have no `DebugChannel` variant.
///
/// # Usage
///
/// ```rust
/// use ay_core::{cached_debug_channel, DebugChannel};
///
/// // Private function (default)
/// cached_debug_channel!(debug_lra, DebugChannel::Lra);
///
/// // With explicit visibility
/// cached_debug_channel!(pub(crate) debug_gomory, DebugChannel::Gomory);
///
/// let _: fn() -> bool = debug_lra;
/// let _: fn() -> bool = debug_gomory;
/// ```
///
/// Centralizes the `OnceLock<bool>` + `debug_channel_active(...)` pattern that
/// was duplicated across six LRA files (#8858) and matches the existing
/// duplicate-reduction pattern for `AY_DEBUG_*` env vars (#3908).
#[macro_export]
macro_rules! cached_debug_channel {
    ($vis:vis $name:ident, $channel:expr) => {
        #[inline]
        $vis fn $name() -> bool {
            static CACHE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            *CACHE.get_or_init(|| $crate::debug_channel_active($channel))
        }
    };
}

/// Unwrap a `Not` wrapper from a literal, flipping the boolean value.
///
/// Theory solvers receive literals as `(TermId, bool)` pairs where the term
/// may be `Not(inner)`. This strips one layer of negation and flips the value,
/// returning the inner atom and its effective polarity.
pub fn unwrap_not(terms: &TermStore, literal: TermId, value: bool) -> (TermId, bool) {
    match terms.get(literal) {
        TermData::Not(inner) => (*inner, !value),
        _ => (literal, value),
    }
}

/// Decode the canonical Bool-equality biconditional introduced by `TermStore::mk_eq`.
///
/// Bool-sorted equalities are normalized in `ay-core` to `ite(lhs, rhs, not(rhs))`
/// (#3421). Consumers that need equality semantics on the canonicalized term
/// can use this helper to recover the original `(lhs, rhs)` pair.
pub fn decode_bool_biconditional_eq(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::Ite(lhs, rhs, else_term) if terms.sort(term) == &Sort::Bool => {
            match terms.get(*else_term) {
                TermData::Not(inner) if *inner == *rhs => Some((*lhs, *rhs)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Determine whether a term should be communicated to the theory solver.
///
/// DPLL(T) theory solvers should only see *atomic* Boolean predicates (e.g., `x <= 5`,
/// `f(a) = b`, `select(a,i) = v`) and should not be asked to interpret Boolean structure
/// like `and/or/xor/=>/ite`.
///
/// This is the single source of truth for theory-atom routing, used by both
/// ay-dpll and ay-chc. See #6881 for the consolidation rationale.
pub fn is_theory_atom(terms: &TermStore, term: TermId) -> bool {
    if terms.sort(term) != &Sort::Bool {
        return false;
    }

    match terms.get(term) {
        TermData::Const(Constant::Bool(_)) => false,
        TermData::Const(_) => false,
        TermData::Var(_, _) => false,
        TermData::Not(_) => false,
        TermData::Ite(_, _, _) => decode_bool_biconditional_eq(terms, term).is_some(),
        TermData::Let(_, _) => false,
        TermData::App(Symbol::Named(name), _args) => match name.as_str() {
            "and" | "or" | "xor" | "=>" => false,
            "=" => true,
            _ => true,
        },
        TermData::App(_, _) => true,
        // Quantifiers are theory literals (handled by E-matching)
        TermData::Forall(..) | TermData::Exists(..) => true,
    }
}

/// Propagate pairwise equalities for variables with identical tight bounds.
///
/// Given a list of `(term, value, reasons)` triples where each variable has
/// tight bounds (lower == upper, non-strict), groups variables by value and
/// propagates equalities between all pairs in each group. Used by both LRA
/// and LIA Nelson-Oppen equality propagation.
///
/// Deduplicates against `propagated_pairs` to avoid re-propagating equalities
/// that were already sent in prior calls (e.g., after push/pop).
///
/// SOUNDNESS (#cross-sort-alias wrong-UNSAT, AUFLIRA 2026-07): pairs whose
/// terms have DIFFERENT sorts are never emitted. Value-based grouping is
/// sort-blind, and in a mixed Int/Real problem an Int constant and a
/// Real-sorted UF application can share a numeric value (`5` and
/// `(f 3) = 5.0`) while an equality between them is ill-sorted — merging
/// their EUF classes puts `Int(5)` and `Rational(5)` in one class, and the
/// constant-conflict check then "refutes" the innocent ground fact
/// `(= (f 3) 5.0)` as the sole reason: a false conflict that surfaced as a
/// wrong UNSAT on satisfiable quantified AUFLIRA inputs. A cross-sort
/// equality is not expressible in well-sorted SMT-LIB, so skipping it can
/// never lose a sound refutation.
pub fn propagate_tight_bound_equalities(
    terms: &TermStore,
    tight_bound_vars: Vec<(TermId, num_rational::BigRational, Vec<TheoryLit>)>,
    propagated_pairs: &mut kani_compat::DetHashSet<(TermId, TermId)>,
) -> Vec<DiscoveredEquality> {
    use kani_compat::DetHashMap as HashMap;

    // Group variables by their value
    let mut vars_by_value: HashMap<num_rational::BigRational, Vec<(TermId, Vec<TheoryLit>)>> =
        Default::default();
    for (term, value, reasons) in tight_bound_vars {
        vars_by_value
            .entry(value)
            .or_insert_with(Vec::new)
            .push((term, reasons));
    }

    // Sort groups by value for deterministic iteration (#2681)
    let mut sorted_groups: Vec<_> = vars_by_value.iter().collect();
    sorted_groups.sort_by_key(|(a, _)| *a);

    let mut equalities = Vec::new();

    for (_value, vars) in sorted_groups {
        if vars.len() < 2 {
            continue;
        }

        // Propagate pairwise equalities between all variables with same value
        for i in 0..vars.len() {
            for j in (i + 1)..vars.len() {
                let (lhs, lhs_reasons) = &vars[i];
                let (rhs, rhs_reasons) = &vars[j];

                // Cross-sort pairs are ill-sorted — see doc comment (SOUNDNESS).
                if terms.sort(*lhs) != terms.sort(*rhs) {
                    continue;
                }

                // Canonicalize the pair to avoid duplicate propagations
                let pair = if lhs.0 < rhs.0 {
                    (*lhs, *rhs)
                } else {
                    (*rhs, *lhs)
                };

                if !propagated_pairs.contains(&pair) {
                    propagated_pairs.insert(pair);

                    // Combine reasons from both variables
                    let mut combined_reasons = lhs_reasons.clone();
                    for r in rhs_reasons {
                        if !combined_reasons.contains(r) {
                            combined_reasons.push(*r);
                        }
                    }

                    equalities.push(DiscoveredEquality::new(*lhs, *rhs, combined_reasons));
                }
            }
        }
    }

    equalities
}

#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;
