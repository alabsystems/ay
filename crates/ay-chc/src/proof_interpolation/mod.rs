// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof/Farkas-certificate-based Craig interpolation for CHC solving.
//!
//! This module extracts interpolants from arithmetic UNSAT certificates (Farkas coefficients).
//! It is intended for PDR/Spacer-style lemma learning: when `A ∧ B` is UNSAT, produce an
//! interpolant `I` such that:
//! - `A ⊨ I`
//! - `I ∧ B` is UNSAT
//! - `I` mentions only shared variables.
//!
//! Today, ay-chc does not have a full SAT+theory proof object. Instead, we rely on the LIA
//! solver to return an UNSAT conflict annotated with Farkas coefficients, and we model that as a
//! single theory-lemma proof step to reuse proof-oriented extraction logic.
//!
//! Submodules:
//! - `farkas`: proof-based Farkas interpolant extraction
//! - `fourier_motzkin`: FM variable elimination
//! - `lia_farkas`: standalone LIA Farkas interpolation
//! - `linear`: linear constraint arithmetic
//! - `projection`: MBP projection helpers
//! - `proof_marking`: proof node classification
//! - `proof_traversal`: proof DAG traversal
//! - `smt_history`: SMT Farkas history orchestrator + precomputed extraction
//! - `strategies`: interpolation strategy implementations
//! - `zero_farkas`: zero-Farkas fallback pipeline

use crate::farkas::{parse_linear_constraint, LinearConstraint};
use crate::farkas_decomposition::decomposed_farkas_interpolant;
use crate::iuc_solver::{IucResult, IucSolver};
use crate::smt::{
    is_theory_atom, FarkasConflict, Partition, SmtContext, SmtResult, UnsatCoreDiagnostics,
};
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_core::term::{TermData, TermId};
use ay_core::{FarkasAnnotation, Proof, ProofId, ProofStep, TheoryLemmaKind};
use ay_core::{TermStore, TheoryResult, TheorySolver};
use ay_lia::LiaSolver;
use num_rational::Rational64;
use num_traits::Signed;
use std::sync::atomic::{AtomicUsize, Ordering};

macro_rules! iuc_trace {
    ($($arg:tt)*) => {
        if iuc_trace_enabled() {
            safe_eprintln!("[IUC] {}", format!($($arg)*));
        }
    };
}

#[derive(Debug, Clone, Copy, Default)]
struct ZeroFarkasStats {
    attempts: usize,
    direct_iuc_successes: usize,
    direct_iuc_core_exact_successes: usize,
    a_side_equality_successes: usize,
    fm_elimination_successes: usize,
    b_side_fm_projection_successes: usize,
    lia_farkas_attempts: usize,
    lia_farkas_successes: usize,
    lia_farkas_precondition_failures: usize,
    lia_farkas_no_certificate_failures: usize,
    lia_farkas_proof_extraction_failures: usize,
    lia_farkas_craig_failures: usize,
    synthetic_successes: usize,
    failures: usize,
}

static ZERO_FARKAS_ATTEMPTS: AtomicUsize = AtomicUsize::new(0);
static ZERO_FARKAS_DIRECT_IUC_SUCCESSES: AtomicUsize = AtomicUsize::new(0);
static ZERO_FARKAS_DIRECT_IUC_CORE_EXACT_SUCCESSES: AtomicUsize = AtomicUsize::new(0);
static ZERO_FARKAS_A_SIDE_EQUALITY_SUCCESSES: AtomicUsize = AtomicUsize::new(0);
static ZERO_FARKAS_FM_ELIMINATION_SUCCESSES: AtomicUsize = AtomicUsize::new(0);
static ZERO_FARKAS_B_SIDE_FM_PROJECTION_SUCCESSES: AtomicUsize = AtomicUsize::new(0);
static ZERO_FARKAS_LIA_FARKAS_ATTEMPTS: AtomicUsize = AtomicUsize::new(0);
static ZERO_FARKAS_LIA_FARKAS_SUCCESSES: AtomicUsize = AtomicUsize::new(0);
static ZERO_FARKAS_LIA_FARKAS_PRECONDITION_FAILURES: AtomicUsize = AtomicUsize::new(0);
static ZERO_FARKAS_LIA_FARKAS_NO_CERTIFICATE_FAILURES: AtomicUsize = AtomicUsize::new(0);
static ZERO_FARKAS_LIA_FARKAS_PROOF_EXTRACTION_FAILURES: AtomicUsize = AtomicUsize::new(0);
static ZERO_FARKAS_LIA_FARKAS_CRAIG_FAILURES: AtomicUsize = AtomicUsize::new(0);
static ZERO_FARKAS_SYNTHETIC_SUCCESSES: AtomicUsize = AtomicUsize::new(0);
static ZERO_FARKAS_FAILURES: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InterpolantKind {
    DirectIucCoreExact,
    DirectIucValidated,
    ASideEquality,
    FourierMotzkin,
    BSideFourierMotzkin,
    LiaFarkas,
    Synthetic,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct InterpolantCandidate {
    pub(crate) expr: ChcExpr,
    pub(crate) kind: InterpolantKind,
    pub(crate) has_farkas_conflicts: bool,
}

impl InterpolantCandidate {
    fn new(expr: ChcExpr, kind: InterpolantKind, has_farkas_conflicts: bool) -> Self {
        Self {
            expr,
            kind,
            has_farkas_conflicts,
        }
    }
}

fn bump_zero_farkas(counter: &AtomicUsize) {
    counter.fetch_add(1, Ordering::Relaxed);
}

mod farkas;
mod fourier_motzkin;
mod lia_farkas;
mod linear;
mod projection;
mod proof_marking;
mod proof_traversal;
mod smt_history;
mod strategies;
mod zero_farkas;

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;

// Re-export pub(crate) items
pub(crate) use farkas::extract_interpolant_from_proof;
pub(crate) use lia_farkas::compute_interpolant_from_lia_farkas;
pub(crate) use linear::{
    build_linear_inequality, rational64_abs, strengthen_strict_lia_constraint,
};
pub(crate) use proof_marking::{collect_farkas_lemmas, mark_proof_nodes};
pub(crate) use proof_traversal::{traverse_proof, TraversalAlgorithm};
pub(crate) use smt_history::{
    compute_interpolant_candidate_from_smt_farkas_history,
    compute_interpolant_from_smt_farkas_history, extract_interpolant_from_precomputed_farkas,
};

// Internal imports shared by child modules via `use super::*`.
use farkas::{
    classify_literal, combine_a_constraints, vars_all_shared, verify_craig_properties, LiteralClass,
};
pub(crate) use fourier_motzkin::try_fourier_motzkin_elimination;
use linear::{flip_linear_constraint, is_equality_constraint, weighted_sum_linear_constraints};
#[cfg(test)]
use linear::{i64_gcd, i64_lcm};
use projection::{as_atom_and_value, flatten_constraints, is_linear_atom, try_mbp_projection};
#[cfg(test)]
use proof_marking::and_with_tail;
use proof_marking::{and_slice, atom_of_literal, collect_theory_atoms};
use strategies::{
    try_a_side_equality_interpolant, try_a_side_farkas_projection, try_b_pure_combination,
    try_per_clause_interpolation, try_relaxed_b_origin_combination, try_split_literals_combination,
    try_synthetic_decomposed_farkas,
};
#[cfg(test)]
use zero_farkas::try_zero_farkas_interpolant;
use zero_farkas::{select_shrunk_b_occurrences, try_zero_farkas_interpolant_candidate};

/// Returns true if IUC tracing is enabled via AY_IUC_TRACE environment variable.
///
/// Used by both proof_interpolation and iuc_solver modules for consistent tracing.
pub(crate) fn iuc_trace_enabled() -> bool {
    // Delegates to ay-core's centralized ChcDebugEnvFlags OnceLock cache (#8506).
    ay_core::chc_debug_env_flags().iuc_trace
}

/// Returns true if zero-Farkas fallbacks should be treated as a hard diagnostic.
///
/// Set `AY_IUC_REQUIRE_FARKAS=1` (or `true`) to force a debug assertion when
/// `compute_interpolant_from_smt_farkas_history` observes UNSAT with no Farkas
/// conflicts. This is used to investigate #2450 regressions where interpolation
/// quality may degrade due to missing theory certificates.
fn iuc_require_farkas_enabled() -> bool {
    // Delegates to ay-core's centralized ChcDebugEnvFlags OnceLock cache (#8506).
    ay_core::chc_debug_env_flags().iuc_require_farkas
}

pub(super) fn trace_zero_farkas_diagnostic(
    a_count: usize,
    shrunk_b_count: usize,
    iuc_core_count: usize,
    iuc_b_core_count: usize,
    used_full_b_fallback: bool,
    smt_diagnostic: Option<UnsatCoreDiagnostics>,
) {
    let base_message = format!(
        "iuc_core={iuc_core_count}, iuc_b_core={iuc_b_core_count}, used_full_b_fallback={used_full_b_fallback}, A_count={a_count}, shrunk_B_count={shrunk_b_count}"
    );
    let with_smt = smt_diagnostic.map(|diag| {
        format!(
            "{base_message}, dt_iters={}, theory_unsat={}, theory_farkas={}, theory_farkas_none={}, splits={}, core_activation_hits={}, total_farkas_seen={}",
            diag.dt_iterations,
            diag.theory_unsat_count,
            diag.theory_farkas_count,
            diag.theory_farkas_none_count,
            diag.split_count,
            diag.activation_core_conflicts,
            diag.total_farkas_conflicts
        )
    });
    let diagnostic_message = with_smt.unwrap_or(base_message);

    if iuc_trace_enabled() {
        safe_eprintln!("[IUC] zero-Farkas fallback: {diagnostic_message}");
    }

    if iuc_require_farkas_enabled() {
        let message = format!(
            "AY_IUC_REQUIRE_FARKAS triggered: UNSAT query reached zero-Farkas fallback ({diagnostic_message})"
        );
        safe_eprintln!("[IUC] {message}");
    }
}

/// Snapshot current zero-Farkas statistics counters.
fn zero_farkas_stats_snapshot() -> ZeroFarkasStats {
    ZeroFarkasStats {
        attempts: ZERO_FARKAS_ATTEMPTS.load(Ordering::Relaxed),
        direct_iuc_successes: ZERO_FARKAS_DIRECT_IUC_SUCCESSES.load(Ordering::Relaxed),
        direct_iuc_core_exact_successes: ZERO_FARKAS_DIRECT_IUC_CORE_EXACT_SUCCESSES
            .load(Ordering::Relaxed),
        a_side_equality_successes: ZERO_FARKAS_A_SIDE_EQUALITY_SUCCESSES.load(Ordering::Relaxed),
        fm_elimination_successes: ZERO_FARKAS_FM_ELIMINATION_SUCCESSES.load(Ordering::Relaxed),
        b_side_fm_projection_successes: ZERO_FARKAS_B_SIDE_FM_PROJECTION_SUCCESSES
            .load(Ordering::Relaxed),
        lia_farkas_attempts: ZERO_FARKAS_LIA_FARKAS_ATTEMPTS.load(Ordering::Relaxed),
        lia_farkas_successes: ZERO_FARKAS_LIA_FARKAS_SUCCESSES.load(Ordering::Relaxed),
        lia_farkas_precondition_failures: ZERO_FARKAS_LIA_FARKAS_PRECONDITION_FAILURES
            .load(Ordering::Relaxed),
        lia_farkas_no_certificate_failures: ZERO_FARKAS_LIA_FARKAS_NO_CERTIFICATE_FAILURES
            .load(Ordering::Relaxed),
        lia_farkas_proof_extraction_failures: ZERO_FARKAS_LIA_FARKAS_PROOF_EXTRACTION_FAILURES
            .load(Ordering::Relaxed),
        lia_farkas_craig_failures: ZERO_FARKAS_LIA_FARKAS_CRAIG_FAILURES.load(Ordering::Relaxed),
        synthetic_successes: ZERO_FARKAS_SYNTHETIC_SUCCESSES.load(Ordering::Relaxed),
        failures: ZERO_FARKAS_FAILURES.load(Ordering::Relaxed),
    }
}

fn trace_zero_farkas_stats(outcome: &str) {
    if !iuc_trace_enabled() {
        return;
    }
    let stats = zero_farkas_stats_snapshot();
    iuc_trace!(
        "zero-Farkas stats [{}]: attempts={}, direct_iuc={}, direct_iuc_core_exact={}, a_eq={}, fm={}, b_fm={}, lia_attempts={}, lia_farkas={}, lia_precond_fail={}, lia_no_cert_fail={}, lia_extract_fail={}, lia_craig_fail={}, synthetic={}, failures={}",
        outcome,
        stats.attempts,
        stats.direct_iuc_successes,
        stats.direct_iuc_core_exact_successes,
        stats.a_side_equality_successes,
        stats.fm_elimination_successes,
        stats.b_side_fm_projection_successes,
        stats.lia_farkas_attempts,
        stats.lia_farkas_successes,
        stats.lia_farkas_precondition_failures,
        stats.lia_farkas_no_certificate_failures,
        stats.lia_farkas_proof_extraction_failures,
        stats.lia_farkas_craig_failures,
        stats.synthetic_successes,
        stats.failures
    );
}

pub(super) fn fail_lia_farkas_interpolant(counter: &AtomicUsize, reason: &str) -> Option<ChcExpr> {
    bump_zero_farkas(counter);
    iuc_trace!("compute_interpolant_from_lia_farkas: {reason}");
    None
}

type SignedLit = (TermId, bool);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DependencyMark {
    None,
    A,
    B,
    AB,
}

impl DependencyMark {
    fn union(self, other: Self) -> Self {
        use DependencyMark::{None, A, AB, B};
        match (self, other) {
            (None, x) | (x, None) => x,
            (A, A) => A,
            (B, B) => B,
            (AB, _) | (_, AB) => AB,
            (A, B) | (B, A) => AB,
        }
    }
}

// ============================================================================
// Kani Verification Harnesses
// ============================================================================

#[cfg(kani)]
mod verification {
    use super::*;

    fn any_dependency_mark() -> DependencyMark {
        let v: u8 = kani::any();
        kani::assume(v < 4);
        match v {
            0 => DependencyMark::None,
            1 => DependencyMark::A,
            2 => DependencyMark::B,
            _ => DependencyMark::AB,
        }
    }

    #[kani::proof]
    fn proof_dependency_mark_union_commutative() {
        let a = any_dependency_mark();
        let b = any_dependency_mark();
        assert_eq!(a.union(b), b.union(a));
    }

    #[kani::proof]
    fn proof_dependency_mark_union_associative() {
        let a = any_dependency_mark();
        let b = any_dependency_mark();
        let c = any_dependency_mark();
        assert_eq!(a.union(b).union(c), a.union(b.union(c)));
    }

    #[kani::proof]
    fn proof_dependency_mark_union_idempotent() {
        let a = any_dependency_mark();
        assert_eq!(a.union(a), a);
    }
}
