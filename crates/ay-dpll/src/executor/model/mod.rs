// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model construction, evaluation, and formatting.
//!
//! This module contains:
//! - `Model` struct representing a satisfying assignment
//! - `EvalValue` enum for evaluated term values
//! - Model evaluation functions for term interpretation
//! - Model formatting functions for SMT-LIB output

// #8529: Use deterministic hash maps in all builds.
use ay_arrays::ArrayModel;
use ay_bv::BvModel;
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, TermData, TermEntryStamp, TermStoreSnapshotStamp};
use ay_core::{Sort, Symbol, TermId, TermStore};
use ay_euf::EufModel;
use ay_fp::{FpModel, FpModelValue};
use ay_lia::LiaModel;
use ay_lra::LraModel;
use ay_seq::SeqModel;
use ay_set::OP_CARD;
use ay_strings::StringModel;
use num_bigint::BigInt;
use num_rational::BigRational;
use std::sync::Arc;

#[cfg(test)]
use crate::executor_types::ModelValidationError;
use crate::executor_types::SolveResult;
use crate::executor_types::{ExecutorError, Result};

use super::Executor;
mod array_reconcile;
mod completion;
mod datatype_cell_authority;
mod datatype_opaque_scope;
mod dt_bounds;
mod dt_collect_scope;
mod dt_construct;
mod dt_construct_budget;
mod dt_egraph_values;
mod dt_model;
mod eval_arith;
mod eval_array;
mod eval_bv;
mod eval_bv_structural;
mod eval_fp;
mod eval_parse;
mod eval_seq;
mod eval_string;
mod eval_uf;
mod eval_var;
mod independent_gate;
pub(in crate::executor) use independent_gate::probe_budget::QuantifiedGateProbeBudget;
pub(in crate::executor) use independent_gate::QuantifiedModelConfirmation;
mod ite_fixup;
mod ite_fixup_limits;
mod minimize;
mod nra_refine;
mod output;
mod output_format;
mod output_objectives;
mod projection_uf;
mod rendered_dt_guard;
mod rendered_dt_limits;
pub(crate) mod sat_emit;
mod set_materialize;
mod string_materialize;
pub(in crate::executor) mod string_witness;
pub(in crate::executor) mod uflia_witness;
mod validation;

/// Whether term evaluation is currently running under a datatype-materializer
/// pin set or lexical scoped binding.  Exact source-semantic certificates must
/// decline in this state because `evaluate_term` is intentionally contextual.
pub(in crate::executor) fn scoped_term_evaluation_override_active() -> bool {
    dt_model::dt_field_override_active()
}

#[cfg(test)]
pub(in crate::executor) fn with_scoped_term_evaluation_override_for_test<R>(
    term: TermId,
    value: EvalValue,
    f: impl FnOnce() -> R,
) -> R {
    dt_model::with_scoped_term_override(term, value, f)
}

pub(in crate::executor) use dt_egraph_values::DtEgraphAssignment;
pub(in crate::executor) use eval_array::ArrayDefIndexCache;
pub(crate) use validation::ValidationStats;

/// Red zone size for `stacker::maybe_grow` in model evaluation (#4602).
pub(super) const EVAL_STACK_RED_ZONE: usize = if cfg!(debug_assertions) {
    128 * 1024
} else {
    32 * 1024
};

/// Stack segment size allocated by stacker for model evaluation recursion.
pub(super) const EVAL_STACK_SIZE: usize = 2 * 1024 * 1024;

/// Normalized array representation: (default value, sorted index→value pairs).
/// Used by `normalize_array_to_stores` for semantic equality comparison of array models.
type NormalizedArray = (Option<String>, Vec<(String, String)>);

/// Cached `AY_DEBUG_MODEL` env var (checked once per process).
pub(super) fn debug_model() -> bool {
    crate::theory_debug_flags::debug_model()
}

/// `evaluate_term` result memoization (`#eval-memo`, perf-only).
///
/// Model validation evaluates the ORIGINAL assertions, which — for VC-style
/// inputs — are giant shared DAGs: the same guard prefix and `ay_let_share_*`
/// subterms recur across dozens of assertions, and `evaluate_term` is a plain
/// structural recursion with NO sharing, so a naive walk re-evaluates each
/// shared subterm exponentially. This module caches `evaluate_term(term_id)`
/// for the duration of a validation pass over a FIXED model.
///
/// SOUNDNESS (verdict-preserving, perf-only): for a fixed model state,
/// `evaluate_term(self, model, term_id)` is a pure function of `term_id`
/// (`self`/`model` are borrowed immutably throughout the recursion), so
/// returning a cached value can only change HOW MANY TIMES a subterm is
/// computed, never WHAT it computes. Two invariants keep the cache valid:
///   1. It is only consulted inside an explicit [`EvalMemoSession`], installed
///      exclusively over passes that hold the model immutable (or that clear
///      the cache on every mutation — see [`eval_memo_clear`]).
///   2. It is entirely bypassed while the dt-materialization override is active
///      (see `dt_model::dt_field_override_active`), the one context where a
///      `term_id` is not a pure function of the model.
/// (The former `AY_DISABLE_EVAL_MEMO=1` differential-check bypass is removed;
/// the memo is always live inside a session.)
mod eval_memo;

pub(in crate::executor) use eval_guard::AssertionsFrozen;
pub(in crate::executor::model) use eval_guard::EvalWorkBudget;
pub(in crate::executor) use eval_memo::with_isolated_eval_memo;
pub(crate) use eval_memo::EvalMemoSession;
pub(in crate::executor) use projection_uf::ProjectionUfModel;

mod div_witness;
#[allow(unused_imports)]
pub(in crate::executor) use div_witness::{
    DivWitnessCandidate, DivWitnessFamily, DivWitnessIndex, DivWitnessIndexCache,
};

/// Evaluation re-entrancy guard (`#eval-cycle-guard`).
///
/// Model evaluation resolves UF function-table placeholders (`@?id`) by
/// recursively evaluating the referenced terms (see
/// `evaluate_uf_app_from_function_table`). Congruent rows can reference each
/// other CYCLICALLY (resolving one row's atom walks back into the same
/// table), and a cyclic derivation has no finite value: the recursion
/// previously diverged, and — because evaluation grows its stack through
/// `stacker::maybe_grow` — it mmapped 2MiB stack segments forever instead of
/// overflowing cleanly, taking the whole machine down once the VM compressor
/// saturated (2026-07-10 watchdog panic: the group_auflia test binary at
/// 108GB RSS). Breaking the cycle with `Unknown` is the honest fail-closed
/// verdict: no committed value is derivable for the cycling term, and every
/// caller already falls through to its next source (or degrades its check)
/// on `Unknown`.
///
/// The guard also carries the memo-admission bookkeeping (#eval-lowlink):
///   - DEPTH-SCOPED purity: each frame tracks the minimum entry depth
///     targeted by cycle re-entries observed during its computation. A
///     frame memoizes iff that minimum is >= its own depth — every observed
///     cycle is then internal to its subtree and its result is a pure
///     function of `(model, term)`
///     (a fresh top-level evaluation reproduces the identical fail-closed
///     cuts). Only frames a cycle actually reaches ABOVE are unmemoizable.
///     The earlier GLOBAL poison vetoed the whole stack over any cycle —
///     with UF-table self-rows guaranteeing bottom cycles, nothing
///     memoized and evaluation went exponential-time (30s verification-consumer spins).
///   - a STOP poison: results computed across an external stop are never
///     memoized (they reflect the interrupt, not the model).
///   - an enter counter driving a periodic external-stop poll, so an
///     interrupt/deadline actually terminates long evaluation passes
///     (previously only the search loop polled the flag; model evaluation
///     ran to completion no matter what).
mod eval_guard;

/// Invalidate the `evaluate_term` result cache after a model mutation
/// (`#eval-memo`). Free function so mutation sites that hold only `&mut Model`
/// (not `&self`) can call it.
pub(super) fn eval_memo_clear() {
    eval_memo::clear();
}

#[cfg(test)]
pub(in crate::executor) fn seed_eval_memo_for_test(term_id: TermId, value: EvalValue) {
    eval_memo::seed_for_test(term_id, value);
}

/// This thread's monotone count of memo-missing `evaluate_term` node visits —
/// the evaluator's deterministic work clock. Used by the W4 witness search to
/// bound its hill-climb by WORK rather than by wall time, so the same file
/// gets the same search on an idle box and a loaded one (`#w4-work-budget`).
pub(crate) fn eval_node_visits() -> u64 {
    eval_guard::enters()
}

mod certificate_data;
use certificate_data::{
    eval_value_has_exact_sort, CertifiedConstInterpModel, CertifiedTotalUfInterpretation,
    CertifiedTotalUfModel, FormulaNeutralFunctionDefaults, QuantifiedConfirmationModelSeal,
    QuantifiedGrantModelSeal, StampedCertificatePin, StampedClosedValueGraph,
};
pub(in crate::executor) use certificate_data::{
    CegqiUfModelEpoch, CertifiedConstInterpEntry, CertifiedConstInterpReadError,
    FormulaNeutralFunctionDefaultEntry, FormulaNeutralFunctionDefaultReadError,
    QuantifiedConfirmationModelEpoch, QuantifiedGrantModelEpoch,
};

/// A satisfying model from check-sat
#[derive(Debug, Clone)]
pub(super) struct Model {
    /// Exact identity installed by a successful quantified-model check.
    ///
    /// It is not SAT authority by itself.  The independent gate also requires
    /// the sealed executor capability carrying the matching public-query,
    /// source-context, and ordered-root snapshot.
    quantified_confirmation_seal: QuantifiedConfirmationModelSeal,
    /// Replacement-sensitive identity retained by model-relative quantified
    /// certificate grants across the final gate's one-shot seal cleanup.
    quantified_grant_model_seal: QuantifiedGrantModelSeal,
    /// SAT variable assignments (indexed by variable)
    pub(super) sat_model: Vec<bool>,
    /// Reverse mapping from term IDs to SAT variables (for efficient lookup)
    pub(super) term_to_var: HashMap<TermId, u32>,
    /// Bool variable overrides for variables eliminated during preprocessing.
    ///
    /// When `VariableSubstitution` eliminates a Bool variable (e.g., `p -> (> x 0)`),
    /// the SAT model has no assignment for `p`. This map stores recovered Bool
    /// values computed by evaluating the substitution expression against the
    /// arithmetic model after solving.
    pub(super) bool_overrides: HashMap<TermId, bool>,
    /// Optional EUF model (for QF_UF and related logics)
    pub(super) euf_model: Option<EufModel>,
    /// Optional array model (for QF_AX and related logics)
    pub(super) array_model: Option<ArrayModel>,
    /// Optional LRA model (for QF_LRA and related logics)
    pub(super) lra_model: Option<LraModel>,
    /// Optional LIA model (for QF_LIA and related logics)
    pub(super) lia_model: Option<LiaModel>,
    /// Optional BV model (for QF_BV and related logics)
    pub(super) bv_model: Option<BvModel>,
    /// Optional FP model (for QF_FP and related logics)
    pub(super) fp_model: Option<FpModel>,
    /// Optional String model (for QF_S and related logics)
    pub(super) string_model: Option<StringModel>,
    /// Optional Seq model (for QF_SEQ and related logics).
    pub(super) seq_model: Option<SeqModel>,
    /// Exact total interpretations certified for quantified UF heads.
    ///
    /// These symbolic projections are result-local and are consulted before
    /// finite EUF tables.  They are model data only; possession of this field
    /// is not authority to emit SAT.
    projection_ufs: ProjectionUfModel,
    /// Exact typed table/default interpretations built by quantified SAT
    /// certificates. Consulted before stale per-application ground values.
    certified_total_ufs: CertifiedTotalUfModel,
    /// Exact constant-function interpretations built by a quantified SAT
    /// certificate.  The declaration bindings and stamped values travel with
    /// this model and are shared by semantic clones; publication authority is
    /// intentionally stored in the non-cloning seals above instead.
    certified_const_interps: CertifiedConstInterpModel,
    /// Canonical defaults for ordinary functions proved absent from the exact
    /// quantified theorem roots. Kept separate from `euf_model` so adding an
    /// output-only declaration cannot change strict-gate classification.
    formula_neutral_function_defaults: FormulaNeutralFunctionDefaults,
    /// Completion-assigned values for declared constants that have no entry in
    /// any theory model (model/completion.rs, #no-fabricated-model-values).
    ///
    /// Filled BEFORE model validation runs, so the independent gate and the
    /// printers read the SAME value. Consulted by `evaluate_var` strictly as
    /// the LAST resort — a theory-model value always wins — which keeps the
    /// slot fill-only at the evaluation level.
    pub(super) completed_values: HashMap<TermId, EvalValue>,
    /// Total-datatype-model construction: the constructed ground value per
    /// datatype-sorted term (model/dt_construct.rs, #dt-total-model). Filled
    /// BEFORE validation so every validator (term evaluator, strict DtOracle,
    /// independent gate) and the printers read the SAME total assignment.
    pub(super) dt_ground: HashMap<TermId, ay_model_check::ModelValue>,
    /// Evaluation pins derived from `dt_ground`: `Element(canonical)` for
    /// datatype-sorted terms, projected/committed scalar values for selector
    /// applications, and Bool values for tester applications
    /// (#dt-total-model). Consulted at the top of `evaluate_term`.
    pub(super) dt_pins: HashMap<TermId, EvalValue>,
}

mod model_base;
mod model_quantified;
mod model_total_uf;

/// Evaluated value from model evaluation
#[derive(Debug, Clone)]
pub(crate) enum EvalValue {
    /// Boolean value
    Bool(bool),
    /// Element from an uninterpreted sort (by name, e.g., "@U!0")
    Element(String),
    /// Rational/integer value (BigRational can represent both)
    Rational(BigRational),
    /// Bitvector value with width
    BitVec {
        /// The numeric value of the bitvector
        value: BigInt,
        /// The bit width of the bitvector
        width: u32,
    },
    /// IEEE 754 floating-point value (as SMT-LIB string)
    Fp(FpModelValue),
    /// String value
    String(String),
    /// Sequence value (parametric: elements can be any EvalValue)
    Seq(Vec<Self>),
    /// Exact real algebraic value (e.g. `√2` for `x*x = 2`), carried as a
    /// polynomial expression over an NRA `root-obj` witness. All arithmetic
    /// and comparisons on it are exact (Sturm-sequence based) — see
    /// `ay_nra::RealAlgebraicValue`.
    Algebraic(ay_nra::RealAlgebraicValue),
    /// Unknown/undefined value
    Unknown,
}

impl PartialEq for EvalValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Bool(a), Self::Bool(b)) => a == b,
            (Self::Element(a), Self::Element(b)) => a == b,
            (Self::Rational(a), Self::Rational(b)) => a == b,
            (
                Self::BitVec {
                    value: v1,
                    width: w1,
                },
                Self::BitVec {
                    value: v2,
                    width: w2,
                },
            ) => v1 == v2 && w1 == w2,
            (Self::Fp(a), Self::Fp(b)) => a.to_smtlib() == b.to_smtlib(),
            (Self::String(a), Self::String(b)) => a == b,
            (Self::Seq(a), Self::Seq(b)) => a == b,
            // Exact algebraic equality: certified by a polynomial GCD/sign
            // argument, never by numeric proximity. An undecided comparison
            // (refinement cap — practically unreachable) compares unequal.
            // Callers that may treat inequality as disequality evidence must
            // use `eval_values_equal_exact` and preserve its tri-state result.
            (Self::Algebraic(a), Self::Algebraic(b)) => a.eq_value(b) == Some(true),
            (Self::Algebraic(a), Self::Rational(r)) | (Self::Rational(r), Self::Algebraic(a)) => {
                a.cmp_rational(r) == Some(std::cmp::Ordering::Equal)
            }
            (Self::Unknown, Self::Unknown) => true,
            _ => false,
        }
    }
}

impl Eq for EvalValue {}

impl Executor {
    /// D1 shadow finalizer for the on-assert lazy-extensionality campaign.
    ///
    /// Correlates the EAGER set (every `__ay_ext_diff` witness the eager path
    /// actually emitted this solve) against the DEMANDED set (array pairs whose
    /// `(= a b)` equality atom the search forced FALSE — i.e. `a ≠ b` was
    /// asserted, which is exactly the antecedent that makes the extensionality
    /// clause `(= a b) ∨ ¬sel_eq` active). Surfaces the counts under
    /// `auflia.ext.*`. Measurement only: nothing here changes the verdict.
    ///
    /// Demand observation is exact only for SAT (the final assignment pins every
    /// atom's polarity via `Model::term_value`). For UNSAT/UNKNOWN there is no
    /// returned assignment, so demand falls back to the SOUND syntactic signal:
    /// a pair is demanded when its `(= a b)` atom is forced false by the
    /// top-level assertions (a hard, unconditional `a ≠ b` fact). This
    /// under-counts transient in-search demand on UNSAT, which the D2 verdict
    /// accounts for.
    pub(in crate::executor) fn finalize_array_ext_shadow(&mut self) {
        let eager = self.array_ext_shadow.emitted.len() as u64;
        if eager == 0 {
            // Nothing emitted — leave the counters absent to avoid noise on the
            // overwhelming majority of (non-array) queries.
            return;
        }

        let is_sat = matches!(self.last_result, Some(SolveResult::Sat));

        // Demand via the final SAT assignment when available (exact realized
        // demand: the pairs the model committed to a ≠ b).
        let model_demanded: Option<u64> = match &self.last_model {
            Some(model) if is_sat => {
                let mut n = 0u64;
                // Snapshot the tiny (eq_term) list so the shared borrow of
                // `self.array_ext_shadow` does not overlap the `self.term_value` call.
                let atoms: Vec<TermId> = self
                    .array_ext_shadow
                    .emitted
                    .iter()
                    .map(|&(eq_term, ..)| eq_term)
                    .collect();
                for eq_term in atoms {
                    if self.term_value(&model.sat_model, &model.term_to_var, eq_term) == Some(false)
                    {
                        n += 1;
                    }
                }
                Some(n)
            }
            _ => None,
        };

        // Demand via top-level forced-false equality atoms (sound on any result,
        // including UNSAT where no model exists): `(= a b)` appears negated as a
        // top-level fact, so a ≠ b is unconditionally asserted.
        let mut top_demanded = 0u64;
        let atoms: Vec<TermId> = self
            .array_ext_shadow
            .emitted
            .iter()
            .map(|&(eq_term, ..)| eq_term)
            .collect();
        for eq_term in atoms {
            if self.array_eq_forced_false_top_level(eq_term) {
                top_demanded += 1;
            }
        }

        // The authoritative demand figure: realized model demand when we have a
        // model, else the sound top-level lower bound.
        let demanded = model_demanded.unwrap_or(top_demanded);
        let dead_mass = eager.saturating_sub(demanded);

        self.last_statistics.set_int("auflia.ext.eager", eager);
        self.last_statistics
            .set_int("auflia.ext.demanded", demanded);
        self.last_statistics
            .set_int("auflia.ext.demanded_toplevel", top_demanded);
        self.last_statistics
            .set_int("auflia.ext.dead_mass", dead_mass);
        if let Some(md) = model_demanded {
            self.last_statistics
                .set_int("auflia.ext.demanded_model", md);
        }
    }

    /// True when the array-equality `atom` is forced FALSE by the top-level
    /// assertions — i.e. `¬atom` (a hard `a ≠ b` fact) is asserted, descending
    /// through top-level `and`/`not`. Sound demand signal for the D1 shadow on
    /// any result (no model required). Conservative: a disjunct-buried
    /// `¬(= a b)` is NOT counted here (that is precisely the qlock over-emission
    /// the campaign targets).
    fn array_eq_forced_false_top_level(&self, atom: TermId) -> bool {
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(a) = stack.pop() {
            if !seen.insert(a) {
                continue;
            }
            match self.ctx.terms.get(a) {
                TermData::Not(inner) if *inner == atom => return true,
                TermData::App(sym, args) if sym.name() == "and" => {
                    stack.extend(args.iter().copied());
                }
                TermData::App(sym, args)
                    if sym.name() == "not" && args.len() == 1 && args[0] == atom =>
                {
                    return true;
                }
                _ => {}
            }
        }
        false
    }

    /// Evaluate a term that should return an integer value
    pub(super) fn evaluate_int_term(&self, model: &Model, term: TermId) -> Result<BigInt> {
        match self.evaluate_term(model, term) {
            EvalValue::Rational(r) => {
                if r.is_integer() {
                    Ok(r.numer().clone())
                } else {
                    Err(ExecutorError::UnsupportedOptimization(
                        "objective evaluated to non-integer rational".to_string(),
                    ))
                }
            }
            EvalValue::Unknown => Err(ExecutorError::UnsupportedOptimization(
                "objective could not be evaluated".to_string(),
            )),
            _ => Err(ExecutorError::UnsupportedOptimization(
                "objective did not evaluate to a number".to_string(),
            )),
        }
    }

    /// Get the value of a term from the model (simple SAT lookup)
    pub(super) fn term_value(
        &self,
        sat_model: &[bool],
        term_to_var: &HashMap<TermId, u32>,
        term_id: TermId,
    ) -> Option<bool> {
        // Use the cached reverse mapping for O(1) amortized lookup (HashMap)
        // Note: Model.term_to_var is always 0-indexed (converted from DIMACS 1-indexed)
        if let Some(&var) = term_to_var.get(&term_id) {
            return sat_model.get(var as usize).copied();
        }
        // Term not in model - could be eliminated or not relevant
        None
    }

    /// Resolve a `(select arr i)` read that the array/BV/EUF models could not
    /// value, by consulting the TOP-LEVEL assertions for an equality pinning it
    /// to a leaf (`Var`/`Const`) term (#aufbv-nonbv-elem).
    ///
    /// Returns the leaf side's evaluated value when some asserted
    /// `(= leaf select)` / `(= select leaf)` exists, else `Unknown`. Restricting
    /// the partner to a `Var`/`Const` keeps the lookup non-recursive (it never
    /// re-enters `evaluate_select`) and matches the head-anchoring equalities the
    /// VC encoder emits for slice reads. Every element of `ctx.assertions` is
    /// conjoined and therefore true in the model, so the value returned is the
    /// solver's committed interpretation — the subsequent full model validation
    /// re-checks it, so this can never fabricate a wrong SAT.
    fn resolve_select_via_asserted_equality(&self, model: &Model, select_id: TermId) -> EvalValue {
        for &assertion in &self.ctx.assertions {
            let TermData::App(sym, eq_args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if sym.name() != "=" || eq_args.len() != 2 {
                continue;
            }
            // Top-level asserted equalities are ambient model facts, not
            // schemas to reinterpret under a lambda-array binder.  Reusing a
            // dependent assertion inside beta evaluation can transfer the
            // value committed at the ambient point to a different point.
            if dt_model::term_depends_on_scoped_binding(&self.ctx.terms, assertion) {
                continue;
            }
            let partner = if eq_args[0] == select_id {
                eq_args[1]
            } else if eq_args[1] == select_id {
                eq_args[0]
            } else {
                continue;
            };
            if !matches!(
                self.ctx.terms.get(partner),
                TermData::Var(_, _) | TermData::Const(_)
            ) {
                continue;
            }
            let value = self.evaluate_term(model, partner);
            if !matches!(value, EvalValue::Unknown) {
                return value;
            }
        }
        EvalValue::Unknown
    }

    /// Evaluate a term under the current model, recursively handling composite terms.
    ///
    /// This handles Boolean connectives (and, or, not, ite), equality/distinct,
    /// and looks up values for variables and function applications.
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#4602).
    pub(super) fn evaluate_term(&self, model: &Model, term_id: TermId) -> EvalValue {
        // W4's search budget is cooperative inside evaluation, not merely at
        // the outer hill-climb. Once spent, even a cached value must not let a
        // partial atom sweep masquerade as a complete score.
        if self.w4_budget_exhausted() {
            return EvalValue::Unknown;
        }
        // A checked projection is a total symbolic interpretation. Resolve it
        // before every TermId-keyed source (datatype override/pin, result memo,
        // EUF table, theory value, or completion fallback), so all consumers
        // observe the selected argument rather than stale per-application
        // state. The shared iterative walk fails closed on its resource cap.
        match model
            .projection_ufs
            .peel_application_chain(&self.ctx.terms, term_id)
        {
            Ok(Some(projected_term)) => return self.evaluate_term(model, projected_term),
            Ok(None) => {}
            Err(_) => return EvalValue::Unknown,
        }
        // Datatype-field re-evaluation override (#dt-field-soundness). When the
        // materialized datatype re-evaluator (`dt_mat_eval`) is active it pins every
        // datatype selector/recognizer subterm to its concrete model value here, so
        // the full evaluator can finish a ground assertion over datatype fields
        // (every string/BV/int/seq predicate) without any op-by-op reimplementation.
        // The override is empty (no-op) on the normal evaluation path. It also
        // DISABLES the result memo (a `term_id` is not a pure function of the model
        // while materialization is pinning subterms) — see `#eval-memo`.
        if dt_model::dt_field_override_active() {
            if let Some(v) = dt_model::active_term_override_lookup(&self.ctx.terms, term_id) {
                return v;
            }
            if let Some(pin) = model.quantified_certificate_pin(&self.ctx.terms, term_id) {
                return pin;
            }
            // Cycle guard (#eval-cycle-guard): fail closed on re-entry. The
            // memo is bypassed in override mode, so no purity bookkeeping is
            // needed; re-entry observations flow into the enclosing frame's
            // scope, which is conservative and correct.
            let Some(_entered) = eval_guard::enter(term_id) else {
                return EvalValue::Unknown;
            };
            if self.w4_budget_exhausted() {
                return EvalValue::Unknown;
            }
            return self.evaluate_term_inner(model, term_id);
        }
        // Certificate projections are model-owned and slot-authenticated.
        // Consult only the `model` passed to this evaluation, before the
        // TermId-only memo. A rollback can reuse the numeric slot; a mismatched
        // birth stamp makes the retained model stale for that term and must
        // fail closed instead of returning either the old pin or a memoized
        // value for the discarded entry.
        if let Some(pin) = model.quantified_certificate_pin(&self.ctx.terms, term_id) {
            return pin;
        }
        // Result memo (perf-only, verdict-preserving; #eval-memo). Live only
        // inside an `EvalMemoSession` over an immutable model. A memoized
        // value is COMPLETE, so it can never extend a cycle — safe to return
        // before the re-entrancy check.
        if let Some(v) = eval_memo::get(term_id) {
            return v;
        }
        // Cycle guard (#eval-cycle-guard): a term already being evaluated on
        // this thread has no finite derivation — fail closed with Unknown.
        // (`enter` records the re-entry's target depth in the CALLER's
        // purity scope.)
        let Some(_entered) = eval_guard::enter(term_id) else {
            return EvalValue::Unknown;
        };
        if self.w4_budget_exhausted() {
            return EvalValue::Unknown;
        }
        // Periodic external-stop poll: lets an interrupt/deadline terminate
        // long evaluation passes instead of running them to completion.
        if eval_guard::should_poll_stop() && self.external_stop_reason().is_some() {
            eval_guard::note_stop();
            return EvalValue::Unknown;
        }
        // Depth-scoped memo admission (#eval-lowlink): open a fresh
        // observation scope, evaluate, memoize iff every cycle re-entry
        // observed targeted THIS frame or deeper (>= our depth — internal to
        // our subtree), then fold observations into the parent's scope.
        let parent_min = eval_guard::swap_min(u32::MAX);
        let stop_before = eval_guard::stop_poison();
        let work_budget_before = eval_guard::work_budget_poison();
        let v = self.evaluate_term_inner(model, term_id);
        let frame_min = eval_guard::min_reentry();
        if !self.w4_budget_exhausted()
            && frame_min >= eval_guard::depth()
            && eval_guard::stop_poison() == stop_before
            && eval_guard::work_budget_poison() == work_budget_before
        {
            eval_memo::put(term_id, &v);
        }
        eval_guard::fold_min(parent_min);
        v
    }

    /// Uncached body of [`Self::evaluate_term`]. Recursive calls go back through
    /// the memoized `evaluate_term` wrapper so shared subterms are computed once.
    fn evaluate_term_inner(&self, model: &Model, term_id: TermId) -> EvalValue {
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            // Total-datatype-model pins (#dt-total-model): a datatype-sorted
            // term, selector application, or tester application whose value the
            // datatype model-construction phase pinned evaluates to that pinned
            // value everywhere, so every validator and printer sees the same
            // total assignment. Empty (no-op) unless construction ran.
            // A pin is ambient and keyed only by TermId, so a term that
            // contains an active lambda binder must instead be evaluated in
            // that beta environment (or remain Unknown).
            if !model.dt_pins.is_empty()
                && !dt_model::term_depends_on_scoped_binding(&self.ctx.terms, term_id)
            {
                if let Some(pin) = model.dt_pins.get(&term_id) {
                    return pin.clone();
                }
            }
            // CONSTANT-INTERPRETATION CERTIFICATE WITNESS pins. When the
            // certificate published `I` as the model, `I(f)` is the CONSTANT
            // function `λ ȳ. c_f` — so `f` applied to anything, and a 0-ary `f`
            // itself, evaluate to `c_f`. Without this the evaluator would fall
            // through to the completion defaults `(get-model)` is overriding,
            // and `(get-value)` would contradict the printed model.
            //
            // Model ownership is load-bearing: a separately passed or cloned
            // model reads only its own package, never executor routing state.
            // Once a package owns the symbol, stale identity or a conflicting
            // application signature must stop here as `Unknown`; falling
            // through would let a lower-priority raw table contradict the
            // certified interpretation. The value is a closed, acyclic graph
            // of scalar literals and const-arrays, so recursion cannot return
            // to the interpreted head.
            match self.const_interp_witness_value(model, term_id) {
                Ok(Some(value)) if value != term_id => {
                    return self.evaluate_term(model, value);
                }
                Ok(Some(_)) | Err(_) => return EvalValue::Unknown,
                Ok(None) => {}
            }
            if let TermData::App(symbol, arguments) = self.ctx.terms.get(term_id) {
                match model.formula_neutral_function_default_for_application(
                    &self.ctx,
                    symbol,
                    arguments,
                    self.ctx.terms.sort(term_id),
                ) {
                    Ok(Some(value)) => return value,
                    Err(_) => return EvalValue::Unknown,
                    Ok(None) => {}
                }
            }
            let term = self.ctx.terms.get(term_id);
            let sort = self.ctx.terms.sort(term_id);

            match term {
                // Constants evaluate to themselves
                TermData::Const(Constant::Bool(b)) => EvalValue::Bool(*b),
                TermData::Const(Constant::Int(n)) => {
                    EvalValue::Rational(BigRational::from(n.clone()))
                }
                TermData::Const(Constant::Rational(r)) => EvalValue::Rational(r.0.clone()),
                TermData::Const(Constant::BitVec { value, width }) => EvalValue::BitVec {
                    value: value.clone(),
                    width: *width,
                },
                TermData::Const(Constant::String(s)) => EvalValue::String(s.clone()),

                // Variables: look up in appropriate model (eval_var.rs)
                TermData::Var(_, _) => self.evaluate_var(model, term_id, sort),

                // Negation
                TermData::Not(inner) => match self.evaluate_term(model, *inner) {
                    EvalValue::Bool(b) => EvalValue::Bool(!b),
                    _ => EvalValue::Unknown,
                },

                // If-then-else
                TermData::Ite(cond, then_br, else_br) => match self.evaluate_term(model, *cond) {
                    EvalValue::Bool(true) => self.evaluate_term(model, *then_br),
                    EvalValue::Bool(false) => self.evaluate_term(model, *else_br),
                    _ => EvalValue::Unknown,
                },

                // Function applications
                TermData::App(sym, args) => {
                    let name = sym.name();
                    // RoundingMode literal constants (#P0.2 symbolic
                    // RoundingMode): evaluate to the mode's long-name Element
                    // so `(= rm RTZ)` compares against the same spelling the
                    // EUF extraction / FP enumeration pin symbolic RM terms
                    // to (`roundTowardZero` — the value z3 prints).
                    if args.is_empty() && crate::executor::rm_domain::is_rm_sort(sort) {
                        if let Some(mode) = ay_fp::RoundingMode::from_name(name) {
                            return EvalValue::Element(
                                crate::executor::rm_domain::rm_long_name(mode).to_string(),
                            );
                        }
                    }
                    match name {
                        "and" => {
                            // All arguments must be true
                            for &arg in args {
                                match self.evaluate_term(model, arg) {
                                    EvalValue::Bool(false) => return EvalValue::Bool(false),
                                    EvalValue::Bool(true) => {}
                                    _ => return EvalValue::Unknown,
                                }
                            }
                            EvalValue::Bool(true)
                        }
                        "or" => {
                            // Any argument must be true
                            for &arg in args {
                                match self.evaluate_term(model, arg) {
                                    EvalValue::Bool(true) => return EvalValue::Bool(true),
                                    EvalValue::Bool(false) => {}
                                    _ => return EvalValue::Unknown,
                                }
                            }
                            EvalValue::Bool(false)
                        }
                        "=>" => {
                            // Implication: a => b is (not a) or b
                            if args.len() == 2 {
                                let a = self.evaluate_term(model, args[0]);
                                let b = self.evaluate_term(model, args[1]);
                                match (a, b) {
                                    (EvalValue::Bool(false), _) => EvalValue::Bool(true),
                                    (EvalValue::Bool(true), EvalValue::Bool(b)) => {
                                        EvalValue::Bool(b)
                                    }
                                    _ => EvalValue::Unknown,
                                }
                            } else {
                                EvalValue::Unknown
                            }
                        }
                        "=" => {
                            // Equality: both arguments must evaluate to same value
                            if args.len() == 2 {
                                let v1 = self.evaluate_term(model, args[0]);
                                let v2 = self.evaluate_term(model, args[1]);
                                let eq_result = match (&v1, &v2) {
                                    (EvalValue::Bool(b1), EvalValue::Bool(b2)) => {
                                        EvalValue::Bool(b1 == b2)
                                    }
                                    (EvalValue::Element(e1), EvalValue::Element(e2)) => {
                                        EvalValue::Bool(e1 == e2)
                                    }
                                    (EvalValue::Rational(r1), EvalValue::Rational(r2)) => {
                                        EvalValue::Bool(r1 == r2)
                                    }
                                    // Exact algebraic (dis)equality via Sturm
                                    // certificates; an undecidable comparison
                                    // fails closed to Unknown.
                                    (EvalValue::Algebraic(a), EvalValue::Algebraic(b)) => {
                                        match a.eq_value(b) {
                                            Some(eq) => EvalValue::Bool(eq),
                                            None => EvalValue::Unknown,
                                        }
                                    }
                                    (EvalValue::Algebraic(a), EvalValue::Rational(r))
                                    | (EvalValue::Rational(r), EvalValue::Algebraic(a)) => {
                                        match a.cmp_rational(r) {
                                            Some(ord) => {
                                                EvalValue::Bool(ord == std::cmp::Ordering::Equal)
                                            }
                                            None => EvalValue::Unknown,
                                        }
                                    }
                                    (
                                        EvalValue::BitVec {
                                            value: v1,
                                            width: w1,
                                        },
                                        EvalValue::BitVec {
                                            value: v2,
                                            width: w2,
                                        },
                                    ) => {
                                        let n1 = Self::normalize_bv_value(v1.clone(), *w1);
                                        let n2 = Self::normalize_bv_value(v2.clone(), *w2);
                                        EvalValue::Bool(n1 == n2 && w1 == w2)
                                    }
                                    (EvalValue::String(s1), EvalValue::String(s2)) => {
                                        EvalValue::Bool(s1 == s2)
                                    }
                                    (EvalValue::Seq(_), EvalValue::Seq(_)) => {
                                        match Self::eval_values_equal_exact(&v1, &v2) {
                                            Some(equal) => EvalValue::Bool(equal),
                                            None => EvalValue::Unknown,
                                        }
                                    }
                                    // FP structural equality for SMT-LIB `=`:
                                    // NaN == NaN (reflexive), +0 != -0 (distinct bit patterns).
                                    // This differs from `fp.eq` (IEEE 754) which has NaN != NaN, +0 == -0.
                                    (EvalValue::Fp(ref a), EvalValue::Fp(ref b)) => {
                                        EvalValue::Bool(a.structural_eq(b))
                                    }
                                    // Cross-type: Rational vs BitVec (#5356).
                                    // Can arise when the evaluator returns mismatched
                                    // types for a well-typed equality (e.g., DT+BV
                                    // combined theories, or int2bv/bv2nat boundaries).
                                    // Compare numerically: Rational must be a non-negative
                                    // integer that fits in the BV width.
                                    (
                                        EvalValue::Rational(r),
                                        EvalValue::BitVec { value: bv, width },
                                    )
                                    | (
                                        EvalValue::BitVec { value: bv, width },
                                        EvalValue::Rational(r),
                                    ) => {
                                        if r.is_integer() {
                                            let int_val = r.to_integer();
                                            let bv_normalized =
                                                Self::normalize_bv_value(bv.clone(), *width);
                                            EvalValue::Bool(int_val == bv_normalized)
                                        } else {
                                            // Non-integer rational can never equal a bitvector
                                            EvalValue::Bool(false)
                                        }
                                    }
                                    _ => {
                                        if matches!(self.ctx.terms.sort(args[0]), Sort::Array(_))
                                            && matches!(
                                                self.ctx.terms.sort(args[1]),
                                                Sort::Array(_)
                                            )
                                        {
                                            self.evaluate_array_equality(model, term_id, args)
                                        } else {
                                            // (#5499) Return Unknown instead of falling
                                            // back to the SAT model. The SAT model is
                                            // the thing being validated; using it as
                                            // evidence is circular. validate_model
                                            // handles Unknown appropriately.
                                            EvalValue::Unknown
                                        }
                                    }
                                };
                                // (#6282) Removed unsound SAT-model fallback for equalities
                                // involving array subterms. The previous code fell back to the
                                // SAT solver's truth value when (= (select a i) 42) evaluated
                                // to Bool(false)/Unknown. This was unsound: the theory solver
                                // returning SAT means "no conflict in the conjunction," not
                                // "every individual equality is correct." The downstream guards
                                // in validate_model correctly handle Bool(false)/Unknown for
                                // array assertions via sat_fallback_count or Unknown degradation.
                                //
                                // (#seq-ite-eq) ite-branch split for a definitively-false
                                // equality. When `eq_result` is Unknown because one operand is an
                                // `(ite c t e)` whose condition `c` is itself Unknown, we cannot
                                // pick a branch — but the ite necessarily equals EITHER `t` or
                                // `e`. If the OTHER operand is unequal to BOTH branches, the
                                // equality is `false` regardless of `c`. This soundly catches
                                // wrong-SAT cases such as
                                //   (= (seq.at v1 0) (ite <unknown> (seq.unit true) emptySeq))
                                // where the LHS `[false]` matches neither `[true]` nor `[]`.
                                if matches!(eq_result, EvalValue::Unknown) {
                                    if let Some(split) =
                                        self.eq_via_ite_branch_split(model, args[0], args[1])
                                    {
                                        return split;
                                    }
                                    // (#uflia-orphaned-congruence) Unknown = between
                                    // two apps of the SAME UF at the SAME argument
                                    // point is TRUE by congruence in every model,
                                    // even when the function itself has no committed
                                    // interpretation (preprocessing substituted it
                                    // away, orphaning both apps). True-direction
                                    // only; see eq_via_uf_congruence.
                                    if let Some(cong) =
                                        self.eq_via_uf_congruence(model, args[0], args[1])
                                    {
                                        return cong;
                                    }
                                    // (#euf-committed-class) Both sides opaque to
                                    // the evaluator (e.g. Seq-sorted terms, which
                                    // have no atomic model representation), but EUF
                                    // COMMITTED them to the same equivalence class:
                                    // the model interprets them identically, so the
                                    // equality holds UNDER THIS MODEL. That is the
                                    // fact EUF recorded when it merged them, and it
                                    // is exactly what the validator needs to certify
                                    // a datatype-selector = UF-projection equality
                                    // over `(Seq Int)` (9227). TRUE-direction only:
                                    // differing class elements stay Unknown
                                    // (fail-closed), never a manufactured `false`.
                                    // The class observations are ambient TermId
                                    // pins, so a beta-dependent equality cannot
                                    // use them as contextual evidence.
                                    if !dt_model::term_depends_on_scoped_binding(
                                        &self.ctx.terms,
                                        term_id,
                                    ) {
                                        if let Some(euf) = model.euf_model.as_ref() {
                                            if let (Some(lhs_elem), Some(rhs_elem)) = (
                                                euf.term_values.get(&args[0]),
                                                euf.term_values.get(&args[1]),
                                            ) {
                                                if lhs_elem == rhs_elem {
                                                    return EvalValue::Bool(true);
                                                }
                                            }
                                        }
                                    }
                                }
                                eq_result
                            } else {
                                EvalValue::Unknown
                            }
                        }
                        "distinct" => {
                            // All arguments must have different values
                            let values: Vec<EvalValue> =
                                args.iter().map(|&a| self.evaluate_term(model, a)).collect();

                            // Check for any unknown values
                            if values.iter().any(|v| matches!(v, EvalValue::Unknown)) {
                                return EvalValue::Unknown;
                            }

                            // Algebraic and sequence values need exact,
                            // tri-state pairwise comparison.  A sequence may
                            // contain an Unknown or an algebraic comparison
                            // whose refinement cap was reached; formatting it
                            // as a debug string would turn that lack of evidence
                            // into a spurious proof of disequality.
                            if values
                                .iter()
                                .any(|v| matches!(v, EvalValue::Algebraic(_) | EvalValue::Seq(_)))
                            {
                                return match Self::eval_values_distinct_exact(&values) {
                                    Some(distinct) => EvalValue::Bool(distinct),
                                    None => EvalValue::Unknown,
                                };
                            }

                            // Check all pairs are distinct
                            let mut seen: HashSet<String> = HashSet::default();
                            for v in &values {
                                let key = match v {
                                    EvalValue::Bool(b) => format!("bool:{b}"),
                                    EvalValue::Element(e) => format!("elem:{e}"),
                                    EvalValue::Rational(r) => format!("rat:{r}"),
                                    EvalValue::BitVec { value, width } => {
                                        let nv = Self::normalize_bv_value(value.clone(), *width);
                                        format!("bv:{width}:{nv}")
                                    }
                                    EvalValue::Fp(fp_val) => {
                                        format!("fp:{}", fp_val.to_smtlib())
                                    }
                                    EvalValue::String(s) => format!("str:{s}"),
                                    EvalValue::Seq(elems) => format!("seq:{elems:?}"),
                                    EvalValue::Algebraic(_) | EvalValue::Unknown => unreachable!(),
                                };
                                if seen.contains(&key) {
                                    return EvalValue::Bool(false);
                                }
                                seen.insert(key);
                            }
                            EvalValue::Bool(true)
                        }
                        "xor" => {
                            // XOR: exactly one of the two arguments must be true
                            if args.len() == 2 {
                                let a = self.evaluate_term(model, args[0]);
                                let b = self.evaluate_term(model, args[1]);
                                match (a, b) {
                                    (EvalValue::Bool(a_val), EvalValue::Bool(b_val)) => {
                                        EvalValue::Bool(a_val != b_val)
                                    }
                                    _ => EvalValue::Unknown,
                                }
                            } else {
                                EvalValue::Unknown
                            }
                        }
                        // Arithmetic operations — delegated to eval_arith.rs
                        "+" | "-" | "*" | "/" | "div" | "mod" | "rem" | "abs" | "to_real"
                        | "to_int" | "is_int" | "<" | "<=" | ">" | ">=" => {
                            self.evaluate_arith_app(model, name, args)
                        }
                        // BV operations — delegated to eval_bv.rs
                        "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt"
                        | "bvsge" | "bvadd" | "bvsub" | "bvmul" | "bvneg" | "bvand" | "bvor"
                        | "bvxor" | "bvnot" | "bvnand" | "bvnor" | "bvxnor" | "bvshl"
                        | "bvlshr" | "bvashr" | "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem"
                        | "bvsmod" | "concat" | "extract" | "zero_extend" | "sign_extend"
                        | "rotate_left" | "rotate_right" | "repeat" | "int2bv" | "bv2nat"
                        | "bvcomp" => self.evaluate_bv_app(model, sym, name, args, sort, term_id),
                        // Finite-set cardinality: count the members of the
                        // carrier AS THE MODEL PRINTS IT (#set-card-model-witness).
                        // `set.card` is otherwise an opaque UF whose value is
                        // read back from the solver's LIA assignment — which is
                        // exactly how `(get-model)` (the empty set) and
                        // `(get-value ((set.card s)))` (1) came to contradict
                        // each other. Counting from the printed interpretation
                        // makes get-value a function of the model, so the two
                        // can never disagree, and lets model validation reject a
                        // carrier whose size does not match the assertion.
                        // Fail-closed: `None` (an infinite/co-finite carrier, an
                        // unevaluable index, a carrier with no interpretation)
                        // falls back to the previous opaque-UF lookup rather
                        // than inventing a count.
                        OP_CARD if args.len() == 1 => {
                            match self.set_card_model_count(model, args[0]) {
                                Some(n) => EvalValue::Rational(BigRational::from(n)),
                                None => {
                                    self.evaluate_uninterpreted_app(model, sym, args, sort, term_id)
                                }
                            }
                        }
                        // Array select: select(a, i) -> evaluate using array axioms,
                        // falling back to BV model for bitblasted select terms (#4087).
                        "select" if args.len() == 2 => {
                            let result = self.evaluate_select(model, args[0], args[1]);
                            if matches!(result, EvalValue::Unknown) {
                                // The remaining select sources are ambient
                                // commitments keyed only by this TermId. They
                                // are not values for a beta-reduced occurrence
                                // whose array or index contains an active
                                // lambda binding. Structural/value-keyed array
                                // evaluation above remains available, while a
                                // missing contextual value fails closed.
                                if dt_model::term_depends_on_scoped_binding(
                                    &self.ctx.terms,
                                    term_id,
                                ) {
                                    return EvalValue::Unknown;
                                }
                                // EUF element fallback for an uninterpreted-sort
                                // array read (#aufbv-uninterp-elem). When the
                                // element sort is an uninterpreted (free) sort,
                                // the BV-backed array model carries no value for
                                // `(select arr i)` — it is not bit-blastable.
                                // The synthesized EUF element model
                                // (`complete_uninterpreted_sort_model`) assigns
                                // the select term its congruence-class element
                                // from the SAT-true equalities. Reading it here
                                // lets the validator decide equalities between
                                // uninterpreted-sort array elements instead of
                                // failing closed. Sound: the element is the
                                // solver's own committed interpretation of the
                                // (dis)equality atoms, re-checked by validation.
                                if matches!(sort, Sort::Uninterpreted(_))
                                    && model.bv_model.is_some()
                                {
                                    if let Some(ref euf_model) = model.euf_model {
                                        if let Some(elem) = euf_model.term_values.get(&term_id) {
                                            return EvalValue::Element(elem.clone());
                                        }
                                    }
                                }
                                if self
                                    .bv_exact_select_array_model_conflict(model, args[0], args[1])
                                {
                                    return EvalValue::Unknown;
                                }
                                // (#6191) LIA/LRA model fallback: in AUFLIA, the LIA
                                // solver treats select terms as opaque variables and
                                // assigns integer values. When the array model cannot
                                // resolve the select (no concrete store entry), use
                                // the LIA model's value directly.
                                if matches!(sort, Sort::Int) {
                                    if let Some(ref lia_model) = model.lia_model {
                                        if let Some(val) = lia_model.values.get(&term_id) {
                                            return EvalValue::Rational(BigRational::from(
                                                val.clone(),
                                            ));
                                        }
                                    }
                                    if let Some(ref lra_model) = model.lra_model {
                                        if let Some(val) = lra_model.values.get(&term_id) {
                                            return EvalValue::Rational(val.clone());
                                        }
                                    }
                                }
                                if matches!(sort, Sort::Real) {
                                    if let Some(ref lra_model) = model.lra_model {
                                        if let Some(val) = lra_model.values.get(&term_id) {
                                            return EvalValue::Rational(val.clone());
                                        }
                                    }
                                }
                                // BV model cache fallback (#4087, unified in #5627).
                                let bv_fallback =
                                    self.bv_model_cache_fallback(model, term_id, sort);
                                if !matches!(bv_fallback, EvalValue::Unknown) {
                                    return bv_fallback;
                                }
                                if matches!(sort, Sort::Bool) {
                                    if let Some(b) = self.term_value(
                                        &model.sat_model,
                                        &model.term_to_var,
                                        term_id,
                                    ) {
                                        return EvalValue::Bool(b);
                                    }
                                }
                                // EUF congruence fallback for selects routed as UF
                                // (#anra-select-nonlinear wrong-sat). When arrays are
                                // handled via UF (QF_AUFNRA/QF_AUFNIA → solve_uf_nra/
                                // solve_uf_nia), there is NO array_model: the select
                                // term `(select A i)` lives only in the EUF model as a
                                // function application. An asserted `(= (select A i) c)`
                                // (c a numeric constant) is tracked in
                                // `func_app_const_terms`, so the select's committed
                                // value is `c`. Without this lookup the validation
                                // evaluator returns Unknown for the select, the LRA/NRA
                                // model independently assigns a transitively-equal
                                // variable a DIFFERENT value (e.g. `x = (select A i)`
                                // with `x = 0` while the select pins to `3.0`), and the
                                // resulting internally-inconsistent model escapes as a
                                // wrong SAT because the strict gate can't observe the
                                // contradiction. Resolving the select to its EUF class
                                // constant exposes it: `(= x (select A i))` then
                                // evaluates to a definitive `Bool(false)`, so the array
                                // oracle degrades SAT → Unknown. This is the solver's
                                // OWN committed interpretation (an asserted equality
                                // every model must satisfy), so reading it is sound and
                                // can never manufacture a wrong UNSAT — it only ever
                                // makes a select concrete, never changes a genuine
                                // satisfying assignment that is already consistent.
                                if matches!(sort, Sort::Int | Sort::Real | Sort::BitVec(_)) {
                                    if let Some(ref euf_model) = model.euf_model {
                                        if let Some(&const_term_id) =
                                            euf_model.func_app_const_terms.get(&term_id)
                                        {
                                            let resolved = self.evaluate_term(model, const_term_id);
                                            if !matches!(resolved, EvalValue::Unknown) {
                                                return resolved;
                                            }
                                        }
                                    }
                                }
                                // Asserted-equality fallback (#aufbv-nonbv-elem):
                                // a `(select arr i)` whose element sort is not
                                // bit-blastable (Bool, or another non-arithmetic
                                // sort) gets no value in the BV-backed array
                                // model. When a TOP-LEVEL assertion pins it equal
                                // to a leaf term — `(= seed (select arr i))`, the
                                // shape deductive-checks emits to anchor a slice's head —
                                // resolve the read to that leaf's value. The
                                // equality is asserted (true in every model), so
                                // this is the solver's own committed
                                // interpretation; validation re-checks it, so it
                                // can never manufacture a wrong SAT.
                                //
                                // Confined to the BV-backed solve: the array-theory
                                // paths (QF_AX / QF_AUFLIA) produce a genuine array
                                // model that authoritatively resolves selects, and
                                // must not be second-guessed by this fallback.
                                if model.bv_model.is_some() {
                                    let resolved =
                                        self.resolve_select_via_asserted_equality(model, term_id);
                                    if !matches!(resolved, EvalValue::Unknown) {
                                        return resolved;
                                    }
                                }
                            }
                            result
                        }
                        // Array store is array-sorted; we can't reduce it to a scalar.
                        // But we still need to handle it so select(store(...)) works.
                        "store" if args.len() == 3 => EvalValue::Unknown,
                        // Array else-value. Symbolic defaults are materialized in
                        // the array model before validation; const/store forms
                        // retain their exact structural semantics.
                        "default" if args.len() == 1 => {
                            self.evaluate_array_default(model, term_id, args[0])
                        }
                        // === String operations (ground evaluation) ===
                        // String operations — delegated to eval_string.rs
                        "str.len" | "str.++" | "str.substr" | "str.at" | "str.contains"
                        | "str.prefixof" | "str.suffixof" | "str.<" | "str.<=" | "str.replace"
                        | "str.replace_all" | "str.indexof" | "str.to_int" | "str.from_int"
                        | "str.to_code" | "str.from_code" | "str.is_digit" | "str.to_lower"
                        | "str.to_upper" | "str.in_re" | "str.replace_re"
                        | "str.replace_re_all" => self.evaluate_str_app(model, name, args),
                        // Sequence operations — delegated to eval_seq.rs
                        "seq.unit" | "seq.empty" | "seq.++" | "seq.len" | "seq.nth"
                        | "seq.extract" | "seq.contains" | "seq.prefixof" | "seq.suffixof"
                        | "seq.indexof" | "seq.last_indexof" | "seq.replace"
                        | "seq.replace_all" => self.evaluate_seq_app(model, name, args),
                        // FP operations — delegated to eval_fp.rs
                        "fp.isNaN" | "fp.isInfinite" | "fp.isZero" | "fp.isNormal"
                        | "fp.isSubnormal" | "fp.isPositive" | "fp.isNegative" | "fp.neg"
                        | "fp.abs" | "fp.eq" | "fp.lt" | "fp.leq" | "fp.gt" | "fp.geq"
                        | "fp.add" | "fp.sub" | "fp.mul" | "fp.div" | "fp.rem" | "fp.sqrt"
                        | "fp.min" | "fp.max" | "fp.roundToIntegral" | "fp.fma" | "fp"
                        | "to_fp" | "to_fp_unsigned" | "fp.to_ubv" | "fp.to_sbv" | "fp.to_real"
                        | "fp.to_ieee_bv" | "fp.zero" | "+zero" | "-zero" | "fp.inf" | "+oo"
                        | "-oo" | "fp.nan" | "NaN" => {
                            self.evaluate_fp_app(model, sym, name, args, sort, term_id)
                        }

                        // Uninterpreted function application — delegated to eval_uf.rs
                        _ => self.evaluate_uninterpreted_app(model, sym, args, sort, term_id),
                    }
                }

                // Let bindings should be expanded, but handle just in case
                TermData::Let(_, body) => self.evaluate_term(model, *body),

                // Quantifiers: can't evaluate without full model - return Unknown
                TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => EvalValue::Unknown,
                // All current TermData variants are handled above.
                // This arm is required by #[non_exhaustive] and catches future variants.
                other => unreachable!("unhandled TermData variant in evaluate_term(): {other:?}"),
            }
        }) // stacker::maybe_grow
    }

    /// Decide `distinct` from exact pairwise equality evidence.
    fn eval_values_distinct_exact(values: &[EvalValue]) -> Option<bool> {
        for i in 0..values.len() {
            for j in (i + 1)..values.len() {
                match Self::eval_values_equal_exact(&values[i], &values[j]) {
                    Some(true) => return Some(false),
                    Some(false) => {}
                    None => return None,
                }
            }
        }
        Some(true)
    }

    /// Whether `other` is provably unequal to both possible ITE values.
    fn ite_branches_definitively_exclude(
        other: &EvalValue,
        then_value: &EvalValue,
        else_value: &EvalValue,
    ) -> bool {
        matches!(
            Self::eval_values_equal_exact(other, then_value),
            Some(false)
        ) && matches!(
            Self::eval_values_equal_exact(other, else_value),
            Some(false)
        )
    }

    /// Sound branch-split for an equality `(= a b)` where one operand is an
    /// `(ite c t e)` whose condition `c` does not evaluate to a concrete
    /// boolean.
    ///
    /// Semantics: an `ite` always equals exactly one of its branches. So if the
    /// non-ite operand `x` is provably unequal to BOTH `t` and `e`, then
    /// `(= x (ite c t e))` is `false` no matter what `c` is. We only ever
    /// conclude `false` here — never `true` — so this can soundly turn a
    /// wrong SAT into a rejected (Bool(false)) equality without ever asserting
    /// an equality that might not hold.
    ///
    /// Returns:
    /// - `Some(EvalValue::Bool(false))` when the equality is definitively false
    ///   regardless of the ite condition;
    /// - `None` otherwise (caller keeps its existing Unknown result).
    fn eq_via_ite_branch_split(
        &self,
        model: &Model,
        lhs: TermId,
        rhs: TermId,
    ) -> Option<EvalValue> {
        // Identify which side (if any) is an ite whose condition is not a
        // concrete bool, and take the other side as the comparison value.
        let try_side = |ite_id: TermId, other_id: TermId| -> Option<EvalValue> {
            let TermData::Ite(cond, then_br, else_br) = self.ctx.terms.get(ite_id) else {
                return None;
            };
            // Only split when the condition is genuinely undecided. If it were
            // decidable we would already have selected a branch above.
            if !matches!(self.evaluate_term(model, *cond), EvalValue::Unknown) {
                return None;
            }
            let other = self.evaluate_term(model, other_id);
            if matches!(other, EvalValue::Unknown) {
                return None;
            }
            let then_v = self.evaluate_term(model, *then_br);
            let else_v = self.evaluate_term(model, *else_br);
            // BOTH comparisons require exact negative evidence.  `PartialEq`
            // intentionally maps an undecided algebraic equality to false, so
            // `!=` is not a disequality certificate here; nested Unknowns in
            // sequences have the same problem.
            if Self::ite_branches_definitively_exclude(&other, &then_v, &else_v) {
                Some(EvalValue::Bool(false))
            } else {
                None
            }
        };

        try_side(lhs, rhs).or_else(|| try_side(rhs, lhs))
    }
}

#[cfg(test)]
mod closed_value_graph_tests;

#[cfg(test)]
mod tests;
