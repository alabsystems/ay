// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The fresh, pure, total recursive evaluator.
//!
//! Internal errors distinguish missing model interpretations from refusals and
//! resource exhaustion. Only genuine missing interpretations permit completion;
//! the public API presents every error as [`EvalOutcome::Unevaluable`].

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use crate::{
    array_select, bitvec, seq, value_eq, ArrayValue, EvalOutcome, ModelValue, ModelView,
    ProvenUnconstrainedKind, MAX_EVAL_DEPTH,
};

pub(crate) mod error;
use error::{EvalError, EvalResource, EvalResult};

#[cfg(test)]
#[path = "eval/admission_tests.rs"]
mod admission_tests;

#[cfg(test)]
#[path = "eval/namespace_tests.rs"]
mod namespace_tests;

mod finite_field;
mod functional_arrays;
pub(crate) mod quantifier;
mod scratch_admission;
mod sequence;
mod symbolic_function;
use quantifier::QuantifierState;

#[cfg(test)]
#[path = "eval/select_fold_tests.rs"]
mod select_fold_tests;

#[cfg(test)]
#[path = "eval/resource_fallback_tests.rs"]
mod resource_fallback_tests;

#[cfg(test)]
#[path = "eval/lambda_failure_tests.rs"]
mod lambda_failure_tests;

#[cfg(test)]
#[path = "eval/conditional_array_tests.rs"]
mod conditional_array_tests;

#[cfg(test)]
#[path = "eval/store_key_failure_tests.rs"]
mod store_key_failure_tests;

#[cfg(test)]
#[path = "eval/select_equality_tests.rs"]
mod select_equality_tests;

/// One entry of the per-evaluator uninterpreted-function graph: a function
/// name, the VALUES its arguments evaluated to, and the single result value
/// adopted for that argument-value key. See [`Evaluator::eval_uninterpreted_app`].
type UfGraphEntry = (String, Option<TermId>, Vec<ModelValue>, ModelValue);

/// One entry of the per-evaluator array-`select` graph: the array-expression
/// TERM after authenticated store misses and known conditional branches have
/// been peeled, the index VALUE, and the single element value adopted for that
/// semantic key. See
/// [`Evaluator::eval_select_via_model`].
type SelectGraphEntry = (TermId, ModelValue, ModelValue);

/// One attempt at a lazy read, without caching failures across evaluations.
enum SelectFold {
    Value(ModelValue),
    /// The terminal base was already evaluated unsuccessfully at this depth.
    UnresolvedBase {
        array: TermId,
        reason: EvalError,
    },
    /// Preserve any proved prefix, but do not cross an indeterminate key.
    Reconstruct {
        array: TermId,
    },
}

/// Datatype dispatch is not an error-based probe for ordinary UF semantics.
enum DatatypeEvaluation {
    Value(ModelValue),
    NotDatatype,
    WrongConstructor,
}

/// Compare two value-key tuples for a congruence-graph lookup.
///
/// `value_eq` is deliberately three-valued: in particular, exact algebraic
/// values from different extensions can be semantically equal even when this
/// checker cannot decide that equality.  A graph lookup may skip an entry only
/// after at least one component is PROVABLY different.  Treating an
/// incomparable component as `false` would permit a second result for a key
/// that may be equal to the first, violating function single-valuedness and
/// potentially confirming a wrong model.
///
/// Keep scanning after an incomparable component because a later
/// `Ok(false)` still proves the tuples distinct.  If no component separates
/// them, the unresolved comparison propagates and the gate fails closed before
/// installing another mapping.
pub(crate) fn congruence_keys_equal(
    stored: &[ModelValue],
    candidate: &[ModelValue],
) -> Result<bool, String> {
    if stored.len() != candidate.len() {
        return Ok(false);
    }

    let mut unresolved = None;
    for (left, right) in stored.iter().zip(candidate) {
        match value_eq(left, right) {
            Ok(true) => {}
            Ok(false) => return Ok(false),
            Err(reason) => {
                if unresolved.is_none() {
                    unresolved = Some(reason);
                }
            }
        }
    }

    match unresolved {
        Some(reason) => Err(format!("cannot decide congruence-key equality: {reason}")),
        None => Ok(true),
    }
}

/// Native evaluator-call depth at which projection dispatch fails closed.
///
/// Projection applications are peeled iteratively, but ordinary terms between
/// projections still recurse through [`Evaluator::eval`]. Keep a conservative
/// backstop below the native-stack exhaustion point seen on libtest's small
/// worker stacks. This does not lower [`MAX_EVAL_DEPTH`] for projection-free
/// evaluation, and consecutive projections consume only the shared logical
/// depth budget because they do not add native evaluator frames.
const MAX_PROJECTION_EVAL_CALL_DEPTH: usize = 128;

/// Maximum nesting depth accepted while validating that a model value inhabits
/// the sort of the term it is meant to interpret.
///
/// The walk fails closed before adding another native frame, so a maliciously
/// deep datatype/array/sequence value cannot overflow libtest's small worker
/// stack. Ordinary model witnesses are far shallower than this bound.
const MAX_TYPED_VALUE_DEPTH: usize = 256;

/// Maximum number of value nodes inspected by one typed-inhabitance walk.
///
/// AY's concrete sequence witnesses are capped at 4096 cells and authored
/// datatype collection roots at 1024. This larger shared envelope admits those
/// complete witnesses while bounding work on a model-provided aggregate. An
/// exhausted budget is evidence insufficiency (`CannotConfirm`), never an
/// equality decision.
const MAX_TYPED_VALUE_WORK: usize = 8192;

/// Maximum typed value-pair comparisons performed by one equality decision.
///
/// Array equality searches ordered override lists and deduplicates semantic
/// keys, both of which are quadratic for an index sort that
/// [`Evaluator::encode_canonical_index_key`] cannot canonically encode. Nested
/// aggregate keys multiply that work further. Meter every recursive pair
/// comparison under one shared budget so an authenticated 8192-node value still
/// cannot trigger unbounded CPU. Exhaustion is unevaluable and therefore becomes
/// `CannotConfirm`.
///
/// The budget is deliberately NOT the knob for large arrays. A total model
/// interpretation over a `(_ BitVec w)` index carries `2^w` store entries, so
/// the rescan grows as `4 * (2^w)^2` and no constant survives the next width;
/// canonical keys make that shape linear instead.
const MAX_TYPED_EQUALITY_COMPARISONS: usize = 65_536;

/// Semantic-key tables for one array-equality decision, built only when the
/// index sort is canonically encodable.
///
/// `visit_order` reproduces the exact sequence the ordered union loop walks --
/// every left store key in store order, then every right one, duplicates and
/// all -- so the fast lane reports the same first unevaluable element
/// comparison as the rescan it replaces.
struct CanonicalIndexTables {
    /// Encoded key of every store entry of the left operand then the right one,
    /// in store order.
    visit_order: Vec<String>,
    /// Encoded key -> position in `left.store` of the LAST entry holding it.
    left: HashMap<String, usize>,
    /// Encoded key -> position in `right.store` of the LAST entry holding it.
    right: HashMap<String, usize>,
}

/// Meter only bitvector materialization that feeds FP decoding. Ordinary
/// legacy BV evaluation retains its existing work admission policy.
struct FpInputGuard<'a> {
    depth: &'a Cell<usize>,
    restore: usize,
}
impl<'a> FpInputGuard<'a> {
    fn enter(depth: &'a Cell<usize>) -> EvalResult<Self> {
        let restore = depth.get();
        let next = restore
            .checked_add(1)
            .ok_or_else(|| EvalError::resource(EvalResource::Depth, "FP input nesting overflow"))?;
        depth.set(next);
        Ok(Self { depth, restore })
    }
}
impl Drop for FpInputGuard<'_> {
    fn drop(&mut self) {
        self.depth.set(self.restore);
    }
}

/// The prefix every sequence-class carrier minted for `sort` must carry.
///
/// Mirrors `ay_dpll::executor::model::independent_gate::sequence_euf_class_value`,
/// which is the sole producer of these tokens. The dependency points the wrong
/// way for a shared constant (`ay-model-check` cannot depend on `ay-dpll`), so
/// the coupling is pinned from both sides instead: a producer-side format
/// change stops matching here, which fails closed rather than admitting an
/// unauthenticated value.
fn sequence_euf_class_prefix(sort: &Sort) -> String {
    format!("@ay-seq-euf-class:{sort:?}:")
}

/// Restores the local binding stack on every exit, including unwinding.
///
/// The evaluator is intentionally reusable across all assertions in one gate
/// pass, so lambda and quantifier bindings must never leak into a later assertion.
struct LocalBindingGuard<'a> {
    bindings: &'a RefCell<Vec<LocalBinding>>,
    restore_len: usize,
}

/// Lambda binders name one term; quantifiers bind a lexical variable name.
/// Both use one ordered stack so either kind can shadow the other.
enum LocalVariable {
    Term(TermId),
    Named(String, Sort),
}

struct LocalBinding {
    variable: LocalVariable,
    value: ModelValue,
}

impl LocalBinding {
    fn binds(&self, terms: &TermStore, term: TermId) -> bool {
        match &self.variable {
            LocalVariable::Term(bound) => *bound == term,
            LocalVariable::Named(name, _) => {
                matches!(terms.get(term), TermData::Var(candidate, _) if candidate == name)
            }
        }
    }
}

/// Restores the active native evaluator-call count on every exit.
struct EvalCallDepthGuard<'a> {
    active_calls: &'a Cell<usize>,
}

impl Drop for EvalCallDepthGuard<'_> {
    fn drop(&mut self) {
        self.active_calls
            .set(self.active_calls.get().saturating_sub(1));
    }
}

impl Drop for LocalBindingGuard<'_> {
    fn drop(&mut self) {
        self.bindings.borrow_mut().truncate(self.restore_len);
    }
}

/// A resource callback cannot recursively enter this same evaluator while a
/// borrowed memo/graph/binding value is being admitted. Fresh evaluators keep
/// their independent graph state and can share the owner's ledger normally.
struct AdmissionCallbackGuard<'a>(&'a Cell<bool>);

impl Drop for AdmissionCallbackGuard<'_> {
    fn drop(&mut self) {
        self.0.set(false);
    }
}

/// A fresh evaluator bound to a term store and a model view.
pub struct Evaluator<'a> {
    admission_refused: RefCell<Option<String>>,
    admission_callback_active: Cell<bool>,
    admission_was_enabled: Cell<bool>,
    functional_work_left: Cell<usize>,
    exact_fp_touched: Cell<bool>,
    fp_input_depth: Cell<usize>,
    functional_capture_depth: Cell<usize>,
    terms: &'a TermStore,
    model: &'a dyn ModelView,
    /// Per-evaluator memo of SUCCESSFULLY computed term values
    /// (#gate-eval-memo): `term -> (value, deepest entry depth at which the
    /// evaluation succeeded)`. The assertions the gate re-checks are shared
    /// DAGs (common guard prefixes, let-shared subterms recur across dozens of
    /// assertions), and `eval` is a plain structural recursion, so without a
    /// memo each shared subterm is re-walked once per occurrence.
    ///
    /// EXACT-BEHAVIOR-PRESERVING, argued in two parts:
    ///
    /// 1. VALUE STABILITY. For a fixed model view, re-evaluating a term always
    ///    yields the value of its first evaluation: every node is a pure
    ///    function of its children's values except UF applications and
    ///    unresolved array reads, whose first evaluation ADOPTS a value into
    ///    `uf_graph`/`select_graph` keyed by argument values — entries are
    ///    never removed or overwritten, so a re-walk finds the identical
    ///    adopted value (and adds nothing: the first walk already inserted
    ///    every key along the value path, and the deterministic short-circuit
    ///    order revisits exactly that path). Returning the memoized value is
    ///    therefore bit-identical to a re-walk, including graph side effects.
    ///
    /// 2. DEPTH-BUDGET GUARD. A success memoized at entry depth `d` proves the
    ///    subtree evaluates within `MAX_EVAL_DEPTH` when started at depth `d`,
    ///    hence at any shallower depth too — the memo is only consulted when
    ///    `current depth <= d`, so a memo hit can never return `Ok` where a
    ///    fresh walk would have failed the depth limit (and vice versa).
    ///
    /// `Err` results are NEVER memoized: an `Err` can be depth-dependent
    /// (recursion limit) or cycle-guard-dependent (an in-flight array/datatype
    /// leaf resolution in the view), so it must be recomputed each time —
    /// rather than turning one failed attempt into a permanent refusal.
    memo: RefCell<ay_core::kani_compat::DetHashMap<TermId, (ModelValue, usize)>>,
    /// Value-keyed interpretation the gate builds for uninterpreted functions
    /// as it evaluates. An uninterpreted function is single-valued, so two
    /// applications whose ARGUMENTS evaluate to equal values must return the
    /// same value; this graph enforces that (first application to reach a given
    /// `(name, arg-values)` key fixes the value for the whole evaluation). It
    /// is what lets the gate catch a model that collapses two congruent
    /// applications' arguments to the same value while pinning them to
    /// different results — the exact QF_UFLIA / array-select wrong-model class.
    uf_graph: RefCell<Vec<UfGraphEntry>>,
    /// Value-keyed interpretation the gate builds for array `select` reads whose
    /// array operand it could not resolve to a concrete `(default, finite-store)`
    /// value (a partial/unreconstructable array leaf). `select` over an array is
    /// a single-valued function of the index, so two reads of the SAME array term
    /// at index values that evaluate equal must denote the same element; this
    /// graph enforces that (first read to reach a given `(array-term,
    /// index-value)` key fixes the element for the whole evaluation). It is the
    /// array analogue of `uf_graph`, and is what lets the gate expose — rather
    /// than honour — an array model that pins two coincident reads to different
    /// values, closing the array-`select` wrong-model class even when the full
    /// array cannot be reconstructed.
    select_graph: RefCell<Vec<SelectGraphEntry>>,
    /// Scoped values while beta-reducing a `lambda-array` read or enumerating
    /// a finite quantifier. The most recent binding wins, so nested scopes are
    /// handled naturally. The term-value memo and model-backed application
    /// fallbacks are explicitly bypassed for terms that depend on an active
    /// binding because neither per-TermId cache is indexed by a lambda
    /// environment. Binder-independent terms remain valid model observations
    /// inside an unrelated lambda body.
    local_bindings: RefCell<Vec<LocalBinding>>,
    symbolic_definitions: RefCell<Vec<(Symbol, Vec<TermId>, TermId, TermId)>>,
    symbolic_active: RefCell<Vec<Symbol>>,
    /// Number of currently active [`Self::eval`] calls. Projection dispatch
    /// uses this only as a native-stack safety backstop; SMT term depth remains
    /// governed by [`MAX_EVAL_DEPTH`].
    active_eval_calls: Cell<usize>,
    /// One resource envelope for all finite quantifiers checked by this
    /// evaluator, including nested bodies and later assertions.
    quantifier_state: QuantifierState,
}

impl<'a> Evaluator<'a> {
    // Dedicated FP callbacks obey the SAME reentry exclusion as shared
    // evaluation admission, including while memo/graph DATA is borrowed.
    fn with_exact_fp_callback(&self, call: impl FnOnce() -> EvalResult<()>) -> EvalResult<()> {
        if self.admission_callback_active.get() {
            return Err(self.reentrant_admission_error());
        }
        if let Some(error) = self.prior_admission_refusal() {
            return Err(error);
        }
        self.admission_callback_active.set(true);
        let guard = AdmissionCallbackGuard(&self.admission_callback_active);
        let result = call();
        drop(guard);
        match result {
            Err(error) => Err(self.admission_error(error.to_string())),
            Ok(()) if self.has_admission_refusal() => {
                Err(self.admission_error("reentrant evaluation during exact FP admission callback"))
            }
            Ok(()) => Ok(()),
        }
    }

    fn poll_exact_fp(&self) -> EvalResult<()> {
        self.with_exact_fp_callback(|| {
            if self.model.exact_fp_interrupted() {
                Err("exact FP original owner interrupted".into())
            } else {
                Ok(())
            }
        })
    }

    fn charge_exact_fp_work(&self, bytes: usize) -> EvalResult<()> {
        self.charge_exact_fp_budget(bytes)?;
        self.with_exact_fp_callback(|| {
            self.model
                .charge_exact_fp_work(bytes.max(1))
                .map_err(EvalError::from)
        })?;
        self.poll_exact_fp()
    }

    fn admit_exact_fp_work(&self, work: usize, storage: usize) -> EvalResult<()> {
        let admission_enabled = self.admission_enabled()?;
        self.charge_exact_fp_budget(work)?;
        self.with_exact_fp_callback(|| {
            self.model
                .admit_exact_fp_work(work.max(1), storage)
                .map_err(EvalError::from)
        })?;
        self.poll_exact_fp()?;
        if self.admission_enabled()? != admission_enabled {
            return Err(self.admission_error("exact FP admission activation changed"));
        }
        Ok(())
    }

    fn charge_exact_fp_budget(&self, bytes: usize) -> EvalResult<()> {
        self.exact_fp_touched.set(true);
        let amount = bytes.max(1);
        self.poll_exact_fp()?;
        let Some(left) = self.functional_work_left.get().checked_sub(amount) else {
            self.functional_work_left.set(0);
            return Err(EvalError::resource(
                EvalResource::Work,
                "exact FP work exhausted",
            ));
        };
        self.functional_work_left.set(left);
        self.charge_quantifier_work(amount)?;
        Ok(())
    }

    fn charge_exact_fp_value(&self, value: &ModelValue) -> EvalResult<()> {
        if matches!(value, ModelValue::FloatingPointExact { .. }) {
            self.charge_exact_fp_work(crate::fp_exact::bytes(value)?)?;
        }
        Ok(())
    }

    fn checked_fp_result(
        &self,
        term: TermId,
        result: EvalResult<ModelValue>,
    ) -> EvalResult<ModelValue> {
        if let Ok(
            value @ (ModelValue::FloatingPoint { .. } | ModelValue::FloatingPointExact { .. }),
        ) = &result
        {
            self.ensure_value_inhabits_sort(value, self.terms.sort(term))?;
        }
        result
    }
    /// Typed semantic keys retain array cardinality evidence and charge every
    /// nested variable-sized FP comparison through this evaluator's owner.
    /// A mere aggregate preflight cannot account an untyped quadratic rescan.
    fn congruence_keys_equal_at_sorts(
        &self,
        stored: &[ModelValue],
        candidate: &[ModelValue],
        sorts: &[&Sort],
    ) -> Result<bool, String> {
        if stored.len() != candidate.len() || stored.len() != sorts.len() {
            return congruence_keys_equal(stored, candidate);
        }
        let mut unresolved = None;
        for ((left, right), &sort) in stored.iter().zip(candidate).zip(sorts) {
            self.ensure_value_inhabits_sort(left, sort)
                .map_err(|error| error.to_string())?;
            self.ensure_value_inhabits_sort(right, sort)
                .map_err(|error| error.to_string())?;
            let mut comparison_work = 0;
            match self.value_eq_for_typed_values(left, right, sort, &mut comparison_work) {
                Ok(true) => {}
                Ok(false) => return Ok(false),
                Err(error @ EvalError::Resource { .. }) => return Err(error.to_string()),
                Err(reason) => {
                    if unresolved.is_none() {
                        unresolved = Some(reason.to_string());
                    }
                }
            }
        }
        match unresolved {
            Some(reason) => Err(format!("cannot decide congruence-key equality: {reason}")),
            None => Ok(true),
        }
    }

    /// Create an evaluator over `terms`, reading leaf values from `model`.
    #[must_use]
    pub fn new(terms: &'a TermStore, model: &'a dyn ModelView) -> Self {
        Self {
            admission_refused: RefCell::new(None),
            admission_callback_active: Cell::new(false),
            admission_was_enabled: Cell::new(false),
            functional_work_left: Cell::new(crate::MODEL_DATA_WORK_LIMIT),
            exact_fp_touched: Cell::new(false),
            fp_input_depth: Cell::new(0),
            functional_capture_depth: Cell::new(0),
            terms,
            model,
            uf_graph: RefCell::new(Vec::new()),
            select_graph: RefCell::new(Vec::new()),
            local_bindings: RefCell::new(Vec::new()),
            symbolic_definitions: RefCell::new(Vec::new()),
            symbolic_active: RefCell::new(Vec::new()),
            memo: RefCell::new(ay_core::kani_compat::DetHashMap::default()),
            active_eval_calls: Cell::new(0),
            quantifier_state: QuantifierState::default(),
        }
    }

    /// Evaluate `term` under the model, surfacing the outcome.
    #[must_use]
    pub fn evaluate(&self, term: TermId) -> EvalOutcome {
        if let Some(error) = self.prior_admission_refusal() {
            return EvalOutcome::Unevaluable(error.to_string());
        }
        if self.model.functional_array_interrupted()
            || (self.exact_fp_touched.get() && self.poll_exact_fp().is_err())
        {
            return EvalOutcome::Unevaluable("model original owner interrupted".into());
        }
        // A nested evaluator may refuse through the same owner ledger while an
        // owned-value callback returns None. Preserve both admission and the
        // original functional owner at the closing publication fence.
        let result = self.eval(term, 0);
        match self.admit_evaluation(0, 0).and(result) {
            // A memo hit still belongs to this original request. It cannot
            // publish a retained value after that owner has stopped.
            Ok(_)
                if self.model.functional_array_interrupted()
                    || (self.exact_fp_touched.get() && self.poll_exact_fp().is_err()) =>
            {
                EvalOutcome::Unevaluable("model original owner interrupted".into())
            }
            Ok(v) => EvalOutcome::Value(v),
            Err(reason) => EvalOutcome::Unevaluable(reason.to_string()),
        }
    }

    fn reentrant_admission_error(&self) -> EvalError {
        // The outer callback frame performs the owner notification after its
        // guard drops. Calling another owner hook here could recurse forever.
        let reason =
            self.retain_admission_refusal("reentrant evaluation during admission callback".into());
        EvalError::resource(EvalResource::Work, reason)
    }

    fn has_admission_refusal(&self) -> bool {
        self.admission_refused.borrow().is_some()
    }

    fn prior_admission_refusal(&self) -> Option<EvalError> {
        self.admission_refused
            .borrow()
            .as_ref()
            .map(|reason| EvalError::resource(EvalResource::Work, reason.clone()))
    }

    fn retain_admission_refusal(&self, reason: String) -> String {
        self.admission_refused
            .borrow_mut()
            .get_or_insert(reason)
            .clone()
    }

    fn admission_error(&self, reason: impl Into<String>) -> EvalError {
        // Preserve the first cause through later publication/memo fences, and
        // drop its borrow before invoking any model notification callback.
        let reason = self.retain_admission_refusal(reason.into());
        if self.admission_was_enabled.get() && !self.admission_callback_active.replace(true) {
            let _guard = AdmissionCallbackGuard(&self.admission_callback_active);
            self.model.refuse_evaluation_work(&reason);
        }
        EvalError::resource(EvalResource::Work, reason)
    }

    fn admission_enabled(&self) -> EvalResult<bool> {
        if self.admission_callback_active.get() {
            return Err(self.reentrant_admission_error());
        }
        if let Some(error) = self.prior_admission_refusal() {
            return Err(error);
        }
        let enabled = {
            self.admission_callback_active.set(true);
            let _guard = AdmissionCallbackGuard(&self.admission_callback_active);
            self.model.has_evaluation_admission()
        };
        self.admission_was_enabled
            .set(self.admission_was_enabled.get() || enabled);
        if self.has_admission_refusal() {
            return Err(self.admission_error("reentrant evaluation during admission callback"));
        }
        Ok(enabled)
    }

    fn admit_evaluation(&self, work: usize, bytes: usize) -> EvalResult<()> {
        if !self.admission_enabled()? {
            return Ok(());
        }
        let result = {
            self.admission_callback_active.set(true);
            let _guard = AdmissionCallbackGuard(&self.admission_callback_active);
            self.model.admit_evaluation_work(work, bytes)
        };
        match result {
            Err(reason) => Err(self.admission_error(reason)),
            Ok(()) if self.has_admission_refusal() => {
                Err(self.admission_error("reentrant evaluation during admission callback"))
            }
            Ok(()) => Ok(()),
        }
    }

    fn admit_value(&self, value: &ModelValue) -> EvalResult<()> {
        if !self.admission_enabled()? {
            return self.admit_evaluation(0, 0);
        }
        crate::admit_model_value_work(value, &mut |work, bytes| {
            self.admit_evaluation(work, bytes)
                .map_err(|error| error.to_string())
        })
        .map_err(|reason| self.admission_error(reason))
    }

    fn clone_value(&self, value: &ModelValue) -> EvalResult<ModelValue> {
        self.admit_value(value)?;
        Ok(value.clone())
    }

    fn admit_array(&self, array: &ArrayValue) -> EvalResult<()> {
        if !self.admission_enabled()? {
            return self.admit_evaluation(0, 0);
        }
        self.admit_value(&array.default)?;
        self.admit_evaluation(
            array.store.len(),
            array
                .store
                .len()
                .checked_mul(size_of::<(ModelValue, ModelValue)>())
                .ok_or_else(|| self.admission_error("array copy accounting overflow"))?,
        )?;
        for (index, value) in &array.store {
            self.admit_value(index)?;
            self.admit_value(value)?;
        }
        Ok(())
    }

    fn array_select_admitted(
        &self,
        array: &ArrayValue,
        index: &ModelValue,
    ) -> EvalResult<ModelValue> {
        self.admit_symbolic_array_read(array, index)?;
        // The free helper clones its selected member. Admit all possible source
        // members before entering it; equality semantics are unchanged.
        self.admit_array(array)?;
        array_select(array, index).map_err(EvalError::from)
    }

    /// Core recursive evaluation. `depth` is the current term's depth; children
    /// are evaluated at `depth + 1`. Exceeding [`MAX_EVAL_DEPTH`] fails closed.
    ///
    /// Memoized over the shared-DAG assertions (see the `memo` field for the
    /// exact-behavior-preservation argument): a hit is taken only when the
    /// stored success depth is at least the current depth, and only `Ok`
    /// results are stored.
    fn eval(&self, mut term: TermId, mut depth: usize) -> EvalResult<ModelValue> {
        if self.admission_callback_active.get() {
            return Err(self.reentrant_admission_error());
        }
        self.admit_evaluation(1, 0)?;
        if self.functional_capture_depth.get() != 0 || self.model.has_functional_arrays() {
            let scalar_bytes = match self.terms.sort(term) {
                Sort::BitVec(sort) => (sort.width as usize).div_ceil(8),
                _ => 0,
            };
            self.charge_functional_work(1 + scalar_bytes)?;
        }
        self.charge_quantifier_work(1)?;
        // This increment is paired one-for-one with `EvalCallDepthGuard::drop`.
        let active_calls = self.active_eval_calls.get().checked_add(1).ok_or_else(|| {
            EvalError::resource(EvalResource::Depth, "evaluator call depth overflow")
        })?;
        self.active_eval_calls.set(active_calls);
        let _call_depth_guard = EvalCallDepthGuard {
            active_calls: &self.active_eval_calls,
        };

        // A checked projection is a total symbolic interpretation. Peel it in
        // this SAME evaluator so the selected argument observes the current
        // UF/select graphs, memo, logical depth budget, and lambda bindings.
        // Iteration avoids adding one native Rust frame per projection while
        // retaining one depth edge per beta reduction. Projection lookup must
        // precede the TermId-keyed memo so symbolic definitions cannot be
        // shadowed by a per-application value.
        loop {
            self.charge_quantifier_work(1)?;
            if depth > MAX_EVAL_DEPTH {
                return Err(EvalError::resource(
                    EvalResource::Depth,
                    format!("recursion depth limit {MAX_EVAL_DEPTH} exceeded"),
                ));
            }
            let TermData::App(_, args) = self.terms.get(term) else {
                break;
            };
            if self.admission_enabled()? {
                let bytes = args
                    .len()
                    .checked_mul(size_of::<ModelValue>())
                    .ok_or_else(|| self.admission_error("application edge accounting overflow"))?;
                self.admit_evaluation(args.len(), bytes)?;
            }
            let Some(projected_argument) = self
                .model
                .projection_argument(term)
                .map_err(|error| error.to_string())?
            else {
                break;
            };
            if active_calls > MAX_PROJECTION_EVAL_CALL_DEPTH {
                return Err(EvalError::resource(
                    EvalResource::Depth,
                    format!(
                        "projection recursion depth limit {MAX_PROJECTION_EVAL_CALL_DEPTH} exceeded"
                    ),
                ));
            }
            let selected = args.get(projected_argument).copied().ok_or_else(|| {
                format!(
                    "projection selects argument {projected_argument}, but application arity is {}",
                    args.len()
                )
            })?;
            let selected_sort = self.terms.sort(selected);
            let result_sort = self.terms.sort(term);
            if selected_sort != result_sort {
                return Err(format!(
                    "projection selected argument sort {selected_sort:?} does not match result sort {result_sort:?}"
                ).into());
            }
            self.admit_evaluation(1, 0)?;
            term = selected;
            depth += 1;
        }

        // Constants are cheaper to recompute than to cache (their evaluation
        // is one clone either way). A term depending on an active lambda
        // binding can denote a different value in each beta environment, so a
        // TermId-only memo entry would be an unsound cross-instance reuse.
        if matches!(self.terms.get(term), TermData::Const(_))
            || self.term_depends_on_local_binding(term)?
        {
            return self.checked_fp_result(term, self.eval_uncached(term, depth));
        }
        let hit = self
            .memo
            .borrow()
            .get(&term)
            .is_some_and(|(_, stored_depth)| depth <= *stored_depth);
        if hit {
            self.validate_symbolic_currency()?;
        }
        if let Some((v, d)) = self.memo.borrow().get(&term) {
            if depth <= *d {
                // Aggregate Arc-backed FP fields are retained DATA. Native
                // shared admission prices copies; FP field consumption keeps
                // its own scalar/typed-operation checkpoint.
                if matches!(
                    v,
                    ModelValue::FloatingPoint { .. } | ModelValue::FloatingPointExact { .. }
                ) {
                    self.ensure_value_inhabits_sort(v, self.terms.sort(term))?;
                }
                return self.clone_value(v);
            }
        }
        let result = self.checked_fp_result(term, self.eval_uncached(term, depth));
        if let Ok(v) = &result {
            let needs_copy = self
                .memo
                .borrow()
                .get(&term)
                .is_none_or(|(_, d)| *d < depth);
            if needs_copy {
                // The callback and copy run before taking a mutable borrow.
                // Recheck the condition afterward rather than relying on a
                // pre-callback view of the memo.
                let copied = self.clone_value(v)?;
                let mut memo = self.memo.borrow_mut();
                match memo.get(&term) {
                    Some((_, d)) if *d >= depth => {}
                    _ => {
                        memo.insert(term, (copied, depth));
                    }
                }
            }
        }
        result
    }

    /// Uncached body of [`Self::eval`]; recursive calls go back through the
    /// memoized wrapper so shared subterms are computed once.
    fn eval_uncached(&self, term: TermId, depth: usize) -> EvalResult<ModelValue> {
        if depth > MAX_EVAL_DEPTH {
            return Err(EvalError::resource(
                EvalResource::Depth,
                format!("recursion depth limit {MAX_EVAL_DEPTH} exceeded"),
            ));
        }
        // Declaration identity precedes spelling and result-sort dispatch.
        // In particular a registered `ff.mul` is a UF even at a field sort;
        // a committed model for `and` cannot be replaced by Boolean AND.
        if let TermData::App(Symbol::Named(name), args) = self.terms.get(term) {
            self.admit_evaluation(name.len(), 0)?;
            if self.terms.is_declared_function(name) {
                const REASON: &str = "registered function identity";
                self.admit_evaluation(1, REASON.len())?;
                return self.eval_uninterpreted_app(
                    term,
                    name,
                    args,
                    depth,
                    REASON.to_owned(),
                    None,
                    |value| self.ensure_value_inhabits_sort(value, self.terms.sort(term)),
                );
            }
        }
        if matches!(self.terms.sort(term), Sort::FiniteField(_)) {
            return self.eval_finite_field(term, depth);
        }
        match self.terms.get(term) {
            TermData::Const(c) => {
                if let Constant::BitVec { value, width } = c {
                    if self.fp_input_depth.get() != 0 {
                        let bits = if value.is_negative() || value.bits() > u64::from(*width) {
                            value.bits().max(u64::from(*width))
                        } else {
                            value.bits()
                        };
                        self.charge_exact_fp_work(
                            usize::try_from(bits.div_ceil(8))
                                .map_err(|_| "bitvector input exceeds address space")?,
                        )?;
                    }
                }
                self.eval_const(c)
            }
            TermData::Var(name, _) => {
                if let Some(value) = self.local_binding(term)? {
                    return Ok(value);
                }
                if let Some(value) = self.model.leaf_value(term) {
                    // The owner admits its own clone before returning this value;
                    // admit subsequent evaluator walks/copies independently.
                    self.admit_value(&value)?;
                    return Ok(value);
                }
                // A nullary constructor is determined structurally in every model.
                if let Some(dt) = self.dt_of_sort(&self.terms.sort(term).clone()) {
                    if let Some(ctor) = dt
                        .constructors
                        .iter()
                        .find(|ctor| ctor.name == *name && ctor.fields.is_empty())
                    {
                        self.admit_evaluation(1, ctor.name.len())?;
                        return Ok(ModelValue::Datatype {
                            ctor: ctor.name.clone(),
                            args: Vec::new(),
                        });
                    }
                }
                Err(EvalError::ModelUnavailable(format!(
                    "model does not pin this leaf: {name} : {:?}",
                    self.terms.sort(term)
                )))
            }
            TermData::Not(inner) => Ok(ModelValue::Bool(!self.eval_bool(*inner, depth + 1)?)),
            TermData::Ite(c, t, e) => {
                let selected = self.conditional_branch(term, *c, *t, *e, depth)?;
                self.eval(selected, depth + 1)
            }
            TermData::App(sym, args) => match sym {
                Symbol::Named(name) => self.eval_named(term, name, args, depth),
                Symbol::Indexed(name, indices) => {
                    let _inputs = if matches!(name.as_str(), "to_fp" | "to_fp_unsigned") {
                        Some(FpInputGuard::enter(&self.fp_input_depth)?)
                    } else {
                        None
                    };
                    // `(_ NaN eb sb)`, `(_ +zero eb sb)`, … are FP VALUES, not
                    // bitvector operators. Routing every indexed symbol to
                    // `bitvec::eval_indexed` made the gate report "unsupported
                    // indexed bitvector operator NaN" and refuse to confirm the
                    // model, so a correct `sat` was published as `unknown`.
                    if args.is_empty() {
                        if let Some(bytes) = crate::fp_exact::special_work(name, indices) {
                            self.charge_exact_fp_work(bytes.saturating_mul(4))?;
                        }
                        if let Some(value) = fp_special_constant(name, indices) {
                            return Ok(value);
                        }
                    }
                    // The ROUNDING conversions take a leading rounding mode,
                    // which is a nullary symbol no model pins — so their first
                    // operand must be resolved syntactically, BEFORE the
                    // blanket `eval_all` below would try to look it up as a
                    // leaf and fail. Each reduces to one correctly rounded
                    // conversion of an exact rational (`crate::fp`).
                    if args.len() == 2 {
                        if let Some(unsigned) = match name.as_str() {
                            "to_fp" => Some(false),
                            "to_fp_unsigned" => Some(true),
                            _ => None,
                        } {
                            let [eb, sb] = <[u32; 2]>::try_from(indices.as_slice())
                                .map_err(|_| "to_fp expects two indices".to_string())?;
                            let rm = self.eval_rounding_mode(args[0], depth)?;
                            let value = self.eval_operand(args[1], depth + 1)?;
                            if self.terms.sort(term) != &Sort::FloatingPoint(eb, sb) {
                                return Err("to_fp result sort disagrees with indices".into());
                            }
                            let scans = crate::fp_exact::conversion_scan_work(&value)?;
                            self.admit_exact_fp_work(scans, 0)?;
                            let source_matches = match (&value, self.terms.sort(args[1])) {
                                (ModelValue::Int(_), Sort::Int | Sort::Real)
                                | (ModelValue::Real(_), Sort::Real) => true,
                                (ModelValue::BitVec { width, .. }, Sort::BitVec(expected)) => {
                                    *width == expected.width
                                }
                                (
                                    ModelValue::FloatingPoint {
                                        exponent_bits,
                                        significand_bits,
                                        ..
                                    }
                                    | ModelValue::FloatingPointExact {
                                        exponent_bits,
                                        significand_bits,
                                        ..
                                    },
                                    Sort::FloatingPoint(e, s),
                                ) => exponent_bits == e && significand_bits == s,
                                _ => false,
                            };
                            if !source_matches {
                                return Err("to_fp payload disagrees with operand sort".into());
                            }
                            let interpretation = if unsigned {
                                crate::fp_exact::ConversionInterpretation::Unsigned
                            } else {
                                crate::fp_exact::ConversionInterpretation::Signed
                            };
                            let plan = crate::fp_exact::conversion_plan(
                                &value,
                                interpretation,
                                eb,
                                sb,
                                rm,
                            )
                            .map_err(|reason| EvalError::resource(EvalResource::Work, reason))?;
                            self.quantifier_state
                                .admit_model_data_storage(plan.storage)?;
                            self.admit_exact_fp_work(plan.work, plan.storage)?;
                            self.charge_exact_fp_work(0)?;
                            let result = plan.materialize();
                            self.charge_exact_fp_work(0)?;
                            return result.map_err(EvalError::from);
                        }
                        if let Some(unsigned) = match name.as_str() {
                            "fp.to_sbv" => Some(false),
                            "fp.to_ubv" => Some(true),
                            _ => None,
                        } {
                            let [width] = <[u32; 1]>::try_from(indices.as_slice())
                                .map_err(|_| "fp.to_sbv/to_ubv expects one index".to_string())?;
                            return self.eval_fp_to_bv(term, name, unsigned, width, args, depth);
                        }
                    }
                    let vals = self.eval_all(args, depth)?;
                    // `((_ to_fp eb sb) <bv>)` is a BIT REINTERPRET, not a
                    // bitvector operator: it reads an `eb + sb`-wide word as the
                    // IEEE fields of an FP value. No rounding is involved, so
                    // the gate can do it exactly and INDEPENDENTLY — it is pure
                    // bit-splitting, sharing no code with the solver.
                    //
                    // The two-operand ROUNDING forms (`(_ to_fp eb sb) <rm>
                    // <real|bv|fp>` and `to_fp_unsigned`) are handled ABOVE, by
                    // `crate::fp::to_fp_rounded`. They used to decline here on
                    // the grounds that "an independent gate must not confirm a
                    // model using the same rounding routine that produced it,
                    // and an approximate reimplementation could confirm a WRONG
                    // model". The first half is the real constraint and is
                    // honoured — nothing in this crate calls into the solver's
                    // FP code. The second half does not apply, because
                    // `crate::fp` rounds by comparing exact `BigRational`s
                    // against exact half-way points; see that module's header.
                    if name == "to_fp" && vals.len() == 1 {
                        if let ModelValue::BitVec { value, .. } = &vals[0] {
                            self.charge_exact_fp_work(
                                usize::try_from(value.bits().div_ceil(8))
                                    .map_err(|_| "FP bits exceed address space")?
                                    .saturating_mul(8),
                            )?;
                        }
                        if let Some(value) = fp_from_ieee_bits(indices, &vals[0]) {
                            return Ok(value);
                        }
                    }
                    bitvec::eval_indexed(name, indices, &vals).map_err(EvalError::from)
                }
                _ => Err("unsupported symbol kind".into()),
            },
            // A `let` should have been expanded before reaching the gate. An
            // empty binding list is harmless to descend into; a non-empty one
            // binds names we cannot faithfully resolve ⇒ fail closed.
            TermData::Let(bindings, body) => {
                if bindings.is_empty() {
                    self.eval(*body, depth + 1)
                } else {
                    Err("unexpanded let binding".into())
                }
            }
            TermData::Forall(bindings, body, _) => self.eval_finite_quantifier(
                quantifier::QuantifierKind::Forall,
                bindings,
                *body,
                depth,
            ),
            TermData::Exists(bindings, body, _) => self.eval_finite_quantifier(
                quantifier::QuantifierKind::Exists,
                bindings,
                *body,
                depth,
            ),
            _ => Err("unsupported term kind".into()),
        }
    }

    fn eval_bool(&self, term: TermId, depth: usize) -> EvalResult<bool> {
        match self.eval_operand(term, depth)? {
            ModelValue::Bool(b) => Ok(b),
            _ => Err("expected a boolean value".into()),
        }
    }

    /// A missing test does not make the conditional's result an unconstrained
    /// model leaf. Authenticate even the unselected branch before choosing.
    fn conditional_branch(
        &self,
        term: TermId,
        condition: TermId,
        positive: TermId,
        negative: TermId,
        depth: usize,
    ) -> EvalResult<TermId> {
        if self.terms.sort(condition) != &Sort::Bool
            || self.terms.sort(positive) != self.terms.sort(term)
            || self.terms.sort(negative) != self.terms.sort(term)
        {
            return Err("malformed conditional condition or branch sort".into());
        }
        let choose_positive =
            self.eval_bool(condition, depth + 1)
                .map_err(|error| match error {
                    EvalError::ModelUnavailable(reason) => {
                        EvalError::Refused(format!("conditional test is unavailable: {reason}"))
                    }
                    other => other,
                })?;
        Ok(if choose_positive { positive } else { negative })
    }

    fn eval_all(&self, args: &[TermId], depth: usize) -> EvalResult<Vec<ModelValue>> {
        args.iter()
            .map(|&a| self.eval_operand(a, depth + 1))
            .collect()
    }

    fn eval_operand(&self, term: TermId, depth: usize) -> EvalResult<ModelValue> {
        self.eval(term, depth).map_err(EvalError::operand)
    }

    fn eval_const(&self, c: &Constant) -> EvalResult<ModelValue> {
        if self.admission_enabled()? {
            crate::evaluation_work::admit_constant_work(c, &mut |work, bytes| {
                self.admit_evaluation(work, bytes)
                    .map_err(|error| error.to_string())
            })
            .map_err(|reason| self.admission_error(reason))?;
        }
        match c {
            Constant::Bool(b) => Ok(ModelValue::Bool(*b)),
            Constant::Int(n) => Ok(ModelValue::Int(n.clone())),
            Constant::Rational(r) => Ok(ModelValue::Real(r.0.clone())),
            Constant::BitVec { value, width } => Ok(ModelValue::BitVec {
                width: *width,
                value: bitvec::normalize(value, *width),
            }),
            Constant::String(s) => Ok(ModelValue::Str(s.clone())),
            _ => Err("unsupported constant kind".into()),
        }
    }

    // ----- application dispatch -------------------------------------------

    fn eval_named(
        &self,
        term: TermId,
        name: &str,
        args: &[TermId],
        depth: usize,
    ) -> EvalResult<ModelValue> {
        if args
            .iter()
            .any(|t| matches!(self.terms.sort(*t), Sort::FiniteField(_)))
            && !matches!(name, "=" | "distinct")
        {
            return Err("unsupported finite-field context".into());
        }
        if args
            .iter()
            .any(|t| matches!(self.terms.sort(*t), Sort::FiniteField(_)))
            && args
                .iter()
                .any(|t| self.terms.sort(*t) != self.terms.sort(args[0]))
        {
            return Err("mixed-field equality".into());
        }
        match name {
            // Core boolean connectives (short-circuiting where SMT-LIB allows).
            "and" => self.eval_and(args, depth),
            "or" => self.eval_or(args, depth),
            "=>" => self.eval_implies(args, depth),
            "xor" => self.eval_xor(args, depth),
            "not" => {
                let [a] = exactly(args)?;
                Ok(ModelValue::Bool(!self.eval_bool(a, depth + 1)?))
            }
            "ite" | "if" => {
                let [c, t, e] = exactly(args)?;
                let selected = self.conditional_branch(term, c, t, e, depth)?;
                self.eval(selected, depth + 1)
            }
            "=" => self.eval_eq(args, depth),
            "distinct" => self.eval_distinct(args, depth),

            // Arithmetic (Int/Real).
            //
            // `(/ x 0)`, `(div x 0)` and `(mod x 0)` are UNCONSTRAINED in
            // SMT-LIB — the Ints/Reals theories leave division by zero to an
            // uninterpreted function — so `eval_arith` routes exactly those
            // three sites through [`Self::division_by_zero`], which adopts the
            // model's own choice and then checks the one residue the theory
            // does fix (the result is still a number of the right sort). The
            // adoption is deliberately NOT applied to the whole arithmetic
            // dispatch: a narrower window cannot mistake an unrelated failure
            // for an under-specified one.
            "+" | "-" | "*" | "/" | "div" | "mod" | "abs" | "to_real" | "to_int" | "is_int"
            | "<" | "<=" | ">" | ">=" => self.eval_arith(term, name, args, depth),

            // Floating-point to exact Real.  This deliberately lives outside
            // `eval_arith`: its operand is an IEEE bit-pattern value, not an
            // Int/Real numeric value.  NaN and the infinities have no real
            // value SMT-LIB fixes, so those adopt the model's choice (checked
            // to still be a number) rather than being computed.
            "fp.to_real" => self.eval_fp_to_real(term, args, depth),

            // Floating-point to its IEEE-754 interchange encoding. Pure
            // bit-reinterpretation, so the gate computes it exactly and
            // independently on every value SMT-LIB determines.
            //
            // NaN is the sole exception, and it takes the underspecified path
            // rather than the generic one because adopting the model's value
            // there is only sound WITH A CHECK: the standard frees the sign bit
            // and the payload, it does not free the result from being a NaN
            // encoding at all. `crate::fp::check_ieee_nan_encoding` enforces
            // exactly that residue, so an adopted `#x00000000` — which z3 also
            // refutes — still fails closed instead of confirming a `sat`.
            "fp.to_ieee_bv" => {
                let [arg] = exactly(args)?;
                let operand = self.eval_operand(arg, depth + 1)?;
                self.charge_exact_fp_value(&operand)?;
                let (width, work) = crate::fp_exact::ieee_work(&operand)?;
                if self.terms.sort(term) != &Sort::bitvec(width) {
                    return Err("fp.to_ieee_bv result has the wrong own sort".into());
                }
                self.charge_exact_fp_work(work)?;
                let checkpoint = || -> EvalResult<()> { self.poll_exact_fp() };
                checkpoint()?;
                let result = match crate::fp::to_ieee_bv(&operand) {
                    Err(reason) if reason == crate::fp::UNDERSPECIFIED => self
                        .adopt_underspecified(term, name, args, depth, reason, |adopted| {
                            crate::fp::check_ieee_nan_encoding(&operand, adopted)
                        }),
                    other => other.map_err(EvalError::from),
                };
                checkpoint()?;
                result
            }

            // The `(fp <sign-bv> <exp-bv> <sig-bv>)` literal: three bitvector
            // fields assembled into a value. Assembling it here rather than
            // adopting the solver's reading of it is the difference between
            // CHECKING an FP assertion and restating one — the literal is the
            // operand of nearly every one of them. The arity guard keeps a
            // user-declared symbol that merely happens to be spelled `fp` on
            // the uninterpreted-application path.
            "fp" => {
                if args.len() != 3 {
                    return Err("FP constructor expects three fields".into());
                }
                let _inputs = FpInputGuard::enter(&self.fp_input_depth)?;
                let values = self.eval_all(args, depth)?;
                for value in &values {
                    if let ModelValue::BitVec { value, .. } = value {
                        self.charge_exact_fp_work(
                            usize::try_from(value.bits().div_ceil(8))
                                .map_err(|_| "FP field exceeds address space")?,
                        )?;
                    }
                }
                crate::fp_exact::literal(&values).map_err(EvalError::from)
            }

            // The rest of the floating-point fragment, computed exactly on
            // `BigInt`/`BigRational` in `crate::fp` — see that module for why
            // an exact reimplementation of IEEE rounding keeps the gate
            // independent.
            //
            // This is a PREFIX arm on purpose. With one match arm per operator,
            // an `fp.` operator nobody had implemented yet fell through to
            // `eval_uninterpreted_app`, which ADOPTS the solver's committed
            // value — silently confirming an interpreted operator the gate
            // never computed. Claiming the whole namespace turns that class of
            // hole into an explicit `Err` and a `CannotConfirm`.
            _ if name.starts_with("fp.") => self.eval_fp(term, name, args, depth),

            // Arrays.
            "select" | "store" | "const-array" | "lambda-array" | "default" => {
                self.eval_array(term, name, args, depth)
            }

            // Strings. Regex structure is interpreted by the separate,
            // proof-checker-parity interval matcher; only String-sorted leaves
            // flow through this evaluator/model view.
            "str.++" | "str.len" | "str.at" | "str.in_re" | "str.in.re" | "str.replace_re"
            | "str.replace_re_all" => self.eval_string(name, args, depth),

            // The rest of the string theory, computed from the operand VALUES.
            // These were reaching the uninterpreted-function path, so the gate
            // adopted the solver's answer for `(str.contains s t)` rather than
            // looking at `s` and `t`.
            _ if crate::strings::handles(name, args.len()) => {
                let vals = self.eval_all(args, depth)?;
                crate::strings::eval(name, &vals).map_err(EvalError::from)
            }

            // Finite sets, computed from the `(Array T Bool)` membership
            // carrier they are modelled on. Also previously adopted.
            _ if crate::sets::handles(name, args.len()) => {
                let domain = args.first().map_or(crate::sets::DomainSize::Unknown, |&a| {
                    element_domain_size(self.terms.sort(a))
                });
                let vals = self.eval_all(args, depth)?;
                crate::sets::eval(name, &vals, &domain).map_err(EvalError::from)
            }

            "mkbv" => {
                let Sort::BitVec(result) = self.terms.sort(term) else {
                    return Err(EvalError::from(
                        "mkbv result must be a bit-vector".to_string(),
                    ));
                };
                if args.is_empty() || args.len() != result.width as usize {
                    return Err(EvalError::from(
                        "mkbv argument count must match result width".to_string(),
                    ));
                }
                let byte_count = args.len().div_ceil(8);
                self.charge_functional_work(byte_count)?;
                let mut bytes = vec![0; byte_count];
                for (index, &arg) in args.iter().enumerate() {
                    if self.eval_bool(arg, depth + 1)? {
                        bytes[index / 8] |= 1 << (index % 8);
                    }
                }
                Ok(ModelValue::BitVec {
                    width: result.width,
                    value: BigInt::from_bytes_le(num_bigint::Sign::Plus, &bytes),
                })
            }
            _ if is_bv_named(name) => {
                let vals = self.eval_all(args, depth)?;
                bitvec::eval_named(name, &vals).map_err(EvalError::from)
            }
            _ if name.starts_with("seq.") => {
                if name == "seq.nth" {
                    return self.eval_sequence_nth(term, args, depth);
                }
                let vals = self.eval_all(args, depth)?;
                seq::eval(name, &vals).map_err(EvalError::from)
            }

            // Datatypes (constructor / selector / tester), else an
            // uninterpreted function: apply the model's value-keyed
            // interpretation (fail closed if it cannot be built).
            _ => match self.eval_datatype(term, name, args, depth)? {
                DatatypeEvaluation::Value(value) => Ok(value),
                DatatypeEvaluation::NotDatatype | DatatypeEvaluation::WrongConstructor => self
                    .eval_uninterpreted_app(
                        term,
                        name,
                        args,
                        depth,
                        format!("uninterpreted or wrong-constructor application: {name}"),
                        None,
                        |_| Ok(()),
                    ),
            },
        }
    }

    /// Adopt the model's committed value for an application whose result
    /// SMT-LIB leaves UNCONSTRAINED on these particular inputs, then CHECK the
    /// residue the standard does constrain.
    ///
    /// SMT-LIB restricts, but does not uniquely determine, `fp.min`/`fp.max` of
    /// `+0` and `-0` and the NaN encoding `fp.to_ieee_bv` returns. On those
    /// inputs the gate may read only a normal, committed application value and
    /// then validates the remaining restriction. Fully unconstrained results
    /// (`fp.to_real` of a non-finite operand and arithmetic division by zero)
    /// use the separate typed [`Self::adopt_proven_unconstrained`] path.
    ///
    /// `residue` is what is left to check once the free part is granted: an
    /// adopted `fp.min` of the two zeros must still be a ZERO of that format,
    /// and an adopted `fp.to_ieee_bv` of NaN must still be a NaN ENCODING.
    /// That is what keeps this path from laundering an evaluator bug into a
    /// confirmed `sat`. A residue failure is an `Err`, i.e. `CannotConfirm` —
    /// fail closed, as everywhere else here.
    /// `((_ fp.to_ubv m) rm x)` / `((_ fp.to_sbv m) rm x)`.
    ///
    /// Computed exactly where SMT-LIB fixes the result. Off that domain (NaN,
    /// the infinities, out of range) the result is unspecified yet still a
    /// FUNCTION of `(rm, x)`: the model's value is adopted, congruence-keyed on
    /// the operator, width and mode (in the key) and on `x` (the one evaluated
    /// argument), and must be a bitvector of the right width.
    fn eval_fp_to_bv(
        &self,
        term: TermId,
        name: &str,
        unsigned: bool,
        width: u32,
        args: &[TermId],
        depth: usize,
    ) -> EvalResult<ModelValue> {
        let [rm_term, x] = exactly(args)?;
        let rm = self.eval_rounding_mode(rm_term, depth)?;
        let value = self.eval_operand(x, depth + 1)?;
        let converted = if matches!(&value, ModelValue::FloatingPointExact { .. }) {
            if self.terms.sort(term) != &Sort::bitvec(width) {
                return Err("FP integer conversion result sort disagrees with width".into());
            }
            let source = crate::fp_exact::view(&value)?;
            if self.terms.sort(x) != &Sort::FloatingPoint(source.eb, source.sb) {
                return Err(
                    "FP integer conversion model payload disagrees with source sort".into(),
                );
            }
            if width == 0 || width > 1024 {
                return Err("unsupported bitvector width".into());
            }
            self.charge_exact_fp_work(crate::fp_exact::bytes(&value)?)?;
            let signedness = if unsigned {
                crate::fp_exact::BvSignedness::Unsigned
            } else {
                crate::fp_exact::BvSignedness::Signed
            };
            let plan = crate::fp_exact::bv_plan(&value, width, signedness, rm)
                .map_err(|reason| EvalError::resource(EvalResource::Work, reason))?;
            self.quantifier_state
                .admit_model_data_storage(plan.storage)?;
            self.admit_exact_fp_work(plan.work, plan.storage)?;
            self.charge_exact_fp_work(0)?;
            let result = plan.materialize();
            self.charge_exact_fp_work(0)?;
            result
        } else {
            crate::fp::to_bv(unsigned, width, rm, &value)
        };
        match converted {
            Err(reason) if reason == crate::fp::UNDERSPECIFIED => {
                let Sort::FloatingPoint(eb, sb) = self.terms.sort(x) else {
                    return Err("fp.to_sbv/to_ubv requires a floating-point operand".into());
                };
                // These are overloaded functions: equal-width encodings in
                // different FP sorts belong to distinct domains. Keep the
                // source format in the identity before comparing typed values;
                // NaNs within ONE format must still share a single result.
                let key = format!("{name}/{width}/{rm:?}/fp/{eb}/{sb}");
                self.adopt_underspecified(term, &key, &args[1..], depth, reason, |adopted| {
                    match adopted {
                        ModelValue::BitVec { width: w, .. } if *w == width => Ok(()),
                        _ => Err(format!("{key} must be a {width}-bit value")),
                    }
                })
            }
            other => other.map_err(EvalError::from),
        }
    }

    fn adopt_underspecified(
        &self,
        term: TermId,
        name: &str,
        args: &[TermId],
        depth: usize,
        reason: String,
        residue: impl Fn(&ModelValue) -> Result<(), String>,
    ) -> EvalResult<ModelValue> {
        // `None`, NOT a typed unconstrained reason: this helper exists for
        // results the standard RESTRICTS rather than frees (a NaN keeps a
        // required encoding even though its sign and payload are
        // unspecified), so only the model's own committed value is
        // admissible. The residue is checked before a new graph entry is
        // installed, so an ill-sorted/bogus pin cannot pollute congruent uses.
        self.eval_uninterpreted_app(term, name, args, depth, reason, None, |value| {
            residue(value).map_err(EvalError::from)
        })
    }

    /// Adopt a value only after an exact evaluator branch has proved that the
    /// operation is unconstrained on the independently evaluated inputs.
    ///
    /// The ordinary committed value has priority. Only when it is absent may
    /// the model supply a definition-selected value through the typed fallback.
    /// `residue` validates the result sort before the value enters `uf_graph`.
    fn adopt_proven_unconstrained(
        &self,
        term: TermId,
        name: &str,
        args: &[TermId],
        depth: usize,
        kind: ProvenUnconstrainedKind,
        residue: impl Fn(&ModelValue) -> Result<(), String>,
    ) -> EvalResult<ModelValue> {
        self.eval_uninterpreted_app(
            term,
            name,
            args,
            depth,
            format!("SMT-LIB leaves {name} unconstrained for these inputs"),
            Some(kind),
            |value| residue(value).map_err(EvalError::from),
        )
    }

    /// `(/ a 0)`, `(div a 0)` and `(mod a 0)`: unspecified but TOTAL.
    ///
    /// SMT-LIB constrains integer division and remainder only for a nonzero
    /// divisor. At zero they are arbitrary-but-FIXED functions of their
    /// arguments — every value is a legal interpretation, so there is nothing
    /// to compute, and refusing turned a legitimate `sat` into `unknown`
    /// (`(assert (< 0 (div 1 0)))` is sat in z3).
    ///
    /// So adopt the model's own choice, exactly as `fp.to_real` at NaN does.
    /// The adoption is keyed by the argument VALUES, which is what makes it an
    /// interpretation rather than a wish: `(div 1 0)` gets ONE value across
    /// every occurrence, so a model claiming it is both 0 and 1 is still
    /// refuted. The sort check is the rest of what can be verified — the
    /// theory says nothing else about these values.
    fn division_by_zero(
        &self,
        term: TermId,
        name: &str,
        args: &[TermId],
        depth: usize,
        kind: ProvenUnconstrainedKind,
    ) -> EvalResult<ModelValue> {
        let (expected_name, expected_sort, operand_sort) = match kind {
            ProvenUnconstrainedKind::RealDivByZero => ("/", Sort::Real, Sort::Real),
            ProvenUnconstrainedKind::IntDivByZero => ("div", Sort::Int, Sort::Int),
            ProvenUnconstrainedKind::IntModByZero => ("mod", Sort::Int, Sort::Int),
            ProvenUnconstrainedKind::FpToRealNonFinite
            | ProvenUnconstrainedKind::SeqNthOutOfBounds => {
                return Err("non-arithmetic unconstrained reason at division-by-zero site".into());
            }
        };
        if name != expected_name
            || self.terms.sort(term) != &expected_sort
            || args.len() != 2
            || args
                .iter()
                .any(|&argument| self.terms.sort(argument) != &operand_sort)
        {
            return Err(
                format!("typed unconstrained reason does not match `{name}` signature").into(),
            );
        }
        self.adopt_proven_unconstrained(term, name, args, depth, kind, |adopted| {
            let well_sorted = match kind {
                ProvenUnconstrainedKind::RealDivByZero => {
                    matches!(adopted, ModelValue::Real(_) | ModelValue::Algebraic(_))
                }
                ProvenUnconstrainedKind::IntDivByZero | ProvenUnconstrainedKind::IntModByZero => {
                    matches!(adopted, ModelValue::Int(_))
                }
                ProvenUnconstrainedKind::FpToRealNonFinite
                | ProvenUnconstrainedKind::SeqNthOutOfBounds => false,
            };
            if well_sorted {
                Ok(())
            } else {
                Err(format!("{name} by zero must still be a number"))
            }
        })
    }

    /// Resolve a `RoundingMode`-sorted operand to one of the five modes.
    ///
    /// A literal (`RNE`, `roundTowardZero`, …) is a nullary symbol that no
    /// model pins, so it is read SYNTACTICALLY; a declared `RoundingMode`
    /// constant is a leaf the model does pin, and arrives as an uninterpreted
    /// token naming its mode. Anything else fails closed.
    fn eval_rounding_mode(
        &self,
        term: TermId,
        depth: usize,
    ) -> EvalResult<crate::fp::RoundingMode> {
        if !matches!(self.terms.sort(term), Sort::Uninterpreted(name) if name == "RoundingMode") {
            return Err("operand is not RoundingMode-sorted".into());
        }
        let syntactic = match self.terms.get(term) {
            TermData::App(Symbol::Named(name), args) if args.is_empty() => {
                self.admit_evaluation(name.len(), 0)?;
                if self.terms.is_declared_function(name) {
                    None
                } else {
                    crate::fp::RoundingMode::from_name(name)
                }
            }
            _ => None,
        };
        if let Some(rm) = syntactic {
            return Ok(rm);
        }
        match self.eval_operand(term, depth + 1)? {
            ModelValue::Uninterpreted(token) => crate::fp::RoundingMode::from_name(&token)
                .ok_or_else(|| {
                    EvalError::Refused(format!("`{token}` does not name a rounding mode"))
                }),
            _ => Err("operand is not a rounding mode".into()),
        }
    }

    /// The `fp.`-prefixed floating-point operators.
    ///
    /// Split by whether the operator takes a leading rounding mode, because
    /// that decides where the value operands start. Anything not listed falls
    /// through to an `Err` and the gate keeps failing closed on it — which is
    /// the point of routing the whole `fp.` namespace here rather than letting
    /// an unimplemented operator reach the adopt-the-solver's-answer path.
    fn eval_fp(
        &self,
        term: TermId,
        name: &str,
        args: &[TermId],
        depth: usize,
    ) -> EvalResult<ModelValue> {
        // Rounding-mode-taking operators: `rm` first, values after.
        if matches!(
            name,
            "fp.add" | "fp.sub" | "fp.mul" | "fp.div" | "fp.fma" | "fp.sqrt" | "fp.roundToIntegral"
        ) {
            let (rm_arg, rest) = args
                .split_first()
                .ok_or_else(|| format!("{name} expects a rounding mode"))?;
            let rm = self.eval_rounding_mode(*rm_arg, depth)?;
            let vals = self.eval_all(rest, depth)?;
            if matches!(
                name,
                "fp.add" | "fp.sub" | "fp.mul" | "fp.div" | "fp.fma" | "fp.sqrt"
            ) && vals
                .iter()
                .any(|v| matches!(v, ModelValue::FloatingPointExact { .. }))
            {
                let scans = crate::fp_exact::arithmetic_scan_work(&vals)?;
                self.admit_exact_fp_work(scans, 0)?;
                for (value, argument) in vals.iter().zip(rest) {
                    let source = crate::fp_exact::view(value)?;
                    let sort = Sort::FloatingPoint(source.eb, source.sb);
                    if self.terms.sort(term) != &sort || self.terms.sort(*argument) != &sort {
                        return Err("FP arithmetic payload format disagrees with term sorts".into());
                    }
                }
                let plan = crate::fp_exact::arithmetic_plan(name, rm, &vals)
                    .map_err(|reason| EvalError::resource(EvalResource::Work, reason))?;
                self.quantifier_state
                    .admit_model_data_storage(plan.storage)?;
                self.admit_exact_fp_work(plan.work, plan.storage)?;
                self.charge_exact_fp_work(0)?;
                let result = plan.materialize();
                self.charge_exact_fp_work(0)?;
                return result.map_err(EvalError::from);
            }
            return match name {
                "fp.fma" => crate::fp::fma(rm, &vals).map_err(EvalError::from),
                "fp.roundToIntegral" | "fp.sqrt" => {
                    let [v] = <&[ModelValue; 1]>::try_from(vals.as_slice())
                        .map_err(|_| format!("{name} expects one argument"))?;
                    if name == "fp.sqrt" {
                        crate::fp::sqrt(rm, v).map_err(EvalError::from)
                    } else if matches!(v, ModelValue::FloatingPointExact { .. }) {
                        let source = crate::fp_exact::view(v)?;
                        let sort = Sort::FloatingPoint(source.eb, source.sb);
                        if self.terms.sort(term) != &sort || self.terms.sort(rest[0]) != &sort {
                            return Err(
                                "fp.roundToIntegral payload format disagrees with term sorts"
                                    .into(),
                            );
                        }
                        // Price classification, exponent and fraction scans before planning.
                        let scans = crate::fp_exact::integral_scan_work(v)?;
                        self.admit_exact_fp_work(scans, 0)?;
                        let plan = crate::fp_exact::integral_plan(v, rm)
                            .map_err(|reason| EvalError::resource(EvalResource::Work, reason))?;
                        self.quantifier_state
                            .admit_model_data_storage(plan.storage)?;
                        self.admit_exact_fp_work(plan.work, plan.storage)?;
                        self.charge_exact_fp_work(0)?;
                        let result = plan.materialize();
                        self.charge_exact_fp_work(0)?;
                        result.map_err(EvalError::from)
                    } else {
                        crate::fp::round_to_integral(rm, v).map_err(EvalError::from)
                    }
                }
                _ => crate::fp::arith(name, rm, &vals)?.ok_or_else(|| {
                    EvalError::Refused(format!("unsupported floating-point operator {name}"))
                }),
            };
        }

        let vals = self.eval_all(args, depth)?;
        for value in &vals {
            self.charge_exact_fp_value(value)?;
        }
        if let [only] = vals.as_slice() {
            if let Some(verdict) = crate::fp::classify(name, only)? {
                return Ok(ModelValue::Bool(verdict));
            }
            if let Some(value) = crate::fp::unary_sign(name, only)? {
                return Ok(value);
            }
        }
        if let Some(verdict) = crate::fp::compare(name, &vals)? {
            return Ok(ModelValue::Bool(verdict));
        }
        match crate::fp::min_max(name, &vals) {
            Ok(Some(value)) => return Ok(value),
            Ok(None) => {}
            // `fp.min`/`fp.max` of `+0` and `-0`: SMT-LIB allows EITHER zero,
            // so there is nothing to compute and nothing to refuse. Adopt the
            // model's own choice — the treatment `fp.to_real` gets at NaN —
            // and then check that what came back is one of the two answers the
            // standard actually allows, so an adopted value is still a checked
            // one. (`min_max` only reports this for two operands of one
            // format, so `vals[0]` is the format to check against.)
            Err(reason) if reason == crate::fp::UNDERSPECIFIED => {
                let like = vals
                    .first()
                    .cloned()
                    .ok_or_else(|| format!("{name} expects two floating-point arguments"))?;
                return self.adopt_underspecified(term, name, args, depth, reason, |adopted| {
                    if is_zero_of_format(adopted, &like) {
                        Ok(())
                    } else {
                        Err(format!(
                            "{name} of +0 and -0 must be a zero of the operands' format"
                        ))
                    }
                });
            }
            Err(reason) => return Err(reason.into()),
        }
        if name == "fp.rem" {
            if vals
                .iter()
                .any(|value| matches!(value, ModelValue::FloatingPointExact { .. }))
            {
                let scans = crate::fp_exact::arithmetic_scan_work(&vals)?;
                self.admit_exact_fp_work(scans, 0)?;
                for (value, argument) in vals.iter().zip(args) {
                    let source = crate::fp_exact::view(value)?;
                    let sort = Sort::FloatingPoint(source.eb, source.sb);
                    if self.terms.sort(term) != &sort || self.terms.sort(*argument) != &sort {
                        return Err("FP remainder payload format disagrees with term sorts".into());
                    }
                }
                let plan =
                    crate::fp_exact::arithmetic_plan(name, crate::fp::RoundingMode::Rne, &vals)
                        .map_err(|reason| EvalError::resource(EvalResource::Work, reason))?;
                self.quantifier_state
                    .admit_model_data_storage(plan.storage)?;
                self.admit_exact_fp_work(plan.work, plan.storage)?;
                self.charge_exact_fp_work(0)?;
                let result = plan.materialize();
                self.charge_exact_fp_work(0)?;
                return result.map_err(EvalError::from);
            }
            return crate::fp::rem(&vals).map_err(EvalError::from);
        }
        Err(format!("unsupported floating-point operator {name}").into())
    }

    /// Evaluate SMT-LIB `fp.to_real` from the model's exact IEEE fields.
    ///
    /// No host float participates in this conversion.  Finite values are
    /// reconstructed as `significand * 2^exponent` using `BigInt` /
    /// `BigRational`; malformed payloads, unsupported field widths, and
    /// impractically large exact shifts are rejected rather than guessed. NaN
    /// and infinity take the separately typed unconstrained-result path after
    /// their exact IEEE encoding has been proved. The shift bound is only a
    /// resource guard: crossing it changes a possible confirmation into
    /// `CannotConfirm`, never the reverse.
    ///
    /// The decoding is kept here, rather than delegated to [`crate::fp`],
    /// because it accepts a WIDER format envelope than the arithmetic there
    /// needs (`fp.to_real` never rounds, so it does not have to bound the
    /// intermediates the way rounding does) — declining a format the gate can
    /// read exactly would be a pure completeness loss.
    fn eval_fp_to_real(
        &self,
        term: TermId,
        args: &[TermId],
        depth: usize,
    ) -> EvalResult<ModelValue> {
        let [arg] = exactly(args)?;
        if self.terms.sort(term) != &Sort::Real {
            return Err("fp.to_real result sort is not Real".into());
        }
        let Sort::FloatingPoint(expected_exponent_bits, expected_significand_bits) =
            self.terms.sort(arg)
        else {
            return Err("fp.to_real operand sort is not FloatingPoint".into());
        };
        let operand = self.eval_operand(arg, depth + 1)?;
        let (ModelValue::FloatingPoint {
            exponent_bits,
            significand_bits,
            ..
        }
        | ModelValue::FloatingPointExact {
            exponent_bits,
            significand_bits,
            ..
        }) = &operand
        else {
            return Err("fp.to_real expects a floating-point value".into());
        };
        if exponent_bits != expected_exponent_bits || significand_bits != expected_significand_bits
        {
            return Err("fp.to_real model payload format disagrees with operand sort".into());
        }
        self.charge_exact_fp_work(crate::fp_exact::bytes(&operand)?)?;
        // The immutable input's fields were validated above. Failure to plan
        // this dyadic now denotes arithmetic/storage capacity, not an absent
        // interpretation that another completion path could replace.
        let plan = crate::fp_exact::real_plan(&operand)
            .map_err(|reason| EvalError::resource(EvalResource::Work, reason))?;
        self.quantifier_state
            .admit_model_data_storage(plan.storage)?;
        self.admit_exact_fp_work(plan.work, plan.storage)?;
        self.charge_exact_fp_work(0)?;
        let converted = plan.materialize();
        self.charge_exact_fp_work(0)?;
        let Some(magnitude) = converted else {
            // Unconstrained by SMT-LIB rather than uncomputable: `fp.to_real`
            // of a NaN or an infinity may be ANY real, so this adopts the
            // model's committed choice, or (only if no commitment exists) the
            // definition-selected fallback. Reaching this exact all-ones
            // exponent branch is what mints the typed evidence; malformed
            // fields were rejected above. The only residue is the Real result
            // sort, checked before the value enters the congruence graph.
            return self.adopt_proven_unconstrained(
                term,
                "fp.to_real",
                args,
                depth,
                ProvenUnconstrainedKind::FpToRealNonFinite,
                |adopted| {
                    if matches!(adopted, ModelValue::Real(_) | ModelValue::Algebraic(_)) {
                        Ok(())
                    } else {
                        Err("fp.to_real of NaN or infinity must still be a real".into())
                    }
                },
            );
        };
        Ok(ModelValue::Real(magnitude))
    }

    /// Evaluate an uninterpreted-function application `(name arg0 ...)` against
    /// the model, keyed by the argument VALUES (not the argument terms).
    ///
    /// The gate evaluates the arguments itself (independently, with exact
    /// arithmetic), then treats the application as a single-valued function of
    /// those argument values: the FIRST application to reach a given
    /// `(name, arg-values)` key fixes the value for every later application with
    /// the same key. The representative value is the model's committed
    /// per-application value ([`ModelView::uf_app_value`]).
    ///
    /// This is what catches a model that collapses two congruent applications'
    /// arguments to the same value while pinning them to different results
    /// (e.g. `i0 = 0` makes `f(3*i0)` and `f(i0)` both `f(0)`, so a strict
    /// inequality between them cannot hold): both applications resolve through
    /// the same graph entry, so the inequality evaluates to `false` and the
    /// gate refutes the witness. Enforcing single-valuedness by argument VALUE
    /// (rather than trusting the per-application pins, which are exactly what is
    /// inconsistent in the wrong model) is the whole point.
    ///
    /// If the model does not pin the application, the result is `Unevaluable`
    /// (`dt_err` is surfaced) — fail closed, never assumed.
    ///
    /// `proven_unconstrained` is present only when the exact calling branch has
    /// positively proved one of [`ProvenUnconstrainedKind`]'s input conditions.
    /// It authorizes a fallback to
    /// [`ModelView::proven_unconstrained_app_value`] *only if* the ordinary
    /// committed value is absent. Generic applications and partially
    /// unspecified results pass `None`.
    ///
    /// `residue` validates the value's remaining theory obligations (at least
    /// its result sort) before a fresh graph entry is installed. It is also
    /// rechecked on graph hits, keeping this primitive fail-closed even if a
    /// future caller supplies a stricter residue for the same value key.
    fn eval_uninterpreted_app(
        &self,
        term: TermId,
        name: &str,
        args: &[TermId],
        depth: usize,
        dt_err: String,
        proven_unconstrained: Option<ProvenUnconstrainedKind>,
        residue: impl Fn(&ModelValue) -> EvalResult<()>,
    ) -> EvalResult<ModelValue> {
        self.eval_uninterpreted_app_checked(
            term,
            name,
            args,
            depth,
            dt_err,
            proven_unconstrained,
            |value| residue(value).map_err(EvalError::from),
        )
    }

    fn eval_uninterpreted_app_checked(
        &self,
        term: TermId,
        name: &str,
        args: &[TermId],
        depth: usize,
        dt_err: String,
        proven_unconstrained: Option<ProvenUnconstrainedKind>,
        residue: impl Fn(&ModelValue) -> EvalResult<()>,
    ) -> EvalResult<ModelValue> {
        // Evaluate the arguments ourselves. If any argument is unevaluable, the
        // application is unevaluable (fail closed).
        if let Some(function) = self.model.symbolic_function(term)? {
            let value = self.eval_symbolic_application(term, args, depth, function)?;
            residue(&value)?;
            return Ok(value);
        }
        self.require_symbolic_function_absent(name)?;
        let arg_vals = self.eval_all(args, depth)?;
        // Consult the value-keyed graph: same function, argument values all
        // equal ⇒ same result. The partial polymorphic sequence operation also
        // retains an originating application for its element-sort instance.
        // The numeric id is not type equality: both stored sorts are checked.
        let instance: Option<TermId> = matches!(
            proven_unconstrained,
            Some(ProvenUnconstrainedKind::SeqNthOutOfBounds)
        )
        .then_some(term);
        {
            let graph = self.uf_graph.borrow();
            if instance.is_some() {
                self.charge_sequence_work(graph.len())?;
            }
            let arg_sorts: Vec<&Sort> = args.iter().map(|&arg| self.terms.sort(arg)).collect();
            for (f, stored_instance, keys, val) in graph.iter() {
                if f != name {
                    continue;
                }
                let same_instance = match (stored_instance, instance) {
                    (None, None) => true,
                    (Some(left), Some(right)) => {
                        if self.terms.entry_stamp(*left).is_none()
                            || self.terms.entry_stamp(right).is_none()
                        {
                            return Err("sequence graph instance has an invalid origin".into());
                        }
                        self.sequence_instance_sorts_equal(
                            self.terms.sort(*left),
                            self.terms.sort(right),
                        )?
                    }
                    _ => false,
                };
                if same_instance
                    && self.congruence_keys_equal_at_sorts(keys, &arg_vals, &arg_sorts)?
                {
                    residue(val)?;
                    return self.clone_value(val);
                }
            }
        }
        // A committed value is keyed only by the application TermId. The same
        // body application can be evaluated under several lambda bindings, so
        // consulting that non-contextual pin here could fabricate a value for
        // the wrong beta instance. A previously established value-keyed graph
        // entry above remains sound; only adopting this term's ambient pin is
        // prohibited.
        if self.term_depends_on_local_binding(term)? {
            return Err("model-backed context-dependent application is unsupported".into());
        }
        // First use adopts the model's value at these evaluated arguments;
        // `uf_app_value_at` lets a total published table reconcile any pin.
        //
        // Report the MISS, not `dt_err`. `dt_err` is the datatype-dispatch
        // failure that routed us here, and for a plain uninterpreted symbol it
        // reads "uninterpreted / unsupported function application: f" — which
        // states that the EVALUATOR does not support `f`. That is not what
        // happened: the evaluator supports `f` fine (this function is exactly
        // that support), and the real reason is that the MODEL committed no
        // value for this application. The two call for opposite fixes — extend
        // the evaluator vs. complete the model — and the misattribution sends a
        // reader to the wrong one. Keep `dt_err` in the text so the datatype
        // path is still diagnosable when that is genuinely the cause.
        let val = if let Some(committed) = self.model.uf_app_value_at(term, &arg_vals) {
            // A normal model commitment always wins. The typed fallback exists
            // solely for otherwise-uncommitted theory applications.
            committed
        } else if let Some(kind) = proven_unconstrained {
            self.model
                .proven_unconstrained_app_value(term, kind)
                .ok_or_else(|| {
                    EvalError::ModelUnavailable(format!(
                        "model supplies no value for proven-unconstrained \
                         application `{name}` ({kind:?}; {dt_err})"
                    ))
                })?
        } else {
            return Err(EvalError::ModelUnavailable(format!(
                "model commits no value for this application of `{name}` \
                 (gate cannot confirm without one; datatype dispatch also \
                 declined: {dt_err})"
            )));
        };
        // Validate before insertion. In particular, a malicious or malformed
        // fallback cannot seed the value-keyed graph with a wrong-sort value
        // that a congruent sibling would later inherit.
        self.admit_value(&val)?;
        residue(&val)?;
        self.admit_evaluation(0, name.len())?;
        let copied = self.clone_value(&val)?;
        self.push_uf_graph_entry((name.to_string(), instance, arg_vals, copied))?;
        Ok(val)
    }

    fn push_uf_graph_entry(&self, entry: UfGraphEntry) -> EvalResult<()> {
        let (length, previous_capacity) = {
            let graph = self.uf_graph.borrow();
            (graph.len(), graph.capacity())
        };
        let capacity = if length == previous_capacity {
            let capacity = previous_capacity.saturating_mul(2).max(4);
            let bytes = capacity
                .checked_mul(std::mem::size_of::<UfGraphEntry>())
                .ok_or("UF graph allocation overflow")?;
            self.admit_evaluation(length, bytes)?;
            capacity
        } else {
            previous_capacity
        };
        let mut graph = self.uf_graph.borrow_mut();
        if graph.len() != length || graph.capacity() != previous_capacity {
            drop(graph);
            return Err(self.admission_error("UF graph changed during storage admission"));
        }
        if capacity != previous_capacity {
            let additional = capacity.saturating_sub(length);
            graph
                .try_reserve_exact(additional)
                .map_err(|_| "UF graph allocation refused")?;
        }
        graph.push(entry);
        Ok(())
    }

    // ----- boolean connectives --------------------------------------------

    fn eval_and(&self, args: &[TermId], depth: usize) -> EvalResult<ModelValue> {
        // `and` is false if ANY conjunct is false (even if others are
        // unevaluable); true only if ALL are true.
        let mut pending: Option<EvalError> = None;
        for &a in args {
            match self.eval_operand(a, depth + 1) {
                Ok(ModelValue::Bool(false)) => return Ok(ModelValue::Bool(false)),
                Ok(ModelValue::Bool(true)) => {}
                Ok(_) => return Err("non-boolean argument to and".into()),
                Err(e) => EvalError::record(&mut pending, e),
            }
        }
        match pending {
            Some(e) => Err(e),
            None => Ok(ModelValue::Bool(true)),
        }
    }

    fn eval_or(&self, args: &[TermId], depth: usize) -> EvalResult<ModelValue> {
        // `or` is true if ANY disjunct is true; false only if ALL are false.
        let mut pending: Option<EvalError> = None;
        for &a in args {
            match self.eval_operand(a, depth + 1) {
                Ok(ModelValue::Bool(true)) => return Ok(ModelValue::Bool(true)),
                Ok(ModelValue::Bool(false)) => {}
                Ok(_) => return Err("non-boolean argument to or".into()),
                Err(e) => EvalError::record(&mut pending, e),
            }
        }
        match pending {
            Some(e) => Err(e),
            None => Ok(ModelValue::Bool(false)),
        }
    }

    fn eval_implies(&self, args: &[TermId], depth: usize) -> EvalResult<ModelValue> {
        // (=> a1 ... an) = (or (not a1) ... (not a_{n-1}) a_n).
        if args.len() < 2 {
            return Err("=> needs at least two arguments".into());
        }
        let (last, init) = args.split_last().expect("len >= 2");
        let mut pending: Option<EvalError> = None;
        for &a in init {
            match self.eval_operand(a, depth + 1) {
                // A false antecedent makes the implication true.
                Ok(ModelValue::Bool(false)) => return Ok(ModelValue::Bool(true)),
                Ok(ModelValue::Bool(true)) => {}
                Ok(_) => return Err("non-boolean antecedent in =>".into()),
                Err(e) => EvalError::record(&mut pending, e),
            }
        }
        match self.eval_operand(*last, depth + 1) {
            Ok(ModelValue::Bool(true)) => Ok(ModelValue::Bool(true)),
            Ok(ModelValue::Bool(false)) => match pending {
                Some(e) => Err(e),
                None => Ok(ModelValue::Bool(false)),
            },
            Ok(_) => Err("non-boolean consequent in =>".into()),
            Err(e) => match pending {
                Some(prior) if !prior.is_model_unavailable() => Err(prior),
                _ => Err(e),
            },
        }
    }

    fn eval_xor(&self, args: &[TermId], depth: usize) -> EvalResult<ModelValue> {
        let mut acc = false;
        for &a in args {
            acc ^= self.eval_bool(a, depth + 1)?;
        }
        Ok(ModelValue::Bool(acc))
    }

    /// Exact equality of two RegLan terms against this model: the string
    /// leaves of each regex are evaluated here, and the languages are then
    /// compared by the independent derivative product in
    /// [`crate::regex_equiv`]. `ModelValue` has no RegLan carrier, so this
    /// term-level decision is the only sound way to judge such an equality.
    fn eval_reglan_eq(&self, left: TermId, right: TermId, depth: usize) -> EvalResult<bool> {
        let owner = scratch_admission::ScratchAdmission::new(self);
        owner.finish(crate::regex_equiv::languages_equal(
            self.terms,
            left,
            right,
            depth + 1,
            |term| self.eval_str(term, depth + 2),
            &owner,
        ))
    }

    fn eval_eq(&self, args: &[TermId], depth: usize) -> EvalResult<ModelValue> {
        if args.len() < 2 {
            return Err("= needs at least two arguments".into());
        }
        let operand_sort = self.terms.sort(args[0]);
        if matches!(operand_sort, Sort::RegLan)
            && args[1..]
                .iter()
                .all(|&arg| matches!(self.terms.sort(arg), Sort::RegLan))
        {
            for &arg in &args[1..] {
                if !self.eval_reglan_eq(args[0], arg, depth)? {
                    return Ok(ModelValue::Bool(false));
                }
            }
            return Ok(ModelValue::Bool(true));
        }
        if let Some(value) = self.functional_array_equality(args, depth)? {
            return Ok(ModelValue::Bool(value));
        }
        // Sound congruence shortcut (closes S1): two applications of the SAME
        // function symbol whose argument VALUES are all equal denote the same
        // value, so the equality holds — even when the function is uninterpreted
        // and cannot itself be evaluated. This lets the gate catch a model that
        // violates congruence, e.g. `(= (f (store a i v)) (f a))` when
        // `store(a,i,v)` and `a` evaluate to the same array. It only ever proves
        // the equality TRUE (equal args ⇒ equal results); it never proves an
        // inequality. Unequal or model-unavailable arguments fall through to
        // value comparison; malformed/resource failures must not disappear.
        let mut congruent = true;
        for &arg in &args[1..] {
            if !self.congruent_equal(args[0], arg, depth)? {
                congruent = false;
                break;
            }
        }
        if congruent {
            return Ok(ModelValue::Bool(true));
        }
        if args[1..]
            .iter()
            .any(|&arg| self.terms.sort(arg) != operand_sort)
        {
            return Err("= operands have different sorts".into());
        }
        let vals = self.eval_all(args, depth)?;
        for v in &vals[1..] {
            if !self.value_eq_at_sort(&vals[0], v, operand_sort)? {
                return Ok(ModelValue::Bool(false));
            }
        }
        Ok(ModelValue::Bool(true))
    }

    /// Equality with the operand sort still attached.
    ///
    /// Most model values carry enough type information for [`value_eq`]. An
    /// [`ArrayValue`] intentionally does not: it stores only a default and a
    /// finite override list. For arrays, the index sort is necessary to decide
    /// whether differing defaults are reachable. A finite override list can
    /// never cover `Int`, for example, while it can cover all of `Bool`.
    fn value_eq_at_sort(
        &self,
        left: &ModelValue,
        right: &ModelValue,
        sort: &Sort,
    ) -> EvalResult<bool> {
        self.ensure_value_inhabits_sort(left, sort)?;
        self.ensure_value_inhabits_sort(right, sort)?;
        let mut comparison_work = 0usize;
        self.value_eq_for_typed_values(left, right, sort, &mut comparison_work)
    }

    /// Equality after both operands have recursively passed
    /// [`Self::ensure_value_inhabits_sort`].
    ///
    /// Keeping the preflight separate makes aggregate validation linear in the
    /// number of value nodes. Recursive datatype/array comparison can reuse the
    /// established field invariant instead of re-walking an entire subtree at
    /// every level.
    fn value_eq_for_typed_values(
        &self,
        left: &ModelValue,
        right: &ModelValue,
        sort: &Sort,
        comparison_work: &mut usize,
    ) -> EvalResult<bool> {
        self.charge_exact_fp_value(left)?;
        self.charge_exact_fp_value(right)?;
        self.admit_symbolic_numeric_work(&[left, right])?;
        self.charge_quantifier_work(1)?;
        *comparison_work = comparison_work.checked_add(1).ok_or_else(|| {
            EvalError::resource(
                EvalResource::Work,
                "typed equality comparison counter overflow",
            )
        })?;
        if *comparison_work > MAX_TYPED_EQUALITY_COMPARISONS {
            return Err(EvalError::resource(
                EvalResource::Work,
                format!("typed equality exceeds comparison limit {MAX_TYPED_EQUALITY_COMPARISONS}"),
            ));
        }
        if let Some(datatype) = self.dt_of_sort(sort) {
            return self.datatype_eq_at_sort(left, right, &datatype, comparison_work);
        }
        match (sort, left, right) {
            (Sort::Array(array_sort), ModelValue::Array(left), ModelValue::Array(right)) => {
                self.array_eq_at_sort(left, right, array_sort, comparison_work)
            }
            (Sort::Seq(element_sort), ModelValue::Seq(left), ModelValue::Seq(right)) => {
                if left.len() != right.len() {
                    return Ok(false);
                }
                let mut unresolved = None;
                for (left_element, right_element) in left.iter().zip(right) {
                    match self.value_eq_for_typed_values(
                        left_element,
                        right_element,
                        element_sort,
                        comparison_work,
                    ) {
                        Ok(true) => {}
                        Ok(false) => return Ok(false),
                        Err(reason) => EvalError::record(&mut unresolved, reason),
                    }
                }
                match unresolved {
                    Some(reason) => Err(reason),
                    None => Ok(true),
                }
            }
            _ => value_eq(left, right).map_err(EvalError::from),
        }
    }

    /// Prove that `value` is a canonical inhabitant of `sort`, within fixed
    /// depth and work budgets.
    ///
    /// Model values deliberately carry less type information than terms:
    /// arrays do not store their index/element sorts, sequences do not store an
    /// element sort, and datatype values store only a constructor name. Exact
    /// equality therefore has to authenticate the complete nested shape against
    /// the declared term sort before comparing payloads. Identical malformed
    /// values are not evidence of equality at an unrelated sort. Residual
    /// witness construction shares this exact validator so its finite-store
    /// keys, elements, and synthesized defaults cannot bypass typed equality's
    /// model boundary.
    pub(crate) fn ensure_value_inhabits_sort(
        &self,
        value: &ModelValue,
        sort: &Sort,
    ) -> EvalResult<()> {
        let mut work = 0usize;
        self.ensure_value_inhabits_sort_bounded(value, sort, 0, &mut work)
    }

    fn ensure_value_inhabits_sort_bounded(
        &self,
        value: &ModelValue,
        sort: &Sort,
        depth: usize,
        work: &mut usize,
    ) -> EvalResult<()> {
        self.charge_quantifier_work(1)?;
        if depth > MAX_TYPED_VALUE_DEPTH {
            return Err(EvalError::resource(
                EvalResource::Depth,
                format!("typed model value nesting exceeds depth limit {MAX_TYPED_VALUE_DEPTH}"),
            ));
        }
        *work = work.checked_add(1).ok_or_else(|| {
            EvalError::resource(
                EvalResource::Work,
                "typed model value work counter overflow",
            )
        })?;
        if *work > MAX_TYPED_VALUE_WORK {
            return Err(EvalError::resource(
                EvalResource::Work,
                format!("typed model value exceeds work limit {MAX_TYPED_VALUE_WORK}"),
            ));
        }

        // Datatypes abstracted to an uninterpreted carrier still have a schema
        // in the model registry. Resolve that schema before the ordinary
        // uninterpreted-sort arm: accepting an opaque token here would discard
        // constructor identity and arity.
        if let Some(datatype) = self.dt_of_sort(sort) {
            let ModelValue::Datatype { ctor, args } = value else {
                return Err("datatype sort requires a constructor-bearing value".into());
            };
            let constructor = datatype
                .constructors
                .iter()
                .find(|candidate| candidate.name == *ctor)
                .ok_or_else(|| "datatype value names a foreign constructor".to_string())?;
            if constructor.fields.len() != args.len() {
                return Err("datatype value has the wrong constructor arity".into());
            }
            for (argument, field) in args.iter().zip(&constructor.fields) {
                self.ensure_value_inhabits_sort_bounded(argument, &field.sort, depth + 1, work)?;
            }
            return Ok(());
        }

        match (value, sort) {
            (ModelValue::Bool(_), Sort::Bool)
            | (ModelValue::Int(_), Sort::Int)
            | (ModelValue::Str(_), Sort::String)
            | (ModelValue::Uninterpreted(_), Sort::Uninterpreted(_) | Sort::TypeVar(_)) => Ok(()),

            // An exact integer is also a canonical Real value; the evaluator
            // intentionally preserves this coercion for `to_real` equality.
            (ModelValue::Int(_) | ModelValue::Real(_) | ModelValue::Algebraic(_), Sort::Real) => {
                Ok(())
            }

            (ModelValue::BitVec { width, value }, Sort::BitVec(bitvec))
                if *width == bitvec.width
                    && !value.is_negative()
                    && value.bits() <= u64::from(bitvec.width) =>
            {
                Ok(())
            }

            (
                ModelValue::FloatingPoint {
                    exponent,
                    significand,
                    exponent_bits,
                    significand_bits,
                    ..
                },
                Sort::FloatingPoint(expected_exponent_bits, expected_significand_bits),
            ) if exponent_bits == expected_exponent_bits
                && significand_bits == expected_significand_bits
                && crate::fp::data_fields_fit(
                    *exponent_bits,
                    *significand_bits,
                    *exponent,
                    *significand,
                ) =>
            {
                Ok(())
            }

            (
                value @ ModelValue::FloatingPointExact {
                    exponent_bits,
                    significand_bits,
                    ..
                },
                Sort::FloatingPoint(expected_eb, expected_sb),
            ) if exponent_bits == expected_eb && significand_bits == expected_sb => {
                self.charge_exact_fp_value(value)?;
                Ok(())
            }

            (ModelValue::Int(codepoint), Sort::Char)
                if !codepoint.is_negative() && codepoint < &BigInt::from(0x3_0000u32) =>
            {
                Ok(())
            }
            (ModelValue::Int(element), Sort::FiniteField(field))
                if !element.is_negative() && element < &BigInt::from(field.modulus()) =>
            {
                Ok(())
            }
            (ModelValue::Int(element), Sort::FiniteDomain(_, size))
                if !element.is_negative() && element < &BigInt::from(*size) =>
            {
                Ok(())
            }

            // AY's own sequence carrier for an EUF-provided class identity.
            //
            // `ay_dpll`'s independent gate reifies a sequence whose model
            // payload is nothing but an EUF equivalence class as the opaque
            // token `@ay-seq-euf-class:{sort:?}:{len}:{class}`. The token embeds
            // the debug rendering of the COMPLETE sequence sort, so this arm
            // re-derives that rendering and admits the value only at the exact
            // sort it was minted for: class `e0` in `(Seq Int)` never inhabits
            // `(Seq Bool)`, and an ad-hoc uninterpreted value inhabits no
            // sequence sort at all.
            //
            // This admits a CARRIER, it does not loosen any comparison. Two
            // such tokens are decided by `value_eq`'s exact string identity;
            // a token against a concrete `ModelValue::Seq` stays incomparable
            // and therefore fail-closed, because the class name is evidence of
            // an equivalence class and never of a sequence's elements.
            (ModelValue::Uninterpreted(token), Sort::Seq(_))
                if token.starts_with(&sequence_euf_class_prefix(sort)) =>
            {
                Ok(())
            }

            (ModelValue::Seq(elements), Sort::Seq(element_sort)) => {
                for element in elements {
                    self.ensure_value_inhabits_sort_bounded(
                        element,
                        element_sort,
                        depth + 1,
                        work,
                    )?;
                }
                Ok(())
            }
            (ModelValue::Array(array), Sort::Array(array_sort)) => {
                self.ensure_value_inhabits_sort_bounded(
                    &array.default,
                    &array_sort.element_sort,
                    depth + 1,
                    work,
                )?;
                for (index, element) in &array.store {
                    self.ensure_value_inhabits_sort_bounded(
                        index,
                        &array_sort.index_sort,
                        depth + 1,
                        work,
                    )?;
                    self.ensure_value_inhabits_sort_bounded(
                        element,
                        &array_sort.element_sort,
                        depth + 1,
                        work,
                    )?;
                }
                Ok(())
            }

            // Regular-language terms are interpreted structurally by
            // `crate::regex`; `ModelValue` intentionally has no RegLan carrier
            // to adopt from a solver model. Equality over a purported regex
            // value therefore remains unsupported and fail-closed.
            (_, Sort::RegLan) => Err("regular-language sorts have no model-value carrier".into()),
            _ => Err(format!(
                "model value shape {} does not inhabit the declared sort",
                crate::value_shape(value)
            )
            .into()),
        }
    }

    /// Equality for a declared datatype while retaining its constructor schema.
    ///
    /// Constructor identity is decisive, and every constructor must have the
    /// declared arity. Fields are compared recursively at their declared sort,
    /// so arrays retain the index sort required by [`Self::array_eq_at_sort`]
    /// and sequences retain their exact element shape. This is not an opaque
    /// carrier coercion: either operand lacking a constructor, naming a foreign
    /// constructor, carrying the wrong arity, or mismatching a nested value
    /// shape still fails closed.
    fn datatype_eq_at_sort(
        &self,
        left: &ModelValue,
        right: &ModelValue,
        datatype: &ay_core::DatatypeSort,
        comparison_work: &mut usize,
    ) -> EvalResult<bool> {
        let (
            ModelValue::Datatype {
                ctor: left_ctor,
                args: left_args,
            },
            ModelValue::Datatype {
                ctor: right_ctor,
                args: right_args,
            },
        ) = (left, right)
        else {
            return Err(format!(
                "datatype equality requires constructor-bearing values: left={left:?}, \
                 right={right:?}"
            )
            .into());
        };
        let left_schema = datatype
            .constructors
            .iter()
            .find(|constructor| constructor.name.as_str() == left_ctor)
            .ok_or_else(|| "datatype value names a foreign constructor".to_string())?;
        let right_schema = datatype
            .constructors
            .iter()
            .find(|constructor| constructor.name.as_str() == right_ctor)
            .ok_or_else(|| "datatype value names a foreign constructor".to_string())?;
        if left_schema.fields.len() != left_args.len()
            || right_schema.fields.len() != right_args.len()
        {
            return Err("datatype value has the wrong constructor arity".into());
        }
        if left_ctor != right_ctor {
            return Ok(false);
        }

        let mut unresolved = None;
        for ((left_field, right_field), field) in
            left_args.iter().zip(right_args).zip(&left_schema.fields)
        {
            let result = self.value_eq_for_typed_values(
                left_field,
                right_field,
                &field.sort,
                comparison_work,
            );
            match result {
                Ok(true) => {}
                Ok(false) => return Ok(false),
                Err(reason) => EvalError::record(&mut unresolved, reason),
            }
        }
        match unresolved {
            Some(reason) => Err(reason),
            None => Ok(true),
        }
    }

    /// Extensional equality for typed array values.
    ///
    /// The untyped comparator in `lib.rs` must fail closed when defaults differ,
    /// because it cannot know whether finite stores cover the index domain. This
    /// evaluator owns the original operand sort, so it can make the exact
    /// distinction:
    ///
    /// * on a provably infinite index sort, finitely many stores always leave an
    ///   index where both defaults are read;
    /// * on a known finite carrier, equal reads at every distinct stored key
    ///   decide equality iff those keys cover the complete carrier;
    /// * on an unknown carrier (notably an uninterpreted sort), it retains the
    ///   fail-closed result.
    fn array_eq_at_sort(
        &self,
        left: &ArrayValue,
        right: &ArrayValue,
        sort: &ay_core::ArraySort,
        comparison_work: &mut usize,
    ) -> EvalResult<bool> {
        let defaults_equal = self.value_eq_for_typed_values(
            &left.default,
            &right.default,
            &sort.element_sort,
            comparison_work,
        )?;

        // A finite override set cannot hide different defaults over an infinite
        // carrier. This proof needs no comparison between the stored keys.
        if !defaults_equal && Self::index_sort_is_definitely_infinite(&sort.index_sort) {
            return Ok(false);
        }

        // Fast lane: when the index sort admits a canonical encoding, the two
        // ordered rescans per union key collapse into two table lookups. The
        // visit order, the selected values and the distinct-key count are
        // identical to the rescan below, so only the CHARGED work differs --
        // and it only ever decreases. See `canonical_index_tables`.
        if let Some(tables) =
            self.canonical_index_tables(left, right, &sort.index_sort, comparison_work)
        {
            for encoded in &tables.visit_order {
                if !self.value_eq_for_typed_values(
                    Self::table_select(&tables.left, encoded, left),
                    Self::table_select(&tables.right, encoded, right),
                    &sort.element_sort,
                    comparison_work,
                )? {
                    return Ok(false);
                }
            }
            if defaults_equal {
                return Ok(true);
            }
            let mut distinct: HashSet<&str> = HashSet::new();
            distinct.extend(tables.left.keys().map(String::as_str));
            distinct.extend(tables.right.keys().map(String::as_str));
            return self.decide_differing_defaults(&sort.index_sort, distinct.len());
        }

        for (key, _) in left.store.iter().chain(&right.store) {
            let left_value =
                self.array_select_at_sort(left, key, &sort.index_sort, comparison_work)?;
            let right_value =
                self.array_select_at_sort(right, key, &sort.index_sort, comparison_work)?;
            if !self.value_eq_for_typed_values(
                &left_value,
                &right_value,
                &sort.element_sort,
                comparison_work,
            )? {
                return Ok(false);
            }
        }
        if defaults_equal {
            return Ok(true);
        }

        let keys = self.distinct_array_keys(left, right, &sort.index_sort, comparison_work)?;
        self.decide_differing_defaults(&sort.index_sort, keys.len())
    }

    /// Decide two arrays whose DEFAULTS differ but whose explicit reads agree:
    /// they are equal exactly when the stored keys cover the whole index
    /// carrier, making both defaults unreachable.
    fn decide_differing_defaults(
        &self,
        index_sort: &Sort,
        distinct_keys: usize,
    ) -> EvalResult<bool> {
        match self.known_finite_index_is_covered(index_sort, distinct_keys) {
            Some(covered) => Ok(covered),
            None => Err(
                "array equality with differing defaults needs index-domain coverage evidence"
                    .into(),
            ),
        }
    }

    /// The value `array` reads at the semantic key `encoded`.
    ///
    /// Exactly [`Self::array_select_at_sort`] for an index sort that
    /// [`Self::encode_canonical_index_key`] admits: the table holds the LAST
    /// store position for each semantic key, which is the entry that function's
    /// reverse scan stops at, and a key absent from the table is one no store
    /// entry matches, i.e. a read of the default.
    fn table_select<'b>(
        table: &HashMap<String, usize>,
        encoded: &str,
        array: &'b ArrayValue,
    ) -> &'b ModelValue {
        table
            .get(encoded)
            .map_or(&array.default, |&position| &array.store[position].1)
    }

    /// Build semantic-key tables for both operands of an array comparison, or
    /// `None` when the index sort is outside the canonically encodable
    /// fragment.
    ///
    /// Encoding work is metered on a LOCAL counter and folded into the shared
    /// `comparison_work` only when every key encoded. A decline therefore
    /// leaves the caller's charge byte-identical to the ordered-rescan path it
    /// falls back to, so admitting this lane can never make a comparison the
    /// meter previously decided become unevaluable.
    fn canonical_index_tables(
        &self,
        left: &ArrayValue,
        right: &ArrayValue,
        index_sort: &Sort,
        comparison_work: &mut usize,
    ) -> Option<CanonicalIndexTables> {
        let mut encode_work = 0usize;
        let mut visit_order = Vec::with_capacity(left.store.len() + right.store.len());
        let mut left_table = HashMap::with_capacity(left.store.len());
        let mut right_table = HashMap::with_capacity(right.store.len());
        for (table, array) in [(&mut left_table, left), (&mut right_table, right)] {
            for (position, (key, _)) in array.store.iter().enumerate() {
                let mut encoded = String::new();
                self.encode_canonical_index_key(key, index_sort, &mut encoded, &mut encode_work)?;
                // Later stores win, matching the reverse scan in
                // `array_select_at_sort`.
                table.insert(encoded.clone(), position);
                visit_order.push(encoded);
            }
        }
        *comparison_work = comparison_work.checked_add(encode_work)?;
        Some(CanonicalIndexTables {
            visit_order,
            left: left_table,
            right: right_table,
        })
    }

    /// Append a canonical, collision-free encoding of one authenticated index
    /// value to `out`, or return `None` to decline the whole fast lane.
    ///
    /// The lane is only sound because on every ADMITTED sort
    /// [`Self::value_eq_for_typed_values`] coincides exactly with structural
    /// equality of the encoded payload:
    ///
    /// * each admitted sort has a SINGLE inhabiting `ModelValue` shape, fixed
    ///   by [`Self::ensure_value_inhabits_sort`], so one element is never
    ///   representable in two encodings. That is precisely why `Real` (which
    ///   admits `Int`, `Real` and `Algebraic` payloads for one number),
    ///   `FloatingPoint` (whose `=` is `fp::same_element`, not field identity),
    ///   `Array` (extensional, and itself three-valued) and the sequence-class
    ///   carrier arm of `ensure_value_inhabits_sort` are all declined;
    /// * `value_eq` decides every admitted shape with `==` on that payload and
    ///   never returns `Err`, so a table lookup cannot silently swallow an
    ///   unevaluable key comparison the rescan would have reported;
    /// * every variant is self-delimiting -- a leading tag, then either a
    ///   `;`-terminated numeral, a byte-length-prefixed string, or a
    ///   parenthesised count-prefixed sequence -- so concatenation is
    ///   injective and two distinct values cannot encode alike.
    ///
    /// The `dt_of_sort` guard is defence in depth, not a live filter: a
    /// datatype can hide behind an uninterpreted NAME, but
    /// `ensure_value_inhabits_sort` already requires a `ModelValue::Datatype`
    /// at any sort that resolves to one, and no arm below matches that shape.
    /// Removing the guard is therefore currently unobservable -- it is kept so
    /// that adding a constructor-aware arm, or relaxing that inhabitance rule,
    /// cannot silently start encoding a constructor value as an opaque token.
    fn encode_canonical_index_key(
        &self,
        value: &ModelValue,
        sort: &Sort,
        out: &mut String,
        encode_work: &mut usize,
    ) -> Option<()> {
        use std::fmt::Write as _;

        *encode_work = encode_work.checked_add(1)?;
        if *encode_work > MAX_TYPED_EQUALITY_COMPARISONS {
            return None;
        }
        if self.dt_of_sort(sort).is_some() {
            return None;
        }
        match (sort, value) {
            (Sort::Bool, ModelValue::Bool(flag)) => out.push(if *flag { 'T' } else { 'F' }),
            (Sort::Int, ModelValue::Int(element)) => {
                let _ = write!(out, "i{element};");
            }
            (Sort::Char, ModelValue::Int(element)) => {
                let _ = write!(out, "c{element};");
            }
            (Sort::FiniteDomain(_, _), ModelValue::Int(element)) => {
                let _ = write!(out, "d{element};");
            }
            // Widths are equal on every authenticated pair, and `value_eq`
            // requires that equality anyway; carrying the width keeps the
            // encoding total rather than relying on that invariant.
            (Sort::BitVec(_), ModelValue::BitVec { width, value }) => {
                let _ = write!(out, "v{width}#{value};");
            }
            (Sort::String, ModelValue::Str(text)) => {
                let _ = write!(out, "s{}:{text}", text.len());
            }
            (Sort::Uninterpreted(_) | Sort::TypeVar(_), ModelValue::Uninterpreted(token)) => {
                let _ = write!(out, "u{}:{token}", token.len());
            }
            (Sort::Seq(element_sort), ModelValue::Seq(elements)) => {
                let _ = write!(out, "q{}(", elements.len());
                for element in elements {
                    self.encode_canonical_index_key(element, element_sort, out, encode_work)?;
                }
                out.push(')');
            }
            _ => return None,
        }
        Some(())
    }

    /// Fallback lane: read `array` at `index` by rescanning the override list
    /// newest-first with full semantic key comparison. Used when the index sort
    /// has no canonical encoding; [`Self::table_select`] replaces it otherwise.
    fn array_select_at_sort(
        &self,
        array: &ArrayValue,
        index: &ModelValue,
        index_sort: &Sort,
        comparison_work: &mut usize,
    ) -> EvalResult<ModelValue> {
        for (stored_index, value) in array.store.iter().rev() {
            if self.value_eq_for_typed_values(stored_index, index, index_sort, comparison_work)? {
                return self.clone_value(value);
            }
        }
        self.clone_value(&array.default)
    }

    /// Fallback lane: the semantically distinct union keys, deduplicated by
    /// pairwise comparison. Used when the index sort has no canonical encoding;
    /// otherwise the encoded key tables already carry the distinct count.
    fn distinct_array_keys<'b>(
        &self,
        left: &'b ArrayValue,
        right: &'b ArrayValue,
        index_sort: &Sort,
        comparison_work: &mut usize,
    ) -> EvalResult<Vec<&'b ModelValue>> {
        let mut distinct: Vec<&'b ModelValue> = Vec::new();
        for (key, _) in left.store.iter().chain(&right.store) {
            let mut duplicate = false;
            for &seen in &distinct {
                if self.value_eq_for_typed_values(key, seen, index_sort, comparison_work)? {
                    duplicate = true;
                    break;
                }
            }
            if !duplicate {
                distinct.push(key);
            }
        }
        Ok(distinct)
    }

    fn index_sort_is_definitely_infinite(sort: &Sort) -> bool {
        matches!(sort, Sort::Int | Sort::Real | Sort::String | Sort::Seq(_))
    }

    /// Whether `distinct_keys` covers a finite scalar carrier whose values the
    /// independent checker can validate without consulting solver state.
    ///
    /// This compares bounded machine counts instead of materialising `2^width`:
    /// a hostile `(_ BitVec 4294967295)` sort must produce an immediate `false`,
    /// not attempt a half-gigabyte cardinality allocation. `None` means unknown
    /// here, not infinite; infinite carriers are handled separately above.
    fn known_finite_index_is_covered(&self, sort: &Sort, distinct_keys: usize) -> Option<bool> {
        if let Some(datatype) = self.dt_of_sort(sort) {
            return datatype
                .constructors
                .iter()
                .all(|constructor| constructor.fields.is_empty())
                .then_some(distinct_keys >= datatype.constructors.len());
        }
        match sort {
            Sort::Bool => Some(distinct_keys >= 2),
            Sort::BitVec(bitvec) => Some(
                bitvec.width < usize::BITS && distinct_keys >= (1usize << bitvec.width as usize),
            ),
            Sort::Char => Some(distinct_keys >= 0x3_0000),
            Sort::FiniteDomain(_, size) => Some((distinct_keys as u128) >= u128::from(*size)),
            _ => None,
        }
    }

    /// Sound congruence test: are `lhs` and `rhs` provably equal because they are
    /// applications of the SAME named function symbol whose corresponding argument
    /// VALUES are all equal? Returns `true` only when congruence PROVES equality
    /// (also the reflexive `lhs == rhs`); `false` means "cannot conclude via
    /// congruence" (the caller falls back to direct value comparison). It never
    /// concludes inequality, so a `false` here can never turn a real equality into a
    /// wrong `false`. Missing interpretations decline the shortcut; hard
    /// evaluation failures retain their category and propagate to the caller.
    fn congruent_equal(&self, lhs: TermId, rhs: TermId, depth: usize) -> EvalResult<bool> {
        if lhs == rhs {
            return Ok(true);
        }
        if depth > MAX_EVAL_DEPTH {
            return Err(EvalError::resource(
                EvalResource::Depth,
                format!("recursion depth limit {MAX_EVAL_DEPTH} exceeded"),
            ));
        }
        let (TermData::App(Symbol::Named(fl), al), TermData::App(Symbol::Named(fr), ar)) =
            (self.terms.get(lhs), self.terms.get(rhs))
        else {
            return Ok(false);
        };
        if fl != fr || al.len() != ar.len() || al.is_empty() {
            return Ok(false);
        }
        // A select has exact lazy read semantics: requiring a whole array value
        // here would reject binder-dependent lambdas before beta reduction and
        // checked conditional/store folding. Decline this optional shortcut;
        // normal read evaluation retains its own sort, scope and resource checks.
        if fl.as_str() == "select" {
            return Ok(false);
        }
        // The two children of lambda-array are a binder and its scoped body.
        // Matching their values at model-assigned indices gives one sample,
        // while equality of the functions requires agreement at every index.
        if fl.as_str() == "lambda-array" {
            return Ok(false);
        }
        for (&x, &y) in al.iter().zip(ar) {
            if self.terms.sort(x) != self.terms.sort(y) {
                return Ok(false);
            }
            let values = self
                .eval_operand(x, depth + 1)
                .and_then(|left| self.eval_operand(y, depth + 1).map(|right| (left, right)));
            let (left, right) = match values {
                Ok(values) => values,
                Err(error) if error.is_model_unavailable() => return Ok(false),
                Err(error) => return Err(error),
            };
            if !self.value_eq_at_sort(&left, &right, self.terms.sort(x))? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn eval_distinct(&self, args: &[TermId], depth: usize) -> EvalResult<ModelValue> {
        let Some(&first) = args.first() else {
            return Ok(ModelValue::Bool(true));
        };
        let operand_sort = self.terms.sort(first);
        if args[1..]
            .iter()
            .any(|&arg| self.terms.sort(arg) != operand_sort)
        {
            return Err("distinct operands have different sorts".into());
        }
        if matches!(operand_sort, Sort::RegLan) {
            for i in 0..args.len() {
                for j in (i + 1)..args.len() {
                    if self.eval_reglan_eq(args[i], args[j], depth)? {
                        return Ok(ModelValue::Bool(false));
                    }
                }
            }
            return Ok(ModelValue::Bool(true));
        }
        let vals = self.eval_all(args, depth)?;
        for i in 0..vals.len() {
            for j in (i + 1)..vals.len() {
                if self.value_eq_at_sort(&vals[i], &vals[j], operand_sort)? {
                    return Ok(ModelValue::Bool(false));
                }
            }
        }
        Ok(ModelValue::Bool(true))
    }

    // ----- arithmetic ------------------------------------------------------

    fn eval_arith(
        &self,
        term: TermId,
        name: &str,
        args: &[TermId],
        depth: usize,
    ) -> EvalResult<ModelValue> {
        self.admit_symbolic_value_scratch(args.len())?;
        let vals = self.eval_all(args, depth)?;
        self.admit_symbolic_arithmetic(&vals)?;
        let sort = self.terms.sort(term);
        match name {
            // An ALGEBRAIC operand cannot be folded into a `BigRational` --
            // that is the lossy step that loses `sqrt(2)` -- so the sum/product
            // is carried in the extension instead. Rational operands are lifted
            // into it; a mix of two DIFFERENT extensions declines (resultants),
            // and declining is a coverage gap, never a wrong answer.
            "+" if vals.iter().any(is_algebraic) => {
                fold_algebraic(&vals, AlgebraicFold::Sum).map_err(EvalError::from)
            }
            "*" if vals.iter().any(is_algebraic) => {
                fold_algebraic(&vals, AlgebraicFold::Product).map_err(EvalError::from)
            }
            "+" => {
                let mut acc = BigRational::zero();
                for v in &vals {
                    acc += as_rational(v)?;
                }
                wrap_numeric(acc, sort).map_err(EvalError::from)
            }
            "*" => {
                let mut acc = BigRational::from(BigInt::from(1));
                for v in &vals {
                    acc *= as_rational(v)?;
                }
                wrap_numeric(acc, sort).map_err(EvalError::from)
            }
            "-" => {
                if vals.is_empty() {
                    return Err("- needs at least one argument".into());
                }
                let mut acc = as_rational(&vals[0])?;
                if vals.len() == 1 {
                    acc = -acc;
                } else {
                    for v in &vals[1..] {
                        acc -= as_rational(v)?;
                    }
                }
                wrap_numeric(acc, sort).map_err(EvalError::from)
            }
            "/" => {
                let [numerator, denominator] = vals.as_slice() else {
                    return Err("/ expects exactly two canonical operands".into());
                };
                let denominator = as_rational(denominator)?;
                if denominator.is_zero() {
                    // SMT-LIB leaves `(/ x 0)` unconstrained — it is an
                    // uninterpreted function on that input, not something
                    // to compute. This exact-zero branch alone mints the
                    // typed reason; adopt the model's choice, checked.
                    return self.division_by_zero(
                        term,
                        name,
                        args,
                        depth,
                        ProvenUnconstrainedKind::RealDivByZero,
                    );
                }
                let numerator = as_rational(numerator)?;
                // Result sort of `/` is Real.
                Ok(ModelValue::Real(numerator / denominator))
            }
            "div" => {
                let [a, b] = vals.as_slice() else {
                    return Err("div expects exactly two operands".into());
                };
                let (a, b) = (as_integer(a)?, as_integer(b)?);
                let Some((q, _)) = euclid(&a, &b) else {
                    return self.division_by_zero(
                        term,
                        name,
                        args,
                        depth,
                        ProvenUnconstrainedKind::IntDivByZero,
                    );
                };
                Ok(ModelValue::Int(q))
            }
            "mod" => {
                let [a, b] = vals.as_slice() else {
                    return Err("mod expects exactly two operands".into());
                };
                let (a, b) = (as_integer(a)?, as_integer(b)?);
                let Some((_, r)) = euclid(&a, &b) else {
                    return self.division_by_zero(
                        term,
                        name,
                        args,
                        depth,
                        ProvenUnconstrainedKind::IntModByZero,
                    );
                };
                Ok(ModelValue::Int(r))
            }
            "abs" => {
                let r = as_rational(&vals[0])?;
                wrap_numeric(r.abs(), sort).map_err(EvalError::from)
            }
            "to_real" => Ok(ModelValue::Real(as_rational(&vals[0])?)),
            "to_int" => {
                let r = as_rational(&vals[0])?;
                Ok(ModelValue::Int(r.floor().to_integer()))
            }
            "is_int" => {
                let r = as_rational(&vals[0])?;
                Ok(ModelValue::Bool(r.is_integer()))
            }
            "<" | "<=" | ">" | ">=" => {
                if vals.len() < 2 {
                    return Err("comparison needs at least two arguments".into());
                }
                // An algebraic operand is ORDERED by refining its isolating
                // interval, not by collapsing it to a rational. `sqrt(2) > 0`
                // is exactly the constraint reduction alone cannot settle --
                // both roots of `x^2 - 2` satisfy the same equalities and
                // differ only in sign.
                if vals.iter().any(is_algebraic) {
                    return compare_with_algebraic(name, &vals)
                        .map(ModelValue::Bool)
                        .map_err(EvalError::from);
                }
                let rats: Vec<BigRational> =
                    vals.iter().map(as_rational).collect::<Result<_, _>>()?;
                let ok = rats.windows(2).all(|w| compare_rat(name, &w[0], &w[1]));
                Ok(ModelValue::Bool(ok))
            }
            _ => Err(format!("unsupported arithmetic operator {name}").into()),
        }
    }

    // ----- arrays ----------------------------------------------------------

    fn eval_array(
        &self,
        term: TermId,
        name: &str,
        args: &[TermId],
        depth: usize,
    ) -> EvalResult<ModelValue> {
        match name {
            "select" => {
                let [a, i] = exactly(args)?;
                let Sort::Array(sort) = self.terms.sort(a) else {
                    return Err("select operand is not an array sort".into());
                };
                if self.terms.sort(i) != &sort.index_sort
                    || self.terms.sort(term) != &sort.element_sort
                {
                    return Err("malformed select index or result sort".into());
                }
                let idx = self.eval_operand(i, depth + 1)?;
                self.ensure_value_inhabits_sort(&idx, &sort.index_sort)?;
                // LAZY McCarthy fold over a syntactic store-chain: return the
                // stored value at the matching index WITHOUT reconstructing the
                // base array — so a `select` at a real (pushed) index resolves
                // even when the base is an intermediate/datatype array the model
                // never materializes. Falls through to full resolution otherwise.
                let unresolved_store = match self.select_over_store_chain(a, &idx, depth)? {
                    SelectFold::Value(value) => return Ok(value),
                    SelectFold::UnresolvedBase { array, reason } => {
                        // Repeating the same failed base reconstruction doubles
                        // the work at every nested select. Preserve the original
                        // read's model lookup and lexical checks, but share the
                        // proved base's graph key with all equivalent reads.
                        return self.eval_select_via_model(term, a, array, &idx, reason);
                    }
                    SelectFold::Reconstruct { array } => array,
                };
                // An unresolved store key is not an absent array interpretation.
                // Full reconstruction may still obtain that key from a shared
                // model observation while evaluating the base, but a missing
                // result cannot authorize an arbitrary value for this read:
                // the store's hit/miss equation remains unestablished.
                match self
                    .eval_array_value(a, depth + 1)
                    .map_err(EvalError::operand)
                {
                    Ok(arr) => self.array_select_admitted(&arr, &idx),
                    Err(reconstruct_err) if reconstruct_err.is_model_unavailable() => {
                        Err(EvalError::Refused(format!(
                            "unresolved store key at {unresolved_store:?}: {reconstruct_err}"
                        )))
                    }
                    Err(error) => Err(error),
                }
            }
            "store" => {
                let [a, i, v] = exactly(args)?;
                let arr = self
                    .eval_array_value(a, depth + 1)
                    .map_err(EvalError::operand)?;
                let idx = self.eval_operand(i, depth + 1)?;
                let val = self.eval_operand(v, depth + 1)?;
                self.admit_array(&arr)?;
                let mut store = arr.store.clone();
                store.push((idx, val));
                Ok(ModelValue::Array(Box::new(ArrayValue {
                    default: arr.default.clone(),
                    store,
                })))
            }
            "const-array" => {
                // `((as const (Array I E)) v)` — a constant array of `v`.
                let [v] = exactly(args)?;
                // Sanity: the result must be an array sort.
                if !matches!(self.terms.sort(term), Sort::Array(_)) {
                    return Err("const-array result is not an array sort".into());
                }
                let default = self.eval_operand(v, depth + 1)?;
                Ok(ModelValue::Array(Box::new(ArrayValue {
                    default,
                    store: Vec::new(),
                })))
            }
            "default" => {
                let [array] = exactly(args)?;
                self.eval_array_default(term, array, depth)
            }
            "lambda-array" => {
                let (bound, body) = self.lambda_array_parts(term, args)?;

                // A binder-independent body denotes a constant array and has
                // an exact finite representation. This is the only sound way
                // to materialize a lambda as `(default, finite-store)` in the
                // gate. Binder-dependent lambdas are still fully supported by
                // structural `select` beta-reduction below, but cannot in
                // general be represented as a finite ArrayValue.
                if self.term_contains(body, bound)? {
                    return Err(EvalError::NonFiniteLambdaArray);
                }
                let default = self.eval_operand(body, depth + 1)?;
                Ok(ModelValue::Array(Box::new(ArrayValue {
                    default,
                    store: Vec::new(),
                })))
            }
            _ => Err(format!("unsupported array operator {name}").into()),
        }
    }

    fn eval_array_value(&self, term: TermId, depth: usize) -> EvalResult<ArrayValue> {
        let value = self.eval(term, depth)?;
        self.ensure_value_inhabits_sort(&value, self.terms.sort(term))?;
        match value {
            ModelValue::Array(a) => Ok(*a),
            _ => Err("expected an array value".into()),
        }
    }

    fn lambda_array_parts(&self, term: TermId, args: &[TermId]) -> EvalResult<(TermId, TermId)> {
        let [bound, body] = exactly(args)?;
        let Sort::Array(array_sort) = self.terms.sort(term) else {
            return Err("lambda-array result is not an array sort".into());
        };
        if !matches!(self.terms.get(bound), TermData::Var(_, _))
            || self.terms.sort(bound) != &array_sort.index_sort
            || self.terms.sort(body) != &array_sort.element_sort
        {
            return Err("malformed lambda-array binder or body sort".into());
        }
        Ok((bound, body))
    }

    /// Exact cardinality when it is provably finite and below `cap`.
    ///
    /// This is intentionally the same conservative classification used by the
    /// solver's Z3-compatible array-default pass. `None` means infinite,
    /// recursive/unknown, or at least `cap`; all three take Z3's large-domain
    /// store-default branch.
    fn finite_sort_cardinality_below(
        &self,
        sort: &Sort,
        cap: usize,
        in_progress: &mut Vec<String>,
    ) -> Option<usize> {
        match sort {
            Sort::Bool => (2 < cap).then_some(2),
            Sort::BitVec(bitvec) => {
                if bitvec.width as usize >= cap.trailing_zeros() as usize {
                    None
                } else {
                    Some(1usize << bitvec.width)
                }
            }
            Sort::FiniteDomain(_, size) => {
                let size = usize::try_from(*size).ok()?;
                (size < cap).then_some(size)
            }
            Sort::Array(array) => {
                let index =
                    self.finite_sort_cardinality_below(&array.index_sort, cap, in_progress)?;
                let element =
                    self.finite_sort_cardinality_below(&array.element_sort, cap, in_progress)?;
                let mut total = 1usize;
                for _ in 0..index {
                    total = total.checked_mul(element)?;
                    if total >= cap {
                        return None;
                    }
                }
                Some(total)
            }
            Sort::Datatype(datatype) => self.datatype_cardinality_below(datatype, cap, in_progress),
            Sort::Uninterpreted(name) => {
                let datatype = self.model.datatype_def(name)?;
                self.datatype_cardinality_below(&datatype, cap, in_progress)
            }
            _ => None,
        }
    }

    fn datatype_cardinality_below(
        &self,
        datatype: &ay_core::DatatypeSort,
        cap: usize,
        in_progress: &mut Vec<String>,
    ) -> Option<usize> {
        if datatype.constructors.is_empty() || in_progress.iter().any(|name| name == &datatype.name)
        {
            return None;
        }
        in_progress.push(datatype.name.clone());
        let result = (|| {
            let mut total = 0usize;
            for constructor in &datatype.constructors {
                let mut variants = 1usize;
                for field in &constructor.fields {
                    let count =
                        self.finite_sort_cardinality_below(&field.sort, cap, in_progress)?;
                    variants = variants.checked_mul(count)?;
                    if variants >= cap {
                        return None;
                    }
                }
                total = total.checked_add(variants)?;
                if total >= cap {
                    return None;
                }
            }
            Some(total)
        })();
        in_progress.pop();
        result
    }

    /// Evaluate an array else-value without touching irrelevant store writes.
    ///
    /// Z3 5.0.0 preserves the base default for infinite/large carriers, but a
    /// small finite carrier uses a shared-epsilon select and a unit carrier uses
    /// the stored value. The finite case therefore reads the solver's committed
    /// scalar application value instead of unsoundly peeling the store.
    fn eval_array_default(
        &self,
        term: TermId,
        array: TermId,
        depth: usize,
    ) -> EvalResult<ModelValue> {
        let Sort::Array(array_sort) = self.terms.sort(array) else {
            return Err("default operand is not an array sort".into());
        };
        if self.terms.sort(term) != &array_sort.element_sort {
            return Err("default result sort does not match array element sort".into());
        }

        let mut current = array;
        let mut seen = HashSet::new();
        while seen.insert(current) {
            self.admit_evaluation(1, 0)?;
            if let TermData::App(_, args) = self.terms.get(current) {
                self.admit_evaluation(args.len(), 0)?;
            }
            self.charge_quantifier_work(1)?;
            if depth + seen.len() > MAX_EVAL_DEPTH {
                return Err(EvalError::resource(
                    EvalResource::Depth,
                    "array default evaluation depth exceeded",
                ));
            }
            // A checked projection owns the application's meaning before its
            // raw builtin spelling, including below a peeled store. Preserve
            // default semantics by redispatching its selected array: a finite
            // store representation's default may be completely overwritten.
            if let Some(selected) = self.default_projection_target(current)? {
                current = selected;
                continue;
            }
            if let TermData::App(Symbol::Named(name), _) = self.terms.get(current) {
                self.admit_evaluation(name.len().div_ceil(64).max(1), 0)?;
                if self.terms.is_declared_function(name) {
                    return self.eval_resolved_array_default(term, current, depth + seen.len());
                }
            }
            match self.terms.get(current) {
                TermData::App(Symbol::Named(name), args) if name == "store" => {
                    let [base, key, value] = exactly(args)?;
                    let Sort::Array(array_sort) = self.terms.sort(current) else {
                        return Err("store result is not an array sort".into());
                    };
                    if self.terms.sort(base) != self.terms.sort(current)
                        || self.terms.sort(key) != &array_sort.index_sort
                        || self.terms.sort(value) != &array_sort.element_sort
                    {
                        return Err("malformed store base, index or value sort".into());
                    }
                    match self.finite_sort_cardinality_below(
                        &array_sort.index_sort,
                        1 << 14,
                        &mut Vec::new(),
                    ) {
                        Some(1) => return self.eval(value, depth + seen.len()),
                        Some(_) => {
                            return self.eval_pinned_array_default(
                                term,
                                "model does not pin finite array default",
                            );
                        }
                        None => current = base,
                    }
                }
                TermData::App(Symbol::Named(name), args) if name == "const-array" => {
                    let [value] = exactly(args)?;
                    let Sort::Array(array_sort) = self.terms.sort(current) else {
                        return Err("const-array result is not an array sort".into());
                    };
                    if self.terms.sort(value) != &array_sort.element_sort {
                        return Err("const-array element sort mismatch".into());
                    }
                    return self.eval(value, depth + seen.len());
                }
                TermData::App(Symbol::Named(name), args) if name == "lambda-array" => {
                    let (bound, body) = self.lambda_array_parts(current, args)?;
                    if self.term_contains(body, bound)? {
                        return self.eval_pinned_array_default(
                            term,
                            "model does not pin opaque array default",
                        );
                    }
                    return self.eval_resolved_array_default(term, current, depth + seen.len());
                }
                TermData::App(symbol, _)
                    if matches!(symbol.name(), "store" | "const-array" | "lambda-array") =>
                {
                    return Err("array default requires a canonical named array operator".into());
                }
                TermData::App(Symbol::Named(name), _)
                    if current == array && name.starts_with("as-array[") =>
                {
                    return self.eval_pinned_array_default(
                        term,
                        "model does not pin opaque array default",
                    );
                }
                _ => return self.eval_resolved_array_default(term, current, depth + seen.len()),
            }
        }
        Err("cyclic array store chain".into())
    }

    fn default_projection_target(&self, array: TermId) -> EvalResult<Option<TermId>> {
        let TermData::App(_, args) = self.terms.get(array) else {
            return Ok(None);
        };
        let Some(index) = self
            .model
            .projection_argument(array)
            .map_err(|error| error.to_string())?
        else {
            return Ok(None);
        };
        // Match the ordinary eval call that would enter this array operand,
        // without recursively materializing it or resetting logical depth.
        let active = self.active_eval_calls.get().checked_add(1).ok_or_else(|| {
            EvalError::resource(EvalResource::Depth, "evaluator call depth overflow")
        })?;
        if active > MAX_PROJECTION_EVAL_CALL_DEPTH {
            return Err(EvalError::resource(
                EvalResource::Depth,
                "projection recursion depth limit exceeded",
            ));
        }
        let selected = args.get(index).copied().ok_or_else(|| {
            EvalError::Refused("array projection selects an absent argument".into())
        })?;
        if !matches!(self.terms.sort(array), Sort::Array(_))
            || self.terms.sort(selected) != self.terms.sort(array)
        {
            return Err("array projection selected argument sort mismatch".into());
        }
        Ok(Some(selected))
    }

    /// A marker from this evaluated array RESULT authenticates only its own
    /// opaque default. Operand failures have already lost that marker.
    fn eval_resolved_array_default(
        &self,
        term: TermId,
        array: TermId,
        depth: usize,
    ) -> EvalResult<ModelValue> {
        match self.eval_array_value(array, depth) {
            Ok(array) => Ok(array.default),
            Err(EvalError::NonFiniteLambdaArray) => {
                self.eval_pinned_array_default(term, "model does not pin opaque array default")
            }
            Err(error) => Err(error),
        }
    }

    fn eval_pinned_array_default(&self, term: TermId, reason: &str) -> EvalResult<ModelValue> {
        self.require_binding_independent_default(term)?;
        self.model
            .uf_app_value(term)
            .ok_or_else(|| EvalError::ModelUnavailable(reason.to_owned()))
    }

    /// An opaque default pin belongs to the ambient application, not to each
    /// distinct array produced by a bound variable valuation.
    fn require_binding_independent_default(&self, term: TermId) -> EvalResult<()> {
        if self.term_depends_on_local_binding(term)? {
            return Err("model-backed context-dependent array default is unsupported".into());
        }
        Ok(())
    }

    /// McCarthy `select` over a SYNTACTIC store-chain:
    /// `select(store(b,j,v), i) = if i==j then v else select(b,i)`, and
    /// `select(const-array d, i) = d`, and
    /// `select(lambda-array(x, body), i) = body[x := i]`. Returns the value
    /// WITHOUT resolving the
    /// base array `b` — so a read at a stored index never needs the base
    /// materialized (essential when `b` is an intermediate/datatype array the
    /// theory model does not reconstruct). A terminal base's reconstruction
    /// failure is returned separately so the caller can consult its original
    /// per-read pin without repeating the failed subtree. An indeterminate
    /// store index still requests the legacy reconstruction fallback. The
    /// outermost (newest) store is matched first, exactly as `store` semantics
    /// require; no failed result is retained beyond this one read attempt.
    fn select_over_store_chain(
        &self,
        a: TermId,
        idx: &ModelValue,
        depth: usize,
    ) -> EvalResult<SelectFold> {
        self.admit_evaluation(1, 0)?;
        if let TermData::App(_, args) = self.terms.get(a) {
            self.admit_evaluation(args.len(), 0)?;
        }
        if let Some(snapshot) = self.checked_array_snapshot(a)? {
            return Ok(SelectFold::Value(self.snapshot_work(|work| {
                snapshot
                    .read_with_stop(idx, work, &mut || self.model.functional_array_interrupted())
            })?));
        }
        self.charge_quantifier_work(1)?;
        if depth > MAX_EVAL_DEPTH {
            return Err(EvalError::resource(
                EvalResource::Depth,
                format!("recursion depth limit {MAX_EVAL_DEPTH} exceeded"),
            ));
        }
        // Checked symbolic projections precede named builtin dispatch. Do not
        // derive a store identity from an application owned by a projection,
        // or hide a failed projection behind an original per-read pin.
        let declared = if let TermData::App(Symbol::Named(name), _) = self.terms.get(a) {
            self.admit_evaluation(name.len().div_ceil(64).max(1), 0)?;
            self.terms.is_declared_function(name)
        } else {
            false
        };
        if declared
            || (matches!(self.terms.get(a), TermData::App(..))
                && self
                    .model
                    .projection_argument(a)
                    .map_err(|error| error.to_string())?
                    .is_some())
        {
            let array = self
                .eval_array_value(a, depth + 1)
                .map_err(EvalError::operand)?;
            return self
                .array_select_admitted(&array, idx)
                .map(SelectFold::Value);
        }
        match self.terms.get(a) {
            TermData::Ite(condition, positive, negative) => {
                self.select_conditional_array(a, [*condition, *positive, *negative], idx, depth)
            }
            TermData::App(Symbol::Named(name), args) if name == "ite" || name == "if" => {
                self.select_conditional_array(a, exactly(args)?, idx, depth)
            }
            TermData::App(Symbol::Named(name), args) if name == "store" => {
                let [base, key, value] = exactly(args)?;
                let Sort::Array(sort) = self.terms.sort(a) else {
                    return Err("store result is not an array sort".into());
                };
                if self.terms.sort(base) != self.terms.sort(a)
                    || self.terms.sort(key) != &sort.index_sort
                    || self.terms.sort(value) != &sort.element_sort
                {
                    return Err("malformed store base, index or value sort".into());
                }
                self.ensure_value_inhabits_sort(idx, &sort.index_sort)?;
                let j = match self.eval_operand(key, depth + 1) {
                    Ok(j) => j,
                    Err(error) if error.is_model_unavailable() => {
                        return Ok(SelectFold::Reconstruct { array: a });
                    }
                    Err(error) => return Err(error),
                };
                self.ensure_value_inhabits_sort(&j, &sort.index_sort)?;
                if value_eq(&j, idx)? {
                    Ok(SelectFold::Value(self.eval(value, depth + 1)?))
                } else {
                    self.select_over_store_chain(base, idx, depth + 1)
                }
            }
            TermData::App(Symbol::Named(name), args)
                if name == "const-array" && args.len() == 1 =>
            {
                Ok(SelectFold::Value(self.eval(args[0], depth + 1)?))
            }
            TermData::App(Symbol::Named(name), args)
                if name == "lambda-array" && args.len() == 2 =>
            {
                let (bound, body) = self.lambda_array_parts(a, args)?;
                Ok(SelectFold::Value(self.eval_with_binding(
                    bound,
                    self.clone_value(idx)?,
                    body,
                    depth + 1,
                )?))
            }
            _ => {
                // The chain bottomed out at a NON-store, non-const-array base `b`
                // (typically a free array `Var`), and `idx` matched — determinately
                // and unequally — every peeled store index above. By McCarthy,
                // `select(store(b,j,v), i) = select(b, i)` whenever `i != j`, so the
                // value of this read is EXACTLY `select(b, idx)` — INDEPENDENT of the
                // peeled stores' VALUES. Read the base `b` at `idx` DIRECTLY instead
                // of reconstructing the whole store-chain array (the caller's
                // fallback), because that reconstruction eagerly evaluates every
                // stored value, and a stored value can carry an unpinned leaf that is
                // irrelevant to a read that misses that store (e.g. a datatype
                // constructor `(C ... free-array-field ...)` stored under the
                // explicit-constructor array encoding). If `b` itself resolves to a
                // concrete `(default, finite-store)` array, read it; otherwise
                // retain the failure for the caller's original committed-read
                // fallback (fail-closed, never a fabricated value). Rebuilding
                // the same failed base again would be exponential for nested
                // selects because depth-sensitive failures are not memoized.
                // (#g4-store-chain-base-read)
                match self
                    .eval_array_value(a, depth + 1)
                    .map_err(EvalError::operand)
                {
                    Ok(arr) => self.array_select_admitted(&arr, idx).map(SelectFold::Value),
                    Err(reason) if reason.is_model_unavailable() => {
                        Ok(SelectFold::UnresolvedBase { array: a, reason })
                    }
                    Err(error) => Err(error),
                }
            }
        }
    }

    /// A known conditional branch denotes exactly its selected array. Keep
    /// the reconstruction layer's logical depth/work even though no whole
    /// array is materialized, then reuse that branch's semantic read key.
    fn select_conditional_array(
        &self,
        array: TermId,
        [condition, positive, negative]: [TermId; 3],
        idx: &ModelValue,
        depth: usize,
    ) -> EvalResult<SelectFold> {
        self.charge_quantifier_work(1)?;
        let selected = self.conditional_branch(array, condition, positive, negative, depth + 1)?;
        self.select_over_store_chain(selected, idx, depth + 2)
    }

    /// Evaluate `(select array_term _)` at the already-computed index value `idx`
    /// by reading the model's committed per-read value, when the array operand
    /// could NOT be resolved to a concrete `(default, finite-store)` value
    /// (`reconstruct_err` is why). This is the array analogue of
    /// [`Evaluator::eval_uninterpreted_app`].
    ///
    /// `semantic_array` differs from `array_term` only after the lazy fold proved
    /// each peeled store key unequal to this read's index or evaluated a checked
    /// conditional's test and selected its branch. These identities make the
    /// reads equal at this index even when their syntax differs. Unknown keys,
    /// unavailable conditions and arbitrary array aliases never justify a step.
    /// The FIRST committed value for `(semantic_array, index-value)` governs all
    /// later equivalent reads, exposing contradictory model pins in either order.
    /// The ORIGINAL read term still selects the model callback; original array
    /// and read expressions still govern lexical-binding dependence checks.
    ///
    /// If the model does not pin this read, the result is `Unevaluable`
    /// (`reconstruct_err` is surfaced) — fail closed, never assumed.
    fn eval_select_via_model(
        &self,
        term: TermId,
        array_term: TermId,
        semantic_array: TermId,
        idx: &ModelValue,
        reconstruct_err: EvalError,
    ) -> EvalResult<ModelValue> {
        if !reconstruct_err.is_model_unavailable() {
            return Err(reconstruct_err);
        }
        // Consult the value-keyed select graph: proved same read, index values
        // equal ⇒ same element. The original array must be binder-independent;
        // otherwise the same array TermId can denote a different array in each
        // beta environment.
        if !self.term_depends_on_local_binding(array_term)? {
            let graph = self.select_graph.borrow();
            for (at, key_idx, val) in graph.iter() {
                let Sort::Array(array_sort) = self.terms.sort(array_term) else {
                    return Err("array read has non-array sort".into());
                };
                self.ensure_value_inhabits_sort(key_idx, &array_sort.index_sort)?;
                self.ensure_value_inhabits_sort(idx, &array_sort.index_sort)?;
                if *at == semantic_array
                    && congruence_keys_equal(
                        std::slice::from_ref(key_idx),
                        std::slice::from_ref(idx),
                    )?
                {
                    return self.clone_value(val);
                }
            }
        }
        // As for UF applications, adopting a per-TermId committed read is not
        // sound when this occurrence depends on the active lambda environment.
        if self.term_depends_on_local_binding(term)? {
            return Err("model-backed context-dependent array read is unsupported".into());
        }
        // First time this `(array-term, index-value)` key is seen: adopt the
        // model's committed per-read value as the representative. A model that
        // does not pin the read leaves the gate unable to confirm (fail closed).
        let val = self.model.array_select_value(term).ok_or(reconstruct_err)?;
        self.admit_value(&val)?;
        let copied_index = self.clone_value(idx)?;
        let copied_value = self.clone_value(&val)?;
        self.select_graph
            .borrow_mut()
            .push((semantic_array, copied_index, copied_value));
        Ok(val)
    }

    /// Most-recent scoped beta binding for `term`, if any.
    fn local_binding(&self, term: TermId) -> EvalResult<Option<ModelValue>> {
        for binding in self.local_bindings.borrow().iter().rev() {
            if binding.binds(self.terms, term) {
                if let LocalVariable::Named(_, sort) = &binding.variable {
                    if self.terms.sort(term) != sort {
                        return Err(quantifier::QuantifierRejection::BindingSortMismatch.into());
                    }
                }
                return self.clone_value(&binding.value).map(Some);
            }
        }
        Ok(None)
    }

    /// Whether `root` syntactically contains any currently bound term.
    ///
    /// Per-TermId model commitments may be reused inside a beta environment
    /// only when this is false. A conservative positive result loses coverage
    /// but cannot admit a value from the wrong lambda instance.
    fn term_depends_on_local_binding(&self, root: TermId) -> EvalResult<bool> {
        let bindings = self.local_bindings.borrow();
        if bindings.is_empty() {
            return Ok(false);
        }

        let mut stack = vec![root];
        let mut seen = HashSet::new();
        while let Some(term) = stack.pop() {
            self.admit_evaluation(1, 0)?;
            self.charge_quantifier_work(1)?;
            if bindings
                .iter()
                .any(|binding| binding.binds(self.terms, term))
            {
                return Ok(true);
            }
            if seen.insert(term) {
                self.push_binding_scan_children(term, &mut stack)?;
            }
        }
        Ok(false)
    }

    /// Evaluate `body` with one scoped lambda variable value.
    fn eval_with_binding(
        &self,
        bound: TermId,
        value: ModelValue,
        body: TermId,
        depth: usize,
    ) -> EvalResult<ModelValue> {
        let restore_len = self.local_bindings.borrow().len();
        self.local_bindings.borrow_mut().push(LocalBinding {
            variable: LocalVariable::Term(bound),
            value,
        });
        let _guard = LocalBindingGuard {
            bindings: &self.local_bindings,
            restore_len,
        };
        self.eval(body, depth)
    }

    /// Whether `needle` occurs syntactically in `root`.
    ///
    /// A negative result proves that a lambda body is binder-independent and
    /// may be materialized as a constant array. A conservative positive result
    /// (for example under a nested binder that reuses the same TermId) merely
    /// loses completeness and therefore remains sound.
    fn term_contains(&self, root: TermId, needle: TermId) -> EvalResult<bool> {
        let mut stack = vec![root];
        let mut seen = HashSet::new();
        while let Some(term) = stack.pop() {
            self.admit_evaluation(1, 0)?;
            if self.functional_capture_depth.get() != 0 {
                self.charge_functional_work(1)?;
            }
            self.charge_quantifier_work(1)?;
            if term == needle {
                return Ok(true);
            }
            if seen.insert(term) {
                self.push_binding_scan_children(term, &mut stack)?;
            }
        }
        Ok(false)
    }

    // ----- strings ---------------------------------------------------------

    fn eval_string(&self, name: &str, args: &[TermId], depth: usize) -> EvalResult<ModelValue> {
        match name {
            "str.len" => {
                let [s] = exactly(args)?;
                let s = self.eval_str(s, depth + 1)?;
                Ok(ModelValue::Int(BigInt::from(s.chars().count())))
            }
            "str.++" => {
                let mut out = String::new();
                for &a in args {
                    out.push_str(&self.eval_str(a, depth + 1)?);
                }
                Ok(ModelValue::Str(out))
            }
            "str.at" => {
                let [s, i] = exactly(args)?;
                let s = self.eval_str(s, depth + 1)?;
                let idx = as_integer(&self.eval_operand(i, depth + 1)?)?;
                let chars: Vec<char> = s.chars().collect();
                match idx.to_usize_checked().filter(|&k| k < chars.len()) {
                    Some(k) => Ok(ModelValue::Str(chars[k].to_string())),
                    None => Ok(ModelValue::Str(String::new())),
                }
            }
            // `str.replace_re` / `str.replace_re_all`.
            //
            // RegLan has no `ModelValue`, so a regex argument cannot be
            // evaluated as a value; like `str.in_re` two arms below, these pass
            // the regex term STRUCTURALLY to this crate's own interval matcher.
            // The SMT-LIB leftmost/shortest clauses distinguish single empty
            // matches from replace-all's non-empty matches. Both are evaluated
            // independently by [`crate::regex::replace`].
            //
            // This previously accepted only `(str.to_re <non-empty literal>)`
            // and reported `Unevaluable` for every other regex, so the gate
            // refused to confirm any model mentioning one and published a
            // computed `sat` as `unknown`.
            "str.replace_re" | "str.replace_re_all" => {
                let [subject, regex, replacement] = exactly(args)?;
                let subject = self.eval_str(subject, depth + 1)?;
                let replacement = self.eval_str(replacement, depth + 1)?;
                let owner = scratch_admission::ScratchAdmission::new(self);
                let out = owner.finish(crate::regex::replace(
                    self.terms,
                    name,
                    &subject,
                    regex,
                    &replacement,
                    name == "str.replace_re_all",
                    depth + 1,
                    |term| self.eval_str(term, depth + 2),
                    &owner,
                ))?;
                Ok(ModelValue::Str(out))
            }
            "str.in_re" | "str.in.re" => {
                let [subject, regex] = exactly(args)?;
                let subject = self.eval_str(subject, depth + 1)?;
                let owner = scratch_admission::ScratchAdmission::new(self);
                let member = owner.finish(crate::regex::matches(
                    self.terms,
                    &subject,
                    regex,
                    depth + 1,
                    |term| self.eval_str(term, depth + 2),
                    &owner,
                ))?;
                Ok(ModelValue::Bool(member))
            }
            _ => Err(format!("unsupported string operator {name}").into()),
        }
    }

    fn eval_str(&self, term: TermId, depth: usize) -> EvalResult<String> {
        match self.eval_operand(term, depth)? {
            ModelValue::Str(s) => Ok(s),
            _ => Err("expected a string value".into()),
        }
    }

    // ----- datatypes -------------------------------------------------------

    /// Resolve the datatype definition for a sort: directly for
    /// `Sort::Datatype` and the builtin Complex product, or via the model's registry for a datatype abstracted
    /// to `Sort::Uninterpreted(name)` (see [`ModelView::datatype_def`]). Any
    /// other sort is not a datatype.
    fn dt_of_sort(&self, sort: &Sort) -> Option<ay_core::DatatypeSort> {
        match sort {
            Sort::Datatype(_) | Sort::Complex => sort.datatype_definition().cloned(),
            Sort::Uninterpreted(name) => self.model.datatype_def(name),
            _ => None,
        }
    }

    fn eval_datatype(
        &self,
        term: TermId,
        name: &str,
        args: &[TermId],
        depth: usize,
    ) -> EvalResult<DatatypeEvaluation> {
        // Constructor ownership comes from the declared result sort, never
        // from a successful model callback after malformed source evaluation.
        if let Some(dt) = self.dt_of_sort(self.terms.sort(term)) {
            if let Some(ctor) = dt.constructors.iter().find(|c| c.name == name) {
                if ctor.fields.len() != args.len()
                    || args
                        .iter()
                        .zip(&ctor.fields)
                        .any(|(&arg, field)| self.terms.sort(arg) != &field.sort)
                {
                    return Err(format!("constructor {name} signature mismatch").into());
                }
                let vals = self.eval_all(args, depth)?;
                return Ok(DatatypeEvaluation::Value(ModelValue::Datatype {
                    ctor: name.to_string(),
                    args: vals,
                }));
            }
        }

        let Some(&argument) = args.first() else {
            return Ok(DatatypeEvaluation::NotDatatype);
        };
        let Some(dt) = self.dt_of_sort(self.terms.sort(argument)) else {
            return Ok(DatatypeEvaluation::NotDatatype);
        };
        if let Some(target) = name.strip_prefix("is-") {
            if dt.constructors.iter().any(|c| c.name == target) {
                if args.len() != 1 {
                    return Err("datatype tester arity mismatch".into());
                }
                if self.terms.sort(term) != &Sort::Bool {
                    return Err("datatype tester result is not Bool".into());
                }
                let value = self.eval_operand(args[0], depth + 1)?;
                self.ensure_value_inhabits_sort(&value, self.terms.sort(args[0]))?;
                let ModelValue::Datatype { ctor, .. } = value else {
                    return Err("tester argument is not a datatype value".into());
                };
                return Ok(DatatypeEvaluation::Value(ModelValue::Bool(ctor == target)));
            }
        }
        let mut selector = false;
        for field in dt.constructors.iter().flat_map(|c| &c.fields) {
            if field.name == name {
                selector = true;
                if &field.sort != self.terms.sort(term) {
                    return Err("datatype selector result sort mismatch".into());
                }
            }
        }
        if !selector {
            return Ok(DatatypeEvaluation::NotDatatype);
        }
        if args.len() != 1 {
            return Err("datatype selector arity mismatch".into());
        }
        // Once the declared selector is known, a failed receiver is not an
        // invitation to retry it as an ordinary UF argument. Only missing
        // model data permits the callback-only selector fallback below.
        match self.eval_operand(args[0], depth + 1) {
            Ok(value) => {
                self.ensure_value_inhabits_sort(&value, self.terms.sort(args[0]))?;
                self.project_selector(&dt, name, value)
            }
            Err(error) if error.is_model_unavailable() => self
                .eval_selector_via_model(term, name, args[0], error)
                .map(DatatypeEvaluation::Value),
            Err(error) => Err(error),
        }
    }

    /// Resolve a datatype-selector application `(sel arg)` — `sel` a genuine
    /// field selector of `arg`'s datatype — whose ARGUMENT the gate could not
    /// reduce to a concrete datatype value (`arg_err` is why), by reading the
    /// model's committed value for the WHOLE selector application.
    ///
    /// This is the datatype-selector analogue of
    /// [`eval_select_via_model`](Self::eval_select_via_model) /
    /// [`eval_uninterpreted_app`](Self::eval_uninterpreted_app): a datatype
    /// selector projects a scalar (or nested-datatype) field, and under the eager
    /// datatype-in-array lowering the selector-over-array read
    /// `(fld_rhs (select <store-chain> i))` is itself a bit-blasted term with its
    /// own committed model value — the SAME value `get-value` would report — even
    /// when the gate cannot independently rebuild the datatype value flowing into
    /// it (its array operand bottoms out in a free base array the gate does not
    /// reconstruct, or a stored constructor carries an unpinned field the read
    /// never touches). Reading that committed value here closes the completeness
    /// gap the explicit-constructor store encoding opened (#g4-dt-selector-via-model).
    ///
    /// SOUNDNESS. `uf_app_value` returns the model's committed value for THIS
    /// exact application term (via the solver's own model evaluator), never a
    /// fabricated one, and yields `None` when the model does not pin it (⇒ fail
    /// closed to the original `arg_err`). Single-valuedness is enforced exactly as
    /// for uninterpreted-function applications: the value is keyed in `uf_graph`
    /// by the selector name plus the argument's committed representative, so two
    /// selector applications whose arguments the model pins EQUAL resolve to the
    /// SAME gate value — a model that pins them differently is surfaced (the
    /// enclosing (dis)equality then evaluates against one shared value), not
    /// honoured. When the argument has no committed representative the value is
    /// still the single committed value of this one term, so no wrong `Sat` can be
    /// manufactured; and this path only CONFIRMS a value — the constructor-
    /// injectivity-through-array-equality hazard the surrounding gate guards is
    /// decided by the array-equality machinery, which this does not touch.
    fn eval_selector_via_model(
        &self,
        term: TermId,
        name: &str,
        arg: TermId,
        arg_err: EvalError,
    ) -> EvalResult<ModelValue> {
        if !arg_err.is_model_unavailable() {
            return Err(arg_err);
        }
        // Unlike structural projection from a concrete constructor, this path
        // reads ambient per-TermId commitments for both the selector and its
        // argument. Neither is indexed by the current beta environment.
        if self.term_depends_on_local_binding(term)? {
            return Err("model-backed context-dependent selector is unsupported".into());
        }
        // A committed representative for the argument (its selector/uf/array
        // committed value, or a pinned leaf), used only to key single-valuedness.
        let arg_key = self
            .model
            .uf_app_value(arg)
            .or_else(|| self.model.array_select_value(arg))
            .or_else(|| self.model.leaf_value(arg));
        if let Some(value) = &arg_key {
            self.ensure_value_inhabits_sort(value, self.terms.sort(arg))?;
        }
        // STRUCTURAL-FIRST (#dt-selector-structural, M1 wrong-SAT root cause):
        // when the argument's own committed value is a datatype value built
        // with the selector's OWN constructor, the selector application is
        // fully determined by SMT-LIB selector semantics — `(sel (C .. a_i ..))
        // = a_i` — and MUST evaluate to that structural projection. The
        // committed per-application value below is consulted ONLY for
        // genuinely under-specified applications (wrong-constructor argument,
        // or no committed argument value at all): honouring a committed
        // per-application value that contradicts the structural projection
        // would let the gate confirm a model that violates
        // `pred(succ(t)) = t`. This branch is a pure function of the
        // argument's committed value, so single-valuedness holds by
        // construction and no `uf_graph` keying is needed.
        if let Some(ModelValue::Datatype { ctor, args: cargs }) = &arg_key {
            if let Some(dt) = self.dt_of_sort(&self.terms.sort(arg).clone()) {
                if let Some(cons) = dt.constructors.iter().find(|c| &c.name == ctor) {
                    if let Some(idx) = cons.fields.iter().position(|f| f.name == name) {
                        if let Some(v) = cargs.get(idx) {
                            return self.clone_value(v);
                        }
                    }
                }
            }
        }
        if let Some(key) = &arg_key {
            let graph = self.uf_graph.borrow();
            let arg_sort = [self.terms.sort(arg)];
            for (f, instance, keys, val) in graph.iter() {
                if f == name
                    && instance.is_none()
                    && self.congruence_keys_equal_at_sorts(
                        keys,
                        std::slice::from_ref(key),
                        &arg_sort,
                    )?
                {
                    return self.clone_value(val);
                }
            }
        }
        let val = self.model.uf_app_value(term).ok_or(arg_err)?;
        self.admit_value(&val)?;
        if let Some(key) = arg_key {
            self.admit_evaluation(0, name.len())?;
            let copied = self.clone_value(&val)?;
            self.push_uf_graph_entry((name.to_string(), None, vec![key], copied))?;
        }
        Ok(val)
    }

    /// Project selector `sel` out of a datatype value, per the datatype `dt`.
    /// A valid value built with a different declared constructor explicitly
    /// grants underspecified application semantics; malformed values do not.
    fn project_selector(
        &self,
        dt: &ay_core::DatatypeSort,
        sel: &str,
        value: ModelValue,
    ) -> EvalResult<DatatypeEvaluation> {
        let ModelValue::Datatype { ctor, args } = value else {
            return Err("selector argument is not a datatype value".into());
        };
        let Some(cons) = dt.constructors.iter().find(|c| c.name == ctor) else {
            return Err("selector: value constructor not found in datatype".into());
        };
        if args.len() != cons.fields.len() {
            return Err("selector: value constructor arity mismatch".into());
        }
        match cons.fields.iter().position(|f| f.name == sel) {
            Some(idx) => self.clone_value(&args[idx]).map(DatatypeEvaluation::Value),
            // Only a valid value of another declared constructor grants this
            // underspecified operation, not malformed or unavailable data.
            None => Ok(DatatypeEvaluation::WrongConstructor),
        }
    }
}

// ===========================================================================
// free helpers
// ===========================================================================

/// The exact value of an indexed FP special constant, if `name` is one.
///
/// `(_ NaN eb sb)`, `(_ +zero eb sb)`, `(_ -zero eb sb)`, `(_ +oo eb sb)` and
/// `(_ -oo eb sb)` are the SMT-LIB spellings of the FP special values. They are
/// nullary CONSTANTS, but they are `Symbol::Indexed`, and the gate routed every
/// indexed symbol to the bitvector operator table — where they are, correctly,
/// unrecognized. The gate then could not confirm any model mentioning one and
/// degraded the verdict, so `(assert (fp.isNaN (_ NaN 11 53)))` was published
/// as `unknown` even though AY refutes its negation as `unsat`.
///
/// SMT-LIB counts the hidden bit in `sb`, so the stored fraction field is
/// `sb - 1` bits. NaN is a single value in the FP sort (payloads are not
/// observable), so the canonical quiet NaN is an exact representative.
///
/// Returns `None` for any other indexed symbol, which keeps the bitvector path
/// and the gate's fail-closed discipline untouched: an out-of-range width
/// declines here rather than producing a truncated value.
fn fp_special_constant(name: &str, indices: &[u32]) -> Option<ModelValue> {
    let [eb, sb] = <[u32; 2]>::try_from(indices).ok()?;
    if !crate::fp::data_format_supported(eb, sb) {
        return crate::fp_exact::special(name, indices);
    }
    let all_ones = if eb == 64 { u64::MAX } else { (1u64 << eb) - 1 };
    let (sign, exponent, significand) = match name {
        "+zero" => (false, 0, 0),
        "-zero" => (true, 0, 0),
        "+oo" => (false, all_ones, 0),
        "-oo" => (true, all_ones, 0),
        "NaN" => (false, all_ones, 1u128 << (sb - 2)),
        _ => return None,
    };
    Some(ModelValue::FloatingPoint {
        sign,
        exponent,
        significand,
        exponent_bits: eb,
        significand_bits: sb,
    })
}

/// Reinterpret an `eb + sb`-wide bitvector as the IEEE fields of an FP value.
///
/// This is SMT-LIB `((_ to_fp eb sb) <bv>)`: a pure re-reading of the same
/// bits, with no rounding and no value change. Splitting them out here keeps
/// the gate independent of the solver's FP code.
///
/// Declines (returns `None`) unless the operand is a bitvector of EXACTLY the
/// width the indices call for, and unless its format is in the original data
/// envelope or is binary128. A width mismatch is a malformed term rather
/// than something to coerce, so it falls through and fails closed.
fn fp_from_ieee_bits(indices: &[u32], value: &ModelValue) -> Option<ModelValue> {
    let [eb, sb] = <[u32; 2]>::try_from(indices).ok()?;
    if !crate::fp::data_format_supported(eb, sb) {
        let ModelValue::BitVec { width, value } = value else {
            return None;
        };
        return crate::fp_exact::decode(value, *width, eb, sb);
    }
    let ModelValue::BitVec { width, value } = value else {
        return None;
    };
    if *width != eb + sb || value.is_negative() || value.bits() > u64::from(*width) {
        return None;
    }
    let fraction_bits = sb - 1;
    let exponent_mask = if eb == 64 { u64::MAX } else { (1u64 << eb) - 1 };
    let fraction_mask = u128::MAX >> (129 - sb);
    // `value` was checked to be in `0 <= value < 2^width`, so these
    // shifts stay in range and both fields are guaranteed to fit their masks.
    let sign = ((value >> (eb + sb - 1) as usize) & BigInt::from(1u8)) == BigInt::from(1u8);
    let exponent =
        u64::try_from((value >> fraction_bits as usize) & BigInt::from(exponent_mask)).ok()?;
    let significand = u128::try_from(value & BigInt::from(fraction_mask)).ok()?;
    Some(ModelValue::FloatingPoint {
        sign,
        exponent,
        significand,
        exponent_bits: eb,
        significand_bits: sb,
    })
}

/// Whether `value` is a floating-point ZERO in the same format as `like`.
///
/// The residue [`Evaluator::eval_fp`] checks after adopting the model's choice
/// for `fp.min`/`fp.max` of `+0` and `-0`. SMT-LIB frees WHICH zero comes back;
/// it does not free the result from being a zero of that format at all, so a
/// model answering `1.0` there is still refuted. Deliberately written from the
/// raw fields rather than routed through [`crate::fp`]: the check must hold
/// even for a format that module's arithmetic envelope declines.
fn is_zero_of_format(value: &ModelValue, like: &ModelValue) -> bool {
    if matches!(value, ModelValue::FloatingPointExact { .. })
        || matches!(like, ModelValue::FloatingPointExact { .. })
    {
        return crate::fp_exact::is_zero_of_format(value, like);
    }
    let (
        &ModelValue::FloatingPoint {
            exponent,
            significand,
            exponent_bits,
            significand_bits,
            ..
        },
        &ModelValue::FloatingPoint {
            exponent_bits: like_eb,
            significand_bits: like_sb,
            ..
        },
    ) = (value, like)
    else {
        return false;
    };
    exponent == 0 && significand == 0 && exponent_bits == like_eb && significand_bits == like_sb
}

/// How many values the ELEMENT sort of a set carrier has.
///
/// A set is modelled as `(Array T Bool)`, so this is the cardinality of `T`.
/// `crate::sets` needs it to decide whether an index exists that neither
/// operand's store overrides — a fact about the sort, which the VALUE cannot
/// carry.
///
/// Unknown beats a guess: an uninterpreted sort has whatever cardinality the
/// model gives it, and claiming it is infinite would decide `set.subset` on an
/// assumption rather than on the model.
fn element_domain_size(sort: &Sort) -> crate::sets::DomainSize {
    use crate::sets::DomainSize;
    let Sort::Array(array) = sort else {
        return DomainSize::Unknown;
    };
    match &array.index_sort {
        Sort::Bool => DomainSize::Finite(BigInt::from(2u8)),
        Sort::BitVec(bv) => DomainSize::Finite(BigInt::from(1u8) << bv.width as usize),
        // A floating-point sort is finite, but its distinct VALUES are fewer
        // than its bit patterns (all the NaN encodings are one value), so its
        // exact cardinality is not `2^(eb+sb)`. Unknown rather than wrong.
        Sort::FloatingPoint(_, _) => DomainSize::Unknown,
        Sort::Int | Sort::Real | Sort::String => DomainSize::Infinite,
        _ => DomainSize::Unknown,
    }
}

/// Destructure exactly `N` arguments, or fail closed.
fn exactly<const N: usize>(args: &[TermId]) -> Result<[TermId; N], String> {
    <[TermId; N]>::try_from(args).map_err(|_| format!("expected {N} arguments, got {}", args.len()))
}

/// Evaluate a comparison chain where at least one operand is algebraic.
///
/// Each adjacent pair is decided by the SIGN of `a - b`, computed by interval
/// refinement. An undecided sign (the refinement budget ran out, or the pair
/// spans two different extensions) is an error the gate fails closed on --
/// never a `false`, which would be an unearned refutation.
fn compare_with_algebraic(name: &str, vals: &[ModelValue]) -> Result<bool, String> {
    use core::cmp::Ordering;

    let carrier = vals
        .iter()
        .find_map(|v| match v {
            ModelValue::Algebraic(a) => Some(a.as_ref().clone()),
            _ => None,
        })
        .ok_or_else(|| "no algebraic operand".to_string())?;

    let lift = |v: &ModelValue| -> Result<crate::algebraic::Algebraic, String> {
        match v {
            ModelValue::Algebraic(a) => Ok(a.as_ref().clone()),
            other => Ok(carrier.with_rational(as_rational(other)?)),
        }
    };

    for pair in vals.windows(2) {
        let difference = lift(&pair[0])?
            .add(&lift(&pair[1])?.neg())
            .map_err(|e| format!("algebraic comparison declined: {e:?}"))?;
        let ordering = difference
            .sign()
            .map(|s| match s {
                0 => Ordering::Equal,
                n if n < 0 => Ordering::Less,
                _ => Ordering::Greater,
            })
            .ok_or_else(|| "algebraic sign undecided within the refinement budget".to_string())?;
        let holds = match name {
            "<" => ordering == Ordering::Less,
            "<=" => ordering != Ordering::Greater,
            ">" => ordering == Ordering::Greater,
            ">=" => ordering != Ordering::Less,
            _ => return Err(format!("unsupported comparison {name}")),
        };
        if !holds {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Whether a value carries an algebraic number.
fn is_algebraic(v: &ModelValue) -> bool {
    matches!(v, ModelValue::Algebraic(_))
}

/// Which fold `fold_algebraic` performs.
enum AlgebraicFold {
    Sum,
    Product,
}

/// Fold a mixed list of algebraic and rational operands inside one extension.
///
/// Every rational is lifted into the algebraic operand's extension, so exact
/// arithmetic applies throughout. The result collapses back to `Real` when it
/// reduces to a rational -- `sqrt(2) * sqrt(2)` IS 2 -- so downstream
/// comparisons see the simplest exact form.
fn fold_algebraic(vals: &[ModelValue], fold: AlgebraicFold) -> Result<ModelValue, String> {
    let first = vals
        .iter()
        .find_map(|v| match v {
            ModelValue::Algebraic(a) => Some(a.as_ref().clone()),
            _ => None,
        })
        .ok_or_else(|| "no algebraic operand".to_string())?;

    let mut acc = match fold {
        AlgebraicFold::Sum => first.with_rational(BigRational::zero()),
        AlgebraicFold::Product => first.with_rational(BigRational::from(BigInt::from(1))),
    };
    for v in vals {
        let operand = match v {
            ModelValue::Algebraic(a) => a.as_ref().clone(),
            other => first.with_rational(as_rational(other)?),
        };
        acc = match fold {
            AlgebraicFold::Sum => acc.add(&operand),
            AlgebraicFold::Product => acc.mul(&operand),
        }
        .map_err(|e| format!("algebraic arithmetic declined: {e:?}"))?;
    }
    Ok(match acc.as_rational() {
        Some(q) => ModelValue::Real(q),
        None => ModelValue::Algebraic(Box::new(acc)),
    })
}

fn as_rational(v: &ModelValue) -> Result<BigRational, String> {
    match v {
        ModelValue::Int(n) => Ok(BigRational::from(n.clone())),
        ModelValue::Real(r) => Ok(r.clone()),
        _ => Err("expected a numeric (Int/Real) value".to_string()),
    }
}

fn as_integer(v: &ModelValue) -> Result<BigInt, String> {
    match v {
        ModelValue::Int(n) => Ok(n.clone()),
        ModelValue::Real(r) if r.is_integer() => Ok(r.to_integer()),
        _ => Err("expected an integer value".to_string()),
    }
}

/// Wrap an exact rational into the result sort: `Int` requires integrality.
fn wrap_numeric(r: BigRational, sort: &Sort) -> Result<ModelValue, String> {
    match sort {
        Sort::Int => {
            if r.is_integer() {
                Ok(ModelValue::Int(r.to_integer()))
            } else {
                Err("non-integer result in an Int context".to_string())
            }
        }
        Sort::Real => Ok(ModelValue::Real(r)),
        _ => Err("arithmetic result sort is neither Int nor Real".to_string()),
    }
}

/// SMT-LIB Euclidean division/remainder: `a = b*q + r` with `0 <= r < |b|`.
/// Returns `None` when `b == 0` (under-specified).
fn euclid(a: &BigInt, b: &BigInt) -> Option<(BigInt, BigInt)> {
    if b.is_zero() {
        return None;
    }
    let abs_b = b.abs();
    let r = a.mod_floor(&abs_b); // in [0, |b|)
    let q = (a - &r) / b; // exact
    Some((q, r))
}

fn compare_rat(op: &str, a: &BigRational, b: &BigRational) -> bool {
    match op {
        "<" => a < b,
        "<=" => a <= b,
        ">" => a > b,
        ">=" => a >= b,
        _ => false,
    }
}

/// Names of the non-indexed bitvector operators handled by [`bitvec::eval_named`].
fn is_bv_named(name: &str) -> bool {
    matches!(
        name,
        "bvadd"
            | "bvsub"
            | "bvmul"
            | "bvudiv"
            | "bvurem"
            | "bvsdiv"
            | "bvsrem"
            | "bvsmod"
            | "bvand"
            | "bvor"
            | "bvxor"
            | "bvnot"
            | "bvnand"
            | "bvnor"
            | "bvxnor"
            | "bvneg"
            | "bvshl"
            | "bvlshr"
            | "bvashr"
            | "concat"
            | "bvcomp"
            | "bv2nat"
            | "bvult"
            | "bvule"
            | "bvugt"
            | "bvuge"
            | "bvslt"
            | "bvsle"
            | "bvsgt"
            | "bvsge"
    )
}

/// Convenience: a checked `BigInt -> usize`.
trait ToUsizeChecked {
    fn to_usize_checked(&self) -> Option<usize>;
}

impl ToUsizeChecked for BigInt {
    fn to_usize_checked(&self) -> Option<usize> {
        use num_traits::ToPrimitive;
        if self.is_negative() {
            None
        } else {
            self.to_usize()
        }
    }
}
