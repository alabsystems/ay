// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Hand-constructed `(assertions, model)` pairs exercising the gate:
//!
//! * (a) models that SATISFY ⇒ `ConfirmedSat`;
//! * (b) models that VIOLATE an assertion ⇒ `ModelViolates` — including
//!   analogues of real wrong-`sat` bugs (seq prefix, array select, datatype
//!   recognizer, seq.indexof);
//! * (c) under-specified / unimplemented / unpinned / quantified ⇒
//!   `CannotConfirm` (never a false `ConfirmedSat`).

use super::*;
use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort, Symbol, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;
use std::cell::Cell;
use std::collections::HashMap;

/// A trivial stub model: a fixed map from leaf `TermId` to value.
struct StubModel {
    leaves: HashMap<TermId, ModelValue>,
}

impl StubModel {
    fn new() -> Self {
        Self {
            leaves: HashMap::new(),
        }
    }
    fn with(mut self, t: TermId, v: ModelValue) -> Self {
        self.leaves.insert(t, v);
        self
    }
}

impl ModelView for StubModel {
    fn leaf_value(&self, t: TermId) -> Option<ModelValue> {
        self.leaves.get(&t).cloned()
    }
}

fn int(n: i64) -> BigInt {
    BigInt::from(n)
}

fn sqrt_two_between(lo: BigRational, hi: BigRational) -> ModelValue {
    ModelValue::Algebraic(Box::new(
        algebraic::Algebraic::root_of(algebraic::integer_poly(&[-2, 0, 1]), lo, hi)
            .expect("the interval isolates positive sqrt(2)"),
    ))
}

fn app(ts: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
    ts.mk_app(Symbol::named(name), args, sort)
}

fn verdict(ts: &TermStore, model: &dyn ModelView, asserts: &[TermId]) -> GateVerdict {
    confirm_model(ts, model, asserts)
}

fn assert_confirmed(v: &GateVerdict) {
    assert!(
        matches!(v, GateVerdict::ConfirmedSat),
        "expected ConfirmedSat, got {v:?}"
    );
}
fn assert_violates(v: &GateVerdict) {
    assert!(
        matches!(v, GateVerdict::ModelViolates { .. }),
        "expected ModelViolates, got {v:?}"
    );
}
fn assert_cannot(v: &GateVerdict) {
    assert!(
        matches!(v, GateVerdict::CannotConfirm { .. }),
        "expected CannotConfirm, got {v:?}"
    );
}

// ===========================================================================
// (a) Satisfying models ⇒ ConfirmedSat
// ===========================================================================

include!("tests/scalar_regex_and_fp.rs");

include!("tests/division_and_fallbacks.rs");

include!("tests/arrays_and_lambda.rs");

include!("tests/violations_and_short_circuit.rs");

// ===========================================================================
// (d) Uninterpreted-function applications — value-keyed function graph
//
// An uninterpreted function is single-valued: two applications whose ARGUMENTS
// evaluate to equal values must return the same value. The gate builds a
// value-keyed graph as it evaluates (`uf_app_value` supplies the committed
// per-application value); the FIRST application to reach a given
// `(name, arg-values)` key fixes the value for every later application with the
// same key. This is what catches the QF_UFLIA / array-select wrong-model class
// where a degenerate integer assignment collapses two distinct applications'
// arguments to the same value while the model pins them to different results.
// ===========================================================================

/// A model implementing only the original one-argument unconstrained hook.
///
/// Its tests protect source compatibility and, more importantly, prove that
/// the new typed default does not silently extend this legacy authority to
/// division-by-zero applications.
struct LegacyUnconstrainedModel {
    leaves: HashMap<TermId, ModelValue>,
    unconstrained_apps: HashMap<TermId, ModelValue>,
    unconstrained_calls: Cell<usize>,
}

impl LegacyUnconstrainedModel {
    fn new() -> Self {
        Self {
            leaves: HashMap::new(),
            unconstrained_apps: HashMap::new(),
            unconstrained_calls: Cell::new(0),
        }
    }

    fn leaf(mut self, t: TermId, v: ModelValue) -> Self {
        self.leaves.insert(t, v);
        self
    }

    fn unconstrained(mut self, t: TermId, v: ModelValue) -> Self {
        self.unconstrained_apps.insert(t, v);
        self
    }
}

impl ModelView for LegacyUnconstrainedModel {
    fn leaf_value(&self, t: TermId) -> Option<ModelValue> {
        self.leaves.get(&t).cloned()
    }

    fn unconstrained_app_value(&self, t: TermId) -> Option<ModelValue> {
        self.unconstrained_calls
            .set(self.unconstrained_calls.get() + 1);
        self.unconstrained_apps.get(&t).cloned()
    }
}

/// A stub model that also answers `uf_app_value` for whole application terms.
struct UfStubModel {
    leaves: HashMap<TermId, ModelValue>,
    uf_apps: HashMap<TermId, ModelValue>,
    unconstrained_apps: HashMap<TermId, (ProvenUnconstrainedKind, ModelValue)>,
    unconstrained_calls: Cell<usize>,
    selects: HashMap<TermId, ModelValue>,
    projections: HashMap<TermId, usize>,
    projection_errors: HashMap<TermId, String>,
}

impl UfStubModel {
    fn new() -> Self {
        Self {
            leaves: HashMap::new(),
            uf_apps: HashMap::new(),
            unconstrained_apps: HashMap::new(),
            unconstrained_calls: Cell::new(0),
            selects: HashMap::new(),
            projections: HashMap::new(),
            projection_errors: HashMap::new(),
        }
    }
    fn leaf(mut self, t: TermId, v: ModelValue) -> Self {
        self.leaves.insert(t, v);
        self
    }
    fn uf(mut self, t: TermId, v: ModelValue) -> Self {
        self.uf_apps.insert(t, v);
        self
    }
    fn unconstrained(mut self, t: TermId, kind: ProvenUnconstrainedKind, v: ModelValue) -> Self {
        self.unconstrained_apps.insert(t, (kind, v));
        self
    }
    fn sel(mut self, t: TermId, v: ModelValue) -> Self {
        self.selects.insert(t, v);
        self
    }
    fn projection(mut self, t: TermId, selected: usize) -> Self {
        self.projections.insert(t, selected);
        self
    }
    fn projection_error(mut self, t: TermId, detail: &str) -> Self {
        self.projection_errors.insert(t, detail.to_string());
        self
    }
}

impl ModelView for UfStubModel {
    fn leaf_value(&self, t: TermId) -> Option<ModelValue> {
        self.leaves.get(&t).cloned()
    }
    fn projection_argument(&self, t: TermId) -> Result<Option<usize>, ProjectionLookupError> {
        if let Some(detail) = self.projection_errors.get(&t) {
            return Err(ProjectionLookupError::inconsistent_model(detail.clone()));
        }
        Ok(self.projections.get(&t).copied())
    }
    fn uf_app_value(&self, t: TermId) -> Option<ModelValue> {
        self.uf_apps.get(&t).cloned()
    }
    fn proven_unconstrained_app_value(
        &self,
        t: TermId,
        kind: ProvenUnconstrainedKind,
    ) -> Option<ModelValue> {
        self.unconstrained_calls
            .set(self.unconstrained_calls.get() + 1);
        self.unconstrained_apps
            .get(&t)
            .and_then(|(expected, value)| (*expected == kind).then(|| value.clone()))
    }
    fn array_select_value(&self, t: TermId) -> Option<ModelValue> {
        self.selects.get(&t).cloned()
    }
}

include!("tests/uf_congruence_and_projection.rs");

// ===========================================================================
// (e) Array-`select` reads via the model — value-keyed select graph
//
// `select` over an array is a single-valued function of the index. When the
// gate cannot resolve the array operand to a concrete `(default, finite-store)`
// value (a partial / unreconstructable array leaf), it reads the model's
// committed per-read value (`array_select_value`) but keys reads by
// `(array-term, index-value)` and takes the first committed value per key. Two
// reads of the SAME array at index values that evaluate EQUAL therefore resolve
// to one element — exposing (rather than honouring) a model that pins them to
// different values — and, because the gate evaluates indices itself, a
// degenerate array whose reads contradict an asserted (in)equality evaluates the
// assertion to `false`. This is the array analogue of the UF value-keyed graph
// above, closing the array-`select` wrong-model class (#array-select-collapse)
// at the gate even when the theory's array interpretation is unavailable.
// ===========================================================================

/// A stub model that pins scalar leaves and answers `array_select_value` for
/// whole `(select A i)` application terms — but deliberately does NOT pin the
/// array leaf itself, so the gate must go through the `select`-via-model fallback
/// (mirroring the real gate, whose fallback fires exactly when the theory array
/// interpretation cannot be reconstructed).
struct ArraySelectStubModel {
    leaves: HashMap<TermId, ModelValue>,
    selects: HashMap<TermId, ModelValue>,
}

impl ArraySelectStubModel {
    fn new() -> Self {
        Self {
            leaves: HashMap::new(),
            selects: HashMap::new(),
        }
    }
    fn leaf(mut self, t: TermId, v: ModelValue) -> Self {
        self.leaves.insert(t, v);
        self
    }
    fn sel(mut self, t: TermId, v: ModelValue) -> Self {
        self.selects.insert(t, v);
        self
    }
}

impl ModelView for ArraySelectStubModel {
    fn leaf_value(&self, t: TermId) -> Option<ModelValue> {
        self.leaves.get(&t).cloned()
    }
    fn array_select_value(&self, t: TermId) -> Option<ModelValue> {
        self.selects.get(&t).cloned()
    }
}

include!("tests/array_select_models.rs");

// ===========================================================================
// (d) The model-INDEPENDENT datatype-congruence NORMALIZER
//     (`is_datatype_tautology_with`): it must PROVE genuine free-datatype
//     tautologies AND REJECT every near-miss non-tautology (soundness).
// ===========================================================================

/// `Option`-like datatype: `None` (nullary) + `Some(value: Int)`.
fn option_sort() -> Sort {
    Sort::Datatype(DatatypeSort::new(
        "Opt",
        vec![
            DatatypeConstructor::new("None", vec![]),
            DatatypeConstructor::new("Some", vec![DatatypeField::new("value", Sort::Int)]),
        ],
    ))
}

/// Single-constructor datatype `Box = Mk(fst: Int, snd: Int)`.
fn box_sort() -> Sort {
    Sort::Datatype(DatatypeSort::new(
        "Box",
        vec![DatatypeConstructor::new(
            "Mk",
            vec![
                DatatypeField::new("fst", Sort::Int),
                DatatypeField::new("snd", Sort::Int),
            ],
        )],
    ))
}

fn is_taut(ts: &TermStore, t: TermId) -> bool {
    is_datatype_tautology_with(ts, t, &|_| None)
}

include!("tests/datatype_normalization.rs");

// ===========================================================================
// (e) Residual free-datatype-array joint-satisfiability
//     (#free-dt-array-residual): a residue consisting ONLY of alias
//     equalities and ground element reads over FREE datatype-element arrays
//     confirms iff no two constraints force different values at one
//     (class, index, field) slot. Everything else stays fail-closed.
// ===========================================================================

/// Datatype `S = mk(f: Int, g: Int)` and its array sort `(Array Int S)`.
fn struct_sort() -> Sort {
    Sort::Datatype(DatatypeSort::new(
        "S",
        vec![DatatypeConstructor::new(
            "mk",
            vec![
                DatatypeField::new("f", Sort::Int),
                DatatypeField::new("g", Sort::Int),
            ],
        )],
    ))
}

/// `(= <ground-int> (fld (select arr idx)))` — a field read over `arr`.
fn field_read_eq(
    ts: &mut TermStore,
    fld: &str,
    arr: TermId,
    idx: TermId,
    ground: TermId,
) -> TermId {
    let sel = app(ts, "select", &[arr, idx], struct_sort());
    let prj = app(ts, fld, &[sel], Sort::Int);
    app(ts, "=", &[ground, prj], Sort::Bool)
}

include!("tests/datatype_array_residuals.rs");

// --- seq.last_indexof / seq.replace_all value-level parity (#p0.1-seq) ------
//
// These VALUE-level tests pin the independent-gate evaluator's semantics for
// `seq.last_indexof` and `seq.replace_all` against HAND-COMPUTED SMT-LIB
// results. z3 4.15.4 is deliberately NOT used as the oracle here: it does not
// recognise `seq.replace_all` at all ("unknown constant") and it computes
// WRONG `seq.last_indexof` values (its rightmost-of-[5,5] for [5] is neither 0
// nor 1). The gate must therefore be validated against the specification, and
// its implementation is kept independent of the solver's own evaluator
// (crate::seq uses `match_at`; the solver uses inline loops) so a shared bug
// cannot mutually confirm a wrong `sat`.

fn mvseq_i(xs: &[i64]) -> ModelValue {
    ModelValue::Seq(xs.iter().map(|&n| ModelValue::Int(int(n))).collect())
}

fn li(s: &[i64], sub: &[i64]) -> BigInt {
    match seq::eval("seq.last_indexof", &[mvseq_i(s), mvseq_i(sub)]).unwrap() {
        ModelValue::Int(n) => n,
        other => panic!("expected Int, got {other:?}"),
    }
}

fn ra(s: &[i64], src: &[i64], dst: &[i64]) -> Vec<i64> {
    match seq::eval("seq.replace_all", &[mvseq_i(s), mvseq_i(src), mvseq_i(dst)]).unwrap() {
        ModelValue::Seq(v) => v
            .into_iter()
            .map(|e| match e {
                ModelValue::Int(n) => n.try_into().unwrap(),
                other => panic!("expected Int element, got {other:?}"),
            })
            .collect(),
        other => panic!("expected Seq, got {other:?}"),
    }
}

include!("tests/sequence_last_indexof.rs");

// ---------------------------------------------------------------------------
// Higher-order combinators (#ho-seq).
//
// The function operand is a FUNCTION-AS-ARRAY, curried exactly as
// `Z3_mk_seq_map` / `Z3_mk_seq_foldl` build it. Before these, the gate reported
// `unsupported sequence operator seq.map` for EVERY assertion mentioning one,
// so a genuine `sat` over a ground `seq.map` could never be confirmed and
// always degraded to `unknown`. Values are hand-computed from the combinator
// definitions; the fail-closed corners (non-array function operand, an
// unevaluable curried layer) are pinned alongside.

/// An `(Array Int Int)` value from explicit `index -> value` pins.
fn mvarr_i(default: i64, pins: &[(i64, i64)]) -> ModelValue {
    ModelValue::Array(Box::new(ArrayValue {
        default: ModelValue::Int(int(default)),
        store: pins
            .iter()
            .map(|&(k, v)| (ModelValue::Int(int(k)), ModelValue::Int(int(v))))
            .collect(),
    }))
}

/// An `(Array Int (Array Int Int))` value from a default inner array plus pins.
fn mvarr2_i(default_inner: ModelValue, pins: &[(i64, ModelValue)]) -> ModelValue {
    ModelValue::Array(Box::new(ArrayValue {
        default: default_inner,
        store: pins
            .iter()
            .map(|(k, v)| (ModelValue::Int(int(*k)), v.clone()))
            .collect(),
    }))
}

fn int_of(value: &ModelValue) -> BigInt {
    match value {
        ModelValue::Int(n) => n.clone(),
        other => panic!("expected Int, got {other:?}"),
    }
}

fn ints_of(value: &ModelValue) -> Vec<i64> {
    match value {
        ModelValue::Seq(v) => v
            .iter()
            .map(|e| match e {
                ModelValue::Int(n) => n.try_into().unwrap(),
                other => panic!("expected Int element, got {other:?}"),
            })
            .collect(),
        other => panic!("expected Seq, got {other:?}"),
    }
}

include!("tests/sequence_higher_order.rs");

// ===========================================================================
// str.replace_re / str.replace_re_all
//
// SMT-LIB 2.6 Unicode Strings decomposes `s = x ++ w ++ z` with `w` in `[[r]]`,
// `|x|` minimal and THEN `|w|` minimal (leftmost, then shortest).
// `str.replace_re` rewrites that one occurrence; `str.replace_re_all` recurses
// on `z`, under the extra `w != ""` side condition. A regex that accepts the
// empty word is where the two clauses come apart, and this gate deliberately
// fails closed there — see `crate::regex::replace`.
//
// Every case below is fully ground, so the verdict is decided entirely by this
// crate's evaluator and its own interval matcher.
// ===========================================================================

fn re_lit(ts: &mut TermStore, text: &str) -> TermId {
    let s = ts.mk_string(text.to_string());
    app(ts, "str.to_re", &[s], Sort::RegLan)
}

fn re_range(ts: &mut TermStore, lo: &str, hi: &str) -> TermId {
    let lo = ts.mk_string(lo.to_string());
    let hi = ts.mk_string(hi.to_string());
    app(ts, "re.range", &[lo, hi], Sort::RegLan)
}

/// Gate `(= (<op> <subject> <regex> <replacement>) <expected>)`.
fn replace_re_verdict(
    op: &str,
    build_regex: impl FnOnce(&mut TermStore) -> TermId,
    subject: &str,
    replacement: &str,
    expected: &str,
) -> GateVerdict {
    let mut ts = TermStore::new();
    let regex = build_regex(&mut ts);
    let s = ts.mk_string(subject.to_string());
    let t = ts.mk_string(replacement.to_string());
    let call = app(&mut ts, op, &[s, regex, t], Sort::String);
    let want = ts.mk_string(expected.to_string());
    let eq = app(&mut ts, "=", &[call, want], Sort::Bool);
    verdict(&ts, &StubModel::new(), &[eq])
}

// ── the shape the group_strings regression exercised: a union pattern ──

include!("tests/regex_replacement.rs");
