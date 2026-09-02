// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! # ay-model-check — an independent, fail-closed model-check gate
//!
//! This crate is a **second, independent** SMT-LIB evaluator whose only job is
//! to re-check a `sat` answer: given the assertions and a model, it evaluates
//! every assertion under the model with a fresh, pure, total recursive
//! evaluator and confirms that they all hold. If it cannot *prove* that every
//! assertion is `true` under the model, the verdict is **not** `ConfirmedSat`,
//! so the caller fails closed (downgrades `sat` to `unknown`).
//!
//! ## Soundness contract (the whole point)
//!
//! * It returns [`GateVerdict::ConfirmedSat`] **only** when every assertion
//!   provably evaluates to `Bool(true)` under the model.
//! * Anything the evaluator cannot faithfully compute — an operator it does not
//!   implement, a leaf the model does not pin, a quantifier, an uninterpreted
//!   function application whose value is not determined, an unknown sort, a
//!   recursion-depth overflow — yields [`EvalOutcome::Unevaluable`], which maps
//!   to [`GateVerdict::CannotConfirm`]. It is **never** assumed `true`.
//! * The evaluator is total and panic-free: every partial/ill-typed/under-
//!   specified case without an exact typed proof and a checked model choice
//!   returns `Unevaluable` instead of unwrapping or panicking.
//!
//! Therefore partial coverage is *sound* (it only produces more
//! `CannotConfirm`); a wrong `ConfirmedSat` is catastrophic and is what this
//! gate exists to prevent.
//!
//! ## Independence
//!
//! This crate depends ONLY on [`ay_core`] (the term/sort types) and exact
//! bignum/rational arithmetic. It does NOT depend on the solver, its theory
//! engines, or its model-construction/`evaluate_term` code (which has had
//! bugs). The compositional evaluation here is written from scratch.

use ay_core::{TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::One;

pub mod algebraic;
mod bitvec;
pub mod dt_axiom;
mod eval;
pub mod fp;
pub mod ieee;
mod projection;
mod regex;
mod residual;
mod seq;
pub mod sets;
pub mod strings;
mod unconstrained;

#[cfg(test)]
mod tests;

pub use dt_axiom::{is_datatype_tautology, is_datatype_tautology_with};
pub use eval::Evaluator;
pub use projection::{
    check_projection_implication, check_projection_implication_with_stop,
    CheckedProjectionImplication, CheckedProjectionUf, ProjectionCertificateRejection,
    ProjectionImplicationCandidate, ProjectionUfCandidate,
};
pub use unconstrained::ProvenUnconstrainedKind;

/// Maximum compositional recursion depth before the evaluator fails closed.
///
/// Ground assertions reaching this gate are shallow in practice; this bound
/// exists purely so a pathologically deep term yields `Unevaluable` instead of
/// overflowing the native stack. Hitting it is treated as "cannot confirm",
/// never as a satisfied assertion.
pub const MAX_EVAL_DEPTH: usize = 2000;

// ===========================================================================
// Model values
// ===========================================================================

/// A concrete value in a model, owned by the gate.
///
/// These are the only value shapes the independent evaluator understands. Each
/// is an *exact* representation (bignum integers, exact rationals, width-tagged
/// bitvectors, and concrete IEEE floating-point payloads).  Floating-point
/// values retain their exact sign/exponent/significand fields; the gate never
/// rounds them through a host float.
#[derive(Clone, Debug)]
pub enum ModelValue {
    /// Boolean.
    Bool(bool),
    /// Mathematical integer (arbitrary precision).
    Int(BigInt),
    /// Exact rational (the `Real` sort).
    Real(BigRational),
    /// Bitvector. `value` is always normalized to `0 <= value < 2^width`.
    BitVec {
        /// Bit width.
        width: u32,
        /// Unsigned numeric value in `[0, 2^width)`.
        value: BigInt,
    },
    /// Exact SMT-LIB floating-point value. `significand_bits` includes the
    /// hidden bit, so `significand` contains exactly
    /// `significand_bits - 1` stored fraction bits.  The representation keeps
    /// positive and negative zero distinct, as SMT-LIB structural equality
    /// requires.  NaN and infinity are represented exactly but operations
    /// whose SMT-LIB result is unspecified (notably `fp.to_real`) are admitted
    /// only through the evaluator's typed, input-proven unconstrained-result
    /// path.
    FloatingPoint {
        /// Sign bit (`true` means negative).
        sign: bool,
        /// Biased exponent field.
        exponent: u64,
        /// Stored fraction/significand field (without the hidden bit).
        significand: u64,
        /// Exponent-field width.
        exponent_bits: u32,
        /// Total significand precision, including the hidden bit.
        significand_bits: u32,
    },
    /// String (sequence of Unicode code points).
    Str(String),
    /// An element of an uninterpreted sort, identified by an opaque token.
    /// Equality over these is token identity.
    Uninterpreted(String),
    /// An array value: a default element plus a finite list of `index -> value`
    /// overrides. `select` of an index not in the override list yields the
    /// default. The override list is ordered oldest-first; the **newest** (last)
    /// matching entry wins, so `select(store(a,i,v), i) = v`.
    Array(Box<ArrayValue>),
    /// A sequence value: its elements in order.
    Seq(Vec<ModelValue>),
    /// A real algebraic number that is not rational — e.g. `sqrt(2)`, which
    /// z3 publishes as `(root-obj (+ (^ x 2) (- 2)) 2)`. [`Self::Real`] holds
    /// a `BigRational` and cannot represent one, so without this variant an
    /// irrational witness reaches the gate as an unpinned leaf and the verdict
    /// fails closed. See [`crate::algebraic`] for the exact arithmetic and its
    /// soundness argument.
    Algebraic(Box<algebraic::Algebraic>),
    /// A datatype value: the constructor name and its field values in order.
    Datatype {
        /// Constructor name.
        ctor: String,
        /// Constructor argument values, in field-declaration order.
        args: Vec<ModelValue>,
    },
}

/// The payload of [`ModelValue::Array`]: a default plus finite overrides.
#[derive(Clone, Debug)]
pub struct ArrayValue {
    /// Value at every index not present in `store`.
    pub default: ModelValue,
    /// `index -> value` overrides, oldest first (newest wins on `select`).
    pub store: Vec<(ModelValue, ModelValue)>,
}

impl ModelValue {
    /// Construct a normalized bitvector value.
    #[must_use]
    pub fn bitvec(value: BigInt, width: u32) -> Self {
        Self::BitVec {
            width,
            value: bitvec::normalize(&value, width),
        }
    }

    /// View as a boolean, if it is one.
    #[must_use]
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Bool(b) => Some(*b),
            _ => None,
        }
    }
}

/// Exact structural value equality, with the few well-typed numeric coercions
/// SMT-LIB allows.
///
/// Returns `Ok(true)`/`Ok(false)` only when equality is decided, and
/// `Err(reason)` (i.e. *unevaluable*) when the available value representation
/// lacks enough evidence. That includes genuinely incomparable shapes and the
/// finite-domain array case below; failing closed can never produce a wrong
/// `false` for a real equality.
///
/// Arrays are compared extensionally at every explicit store key. Equal
/// explicit reads plus equal defaults prove equality. Differing defaults remain
/// undecided because `ArrayValue` carries no index-sort/cardinality evidence:
/// over a finite domain the stores may cover every index, making both defaults
/// unreachable.
pub(crate) fn value_eq(a: &ModelValue, b: &ModelValue) -> Result<bool, String> {
    use ModelValue as V;
    match (a, b) {
        (V::Bool(x), V::Bool(y)) => Ok(x == y),
        (V::Int(x), V::Int(y)) => Ok(x == y),
        (V::Real(x), V::Real(y)) => Ok(x == y),
        // Int vs Real: compare as exact rationals (only arises through to_real).
        (V::Int(x), V::Real(y)) => Ok(&BigRational::from(x.clone()) == y),
        (V::Real(x), V::Int(y)) => Ok(x == &BigRational::from(y.clone())),
        (
            V::BitVec {
                width: w1,
                value: v1,
            },
            V::BitVec {
                width: w2,
                value: v2,
            },
        ) => Ok(w1 == w2 && v1 == v2),
        // `=` on floating-point is identity of the DENOTED ELEMENT, which is
        // raw-field identity everywhere except NaN — see `fp::same_element`.
        (V::FloatingPoint { .. }, V::FloatingPoint { .. }) => Ok(fp::same_element(a, b)),
        // Algebraic equality is decided by reduction in one extension. Values
        // in DIFFERENT extensions come back `None` and fall through to the
        // incomparable arm -- deciding those needs resultants, and guessing
        // would let the gate confirm a wrong model.
        (V::Algebraic(x), V::Algebraic(y)) => x
            .equals(y)
            .ok_or_else(|| "algebraic equality across different extensions".to_string()),
        // An algebraic value equals a rational exactly when it reduces to that
        // constant -- `sqrt(2)^2` reduces to `2`, `sqrt(2)` itself to nothing.
        (V::Algebraic(a), V::Real(q)) | (V::Real(q), V::Algebraic(a)) => Ok(a.equals_rational(q)),
        (V::Algebraic(a), V::Int(n)) | (V::Int(n), V::Algebraic(a)) => {
            Ok(a.equals_rational(&BigRational::from(n.clone())))
        }
        (V::Str(x), V::Str(y)) => Ok(x == y),
        (V::Uninterpreted(x), V::Uninterpreted(y)) => Ok(x == y),
        (V::Seq(x), V::Seq(y)) => {
            if x.len() != y.len() {
                return Ok(false);
            }
            for (e, f) in x.iter().zip(y.iter()) {
                if !value_eq(e, f)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (V::Array(x), V::Array(y)) => array_eq(x, y),
        (V::Datatype { ctor: c1, args: a1 }, V::Datatype { ctor: c2, args: a2 }) => {
            if c1 != c2 || a1.len() != a2.len() {
                return Ok(false);
            }
            for (e, f) in a1.iter().zip(a2.iter()) {
                if !value_eq(e, f)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        // Name BOTH shapes. The bare message sent a reader looking for a
        // missing comparison rule, when the real signal is that the model
        // published ONE value in TWO encodings -- e.g. a nullary constructor as
        // both `Datatype { ctor: "v1" }` and `Uninterpreted("v1")`, or a
        // constant array as both an `Array` and its unparsed SMT-LIB text.
        // The fix for that is to normalize the PRODUCER; teaching `value_eq` to
        // equate encodings would loosen the comparison this gate depends on.
        (a, b) => Err(format!(
            "equality between incomparable model values ({} vs {})",
            value_shape(a),
            value_shape(b)
        )),
    }
}

/// `select` an index out of an array value (newest matching override wins,
/// else the default). An index whose comparison is itself unevaluable makes the
/// whole select unevaluable (fail closed).
pub(crate) fn array_select(arr: &ArrayValue, idx: &ModelValue) -> Result<ModelValue, String> {
    for (k, v) in arr.store.iter().rev() {
        if value_eq(k, idx)? {
            return Ok(v.clone());
        }
    }
    Ok(arr.default.clone())
}

/// Extensional equality of two array values over the `(default, finite-store)`
/// representation.
///
/// A differing read at an explicit store key proves the arrays unequal. Equal
/// explicit reads plus equal defaults prove them equal. Differing defaults do
/// *not* by themselves prove inequality: over a finite index sort (notably
/// `Bool` and bit-vectors), the explicit stores may cover the whole domain, in
/// which case the defaults are unreachable. [`ArrayValue`] deliberately carries
/// no index-sort/cardinality evidence, so that last case must fail closed.
fn array_eq(a: &ArrayValue, b: &ArrayValue) -> Result<bool, String> {
    for (k, _) in a.store.iter().chain(b.store.iter()) {
        let va = array_select(a, k)?;
        let vb = array_select(b, k)?;
        if !value_eq(&va, &vb)? {
            return Ok(false);
        }
    }
    if value_eq(&a.default, &b.default)? {
        Ok(true)
    } else {
        Err(
            "array equality with differing defaults needs index-domain coverage evidence"
                .to_string(),
        )
    }
}

// Re-export of a tiny helper used across modules.
pub(crate) fn pow2(width: u32) -> BigInt {
    BigInt::one() << (width as usize)
}

// ===========================================================================
// The model view the gate reads
// ===========================================================================

/// Read-only access to a model, as seen by the gate.
///
/// The gate does **all** compositional evaluation itself; it only asks the model
/// for the values of *leaves* — declared constants/variables (and array/seq
/// variables, etc.). [`leaf_value`](ModelView::leaf_value) returns the model's
/// committed value for such a leaf, or `None` if the model does not pin it (in
/// which case the gate fails closed for any assertion that needs it).
///
/// Crucially, an implementor should **only** answer for genuine leaves. It must
/// not, for example, fabricate per-application values for uninterpreted function
/// applications: returning unrelated values for `(f a)` and `(f b)` while
/// `a = b` would let the gate confirm an internally-inconsistent model. The gate
/// returns `Unevaluable` for any function application it does not interpret,
/// which is the sound behaviour.
pub trait ModelView {
    /// The model's value for a leaf term, or `None` if unpinned.
    fn leaf_value(&self, t: TermId) -> Option<ModelValue>;

    /// The selected argument index when application `t` has an independently
    /// checked exact projection interpretation.
    ///
    /// The evaluator validates that `t` is an application, the index is in
    /// bounds, and the selected argument's sort is exactly the application's
    /// result sort. It then evaluates that argument in the *current* evaluator
    /// frame. This preserves the value-keyed UF graph, memo, recursion budget,
    /// and active lambda bindings; an implementation must not evaluate or pin
    /// the application itself. Returning `Ok(None)` means no exact projection
    /// is available. `Err` means model state claims a projection for the
    /// application's symbol but cannot apply it coherently (for example, its
    /// signature differs); the evaluator fails closed instead of consulting a
    /// lower-priority per-application UF value. The default keeps existing
    /// model views fail-closed.
    fn projection_argument(&self, _t: TermId) -> Result<Option<usize>, ProjectionLookupError> {
        Ok(None)
    }

    /// Resolve a datatype declared under a bare `Sort::Uninterpreted(name)`.
    ///
    /// Some front-ends abstract algebraic datatypes to uninterpreted sorts
    /// (their constructor/selector/tester applications then carry
    /// `Sort::Uninterpreted(name)` rather than `Sort::Datatype`). Returning the
    /// datatype definition here lets the evaluator interpret those applications
    /// (constructors, selectors, testers) faithfully — the SAME congruence-free
    /// projection it does for `Sort::Datatype`, so it can both CONFIRM a valid
    /// datatype-carrying model and REFUTE a constructor-injectivity violation.
    ///
    /// Default: `None` — no registry, so datatype ops over uninterpreted sorts
    /// stay unevaluable (fail-closed). Overriding NEVER weakens soundness: the
    /// evaluator still only projects a selector out of a value built by a KNOWN
    /// constructor, and re-checks every assertion.
    fn datatype_def(&self, _name: &str) -> Option<ay_core::DatatypeSort> {
        None
    }

    /// The model's committed value for the uninterpreted-function application
    /// term `t`, or `None` if the model does not pin it.
    ///
    /// Unlike [`leaf_value`](ModelView::leaf_value), this may be asked for a
    /// whole application `(f a b ...)`. It returns the value the model
    /// *committed* to for that specific application. The gate does NOT use it as
    /// a naive per-application lookup (which, as noted above, could confirm an
    /// internally-inconsistent model): it keys applications by their evaluated
    /// argument VALUES and takes the first committed value seen for each key as
    /// the single value of the function there. Two applications the model pins
    /// to different values while their arguments evaluate equal therefore
    /// resolve to the SAME gate value — exposing (not hiding) the inconsistency,
    /// which is what catches the collapse-to-degenerate-argument wrong models.
    ///
    /// The default implementation returns `None` (an implementor that does not
    /// model uninterpreted functions keeps the sound fail-closed behaviour: any
    /// assertion needing a UF value becomes `CannotConfirm`).
    fn uf_app_value(&self, _t: TermId) -> Option<ModelValue> {
        None
    }

    /// The value an asserted definition fixes for a non-finite `fp.to_real`
    /// application `t`.
    ///
    /// This is the original public hook retained for source compatibility.
    /// New implementations that need to distinguish all independently proven
    /// unconstrained cases should implement
    /// [`proven_unconstrained_app_value`](Self::proven_unconstrained_app_value)
    /// instead. The default typed hook delegates here ONLY for
    /// [`ProvenUnconstrainedKind::FpToRealNonFinite`], preserving this method's
    /// historical meaning without granting legacy implementations authority
    /// over division by zero.
    ///
    /// WHY THIS IS SOUND. An implementor may answer this from the assertion
    /// itself, which [`uf_app_value`](Self::uf_app_value) must never do for a
    /// theory head. The evaluator calls this method only through the typed hook
    /// after independently proving that the operand is NaN or infinity.
    ///
    /// Default: `None` — fail closed, exactly as before.
    fn unconstrained_app_value(&self, _t: TermId) -> Option<ModelValue> {
        None
    }

    /// The value an asserted definition fixes for the application `t`, asked
    /// ONLY after the evaluator proves the typed unconstrained-input condition.
    ///
    /// The admitted cases are enumerated by [`ProvenUnconstrainedKind`]:
    /// non-finite `fp.to_real`, Real division by zero, and integer `div`/`mod`
    /// by zero. In each case the theory permits every value of the result sort.
    /// A solver may therefore have no ordinary per-application commitment even
    /// though an asserted definition selects a legal value.
    ///
    /// WHY THIS IS A SEPARATE METHOD, AND WHY IT IS SOUND.  An implementor may
    /// answer this from the ASSERTION ITSELF, which `uf_app_value` must never
    /// do for a theory head: for an operation the gate computes, "no value"
    /// means the gate's own evaluator failed, and adopting the assertion's
    /// claim would turn that evaluator bug into a confirmed wrong `sat`. The
    /// caller therefore reaches this method only after its evaluator has
    /// POSITIVELY established the condition represented by `kind` from exact,
    /// independently evaluated operands — never from an evaluation failure.
    /// Adoption then cannot admit a forbidden model, because choosing the
    /// interpretation that satisfies the definition is itself legal, every
    /// other assertion is still checked against that choice, and the gate's
    /// value-keyed `uf_graph` still forces equal argument values to one result.
    /// A committed [`uf_app_value`](ModelView::uf_app_value) always takes
    /// precedence; this fallback is consulted only when that lookup returns
    /// `None`.
    ///
    /// By default, the pre-existing non-finite-`fp.to_real` hook remains
    /// effective. Division-by-zero kinds deliberately do not delegate to it:
    /// an implementation written before those cases existed never opted into
    /// supplying their values.
    fn proven_unconstrained_app_value(
        &self,
        t: TermId,
        kind: ProvenUnconstrainedKind,
    ) -> Option<ModelValue> {
        if kind == ProvenUnconstrainedKind::FpToRealNonFinite {
            self.unconstrained_app_value(t)
        } else {
            None
        }
    }

    /// The model's value for the uninterpreted-function application `t` whose
    /// arguments the evaluator has ALREADY reduced to `arg_values`.
    ///
    /// Identical contract to [`uf_app_value`](ModelView::uf_app_value) — the
    /// value is still keyed into the evaluator's `uf_graph` by those argument
    /// values, so single-valuedness is enforced exactly as before. The extra
    /// parameter exists because a model can be TOTAL on a function without
    /// pinning the individual application term: an implementor whose emitted
    /// model serialises `f` as a complete table-plus-default interpretation can
    /// read that interpretation AT this argument point, which a TermId-only
    /// lookup cannot express.
    ///
    /// The default implementation ignores `arg_values` and delegates, so every
    /// existing implementor keeps its current behaviour verbatim.
    fn uf_app_value_at(&self, t: TermId, arg_values: &[ModelValue]) -> Option<ModelValue> {
        let _ = arg_values;
        self.uf_app_value(t)
    }

    /// The model's committed value for the array-`select` application term `t`
    /// (`(select A i)`), or `None` if the model does not pin it.
    ///
    /// This is the array analogue of [`uf_app_value`](ModelView::uf_app_value)
    /// and exists for the SAME reason: the gate evaluates `select` structurally
    /// whenever it can resolve `A` to a concrete `(default, finite-store)`
    /// interpretation (definitional equality or the reconstructed array model),
    /// but when that resolution FAILS — a partial/unreconstructable array leaf —
    /// the whole `select` would be `Unevaluable` and the gate would fail closed
    /// (`CannotConfirm`), letting an internally-inconsistent array model ship as
    /// `sat`. This accessor lets the gate read the model's committed value for
    /// that specific read instead.
    ///
    /// As with `uf_app_value`, the gate does NOT trust these per-application pins
    /// naively: `select` over an array is a single-valued function of the index,
    /// so two reads of the SAME array term at index values that evaluate EQUAL
    /// must denote the same element (McCarthy functionality). The gate keys reads
    /// by `(array-term, index-value)` and takes the first committed value per key
    /// as the single element there. Two reads the model pins to different values
    /// while their (array, index) coincide therefore resolve to the SAME gate
    /// value — exposing (not hiding) the inconsistency — and, because the gate
    /// evaluates the indices itself, a degenerate array whose reads contradict an
    /// asserted (in)equality evaluates the enclosing assertion to `false`
    /// (`ModelViolates`).
    ///
    /// The default implementation returns `None` (sound fail-closed: an
    /// unresolvable `select` stays `CannotConfirm`).
    fn array_select_value(&self, _t: TermId) -> Option<ModelValue> {
        None
    }
}

/// A model view claimed a symbolic projection but could not read it
/// coherently.
///
/// This is deliberately distinct from `Ok(None)`: absence permits ordinary UF
/// evaluation, while an inconsistent projection must stop evaluation before a
/// finite table or per-application pin can shadow the symbolic interpretation.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProjectionLookupError {
    /// The installed projection interpretation conflicts with the application
    /// being evaluated.
    InconsistentModel {
        /// Stable human-readable detail for fail-closed diagnostics.
        detail: String,
    },
}

impl ProjectionLookupError {
    /// Construct an inconsistent-model lookup error.
    #[must_use]
    pub fn inconsistent_model(detail: impl Into<String>) -> Self {
        Self::InconsistentModel {
            detail: detail.into(),
        }
    }
}

impl std::fmt::Display for ProjectionLookupError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InconsistentModel { detail } => {
                write!(f, "inconsistent symbolic projection model: {detail}")
            }
        }
    }
}

impl std::error::Error for ProjectionLookupError {}

// ===========================================================================
// Evaluation outcome and gate verdict
// ===========================================================================

/// The result of evaluating a single (sub)term under the model.
#[derive(Clone, Debug)]
pub enum EvalOutcome {
    /// A fully-computed value.
    Value(ModelValue),
    /// The evaluator could not faithfully compute a value (unimplemented
    /// operator, unpinned leaf, quantifier, under-specified result, etc.).
    /// The string is a human-readable reason for diagnostics.
    Unevaluable(String),
}

/// The verdict of the independent model-check gate over all assertions.
#[derive(Clone, Debug)]
pub enum GateVerdict {
    /// Every assertion provably evaluates to `true` under the model.
    ConfirmedSat,
    /// Some assertion provably evaluates to `false` under the model: a *caught*
    /// wrong-`sat`. `assertion` is the offending top-level assertion term.
    ModelViolates {
        /// The assertion that the model falsifies.
        assertion: TermId,
    },
    /// The gate could not confirm the model (some assertion was unevaluable or
    /// did not reduce to a boolean). Fail closed: the caller downgrades to
    /// `unknown`.
    CannotConfirm {
        /// Diagnostic reason.
        reason: String,
    },
}

/// Evaluate a single term under the model with a fresh evaluator.
///
/// Exposed primarily for tests; [`confirm_model`] is the gate entry point.
#[must_use]
pub fn evaluate_term(terms: &TermStore, model: &dyn ModelView, term: TermId) -> EvalOutcome {
    Evaluator::new(terms, model).evaluate(term)
}

/// The independent, fail-closed model-check gate.
///
/// Re-checks `assertions` against `model` with a fresh recursive evaluator:
///
/// * if **every** assertion evaluates to `Value(Bool(true))` ⇒ [`GateVerdict::ConfirmedSat`];
/// * if **any** assertion evaluates to `Value(Bool(false))` ⇒
///   [`GateVerdict::ModelViolates`] (a caught wrong-`sat`);
/// * otherwise (any assertion unevaluable, or a non-boolean top value) ⇒
///   [`GateVerdict::CannotConfirm`].
///
/// The check is conservative: it confirms only what it can fully and faithfully
/// compute under the model.
#[must_use]
pub fn confirm_model(
    terms: &TermStore,
    model: &dyn ModelView,
    assertions: &[TermId],
) -> GateVerdict {
    confirm_model_with_policy(
        terms,
        model,
        assertions,
        ResidualPolicy::MaterializeAndReplay,
    )
}

/// Re-run the ordinary confirmation scan against a model whose formerly-free
/// leaves have been completed by the residual witness builder.
///
/// This is deliberately the same fresh-evaluator path as [`confirm_model`],
/// except that residual admission is disabled.  A completed witness therefore
/// earns `ConfirmedSat` only by making every assertion evaluate to `true`; it
/// cannot recursively justify a remaining coverage gap with another abstract
/// extension argument.
pub(crate) fn confirm_completed_model(
    terms: &TermStore,
    model: &dyn ModelView,
    assertions: &[TermId],
) -> GateVerdict {
    confirm_model_with_policy(terms, model, assertions, ResidualPolicy::ReplayOnly)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ResidualPolicy {
    MaterializeAndReplay,
    ReplayOnly,
}

fn confirm_model_with_policy(
    terms: &TermStore,
    model: &dyn ModelView,
    assertions: &[TermId],
    residual_policy: ResidualPolicy,
) -> GateVerdict {
    let evaluator = Evaluator::new(terms, model);
    // Registry-aware datatype resolver: maps a `Sort::Uninterpreted(name)` that
    // abstracts a declared datatype back to its definition, so the
    // model-independent tautology guard applies to UF-abstracted datatypes too
    // (the eager DtAufbv lowering). Derived from the front-end declaration
    // tables via `ModelView::datatype_def`, so it is model-independent.
    let resolve = |name: &str| model.datatype_def(name);
    // A concrete `false` on ANY assertion outranks a coverage gap on an
    // earlier one: scan ALL assertions before returning `CannotConfirm`.
    // Previously this returned at the FIRST `Unevaluable`, so a ground
    // refutation hiding behind an earlier unevaluable assertion was reported
    // as a mere coverage gap — which the enforcement layer fails OPEN on
    // (QF_AUFLIA seed-77 case 195: assertion `(< (fa x) (fa n))` evaluated
    // `false` under `x = n = -3`, but an earlier array-select assertion was
    // unevaluable, so the wrong model shipped as `sat`). The first gap's
    // reason is preserved for telemetry.
    let mut first_gap: Option<String> = None;
    // The unevaluable (non-tautology) assertions, kept for the residual
    // free-datatype-array joint-satisfiability decision below
    // (#free-dt-array-residual); `non_residual_gap` records a coverage gap of
    // any OTHER kind (a non-boolean top value), which that decision must not
    // paper over.
    let mut residue: Vec<TermId> = Vec::new();
    let mut non_residual_gap = false;
    for &assertion in assertions {
        match evaluator.evaluate(assertion) {
            EvalOutcome::Value(ModelValue::Bool(true)) => {}
            EvalOutcome::Value(ModelValue::Bool(false)) => {
                // The model evaluator computed `false`, but for ay's OWN injected
                // DATATYPE-CONGRUENCE / tester / selector axioms it cannot
                // canonicalize the datatype-carrying-array operands and so
                // over-computes a TAUTOLOGY to `false`. Before rejecting, prove
                // the assertion from the FREE datatype + Boolean theory alone
                // (model-independent). A `true` there means the assertion holds
                // in EVERY model — the evaluator's `false` was a datatype-model
                // decoupling artifact — so it is NOT a violation. A genuine
                // violation is NOT a tautology, so this never suppresses one and
                // no wrong `Sat` can be confirmed. Mirrors ay-dpll's strict-oracle
                // dt_axiom_bool guard (#g4-dt-consistency).
                if is_datatype_tautology_with(terms, assertion, &resolve) {
                    continue;
                }
                return GateVerdict::ModelViolates { assertion };
            }
            EvalOutcome::Value(_) => {
                non_residual_gap = true;
                first_gap
                    .get_or_insert_with(|| "assertion did not evaluate to a boolean".to_string());
            }
            EvalOutcome::Unevaluable(reason) => {
                // The model evaluator could not ground-evaluate this assertion
                // (e.g. an unpinned scalar leaf inside a datatype
                // selector-over-constructor round-trip, or a datatype-carrying
                // array read it cannot canonicalize). Before failing closed,
                // prove the assertion from the FREE datatype + Boolean theory
                // alone (model-INDEPENDENT). A `Some(true)` there means the
                // assertion holds in EVERY model, so it holds in OURS — this is
                // the SAME sound tautology guard the `Bool(false)` arm uses,
                // just applied to a coverage gap instead of an over-computed
                // `false`. It can only CONFIRM (never refute), so no wrong `Sat`
                // is possible: a genuine violation is not a tautology
                // (`dt_axiom_bool` returns `Some(false)`/`None`, not
                // `Some(true)`), so it is never suppressed (#g4-dt-taut-uneval).
                if is_datatype_tautology_with(terms, assertion, &resolve) {
                    continue;
                }
                residue.push(assertion);
                first_gap.get_or_insert(reason);
            }
        }
    }
    let Some(reason) = first_gap else {
        return GateVerdict::ConfirmedSat;
    };
    // Residual free-datatype-array joint-satisfiability
    // (#free-dt-array-residual): when the ONLY residue consists of alias
    // equalities and ground element reads over genuinely FREE datatype-element
    // array variables, and those constraints are jointly satisfiable (no two
    // force different values at one (class, index, field) slot), the confirmed
    // partial model provably extends to a full model — every other assertion
    // ground-confirmed above using no value of the free arrays (proved by the
    // pin probes inside the decision). This maps Sat -> {Sat, Unknown} only:
    // any residue beyond that fragment, any pinned read over the class, or
    // any conflict keeps the fail-closed verdict below.
    if residual_policy == ResidualPolicy::MaterializeAndReplay
        && !non_residual_gap
        && residual::free_dt_array_residue_extends(
            terms, model, &evaluator, assertions, &residue, &resolve,
        )
    {
        return GateVerdict::ConfirmedSat;
    }
    GateVerdict::CannotConfirm { reason }
}

/// The shape name of a model value, for diagnostics only.
fn value_shape(value: &ModelValue) -> &'static str {
    match value {
        ModelValue::Bool(_) => "Bool",
        ModelValue::Int(_) => "Int",
        ModelValue::Real(_) => "Real",
        ModelValue::BitVec { .. } => "BitVec",
        ModelValue::FloatingPoint { .. } => "FloatingPoint",
        ModelValue::Str(_) => "Str",
        ModelValue::Uninterpreted(_) => "Uninterpreted",
        ModelValue::Seq(_) => "Seq",
        ModelValue::Array(_) => "Array",
        ModelValue::Algebraic(_) => "Algebraic",
        ModelValue::Datatype { .. } => "Datatype",
    }
}
