// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// One exact, total UF interpretation constructed by a quantified SAT
/// certificate. Keys and values stay typed so model evaluation never depends
/// on producer-specific SMT-LIB string spellings (`-1` vs `(- 1)`, `1` vs
/// `1.0`, and so on).
#[derive(Debug, Clone)]
pub(super) struct CertifiedTotalUfInterpretation {
    pub(super) arg_sorts: Vec<Sort>,
    pub(super) result_sort: Sort,
    pub(super) rows: Vec<(Vec<EvalValue>, EvalValue)>,
    pub(super) default: EvalValue,
    /// Exact SMT-LIB spellings of `rows`, checked when the interpretation is
    /// installed.  Model output consumes these with [`Self::default`] as an
    /// explicit else branch; it never infers totality from raw EUF row order.
    pub(super) rendered_rows: Vec<(Vec<String>, String)>,
    pub(super) rendered_default: String,
    /// Set only by the quantified model check's completion
    /// (`install_model_check_total_uf`): keys and values may then be any
    /// scalar kind (bit-vector, floating-point, rounding mode) and abstract
    /// elements of a plain uninterpreted sort, all taken from the same staged
    /// model the table is installed into.
    pub(super) element_carriers: bool,
}

/// One ground value owned by the exact certificate model that established it.
///
/// `TermId` is only a reusable slot number. The entry birth stamp prevents a
/// model retained across speculative rollback from applying an old value to a
/// different term later allocated in the same slot.
#[derive(Debug, Clone)]
pub(super) struct StampedCertificatePin {
    pub(super) entry_stamp: TermEntryStamp,
    pub(super) value: EvalValue,
}

/// One immutable constant-function interpretation installed by an exact
/// quantified certificate.
///
/// The checked frontend binding is deliberately stored in the model beside
/// the value.  Evaluation and output therefore cannot accidentally consult a
/// producer-side sidecar belonging to another solve or another model object.
/// `CheckedProjectionBinding` is affine; sharing the package through `Arc`
/// lets a plain model clone preserve semantic data without manufacturing a
/// second copy of the declaration authority.  The clone still drops every SAT
/// publication seal (see `Quantified*ModelSeal::clone`).
#[derive(Debug)]
pub(in crate::executor) struct CertifiedConstInterpEntry {
    pub(super) binding: ay_frontend::CheckedProjectionBinding,
    pub(super) body: CertifiedConstInterpBody,
    /// Exact frontend term for a nullary declaration. Arity>0 heads have no
    /// standalone declaration term and store `None`.
    pub(super) declaration_term: Option<(TermId, TermEntryStamp)>,
}

/// The BODY of one certified interpretation `I(f) = lambda x-bar. body`.
///
/// The certificate's accepting step is the same for every variant — substitute
/// `I` into every assertion and demand an INDEPENDENT solver `Unsat` on the
/// negation — so the variant says only what SHAPE of function was certified,
/// never how much it is trusted.
#[derive(Debug, Clone)]
pub(in crate::executor) enum CertifiedConstInterpBody {
    /// `lambda x-bar. c` for a CLOSED constant `c` (a scalar literal, or a
    /// recursively nested `const-array`). The historical and still by far the
    /// commonest shape.
    Constant {
        value: TermId,
        value_graph: StampedClosedValueGraph,
    },
    /// `lambda x-bar. k + sum_i c_i * x_i` over `Int` parameters with an `Int`
    /// result — the SYMBOLIC default.
    ///
    /// The restriction to a linear body over the DECLARED PARAMETERS is
    /// load-bearing, and it is a restriction on the SHAPE, not on the numbers:
    /// a body may mention no uninterpreted head at all, so two certified
    /// interpretations can never be circular, and an entry carries NO `TermId`
    /// — only arbitrary-precision integers. That is why this variant needs no
    /// stamp-currency treatment: there is no arena slot to go stale.
    LinearInt(LinearIntBody),
}

/// `k + sum_i c_i * x_i` over the declared `Int` parameters of one head.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::executor) struct LinearIntBody {
    coefficients: Box<[BigInt]>,
    constant: BigInt,
}

impl LinearIntBody {
    /// `None` for a nullary head: a 0-ary linear body IS a constant, and it
    /// must travel through [`CertifiedConstInterpBody::Constant`] so that the
    /// nullary declaration-term identity check still applies to it.
    pub(in crate::executor) fn new(coefficients: Vec<BigInt>, constant: BigInt) -> Option<Self> {
        (!coefficients.is_empty()).then(|| Self {
            coefficients: coefficients.into_boxed_slice(),
            constant,
        })
    }

    pub(in crate::executor) fn arity(&self) -> usize {
        self.coefficients.len()
    }

    pub(in crate::executor) fn coefficients(&self) -> &[BigInt] {
        &self.coefficients
    }

    pub(in crate::executor) fn constant(&self) -> &BigInt {
        &self.constant
    }

    /// The body's value at an integer argument point.
    ///
    /// `None` on an arity mismatch — never a fabricated value. This is the
    /// "evaluate the default term AT the argument point" operation both the
    /// ordinary evaluator and the independent gate perform; the arithmetic is
    /// arbitrary precision, so there is no overflow surface.
    pub(in crate::executor) fn evaluate(&self, arguments: &[BigInt]) -> Option<BigInt> {
        if arguments.len() != self.coefficients.len() {
            return None;
        }
        let mut value = self.constant.clone();
        for (coefficient, argument) in self.coefficients.iter().zip(arguments) {
            value += coefficient * argument;
        }
        Some(value)
    }
}

/// Exact live slots of one closed value admitted by a constant-interpretation
/// certificate.
///
/// A `TermId` is a reusable arena slot, so pinning only the root is not enough
/// for a compound value.  Today the admitted compound values are recursively
/// nested `const-array` nodes; retaining every reachable node's birth stamp
/// makes that restriction robust if a speculative term suffix is rolled back
/// and its numeric slots are later reused.
#[derive(Debug, Clone)]
pub(in crate::executor) struct StampedClosedValueGraph {
    pub(super) slots: Box<[(TermId, TermEntryStamp)]>,
}

impl StampedClosedValueGraph {
    pub(super) fn capture(terms: &TermStore, root: TermId, expected_sort: &Sort) -> Option<Self> {
        if terms.entry_stamp(root).is_none() || terms.sort(root) != expected_sort {
            return None;
        }

        let mut seen = HashSet::default();
        let mut stack = vec![root];
        let mut slots = Vec::new();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            let stamp = terms.entry_stamp(term)?;
            let sort = terms.sort(term);
            match terms.get(term) {
                TermData::Const(constant) if scalar_literal_has_exact_sort(constant, sort) => {}
                TermData::App(Symbol::Named(name), arguments)
                    if name == "const-array" && arguments.len() == 1 =>
                {
                    let Sort::Array(array) = sort else {
                        return None;
                    };
                    let child = arguments[0];
                    if terms.entry_stamp(child).is_none()
                        || terms.sort(child) != &array.element_sort
                    {
                        return None;
                    }
                    stack.push(child);
                }
                _ => return None,
            }
            slots.push((term, stamp));
        }

        Some(Self {
            slots: slots.into_boxed_slice(),
        })
    }

    pub(super) fn is_current(&self, terms: &TermStore, root: TermId, expected_sort: &Sort) -> bool {
        terms.entry_stamp(root).is_some()
            && terms.sort(root) == expected_sort
            && self.slots.first().is_some_and(|(term, _)| *term == root)
            && self
                .slots
                .iter()
                .all(|(term, stamp)| terms.entry_stamp(*term) == Some(*stamp))
    }
}

fn scalar_literal_has_exact_sort(constant: &Constant, sort: &Sort) -> bool {
    match (constant, sort) {
        (Constant::Bool(_), Sort::Bool)
        | (Constant::Int(_), Sort::Int)
        | (Constant::Rational(_), Sort::Real)
        | (Constant::String(_), Sort::String) => true,
        (Constant::BitVec { width, .. }, Sort::BitVec(bitvec)) => *width == bitvec.width,
        _ => false,
    }
}

impl CertifiedConstInterpEntry {
    pub(super) fn is_current(&self, ctx: &ay_frontend::Context) -> bool {
        ctx.projection_binding_still_current(&self.binding)
            && match &self.body {
                CertifiedConstInterpBody::Constant { value, value_graph } => {
                    value_graph.is_current(&ctx.terms, *value, self.binding.result_sort())
                }
                // No arena slot to go stale; what CAN drift is the
                // declaration's signature, and the linear body is only
                // meaningful against the exact Int arity it was certified for.
                CertifiedConstInterpBody::LinearInt(linear) => {
                    linear.arity() == self.binding.parameter_sorts().len()
                        && self.binding.result_sort() == &Sort::Int
                        && self
                            .binding
                            .parameter_sorts()
                            .iter()
                            .all(|sort| sort == &Sort::Int)
                }
            }
            && match (
                self.binding.parameter_sorts().is_empty(),
                self.declaration_term,
            ) {
                (false, None) => true,
                (true, Some((term, stamp))) => {
                    ctx.terms.entry_stamp(term) == Some(stamp)
                        && matches!(ctx.terms.get(term), TermData::Var(_, _))
                        && ctx.terms.sort(term) == self.binding.result_sort()
                }
                _ => false,
            }
    }

    pub(in crate::executor) fn symbol(&self) -> &Symbol {
        self.binding.symbol()
    }

    pub(in crate::executor) fn name(&self) -> Option<&str> {
        let Symbol::Named(name) = self.binding.symbol() else {
            return None;
        };
        Some(name)
    }

    pub(in crate::executor) fn parameter_sorts(&self) -> &[Sort] {
        self.binding.parameter_sorts()
    }

    pub(in crate::executor) fn result_sort(&self) -> &Sort {
        self.binding.result_sort()
    }

    pub(in crate::executor) fn body(&self) -> &CertifiedConstInterpBody {
        &self.body
    }

    /// The closed constant this entry publishes, or `None` for a symbolic
    /// body. Never a "best effort" value: a caller that cannot evaluate a
    /// symbolic body at an argument point must fail closed, not substitute a
    /// constant that was never certified.
    #[cfg(test)]
    pub(in crate::executor) fn constant_value(&self) -> Option<TermId> {
        match &self.body {
            CertifiedConstInterpBody::Constant { value, .. } => Some(*value),
            CertifiedConstInterpBody::LinearInt(_) => None,
        }
    }

    /// The exact stamped arena slots this entry retains. A symbolic body
    /// retains none: it carries only integers, so there is nothing for a
    /// reader's preflight to visit or for a slot reuse to invalidate.
    pub(super) fn value_graph_slots(&self) -> &[(TermId, TermEntryStamp)] {
        match &self.body {
            CertifiedConstInterpBody::Constant { value_graph, .. } => &value_graph.slots,
            CertifiedConstInterpBody::LinearInt(_) => &[],
        }
    }

    pub(super) fn declaration_term(&self) -> Option<TermId> {
        self.declaration_term.map(|(term, _)| term)
    }
}

/// Model-owned package for the complete interpretation proved by the
/// constant-interpretation certificate.
#[derive(Debug, Clone, Default)]
pub(super) struct CertifiedConstInterpModel {
    pub(super) entries: Arc<[CertifiedConstInterpEntry]>,
}

/// One canonical interpretation for an ordinary function proved absent from
/// an exact theorem root window.
///
/// This lives outside `EufModel`: merely allocating an empty EUF model changes
/// strict-gate evidence classification (`euf_backed`) even when the completed
/// function is irrelevant to the formula. The checked binding retains stable
/// declaration identity/kind/signature, while the typed value is the exact
/// constant body used by both evaluation and output.
#[derive(Debug)]
pub(in crate::executor) struct FormulaNeutralFunctionDefaultEntry {
    pub(super) binding: ay_frontend::CheckedProjectionBinding,
    pub(super) value: EvalValue,
}

impl FormulaNeutralFunctionDefaultEntry {
    pub(super) fn is_current(&self, ctx: &ay_frontend::Context) -> bool {
        ctx.projection_binding_still_current(&self.binding)
            && !self.binding.parameter_sorts().is_empty()
            && eval_value_has_exact_sort(&self.value, self.binding.result_sort())
    }

    pub(in crate::executor) fn symbol(&self) -> &Symbol {
        self.binding.symbol()
    }

    pub(in crate::executor) fn parameter_sorts(&self) -> &[Sort] {
        self.binding.parameter_sorts()
    }

    pub(in crate::executor) fn result_sort(&self) -> &Sort {
        self.binding.result_sort()
    }

    pub(in crate::executor) fn value(&self) -> &EvalValue {
        &self.value
    }
}

#[derive(Debug, Clone, Default)]
pub(super) struct FormulaNeutralFunctionDefaults {
    pub(super) entries: Arc<[FormulaNeutralFunctionDefaultEntry]>,
}

pub(super) fn eval_value_has_exact_sort(value: &EvalValue, sort: &Sort) -> bool {
    match (value, sort) {
        (EvalValue::Bool(_), Sort::Bool)
        | (EvalValue::Rational(_), Sort::Real)
        | (EvalValue::String(_), Sort::String)
        | (EvalValue::Element(_), Sort::RegLan)
        | (EvalValue::Element(_), Sort::Uninterpreted(_))
        | (EvalValue::Element(_), Sort::Datatype(_)) => true,
        (EvalValue::Rational(value), Sort::Int) => value.is_integer(),
        (EvalValue::Complex { real, imaginary }, Sort::Complex) => {
            eval_value_has_exact_sort(real, &Sort::Real)
                && eval_value_has_exact_sort(imaginary, &Sort::Real)
        }
        (EvalValue::BitVec { width, .. }, Sort::BitVec(sort)) => *width == sort.width,
        (EvalValue::FiniteField { value, field }, Sort::FiniteField(expected)) => {
            field == expected && *value < field.modulus()
        }
        (EvalValue::Fp(value), Sort::FloatingPoint(eb, sb)) => {
            value.eb() == *eb && value.sb() == *sb
        }
        // The completion producer installs only the canonical empty sequence;
        // accepting populated values here would require recursively checking
        // every parametric element sort.
        (EvalValue::Seq(elements), Sort::Seq(_)) => elements.is_empty(),
        _ => false,
    }
}

#[derive(Debug, thiserror::Error)]
pub(in crate::executor) enum FormulaNeutralFunctionDefaultReadError {
    #[error("formula-neutral function default has stale source identity")]
    StaleIdentity,
    #[error("formula-neutral function default application has a conflicting signature")]
    SignatureConflict,
}

/// What a certificate hands to [`Model::install_certified_const_interps`].
///
/// Producer-side only: installation is where a witness becomes an entry, and
/// it is the single place the shape restrictions on a symbolic body are
/// checked (Int result, Int parameters, one coefficient per parameter).
#[derive(Debug, Clone)]
pub(in crate::executor) enum CertifiedConstInterpWitness {
    Constant(TermId),
    LinearInt(LinearIntBody),
}

/// One read of a model-owned certified interpretation AT an application.
///
/// A constant answers with the term it publishes; a symbolic body answers with
/// the body plus the application's argument terms, because the value only
/// exists once those arguments are evaluated. The two are deliberately
/// distinct variants rather than one "value" so no caller can silently treat a
/// symbolic interpretation as if it were constant.
#[derive(Debug, Clone)]
pub(in crate::executor) enum CertifiedConstInterpRead {
    Constant(TermId),
    LinearInt {
        body: LinearIntBody,
        arguments: Vec<TermId>,
    },
}

/// A fail-closed read of a model-owned certified constant interpretation.
#[derive(Debug, thiserror::Error)]
pub(in crate::executor) enum CertifiedConstInterpReadError {
    #[error("certified constant interpretation has stale source or value identity")]
    StaleIdentity,
    #[error("certified constant interpretation application has a conflicting signature")]
    SignatureConflict,
}

/// Result-local model data for certificate-constructed total UF tables.
/// Possession is not SAT authority; only the sealed certificate path installs
/// it after proving the corresponding completed interpretation M'.
#[derive(Debug, Default)]
pub(super) struct CertifiedTotalUfModel {
    pub(super) by_symbol: HashMap<String, CertifiedTotalUfInterpretation>,
    /// Exact ground projection of a certificate-constructed interpretation.
    ///
    /// This deliberately lives in `Model`, not `Executor`: replacing the model
    /// replaces its pins atomically, and evaluating a separately passed model
    /// can never observe another model's certificate sidecar.
    pub(super) ground_pins: HashMap<TermId, StampedCertificatePin>,
    /// Opaque identity of the exact CEGQI UF re-completion carried by this
    /// model. Cloning preserves semantic tables but deliberately drops this
    /// identity; installing any different certified table also revokes it
    /// before changing the interpretation.
    pub(super) cegqi_recompletion_epoch: Option<CegqiUfModelEpoch>,
}

impl Clone for CertifiedTotalUfModel {
    fn clone(&self) -> Self {
        Self {
            by_symbol: self.by_symbol.clone(),
            ground_pins: self.ground_pins.clone(),
            // A clone is a distinct model witness. Preserve semantic tables and
            // pins, but never publication authority for the source object.
            cegqi_recompletion_epoch: None,
        }
    }
}

/// Result-local identity for one exact CEGQI-completed UF model.
///
/// Pointer identity binds the quantified theorem to the model installed at the
/// SAT boundary without making the table contents forgeable or relying on a
/// lossy hash. Only the sealed CEGQI authority combines this identity with
/// source bindings and query roots; possession is not SAT authority by itself.
#[derive(Clone, Debug)]
pub(in crate::executor) struct CegqiUfModelEpoch(Arc<CegqiUfModelEpochMarker>);

#[derive(Debug)]
struct CegqiUfModelEpochMarker;

impl CegqiUfModelEpoch {
    pub(super) fn fresh() -> Self {
        Self(Arc::new(CegqiUfModelEpochMarker))
    }

    pub(super) fn is_same_epoch(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

/// Opaque identity of the exact installed model checked by the mandatory
/// quantified-model gate.
///
/// This identity is deliberately narrower than general model provenance.  A
/// successful quantified check seals the model immediately before the
/// compositional independent gate consumes the paired executor capability.
/// Replacing the model cannot preserve the identity, and explicit revocation
/// invalidates it before any later mutation can reuse the capability.
#[derive(Debug)]
pub(in crate::executor) struct QuantifiedConfirmationModelEpoch(
    Arc<QuantifiedConfirmationModelEpochMarker>,
);

#[derive(Debug)]
struct QuantifiedConfirmationModelEpochMarker;

impl QuantifiedConfirmationModelEpoch {
    pub(super) fn fresh() -> Self {
        Self(Arc::new(QuantifiedConfirmationModelEpochMarker))
    }
}

/// Result-local slot holding the transient quantified-confirmation identity.
///
/// Cloning model data deliberately drops the slot. A clone is a distinct
/// installed witness that can be mutated independently, so it must never
/// inherit authority merely because every copied field initially agrees.
#[derive(Debug, Default)]
pub(super) struct QuantifiedConfirmationModelSeal(
    Option<Arc<QuantifiedConfirmationModelEpochMarker>>,
);

impl Clone for QuantifiedConfirmationModelSeal {
    fn clone(&self) -> Self {
        Self::default()
    }
}

/// Stable identity of a model retained by a quantified certificate grant.
///
/// This is intentionally distinct from [`QuantifiedConfirmationModelEpoch`]:
/// the public quantified-model gate revokes its one-shot direct-confirmation
/// seal on entry, before it consults durable DT/MBQI grants. A grant therefore
/// needs a separate replacement-sensitive identity that survives that cleanup.
#[derive(Debug)]
pub(in crate::executor) struct QuantifiedGrantModelEpoch(Arc<QuantifiedGrantModelEpochMarker>);

#[derive(Debug)]
struct QuantifiedGrantModelEpochMarker;

impl QuantifiedGrantModelEpoch {
    pub(super) fn fresh() -> Self {
        Self(Arc::new(QuantifiedGrantModelEpochMarker))
    }
}

#[derive(Debug, Default)]
pub(super) struct QuantifiedGrantModelSeal(Option<Arc<QuantifiedGrantModelEpochMarker>>);

impl Clone for QuantifiedGrantModelSeal {
    fn clone(&self) -> Self {
        Self::default()
    }
}

impl QuantifiedGrantModelSeal {
    pub(super) fn is_installed(&self) -> bool {
        self.0.is_some()
    }
    pub(super) fn install(&mut self, epoch: &QuantifiedGrantModelEpoch) {
        self.0 = Some(Arc::clone(&epoch.0));
    }

    pub(super) fn carries(&self, epoch: &QuantifiedGrantModelEpoch) -> bool {
        self.0
            .as_ref()
            .is_some_and(|installed| Arc::ptr_eq(installed, &epoch.0))
    }

    pub(super) fn revoke(&mut self) {
        self.0 = None;
    }
}

impl QuantifiedConfirmationModelSeal {
    pub(super) fn is_installed(&self) -> bool {
        self.0.is_some()
    }
    pub(super) fn install(&mut self, epoch: &QuantifiedConfirmationModelEpoch) {
        self.0 = Some(Arc::clone(&epoch.0));
    }

    pub(super) fn revoke(&mut self) {
        self.0 = None;
    }

    pub(super) fn carries(&self, epoch: &QuantifiedConfirmationModelEpoch) -> bool {
        self.0
            .as_ref()
            .is_some_and(|installed| Arc::ptr_eq(installed, &epoch.0))
    }
}
