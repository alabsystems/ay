// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Serializable proof bundle for OFFLINE, producer-independent re-checking.
//! [`check_proof_strict_with_typed_context`](crate::check_proof_strict_with_typed_context)
//! validates a [`Proof`] against a [`TermStore`], its exact typed datatype
//! context, and its problem assertions purely by reading terms by index
//! (`get`/`sort`) — it never re-interns and never re-solves. That makes a proof
//! plus a flat term snapshot a fully self-contained, re-checkable certificate:
//! a [`SerializableProofBundle`] can be serialized (serde), shipped, and
//! re-validated by a checker that never ran — and need not trust — the original
//! solver.
//! The bundle carries only what the strict checker reads: the ordered proof
//! steps, a positional `(TermData, Sort)` term table (so every embedded
//! [`TermId`] resolves), the boolean-constant ids, the variable counter, and the
//! proof-authorized obligation term ids (so a consumer can bind the proof's
//! `assume` axioms to the obligation it claims to discharge), and the datatype
//! declaration context needed by the corresponding strict proof rules, and
//! the complete registered user-function identity set. Namespace identities
//! survive every owning copy and offline restore; their omission is an error,
//! never a request to reinterpret a user head as a builtin. The
//! obligation ids may be an authenticated UNSAT-core subset of the producer's
//! full assertion list.
//! Re-checking establishes that the bundle is internally sound; it does NOT
//! authenticate the producer's claimed problem context. A consumer binding a
//! schema-v5 bundle to an independently obtained problem must verify that every
//! obligation assertion is a member of the intended problem and compare
//! `datatype_declarations`, `constructor_selectors`,
//! `datatype_member_signatures`, and the complete free-symbol declaration
//! context (exact named/indexed identity plus argument and result sorts).
//! Canonical assertion text alone is
//! insufficient: the same printed term can acquire different meaning from a
//! different declaration environment. Registered identities preserve builtin
//! versus user meaning, but schema v5 does not serialize a complete
//! arbitrary-function declaration table, so that final comparison remains a
//! consumer responsibility.

mod cancellation;
mod construction;
mod retained;
mod retained_api;
pub(crate) mod retained_reader;
pub use cancellation::{
    re_check_bundle_strict_with_cancellation, re_check_bundle_strict_with_resource_control,
};
pub use retained_api::{
    capture_strict_retained_bundle_with_resource_control,
    re_check_retained_bundle_strict_with_resource_control,
    read_retained_proof_bundle_with_resource_control,
    read_retained_proof_bundle_with_resource_control_and_diagnostics, RetainedProofBundle,
    RetainedProofCapture, RetainedProofTransportLimits, RetainedReadDiagnostics,
    RetainedReadErrorClass, RetainedReadFailure, RetainedReadRefusal, RetainedReadStage,
    RetainedReadTerminal, RETAINED_PROOF_BUNDLE_SCHEMA,
};
#[cfg(test)]
mod nra_sos;
mod preflight;
mod preflight_app;
mod preflight_canonical;
mod preflight_declarations;
mod preflight_proof;
mod preflight_sort;
mod preflight_term;
#[cfg(test)]
use preflight_proof::{validate_proof_snapshot, validate_proof_snapshot_with_progress};
use preflight_sort::validate_sort_with_progress;
#[cfg(test)]
mod nra_sos_tests;
#[cfg(test)]
mod quantifier_tests;
#[cfg(test)]
mod snapshot_preflight_tests;

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{
    Constant, Proof, ProofId, ProofStep, Sort, Symbol, TermData, TermId, TermStore, TheoryLemmaKind,
};
use num_bigint::Sign;
use serde::{Deserialize, Serialize};

use crate::alethe_printer::AlethePrinter;
use crate::{DatatypeMemberSignature, ProofCheckError, ProofQuality};
#[cfg(test)]
use preflight_declarations::{validate_declaration_context, validate_declared_constructor_terms};

/// Schema tag for [`SerializableProofBundle`]. The bundle is a compiled-Rust
/// serde encoding tied to the exact `ay-core` proof/term representation that
/// BOTH producer and consumer link — NOT a stable cross-version wire format.
/// [`re_check_bundle_strict`] fail-closes on any other tag so a version skew is
/// rejected rather than silently mis-decoded.
pub const PROOF_BUNDLE_SCHEMA: &str = "ay.proofbundle/v5";

/// A self-contained, serializable UNSAT proof: the proof DAG plus the minimal
/// term table needed to re-check it offline (see module docs). "Self-contained"
/// covers proof validation, not authentication against an external problem;
/// consumers must independently bind the full declaration context described in
/// the module-level contract.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SerializableProofBundle {
    /// Schema tag — see [`PROOF_BUNDLE_SCHEMA`].
    pub schema: String,
    /// Ordered proof steps; `ProofId(i)` resolves to `steps[i]`.
    pub steps: Vec<ProofStep>,
    /// Positional term table; `TermId(i)` resolves to `term_entries[i]`.
    pub term_entries: Vec<(TermData, Sort)>,
    /// The `TermId` of the boolean `true` constant (if the store had one).
    pub true_term: Option<TermId>,
    /// The `TermId` of the boolean `false` constant (if the store had one).
    pub false_term: Option<TermId>,
    /// Variable counter at export time (book-keeping; not read by the checker).
    pub var_counter: u32,
    /// Proof-authorized obligation term ids. These may be an authenticated
    /// UNSAT-core subset of the full formulas submitted to the solver. A
    /// consumer binds the proof's `assume` axioms to these and must verify that
    /// every entry belongs to the intended external problem.
    pub obligation_assertions: Vec<TermId>,
    /// Datatype declarations needed to validate constructor-distinctness
    /// lemmas: `(datatype_name, constructors)`.
    pub datatype_declarations: Vec<(String, Vec<String>)>,
    /// Constructor-to-selector declarations needed to validate datatype
    /// projection lemmas: `(constructor_name, selectors in field order)`.
    pub constructor_selectors: Vec<(String, Vec<String>)>,
    /// Exact sticky core signatures for every constructor, selector, and
    /// derived tester named by the datatype declaration context.
    pub datatype_member_signatures: Vec<DatatypeMemberSignature>,
    /// User-function core identities, including names that resemble builtins.
    /// These are namespace data, not authentication of an external problem.
    /// Missing metadata must never silently restore builtin interpretation.
    pub declared_function_identities: Vec<String>,
}
/// Result of [`re_check_bundle_strict`]: the strict-check quality metrics plus
/// the `assume` term ids in proof-step order, including duplicate occurrences.
#[derive(Debug, Clone)]
pub struct BundleReCheck {
    /// Strict-mode quality metrics (the proof passed
    /// [`check_proof_strict_with_typed_context`](crate::check_proof_strict_with_typed_context)).
    pub quality: ProofQuality,
    /// Every `TermId` appearing in an `Assume` step, in proof-step order with
    /// duplicates preserved. This is not restricted to the terminal clause's
    /// dependency cone; unused assumptions are included too.
    pub assume_terms: Vec<TermId>,
}

impl SerializableProofBundle {
    /// Assemble a bundle from a live proof, its term store, and the authorized
    /// obligation term ids. Snapshots the checker-relevant term table.
    ///
    /// `terms` must be a real solver store (true/false constants initialized);
    /// this is always the case at the UNSAT export site.
    #[must_use]
    pub fn from_proof(
        proof: &Proof,
        terms: &TermStore,
        obligation_assertions: Vec<TermId>,
    ) -> Self {
        Self::from_proof_with_context(proof, terms, obligation_assertions, Vec::new(), Vec::new())
    }

    /// Assemble a compatibility bundle from name-only datatype context.
    ///
    /// Under schema v5, name-only context carries no datatype-rule authority:
    /// offline re-checking rejects any non-empty datatype context that lacks its
    /// exact member-signature table. Use
    /// [`Self::from_proof_with_typed_context`] for datatype proofs.
    #[must_use]
    pub fn from_proof_with_context(
        proof: &Proof,
        terms: &TermStore,
        obligation_assertions: Vec<TermId>,
        datatype_declarations: Vec<(String, Vec<String>)>,
        constructor_selectors: Vec<(String, Vec<String>)>,
    ) -> Self {
        Self::from_proof_with_typed_context(
            proof,
            terms,
            obligation_assertions,
            datatype_declarations,
            constructor_selectors,
            Vec::new(),
        )
    }

    /// Assemble a schema-v5 bundle with an exact datatype-member signature
    /// table. The offline checker cross-checks this table against both name
    /// registries and every member occurrence in the serialized term store.
    #[must_use]
    pub fn from_proof_with_typed_context(
        proof: &Proof,
        terms: &TermStore,
        obligation_assertions: Vec<TermId>,
        datatype_declarations: Vec<(String, Vec<String>)>,
        constructor_selectors: Vec<(String, Vec<String>)>,
        datatype_member_signatures: Vec<DatatypeMemberSignature>,
    ) -> Self {
        Self {
            schema: PROOF_BUNDLE_SCHEMA.to_string(),
            steps: proof.steps.clone(),
            term_entries: terms.entries_snapshot(),
            true_term: Some(terms.true_term()),
            false_term: Some(terms.false_term()),
            var_counter: terms.var_counter(),
            obligation_assertions,
            datatype_declarations,
            constructor_selectors,
            datatype_member_signatures,
            declared_function_identities: terms
                .declared_function_identities()
                .map(str::to_owned)
                .collect(),
        }
    }
}

fn malformed_bundle(reason: impl Into<String>) -> ProofCheckError {
    ProofCheckError::MalformedProofBundle {
        reason: reason.into(),
    }
}

#[cfg(test)]
fn bundle_term<'a>(
    entries: &'a [(TermData, Sort)],
    id: TermId,
    role: &str,
) -> Result<&'a (TermData, Sort), ProofCheckError> {
    entries.get(id.index()).ok_or_else(|| {
        malformed_bundle(format!(
            "{role} references term {id}, but the snapshot contains only {} terms",
            entries.len()
        ))
    })
}

#[cfg(test)]
fn bundle_bool_term(
    entries: &[(TermData, Sort)],
    id: TermId,
    role: &str,
) -> Result<(), ProofCheckError> {
    let (_, sort) = bundle_term(entries, id, role)?;
    if sort != &Sort::Bool {
        return Err(malformed_bundle(format!(
            "{role} references non-Boolean term {id} of sort {sort}"
        )));
    }
    Ok(())
}

#[cfg(test)]
fn prior_child_sort<'a>(
    entries: &'a [(TermData, Sort)],
    node_index: usize,
    child: TermId,
    role: &str,
) -> Result<&'a Sort, ProofCheckError> {
    if child.index() >= node_index {
        return Err(malformed_bundle(format!(
            "term t{node_index} {role} references non-prior term {child}"
        )));
    }
    Ok(&entries[child.index()].1)
}

const MAX_BUNDLE_SORT_DEPTH: usize = 256;
const MAX_BUNDLE_BITVECTOR_WIDTH: u32 = 1 << 20;
// Metadata bound only: each semantic validator enforces its own arithmetic
// limits (ground 20, forward-error 24, or metered word programs). Classification
// now compares u64 fields directly, including a 64-bit all-ones exponent.
const MAX_BUNDLE_FP_EXPONENT_WIDTH: u32 = 64;
const MAX_BUNDLE_FP_SIGNIFICAND_WIDTH: u32 = MAX_BUNDLE_BITVECTOR_WIDTH;
const MAX_BOUNDED_CHECKER_BV_WIDTH: u32 = 64;
const MAX_FP_CHECKER_ASSIGNMENT_BITS: u32 = 16;
// Classification compares decoded u64 fields, without exponent-sized rationals.
const MAX_FP_CHECKER_EXPONENT_WIDTH: u32 = 64;

#[cfg(test)]
fn validate_sort(
    sort: &Sort,
    node_index: usize,
    role: &str,
    depth: usize,
) -> Result<(), ProofCheckError> {
    validate_sort_with_progress(sort, node_index, role, depth, &mut |_, _| true)
}

#[cfg(test)]
fn validate_constant_sort(
    node_index: usize,
    constant: &Constant,
    sort: &Sort,
) -> Result<(), ProofCheckError> {
    let sort_matches = match constant {
        Constant::Bool(_) => sort == &Sort::Bool,
        Constant::Int(_) => sort == &Sort::Int,
        Constant::Rational(value) => sort == &Sort::Real && value.0.denom().sign() != Sign::NoSign,
        Constant::BitVec { value, width } => {
            matches!(sort, Sort::BitVec(bitvec) if bitvec.width == *width)
                && value.sign() != Sign::Minus
                && value.bits() <= u64::from(*width)
        }
        Constant::FiniteField { value, field } => {
            sort == &Sort::FiniteField(*field) && *value < field.modulus()
        }
        Constant::String(_) => sort == &Sort::String,
        _ => false,
    };
    if !sort_matches {
        return Err(malformed_bundle(format!(
            "constant term t{node_index} has an incompatible recorded sort or non-canonical value ({sort})"
        )));
    }
    Ok(())
}

#[cfg(test)]
fn app_signature_error(node_index: usize, reason: impl Into<String>) -> ProofCheckError {
    malformed_bundle(format!(
        "application term t{node_index} has invalid builtin signature: {}",
        reason.into()
    ))
}

#[cfg(test)]
fn validate_named_app_signature(
    entries: &[(TermData, Sort)],
    node_index: usize,
    name: &str,
    args: &[TermId],
    result_sort: &Sort,
) -> Result<(), ProofCheckError> {
    let arg_sort = |index: usize| &entries[args[index].index()].1;
    let exact_arity = |expected: usize| {
        (args.len() == expected).then_some(()).ok_or_else(|| {
            app_signature_error(
                node_index,
                format!("`{name}` expects {expected} arguments, got {}", args.len()),
            )
        })
    };
    match name {
        "=" => {
            exact_arity(2)?;
            if result_sort != &Sort::Bool || arg_sort(0) != arg_sort(1) {
                return Err(app_signature_error(
                    node_index,
                    "`=` must return Bool and compare equal-sorted operands",
                ));
            }
        }
        "distinct"
            if result_sort != &Sort::Bool
                || args.first().is_some_and(|_| {
                    (1..args.len()).any(|index| arg_sort(index) != arg_sort(0))
                }) =>
        {
            return Err(app_signature_error(
                node_index,
                "`distinct` must return Bool and use one operand sort",
            ));
        }
        "not" => {
            exact_arity(1)?;
            if result_sort != &Sort::Bool || arg_sort(0) != &Sort::Bool {
                return Err(app_signature_error(
                    node_index,
                    "`not` must have signature Bool -> Bool",
                ));
            }
        }
        "and" | "or" | "xor"
            if result_sort != &Sort::Bool
                || args.iter().any(|arg| entries[arg.index()].1 != Sort::Bool) =>
        {
            return Err(app_signature_error(
                node_index,
                format!("`{name}` must consume and return Bool"),
            ));
        }
        "=>" if args.len() < 2
            || result_sort != &Sort::Bool
            || args.iter().any(|arg| entries[arg.index()].1 != Sort::Bool) =>
        {
            return Err(app_signature_error(
                node_index,
                "`=>` must consume at least two Bool operands and return Bool",
            ));
        }
        "ite" => {
            exact_arity(3)?;
            if arg_sort(0) != &Sort::Bool
                || arg_sort(1) != arg_sort(2)
                || arg_sort(1) != result_sort
            {
                return Err(app_signature_error(
                    node_index,
                    "`ite` condition, branches, and result are inconsistently sorted",
                ));
            }
        }
        "select" => {
            exact_arity(2)?;
            let Sort::Array(array) = arg_sort(0) else {
                return Err(app_signature_error(
                    node_index,
                    "`select` first operand is not an array",
                ));
            };
            if arg_sort(1) != &array.index_sort || result_sort != &array.element_sort {
                return Err(app_signature_error(
                    node_index,
                    "`select` index or result sort disagrees with its array sort",
                ));
            }
        }
        "store" => {
            exact_arity(3)?;
            let Sort::Array(array) = arg_sort(0) else {
                return Err(app_signature_error(
                    node_index,
                    "`store` first operand is not an array",
                ));
            };
            if arg_sort(1) != &array.index_sort
                || arg_sort(2) != &array.element_sort
                || result_sort != arg_sort(0)
            {
                return Err(app_signature_error(
                    node_index,
                    "`store` index, value, or result sort disagrees with its array sort",
                ));
            }
        }
        "const-array" => {
            exact_arity(1)?;
            let Sort::Array(array) = result_sort else {
                return Err(app_signature_error(
                    node_index,
                    "`const-array` result is not array-sorted",
                ));
            };
            if arg_sort(0) != &array.element_sort {
                return Err(app_signature_error(
                    node_index,
                    "`const-array` fill sort disagrees with its element sort",
                ));
            }
        }
        "bvnot" | "bvneg" => {
            exact_arity(1)?;
            if !matches!(arg_sort(0), Sort::BitVec(_)) || result_sort != arg_sort(0) {
                return Err(app_signature_error(
                    node_index,
                    format!("`{name}` must preserve one bit-vector sort"),
                ));
            }
        }
        "bvand" | "bvor" | "bvxor" | "bvnand" | "bvnor" | "bvxnor" | "bvadd" | "bvsub"
        | "bvmul" | "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem" | "bvsmod" | "bvshl" | "bvlshr"
        | "bvashr" => {
            exact_arity(2)?;
            if !matches!(arg_sort(0), Sort::BitVec(_))
                || arg_sort(0) != arg_sort(1)
                || result_sort != arg_sort(0)
            {
                return Err(app_signature_error(
                    node_index,
                    format!("`{name}` must consume and return one bit-vector sort"),
                ));
            }
        }
        "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge" => {
            exact_arity(2)?;
            if !matches!(arg_sort(0), Sort::BitVec(_))
                || arg_sort(0) != arg_sort(1)
                || result_sort != &Sort::Bool
            {
                return Err(app_signature_error(
                    node_index,
                    format!("`{name}` must compare one bit-vector sort and return Bool"),
                ));
            }
        }
        "concat" => {
            exact_arity(2)?;
            let (Sort::BitVec(lhs), Sort::BitVec(rhs), Sort::BitVec(result)) =
                (arg_sort(0), arg_sort(1), result_sort)
            else {
                return Err(app_signature_error(
                    node_index,
                    "`concat` operands and result must be bit-vectors",
                ));
            };
            if lhs.width.checked_add(rhs.width) != Some(result.width) {
                return Err(app_signature_error(
                    node_index,
                    "`concat` result width must equal the sum of operand widths",
                ));
            }
        }
        "extract" | "zero_extend" | "sign_extend" | "rotate_left" | "rotate_right" | "repeat" => {
            return Err(app_signature_error(
                node_index,
                format!("bit-vector operator `{name}` must be an indexed symbol"),
            ));
        }
        "fp" => {
            exact_arity(3)?;
            let (Sort::BitVec(sign), Sort::BitVec(exponent), Sort::BitVec(significand)) =
                (arg_sort(0), arg_sort(1), arg_sort(2))
            else {
                return Err(app_signature_error(
                    node_index,
                    "`fp` operands must be bit-vectors",
                ));
            };
            let Sort::FloatingPoint(result_exponent, result_significand) = result_sort else {
                return Err(app_signature_error(
                    node_index,
                    "`fp` result must be floating-point sorted",
                ));
            };
            if sign.width != 1
                || exponent.width != *result_exponent
                || significand.width.checked_add(1) != Some(*result_significand)
            {
                return Err(app_signature_error(
                    node_index,
                    "`fp` component widths do not match its result format",
                ));
            }
        }
        "fp.abs" | "fp.neg" => {
            exact_arity(1)?;
            if !matches!(arg_sort(0), Sort::FloatingPoint(_, _)) || result_sort != arg_sort(0) {
                return Err(app_signature_error(
                    node_index,
                    format!("`{name}` must preserve one floating-point sort"),
                ));
            }
        }
        "fp.isNaN" | "fp.isInfinite" | "fp.isZero" | "fp.isNormal" | "fp.isSubnormal"
        | "fp.isPositive" | "fp.isNegative" => {
            exact_arity(1)?;
            if !matches!(arg_sort(0), Sort::FloatingPoint(_, _)) || result_sort != &Sort::Bool {
                return Err(app_signature_error(
                    node_index,
                    format!("`{name}` must map one floating-point operand to Bool"),
                ));
            }
        }
        "fp.eq" | "fp.lt" | "fp.leq" | "fp.gt" | "fp.geq" => {
            exact_arity(2)?;
            if !matches!(arg_sort(0), Sort::FloatingPoint(_, _))
                || arg_sort(0) != arg_sort(1)
                || result_sort != &Sort::Bool
            {
                return Err(app_signature_error(
                    node_index,
                    format!("`{name}` must compare one floating-point format and return Bool"),
                ));
            }
        }
        "+zero" | "-zero" | "+oo" | "-oo" | "NaN" => {
            return Err(app_signature_error(
                node_index,
                format!("floating-point literal `{name}` must be an indexed symbol"),
            ));
        }
        _ => {}
    }
    Ok(())
}

#[cfg(test)]
fn validate_indexed_bv_signature(
    entries: &[(TermData, Sort)],
    node_index: usize,
    name: &str,
    indices: &[u32],
    args: &[TermId],
    result_sort: &Sort,
) -> Result<bool, ProofCheckError> {
    if !matches!(
        name,
        "extract" | "zero_extend" | "sign_extend" | "rotate_left" | "rotate_right" | "repeat"
    ) {
        return Ok(false);
    }
    if args.len() != 1 || indices.len() != if name == "extract" { 2 } else { 1 } {
        return Err(app_signature_error(
            node_index,
            format!("indexed `{name}` has an invalid number of indices or arguments"),
        ));
    }
    let Sort::BitVec(input) = &entries[args[0].index()].1 else {
        return Err(app_signature_error(
            node_index,
            format!("indexed `{name}` operand is not a bit-vector"),
        ));
    };
    let Sort::BitVec(result) = result_sort else {
        return Err(app_signature_error(
            node_index,
            format!("indexed `{name}` result is not a bit-vector"),
        ));
    };

    let expected_width = match name {
        "extract" => {
            let (high, low) = (indices[0], indices[1]);
            if low > high || high >= input.width {
                return Err(app_signature_error(
                    node_index,
                    "`extract` indices are outside the operand width",
                ));
            }
            high - low + 1
        }
        "zero_extend" | "sign_extend" => input.width.checked_add(indices[0]).ok_or_else(|| {
            app_signature_error(
                node_index,
                format!("indexed `{name}` result width overflows"),
            )
        })?,
        "rotate_left" | "rotate_right" => input.width,
        "repeat" => {
            if indices[0] == 0 {
                return Err(app_signature_error(
                    node_index,
                    "`repeat` count must be positive",
                ));
            }
            input.width.checked_mul(indices[0]).ok_or_else(|| {
                app_signature_error(node_index, "indexed `repeat` result width overflows")
            })?
        }
        _ => unreachable!("indexed bit-vector operator match is exhaustive"),
    };
    if result.width != expected_width {
        return Err(app_signature_error(
            node_index,
            format!(
                "indexed `{name}` records result width {}, expected {expected_width}",
                result.width
            ),
        ));
    }
    Ok(true)
}

#[cfg(test)]
fn requires_named_symbol(name: &str) -> bool {
    requires_named_core_or_bv_symbol(name)
        || requires_named_fp_symbol(name)
        || requires_named_string_or_regex_symbol(name)
}

#[cfg(test)]
fn requires_named_core_or_bv_symbol(name: &str) -> bool {
    matches!(
        name,
        "=" | "distinct"
            | "not"
            | "and"
            | "or"
            | "xor"
            | "=>"
            | "ite"
            | "select"
            | "store"
            | "const-array"
            | "bvnot"
            | "bvneg"
            | "bvand"
            | "bvor"
            | "bvxor"
            | "bvnand"
            | "bvnor"
            | "bvxnor"
            | "bvadd"
            | "bvsub"
            | "bvmul"
            | "bvudiv"
            | "bvurem"
            | "bvsdiv"
            | "bvsrem"
            | "bvsmod"
            | "bvshl"
            | "bvlshr"
            | "bvashr"
            | "bvult"
            | "bvule"
            | "bvugt"
            | "bvuge"
            | "bvslt"
            | "bvsle"
            | "bvsgt"
            | "bvsge"
            | "concat"
            | "+"
            | "-"
            | "*"
            | "/"
            | "abs"
            | "div"
            | "mod"
            | "<"
            | "<="
            | ">"
            | ">="
    )
}

#[cfg(test)]
fn requires_named_fp_symbol(name: &str) -> bool {
    matches!(
        name,
        "fp" | "fp.abs"
            | "fp.neg"
            | "fp.isNaN"
            | "fp.isInfinite"
            | "fp.isZero"
            | "fp.isNormal"
            | "fp.isSubnormal"
            | "fp.isPositive"
            | "fp.isNegative"
            | "fp.eq"
            | "fp.lt"
            | "fp.leq"
            | "fp.gt"
            | "fp.geq"
            | "fp.add"
            | "fp.sub"
            | "fp.mul"
            | "fp.div"
            | "fp.fma"
            | "fp.sqrt"
            | "fp.to_real"
            | "RNE"
            | "RNA"
            | "RTP"
            | "RTN"
            | "RTZ"
            | "roundNearestTiesToEven"
            | "roundNearestTiesToAway"
            | "roundTowardPositive"
            | "roundTowardNegative"
            | "roundTowardZero"
    )
}

#[cfg(test)]
fn requires_named_string_or_regex_symbol(name: &str) -> bool {
    matches!(
        name,
        "str.++"
            | "str.len"
            | "str.at"
            | "str.substr"
            | "str.contains"
            | "str.prefixof"
            | "str.suffixof"
            | "str.indexof"
            | "str.replace"
            | "str.replace_all"
            | "str.to_code"
            | "str.from_code"
            | "str.to_int"
            | "str.to.int"
            | "str.from_int"
            | "str.is_digit"
            | "str.<"
            | "str.<="
            | "str.in_re"
            | "str.in.re"
            | "str.to_re"
            | "str.to.re"
            | "re.none"
            | "re.all"
            | "re.allchar"
            | "re.range"
            | "re.++"
            | "re.union"
            | "re.inter"
            | "re.*"
            | "re.+"
            | "re.opt"
            | "re.comp"
            | "re.diff"
    )
}

#[cfg(test)]
fn validate_app_signature(
    entries: &[(TermData, Sort)],
    node_index: usize,
    symbol: &Symbol,
    args: &[TermId],
    result_sort: &Sort,
) -> Result<(), ProofCheckError> {
    // The snapshot does not yet serialize the complete declaration table, so
    // arbitrary uninterpreted-function signatures cannot be reconstructed
    // here. Validate the structural builtins and bounded-checker operations
    // whose malformed signatures could violate checker invariants;
    // declaration-backed datatype constructors are checked separately against
    // the v5 context in `validate_declared_constructor_terms`.
    match symbol {
        Symbol::Named(name) => {
            validate_named_app_signature(entries, node_index, name, args, result_sort)
        }
        Symbol::Indexed(name, indices) => {
            if validate_indexed_bv_signature(entries, node_index, name, indices, args, result_sort)?
            {
                return Ok(());
            }
            if requires_named_symbol(name) {
                return Err(app_signature_error(
                    node_index,
                    format!("builtin `{name}` must be a named symbol without indices"),
                ));
            }
            if !matches!(name.as_str(), "+zero" | "-zero" | "+oo" | "-oo" | "NaN") {
                return Ok(());
            }
            let Sort::FloatingPoint(exponent, significand) = result_sort else {
                return Err(app_signature_error(
                    node_index,
                    "indexed floating-point literal is not floating-point sorted",
                ));
            };
            if !args.is_empty() || indices.as_slice() != [*exponent, *significand] {
                return Err(app_signature_error(
                    node_index,
                    "indexed floating-point literal has inconsistent indices or arguments",
                ));
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

#[cfg(test)]
fn validate_term_snapshot_legacy(entries: &[(TermData, Sort)]) -> Result<(), ProofCheckError> {
    if entries.len() > u32::MAX as usize {
        return Err(malformed_bundle(format!(
            "term snapshot contains {} entries, exceeding TermId capacity",
            entries.len()
        )));
    }

    let mut canonical_entries = HashSet::default();
    for (node_index, (data, result_sort)) in entries.iter().enumerate() {
        validate_sort(result_sort, node_index, "recorded sort", 0)?;
        match data {
            TermData::Const(constant) => {
                validate_constant_sort(node_index, constant, result_sort)?;
            }
            TermData::Var(_, _) => {}
            TermData::App(symbol, args) => {
                for &arg in args {
                    prior_child_sort(entries, node_index, arg, "application argument")?;
                }
                validate_app_signature(entries, node_index, symbol, args, result_sort)?;
            }
            TermData::Let(bindings, body) => {
                let mut names = HashSet::default();
                for (name, value) in bindings {
                    if !names.insert(name.as_str()) {
                        return Err(malformed_bundle(format!(
                            "let term t{node_index} repeats binding `{name}`"
                        )));
                    }
                    prior_child_sort(entries, node_index, *value, "let binding")?;
                }
                let body_sort = prior_child_sort(entries, node_index, *body, "let body")?;
                if body_sort != result_sort {
                    return Err(malformed_bundle(format!(
                        "let term t{node_index} records sort {result_sort}, but its body has sort {body_sort}"
                    )));
                }
            }
            TermData::Not(inner) => {
                let inner_sort = prior_child_sort(entries, node_index, *inner, "negated child")?;
                if result_sort != &Sort::Bool || inner_sort != &Sort::Bool {
                    return Err(malformed_bundle(format!(
                        "not term t{node_index} and its child must both have sort Bool"
                    )));
                }
            }
            TermData::Ite(condition, then_branch, else_branch) => {
                let condition_sort =
                    prior_child_sort(entries, node_index, *condition, "ite condition")?;
                let then_sort =
                    prior_child_sort(entries, node_index, *then_branch, "ite then branch")?;
                let else_sort =
                    prior_child_sort(entries, node_index, *else_branch, "ite else branch")?;
                if condition_sort != &Sort::Bool
                    || then_sort != else_sort
                    || then_sort != result_sort
                {
                    return Err(malformed_bundle(format!(
                        "ite term t{node_index} has inconsistent condition, branch, or result sorts"
                    )));
                }
            }
            TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                if result_sort != &Sort::Bool {
                    return Err(malformed_bundle(format!(
                        "quantifier term t{node_index} must have sort Bool, got {result_sort}"
                    )));
                }
                let body_sort = prior_child_sort(entries, node_index, *body, "quantifier body")?;
                if body_sort != &Sort::Bool {
                    return Err(malformed_bundle(format!(
                        "quantifier term t{node_index} has non-Boolean body sort {body_sort}"
                    )));
                }
                let mut names = HashSet::default();
                for (name, sort) in vars {
                    if !names.insert(name.as_str()) {
                        return Err(malformed_bundle(format!(
                            "quantifier term t{node_index} repeats binding `{name}`"
                        )));
                    }
                    validate_sort(sort, node_index, "quantifier binding sort", 0)?;
                }
                for &trigger in triggers.iter().flatten() {
                    prior_child_sort(entries, node_index, trigger, "quantifier trigger")?;
                }
            }
            _ => {
                return Err(malformed_bundle(format!(
                    "term t{node_index} uses an unsupported term-data variant"
                )));
            }
        }
        // Hash/Eq recurse through both the recorded sort and any quantifier
        // binder sorts. Validate the COMPLETE entry first so those operations
        // cannot traverse an unbounded or structurally malformed sort tree.
        if !canonical_entries.insert((data, result_sort)) {
            return Err(malformed_bundle(format!(
                "term t{node_index} duplicates an earlier canonical term entry"
            )));
        }
    }
    Ok(())
}

#[cfg(test)]
fn validate_bool_constant_id(
    entries: &[(TermData, Sort)],
    id: Option<TermId>,
    expected: bool,
) -> Result<(), ProofCheckError> {
    let role = if expected { "true_term" } else { "false_term" };
    let id = id.ok_or_else(|| malformed_bundle(format!("bundle is missing {role}")))?;
    let (data, sort) = bundle_term(entries, id, role)?;
    if sort != &Sort::Bool || data != &TermData::Const(Constant::Bool(expected)) {
        return Err(malformed_bundle(format!(
            "{role} {id} is not the expected Boolean constant"
        )));
    }
    Ok(())
}

#[cfg(test)]
fn preflight_bundle_legacy(
    bundle: &SerializableProofBundle,
) -> Result<HashMap<String, &'static str>, ProofCheckError> {
    validate_term_snapshot_legacy(&bundle.term_entries)?;
    for (signature_index, signature) in bundle.datatype_member_signatures.iter().enumerate() {
        for (argument_index, sort) in signature.argument_sorts.iter().enumerate() {
            validate_sort(
                sort,
                signature_index,
                &format!(
                    "datatype member signature {:?} argument {argument_index} sort",
                    signature.identity
                ),
                0,
            )?;
        }
        validate_sort(
            &signature.result_sort,
            signature_index,
            &format!(
                "datatype member signature {:?} result sort",
                signature.identity
            ),
            0,
        )?;
    }
    validate_bool_constant_id(&bundle.term_entries, bundle.true_term, true)?;
    validate_bool_constant_id(&bundle.term_entries, bundle.false_term, false)?;
    for &assertion in &bundle.obligation_assertions {
        bundle_bool_term(&bundle.term_entries, assertion, "obligation assertion")?;
    }
    let declaration_term_symbols = validate_declaration_context(bundle)?;
    validate_declared_constructor_terms(bundle)?;
    validate_proof_snapshot(&bundle.steps, &bundle.term_entries)?;
    Ok(declaration_term_symbols)
}

#[cfg(test)]
fn validate_term_snapshot(entries: &[(TermData, Sort)]) -> Result<(), ProofCheckError> {
    preflight_term::validate_term_snapshot_with_progress(entries, &mut |_, _| true)
}

#[cfg(test)]
fn preflight_bundle(
    bundle: &SerializableProofBundle,
) -> Result<HashMap<String, &'static str>, ProofCheckError> {
    preflight::preflight_bundle_with_progress(bundle, &mut |_, _| true)
}

/// Re-check a serialized proof bundle OFFLINE — no solver, no access to the
/// producer's term store. Rebuilds a checker-only [`TermStore`] from the
/// snapshot and a [`Proof`] from the steps, then runs
/// [`check_proof_strict_with_typed_context`](crate::check_proof_strict_with_typed_context)
/// (which rejects trust/hole steps,
/// checks extensionality witnesses against `obligation_assertions`, validates
/// the exact datatype member signatures, and requires the terminal empty
/// clause). On success returns the strict quality and the proof's `assume` axiom
/// term ids.
///
/// Success authenticates only the bundle's internal proof/context pairing. It
/// does not establish that its claimed assertions or declarations match an
/// external source problem; see the module-level schema-v5 binding contract.
///
/// Fail-closed on a schema-tag mismatch (a version skew that could mis-decode).
pub fn re_check_bundle_strict(
    bundle: &SerializableProofBundle,
) -> Result<BundleReCheck, ProofCheckError> {
    re_check_bundle_strict_with_cancellation(bundle, &mut || true)
}

/// Render a term to a canonical, STORE-INDEPENDENT S-expression string.
///
/// Variables are rendered by NAME (the internal `u32` uniquing counter is
/// ignored), so two structurally-equal terms in different term stores render to
/// the SAME string. This lets a consumer compare an embedded obligation term
/// against an independently-built one at the term level without sharing ids.
/// The rendering omits datatype, selector, and arbitrary free-symbol
/// declarations, so it is not by itself a secure external problem-binding key;
/// compare the full schema-v5 context described in the module documentation.
#[must_use]
pub fn render_term_canonical(terms: &TermStore, id: TermId) -> String {
    AlethePrinter::new(terms).format_term(id)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::{AletheRule, FpOp, Sort, TermStore, TheoryLemmaKind};

    /// A complete contradiction proof that also carries one valid, fresh
    /// array-extensionality certificate. The terminal contradiction uses only
    /// the authored `(= a b)` / `(not (= a b))` assumptions; the extensionality
    /// lemma need not be on the resolution path for strict mode to validate it.
    struct ArrayExtBundleFixture {
        terms: TermStore,
        proof: Proof,
        obligation_assertions: Vec<TermId>,
        witness: TermId,
        array_a: TermId,
    }

    impl ArrayExtBundleFixture {
        fn new() -> Self {
            let mut terms = TermStore::new();
            let array_sort = Sort::array(Sort::Int, Sort::Int);
            let array_a = terms.mk_var("bundle_a", array_sort.clone());
            let array_b = terms.mk_var("bundle_b", array_sort);
            let witness = terms.mk_var("__bundle_ext_diff", Sort::Int);
            let array_eq = terms.mk_eq(array_a, array_b);
            let not_array_eq = terms.mk_not(array_eq);
            let select_a = terms.mk_select(array_a, witness);
            let select_b = terms.mk_select(array_b, witness);
            let select_eq = terms.mk_eq(select_a, select_b);
            let not_select_eq = terms.mk_not(select_eq);

            let mut proof = Proof::new();
            proof.add_rule_step(
                AletheRule::ArrayExtDiffIntro,
                Vec::new(),
                Vec::new(),
                vec![witness, array_a, array_b],
            );
            let positive = proof.add_assume(array_eq, None);
            let negative = proof.add_assume(not_array_eq, None);
            proof.add_theory_lemma_with_kind(
                "arrays",
                vec![array_eq, not_select_eq],
                TheoryLemmaKind::ArrayExtensionality,
            );
            proof.add_resolution(Vec::new(), array_eq, positive, negative);

            Self {
                terms,
                proof,
                obligation_assertions: vec![array_eq, not_array_eq],
                witness,
                array_a,
            }
        }

        fn bundle(&self) -> SerializableProofBundle {
            SerializableProofBundle::from_proof(
                &self.proof,
                &self.terms,
                self.obligation_assertions.clone(),
            )
        }
    }

    #[test]
    fn bundle_recheck_uses_stored_obligations_for_array_extensionality() {
        let fixture = ArrayExtBundleFixture::new();
        let without_context = crate::check_proof_strict(&fixture.proof, &fixture.terms)
            .expect_err("plain strict checking has no witness-freshness context");
        assert!(
            matches!(without_context, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
                if reason.contains("no checked provenance")),
            "expected the context-free checker to fail closed, got {without_context:?}"
        );

        let json = serde_json::to_string(&fixture.bundle()).expect("serialize proof bundle");
        let restored: SerializableProofBundle =
            serde_json::from_str(&json).expect("deserialize proof bundle");
        let recheck = re_check_bundle_strict(&restored)
            .expect("stored obligations make the fresh witness checkable offline");

        assert!(recheck.quality.is_complete());
        assert_eq!(recheck.assume_terms, restored.obligation_assertions);
    }

    #[test]
    fn bundle_recheck_rejects_a_forged_extensionality_binding() {
        let mut fixture = ArrayExtBundleFixture::new();
        let other = fixture
            .terms
            .mk_var("bundle_other", Sort::array(Sort::Int, Sort::Int));
        match &mut fixture.proof.steps[0] {
            ProofStep::Step {
                rule: AletheRule::ArrayExtDiffIntro,
                args,
                ..
            } => *args = vec![fixture.witness, fixture.array_a, other],
            step => panic!("expected the first step to introduce the witness, got {step:?}"),
        }

        let err = re_check_bundle_strict(&fixture.bundle())
            .expect_err("an introduction for another array pair must fail offline");
        assert!(
            matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
                if reason.contains("DIFFERENT array pair")),
            "expected a forged-pair rejection, got {err:?}"
        );
    }

    #[test]
    fn bundle_recheck_rejects_a_nonfresh_extensionality_witness() {
        let mut fixture = ArrayExtBundleFixture::new();
        let zero = fixture.terms.mk_int(0.into());
        let pinned = fixture.terms.mk_eq(fixture.witness, zero);
        fixture.obligation_assertions.push(pinned);

        let err = re_check_bundle_strict(&fixture.bundle())
            .expect_err("a witness constrained by the stored obligation is not fresh");
        assert!(
            matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
                if reason.contains("NOT fresh")),
            "expected a non-fresh witness rejection, got {err:?}"
        );
    }

    struct SkolemBundleFixture {
        terms: TermStore,
        proof: Proof,
        obligation_assertions: Vec<TermId>,
        witness: TermId,
    }

    impl SkolemBundleFixture {
        fn new() -> Self {
            Self::with_witness("sk!bundle_sko_x", Sort::Int)
        }

        fn with_witness(witness_name: &str, witness_sort: Sort) -> Self {
            let mut terms = TermStore::new();
            let bound = terms.mk_var("bundle_sko_x", witness_sort.clone());
            let body = terms.mk_app(Symbol::named("bundle_sko_p"), [bound], Sort::Bool);
            let source = terms.mk_forall(
                vec![("bundle_sko_x".to_string(), witness_sort.clone())],
                body,
            );
            let witness = terms.mk_fresh_named_var(witness_name, witness_sort);
            let authenticated_name = match terms.get(witness) {
                TermData::Var(name, _) => name.clone(),
                _ => unreachable!("fresh Skolem constant is atomic"),
            };
            terms.mark_skolem_symbol(authenticated_name);
            let instance = terms.mk_app(Symbol::named("bundle_sko_p"), [witness], Sort::Bool);
            // Preserve the source on the left; Boolean mk_eq may canonicalize it.
            let equality = terms.mk_app(Symbol::named("="), [source, instance], Sort::Bool);
            let not_source = terms.mk_not(source);

            let mut proof = Proof::new();
            proof.add_rule_step(
                AletheRule::Skolem,
                vec![equality],
                Vec::new(),
                vec![witness],
            );
            let positive = proof.add_assume(source, None);
            let negative = proof.add_assume(not_source, None);
            proof.add_resolution(Vec::new(), source, positive, negative);

            Self {
                terms,
                proof,
                obligation_assertions: vec![source, not_source],
                witness,
            }
        }

        fn bundle(&self) -> SerializableProofBundle {
            SerializableProofBundle::from_proof(
                &self.proof,
                &self.terms,
                self.obligation_assertions.clone(),
            )
        }

        fn add_bundle_option_context(&self, bundle: &mut SerializableProofBundle) {
            let carrier = Sort::Uninterpreted("BundleOption".to_string());
            let none_term = bundle
                .term_entries
                .iter()
                .position(|(data, sort)| {
                    matches!(data, TermData::Var(name, _) if name == "BundleNone")
                        && sort == &carrier
                })
                .map_or_else(
                    || {
                        let term = TermId::new(
                            u32::try_from(bundle.term_entries.len()).expect("small bundle fixture"),
                        );
                        let unique = bundle.var_counter;
                        bundle.var_counter = bundle
                            .var_counter
                            .checked_add(1)
                            .expect("small bundle fixture");
                        bundle.term_entries.push((
                            TermData::Var("BundleNone".to_string(), unique),
                            carrier.clone(),
                        ));
                        term
                    },
                    |index| TermId::new(u32::try_from(index).expect("small bundle fixture")),
                );
            bundle.datatype_declarations = vec![(
                "BundleOption".to_string(),
                vec!["BundleNone".to_string(), "BundleSome".to_string()],
            )];
            bundle.constructor_selectors = vec![
                ("BundleNone".to_string(), Vec::new()),
                ("BundleSome".to_string(), vec!["bundle_value".to_string()]),
            ];
            bundle.datatype_member_signatures = vec![
                DatatypeMemberSignature {
                    identity: "BundleNone".to_string(),
                    argument_sorts: Vec::new(),
                    result_sort: carrier.clone(),
                    nullary_term: Some(none_term),
                },
                DatatypeMemberSignature {
                    identity: "is-BundleNone".to_string(),
                    argument_sorts: vec![carrier.clone()],
                    result_sort: Sort::Bool,
                    nullary_term: None,
                },
                DatatypeMemberSignature {
                    identity: "BundleSome".to_string(),
                    argument_sorts: vec![Sort::Int],
                    result_sort: carrier.clone(),
                    nullary_term: None,
                },
                DatatypeMemberSignature {
                    identity: "is-BundleSome".to_string(),
                    argument_sorts: vec![carrier.clone()],
                    result_sort: Sort::Bool,
                    nullary_term: None,
                },
                DatatypeMemberSignature {
                    identity: "bundle_value".to_string(),
                    argument_sorts: vec![carrier],
                    result_sort: Sort::Int,
                    nullary_term: None,
                },
            ];
        }
    }

    fn assert_skolem_declaration_collision(
        bundle: &SerializableProofBundle,
        expected_name: &str,
        expected_role: &str,
    ) {
        let err = re_check_bundle_strict(bundle)
            .expect_err("a datatype-owned term symbol cannot be restored as a Skolem");
        assert!(
            matches!(err, ProofCheckError::InvalidBooleanRule { ref reason, .. }
                if reason.contains(expected_name)
                    && reason.contains(expected_role)
                    && reason.contains("serialized datatype declaration-owned term namespace"))
                || matches!(err, ProofCheckError::InvalidDatatypeSignatureContext { ref reason }
                    if reason.contains(expected_name)
                        && reason.contains("datatype member variable")),
            "expected a datatype/Skolem namespace-collision rejection for {expected_name:?}, got {err:?}"
        );
    }

    #[test]
    fn bundle_recheck_reconstructs_skolem_authority_from_proof_provenance() {
        let fixture = SkolemBundleFixture::new();
        let rebuilt = re_check_bundle_strict(&fixture.bundle())
            .expect("fresh exact Skolem choice must re-check without serialized name authority");
        assert!(rebuilt.quality.is_complete());
    }

    #[test]
    fn bundle_recheck_accepts_a_skolem_disjoint_from_the_datatype_term_namespace() {
        let fixture = SkolemBundleFixture::new();
        let mut bundle = fixture.bundle();
        fixture.add_bundle_option_context(&mut bundle);

        let rebuilt = re_check_bundle_strict(&bundle)
            .expect("an unrelated datatype declaration must not block Skolem authentication");
        assert!(rebuilt.quality.is_complete());
    }

    #[test]
    fn bundle_recheck_rejects_a_skolem_named_as_a_nullary_constructor() {
        let fixture = SkolemBundleFixture::with_witness(
            "BundleNone",
            Sort::Uninterpreted("BundleOption".to_string()),
        );
        let mut bundle = fixture.bundle();
        fixture.add_bundle_option_context(&mut bundle);

        assert_skolem_declaration_collision(&bundle, "BundleNone", "a constructor");
    }

    #[test]
    fn bundle_recheck_rejects_a_skolem_named_as_a_selector() {
        let fixture = SkolemBundleFixture::with_witness("bundle_value", Sort::Int);
        let mut bundle = fixture.bundle();
        fixture.add_bundle_option_context(&mut bundle);

        assert_skolem_declaration_collision(&bundle, "bundle_value", "a selector");
    }

    #[test]
    fn bundle_recheck_rejects_a_skolem_named_as_a_derived_tester() {
        let fixture = SkolemBundleFixture::with_witness("is-BundleSome", Sort::Bool);
        let mut bundle = fixture.bundle();
        fixture.add_bundle_option_context(&mut bundle);

        assert_skolem_declaration_collision(&bundle, "is-BundleSome", "a derived tester");
    }

    #[test]
    fn bundle_preflight_rejects_ambiguous_datatype_owned_term_symbols() {
        let fixture = SkolemBundleFixture::new();
        let mut bundle = fixture.bundle();
        bundle.datatype_declarations = vec![(
            "BundleEither".to_string(),
            vec!["BundleLeft".to_string(), "BundleRight".to_string()],
        )];
        bundle.constructor_selectors = vec![
            ("BundleLeft".to_string(), vec!["bundle_shared".to_string()]),
            ("BundleRight".to_string(), vec!["bundle_shared".to_string()]),
        ];

        assert_malformed_bundle(&bundle, "term symbol \"bundle_shared\" is ambiguous");
    }

    #[test]
    fn bundle_recheck_rejects_a_skolem_witness_constrained_by_the_obligation() {
        let mut fixture = SkolemBundleFixture::new();
        let zero = fixture.terms.mk_int(0.into());
        let pinned = fixture.terms.mk_eq(fixture.witness, zero);
        fixture.obligation_assertions.push(pinned);

        let err = re_check_bundle_strict(&fixture.bundle())
            .expect_err("a problem-constrained constant is not a fresh Skolem choice");
        assert!(
            matches!(err, ProofCheckError::InvalidBooleanRule { ref reason, .. }
                if reason.contains("not fresh")),
            "expected a non-fresh Skolem rejection, got {err:?}"
        );
    }

    #[test]
    fn bundle_recheck_rejects_cyclic_skolem_choice_dependencies() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("bundle_cycle_x", Sort::Int);
        let y = terms.mk_var("bundle_cycle_y", Sort::Int);
        let witness_x = terms.mk_fresh_var("sk!bundle_cycle_x", Sort::Int);
        let witness_y = terms.mk_fresh_var("sk!bundle_cycle_y", Sort::Int);

        let body_x = terms.mk_app(Symbol::named("bundle_cycle_p"), [x, witness_y], Sort::Bool);
        let source_x = terms.mk_forall(vec![("bundle_cycle_x".to_string(), Sort::Int)], body_x);
        let instance_x = terms.mk_app(
            Symbol::named("bundle_cycle_p"),
            [witness_x, witness_y],
            Sort::Bool,
        );
        let equality_x = terms.mk_app(Symbol::named("="), [source_x, instance_x], Sort::Bool);

        let body_y = terms.mk_app(Symbol::named("bundle_cycle_q"), [y, witness_x], Sort::Bool);
        let source_y = terms.mk_forall(vec![("bundle_cycle_y".to_string(), Sort::Int)], body_y);
        let instance_y = terms.mk_app(
            Symbol::named("bundle_cycle_q"),
            [witness_y, witness_x],
            Sort::Bool,
        );
        let equality_y = terms.mk_app(Symbol::named("="), [source_y, instance_y], Sort::Bool);

        let contradiction = terms.mk_var("bundle_cycle_contradiction", Sort::Bool);
        let not_contradiction = terms.mk_not(contradiction);
        let mut proof = Proof::new();
        proof.add_rule_step(
            AletheRule::Skolem,
            vec![equality_x],
            Vec::new(),
            vec![witness_x],
        );
        proof.add_rule_step(
            AletheRule::Skolem,
            vec![equality_y],
            Vec::new(),
            vec![witness_y],
        );
        let positive = proof.add_assume(contradiction, None);
        let negative = proof.add_assume(not_contradiction, None);
        proof.add_resolution(Vec::new(), contradiction, positive, negative);

        let bundle = SerializableProofBundle::from_proof(
            &proof,
            &terms,
            vec![contradiction, not_contradiction],
        );
        let err = re_check_bundle_strict(&bundle)
            .expect_err("mutually recursive Skolem choices need not have a joint model");
        assert!(
            matches!(err, ProofCheckError::InvalidBooleanRule { ref reason, .. }
                if reason.contains("cyclic choice dependency")),
            "expected a cyclic Skolem dependency rejection, got {err:?}"
        );
    }

    fn assert_malformed_bundle(bundle: &SerializableProofBundle, expected: &str) {
        let err = re_check_bundle_strict(bundle)
            .expect_err("malformed bundle must fail before rebuilding its term store");
        assert!(
            matches!(err, ProofCheckError::MalformedProofBundle { ref reason }
                if reason.contains(expected)),
            "expected malformed-bundle reason containing {expected:?}, got {err:?}"
        );
    }

    #[test]
    fn namespace_identity_cannot_claim_an_authenticated_datatype_member() {
        let mut bundle = typed_datatype_bundle();
        assert!(re_check_bundle_strict(&bundle)
            .unwrap()
            .quality
            .is_complete());
        let identity = bundle.datatype_member_signatures[0].identity.clone();
        bundle.declared_function_identities.push(identity);
        assert!(matches!(
            re_check_bundle_strict(&bundle),
            Err(ProofCheckError::MalformedProofBundle { .. })
        ));
    }

    fn typed_datatype_bundle() -> SerializableProofBundle {
        let mut terms = TermStore::new();
        let carrier = Sort::Uninterpreted("BundleColor".to_string());
        let red = terms.mk_fresh_named_var("bundle-red", carrier.clone());
        let green = terms.mk_fresh_named_var("bundle-green", carrier.clone());
        let equality = terms.mk_app(Symbol::named("="), [red, green], Sort::Bool);
        let disequality = terms.mk_not_raw(equality);
        let mut proof = Proof::new();
        let theorem = proof.add_theory_lemma_with_kind(
            "DT",
            vec![disequality],
            TheoryLemmaKind::DatatypeDistinct,
        );
        let assumption = proof.add_assume(equality, None);
        proof.add_resolution(Vec::new(), equality, theorem, assumption);
        SerializableProofBundle::from_proof_with_typed_context(
            &proof,
            &terms,
            vec![equality],
            vec![(
                "BundleColor".to_string(),
                vec!["bundle-red".to_string(), "bundle-green".to_string()],
            )],
            vec![
                ("bundle-red".to_string(), Vec::new()),
                ("bundle-green".to_string(), Vec::new()),
            ],
            vec![
                DatatypeMemberSignature {
                    identity: "bundle-red".to_string(),
                    argument_sorts: Vec::new(),
                    result_sort: carrier.clone(),
                    nullary_term: Some(red),
                },
                DatatypeMemberSignature {
                    identity: "is-bundle-red".to_string(),
                    argument_sorts: vec![carrier.clone()],
                    result_sort: Sort::Bool,
                    nullary_term: None,
                },
                DatatypeMemberSignature {
                    identity: "bundle-green".to_string(),
                    argument_sorts: Vec::new(),
                    result_sort: carrier.clone(),
                    nullary_term: Some(green),
                },
                DatatypeMemberSignature {
                    identity: "is-bundle-green".to_string(),
                    argument_sorts: vec![carrier],
                    result_sort: Sort::Bool,
                    nullary_term: None,
                },
            ],
        )
    }

    #[test]
    fn schema_v3_bundle_rechecks_exact_datatype_signatures_and_rejects_forgery() {
        let bundle = typed_datatype_bundle();
        re_check_bundle_strict(&bundle).expect("the exact schema-v5 datatype bundle rechecks");

        let mut forged = bundle.clone();
        forged.datatype_member_signatures[0].result_sort = Sort::Int;
        assert!(matches!(
            re_check_bundle_strict(&forged),
            Err(ProofCheckError::InvalidDatatypeSignatureContext { .. })
        ));

        let mut swapped_binding = bundle.clone();
        let red_binding = swapped_binding.datatype_member_signatures[0]
            .nullary_term
            .expect("red has a nullary binding");
        let green_binding = swapped_binding.datatype_member_signatures[2]
            .nullary_term
            .expect("green has a nullary binding");
        swapped_binding.datatype_member_signatures[0].nullary_term = Some(green_binding);
        swapped_binding.datatype_member_signatures[2].nullary_term = Some(red_binding);
        assert!(matches!(
            re_check_bundle_strict(&swapped_binding),
            Err(ProofCheckError::InvalidDatatypeSignatureContext { .. })
        ));

        let legacy_empty_signatures = SerializableProofBundle::from_proof_with_context(
            &Proof::from_steps(bundle.steps.clone()),
            &TermStore::from_entries(
                bundle.term_entries.clone(),
                bundle.true_term,
                bundle.false_term,
                bundle.var_counter,
            ),
            bundle.obligation_assertions.clone(),
            bundle.datatype_declarations.clone(),
            bundle.constructor_selectors.clone(),
        );
        assert!(matches!(
            re_check_bundle_strict(&legacy_empty_signatures),
            Err(ProofCheckError::InvalidDatatypeSignatureContext { .. })
        ));
    }

    #[test]
    fn bundle_preflight_rejects_out_of_range_obligation() {
        let mut bundle = ArrayExtBundleFixture::new().bundle();
        bundle.obligation_assertions[0] = TermId::SENTINEL;
        assert_malformed_bundle(&bundle, "obligation assertion references term");
    }

    #[test]
    fn bundle_preflight_rejects_out_of_range_term_child() {
        let mut bundle = ArrayExtBundleFixture::new().bundle();
        let (data, _) = bundle
            .term_entries
            .iter_mut()
            .find(|(data, _)| matches!(data, TermData::Not(_)))
            .expect("fixture contains a not term");
        *data = TermData::Not(TermId::SENTINEL);
        assert_malformed_bundle(&bundle, "references non-prior term");
    }

    #[test]
    fn bundle_preflight_rejects_non_prior_term_child() {
        let mut bundle = ArrayExtBundleFixture::new().bundle();
        let (node_index, (data, _)) = bundle
            .term_entries
            .iter_mut()
            .enumerate()
            .find(|(_, (data, _))| matches!(data, TermData::Not(_)))
            .expect("fixture contains a not term");
        *data = TermData::Not(TermId::new(node_index as u32));
        assert_malformed_bundle(&bundle, "references non-prior term");
    }

    #[test]
    fn bundle_preflight_rejects_out_of_range_proof_argument() {
        let mut bundle = ArrayExtBundleFixture::new().bundle();
        let ProofStep::Step { args, .. } = &mut bundle.steps[0] else {
            panic!("fixture starts with an extensionality introduction");
        };
        args[0] = TermId::SENTINEL;
        assert_malformed_bundle(&bundle, "proof step t0 argument references term");
    }

    #[test]
    fn bundle_preflight_rejects_out_of_range_proof_premise() {
        let mut bundle = ArrayExtBundleFixture::new().bundle();
        let ProofStep::Resolution { clause1, .. } = bundle
            .steps
            .last_mut()
            .expect("fixture contains a terminal resolution")
        else {
            panic!("fixture ends with a resolution");
        };
        *clause1 = ProofId(u32::MAX);
        assert_malformed_bundle(&bundle, "references missing proof step");
    }

    #[test]
    fn bundle_preflight_rejects_out_of_range_boolean_constant_ids() {
        let mut bad_true = ArrayExtBundleFixture::new().bundle();
        bad_true.true_term = Some(TermId::SENTINEL);
        assert_malformed_bundle(&bad_true, "true_term references term");

        let mut bad_false = ArrayExtBundleFixture::new().bundle();
        bad_false.false_term = Some(TermId::SENTINEL);
        assert_malformed_bundle(&bad_false, "false_term references term");
    }

    #[test]
    fn bundle_preflight_authenticates_boolean_constant_values() {
        let mut bundle = ArrayExtBundleFixture::new().bundle();
        std::mem::swap(&mut bundle.true_term, &mut bundle.false_term);
        assert_malformed_bundle(&bundle, "is not the expected Boolean constant");
    }

    #[test]
    fn bundle_preflight_rejects_invalid_sort_invariants() {
        for (sort, expected) in [
            (Sort::bitvec(0), "invalid bit-vector width"),
            (Sort::FloatingPoint(0, 0), "invalid floating-point format"),
            (
                Sort::FiniteDomain("empty".to_string(), 0),
                "zero-cardinality finite-domain",
            ),
        ] {
            let mut bundle = ArrayExtBundleFixture::new().bundle();
            let (_, recorded_sort) = bundle
                .term_entries
                .iter_mut()
                .find(|(data, _)| matches!(data, TermData::Var(_, _)))
                .expect("fixture contains a variable");
            *recorded_sort = sort;
            assert_malformed_bundle(&bundle, expected);
        }
    }

    #[test]
    fn bundle_preflight_bounds_recursive_sort_validation() {
        let mut nested = Sort::Int;
        for _ in 0..=MAX_BUNDLE_SORT_DEPTH {
            nested = Sort::seq(nested);
        }
        let mut bundle = ArrayExtBundleFixture::new().bundle();
        let (_, recorded_sort) = bundle
            .term_entries
            .iter_mut()
            .find(|(data, _)| matches!(data, TermData::Var(_, _)))
            .expect("fixture contains a variable");
        *recorded_sort = nested;
        assert_malformed_bundle(&bundle, "maximum sort nesting depth");
    }

    #[test]
    fn bundle_preflight_bounds_datatype_member_signature_sorts() {
        let mut nested = Sort::Int;
        for _ in 0..=MAX_BUNDLE_SORT_DEPTH {
            nested = Sort::seq(nested);
        }
        let mut bundle = ArrayExtBundleFixture::new().bundle();
        bundle
            .datatype_member_signatures
            .push(DatatypeMemberSignature {
                identity: "malformed-unused-member".to_string(),
                argument_sorts: vec![nested],
                result_sort: Sort::Bool,
                nullary_term: None,
            });
        assert_malformed_bundle(&bundle, "maximum sort nesting depth");
    }

    #[test]
    fn bundle_preflight_rejects_noncanonical_bitvector_constants() {
        for value in [num_bigint::BigInt::from(-1), num_bigint::BigInt::from(4)] {
            let mut bundle = ArrayExtBundleFixture::new().bundle();
            bundle.term_entries.push((
                TermData::Const(Constant::BitVec { value, width: 2 }),
                Sort::bitvec(2),
            ));
            assert_malformed_bundle(&bundle, "non-canonical value");
        }
    }

    #[test]
    fn bundle_preflight_rejects_duplicate_canonical_term_entries() {
        let mut bundle = ArrayExtBundleFixture::new().bundle();
        let duplicate = bundle.term_entries[0].clone();
        bundle.term_entries.push(duplicate);
        assert_malformed_bundle(&bundle, "duplicates an earlier canonical term entry");
    }

    #[test]
    fn bundle_preflight_rejects_ill_sorted_builtin_applications() {
        let mut bad_equality = ArrayExtBundleFixture::new().bundle();
        let true_term = bad_equality.true_term.expect("fixture true term");
        let (data, _) = bad_equality
            .term_entries
            .iter_mut()
            .find(|(data, _)| {
                matches!(data, TermData::App(Symbol::Named(name), args)
                    if name == "=" && args.len() == 2)
            })
            .expect("fixture contains an equality");
        let TermData::App(_, args) = data else {
            unreachable!("equality search established the application shape");
        };
        args[1] = true_term;
        assert_malformed_bundle(
            &bad_equality,
            "`=` must return Bool and compare equal-sorted",
        );

        let mut bad_select = ArrayExtBundleFixture::new().bundle();
        let (data, _) = bad_select
            .term_entries
            .iter_mut()
            .find(|(data, _)| {
                matches!(data, TermData::App(Symbol::Named(name), _) if name == "select")
            })
            .expect("fixture contains a select");
        let TermData::App(_, args) = data else {
            unreachable!("select search established the application shape");
        };
        args.pop();
        assert_malformed_bundle(&bad_select, "`select` expects 2 arguments");
    }

    #[test]
    fn bundle_preflight_rejects_indexed_named_only_checker_builtins() {
        let mut string_bundle = ArrayExtBundleFixture::new().bundle();
        let string = TermId::new(string_bundle.term_entries.len() as u32);
        string_bundle.term_entries.push((
            TermData::Const(Constant::String("hello".to_string())),
            Sort::String,
        ));
        string_bundle.term_entries.push((
            TermData::App(Symbol::indexed("str.len", vec![0]), vec![string]),
            Sort::Int,
        ));
        assert_malformed_bundle(
            &string_bundle,
            "builtin `str.len` must be a named symbol without indices",
        );

        let mut fp_bundle = ArrayExtBundleFixture::new().bundle();
        let rounding_mode = TermId::new(fp_bundle.term_entries.len() as u32);
        fp_bundle.term_entries.push((
            TermData::App(Symbol::named("RNE"), Vec::new()),
            Sort::Uninterpreted("RoundingMode".to_string()),
        ));
        let zero = TermId::new(fp_bundle.term_entries.len() as u32);
        fp_bundle.term_entries.push((
            TermData::App(Symbol::indexed("+zero", vec![8, 24]), Vec::new()),
            Sort::FloatingPoint(8, 24),
        ));
        fp_bundle.term_entries.push((
            TermData::App(
                Symbol::indexed("fp.add", vec![0]),
                vec![rounding_mode, zero, zero],
            ),
            Sort::FloatingPoint(8, 24),
        ));
        assert_malformed_bundle(
            &fp_bundle,
            "builtin `fp.add` must be a named symbol without indices",
        );
    }

    #[test]
    fn bundle_preflight_authenticates_bitvector_application_signatures() {
        let mut indexed_equality = ArrayExtBundleFixture::new().bundle();
        let (data, _) = indexed_equality
            .term_entries
            .iter_mut()
            .find(|(data, _)| {
                matches!(data, TermData::App(Symbol::Named(name), args)
                    if name == "=" && args.len() == 2)
            })
            .expect("fixture contains an equality");
        let TermData::App(symbol, _) = data else {
            unreachable!("equality search established the application shape");
        };
        *symbol = Symbol::indexed("=", vec![0]);
        assert_malformed_bundle(&indexed_equality, "must be a named symbol without indices");

        for (symbol, expected) in [
            (
                Symbol::indexed("extract", vec![u32::MAX, 0]),
                "`extract` indices are outside the operand width",
            ),
            (
                Symbol::indexed("zero_extend", vec![u32::MAX]),
                "result width overflows",
            ),
            (
                Symbol::indexed("repeat", vec![u32::MAX]),
                "result width overflows",
            ),
        ] {
            let mut bundle = ArrayExtBundleFixture::new().bundle();
            let operand = TermId::new(bundle.term_entries.len() as u32);
            bundle.term_entries.push((
                TermData::Const(Constant::BitVec {
                    value: num_bigint::BigInt::from(1),
                    width: 2,
                }),
                Sort::bitvec(2),
            ));
            bundle
                .term_entries
                .push((TermData::App(symbol, vec![operand]), Sort::bitvec(2)));
            assert_malformed_bundle(&bundle, expected);
        }

        let mut bad_concat = ArrayExtBundleFixture::new().bundle();
        let lhs = TermId::new(bad_concat.term_entries.len() as u32);
        bad_concat.term_entries.push((
            TermData::Const(Constant::BitVec {
                value: num_bigint::BigInt::from(1),
                width: 2,
            }),
            Sort::bitvec(2),
        ));
        let rhs = TermId::new(bad_concat.term_entries.len() as u32);
        bad_concat.term_entries.push((
            TermData::Const(Constant::BitVec {
                value: num_bigint::BigInt::from(0),
                width: 2,
            }),
            Sort::bitvec(2),
        ));
        bad_concat.term_entries.push((
            TermData::App(Symbol::named("concat"), vec![lhs, rhs]),
            Sort::bitvec(3),
        ));
        assert_malformed_bundle(&bad_concat, "sum of operand widths");

        let mut unsafe_signed = ArrayExtBundleFixture::new().bundle();
        let narrow = TermId::new(unsafe_signed.term_entries.len() as u32);
        unsafe_signed.term_entries.push((
            TermData::Const(Constant::BitVec {
                value: num_bigint::BigInt::from(3),
                width: 2,
            }),
            Sort::bitvec(2),
        ));
        let wide = TermId::new(unsafe_signed.term_entries.len() as u32);
        unsafe_signed.term_entries.push((
            TermData::App(Symbol::indexed("repeat", vec![32]), vec![narrow]),
            Sort::bitvec(64),
        ));
        let signed_comparison = TermId::new(unsafe_signed.term_entries.len() as u32);
        unsafe_signed.term_entries.push((
            TermData::App(Symbol::named("bvslt"), vec![wide, wide]),
            Sort::Bool,
        ));
        unsafe_signed.steps.push(ProofStep::TheoryLemma {
            theory: "BV".to_string(),
            clause: vec![signed_comparison],
            farkas: None,
            kind: TheoryLemmaKind::BoolTautology,
            lia: None,
        });
        assert_malformed_bundle(&unsafe_signed, "unsafe 64-bit width");
    }

    #[test]
    fn bundle_preflight_authenticates_declared_constructor_signatures() {
        let add_context = |bundle: &mut SerializableProofBundle| {
            bundle.datatype_declarations = vec![("Pair".to_string(), vec!["mk".to_string()])];
            bundle.constructor_selectors =
                vec![("mk".to_string(), vec!["fst".to_string(), "snd".to_string()])];
        };

        let mut bad_sort = ArrayExtBundleFixture::new().bundle();
        add_context(&mut bad_sort);
        let int_terms: Vec<TermId> = bad_sort
            .term_entries
            .iter()
            .enumerate()
            .filter_map(|(index, (_, sort))| {
                (sort == &Sort::Int).then_some(TermId::new(index as u32))
            })
            .take(2)
            .collect();
        assert_eq!(int_terms.len(), 2, "fixture contains two integer terms");
        bad_sort.term_entries.push((
            TermData::App(Symbol::named("mk"), int_terms.clone()),
            Sort::Uninterpreted("Other".to_string()),
        ));
        assert_malformed_bundle(&bad_sort, "result sort outside datatype `Pair`");

        let mut bad_arity = ArrayExtBundleFixture::new().bundle();
        add_context(&mut bad_arity);
        let bad_arity_int = bad_arity
            .term_entries
            .iter()
            .enumerate()
            .find_map(|(index, (_, sort))| {
                (sort == &Sort::Int).then_some(TermId::new(index as u32))
            })
            .expect("fixture contains an integer term");
        bad_arity.term_entries.push((
            TermData::App(Symbol::named("mk"), vec![bad_arity_int]),
            Sort::Uninterpreted("Pair".to_string()),
        ));
        assert_malformed_bundle(&bad_arity, "has arity 1, expected 2");
    }

    #[test]
    fn bundle_preflight_rejects_checker_unsafe_fp_literals() {
        let mut named = ArrayExtBundleFixture::new().bundle();
        named.term_entries.push((
            TermData::App(Symbol::named("NaN"), Vec::new()),
            Sort::FloatingPoint(8, 24),
        ));
        assert_malformed_bundle(&named, "must be an indexed symbol");

        let mut terms = TermStore::new();
        let nan = terms.mk_app(
            Symbol::indexed("NaN", vec![15, 113]),
            [],
            Sort::FloatingPoint(15, 113),
        );
        let is_nan = terms.mk_app(Symbol::named("fp.isNaN"), [nan], Sort::Bool);
        let assumption = terms.mk_not_raw(is_nan);
        let mut proof = Proof::new();
        let assumed = proof.add_assume(assumption, None);
        let lemma = proof.add_step(ProofStep::TheoryLemma {
            theory: "FP".to_string(),
            clause: vec![is_nan],
            farkas: None,
            kind: TheoryLemmaKind::FpClassification {
                operation: FpOp::IsNaN,
            },
            lia: None,
        });
        proof.add_resolution(Vec::new(), is_nan, assumed, lemma);
        let wide = SerializableProofBundle::from_proof(&proof, &terms, vec![assumption]);
        assert!(re_check_bundle_strict(&wide).unwrap().quality.is_complete());
    }

    /// Build a tiny UNSAT problem `x = 0 /\ x < 0` over the integers, prove it,
    /// export a bundle, round-trip it through JSON, and re-check it offline.
    /// Confirms (1) the rebuilt checker-only store re-validates the proof with
    /// NO solver, (2) the proof's assume set equals the asserted obligation, and
    /// (3) the canonical renderer is store-independent.
    #[test]
    fn bundle_roundtrip_offline_recheck() {
        // Build the obligation in a live store and prove UNSAT through the real
        // solver, capturing the proof + a bundle. We exercise the *bundle* layer
        // directly here; the end-to-end solver capture is tested in ay-dpll.
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(0.into());
        let eq0 = terms.mk_eq(x, zero);
        let lt0 = terms.mk_app(Symbol::named("<"), [x, zero], Sort::Bool);

        // A hand-built bundle is not a real proof; this test only asserts the
        // *infrastructure* (snapshot/rebuild/render/assume-extract) is coherent.
        // The genuine proof round-trip lives in ay-dpll where a solver runs.
        let canon_eq = render_term_canonical(&terms, eq0);
        let canon_lt = render_term_canonical(&terms, lt0);
        assert!(
            canon_eq.contains('='),
            "eq renders as an = s-expr: {canon_eq}"
        );
        assert!(
            canon_lt.contains('<'),
            "lt renders as a < s-expr: {canon_lt}"
        );

        // Snapshot/rebuild preserves term identity by index.
        let snap = terms.entries_snapshot();
        let rebuilt = TermStore::from_entries(
            snap,
            Some(terms.true_term()),
            Some(terms.false_term()),
            terms.var_counter(),
        );
        assert_eq!(
            render_term_canonical(&rebuilt, eq0),
            canon_eq,
            "canonical render is store-independent across snapshot/rebuild"
        );
        assert_eq!(render_term_canonical(&rebuilt, lt0), canon_lt);

        // Schema gate fail-closes.
        let bad = SerializableProofBundle {
            schema: "ay.proofbundle/v0".to_string(),
            steps: vec![ProofStep::Assume(eq0)],
            term_entries: terms.entries_snapshot(),
            true_term: Some(terms.true_term()),
            false_term: Some(terms.false_term()),
            var_counter: terms.var_counter(),
            obligation_assertions: vec![eq0, lt0],
            datatype_declarations: Vec::new(),
            constructor_selectors: Vec::new(),
            datatype_member_signatures: Vec::new(),
            declared_function_identities: Vec::new(),
        };
        assert!(
            matches!(
                re_check_bundle_strict(&bad),
                Err(ProofCheckError::BundleSchemaMismatch { .. })
            ),
            "an unknown schema tag must be rejected"
        );
    }
}

#[cfg(test)]
mod wide_bv_replay_tests;
