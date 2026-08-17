// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Strict-mode semantic validation for `TheoryLemmaKind::DatatypeDistinct`
//! proof steps.
//!
//! Context (#8419 / trust_count→0): the datatype solver refutes
//! `(= C1(..) C2(..))` for two DISTINCT constructors of the same datatype (a
//! value cannot simultaneously be two different constructors). Previously this
//! conflict was emitted as a `Generic`/`trust` lemma — an unverified fallback.
//!
//! This module validates the canonical datatype-distinctness clause against the
//! datatype constructor registry passed in from the executor (the proof checker
//! does not otherwise see `declare-datatype` declarations — runtime datatype
//! terms carry `Sort::Uninterpreted`). Two shapes are accepted:
//!
//! - UNIT disjointness — `(cl (not (= C1(..) C2(..))))`: the disequality of two
//!   distinct-constructor applications of the same datatype.
//! - BINARY exclusion — `(cl (not (= t C1(..))) (not (= t C2(..))))`: a value
//!   `t` cannot equal two distinct constructors.
//!
//! Both are tautologies of datatype theory exactly when `C1` and `C2` are
//! registered constructors of the SAME datatype with DIFFERENT names. The
//! distinctness principle itself is machine-checked in
//! `verification/lean/AySoundness/Datatype.lean`. Without the registry (no
//! declarations supplied), strict mode fails closed — it never assumes
//! distinctness by shape alone, which would be unsound.

use std::collections::{BTreeMap, BTreeSet};

use ay_core::kani_compat::det_hash_set_with_capacity;
use ay_core::{ProofId, Sort, Symbol, TermData, TermId, TermStore};
use serde::{Deserialize, Serialize};

use super::ProofCheckError;

/// Datatype declarations supplied by the executor: `(datatype_name, [constructor_name, ..])`.
pub(crate) type DatatypeDecls<'a> = &'a [(String, Vec<String>)];

/// Exact core signature of one datatype constructor, selector, or tester.
///
/// The identity is the sticky, collision-free symbol carried by [`TermData`],
/// not a source-level spelling.  Strict proof checking uses this table to
/// authenticate both sides of every datatype-member application: declaration
/// registries that contain names and arities alone are not sufficient because
/// a caller can construct an [`TermData::App`] with arbitrary argument and
/// result sorts.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DatatypeMemberSignature {
    /// Exact internal constructor, selector, or tester identity.
    pub identity: String,
    /// Exact argument sorts, in declaration order.
    pub argument_sorts: Vec<Sort>,
    /// Exact result sort.
    pub result_sort: Sort,
    /// Exact bound term for a nullary constructor. `None` for every selector,
    /// tester, and non-nullary constructor.
    ///
    /// A name-and-sort-equivalent [`TermData::Var`] is not constructor
    /// authority: source shadowing may create another variable with the same
    /// spelling. The live frontend records the one exact bound constructor
    /// term and schema-v3 bundles preserve its positional [`TermId`].
    pub nullary_term: Option<TermId>,
}
fn invalid_signature_context(reason: impl Into<String>) -> ProofCheckError {
    ProofCheckError::InvalidDatatypeSignatureContext {
        reason: reason.into(),
    }
}

type DatatypeSignatureMap<'a> = BTreeMap<&'a str, &'a DatatypeMemberSignature>;

/// Validate one complete typed datatype declaration context and every use of
/// its member identities in the term store.
///
/// This is deliberately a whole-store preflight.  Once an identity is claimed
/// as a datatype member, no malformed occurrence of that identity may coexist
/// in the authenticated store, even when a particular proof step happens not
/// to visit it.  The declaration/name registries and typed table are required
/// to be exact, complete, and mutually consistent.
pub(crate) fn validate_datatype_signature_context(
    terms: &TermStore,
    dt_decls: Option<DatatypeDecls<'_>>,
    ctor_selectors: Option<SelectorDecls<'_>>,
    member_signatures: &[DatatypeMemberSignature],
) -> Result<(), ProofCheckError> {
    let declarations = dt_decls.unwrap_or(&[]);
    let selectors = ctor_selectors.unwrap_or(&[]);
    let signatures = collect_member_signatures(member_signatures)?;
    let mut expected_members = BTreeSet::new();
    let constructor_carriers =
        collect_constructor_declarations(declarations, &mut expected_members)?;
    let selector_lists =
        collect_selector_declarations(selectors, &constructor_carriers, &mut expected_members)?;

    validate_declared_member_signatures(
        terms,
        &signatures,
        &constructor_carriers,
        &selector_lists,
    )?;
    validate_exact_member_set(&signatures, &expected_members)?;
    validate_datatype_member_terms(terms, &signatures)
}

fn collect_member_signatures(
    member_signatures: &[DatatypeMemberSignature],
) -> Result<DatatypeSignatureMap<'_>, ProofCheckError> {
    let mut signatures = BTreeMap::new();
    for signature in member_signatures {
        if signature.identity.is_empty() {
            return Err(invalid_signature_context(
                "datatype member signature has an empty identity",
            ));
        }
        if signatures
            .insert(signature.identity.as_str(), signature)
            .is_some()
        {
            return Err(invalid_signature_context(format!(
                "datatype member signature {:?} is duplicated",
                signature.identity
            )));
        }
    }
    Ok(signatures)
}

fn collect_constructor_declarations<'a>(
    declarations: DatatypeDecls<'a>,
    expected_members: &mut BTreeSet<String>,
) -> Result<BTreeMap<&'a str, &'a str>, ProofCheckError> {
    let mut datatype_names = BTreeSet::new();
    let mut constructor_carriers = BTreeMap::new();
    for (datatype, constructors) in declarations {
        if datatype.is_empty() || !datatype_names.insert(datatype.as_str()) {
            return Err(invalid_signature_context(format!(
                "datatype declaration name {datatype:?} is empty or duplicated"
            )));
        }
        if constructors.is_empty() {
            return Err(invalid_signature_context(format!(
                "datatype {datatype:?} has no constructors"
            )));
        }
        for constructor in constructors {
            if constructor.is_empty()
                || constructor_carriers
                    .insert(constructor.as_str(), datatype.as_str())
                    .is_some()
            {
                return Err(invalid_signature_context(format!(
                    "constructor declaration name {constructor:?} is empty or duplicated"
                )));
            }
            if !expected_members.insert(constructor.clone()) {
                return Err(invalid_signature_context(format!(
                    "datatype member identity {constructor:?} is ambiguous"
                )));
            }
            let tester = format!("is-{constructor}");
            if !expected_members.insert(tester.clone()) {
                return Err(invalid_signature_context(format!(
                    "derived tester identity {tester:?} is ambiguous"
                )));
            }
        }
    }
    Ok(constructor_carriers)
}

fn collect_selector_declarations<'a>(
    selectors: SelectorDecls<'a>,
    constructor_carriers: &BTreeMap<&str, &str>,
    expected_members: &mut BTreeSet<String>,
) -> Result<BTreeMap<&'a str, &'a [String]>, ProofCheckError> {
    let mut selector_lists = BTreeMap::new();
    for (constructor, fields) in selectors {
        if !constructor_carriers.contains_key(constructor.as_str()) {
            return Err(invalid_signature_context(format!(
                "selector declaration references unknown constructor {constructor:?}"
            )));
        }
        if selector_lists
            .insert(constructor.as_str(), fields.as_slice())
            .is_some()
        {
            return Err(invalid_signature_context(format!(
                "selector declaration for constructor {constructor:?} is duplicated"
            )));
        }
        for selector in fields {
            if selector.is_empty() || !expected_members.insert(selector.clone()) {
                return Err(invalid_signature_context(format!(
                    "selector identity {selector:?} is empty or ambiguous"
                )));
            }
        }
    }
    Ok(selector_lists)
}

fn validate_declared_member_signatures(
    terms: &TermStore,
    signatures: &DatatypeSignatureMap<'_>,
    constructor_carriers: &BTreeMap<&str, &str>,
    selector_lists: &BTreeMap<&str, &[String]>,
) -> Result<(), ProofCheckError> {
    for (&constructor, &datatype) in constructor_carriers {
        let Some(&fields) = selector_lists.get(constructor) else {
            return Err(invalid_signature_context(format!(
                "constructor {constructor:?} is missing its complete selector declaration"
            )));
        };
        let constructor_signature =
            validate_constructor_signature(terms, signatures, constructor, datatype, fields)?;
        validate_tester_signature(signatures, constructor, constructor_signature)?;
        validate_selector_signatures(signatures, fields, constructor_signature)?;
    }
    Ok(())
}

fn validate_constructor_signature<'a>(
    terms: &TermStore,
    signatures: &DatatypeSignatureMap<'a>,
    constructor: &str,
    datatype: &str,
    fields: &[String],
) -> Result<&'a DatatypeMemberSignature, ProofCheckError> {
    let Some(signature) = signatures.get(constructor).copied() else {
        return Err(invalid_signature_context(format!(
            "constructor {constructor:?} is missing its exact typed signature"
        )));
    };
    if !sort_matches_datatype(&signature.result_sort, datatype) {
        return Err(invalid_signature_context(format!(
            "constructor {constructor:?} has result sort {}, expected datatype {datatype:?}",
            signature.result_sort
        )));
    }
    if signature.argument_sorts.len() != fields.len() {
        return Err(invalid_signature_context(format!(
            "constructor {constructor:?} has {} typed arguments but {} declared selectors",
            signature.argument_sorts.len(),
            fields.len()
        )));
    }
    match (signature.argument_sorts.is_empty(), signature.nullary_term) {
        (true, Some(term)) => {
            if term.index() >= terms.len() {
                return Err(invalid_signature_context(format!(
                    "nullary constructor {constructor:?} binds missing term {term}"
                )));
            }
            if !matches!(
                terms.get(term),
                TermData::Var(identity, _) if identity == constructor
            ) || terms.sort(term) != &signature.result_sort
            {
                return Err(invalid_signature_context(format!(
                    "nullary constructor {constructor:?} does not bind its exact same-name variable of the declared result sort"
                )));
            }
        }
        (true, None) => {
            return Err(invalid_signature_context(format!(
                "nullary constructor {constructor:?} is missing its exact bound term"
            )));
        }
        (false, Some(term)) => {
            return Err(invalid_signature_context(format!(
                "non-nullary constructor {constructor:?} unexpectedly binds nullary term {term}"
            )));
        }
        (false, None) => {}
    }
    Ok(signature)
}

fn validate_tester_signature(
    signatures: &DatatypeSignatureMap<'_>,
    constructor: &str,
    constructor_signature: &DatatypeMemberSignature,
) -> Result<(), ProofCheckError> {
    let tester = format!("is-{constructor}");
    let Some(signature) = signatures.get(tester.as_str()).copied() else {
        return Err(invalid_signature_context(format!(
            "tester {tester:?} is missing its exact typed signature"
        )));
    };
    if signature.argument_sorts.as_slice()
        != std::slice::from_ref(&constructor_signature.result_sort)
        || signature.result_sort != Sort::Bool
    {
        return Err(invalid_signature_context(format!(
            "tester {tester:?} does not have the exact signature ({}) -> Bool",
            constructor_signature.result_sort
        )));
    }
    if signature.nullary_term.is_some() {
        return Err(invalid_signature_context(format!(
            "tester {tester:?} unexpectedly carries a nullary constructor binding"
        )));
    }
    Ok(())
}

fn validate_selector_signatures(
    signatures: &DatatypeSignatureMap<'_>,
    fields: &[String],
    constructor_signature: &DatatypeMemberSignature,
) -> Result<(), ProofCheckError> {
    for (index, selector) in fields.iter().enumerate() {
        let Some(signature) = signatures.get(selector.as_str()).copied() else {
            return Err(invalid_signature_context(format!(
                "selector {selector:?} is missing its exact typed signature"
            )));
        };
        if signature.argument_sorts.as_slice()
            != std::slice::from_ref(&constructor_signature.result_sort)
            || signature.result_sort != constructor_signature.argument_sorts[index]
        {
            return Err(invalid_signature_context(format!(
                "selector {selector:?} does not have the exact declared field-{index} signature"
            )));
        }
        if signature.nullary_term.is_some() {
            return Err(invalid_signature_context(format!(
                "selector {selector:?} unexpectedly carries a nullary constructor binding"
            )));
        }
    }
    Ok(())
}

fn validate_exact_member_set(
    signatures: &DatatypeSignatureMap<'_>,
    expected_members: &BTreeSet<String>,
) -> Result<(), ProofCheckError> {
    let actual_members: BTreeSet<&str> = signatures.keys().copied().collect();
    let expected_member_refs: BTreeSet<&str> =
        expected_members.iter().map(String::as_str).collect();
    if actual_members != expected_member_refs {
        let missing: Vec<_> = expected_member_refs
            .difference(&actual_members)
            .copied()
            .collect();
        let extra: Vec<_> = actual_members
            .difference(&expected_member_refs)
            .copied()
            .collect();
        return Err(invalid_signature_context(format!(
            "typed datatype member table is not exact (missing {missing:?}, extra {extra:?})"
        )));
    }
    Ok(())
}

fn validate_datatype_member_terms(
    terms: &TermStore,
    signatures: &DatatypeSignatureMap<'_>,
) -> Result<(), ProofCheckError> {
    for node_index in 0..terms.len() {
        let raw_id = u32::try_from(node_index).map_err(|_| {
            invalid_signature_context("term-store index does not fit the TermId representation")
        })?;
        let term = TermId::new(raw_id);
        match terms.get(term) {
            TermData::Var(identity, _) => {
                let Some(signature) = signatures.get(identity.as_str()).copied() else {
                    continue;
                };
                validate_member_variable(terms, term, identity, signature)?;
            }
            TermData::App(Symbol::Named(identity), arguments) => {
                let Some(signature) = signatures.get(identity.as_str()).copied() else {
                    continue;
                };
                validate_member_application(terms, term, identity, arguments, signature)?;
            }
            TermData::App(Symbol::Indexed(identity, _), _)
                if signatures.contains_key(identity.as_str()) =>
            {
                return Err(invalid_signature_context(format!(
                    "datatype member term {term} `{identity}` uses an indexed symbol"
                )));
            }
            _ => {}
        }
    }

    Ok(())
}

fn validate_member_variable(
    terms: &TermStore,
    term: TermId,
    identity: &str,
    signature: &DatatypeMemberSignature,
) -> Result<(), ProofCheckError> {
    if signature.nullary_term != Some(term) {
        return Err(invalid_signature_context(format!(
            "datatype member variable {term} `{identity}` is not its declaration's exact nullary constructor binding"
        )));
    }
    if terms.sort(term) != &signature.result_sort {
        return Err(invalid_signature_context(format!(
            "datatype member term {term} `{identity}` has result sort {}, expected {}",
            terms.sort(term),
            signature.result_sort
        )));
    }
    Ok(())
}

/// Validate one `App(Named(identity), arguments)` occurrence of a datatype
/// member.
///
/// A NULLARY constructor has two authenticated core representations, and both
/// reach here:
///
/// - `declare-datatype` binds it as an exact [`TermData::Var`], recorded as
///   [`DatatypeMemberSignature::nullary_term`] (see
///   `elaborate::datatypes::register_elaborated_datatype_constructors`).
/// - The embedder path `try_declare_fun(C, &[], dt)` + `try_apply(&C, &[])`,
///   and the SMT-LIB `(C)` spelling, instead build a ZERO-ARGUMENT
///   `App(Named(C), [])`.
///
/// The datatype solver treats the two identically: `euf::dt` classifies any
/// `App(Symbol::Named(name), args)` whose `name` `is_constructor` as a
/// constructor term, arity 0 included. So the application form is not a
/// malformed occurrence — declining it rejected proofs of obligations the
/// solver had correctly refuted.
///
/// Authority for an application comes from the exact member identity, which is
/// already the rule for every non-nullary constructor, selector, and tester
/// application below. Only the [`TermData::Var`] form needs the extra TermId
/// pin (see [`validate_member_variable`]), because a shadowing source variable
/// can share a constructor's spelling while an application of the exact
/// internal identity cannot.
///
/// A nullary constructor applied to a NON-EMPTY argument list is still
/// rejected: its `argument_sorts` are empty, so the arity check below fails.
fn validate_member_application(
    terms: &TermStore,
    term: TermId,
    identity: &str,
    arguments: &[TermId],
    signature: &DatatypeMemberSignature,
) -> Result<(), ProofCheckError> {
    if arguments.len() != signature.argument_sorts.len() {
        return Err(invalid_signature_context(format!(
            "datatype member term {term} `{identity}` has {} arguments, expected {}",
            arguments.len(),
            signature.argument_sorts.len()
        )));
    }
    for (index, (&argument, expected_sort)) in arguments
        .iter()
        .zip(signature.argument_sorts.iter())
        .enumerate()
    {
        if terms.sort(argument) != expected_sort {
            return Err(invalid_signature_context(format!(
                "datatype member term {term} `{identity}` argument {index} has sort {}, expected {expected_sort}",
                terms.sort(argument)
            )));
        }
    }
    if terms.sort(term) != &signature.result_sort {
        return Err(invalid_signature_context(format!(
            "datatype member term {term} `{identity}` has result sort {}, expected {}",
            terms.sort(term),
            signature.result_sort
        )));
    }
    Ok(())
}

/// Recognize whether `clause` is a valid datatype constructor-distinctness
/// lemma under the given declarations — i.e. whether
/// [`validate_datatype_distinct`] would accept it.
///
/// The proof classifier (`ay-dpll`) calls this to upgrade `Generic` lemmas the
/// live conflict classifier could not label (it lacks the datatype registry)
/// into the strict-checkable `DatatypeDistinct` kind. Because it shares the
/// exact validator logic, the classifier and checker cannot drift: a clause is
/// upgraded only if the strict checker will independently re-validate it.
#[must_use]
pub fn recognize_datatype_distinct(
    terms: &TermStore,
    clause: &[TermId],
    dt_decls: &[(String, Vec<String>)],
) -> bool {
    // ProofId is irrelevant to acceptance; only used in error messages.
    validate_datatype_distinct(terms, ProofId(0), clause, dt_decls).is_ok()
}

/// Validate a `DatatypeDistinct` lemma in strict mode against the datatype
/// declarations.
///
/// Returns `Ok(())` only when the clause is one of the accepted distinctness
/// schemas AND every constructor it names is a registered constructor of the
/// same datatype with the two heads distinct. Fails closed otherwise.
pub(crate) fn validate_datatype_distinct(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    dt_decls: DatatypeDecls<'_>,
) -> Result<(), ProofCheckError> {
    let invalid = |reason: String| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason,
    };

    if clause.is_empty() {
        return Err(invalid(
            "datatype distinctness clause must be non-empty".to_string(),
        ));
    }
    if clause
        .iter()
        .any(|&literal| terms.sort(literal) != &Sort::Bool)
    {
        return Err(invalid(
            "datatype distinctness clause literals must have sort Bool".to_string(),
        ));
    }

    let literals = flatten_clause_literals(terms, clause);

    match literals.len() {
        // UNIT disjointness: (not (= C1(..) C2(..)))
        1 => {
            let (lhs, rhs) = negated_equality_sides(terms, literals[0]).ok_or_else(|| {
                invalid(
                    "datatype distinctness unit clause must be a negated equality \
                     (not (= C1 C2))"
                        .to_string(),
                )
            })?;
            check_distinct_constructors(terms, dt_decls, lhs, rhs, step_id)
        }
        // BINARY exclusion: (not (= t C1)) (not (= t C2))
        2 => {
            let (a1, b1) = negated_equality_sides(terms, literals[0]).ok_or_else(|| {
                invalid("datatype distinctness literal 0 must be a negated equality".to_string())
            })?;
            let (a2, b2) = negated_equality_sides(terms, literals[1]).ok_or_else(|| {
                invalid("datatype distinctness literal 1 must be a negated equality".to_string())
            })?;
            // Identify the shared term `t` and the two constructor operands.
            let (c1, c2) = shared_term_constructors(a1, b1, a2, b2).ok_or_else(|| {
                invalid(
                    "datatype distinctness binary clause must share a common term \
                     across both disequalities"
                        .to_string(),
                )
            })?;
            check_distinct_constructors(terms, dt_decls, c1, c2, step_id)
        }
        n => Err(invalid(format!(
            "datatype distinctness clause has {n} literals; expected 1 (unit \
             disjointness) or 2 (binary exclusion)"
        ))),
    }
}

/// Recognize a datatype tester evaluation theorem under the supplied
/// datatype declarations. See [`validate_datatype_tester_eval`].
#[must_use]
pub fn recognize_datatype_tester_eval(
    terms: &TermStore,
    clause: &[TermId],
    dt_decls: &[(String, Vec<String>)],
) -> bool {
    validate_datatype_tester_eval(terms, ProofId(0), clause, dt_decls, None, true).is_ok()
}

/// Declaration-complete recognizer used by the executor for tester axioms that
/// also depend on constructor arity (the nullary-sibling exhaustiveness form).
#[must_use]
pub fn recognize_datatype_tester_eval_with_selectors(
    terms: &TermStore,
    clause: &[TermId],
    dt_decls: &[(String, Vec<String>)],
    ctor_selectors: &[(String, Vec<String>)],
) -> bool {
    validate_datatype_tester_eval(
        terms,
        ProofId(0),
        clause,
        dt_decls,
        Some(ctor_selectors),
        true,
    )
    .is_ok()
}

/// Validate an exact datatype tester axiom.
///
/// A matching tester is true on its constructor application,
/// `(is-C (C ...))`; a tester for another constructor of the same datatype is
/// false, `(not (is-C (D ...)))`.  The same declaration-backed lane also
/// accepts the two symbolic tester schemas needed to discharge authored roots
/// without pretending the tested value is a constructor application:
///
/// * exclusion: `¬is-C(t) ∨ ¬is-D(t)` for distinct constructors of one datatype;
/// * exhaustiveness: every declared tester on the same `t`, or the equivalent
///   two-constructor form `is-C(t) ∨ t = D` when `D` is nullary.
///
/// Constructor and tester identities are authenticated by the declaration
/// registry, so an arbitrary unary Boolean function whose name merely resembles
/// a tester cannot enter this lane.
pub(crate) fn validate_datatype_tester_eval(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    dt_decls: DatatypeDecls<'_>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
    typed_member_context: bool,
) -> Result<(), ProofCheckError> {
    let invalid = |reason: String| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason,
    };
    let literals = flatten_clause_literals(terms, clause);
    if literals.is_empty()
        || literals
            .iter()
            .any(|&literal| terms.sort(literal) != &Sort::Bool)
    {
        return Err(invalid(
            "datatype tester axiom must be a non-empty Bool clause".to_string(),
        ));
    }

    // Concrete unit evaluation: `is-C(C(..))` / `¬is-C(D(..))`.
    if let [literal] = literals.as_slice() {
        if !typed_member_context {
            return Err(invalid(
                "concrete datatype tester evaluation requires exact typed member signatures"
                    .to_string(),
            ));
        }
        let (tester, positive) = match terms.get(*literal) {
            TermData::Not(inner) => (*inner, false),
            _ => (*literal, true),
        };
        let (tested_ctor, tested_value) = tester_application(terms, tester).ok_or_else(|| {
            invalid("datatype tester-evaluation literal is not a tester application".to_string())
        })?;
        let tested_datatype = constructor_datatype(dt_decls, tested_ctor).ok_or_else(|| {
            invalid("datatype tester names an unregistered constructor".to_string())
        })?;
        let (actual_ctor, actual_datatype) = constructor_head(terms, dt_decls, tested_value)
            .ok_or_else(|| {
                invalid(
                    "datatype tester argument is not an application of a registered constructor"
                        .to_string(),
                )
            })?;
        if tested_datatype != actual_datatype {
            return Err(invalid(format!(
                "datatype tester and constructor belong to different datatypes \
                 ({tested_datatype} vs {actual_datatype})"
            )));
        }
        let expected_positive = tested_ctor == actual_ctor;
        if positive != expected_positive {
            return Err(invalid(format!(
                "datatype tester polarity is wrong for is-{tested_ctor}({actual_ctor}(...))"
            )));
        }
        return Ok(());
    }

    // Symbolic mutual exclusion: `¬is-C(t) ∨ ¬is-D(t)`.
    if let [left, right] = literals.as_slice() {
        if let (TermData::Not(left_tester), TermData::Not(right_tester)) =
            (terms.get(*left), terms.get(*right))
        {
            if let (Some((left_ctor, left_value)), Some((right_ctor, right_value))) = (
                tester_application(terms, *left_tester),
                tester_application(terms, *right_tester),
            ) {
                let left_dt = constructor_datatype(dt_decls, left_ctor);
                let right_dt = constructor_datatype(dt_decls, right_ctor);
                if left_value == right_value
                    && left_ctor != right_ctor
                    && left_dt.is_some()
                    && left_dt == right_dt
                    && left_dt.is_some_and(|datatype| {
                        sort_matches_datatype(terms.sort(left_value), datatype)
                    })
                {
                    return Ok(());
                }
            }
        }

        // Two-constructor exhaustiveness with a nullary sibling:
        // `is-C(t) ∨ t = D` (literal order and equality orientation arbitrary).
        for (tester_literal, equality_literal) in [(*left, *right), (*right, *left)] {
            let Some((tested_ctor, tested_value)) = tester_application(terms, tester_literal)
            else {
                continue;
            };
            let Some((eq_lhs, eq_rhs)) = equality_sides(terms, equality_literal) else {
                continue;
            };
            for (value_side, ctor_side) in [(eq_lhs, eq_rhs), (eq_rhs, eq_lhs)] {
                if value_side != tested_value || terms.sort(value_side) != terms.sort(ctor_side) {
                    continue;
                }
                let Some(selectors) = ctor_selectors else {
                    continue;
                };
                let syntactically_nullary = matches!(terms.get(ctor_side), TermData::Var(..))
                    || matches!(terms.get(ctor_side), TermData::App(_, args) if args.is_empty());
                if !syntactically_nullary {
                    continue;
                }
                let Some((sibling_ctor, sibling_dt)) = constructor_head(terms, dt_decls, ctor_side)
                else {
                    continue;
                };
                // The constructor registry by itself records names, not arity.
                // Require the independently supplied constructor→selector map
                // to contain the sibling with exactly zero fields; term shape
                // alone (`Var` / zero-arg App) is forgeable.
                if !selectors
                    .iter()
                    .any(|(constructor, fields)| constructor == &sibling_ctor && fields.is_empty())
                {
                    continue;
                }
                let Some(tested_dt) = constructor_datatype(dt_decls, tested_ctor) else {
                    continue;
                };
                let Some((_, constructors)) = dt_decls.iter().find(|(dt, _)| dt == tested_dt)
                else {
                    continue;
                };
                if sibling_dt == tested_dt
                    && sort_matches_datatype(terms.sort(tested_value), tested_dt)
                    && sibling_ctor != tested_ctor
                    && constructors.len() == 2
                    && constructors.iter().any(|ctor| ctor == tested_ctor)
                    && constructors.iter().any(|ctor| ctor == &sibling_ctor)
                {
                    return Ok(());
                }
            }
        }
    }

    // General tester exhaustiveness: exactly one positive tester for every
    // constructor of a datatype, all applied to the identical subject.
    let mut subject = None;
    let mut datatype = None;
    let mut tester_names: Vec<&str> = Vec::new();
    for &literal in &literals {
        if matches!(terms.get(literal), TermData::Not(_)) {
            return Err(invalid(
                "datatype tester exhaustiveness requires positive testers".to_string(),
            ));
        }
        let (ctor, value) = tester_application(terms, literal).ok_or_else(|| {
            invalid("datatype tester clause has a non-tester literal".to_string())
        })?;
        let dt = constructor_datatype(dt_decls, ctor).ok_or_else(|| {
            invalid("datatype tester names an unregistered constructor".to_string())
        })?;
        if subject
            .replace(value)
            .is_some_and(|previous| previous != value)
            || datatype.replace(dt).is_some_and(|previous| previous != dt)
            || tester_names.contains(&ctor)
        {
            return Err(invalid(
                "datatype tester exhaustiveness must use one common subject and distinct \
                 constructors of one datatype"
                    .to_string(),
            ));
        }
        tester_names.push(ctor);
    }
    let Some(dt) = datatype else {
        return Err(invalid(
            "datatype tester clause has no datatype".to_string(),
        ));
    };
    let Some(subject) = subject else {
        return Err(invalid("datatype tester clause has no subject".to_string()));
    };
    if !sort_matches_datatype(terms.sort(subject), dt) {
        return Err(invalid(
            "datatype tester subject sort does not match its declared datatype".to_string(),
        ));
    }
    let constructors = dt_decls
        .iter()
        .find_map(|(name, constructors)| (name == dt).then_some(constructors))
        .ok_or_else(|| invalid("datatype declaration disappeared during validation".to_string()))?;
    if tester_names.len() == constructors.len()
        && constructors
            .iter()
            .all(|ctor| tester_names.contains(&ctor.as_str()))
    {
        Ok(())
    } else {
        Err(invalid(
            "datatype tester exhaustiveness omits or adds a constructor".to_string(),
        ))
    }
}

/// Decode a named unary Boolean tester `is-<constructor>(value)`.
fn tester_application(terms: &TermStore, term: TermId) -> Option<(&str, TermId)> {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    let constructor = name.strip_prefix("is-")?;
    let [value] = args.as_slice() else {
        return None;
    };
    (terms.sort(term) == &Sort::Bool).then_some((constructor, *value))
}

/// Given two disequalities `(not (= a1 b1))` and `(not (= a2 b2))`, find the
/// shared operand `t` and return the two non-shared operands `(c1, c2)`.
fn shared_term_constructors(
    a1: TermId,
    b1: TermId,
    a2: TermId,
    b2: TermId,
) -> Option<(TermId, TermId)> {
    if a1 == a2 {
        Some((b1, b2))
    } else if a1 == b2 {
        Some((b1, a2))
    } else if b1 == a2 {
        Some((a1, b2))
    } else if b1 == b2 {
        Some((a1, a2))
    } else {
        None
    }
}

/// Verify that `lhs` and `rhs` are applications of DISTINCT constructors of the
/// SAME registered datatype.
fn check_distinct_constructors(
    terms: &TermStore,
    dt_decls: DatatypeDecls<'_>,
    lhs: TermId,
    rhs: TermId,
    step_id: ProofId,
) -> Result<(), ProofCheckError> {
    let invalid = |reason: String| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason,
    };

    if terms.sort(lhs) != terms.sort(rhs) {
        return Err(invalid(
            "datatype distinctness equality operands have different sorts".to_string(),
        ));
    }

    let (lhs_ctor, lhs_dt) = constructor_head(terms, dt_decls, lhs).ok_or_else(|| {
        invalid(
            "datatype distinctness: left side is not an application of a registered \
             datatype constructor"
                .to_string(),
        )
    })?;
    let (rhs_ctor, rhs_dt) = constructor_head(terms, dt_decls, rhs).ok_or_else(|| {
        invalid(
            "datatype distinctness: right side is not an application of a registered \
             datatype constructor"
                .to_string(),
        )
    })?;

    if lhs_dt != rhs_dt {
        return Err(invalid(format!(
            "datatype distinctness: constructors belong to different datatypes \
             ({lhs_dt} vs {rhs_dt})"
        )));
    }
    if lhs_ctor == rhs_ctor {
        return Err(invalid(format!(
            "datatype distinctness: both sides use the same constructor {lhs_ctor}; \
             a disequality of identical constructors is injectivity, not distinctness"
        )));
    }

    Ok(())
}

/// Head constructor of `term`, if it is an application (or variable) whose
/// symbol is a registered datatype constructor. Returns `(ctor_name, datatype_name)`.
fn constructor_head<'a>(
    terms: &TermStore,
    dt_decls: DatatypeDecls<'a>,
    term: TermId,
) -> Option<(String, &'a str)> {
    let name = match terms.get(term) {
        TermData::App(Symbol::Named(name), _) => name.clone(),
        TermData::Var(n, _) => n.clone(),
        _ => return None,
    };
    let dt = constructor_datatype(dt_decls, &name)?;
    if !sort_matches_datatype(terms.sort(term), dt) {
        return None;
    }
    Some((name, dt))
}

fn sort_matches_datatype(sort: &Sort, datatype: &str) -> bool {
    match sort {
        Sort::Uninterpreted(name) => name == datatype,
        Sort::Datatype(definition) => definition.name.as_str() == datatype,
        _ => false,
    }
}

/// The datatype a constructor symbol belongs to, if registered.
fn constructor_datatype<'a>(dt_decls: DatatypeDecls<'a>, ctor_name: &str) -> Option<&'a str> {
    dt_decls.iter().find_map(|(dt, ctors)| {
        if ctors.iter().any(|c| c == ctor_name) {
            Some(dt.as_str())
        } else {
            None
        }
    })
}

/// Constructor→selector registry supplied by the executor:
/// `(constructor_name, [selector_name in field order])`.
pub(crate) type SelectorDecls<'a> = &'a [(String, Vec<String>)];

/// Validate a finite-enum pigeonhole lemma.
///
/// Clause shape: the COMPLETE graph of equalities over `m` distinct terms of one
/// datatype sort whose `k` constructors are ALL NULLARY, with `m > k`:
///
/// ```text
/// (cl (= t1 t2) (= t1 t3) ... (= t_{m-1} t_m))
/// ```
///
/// Soundness: an all-nullary datatype's carrier is EXACTLY its `k` constructor
/// constants, so any `m > k` terms of that sort must contain an equal pair and
/// the disjunction holds in every model.
///
/// Everything the argument rests on is re-derived here from the declaration
/// registry — the constructor COUNT and, critically, the NULLARITY that makes the
/// carrier finite. The executor's claim is never taken on trust: a datatype with
/// any non-nullary constructor has an infinite carrier and no pigeonhole, so a
/// missing or non-empty selector entry fails closed.
pub(crate) fn validate_datatype_enum_pigeonhole(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    dt_decls: DatatypeDecls<'_>,
    ctor_selectors: Option<SelectorDecls<'_>>,
) -> Result<(), ProofCheckError> {
    let invalid = |reason: String| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason,
    };

    let literals = flatten_clause_literals(terms, clause);
    if literals.is_empty() {
        return Err(invalid(
            "enum pigeonhole clause must be non-empty".to_string(),
        ));
    }

    let mut values = det_hash_set_with_capacity(literals.len().saturating_add(1));
    let mut pairs = det_hash_set_with_capacity(literals.len());
    let mut sort_name: Option<String> = None;

    for &literal in &literals {
        let Some((lhs, rhs)) = syntactic_equality_sides(terms, literal) else {
            return Err(invalid(
                "enum pigeonhole literals must all be equalities".to_string(),
            ));
        };
        if lhs == rhs {
            return Err(invalid(
                "enum pigeonhole literals must relate DISTINCT terms".to_string(),
            ));
        }
        for value in [lhs, rhs] {
            // Each member's sort is invariant across all its incident edges.
            // Validate it only on first insertion; a complete graph repeats a
            // member O(m) times, and rescanning a long datatype name at every
            // edge made this otherwise-quadratic in the certificate size.
            if !values.insert(value) {
                continue;
            }
            let Sort::Uninterpreted(name) = terms.sort(value) else {
                return Err(invalid(
                    "enum pigeonhole applies only to a declared datatype sort".to_string(),
                ));
            };
            match &sort_name {
                None => sort_name = Some(name.clone()),
                Some(seen) if seen == name => {}
                Some(_) => {
                    return Err(invalid(
                        "enum pigeonhole literals must all share ONE datatype sort".to_string(),
                    ));
                }
            }
        }
        let pair = if lhs.0 < rhs.0 {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        };
        if !pairs.insert(pair) {
            return Err(invalid("enum pigeonhole clause repeats a pair".to_string()));
        }
    }

    let Some(sort_name) = sort_name else {
        return Err(invalid("enum pigeonhole clause has no sort".to_string()));
    };
    let Some((_, constructors)) = dt_decls.iter().find(|(dt, _)| dt == &sort_name) else {
        return Err(invalid(format!(
            "enum pigeonhole sort {sort_name} is not a declared datatype"
        )));
    };
    let k = constructors.len();
    if k == 0 {
        return Err(invalid(format!(
            "enum pigeonhole sort {sort_name} declares no constructors"
        )));
    }

    // NULLARITY is what makes the carrier finite, so it is checked, not assumed.
    let Some(selectors) = ctor_selectors else {
        return Err(invalid(
            "enum pigeonhole needs the constructor->selector registry to establish \
             that every constructor is nullary"
                .to_string(),
        ));
    };
    for ctor in constructors {
        match selectors.iter().find(|(name, _)| name == ctor) {
            Some((_, fields)) if fields.is_empty() => {}
            Some((_, _)) => {
                return Err(invalid(format!(
                    "enum pigeonhole requires an all-nullary datatype, but constructor \
                     {ctor} of {sort_name} takes fields"
                )));
            }
            None => {
                return Err(invalid(format!(
                    "constructor {ctor} of {sort_name} is absent from the selector \
                     registry, so nullarity cannot be established"
                )));
            }
        }
    }

    let m = values.len();
    if m <= k {
        return Err(invalid(format!(
            "enum pigeonhole needs more terms than constructors, got {m} terms for \
             {k} constructors of {sort_name}"
        )));
    }
    let expected = m
        .checked_mul(m.saturating_sub(1))
        .map(|pairs| pairs / 2)
        .ok_or_else(|| invalid("enum pigeonhole pair count overflowed".to_string()))?;
    if literals.len() != expected {
        return Err(invalid(format!(
            "enum pigeonhole must be the COMPLETE graph on its {m} terms: expected \
             {expected} literals, got {}",
            literals.len()
        )));
    }

    Ok(())
}

/// Recognize whether `clause` is a valid datatype selector-projection lemma
/// under the given constructor→selector registry — i.e. whether
/// [`validate_datatype_selector_project`] would accept it.
#[must_use]
pub fn recognize_datatype_selector_project(
    terms: &TermStore,
    clause: &[TermId],
    ctor_selectors: &[(String, Vec<String>)],
) -> bool {
    validate_datatype_selector_project(terms, ProofId(0), clause, ctor_selectors).is_ok()
}

/// Validate a `DatatypeSelectorProject` lemma in strict mode against the
/// constructor→selector registry.
///
/// Accepts the unit positive equality `(cl (= (sel_i (C a_0 .. a_n)) a_i))`
/// (selector on either side) exactly when `sel_i` is the registered field-`i`
/// selector of constructor `C` and `a_i` is the `i`-th argument of the
/// constructor application — the selector-projection axiom of datatype theory
/// (`fst (mk x y) = x`). The principle is machine-checked in
/// `verification/lean/AySoundness/CombinedDtSelector.lean`. Fails closed when
/// the registry does not place the selector at a field index whose argument
/// matches the other side — so a forged `(= (snd (mk x y)) x)` is rejected.
pub(crate) fn validate_datatype_selector_project(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    ctor_selectors: SelectorDecls<'_>,
) -> Result<(), ProofCheckError> {
    let invalid = |reason: String| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason,
    };

    if clause.is_empty() {
        return Err(invalid(
            "datatype selector-projection clause must be non-empty".to_string(),
        ));
    }
    if clause
        .iter()
        .any(|&literal| terms.sort(literal) != &Sort::Bool)
    {
        return Err(invalid(
            "datatype selector-projection clause literals must have sort Bool".to_string(),
        ));
    }
    let literals = flatten_clause_literals(terms, clause);
    if literals.len() != 1 {
        return Err(invalid(format!(
            "datatype selector-projection clause has {} literals; expected a unit \
             positive equality `(= (sel (C ..)) a_i)`",
            literals.len()
        )));
    }
    let (lhs, rhs) = equality_sides(terms, literals[0]).ok_or_else(|| {
        invalid("datatype selector-projection literal must be an equality".to_string())
    })?;

    // The selector application may be on either side of the equality.
    for (sel_side, value_side) in [(lhs, rhs), (rhs, lhs)] {
        let Some((ctor_name, ctor_args, sel_name)) = selector_over_constructor(terms, sel_side)
        else {
            continue;
        };
        let Some(field_idx) = selector_field_index(ctor_selectors, &ctor_name, &sel_name) else {
            continue;
        };
        // A constructor application is fully applied: its arg count must equal the
        // constructor's declared field count, and the projected field must be the
        // matching argument.
        let Some((_, selectors)) = ctor_selectors.iter().find(|(c, _)| *c == ctor_name) else {
            continue;
        };
        if ctor_args.len() == selectors.len()
            && field_idx < ctor_args.len()
            && ctor_args[field_idx] == value_side
        {
            return Ok(());
        }
    }
    Err(invalid(
        "datatype selector-projection does not match `(= (sel_i (C a_0 .. a_n)) a_i)` \
         for a registered field-i selector"
            .to_string(),
    ))
}

/// Recognize whether `clause` is a valid datatype constructor-coverage
/// (exhaustiveness) lemma under the given declarations — i.e. whether
/// [`validate_datatype_exhaustive`] would accept it.
///
/// The DT axiom recorder (`ay-dpll`) calls this to tag the eagerly injected
/// exhaustiveness disjunctions with the strict-checkable `DatatypeExhaustive`
/// kind. Because it IS the strict validator, classifier and checker cannot
/// drift: a clause is tagged only if strict mode will independently
/// re-validate it.
#[must_use]
pub fn recognize_datatype_exhaustive(
    terms: &TermStore,
    clause: &[TermId],
    dt_decls: &[(String, Vec<String>)],
) -> bool {
    validate_datatype_exhaustive(terms, ProofId(0), clause, dt_decls).is_ok()
}

/// Validate a `DatatypeExhaustive` lemma in strict mode against the datatype
/// declarations.
///
/// Accepted shape: `(cl (is-C1 t) ... (is-Ck t))` — one POSITIVE tester per
/// declared constructor of `t`'s datatype, every tester applied to the SAME
/// scrutinee `t`, with the tester set covering the declared constructor list
/// EXACTLY (no omission, no duplicate, no foreign tester). For a
/// single-constructor datatype the disjunction degenerates to the unit
/// `(cl (is-C t))` (that is what `mk_or` interns), which is accepted.
///
/// The coverage list is re-derived from the declaration registry — the clause
/// is never trusted to name "all" constructors by itself, so an exhaustiveness
/// claim over a truncated tester set fails closed. The scrutinee must NOT
/// itself be a registered constructor application: the emitter never generates
/// coverage over an explicit constructor (it is redundant there), and that
/// shape belongs to the tester-EVALUATION family with its own validator —
/// keeping the two lanes disjoint. Rejecting more is always fail-closed.
pub(crate) fn validate_datatype_exhaustive(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    dt_decls: DatatypeDecls<'_>,
) -> Result<(), ProofCheckError> {
    let invalid = |reason: String| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason,
    };

    let literals = flatten_clause_literals(terms, clause);
    if literals.is_empty() {
        return Err(invalid(
            "datatype exhaustiveness clause must be non-empty".to_string(),
        ));
    }

    let mut subject: Option<TermId> = None;
    let mut datatype: Option<&str> = None;
    let mut tester_names: Vec<&str> = Vec::new();
    for &literal in &literals {
        if matches!(terms.get(literal), TermData::Not(_)) {
            return Err(invalid(
                "datatype exhaustiveness requires POSITIVE testers only".to_string(),
            ));
        }
        let (ctor, value) = tester_application(terms, literal).ok_or_else(|| {
            invalid("datatype exhaustiveness clause has a non-tester literal".to_string())
        })?;
        let dt = constructor_datatype(dt_decls, ctor).ok_or_else(|| {
            invalid("datatype exhaustiveness tester names an unregistered constructor".to_string())
        })?;
        if subject
            .replace(value)
            .is_some_and(|previous| previous != value)
        {
            return Err(invalid(
                "datatype exhaustiveness testers must share ONE scrutinee".to_string(),
            ));
        }
        if datatype.replace(dt).is_some_and(|previous| previous != dt) {
            return Err(invalid(
                "datatype exhaustiveness testers must belong to ONE datatype".to_string(),
            ));
        }
        if tester_names.contains(&ctor) {
            return Err(invalid(
                "datatype exhaustiveness repeats a constructor tester".to_string(),
            ));
        }
        tester_names.push(ctor);
    }
    let (Some(dt), Some(subject)) = (datatype, subject) else {
        return Err(invalid(
            "datatype exhaustiveness clause has no tester".to_string(),
        ));
    };
    if !sort_matches_datatype(terms.sort(subject), dt) {
        return Err(invalid(
            "datatype exhaustiveness scrutinee sort does not match the testers' datatype"
                .to_string(),
        ));
    }
    if constructor_head(terms, dt_decls, subject).is_some() {
        return Err(invalid(
            "datatype exhaustiveness scrutinee must not itself be a constructor \
             application; that shape is tester EVALUATION"
                .to_string(),
        ));
    }
    let constructors = dt_decls
        .iter()
        .find_map(|(name, constructors)| (name == dt).then_some(constructors))
        .ok_or_else(|| invalid("datatype declaration disappeared during validation".to_string()))?;
    if tester_names.len() == constructors.len()
        && constructors
            .iter()
            .all(|ctor| tester_names.contains(&ctor.as_str()))
    {
        Ok(())
    } else {
        Err(invalid(
            "datatype exhaustiveness omits or adds a constructor relative to the \
             declared constructor list"
                .to_string(),
        ))
    }
}

/// Recognize whether `clause` is a valid guarded constructor-reconstruction
/// lemma under the given registries — i.e. whether
/// [`validate_datatype_constructor_reconstruct`] would accept it.
///
/// The DT axiom recorder (`ay-dpll`) calls this to tag the eagerly injected
/// constructor axioms (`is-C(t) => t = C(sel_1(t), ..)`, desugared to the
/// guarded disjunction at `mk_implies`) with the strict-checkable
/// `DatatypeConstructorReconstruct` kind. Shares the exact validator, so the
/// classifier and checker cannot drift.
#[must_use]
pub fn recognize_datatype_constructor_reconstruct(
    terms: &TermStore,
    clause: &[TermId],
    dt_decls: &[(String, Vec<String>)],
    ctor_selectors: &[(String, Vec<String>)],
) -> bool {
    validate_datatype_constructor_reconstruct(terms, ProofId(0), clause, dt_decls, ctor_selectors)
        .is_ok()
}

/// Validate a `DatatypeConstructorReconstruct` lemma in strict mode against
/// the datatype AND constructor→selector registries.
///
/// Accepted shape — exactly what the DT axiom emitter interns for its
/// constructor family (`mk_implies` desugars `=>` to a disjunction whose
/// literal order is canonicalized, and `mk_eq` orients the equality
/// arbitrarily, so both orders of both are accepted):
///
/// ```text
/// (cl (not (is-C t)) (= t (C (sel_1 t) .. (sel_k t))))   k >= 1
/// (cl (not (is-C t)) (= t C))                            C nullary
/// ```
///
/// Soundness: if `t` is built by constructor `C` then each `sel_i(t)` is
/// `t`'s field `i`, so re-applying `C` to ALL its selector projections in
/// declared field order rebuilds `t`; otherwise the guard literal holds. The
/// argument rests on `sel_1 .. sel_k` being EXACTLY `C`'s declared selector
/// list in declared order — re-derived here from the registry, never from the
/// clause — so a permuted (`C(snd(t), fst(t))`), truncated, repeated, or
/// foreign selector chain fails closed, as does an unregistered constructor,
/// a tester/equality subject mismatch, or a scrutinee whose sort is not `C`'s
/// datatype. Nullary reconstruction requires the registry to record `C` with
/// ZERO fields; term shape alone (`Var` / zero-arg `App`) is forgeable.
pub(crate) fn validate_datatype_constructor_reconstruct(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    dt_decls: DatatypeDecls<'_>,
    ctor_selectors: SelectorDecls<'_>,
) -> Result<(), ProofCheckError> {
    let invalid = |reason: String| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason,
    };

    let literals = flatten_clause_literals(terms, clause);
    if literals.len() != 2 {
        return Err(invalid(format!(
            "datatype constructor reconstruction has {} literals; expected the guarded \
             disjunction (cl (not (is-C t)) (= t (C (sel_1 t) ..)))",
            literals.len()
        )));
    }

    // `mk_or` canonicalizes literal order, `mk_eq` orients its operands: try
    // both literal assignments and both equality orientations.
    for (guard, conclusion) in [(literals[0], literals[1]), (literals[1], literals[0])] {
        let TermData::Not(tester) = terms.get(guard) else {
            continue;
        };
        let Some((ctor, scrutinee)) = tester_application(terms, *tester) else {
            continue;
        };
        let Some(dt) = constructor_datatype(dt_decls, ctor) else {
            continue;
        };
        if !sort_matches_datatype(terms.sort(scrutinee), dt) {
            continue;
        }
        let Some((eq_lhs, eq_rhs)) = equality_sides(terms, conclusion) else {
            continue;
        };
        for (subject_side, rebuilt_side) in [(eq_lhs, eq_rhs), (eq_rhs, eq_lhs)] {
            if subject_side == scrutinee
                && reconstruction_matches(terms, ctor_selectors, ctor, scrutinee, rebuilt_side)
            {
                return Ok(());
            }
        }
    }
    Err(invalid(
        "datatype constructor reconstruction does not match \
         (cl (not (is-C t)) (= t (C (sel_1 t) .. (sel_k t)))) for a registered \
         constructor with its FULL declared selector list in declared field order"
            .to_string(),
    ))
}

/// True when `rebuilt` is `ctor` applied to EXACTLY its registered selector
/// list, each selector applied to `scrutinee`, in declared field order — or,
/// for a REGISTRY-nullary `ctor`, the bare constructor constant.
fn reconstruction_matches(
    terms: &TermStore,
    ctor_selectors: SelectorDecls<'_>,
    ctor: &str,
    scrutinee: TermId,
    rebuilt: TermId,
) -> bool {
    // The selector registry is the sole authority on the constructor's field
    // list (and, via emptiness, its nullarity). No entry -> fail closed.
    let Some((_, selectors)) = ctor_selectors
        .iter()
        .find(|(constructor, _)| constructor == ctor)
    else {
        return false;
    };
    match terms.get(rebuilt) {
        TermData::App(Symbol::Named(name), args) if name == ctor => {
            args.len() == selectors.len()
                && args.iter().zip(selectors.iter()).all(|(&arg, selector)| {
                    matches!(
                        terms.get(arg),
                        TermData::App(Symbol::Named(sel_name), sel_args)
                            if sel_name == selector
                                && sel_args.as_slice() == [scrutinee]
                    )
                })
        }
        TermData::Var(name, _) if name == ctor => selectors.is_empty(),
        _ => false,
    }
}

/// Decode `(sel (C a_0 .. a_n))` into `(ctor_name, [a_0 .. a_n], sel_name)`.
fn selector_over_constructor(
    terms: &TermStore,
    term: TermId,
) -> Option<(String, Vec<TermId>, String)> {
    let TermData::App(Symbol::Named(sel_name), sel_args) = terms.get(term) else {
        return None;
    };
    if sel_args.len() != 1 {
        return None;
    }
    if !matches!(
        terms.sort(sel_args[0]),
        Sort::Uninterpreted(_) | Sort::Datatype(_)
    ) {
        return None;
    }
    let TermData::App(Symbol::Named(ctor_name), ctor_args) = terms.get(sel_args[0]) else {
        return None;
    };
    Some((ctor_name.clone(), ctor_args.clone(), sel_name.clone()))
}

/// The field position of `sel_name` among `ctor_name`'s registered selectors.
fn selector_field_index(
    ctor_selectors: SelectorDecls<'_>,
    ctor_name: &str,
    sel_name: &str,
) -> Option<usize> {
    let (_, selectors) = ctor_selectors.iter().find(|(c, _)| c == ctor_name)?;
    selectors.iter().position(|s| s == sel_name)
}

/// Decode the Boolean application shape `(= a b)` without comparing operand
/// sorts. Callers that establish one common sort independently can use this to
/// avoid repeating an arbitrarily long sort-name comparison at every edge.
fn syntactic_equality_sides(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args)
            if name == "=" && args.len() == 2 && terms.sort(term) == &Sort::Bool =>
        {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// Decode a sort-correct positive equality `(= a b)` into `(a, b)`.
fn equality_sides(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    let (lhs, rhs) = syntactic_equality_sides(terms, term)?;
    (terms.sort(lhs) == terms.sort(rhs)).then_some((lhs, rhs))
}

/// Flatten a clause to its literals, unwrapping a single `(or ..)` literal.
fn flatten_clause_literals(terms: &TermStore, clause: &[TermId]) -> Vec<TermId> {
    if clause.len() == 1 {
        if let TermData::App(Symbol::Named(name), args) = terms.get(clause[0]) {
            if name == "or"
                && terms.sort(clause[0]) == &Sort::Bool
                && args.iter().all(|&arg| terms.sort(arg) == &Sort::Bool)
            {
                return args.clone();
            }
        }
    }
    clause.to_vec()
}

/// Decode `(not (= a b))` into `(a, b)`.
fn negated_equality_sides(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    let TermData::Not(inner) = terms.get(term) else {
        return None;
    };
    equality_sides(terms, *inner)
}
