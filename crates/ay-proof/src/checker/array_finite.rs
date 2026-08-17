// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact finite-carrier array schemas.
//!
//! These validators deliberately share no enumeration result with the solver.
//! They recover the carrier from the term sorts plus the authenticated
//! datatype context and then account for every point themselves. A kind tag
//! therefore carries no authority: missing, duplicated, foreign, or ill-sorted
//! points all fail closed.

use std::collections::BTreeSet;

use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::{BigInt, Sign};

use super::{DatatypeMemberSignature, ProofCheckError};

mod extensionality;
mod select_expansion;

use extensionality::matches_finite_extensionality;
use select_expansion::matches_finite_select_expansion;

/// Keep the proof recognizer exactly aligned with the live solver's eager enum
/// lane. Besides bounding work on an untrusted declaration registry, this
/// means the classifier never assigns this rule to an axiom the producer would
/// not itself enumerate.
const MAX_FINITE_ENUM_INDEX_CARDINALITY: usize = 16;

#[derive(Clone, Copy)]
struct DatatypeContext<'a> {
    declarations: &'a [(String, Vec<String>)],
    selectors: &'a [(String, Vec<String>)],
    member_signatures: &'a [DatatypeMemberSignature],
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum DomainPoint {
    Bool(bool),
    BitVec(BigInt),
    Enum(TermId),
}

#[derive(Clone)]
enum FiniteCarrier {
    Bool,
    BitVec { width: u32 },
    Enum { members: BTreeSet<TermId> },
}

impl FiniteCarrier {
    fn for_sort(
        terms: &TermStore,
        sort: &Sort,
        allow_bitvectors: bool,
        datatype_context: Option<DatatypeContext<'_>>,
    ) -> Option<Self> {
        match sort {
            Sort::Bool => Some(Self::Bool),
            Sort::BitVec(bitvec) if allow_bitvectors && (1..=8).contains(&bitvec.width) => {
                Some(Self::BitVec {
                    width: bitvec.width,
                })
            }
            Sort::Uninterpreted(_) | Sort::Datatype(_) => {
                let members = enum_member_terms(terms, sort, datatype_context?)?;
                Some(Self::Enum { members })
            }
            _ => None,
        }
    }

    fn cardinality(&self) -> usize {
        match self {
            Self::Bool => 2,
            Self::BitVec { width } => 1usize << *width,
            Self::Enum { members } => members.len(),
        }
    }

    fn point(&self, terms: &TermStore, index_sort: &Sort, term: TermId) -> Option<DomainPoint> {
        if terms.sort(term) != index_sort {
            return None;
        }
        match (self, terms.get(term)) {
            (Self::Bool, TermData::Const(Constant::Bool(value))) => Some(DomainPoint::Bool(*value)),
            (
                Self::BitVec { width },
                TermData::Const(Constant::BitVec {
                    value,
                    width: literal_width,
                }),
            ) if literal_width == width => {
                let modulus = BigInt::from(1_u8) << *width;
                if value.sign() == Sign::Minus || value >= &modulus {
                    None
                } else {
                    Some(DomainPoint::BitVec(value.clone()))
                }
            }
            (Self::Enum { members }, TermData::Var(_, _)) if members.contains(&term) => {
                Some(DomainPoint::Enum(term))
            }
            _ => None,
        }
    }

    fn is_complete(&self, points: &BTreeSet<DomainPoint>) -> bool {
        if points.len() != self.cardinality() {
            return false;
        }
        match self {
            Self::Enum { members } => members
                .iter()
                .all(|member| points.contains(&DomainPoint::Enum(*member))),
            // `point` admits only the two Bool constants or an in-range BV
            // value. A duplicate-free set with the carrier's cardinality must
            // therefore be the whole carrier.
            Self::Bool | Self::BitVec { .. } => true,
        }
    }
}

/// Recognize a strict-checkable complete finite-array extensionality
/// biconditional over `Bool` or a `1..=8`-bit bit-vector index.
///
/// Enum indices need authenticated declaration/member identity and are handled
/// by [`recognize_array_finite_extensionality_with_typed_context`].
#[must_use]
pub fn recognize_array_finite_extensionality(terms: &TermStore, clause: &[TermId]) -> bool {
    matches_finite_extensionality(terms, clause, None)
}

/// Typed-context form of [`recognize_array_finite_extensionality`], additionally
/// recognizing complete all-nullary enum carriers.
///
/// Classification is not proof authority: strict checking globally validates
/// this exact datatype context before applying the same structural matcher.
#[must_use]
pub fn recognize_array_finite_extensionality_with_typed_context(
    terms: &TermStore,
    clause: &[TermId],
    datatype_declarations: &[(String, Vec<String>)],
    constructor_selectors: &[(String, Vec<String>)],
    datatype_member_signatures: &[DatatypeMemberSignature],
) -> bool {
    matches_finite_extensionality(
        terms,
        clause,
        Some(DatatypeContext {
            declarations: datatype_declarations,
            selectors: constructor_selectors,
            member_signatures: datatype_member_signatures,
        }),
    )
}

/// Recognize a strict-checkable complete symbolic-select expansion over a
/// `Bool` index.
///
/// Enum indices need authenticated declaration/member identity and are handled
/// by [`recognize_array_finite_select_expansion_with_typed_context`].
#[must_use]
pub fn recognize_array_finite_select_expansion(terms: &TermStore, clause: &[TermId]) -> bool {
    matches_finite_select_expansion(terms, clause, None)
}

/// Typed-context form of [`recognize_array_finite_select_expansion`],
/// additionally recognizing complete all-nullary enum carriers.
#[must_use]
pub fn recognize_array_finite_select_expansion_with_typed_context(
    terms: &TermStore,
    clause: &[TermId],
    datatype_declarations: &[(String, Vec<String>)],
    constructor_selectors: &[(String, Vec<String>)],
    datatype_member_signatures: &[DatatypeMemberSignature],
) -> bool {
    matches_finite_select_expansion(
        terms,
        clause,
        Some(DatatypeContext {
            declarations: datatype_declarations,
            selectors: constructor_selectors,
            member_signatures: datatype_member_signatures,
        }),
    )
}

pub(crate) fn validate_array_finite_extensionality(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    datatype_declarations: Option<&[(String, Vec<String>)]>,
    constructor_selectors: Option<&[(String, Vec<String>)]>,
    datatype_member_signatures: Option<&[DatatypeMemberSignature]>,
) -> Result<(), ProofCheckError> {
    let datatype_context = typed_context(
        datatype_declarations,
        constructor_selectors,
        datatype_member_signatures,
    );
    if matches_finite_extensionality(terms, clause, datatype_context) {
        Ok(())
    } else {
        Err(ProofCheckError::InvalidTheoryLemma {
            step,
            reason: "finite-array extensionality must be exactly one biconditional between an array equality and complete, duplicate-free pointwise equality over Bool, BV width 1..=8, or an authenticated all-nullary enum carrier"
                .to_string(),
        })
    }
}

pub(crate) fn validate_array_finite_select_expansion(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    datatype_declarations: Option<&[(String, Vec<String>)]>,
    constructor_selectors: Option<&[(String, Vec<String>)]>,
    datatype_member_signatures: Option<&[DatatypeMemberSignature]>,
) -> Result<(), ProofCheckError> {
    let datatype_context = typed_context(
        datatype_declarations,
        constructor_selectors,
        datatype_member_signatures,
    );
    if matches_finite_select_expansion(terms, clause, datatype_context) {
        Ok(())
    } else {
        Err(ProofCheckError::InvalidTheoryLemma {
            step,
            reason: "finite symbolic-select expansion must be exactly the complete, duplicate-free Bool/all-nullary-enum ITE expansion of one well-sorted select"
                .to_string(),
        })
    }
}

fn typed_context<'a>(
    declarations: Option<&'a [(String, Vec<String>)]>,
    selectors: Option<&'a [(String, Vec<String>)]>,
    member_signatures: Option<&'a [DatatypeMemberSignature]>,
) -> Option<DatatypeContext<'a>> {
    Some(DatatypeContext {
        declarations: declarations?,
        selectors: selectors?,
        member_signatures: member_signatures?,
    })
}

fn equality_sides(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(Symbol::Named(name), arguments) = terms.get(term) else {
        return None;
    };
    if name != "="
        || arguments.len() != 2
        || terms.sort(term) != &Sort::Bool
        || terms.sort(arguments[0]) != terms.sort(arguments[1])
    {
        return None;
    }
    Some((arguments[0], arguments[1]))
}

fn select_parts(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(Symbol::Named(name), arguments) = terms.get(term) else {
        return None;
    };
    if name != "select" || arguments.len() != 2 {
        return None;
    }
    let array = arguments[0];
    let index = arguments[1];
    let Sort::Array(array_sort) = terms.sort(array) else {
        return None;
    };
    if terms.sort(index) != &array_sort.index_sort || terms.sort(term) != &array_sort.element_sort {
        return None;
    }
    Some((array, index))
}

fn enum_member_terms(
    terms: &TermStore,
    index_sort: &Sort,
    context: DatatypeContext<'_>,
) -> Option<BTreeSet<TermId>> {
    let datatype_name = match index_sort {
        Sort::Uninterpreted(name) => name.as_str(),
        Sort::Datatype(datatype) => datatype.name.as_str(),
        _ => return None,
    };
    let mut matching_declarations = context
        .declarations
        .iter()
        .filter(|(name, _)| name == datatype_name);
    let (_, constructors) = matching_declarations.next()?;
    if matching_declarations.next().is_some()
        || constructors.is_empty()
        || constructors.len() > MAX_FINITE_ENUM_INDEX_CARDINALITY
    {
        return None;
    }
    let constructor_names: BTreeSet<&str> = constructors.iter().map(String::as_str).collect();
    if constructor_names.len() != constructors.len() {
        return None;
    }

    if let Sort::Datatype(datatype) = index_sort {
        let datatype_constructor_names: BTreeSet<&str> = datatype
            .constructors
            .iter()
            .map(|constructor| constructor.name.as_str())
            .collect();
        if datatype_constructor_names.len() != datatype.constructors.len()
            || datatype_constructor_names != constructor_names
            || datatype
                .constructors
                .iter()
                .any(|constructor| !constructor.fields.is_empty())
        {
            return None;
        }
    }

    let mut members = BTreeSet::new();
    for constructor in constructors {
        let mut selector_matches = context
            .selectors
            .iter()
            .filter(|(name, _)| name == constructor);
        let (_, fields) = selector_matches.next()?;
        if selector_matches.next().is_some() || !fields.is_empty() {
            return None;
        }

        let mut signature_matches = context
            .member_signatures
            .iter()
            .filter(|signature| signature.identity == *constructor);
        let signature = signature_matches.next()?;
        if signature_matches.next().is_some()
            || !signature.argument_sorts.is_empty()
            || &signature.result_sort != index_sort
        {
            return None;
        }
        let member = signature.nullary_term?;
        if member.index() >= terms.len()
            || terms.sort(member) != index_sort
            || !matches!(terms.get(member), TermData::Var(name, _) if name == constructor)
            || !members.insert(member)
        {
            return None;
        }
    }
    Some(members)
}
