// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_core::{ProofId, TermData, TermId, TermStore};

use super::{
    constructor_datatype, constructor_head, flatten_clause_literals, sort_matches_datatype,
    tester_application, DatatypeDecls, ProofCheckError,
};

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
