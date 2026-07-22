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

use ay_core::{ProofId, TermData, TermId, TermStore};

use super::ProofCheckError;

/// Datatype declarations supplied by the executor: `(datatype_name, [constructor_name, ..])`.
pub(crate) type DatatypeDecls<'a> = &'a [(String, Vec<String>)];

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
        TermData::App(sym, _) => sym.name().to_string(),
        TermData::Var(n, _) => n.clone(),
        _ => return None,
    };
    let dt = constructor_datatype(dt_decls, &name)?;
    Some((name, dt))
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

/// Decode `(sel (C a_0 .. a_n))` into `(ctor_name, [a_0 .. a_n], sel_name)`.
fn selector_over_constructor(
    terms: &TermStore,
    term: TermId,
) -> Option<(String, Vec<TermId>, String)> {
    let TermData::App(sel_sym, sel_args) = terms.get(term) else {
        return None;
    };
    if sel_args.len() != 1 {
        return None;
    }
    let TermData::App(ctor_sym, ctor_args) = terms.get(sel_args[0]) else {
        return None;
    };
    Some((
        ctor_sym.name().to_string(),
        ctor_args.clone(),
        sel_sym.name().to_string(),
    ))
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

/// Decode a positive equality `(= a b)` into `(a, b)`.
fn equality_sides(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// Flatten a clause to its literals, unwrapping a single `(or ..)` literal.
fn flatten_clause_literals(terms: &TermStore, clause: &[TermId]) -> Vec<TermId> {
    if clause.len() == 1 {
        if let TermData::App(sym, args) = terms.get(clause[0]) {
            if sym.name() == "or" {
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
    match terms.get(*inner) {
        TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}
