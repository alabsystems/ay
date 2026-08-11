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

use ay_core::kani_compat::det_hash_set_with_capacity;
use ay_core::{ProofId, Sort, Symbol, TermData, TermId, TermStore};

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
    validate_datatype_tester_eval(terms, ProofId(0), clause, dt_decls, None).is_ok()
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
    validate_datatype_tester_eval(terms, ProofId(0), clause, dt_decls, Some(ctor_selectors)).is_ok()
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
