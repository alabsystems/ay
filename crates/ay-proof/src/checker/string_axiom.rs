// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Strict-mode schema validation for string-theory lemma kinds:
//!
//! - `TheoryLemmaKind::StringLengthAxiom` (`str.len`, `str.++`)
//! - `TheoryLemmaKind::StringContentAxiom` (`str.substr`, `str.contains`,
//!   `str.replace`, `str.indexof`, `str.at`, `str.++`)
//! - `TheoryLemmaKind::StringNormalForm` (`str.to_code`, `str.from_code`,
//!   `str.++`, `str.len`)
//!
//! Context (#8820): previously these lemmas passed any non-empty clause,
//! allowing forged UNSAT proofs. Strict mode now fails closed: length lemmas
//! pass only when the checker can statically prove the clause true, and
//! content/normal-form lemmas are rejected until they have semantic
//! validators.
//!
//! Full semantic validation of string axioms (#8074) remains future work.

use ay_core::{Constant, ProofId, Sort, TermData, TermId, TermStore};
use num_bigint::BigInt;

use super::ProofCheckError;

pub(crate) fn validate_string_length_axiom(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    validate_with_required_ops(
        terms,
        step_id,
        clause,
        "string_length_axiom",
        // Length axioms must mention `str.len`. They typically also mention
        // `str.++` (concatenation) or string constants.
        &[&["str.len"]],
    )?;
    require_statically_true_clause(terms, step_id, clause, "string_length_axiom")
}

pub(crate) fn validate_string_content_axiom(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    validate_with_required_ops(
        terms,
        step_id,
        clause,
        "string_content_axiom",
        // Content axioms must mention at least one content-rewriting operator.
        &[&[
            "str.substr",
            "str.contains",
            "str.replace",
            "str.indexof",
            "str.at",
            "str.prefixof",
            "str.suffixof",
            "str.++",
        ]],
    )?;
    Err(ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: "string_content_axiom lacks a strict semantic validator; \
                 rejecting in fail-closed mode"
            .to_string(),
    })
}

pub(crate) fn validate_string_normal_form(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    validate_with_required_ops(
        terms,
        step_id,
        clause,
        "string_normal_form",
        // Normal-form reasoning is about word equations, code injectivity,
        // and concatenation normal forms. The clause must mention at least
        // one of these markers.
        &[&[
            "str.++",
            "str.to_code",
            "str.from_code",
            "str.to_int",
            "str.from_int",
            "str.len",
        ]],
    )?;
    Err(ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: "string_normal_form lacks a strict semantic validator; \
                 rejecting in fail-closed mode"
            .to_string(),
    })
}

/// Shared schema validator: every literal must be Bool-sorted, and the
/// clause must mention at least one operator from each required group.
///
/// `required_groups` is a list of "AND" requirements — each inner slice is a
/// disjunctive set of allowed operator names, and at least one of them must
/// appear. All groups must be satisfied for the clause to pass.
fn validate_with_required_ops(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    context: &str,
    required_groups: &[&[&str]],
) -> Result<(), ProofCheckError> {
    if clause.is_empty() {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: format!("{context} clause must be non-empty"),
        });
    }

    for &lit in clause {
        let sort = terms.sort(lit);
        if !matches!(sort, Sort::Bool) {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: format!(
                    "{context} literal has non-Bool sort {sort:?}; string \
                     axiom clauses must be propositional"
                ),
            });
        }
    }

    for group in required_groups {
        let found = clause
            .iter()
            .any(|&lit| contains_any_op(terms, lit, group, &mut Vec::new()));
        if !found {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: format!("{context} clause must reference at least one of: {group:?}"),
            });
        }
    }

    // Always require at least one String-sorted or String-producing sub-term
    // — a clause with no string content cannot be a string axiom.
    let mentions_string = clause.iter().any(|&lit| mentions_string(terms, lit));
    if !mentions_string {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: format!(
                "{context} clause does not mention any String-sorted sub-term; \
                 a forged lemma cannot hide behind this rule"
            ),
        });
    }

    Ok(())
}

fn require_statically_true_clause(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    context: &str,
) -> Result<(), ProofCheckError> {
    match eval_clause(terms, clause) {
        Some(true) => Ok(()),
        Some(false) => Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: format!(
                "{context} clause is statically false under concrete string \
                 semantics"
            ),
        }),
        None => Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: format!(
                "{context} clause is not statically provable by the strict \
                 string checker"
            ),
        }),
    }
}

fn eval_clause(terms: &TermStore, clause: &[TermId]) -> Option<bool> {
    let mut all_false = true;
    for &lit in clause {
        match eval_bool(terms, lit) {
            Some(true) => return Some(true),
            Some(false) => {}
            None => all_false = false,
        }
    }
    all_false.then_some(false)
}

fn eval_bool(terms: &TermStore, term: TermId) -> Option<bool> {
    match terms.get(term) {
        TermData::Const(Constant::Bool(value)) => Some(*value),
        TermData::Not(inner) => eval_bool(terms, *inner).map(|value| !value),
        TermData::App(sym, args) => match sym.name() {
            "=" if args.len() == 2 => {
                let lhs = eval_int(terms, args[0])?;
                let rhs = eval_int(terms, args[1])?;
                Some(lhs == rhs)
            }
            "<" if args.len() == 2 => eval_int_comparison(terms, args, |lhs, rhs| lhs < rhs),
            "<=" if args.len() == 2 => eval_int_comparison(terms, args, |lhs, rhs| lhs <= rhs),
            ">" if args.len() == 2 => eval_int_comparison(terms, args, |lhs, rhs| lhs > rhs),
            ">=" if args.len() == 2 => eval_int_comparison(terms, args, |lhs, rhs| lhs >= rhs),
            "or" => eval_or(terms, args),
            "and" => eval_and(terms, args),
            _ => None,
        },
        _ => None,
    }
}

fn eval_int_comparison(
    terms: &TermStore,
    args: &[TermId],
    cmp: impl FnOnce(&BigInt, &BigInt) -> bool,
) -> Option<bool> {
    let lhs = eval_int(terms, args[0])?;
    let rhs = eval_int(terms, args[1])?;
    Some(cmp(&lhs, &rhs))
}

fn eval_or(terms: &TermStore, args: &[TermId]) -> Option<bool> {
    let mut all_false = true;
    for &arg in args {
        match eval_bool(terms, arg) {
            Some(true) => return Some(true),
            Some(false) => {}
            None => all_false = false,
        }
    }
    all_false.then_some(false)
}

fn eval_and(terms: &TermStore, args: &[TermId]) -> Option<bool> {
    let mut all_true = true;
    for &arg in args {
        match eval_bool(terms, arg) {
            Some(false) => return Some(false),
            Some(true) => {}
            None => all_true = false,
        }
    }
    all_true.then_some(true)
}

fn eval_int(terms: &TermStore, term: TermId) -> Option<BigInt> {
    match terms.get(term) {
        TermData::Const(Constant::Int(value)) => Some(value.clone()),
        TermData::App(sym, args) if sym.name() == "str.len" && args.len() == 1 => {
            eval_string_len(terms, args[0])
        }
        _ => None,
    }
}

fn eval_string_len(terms: &TermStore, term: TermId) -> Option<BigInt> {
    match terms.get(term) {
        TermData::Const(Constant::String(value)) => Some(BigInt::from(value.chars().count())),
        TermData::App(sym, args) if sym.name() == "str.++" => {
            let mut total = BigInt::from(0u8);
            for &arg in args {
                total += eval_string_len(terms, arg)?;
            }
            Some(total)
        }
        _ => None,
    }
}

fn contains_any_op(
    terms: &TermStore,
    term: TermId,
    names: &[&str],
    stack: &mut Vec<TermId>,
) -> bool {
    if stack.len() > 512 {
        return false;
    }
    stack.push(term);
    let result = match terms.get(term) {
        TermData::App(sym, args) => {
            let sym_name = sym.name();
            names.contains(&sym_name)
                || args
                    .iter()
                    .any(|&a| contains_any_op(terms, a, names, stack))
        }
        TermData::Not(inner) => contains_any_op(terms, *inner, names, stack),
        TermData::Ite(c, t, e) => {
            contains_any_op(terms, *c, names, stack)
                || contains_any_op(terms, *t, names, stack)
                || contains_any_op(terms, *e, names, stack)
        }
        _ => false,
    };
    stack.pop();
    result
}

fn mentions_string(terms: &TermStore, term: TermId) -> bool {
    mentions_string_inner(terms, term, &mut Vec::new())
}

fn mentions_string_inner(terms: &TermStore, term: TermId, stack: &mut Vec<TermId>) -> bool {
    if stack.len() > 512 {
        return false;
    }
    stack.push(term);
    let result = matches!(terms.sort(term), Sort::String)
        || match terms.get(term) {
            TermData::App(_, args) => args.iter().any(|&a| mentions_string_inner(terms, a, stack)),
            TermData::Not(inner) => mentions_string_inner(terms, *inner, stack),
            TermData::Ite(c, t, e) => {
                mentions_string_inner(terms, *c, stack)
                    || mentions_string_inner(terms, *t, stack)
                    || mentions_string_inner(terms, *e, stack)
            }
            _ => false,
        };
    stack.pop();
    result
}
