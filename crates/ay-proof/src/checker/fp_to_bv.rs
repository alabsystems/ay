// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Strict-mode schema validation for `TheoryLemmaKind::FpToBv` proof steps.
//!
//! Context (#8820): previously these lemmas were accepted with only a
//! non-empty clause check. This module adds schema validation that catches
//! the most common forgeries:
//!
//! - Every literal must be Boolean-sorted (FP→BV lowering always produces
//!   propositional clauses).
//! - The clause must reference either an FP-sorted sub-term or a BV-sorted
//!   sub-term (the two sides of the lowering). A clause mentioning neither
//!   is not an FP→BV axiom.
//! - The clause must mention the specific FP operation carried by the proof
//!   annotation, so `FpToBv { operation: Add }` cannot justify a clause about
//!   `fp.isNaN`, `fp.mul`, or any other unrelated FP operator.
//!
//! Full semantic verification — i.e. re-running the FP operation and checking
//! the BV circuit encoding matches IEEE 754 — is future work tracked by
//! #8075. Strict mode is fail-closed until that checker exists: even
//! schema-shaped FP→BV lemmas are rejected instead of accepted as proof.

use ay_core::{FpOp, ProofId, Sort, TermData, TermId, TermStore};

use super::ProofCheckError;

/// Validate an `FpToBv { operation }` lemma in strict mode.
pub(crate) fn validate_fp_to_bv(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    operation: FpOp,
) -> Result<(), ProofCheckError> {
    if clause.is_empty() {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "fp_to_bv clause must be non-empty".to_string(),
        });
    }

    for &lit in clause {
        let sort = terms.sort(lit);
        if !matches!(sort, Sort::Bool) {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: format!(
                    "fp_to_bv literal has non-Bool sort {sort:?}; FP→BV \
                     axiom clauses must be propositional"
                ),
            });
        }
    }

    let mentions_fp_or_bv = clause.iter().any(|&lit| mentions_fp_or_bv(terms, lit));
    if !mentions_fp_or_bv {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "fp_to_bv clause must mention at least one \
                     floating-point or bitvector sub-term"
                .to_string(),
        });
    }

    let mentions_declared_operation = clause
        .iter()
        .any(|&lit| mentions_fp_operation(terms, lit, operation));
    if !mentions_declared_operation {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: format!("fp_to_bv clause must reference declared operation {operation}"),
        });
    }

    Err(ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: format!(
            "fp_to_bv {operation} lacks a strict semantic lowering certificate; \
             rejecting in fail-closed mode"
        ),
    })
}

fn mentions_fp_or_bv(terms: &TermStore, term: TermId) -> bool {
    mentions_fp_or_bv_inner(terms, term, &mut Vec::new())
}

fn mentions_fp_or_bv_inner(terms: &TermStore, term: TermId, stack: &mut Vec<TermId>) -> bool {
    if stack.len() > 512 {
        return false;
    }
    stack.push(term);
    let sort = terms.sort(term);
    let result = matches!(sort, Sort::FloatingPoint(_, _) | Sort::BitVec(_))
        || match terms.get(term) {
            TermData::App(_, args) => args
                .iter()
                .any(|&a| mentions_fp_or_bv_inner(terms, a, stack)),
            TermData::Not(inner) => mentions_fp_or_bv_inner(terms, *inner, stack),
            TermData::Ite(c, t, e) => {
                mentions_fp_or_bv_inner(terms, *c, stack)
                    || mentions_fp_or_bv_inner(terms, *t, stack)
                    || mentions_fp_or_bv_inner(terms, *e, stack)
            }
            _ => false,
        };
    stack.pop();
    result
}

fn mentions_fp_operation(terms: &TermStore, term: TermId, operation: FpOp) -> bool {
    mentions_fp_operation_inner(terms, term, operation, &mut Vec::new())
}

fn mentions_fp_operation_inner(
    terms: &TermStore,
    term: TermId,
    operation: FpOp,
    stack: &mut Vec<TermId>,
) -> bool {
    if stack.len() > 512 {
        return false;
    }
    stack.push(term);
    let result = match terms.get(term) {
        TermData::App(sym, args) => {
            app_matches_fp_operation(terms, sym.name(), args, operation)
                || args
                    .iter()
                    .any(|&a| mentions_fp_operation_inner(terms, a, operation, stack))
        }
        TermData::Not(inner) => mentions_fp_operation_inner(terms, *inner, operation, stack),
        TermData::Ite(c, t, e) => {
            mentions_fp_operation_inner(terms, *c, operation, stack)
                || mentions_fp_operation_inner(terms, *t, operation, stack)
                || mentions_fp_operation_inner(terms, *e, operation, stack)
        }
        _ => false,
    };
    stack.pop();
    result
}

fn app_matches_fp_operation(
    terms: &TermStore,
    name: &str,
    args: &[TermId],
    operation: FpOp,
) -> bool {
    match operation {
        FpOp::StructuralEq => {
            name == "="
                && args.len() == 2
                && matches!(terms.sort(args[0]), Sort::FloatingPoint(_, _))
                && matches!(terms.sort(args[1]), Sort::FloatingPoint(_, _))
        }
        FpOp::FromReal => {
            name == "to_fp" && args.len() == 2 && matches!(terms.sort(args[1]), Sort::Real)
        }
        FpOp::FromSbv => {
            name == "to_fp"
                && (args.len() == 1 || args.len() == 2)
                && matches!(terms.sort(args[args.len() - 1]), Sort::BitVec(_))
        }
        FpOp::FromUbv => {
            name == "to_fp_unsigned"
                && args.len() == 2
                && matches!(terms.sort(args[1]), Sort::BitVec(_))
        }
        FpOp::FromFp => {
            name == "to_fp"
                && args.len() == 2
                && matches!(terms.sort(args[1]), Sort::FloatingPoint(_, _))
        }
        _ => fp_operation_symbol_names(operation).contains(&name),
    }
}

fn fp_operation_symbol_names(operation: FpOp) -> &'static [&'static str] {
    match operation {
        FpOp::Add => &["fp.add"],
        FpOp::Sub => &["fp.sub"],
        FpOp::Mul => &["fp.mul"],
        FpOp::Div => &["fp.div"],
        FpOp::Sqrt => &["fp.sqrt"],
        FpOp::Neg => &["fp.neg"],
        FpOp::Abs => &["fp.abs"],
        FpOp::Fma => &["fp.fma"],
        FpOp::Eq => &["fp.eq"],
        FpOp::Lt => &["fp.lt"],
        FpOp::Le => &["fp.leq"],
        FpOp::Gt => &["fp.gt"],
        FpOp::Ge => &["fp.geq"],
        FpOp::ToReal => &["fp.to_real"],
        FpOp::ToSbv => &["fp.to_sbv"],
        FpOp::ToUbv => &["fp.to_ubv"],
        FpOp::RoundToIntegral => &["fp.roundToIntegral"],
        FpOp::Min => &["fp.min"],
        FpOp::Max => &["fp.max"],
        FpOp::Rem => &["fp.rem"],
        FpOp::IsNaN => &["fp.isNaN"],
        FpOp::IsInfinite => &["fp.isInfinite"],
        FpOp::IsZero => &["fp.isZero"],
        FpOp::IsNormal => &["fp.isNormal"],
        FpOp::IsSubnormal => &["fp.isSubnormal"],
        FpOp::IsPositive => &["fp.isPositive"],
        FpOp::IsNegative => &["fp.isNegative"],
        FpOp::ToIeeeBv => &["fp.to_ieee_bv"],
        FpOp::FromReal | FpOp::FromSbv | FpOp::FromUbv | FpOp::FromFp | FpOp::StructuralEq => &[],
        _ => &[],
    }
}
