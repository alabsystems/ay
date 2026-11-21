// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded typed attribution of a rejected arithmetic certificate. No source
//! payload, recursive term rendering or complete proof is formatted here.

use super::*;
use ay_core::TermStore;

type Comparison = (TermId, TermId, bool, &'static str, [TermId; 2]);

fn comparison(terms: &TermStore, literal: TermId) -> Option<Comparison> {
    terms.entry_stamp(literal)?;
    let (atom, negative) = match terms.get(literal) {
        TermData::Not(inner) => (*inner, true),
        _ => (literal, false),
    };
    terms.entry_stamp(atom)?;
    let TermData::App(Symbol::Named(operator), args) = terms.get(atom) else {
        return None;
    };
    let operator = match operator.as_str() {
        "=" => "=",
        "<=" => "<=",
        "<" => "<",
        ">=" => ">=",
        ">" => ">",
        _ => return None,
    };
    let &[left, right] = args.as_slice() else {
        return None;
    };
    Some((literal, atom, negative, operator, [left, right]))
}

pub(super) fn arithmetic_step_note(
    terms: &TermStore,
    proof: &Proof,
    error: &ProofCheckError,
    budget: &RepairBudget,
) -> String {
    let ProofCheckError::InvalidTheoryLemma { step, .. } = error else {
        return "native-arithmetic-failure: no arithmetic step".to_owned();
    };
    let Some(ProofStep::TheoryLemma {
        clause,
        kind,
        farkas,
        lia,
        ..
    }) = proof.steps.get(step.0 as usize)
    else {
        return format!("native-arithmetic-failure: step={} not-theory", step.0);
    };
    let kind = match kind {
        TheoryLemmaKind::LraFarkas => "LraFarkas",
        TheoryLemmaKind::LiaGeneric => "LiaGeneric",
        TheoryLemmaKind::IntCgCutChain => "IntCgCutChain",
        _ => "other",
    };
    // Rational64 coefficients and IDs have fixed scalar widths. Refuse all
    // larger vectors before copying or Debug formatting their contents.
    if clause.len() > 8
        || farkas.as_ref().is_some_and(|f| f.coefficients.len() > 8)
        || !budget.pay(64, 16_384)
    {
        return format!(
            "native-arithmetic-failure: step={} kind={kind} clause_len={} payload=omitted",
            step.0,
            clause.len(),
        );
    }
    let mut rows = Vec::with_capacity(clause.len());
    for &literal in clause {
        rows.push(comparison(terms, literal));
    }
    let coefficients = farkas.as_ref().map(|f| f.coefficients.as_slice());
    format!(
        "native-arithmetic-failure: step={} kind={kind} clause={clause:?} \
         comparisons={rows:?} coefficients={coefficients:?} lia_present={}",
        step.0,
        lia.is_some(),
    )
}
