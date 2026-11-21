// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded, noncertifying native IR at the point a proof is rejected. Never
//! retain the rejected proof or format its unused annotations/sort payloads.

use std::collections::HashSet;

use ay_core::{Constant, Proof, ProofStep, Sort, Symbol, TermData, TermId, TermStore};
use ay_proof::ProofCheckError;

const MAX_LITERALS: usize = 32;
const MAX_NODES: usize = 128;
const MAX_EDGES: usize = 1_024;
const MAX_DEPTH: usize = 32;
const MAX_NAME: usize = 256;
const MAX_OUTPUT: usize = 64 * 1_024;

fn append(output: &mut String, line: &str) -> bool {
    const OMITTED: &str = "[native IR output cap exceeded]\n";
    if output
        .len()
        .saturating_add(line.len())
        .saturating_add(OMITTED.len())
        > MAX_OUTPUT
    {
        output.push_str(OMITTED);
        return false;
    }
    output.push_str(line);
    true
}

pub(super) fn render(proof: &Proof, terms: &TermStore, error: &ProofCheckError) -> String {
    let ProofCheckError::InvalidTheoryLemma { step, .. } = error else {
        return "noncertifying rejected-step IR unavailable for this error class".into();
    };
    let Some(ProofStep::TheoryLemma { clause, kind, .. }) = proof.steps.get(step.0 as usize) else {
        return format!("noncertifying rejected-step IR unavailable for {step}");
    };
    if clause.len() > MAX_LITERALS {
        return format!("noncertifying rejected-step IR {step}: literal cap exceeded");
    }
    // Never format a payload-carrying kind's Debug representation: its fields
    // are not part of this bounded native-term diagnostic.
    let kind = match kind {
        ay_core::TheoryLemmaKind::BoolTautology => "BoolTautology",
        ay_core::TheoryLemmaKind::BvBitBlast => "BvBitBlast",
        ay_core::TheoryLemmaKind::BvLiaTautology => "BvLiaTautology",
        _ => "OtherTheoryKind",
    };
    let mut output = format!("noncertifying rejected-step IR {step} {kind}: clause={clause:?}\n");
    let mut pending: Vec<_> = clause.iter().rev().map(|&term| (term, 0usize)).collect();
    let mut seen = HashSet::new();
    let mut edges = 0usize;
    while let Some((term, depth)) = pending.pop() {
        if depth > MAX_DEPTH || seen.len() >= MAX_NODES {
            output.push_str("[native IR walk cap exceeded]\n");
            break;
        }
        if !seen.insert(term) {
            continue;
        }
        if terms.entry_stamp(term).is_none() {
            if !append(&mut output, &format!("{term:?}: invalid term ID\n")) {
                break;
            }
            continue;
        }
        // Only scalar sort tags are rendered. No recursive sort descriptor or
        // user-owned sort name is cloned, compared, or sent through Display.
        let sort = match terms.sort(term) {
            Sort::Bool => "Bool".into(),
            Sort::Int => "Int".into(),
            Sort::Real => "Real".into(),
            Sort::BitVec(width) => format!("BV{}", width.width),
            Sort::Array(_) => "Array".into(),
            _ => "OtherSort".into(),
        };
        let inline_children;
        let (shape, children): (String, &[TermId]) = match terms.get(term) {
            TermData::Var(name, _) if name.len() <= MAX_NAME => (format!("Var {name:?}"), &[]),
            TermData::Const(Constant::Bool(value)) => (format!("Bool {value}"), &[]),
            TermData::Const(Constant::Int(value)) if value.bits() <= 256 => {
                (format!("Int {value}"), &[])
            }
            TermData::Const(Constant::Rational(value))
                if value.0.numer().bits() <= 256 && value.0.denom().bits() <= 256 =>
            {
                (
                    format!("Rational {}/{}", value.0.numer(), value.0.denom()),
                    &[],
                )
            }
            TermData::Const(Constant::BitVec { value, width })
                if value.bits() <= 256 && *width <= 4_096 =>
            {
                (format!("BitVec width={width} value_hex={value:x}"), &[])
            }
            TermData::Const(Constant::String(value)) if value.len() <= MAX_NAME => {
                (format!("String {value:?}"), &[])
            }
            TermData::App(Symbol::Named(name), arguments)
                if name.len() <= MAX_NAME && arguments.len() <= MAX_LITERALS =>
            {
                (format!("App {name:?} args={arguments:?}"), arguments)
            }
            TermData::App(Symbol::Indexed(name, indices), arguments)
                if name.len() <= MAX_NAME
                    && indices.len() <= 8
                    && arguments.len() <= MAX_LITERALS =>
            {
                (
                    format!("IndexedApp {name:?} indices={indices:?} args={arguments:?}"),
                    arguments,
                )
            }
            TermData::Not(child) => (format!("Not {child:?}"), std::slice::from_ref(child)),
            TermData::Ite(condition, yes, no) => {
                inline_children = [*condition, *yes, *no];
                (format!("Ite {inline_children:?}"), &inline_children)
            }
            // Binders, unknown variants and oversized raw data are left
            // opaque. This diagnostic is not a source codec or an evaluator.
            _ => ("[raw payload or shape omitted]".into(), &[]),
        };
        let line = format!("{term:?} {sort}: {shape}\n");
        if !append(&mut output, &line) {
            break;
        }
        edges = edges.saturating_add(children.len());
        if edges > MAX_EDGES || pending.len().saturating_add(children.len()) > MAX_EDGES {
            output.push_str("[native IR edge cap exceeded]\n");
            break;
        }
        pending.extend(children.iter().rev().map(|&child| (child, depth + 1)));
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::{ProofId, TheoryLemmaKind};

    #[test]
    fn rejected_step_ir_refuses_large_raw_metadata_and_invalid_ids() {
        let mut terms = TermStore::new();
        let huge = terms.mk_var("x".repeat(1_000_000), Sort::Bool);
        let mut proof = Proof::new();
        proof.add_theory_lemma_with_kind(
            "BV",
            vec![huge, TermId(u32::MAX)],
            TheoryLemmaKind::BvBitBlast,
        );
        let error = ProofCheckError::InvalidTheoryLemma {
            step: ProofId(0),
            reason: "r".repeat(1_000_000),
        };
        let text = render(&proof, &terms, &error);
        assert!(text.contains("noncertifying"));
        assert!(text.contains("payload or shape omitted"));
        assert!(text.contains("invalid term ID"));
        assert!(text.len() < 1_024);
    }
}
