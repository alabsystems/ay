// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Price every owned proof field before literal equality or cloning. In
//! particular, checker-irrelevant nested hints still occupy the retained proof.

use ay_core::{FarkasAnnotation, LiaAnnotation, Proof, ProofStep, Sort};

use crate::executor::proof::rule_owned_payload::{rule_owned_payload, RuleOwnedPayload};

use super::MAX_SUPPORT_PAYLOAD;

struct Control<'a> {
    progress: &'a mut dyn FnMut(usize, usize) -> bool,
    payload: usize,
}

impl Control<'_> {
    fn charge(&mut self, count: usize, bytes: usize) -> Option<()> {
        self.payload = self.payload.checked_add(count)?;
        (self.payload <= MAX_SUPPORT_PAYLOAD && (self.progress)(count, bytes)).then_some(())
    }

    fn vector<T>(&mut self, count: usize) -> Option<()> {
        self.charge(count, count.checked_mul(std::mem::size_of::<T>())?)
    }

    fn text(&mut self, text: &str) -> Option<()> {
        self.charge(text.len(), text.len())
    }

    fn farkas(&mut self, hint: &FarkasAnnotation) -> Option<()> {
        self.vector::<num_rational::Rational64>(hint.coefficients.len())
    }

    fn sort(&mut self, sort: &Sort, depth: usize) -> Option<()> {
        if depth > 32 {
            return None;
        }
        self.vector::<Sort>(1)?;
        match sort {
            Sort::Bool
            | Sort::Int
            | Sort::Real
            | Sort::BitVec(_)
            | Sort::String
            | Sort::RegLan
            | Sort::FloatingPoint(..)
            | Sort::Char => Some(()),
            Sort::Uninterpreted(name) => self.text(name),
            Sort::Array(array) => {
                self.sort(&array.index_sort, depth + 1)?;
                self.sort(&array.element_sort, depth + 1)
            }
            Sort::Seq(element) => self.sort(element, depth + 1),
            _ => None,
        }
    }
}

pub(super) fn preflight(
    proof: &Proof,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Option<()> {
    let mut control = Control {
        progress,
        payload: 0,
    };
    control.vector::<ProofStep>(proof.steps.len())?;
    // Hash-map cloning can retain spare buckets; inspect capacity before
    // iterating or cloning even a sparsely populated named-step table.
    control.vector::<(String, ay_core::ProofId)>(proof.named_steps.capacity())?;
    for name in proof.named_steps.keys() {
        control.text(name)?;
    }
    for step in &proof.steps {
        control.charge(1, 0)?;
        match step {
            ProofStep::Assume(_) => {}
            ProofStep::Resolution { clause, .. } => {
                control.vector::<ay_core::TermId>(clause.len())?
            }
            ProofStep::TheoryLemma {
                theory,
                clause,
                farkas,
                lia,
                ..
            } => {
                control.text(theory)?;
                control.vector::<ay_core::TermId>(clause.len())?;
                if let Some(hint) = farkas {
                    control.farkas(hint)?;
                }
                match lia {
                    Some(LiaAnnotation::CuttingPlane(hint)) => control.farkas(&hint.farkas)?,
                    Some(
                        LiaAnnotation::BoundsGap
                        | LiaAnnotation::Divisibility
                        | LiaAnnotation::LinearIdentity,
                    )
                    | None => {}
                    _ => return None,
                }
            }
            ProofStep::Step {
                rule,
                clause,
                premises,
                args,
            } => {
                if let RuleOwnedPayload::Text(name) = rule_owned_payload(rule)? {
                    control.text(name)?;
                }
                control.vector::<ay_core::TermId>(clause.len())?;
                control.vector::<ay_core::ProofId>(premises.len())?;
                control.vector::<ay_core::TermId>(args.len())?;
            }
            ProofStep::Anchor { variables, .. } => {
                control.vector::<(String, Sort)>(variables.len())?;
                for (name, sort) in variables {
                    control.text(name)?;
                    control.sort(sort, 0)?;
                }
            }
            _ => return None,
        }
    }
    Some(())
}
