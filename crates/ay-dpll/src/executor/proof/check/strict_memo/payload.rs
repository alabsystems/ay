// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Complete bounded retention accounting. Refusal skips a memo operation,
//! never the original caller-owned semantic walk or its result.

use ay_core::{FarkasAnnotation, LiaAnnotation, Proof, ProofStep, Sort};
use ay_proof::{ProofCheckError, ProofQuality};

use crate::executor::proof::rule_owned_payload::{rule_owned_payload, RuleOwnedPayload};

use super::{StrictWalkKey, STRICT_WALK_MEMO_MAX_PAYLOAD};

const MAX_SORT_DEPTH: usize = 64;

pub(super) struct Counter {
    used: usize,
    limit: usize,
}

impl Counter {
    pub(super) fn new(limit: usize) -> Self {
        Self { used: 0, limit }
    }

    fn add(&mut self, amount: usize) -> Option<()> {
        self.used = self.used.checked_add(amount)?;
        (self.used <= self.limit).then_some(())
    }

    fn text(&mut self, text: &str) -> Option<()> {
        self.add(text.len())
    }

    fn farkas(&mut self, hint: &FarkasAnnotation) -> Option<()> {
        let FarkasAnnotation { coefficients } = hint;
        self.add(coefficients.len())
    }

    pub(super) fn sort(&mut self, sort: &Sort, depth: usize) -> Option<()> {
        if depth > MAX_SORT_DEPTH {
            return None;
        }
        self.add(1)?;
        match sort {
            Sort::Bool
            | Sort::Int
            | Sort::Real
            | Sort::BitVec(_)
            | Sort::String
            | Sort::RegLan
            | Sort::FloatingPoint(..)
            | Sort::Char
            | Sort::Complex => Some(()),
            Sort::Uninterpreted(name) | Sort::TypeVar(name) | Sort::FiniteDomain(name, _) => {
                self.text(name)
            }
            Sort::Array(array) => {
                self.sort(&array.index_sort, depth + 1)?;
                self.sort(&array.element_sort, depth + 1)
            }
            Sort::Seq(element) => self.sort(element, depth + 1),
            Sort::Datatype(datatype) => {
                self.text(&datatype.name)?;
                self.add(datatype.constructors.len())?;
                for constructor in &datatype.constructors {
                    self.text(&constructor.name)?;
                    self.add(constructor.fields.len())?;
                    for field in &constructor.fields {
                        self.text(&field.name)?;
                        self.sort(&field.sort, depth + 1)?;
                    }
                }
                Some(())
            }
            _ => None,
        }
    }

    pub(super) fn proof(&mut self, proof: &Proof) -> Option<()> {
        self.add(proof.steps.len())?;
        // Unlike Vec::clone, HashMap::clone can retain spare buckets.
        self.add(proof.named_steps.capacity())?;
        for name in proof.named_steps.keys() {
            self.text(name)?;
        }
        for step in &proof.steps {
            match step {
                ProofStep::Assume(_) => self.add(1)?,
                ProofStep::Resolution {
                    clause,
                    pivot: _,
                    clause1: _,
                    clause2: _,
                } => {
                    self.add(clause.len())?;
                    self.add(3)?;
                }
                ProofStep::TheoryLemma {
                    theory,
                    clause,
                    farkas,
                    lia,
                    kind: _,
                } => {
                    self.text(theory)?;
                    self.add(clause.len())?;
                    if let Some(hint) = farkas {
                        self.farkas(hint)?;
                    }
                    match lia {
                        Some(LiaAnnotation::CuttingPlane(hint)) => self.farkas(&hint.farkas)?,
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
                        self.text(name)?;
                    }
                    self.add(clause.len())?;
                    self.add(premises.len())?;
                    self.add(args.len())?;
                }
                ProofStep::Anchor {
                    variables,
                    end_step: _,
                } => {
                    self.add(1)?;
                    self.add(variables.len())?;
                    for (name, sort) in variables {
                        self.text(name)?;
                        self.sort(sort, 0)?;
                    }
                }
                // Native certificate payloads were already uncacheable here;
                // unknown future variants cannot claim an unpriced clone.
                _ => return None,
            }
        }
        Some(())
    }

    fn declarations(&mut self, declarations: &[(String, Vec<String>)]) -> Option<()> {
        self.add(declarations.len())?;
        for (name, members) in declarations {
            self.text(name)?;
            self.add(members.len())?;
            for member in members {
                self.text(member)?;
            }
        }
        Some(())
    }

    fn key(&mut self, key: &StrictWalkKey<'_>) -> Option<()> {
        self.declarations(key.datatype_decls)?;
        self.declarations(key.selector_decls)?;
        self.add(key.member_signatures.len())?;
        for member in key.member_signatures {
            self.text(&member.identity)?;
            self.add(member.argument_sorts.len())?;
            for sort in &member.argument_sorts {
                self.sort(sort, 0)?;
            }
            self.sort(&member.result_sort, 0)?;
            self.add(usize::from(member.nullary_term.is_some()))?;
        }
        self.add(key.problem.len())
    }

    fn outcome(&mut self, outcome: &Result<ProofQuality, ProofCheckError>) -> Option<()> {
        match outcome {
            Ok(quality) => self.add(quality.trust_theory_kinds.len()),
            Err(error) => match error {
                ProofCheckError::BundleSchemaMismatch { expected, found } => {
                    self.text(expected)?;
                    self.text(found)
                }
                ProofCheckError::InvalidBooleanRule { rule, reason, .. } => {
                    self.text(rule)?;
                    self.text(reason)
                }
                ProofCheckError::MalformedProofBundle { reason }
                | ProofCheckError::InvalidDatatypeSignatureContext { reason }
                | ProofCheckError::InvalidTheoryLemma { reason, .. }
                | ProofCheckError::StrictProofModeTrust { reason } => self.text(reason),
                ProofCheckError::InvalidResolution { rule, .. }
                | ProofCheckError::UnsupportedResolutionArity { rule, .. }
                | ProofCheckError::MalformedResolutionArgs { rule, .. }
                | ProofCheckError::UnvalidatedRule { rule, .. } => self.text(rule),
                ProofCheckError::ResourceLimit
                | ProofCheckError::Cancelled
                | ProofCheckError::EmptyProof
                | ProofCheckError::UnauthorizedAssumption { .. }
                | ProofCheckError::NoClauseProducingSteps
                | ProofCheckError::MissingPremise { .. }
                | ProofCheckError::NonPriorPremise { .. }
                | ProofCheckError::PremiseHasNoClause { .. }
                | ProofCheckError::InvalidDrup { .. }
                | ProofCheckError::HoleStep { .. }
                | ProofCheckError::FinalClauseNotEmpty { .. }
                | ProofCheckError::TrustStep { .. }
                | ProofCheckError::UnsupportedTheoryLemmaKind { .. } => Some(()),
                _ => None,
            },
        }
    }
}

#[cfg(test)]
fn document(proof: &Proof, limit: usize) -> Option<usize> {
    let mut counter = Counter::new(limit);
    counter.proof(proof)?;
    Some(counter.used)
}

#[cfg(test)]
#[path = "payload_tests.rs"]
mod tests;

pub(super) fn inputs_fit(
    proof: &Proof,
    key: &StrictWalkKey<'_>,
    outcome: Option<&Result<ProofQuality, ProofCheckError>>,
) -> bool {
    let mut counter = Counter::new(STRICT_WALK_MEMO_MAX_PAYLOAD);
    (|| {
        counter.proof(proof)?;
        counter.key(key)?;
        if let Some(outcome) = outcome {
            counter.outcome(outcome)?;
        }
        Some(())
    })()
    .is_some()
}
