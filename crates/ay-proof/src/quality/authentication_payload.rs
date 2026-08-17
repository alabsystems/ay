// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Account the complete dynamic proof/context payload and every reachable
/// term-DAG edge before semantic validation starts. This replaces scalar
/// `terms.len() * constant` guesses with data-dependent charges and provides
/// frequent caller-owned cancellation/deadline polls while walking the input.
pub(super) fn meter_authentication_payload(
    proof: &Proof,
    terms: &TermStore,
    dt_decls: Option<&[(String, Vec<String>)]>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
    datatype_member_signatures: Option<&[DatatypeMemberSignature]>,
    problem_assertions: Option<&[TermId]>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<AuthenticationPayloadStats, ProofCheckError> {
    let mut stats = PayloadStats::default();
    let mut overflow = false;
    let registry = {
        let mut counting_progress = |work: usize, bytes: usize| {
            let Some(next_work) = stats.work.checked_add(work) else {
                overflow = true;
                return false;
            };
            let Some(next_bytes) = stats.bytes.checked_add(bytes) else {
                overflow = true;
                return false;
            };
            stats.work = next_work;
            stats.bytes = next_bytes;
            progress(work, bytes)
        };
        meter_authentication_payload_inner(
            proof,
            terms,
            dt_decls,
            ctor_selectors,
            datatype_member_signatures,
            problem_assertions,
            &mut counting_progress,
        )?
    };
    if overflow {
        Err(ProofCheckError::ResourceLimit)
    } else {
        Ok(AuthenticationPayloadStats {
            aggregate: stats,
            datatype_registry: registry.datatype,
            selector_registry: registry.selectors,
        })
    }
}

fn meter_authentication_payload_inner(
    proof: &Proof,
    terms: &TermStore,
    dt_decls: Option<&[(String, Vec<String>)]>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
    datatype_member_signatures: Option<&[DatatypeMemberSignature]>,
    problem_assertions: Option<&[TermId]>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<RegistryContextStats, ProofCheckError> {
    charge_progress(
        progress,
        proof.steps.len(),
        checked_mul_usize(proof.steps.capacity(), size_of::<ProofStep>())?,
    )?;
    let datatype = match dt_decls {
        Some(declarations) => charge_name_lists(declarations, progress)?,
        None => RegistryPayloadStats::default(),
    };
    let selectors = match ctor_selectors {
        Some(selectors) => charge_name_lists(selectors, progress)?,
        None => RegistryPayloadStats::default(),
    };
    if let Some(signatures) = datatype_member_signatures {
        charge_progress(
            progress,
            signatures.len(),
            checked_mul_usize(signatures.len(), size_of::<DatatypeMemberSignature>())?,
        )?;
        for signature in signatures {
            charge_progress(
                progress,
                checked_add_usize(signature.identity.len(), 1)?,
                checked_add_usize(
                    signature.identity.capacity(),
                    checked_mul_usize(signature.argument_sorts.capacity(), size_of::<Sort>())?,
                )?,
            )?;
            for sort in &signature.argument_sorts {
                meter_sort(sort, progress)?;
            }
            meter_sort(&signature.result_sort, progress)?;
        }
    }

    let mut pending = Vec::new();
    if datatype_member_signatures.is_some() {
        // Typed-context validation scans every term, including terms not
        // reachable from this proof fragment, so meter that exact authority
        // surface before entering the global preflight.
        for index in 0..terms.len() {
            let raw = u32::try_from(index).map_err(|_| ProofCheckError::ResourceLimit)?;
            push_term(&mut pending, TermId::new(raw), progress)?;
        }
    }
    if let Some(assertions) = problem_assertions {
        push_term_slice(&mut pending, assertions, progress)?;
    }

    meter_proof_steps(proof, &mut pending, progress)?;

    meter_reachable_terms(terms, pending, progress)?;
    Ok(RegistryContextStats {
        datatype,
        selectors,
    })
}

fn meter_proof_steps(
    proof: &Proof,
    pending: &mut Vec<TermId>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    for step in &proof.steps {
        charge_progress(progress, 1, 0)?;
        match step {
            ProofStep::Assume(term) => push_term(pending, *term, progress)?,
            ProofStep::Resolution { clause, pivot, .. } => {
                charge_progress(
                    progress,
                    1,
                    checked_mul_usize(clause.capacity(), size_of::<TermId>())?,
                )?;
                push_term_slice(pending, clause, progress)?;
                push_term(pending, *pivot, progress)?;
            }
            ProofStep::TheoryLemma {
                theory,
                clause,
                farkas,
                lia,
                ..
            } => {
                let clause_bytes = checked_mul_usize(clause.capacity(), size_of::<TermId>())?;
                charge_progress(
                    progress,
                    checked_add_usize(theory.len(), 1)?,
                    checked_add_usize(theory.capacity(), clause_bytes)?,
                )?;
                push_term_slice(pending, clause, progress)?;
                if let Some(annotation) = farkas {
                    charge_progress(
                        progress,
                        annotation.coefficients.len(),
                        checked_mul_usize(
                            annotation.coefficients.capacity(),
                            size_of::<num_rational::Rational64>(),
                        )?,
                    )?;
                }
                if let Some(LiaAnnotation::CuttingPlane(annotation)) = lia {
                    charge_progress(
                        progress,
                        annotation.farkas.coefficients.len(),
                        checked_mul_usize(
                            annotation.farkas.coefficients.capacity(),
                            size_of::<num_rational::Rational64>(),
                        )?,
                    )?;
                }
            }
            ProofStep::Step {
                rule,
                clause,
                premises,
                args,
            } => {
                let clause_bytes = checked_mul_usize(clause.capacity(), size_of::<TermId>())?;
                let premise_bytes = checked_mul_usize(premises.capacity(), size_of::<ProofId>())?;
                let arg_bytes = checked_mul_usize(args.capacity(), size_of::<TermId>())?;
                let mut bytes = checked_add_usize(clause_bytes, premise_bytes)?;
                bytes = checked_add_usize(bytes, arg_bytes)?;
                if let AletheRule::Custom(name) = rule {
                    bytes = checked_add_usize(bytes, name.capacity())?;
                }
                let rule_name_work = match rule {
                    AletheRule::Custom(name) => checked_add_usize(name.len(), 1)?,
                    _ => 1,
                };
                charge_progress(progress, rule_name_work, bytes)?;
                push_term_slice(pending, clause, progress)?;
                push_term_slice(pending, args, progress)?;
            }
            ProofStep::Anchor { variables, .. } => {
                charge_progress(
                    progress,
                    variables.len(),
                    checked_mul_usize(variables.capacity(), size_of::<(String, Sort)>())?,
                )?;
                for (name, sort) in variables {
                    charge_progress(progress, checked_add_usize(name.len(), 1)?, name.capacity())?;
                    meter_sort(sort, progress)?;
                }
            }
            _ => charge_progress(progress, 1, 0)?,
        }
    }
    Ok(())
}
