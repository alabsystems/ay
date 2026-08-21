// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

pub(crate) fn validate_step(
    terms: &TermStore,
    derived_clauses: &mut Vec<Option<Vec<TermId>>>,
    step_id: ProofId,
    step: &ProofStep,
    strict: bool,
    // When `Some` AND a strict `AletheRule::Trust` step is encountered, the step
    // is DEFERRED (its clause is collected here and admitted as an axiom) instead
    // of being rejected. The collected clauses MUST be independently discharged
    // by the caller; this is never an unconditional accept.
    trust_collector: Option<&mut Vec<(ProofId, Vec<TermId>)>>,
) -> Result<(), ProofCheckError> {
    validate_step_with_datatypes(
        terms,
        derived_clauses,
        step_id,
        step,
        strict,
        None,
        None,
        None,
        None,
        None,
        None,
        trust_collector,
    )
}

/// As [`validate_step`], but with the datatype constructor registry threaded in
/// so strict mode can validate `TheoryLemmaKind::DatatypeDistinct` lemmas.
///
/// Runtime datatype terms carry `Sort::Uninterpreted`, so the checker cannot
/// recover constructor membership from the `TermStore` alone — the executor
/// supplies the `declare-datatype` declarations explicitly. When `dt_decls` is
/// `None`, datatype-distinctness lemmas fail closed in strict mode.
///
/// `datatype_member_signatures.is_some()` is only a dispatch marker here. The
/// caller MUST have run [`validate_datatype_signature_context`] over this exact
/// `TermStore` and exact registry slices first. This covers both datatype
/// lemmas and finite-array schemas over an enum index. All production callers
/// satisfy that precondition through the public typed whole-proof entry points;
/// direct calls are crate-private validator-shape tests and confer no proof
/// authority.
#[allow(clippy::too_many_arguments)]
pub(crate) fn validate_step_with_datatypes(
    terms: &TermStore,
    derived_clauses: &mut Vec<Option<Vec<TermId>>>,
    step_id: ProofId,
    step: &ProofStep,
    strict: bool,
    dt_decls: Option<datatype_axiom::DatatypeDecls<'_>>,
    ctor_selectors: Option<datatype_axiom::SelectorDecls<'_>>,
    datatype_member_signatures: Option<&[DatatypeMemberSignature]>,
    // Whole-proof extensionality diff-witness provenance, built once by the
    // caller from the proof's `array_ext_diff_intro` steps and the PROBLEM's
    // assertions. `None` (no problem assertion set available) keeps
    // `TheoryLemmaKind::ArrayExtensionality` fail-closed.
    ext_diff: Option<&ExtDiffRegistry>,
    // Problem-derived registry of sets asserted empty; `None` keeps
    // `SetCardEmptyByAssertion` fail-closed.
    empty_sets: Option<&EmptySetRegistry>,
    // Whole-proof registry of fresh-symbol definitional extensions, built once
    // by the caller from the proof's `fresh_def_bound` steps. `None` means no
    // caller vetted them, and a strict `fresh_def_bound` step is then rejected
    // — the registry, not the step, is where freshness is decided.
    fresh_defs: Option<&FreshDefRegistry>,
    // Deferred-trust recovery (see [`validate_step`]): when `Some`, a strict
    // `Trust` step is collected for independent discharge instead of rejected.
    trust_collector: Option<&mut Vec<(ProofId, Vec<TermId>)>>,
) -> Result<(), ProofCheckError> {
    let mut unbounded = |_: usize, _: usize| true;
    validate_step_with_datatypes_and_progress(
        terms,
        derived_clauses,
        step_id,
        step,
        strict,
        dt_decls,
        ctor_selectors,
        datatype_member_signatures,
        ext_diff,
        empty_sets,
        fresh_defs,
        trust_collector,
        &mut unbounded,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn validate_step_with_datatypes_and_progress(
    terms: &TermStore,
    derived_clauses: &mut Vec<Option<Vec<TermId>>>,
    step_id: ProofId,
    step: &ProofStep,
    strict: bool,
    dt_decls: Option<datatype_axiom::DatatypeDecls<'_>>,
    ctor_selectors: Option<datatype_axiom::SelectorDecls<'_>>,
    datatype_member_signatures: Option<&[DatatypeMemberSignature]>,
    ext_diff: Option<&ExtDiffRegistry>,
    empty_sets: Option<&EmptySetRegistry>,
    fresh_defs: Option<&FreshDefRegistry>,
    trust_collector: Option<&mut Vec<(ProofId, Vec<TermId>)>>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    debug_assert_eq!(
        step_id.0 as usize,
        derived_clauses.len(),
        "BUG: step_id {} does not match derived_clauses index {}",
        step_id.0,
        derived_clauses.len()
    );
    match step {
        ProofStep::Assume(term) => derived_clauses.push(Some(vec![*term])),
        ProofStep::TheoryLemma {
            clause,
            kind,
            farkas,
            lia,
            ..
        } => validate_theory_lemma(
            terms,
            derived_clauses,
            step_id,
            clause,
            farkas.as_ref(),
            *kind,
            lia.as_ref(),
            strict,
            dt_decls,
            ctor_selectors,
            datatype_member_signatures,
            ext_diff,
            empty_sets,
            trust_collector,
            progress,
        )?,
        ProofStep::Step {
            rule: AletheRule::FreshDefBound,
            clause,
            premises,
            args,
        } => derived_clauses.push(Some(validate_fresh_def_bound_step(
            terms, step_id, clause, premises, args, strict, fresh_defs,
        )?)),
        // An `array_ext_diff_intro` is a DEFINITION, not an inference: it
        // records that a fresh symbol is the extensionality difference witness
        // for one array pair. It is validated for shape here and recorded as
        // producing NO clause (like an `anchor`), so it can never be resolved
        // against, never seed a RUP check, and never be mistaken for a derived
        // empty clause. The provenance conditions that make it MEAN anything
        // (freshness, bound-once) are whole-proof and live in
        // `ExtDiffRegistry::collect`.
        ProofStep::Step {
            rule: AletheRule::ArrayExtDiffIntro,
            clause,
            premises,
            args,
        } => {
            let _binding =
                array_axiom::validate_ext_diff_intro(terms, step_id, clause, premises, args)?;
            derived_clauses.push(None);
        }
        ProofStep::Resolution {
            clause,
            pivot,
            clause1,
            clause2,
        } => validate_resolution_step(
            terms,
            derived_clauses,
            step_id,
            clause,
            *pivot,
            *clause1,
            *clause2,
        )?,
        ProofStep::Step {
            rule,
            clause,
            premises,
            args,
        } => validate_alethe_step(
            terms,
            derived_clauses,
            step_id,
            rule,
            clause,
            premises,
            args,
            strict,
            trust_collector,
            progress,
        )?,
        ProofStep::Anchor { .. } => derived_clauses.push(None),
        _ => unreachable!("unexpected ProofStep variant"),
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn validate_alethe_step(
    terms: &TermStore,
    derived_clauses: &mut Vec<Option<Vec<TermId>>>,
    step_id: ProofId,
    rule: &AletheRule,
    clause: &[TermId],
    premises: &[ProofId],
    args: &[TermId],
    strict: bool,
    mut trust_collector: Option<&mut Vec<(ProofId, Vec<TermId>)>>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    // `Hole` belongs here alongside `Trust`. AY treats the two as one family:
    // a hole carries an obligation, not a placeholder. In deferred-trust mode
    // collect that obligation; plain strict mode keeps it a hard rejection.
    let deferrable = strict && matches!(rule, AletheRule::Trust | AletheRule::Hole);
    if deferrable {
        match &mut trust_collector {
            Some(collector) => collector.push((step_id, clause.to_vec())),
            None => {
                // Same triage disclosure as `GENERIC lemma declined` below:
                // the typed error names only the step id, but the CLAUSE the
                // trust step asserts is the one fact a strict-decline triage
                // needs to route the fix (missing repair lane vs producer
                // defect). Gated on the typed `--debug-cert` carrier.
                if ay_core::misc_cli_flags().debug_cert {
                    let rendered: Vec<String> = clause
                        .iter()
                        .map(|&t| crate::format_term_alethe(terms, t))
                        .collect();
                    ay_core::safe_eprintln!(
                        "c !! TRUST step rejected at {step_id:?} rule={rule:?} clause=[{}]",
                        rendered.join(" | ")
                    );
                }
                return Err(match rule {
                    AletheRule::Hole => ProofCheckError::HoleStep { step: step_id },
                    _ => ProofCheckError::TrustStep { step: step_id },
                });
            }
        }
    }
    validate_generic_step(
        terms,
        derived_clauses,
        step_id,
        rule,
        clause,
        premises,
        args,
        strict,
        // Only a hole that was collected may skip its own rejection.
        deferrable && trust_collector.is_some(),
        progress,
    )
}
