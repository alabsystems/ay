// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authenticate every Skolem step and retain one-to-one source/witness bindings.

use super::meter::{id_map_entry, invalid_named, proof_id};
use super::*;

pub(super) fn collect_skolem_bindings(
    proof: &Proof,
    terms: &TermStore,
    authority: SkolemWitnessAuthority,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<Vec<SkolemBinding>, ProofCheckError> {
    if proof.steps.len() > u32::MAX as usize {
        return Err(ProofCheckError::ResourceLimit);
    }
    let mut source_to_witness = HashMap::<TermId, (TermId, ProofId)>::default();
    let mut witness_to_source = HashMap::<TermId, (TermId, ProofId)>::default();
    let mut bindings = Vec::new();
    let mut work = 0usize;
    for (index, proof_step) in proof.steps.iter().enumerate() {
        let step = proof_id(index)?;
        QuantifierMeter::new(step, "sko_forall", &mut work, progress).charge(1, 0)?;
        let ProofStep::Step {
            rule: AletheRule::Skolem,
            clause,
            premises,
            args,
        } = proof_step
        else {
            continue;
        };
        validate_sko_forall_with_authority_and_progress(
            terms,
            step,
            clause,
            premises.len(),
            args,
            authority,
            &mut work,
            progress,
        )?;
        let mut meter = QuantifierMeter::new(step, "sko_forall", &mut work, progress);
        let [equality] = clause.as_slice() else {
            return Err(meter.invalid("validated Skolem step lost its single conclusion literal")?);
        };
        let TermData::App(Symbol::Named(name), equality_args) = meter.term(terms, *equality)?
        else {
            return Err(meter.invalid("validated Skolem step lost its equality source")?);
        };
        meter.name(name)?;
        let [source, _] = equality_args.as_slice() else {
            return Err(meter.invalid("validated Skolem step lost its equality source")?);
        };
        if name != "=" {
            return Err(meter.invalid("validated Skolem step lost its equality source")?);
        }
        let [witness] = args.as_slice() else {
            return Err(meter.invalid("validated Skolem step lost its single witness argument")?);
        };
        let TermData::Var(name, _) = meter.term(terms, *witness)? else {
            return Err(meter.invalid("validated Skolem witness is no longer atomic")?);
        };
        id_map_entry(&mut meter, &source_to_witness, *source)?;
        if source_to_witness
            .insert(*source, (*witness, step))
            .is_some()
        {
            return Err(invalid_named(
                &mut meter,
                step,
                "forall source was already bound to a witness",
                &[name],
            )?);
        }
        id_map_entry(&mut meter, &witness_to_source, *witness)?;
        if witness_to_source
            .insert(*witness, (*source, step))
            .is_some()
        {
            return Err(invalid_named(
                &mut meter,
                step,
                "Skolem witness was already bound to a forall source",
                &[name],
            )?);
        }
        meter.queue_room(&bindings)?;
        meter.owned_name(name)?;
        meter.push(
            &mut bindings,
            SkolemBinding {
                step,
                source: *source,
                witness: *witness,
                name: name.clone(),
            },
        )?;
    }
    QuantifierMeter::new(ProofId(0), "sko_forall", &mut work, progress).charge(0, 0)?;
    Ok(bindings)
}
