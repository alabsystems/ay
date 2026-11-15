// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact witness/declaration namespace and full-arena freshness checks.

use super::meter::{id_map_entry, invalid_named};
use super::*;

pub(super) fn build_bundle_registry<'a>(
    bindings: &'a [SkolemBinding],
    declaration_term_symbols: &HashMap<String, &'static str>,
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<BundleRegistry<'a>, ProofCheckError> {
    let Some(fallback_step) = bindings.first().map(|binding| binding.step) else {
        return Err(
            meter.invalid("bundle registry requires at least one authenticated Skolem binding")?
        );
    };
    let mut registry = BundleRegistry {
        by_name: HashMap::default(),
        binding_by_witness: HashMap::default(),
        fallback_step,
    };
    for binding in bindings {
        // Unlike our grow-only registries, this borrowed table can contain
        // tombstones. Its allocation bounds the raw bucket count even when
        // len/capacity were reduced by deletions. No table scan is necessary.
        let declaration_slots = declaration_term_symbols.allocation_size()
            / std::mem::size_of::<(String, &'static str)>();
        meter.lookup(&binding.name, declaration_slots)?;
        if let Some(role) = declaration_term_symbols.get(&binding.name) {
            return Err(invalid_named(meter, binding.step, "Skolem symbol collides in the serialized datatype declaration-owned term namespace", &[&binding.name, role])?);
        }
        meter.name_map_entry(&registry.by_name, &binding.name)?;
        meter.owned_name(&binding.name)?;
        if registry
            .by_name
            .insert(binding.name.clone(), binding.witness)
            .is_some()
        {
            return Err(invalid_named(
                meter,
                binding.step,
                "Skolem symbol name is shared by witnesses",
                &[&binding.name],
            )?);
        }
        id_map_entry(meter, &registry.binding_by_witness, binding.witness)?;
        registry.binding_by_witness.insert(binding.witness, binding);
    }
    meter.charge(0, 0)?;
    Ok(registry)
}

fn check_global_name(
    registry: &BundleRegistry<'_>,
    term: TermId,
    name: &str,
    role: &str,
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<(), ProofCheckError> {
    meter.lookup(name, registry.by_name.len())?;
    let Some(&witness) = registry.by_name.get(name) else {
        return Ok(());
    };
    if term == witness && role == "atomic witness" {
        return Ok(());
    }
    meter.lookup("", registry.binding_by_witness.len())?;
    let Some(binding) = registry.binding_by_witness.get(&witness).copied() else {
        return Err(meter.invalid("Skolem name registry references an unknown witness")?);
    };
    Err(invalid_named(
        meter,
        binding.step,
        "Skolem symbol is not globally fresh",
        &[name, role],
    )?)
}

pub(super) fn validate_global_name_freshness(
    terms: &TermStore,
    registry: &BundleRegistry<'_>,
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<(), ProofCheckError> {
    // This is deliberately a FULL arena scan, not merely a proof-root walk.
    for index in 0..terms.len() {
        let term = TermId::new(u32::try_from(index).map_err(|_| ProofCheckError::ResourceLimit)?);
        match meter.term(terms, term)? {
            TermData::Var(name, _) => {
                check_global_name(registry, term, name, "atomic witness", meter)?
            }
            TermData::App(symbol, _) => {
                check_global_name(registry, term, symbol.name(), "an application head", meter)?
            }
            TermData::Let(bindings, _) => {
                for (name, _) in bindings {
                    check_global_name(registry, term, name, "a let binder", meter)?;
                }
            }
            TermData::Forall(vars, _, _) | TermData::Exists(vars, _, _) => {
                for (name, _) in vars {
                    check_global_name(registry, term, name, "a quantifier binder", meter)?;
                }
            }
            TermData::Const(..) | TermData::Not(..) | TermData::Ite(..) => {}
            _ => return Err(ProofCheckError::ResourceLimit),
        }
    }
    meter.charge(0, 0)
}
