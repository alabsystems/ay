// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact ordered opaque declarations. Serialized rows describe an input;
//! replay authenticates their identity only against real native declarations.

use super::*;

pub(super) fn exported(
    solver: &Solver,
    gaps: &mut Vec<String>,
) -> Vec<NativeReplaySortDeclaration> {
    let context = solver.executor.context();
    solver.native_replay_events.iter().filter_map(|event| {
        let NativeReplayEventKind::DeclareSort { name, core_name } = &event.kind else { return None; };
        if !matches!(context.sort_definition(name), Some(Sort::Uninterpreted(core)) if core == core_name)
            || context.is_live_datatype_carrier(core_name)
            || context.sort_surface_name(core_name) != name
        {
            gaps.push("native opaque sort event lacks its exact live declaration".into());
        }
        Some(NativeReplaySortDeclaration { name: name.clone(), core_name: core_name.clone() })
    }).collect()
}

pub(super) fn validate(artifact: &NativeReplayArtifact) -> Result<(), SolverError> {
    let mut rows = artifact.sort_declarations.iter();
    let mut names = HashSet::default();
    let mut cores = HashSet::default();
    for event in &artifact.events {
        let NativeReplayEventKind::DeclareSort { name, core_name } = &event.kind else {
            continue;
        };
        let row = rows.next().ok_or_else(|| {
            native_replay_artifact_error(
                "native opaque sort event is absent from its ordered header",
            )
        })?;
        if row.name != *name || row.core_name != *core_name {
            return Err(native_replay_artifact_error(
                "opaque sort header differs from its exact ordered declaration event",
            ));
        }
        if name.is_empty()
            || ay_frontend::is_reserved_symbol(name)
            || !names.insert(name.as_str())
            || !cores.insert(core_name.as_str())
            || (name != core_name && !is_allocator_private_datatype_carrier_identity(core_name))
        {
            return Err(native_replay_artifact_error(
                "invalid, duplicate or unauthorized opaque sort identity",
            ));
        }
    }
    if rows.next().is_some() {
        return Err(native_replay_artifact_error(
            "native opaque sort header lacks one ordered declaration event",
        ));
    }
    // Opaque carriers cannot also claim datatype membership. The common remap
    // enforces the same bijection again against newly allocated live carriers.
    for identity in &artifact.symbol_identities {
        if identity
            .datatype_core
            .as_deref()
            .is_some_and(|core| cores.contains(core))
            || identity
                .datatype_surface
                .as_deref()
                .is_some_and(|name| names.contains(name))
        {
            return Err(native_replay_artifact_error(
                "opaque sort identity also claims datatype provenance",
            ));
        }
    }
    for event in &artifact.events {
        if event
            .kind
            .datatypes()
            .iter()
            .any(|datatype| names.contains(datatype.name.as_str()))
        {
            return Err(native_replay_artifact_error(
                "opaque sort name also declares a datatype",
            ));
        }
    }
    Ok(())
}

pub(super) fn replay(
    solver: &mut Solver,
    name: &str,
    old_core: &str,
    remap: &mut NativeReplayIdentityRemap,
) -> Result<(), SolverError> {
    solver.try_declare_opaque_sort(name)?;
    let context = solver.executor.context();
    let Some(Sort::Uninterpreted(new_core)) = context.sort_definition(name) else {
        return Err(native_replay_artifact_error(
            "rebuilt opaque sort lacks its actual nominal carrier",
        ));
    };
    if context.is_live_datatype_carrier(new_core) || context.sort_surface_name(new_core) != name {
        return Err(native_replay_artifact_error(
            "rebuilt opaque declaration has inconsistent nominal provenance",
        ));
    }
    remap.insert_carrier(old_core, new_core)
}
