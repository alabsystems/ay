// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Free-variable identity checks for native replay artifacts.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::TermId;

use super::{
    final_check_sat_assumptions, is_allocator_private_declaration_identity,
    native_replay_artifact_error, native_replay_term_error, NativeReplayArtifact,
    NativeReplaySymbolKind, NativeReplayTermNode, SolverError, NATIVE_REPLAY_BINDER_SCAN_BUDGET,
};

/// Validate constant identities and return their public names for the later
/// constant/function namespace collision check.
pub(super) fn validate_constant_identities<'a>(
    artifact: &'a NativeReplayArtifact,
    nodes: &HashMap<TermId, &NativeReplayTermNode>,
) -> Result<HashSet<&'a str>, SolverError> {
    let mut declaration_terms = HashSet::default();
    let mut declaration_names = HashSet::default();
    let mut declaration_core_names = HashSet::default();
    for declaration in &artifact.declarations {
        if !declaration_terms.insert(declaration.term) {
            return Err(native_replay_artifact_error(format!(
                "duplicate declaration for term {}",
                declaration.term.0
            )));
        }
        if !declaration_names.insert(declaration.name.as_str()) {
            return Err(native_replay_artifact_error(format!(
                "duplicate native constant declaration name `{}`",
                declaration.name
            )));
        }
        if ay_frontend::is_reserved_symbol(&declaration.name) {
            return Err(native_replay_artifact_error(format!(
                "native constant declaration name `{}` is reserved",
                declaration.name
            )));
        }
        if !declaration_core_names.insert(declaration.core_name.as_str()) {
            return Err(native_replay_artifact_error(format!(
                "duplicate native constant core identity `{}`",
                declaration.core_name
            )));
        }
        if declaration.core_name != declaration.name
            && !is_allocator_private_declaration_identity(&declaration.core_name)
        {
            return Err(native_replay_artifact_error(format!(
                "declaration `{}` claims an unauthorized private core identity `{}`",
                declaration.name, declaration.core_name
            )));
        }
        let Some(node) = nodes.get(&declaration.term) else {
            return Err(native_replay_artifact_error(format!(
                "declaration `{}` references missing term {}",
                declaration.name, declaration.term.0
            )));
        };
        let TermData::Var(node_name, _) = &node.data else {
            return Err(native_replay_artifact_error(format!(
                "declaration `{}` targets non-variable term {}",
                declaration.name, declaration.term.0
            )));
        };
        if node_name != &declaration.core_name {
            return Err(native_replay_artifact_error(format!(
                "declaration `{}` records core identity `{}`, but term {} uses `{node_name}`",
                declaration.name, declaration.core_name, declaration.term.0
            )));
        }
        if node.is_datatype_constructor {
            return Err(native_replay_artifact_error(format!(
                "term {} cannot be both a native constant and a datatype constructor",
                declaration.term.0
            )));
        }
    }
    reject_unmarked_constructor_core_collisions(artifact, nodes, &declaration_terms)?;
    Ok(declaration_names)
}

/// Reject a flag-false Var that claims a live nullary-constructor core unless
/// every reachable occurrence is protected by a matching lexical binder.
fn reject_unmarked_constructor_core_collisions(
    artifact: &NativeReplayArtifact,
    nodes: &HashMap<TermId, &NativeReplayTermNode>,
    declaration_terms: &HashSet<TermId>,
) -> Result<(), SolverError> {
    let mut candidates = HashMap::default();
    for node in &artifact.terms {
        let TermData::Var(core_name, _) = &node.data else {
            continue;
        };
        if node.is_datatype_constructor || declaration_terms.contains(&node.id) {
            continue;
        }
        if artifact.symbol_identities.iter().any(|identity| {
            identity.core_name == *core_name
                && identity.kind == NativeReplaySymbolKind::DatatypeConstructor
                && identity.api_domain.is_empty()
                && identity.engine_domain.is_empty()
                && identity.engine_range == node.sort
        }) {
            candidates.insert(node.id, (core_name.clone(), node.sort.clone()));
        }
    }
    if candidates.is_empty() {
        return Ok(());
    }
    reject_free_candidate_occurrences(artifact, nodes, &candidates)
}

#[derive(Default)]
struct LexicalScope {
    parent: Option<usize>,
    bindings: Vec<(String, ay_core::Sort)>,
}

fn reject_free_candidate_occurrences(
    artifact: &NativeReplayArtifact,
    nodes: &HashMap<TermId, &NativeReplayTermNode>,
    candidates: &HashMap<TermId, (String, ay_core::Sort)>,
) -> Result<(), SolverError> {
    let mut roots = artifact
        .assertions
        .iter()
        .map(|assertion| assertion.term)
        .collect::<Vec<_>>();
    if let Some(assumptions) = final_check_sat_assumptions(&artifact.events) {
        roots.extend_from_slice(assumptions);
    }
    let mut scopes = Vec::<LexicalScope>::new();
    let mut pending = roots
        .iter()
        .copied()
        .map(|root| (root, None))
        .collect::<Vec<_>>();
    let mut seen = HashSet::default();
    let mut reached = HashSet::default();
    let mut work = 0usize;
    while let Some((term, scope)) = pending.pop() {
        if !seen.insert((term, scope)) {
            continue;
        }
        work += 1;
        if work > NATIVE_REPLAY_BINDER_SCAN_BUDGET {
            return Err(native_replay_artifact_error(format!(
                "constructor-collision validation exceeds {NATIVE_REPLAY_BINDER_SCAN_BUDGET} aggregate work units"
            )));
        }
        let node = nodes.get(&term).ok_or_else(|| {
            native_replay_term_error(term, format!("references missing term {}", term.0))
        })?;
        match node.data.clone() {
            TermData::Const(_) => {}
            TermData::Var(_, _) => {
                if let Some((name, sort)) = candidates.get(&term) {
                    reached.insert(term);
                    if !is_bound_by_scope(&scopes, scope, name, sort) {
                        return Err(native_replay_artifact_error(format!(
                            "free variable term {} reuses nullary datatype-constructor identity `{name}`",
                            term.0
                        )));
                    }
                }
            }
            TermData::App(_, args) => pending.extend(args.into_iter().map(|arg| (arg, scope))),
            TermData::Not(inner) => pending.push((inner, scope)),
            TermData::Ite(condition, then_term, else_term) => {
                pending.extend([condition, then_term, else_term].map(|child| (child, scope)));
            }
            TermData::Let(bindings, body) => {
                pending.extend(bindings.iter().map(|(_, value)| (*value, scope)));
                let mut scoped_bindings = Vec::with_capacity(bindings.len());
                for (name, value) in bindings {
                    let value = nodes.get(&value).ok_or_else(|| {
                        native_replay_term_error(
                            term,
                            format!("let binding references missing term {}", value.0),
                        )
                    })?;
                    scoped_bindings.push((name, value.sort.clone()));
                }
                let nested = push_scope(&mut scopes, scope, scoped_bindings);
                pending.push((body, Some(nested)));
            }
            TermData::Forall(bindings, body, triggers)
            | TermData::Exists(bindings, body, triggers) => {
                let nested = push_scope(&mut scopes, scope, bindings);
                pending.push((body, Some(nested)));
                pending.extend(
                    triggers
                        .into_iter()
                        .flatten()
                        .map(|trigger| (trigger, Some(nested))),
                );
            }
            _ => {
                return Err(native_replay_term_error(
                    term,
                    "constructor-collision validation encountered an unsupported future term kind",
                ));
            }
        }
    }
    if let Some((&term, (name, _))) = candidates.iter().find(|(term, _)| !reached.contains(*term)) {
        return Err(native_replay_artifact_error(format!(
            "unreachable variable term {} reuses nullary datatype-constructor identity `{name}`",
            term.0
        )));
    }
    Ok(())
}

fn push_scope(
    scopes: &mut Vec<LexicalScope>,
    parent: Option<usize>,
    bindings: Vec<(String, ay_core::Sort)>,
) -> usize {
    let id = scopes.len();
    scopes.push(LexicalScope { parent, bindings });
    id
}

fn is_bound_by_scope(
    scopes: &[LexicalScope],
    mut scope: Option<usize>,
    name: &str,
    sort: &ay_core::Sort,
) -> bool {
    while let Some(id) = scope {
        let frame = &scopes[id];
        if let Some((_, binder_sort)) = frame
            .bindings
            .iter()
            .rev()
            .find(|(binder, _)| binder == name)
        {
            return binder_sort == sort;
        }
        scope = frame.parent;
    }
    false
}
