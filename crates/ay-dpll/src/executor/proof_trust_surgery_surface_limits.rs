// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded source-tree and dynamic-printer policy for retained surfaces.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, ProofStep, TermId, TheoryLemmaKind};
use ay_frontend::command::{
    Constant as FrontendConstant, Index as FrontendIndex, MatchPattern as FrontendMatchPattern,
    QualifiedIdentifier as FrontendQualifiedIdentifier, Sort as FrontendSort, Term as FrontendTerm,
};
use ay_frontend::SExpr;

pub(in crate::executor) use super::source_work::{ProofSourcePass, ProofSourceWorkEnvelope};

#[path = "proof_trust_surgery_surface_payload.rs"]
mod payload;
pub(in crate::executor) use payload::render_roots_have_bounded_payload;

#[cfg(test)]
#[path = "proof_trust_surgery_surface_limits_tests.rs"]
mod tests;

const MAX_SURFACE_NODES: usize = 8_192;
pub(super) const MAX_SURFACE_DEPTH: usize = 256;
pub(super) const MAX_REQUIREMENT_BYTES: usize = 8 * 1024 * 1024;
pub(super) const MAX_AGGREGATE_SOURCE_WORK: usize = 32 * 1024 * 1024;

/// Return child arity without cloning the term's child vector.
pub(in crate::executor) fn term_child_count(
    terms: &ay_core::TermStore,
    term: TermId,
) -> Option<usize> {
    Some(match terms.get(term) {
        TermData::Const(_) | TermData::Var(..) => 0,
        TermData::App(_, args) => args.len(),
        TermData::Let(bindings, _) => bindings.len().checked_add(1)?,
        TermData::Not(_) => 1,
        TermData::Ite(..) => 3,
        TermData::Forall(..) | TermData::Exists(..) => 1,
        _ => return None,
    })
}

fn constant_bytes(constant: &FrontendConstant) -> Option<usize> {
    Some(match constant {
        FrontendConstant::True => 4,
        FrontendConstant::False => 5,
        FrontendConstant::Numeral(value)
        | FrontendConstant::Decimal(value)
        | FrontendConstant::Hexadecimal(value)
        | FrontendConstant::Binary(value) => value.len(),
        FrontendConstant::String(value) => value.len().checked_add(2)?,
        _ => return None,
    })
}

fn indices_bytes(indices: &[FrontendIndex]) -> Option<usize> {
    indices.iter().try_fold(0usize, |bytes, index| {
        bytes.checked_add(index.text().len().saturating_add(1))
    })
}

fn qualified_identifier_bytes(identifier: &FrontendQualifiedIdentifier) -> Option<usize> {
    match identifier {
        FrontendQualifiedIdentifier::Symbol(name) => Some(name.len()),
        FrontendQualifiedIdentifier::Indexed(name, indices) => name
            .len()
            .checked_add(indices_bytes(indices)?)
            .and_then(|bytes| bytes.checked_add(4)),
        _ => None,
    }
}

/// Estimate the bounded aggregate work of rendering every surface subtree.
pub(in crate::executor) fn surface_source_work(root: &FrontendTerm) -> Option<usize> {
    enum SurfaceNode<'a> {
        Term(&'a FrontendTerm, usize),
        Sort(&'a FrontendSort, usize),
        SExpr(&'a SExpr, usize),
    }

    let mut pending = vec![SurfaceNode::Term(root, 0usize)];
    let mut visited = 0usize;
    let mut source_bytes = 0usize;
    let mut max_depth = 0usize;
    while let Some(node) = pending.pop() {
        visited += 1;
        let depth = match &node {
            SurfaceNode::Term(_, depth)
            | SurfaceNode::Sort(_, depth)
            | SurfaceNode::SExpr(_, depth) => *depth,
        };
        if visited > MAX_SURFACE_NODES || depth > MAX_SURFACE_DEPTH {
            return None;
        }
        max_depth = max_depth.max(depth);
        let local_bytes = match node {
            SurfaceNode::Term(term, depth) => match term {
                FrontendTerm::Const(constant) => constant_bytes(constant),
                FrontendTerm::Symbol(symbol) => Some(symbol.len()),
                FrontendTerm::App(operator, args) | FrontendTerm::IndexedApp(operator, _, args) => {
                    if visited
                        .saturating_add(pending.len())
                        .saturating_add(args.len())
                        > MAX_SURFACE_NODES
                    {
                        return None;
                    }
                    for child in args {
                        pending.push(SurfaceNode::Term(child, depth + 1));
                    }
                    let head_bytes = match term {
                        FrontendTerm::IndexedApp(_, indices, _) => indices_bytes(indices)
                            .and_then(|bytes| operator.len().checked_add(bytes))
                            .and_then(|bytes| bytes.checked_add(4)),
                        _ => Some(operator.len()),
                    };
                    head_bytes.and_then(|bytes| bytes.checked_add(args.len().saturating_add(2)))
                }
                FrontendTerm::QualifiedApp(identifier, sort, args) => {
                    if visited
                        .saturating_add(pending.len())
                        .saturating_add(args.len())
                        .saturating_add(1)
                        > MAX_SURFACE_NODES
                    {
                        return None;
                    }
                    for child in args {
                        pending.push(SurfaceNode::Term(child, depth + 1));
                    }
                    pending.push(SurfaceNode::Sort(sort, depth + 1));
                    qualified_identifier_bytes(identifier)
                        .and_then(|bytes| bytes.checked_add(args.len().saturating_add(7)))
                }
                FrontendTerm::Let(bindings, body) => {
                    if visited
                        .saturating_add(pending.len())
                        .saturating_add(bindings.len())
                        .saturating_add(1)
                        > MAX_SURFACE_NODES
                    {
                        return None;
                    }
                    pending.push(SurfaceNode::Term(body, depth + 1));
                    let mut bytes = 7usize;
                    for (name, value) in bindings {
                        pending.push(SurfaceNode::Term(value, depth + 1));
                        bytes = bytes.checked_add(name.len().saturating_add(3))?;
                    }
                    Some(bytes)
                }
                FrontendTerm::Forall(bindings, body)
                | FrontendTerm::Exists(bindings, body)
                | FrontendTerm::Lambda(bindings, body) => {
                    if visited
                        .saturating_add(pending.len())
                        .saturating_add(bindings.len())
                        .saturating_add(1)
                        > MAX_SURFACE_NODES
                    {
                        return None;
                    }
                    pending.push(SurfaceNode::Term(body, depth + 1));
                    let mut bytes = 10usize;
                    for (name, sort) in bindings {
                        pending.push(SurfaceNode::Sort(sort, depth + 1));
                        bytes = bytes.checked_add(name.len().saturating_add(3))?;
                    }
                    Some(bytes)
                }
                FrontendTerm::Match(scrutinee, cases) => {
                    if visited
                        .saturating_add(pending.len())
                        .saturating_add(cases.len())
                        .saturating_add(1)
                        > MAX_SURFACE_NODES
                    {
                        return None;
                    }
                    pending.push(SurfaceNode::Term(scrutinee, depth + 1));
                    let mut bytes = 10usize;
                    for (pattern, body) in cases {
                        pending.push(SurfaceNode::Term(body, depth + 1));
                        let pattern_bytes = match pattern {
                            FrontendMatchPattern::Symbol(name) => Some(name.len()),
                            FrontendMatchPattern::Constructor(name, variables) => variables
                                .iter()
                                .try_fold(name.len().saturating_add(2), |bytes, variable| {
                                    bytes.checked_add(variable.len().saturating_add(1))
                                }),
                            _ => None,
                        };
                        bytes = pattern_bytes.and_then(|pattern_bytes| {
                            bytes.checked_add(pattern_bytes.saturating_add(3))
                        })?;
                    }
                    Some(bytes)
                }
                // Collectors strip annotations before rendering, but every
                // parsed-source snapshot still clones their complete payload.
                FrontendTerm::Annotated(body, annotations) => {
                    if visited
                        .saturating_add(pending.len())
                        .saturating_add(annotations.len())
                        .saturating_add(1)
                        > MAX_SURFACE_NODES
                    {
                        return None;
                    }
                    pending.push(SurfaceNode::Term(body, depth + 1));
                    let mut bytes = 0usize;
                    for (name, value) in annotations {
                        pending.push(SurfaceNode::SExpr(value, depth + 1));
                        bytes = bytes.checked_add(name.len().saturating_add(1))?;
                    }
                    Some(bytes)
                }
                _ => None,
            },
            SurfaceNode::Sort(sort, depth) => match sort {
                FrontendSort::Simple(name) => Some(name.len()),
                FrontendSort::Parameterized(name, parameters) => {
                    if visited
                        .saturating_add(pending.len())
                        .saturating_add(parameters.len())
                        > MAX_SURFACE_NODES
                    {
                        return None;
                    }
                    for parameter in parameters {
                        pending.push(SurfaceNode::Sort(parameter, depth + 1));
                    }
                    name.len().checked_add(parameters.len().saturating_add(2))
                }
                FrontendSort::Indexed(name, indices) => indices_bytes(indices)
                    .and_then(|bytes| name.len().checked_add(bytes))
                    .and_then(|bytes| bytes.checked_add(4)),
                _ => None,
            },
            SurfaceNode::SExpr(sexpr, depth) => match sexpr {
                SExpr::Symbol(value)
                | SExpr::Keyword(value)
                | SExpr::Numeral(value)
                | SExpr::Decimal(value)
                | SExpr::Hexadecimal(value)
                | SExpr::Binary(value) => Some(value.len()),
                SExpr::String(value) => value.len().checked_mul(2).and_then(|n| n.checked_add(2)),
                SExpr::True => Some(4),
                SExpr::False => Some(5),
                SExpr::List(items) => {
                    if visited
                        .saturating_add(pending.len())
                        .saturating_add(items.len())
                        > MAX_SURFACE_NODES
                    {
                        return None;
                    }
                    for item in items {
                        pending.push(SurfaceNode::SExpr(item, depth + 1));
                    }
                    Some(items.len().saturating_add(2))
                }
                _ => None,
            },
        };
        let local_bytes = local_bytes?;
        let next = source_bytes.checked_add(local_bytes)?;
        source_bytes = next;
    }
    // Every token can occur in each formatted ancestor, and both the ordinary
    // and deep collectors may render it. The factor of four also covers
    // quoting/parenthesis expansion without constructing those strings.
    source_bytes
        .checked_mul(max_depth.saturating_add(1))
        .and_then(|bytes| bytes.checked_mul(4))
        .filter(|&bytes| bytes <= MAX_REQUIREMENT_BYTES)
}

/// Bound recursive collectors before they allocate one rendering per surface
/// subtree or clone a parsed body. Annotation payloads are charged even though
/// collectors strip them, because parsed-source snapshots clone them first.
pub(in crate::executor) fn surface_source_is_bounded(root: &FrontendTerm) -> bool {
    surface_source_work(root).is_some()
}

/// Cost of one complete pass over a parsed source stack, or `None` when the
/// stack is unbounded or a single pass over it already exceeds the aggregate
/// ceiling. Repeated entries are charged because downstream snapshots clone
/// them independently.
pub(in crate::executor) fn surface_pass_work<'a>(
    roots: impl IntoIterator<Item = &'a FrontendTerm>,
) -> Option<usize> {
    roots.into_iter().try_fold(0usize, |used, root| {
        used.checked_add(surface_source_work(root)?.max(1))
            .filter(|&next| next <= MAX_AGGREGATE_SOURCE_WORK)
    })
}

/// Preflight a complete parsed source stack before any recursive AST clone or
/// formatter runs. Repeated entries are charged because downstream snapshots
/// clone them independently.
pub(in crate::executor) fn surface_sources_have_bounded_work<'a>(
    roots: impl IntoIterator<Item = &'a FrontendTerm>,
) -> bool {
    surface_pass_work(roots).is_some()
}

/// Validate the complete root-to-leaf depth of every term the recursive
/// Alethe formatter will visit. Heights are memoized exactly, so a shared DAG
/// tail first seen below a shallow root cannot hide a deeper later path.
pub(super) fn render_roots_have_bounded_depth(
    terms: &ay_core::TermStore,
    roots: &[TermId],
    max_terms: usize,
    max_work: usize,
) -> bool {
    fn height(
        terms: &ay_core::TermStore,
        term: TermId,
        depth: usize,
        memo: &mut HashMap<TermId, usize>,
        active: &mut HashSet<TermId>,
        remaining_work: &mut usize,
        max_terms: usize,
    ) -> Option<usize> {
        if depth > MAX_SURFACE_DEPTH {
            return None;
        }
        *remaining_work = remaining_work.checked_sub(1)?;
        if let Some(&height) = memo.get(&term) {
            return depth
                .checked_add(height)
                .filter(|&path| path <= MAX_SURFACE_DEPTH.saturating_add(1))
                .map(|_| height);
        }
        if memo.len() >= max_terms || !active.insert(term) {
            return None;
        }
        let child_count = term_child_count(terms, term)?;
        if child_count > *remaining_work || memo.len().saturating_add(child_count) > max_terms {
            return None;
        }
        let mut child_height = 0usize;
        for child in terms.children(term) {
            child_height = child_height.max(height(
                terms,
                child,
                depth + 1,
                memo,
                active,
                remaining_work,
                max_terms,
            )?);
            if child_height >= MAX_SURFACE_DEPTH.saturating_add(1) {
                return None;
            }
        }
        active.remove(&term);
        let height = child_height.checked_add(1)?;
        if height > MAX_SURFACE_DEPTH.saturating_add(1) {
            return None;
        }
        memo.insert(term, height);
        Some(height)
    }

    let mut memo = HashMap::default();
    let mut active = HashSet::default();
    let mut remaining_work = max_work;
    roots.iter().all(|&root| {
        height(
            terms,
            root,
            0,
            &mut memo,
            &mut active,
            &mut remaining_work,
            max_terms,
        )
        .is_some()
    })
}

/// Dynamic printer substitutions have higher precedence than retained source
/// overrides and cannot be represented by the static audit.
pub(in crate::executor) fn live_proof_rendering_is_static(
    proof: &Proof,
    live: &[bool],
    terms: &ay_core::TermStore,
    effective: &HashMap<TermId, String>,
) -> bool {
    // This also covers newly hoisted plan premises, which are absent from the
    // old proof's live-step census but would trigger the let-assume bridge.
    !effective
        .values()
        .any(|surface| surface.starts_with("(let"))
        && live.len() == proof.steps.len()
        && proof.steps.iter().zip(live).all(|(step, &is_live)| {
            !is_live
                || match step {
                    ProofStep::Step {
                        rule: AletheRule::Skolem,
                        ..
                    } => false,
                    ProofStep::Step {
                        rule: AletheRule::Resolution | AletheRule::ThResolution,
                        args,
                        ..
                    } if !effective.is_empty() && !args.is_empty() => false,
                    ProofStep::TheoryLemma {
                        kind: TheoryLemmaKind::ArrayExtensionality,
                        ..
                    } => false,
                    ProofStep::Assume(term) => !matches!(terms.get(*term), TermData::Let(..)),
                    _ => true,
                }
        })
}
