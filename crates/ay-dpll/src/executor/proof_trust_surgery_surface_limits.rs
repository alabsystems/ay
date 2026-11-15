// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded source-tree and dynamic-printer policy for retained surfaces.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, ProofStep, TermId, TheoryLemmaKind};
use ay_frontend::command::Term as FrontendTerm;

pub(in crate::executor) use super::source_work::{ProofSourcePass, ProofSourceWorkEnvelope};

#[path = "proof_trust_surgery_surface_payload.rs"]
mod payload;
pub(in crate::executor) use payload::{
    expanded_render_work_bound, render_roots_have_bounded_payload,
};

#[path = "proof_trust_surgery_surface_limits_nodes.rs"]
mod nodes;
use nodes::SurfaceNode;

#[cfg(test)]
#[path = "proof_trust_surgery_surface_limits_tests.rs"]
mod tests;

const MAX_SURFACE_NODES: usize = 8_192;
pub(super) const MAX_SURFACE_DEPTH: usize = 256;
pub(super) const MAX_REQUIREMENT_BYTES: usize = 8 * 1024 * 1024;
pub(super) const MAX_AGGREGATE_SOURCE_WORK: usize = 32 * 1024 * 1024;
/// Node ceiling of a [`SurfaceWorkModel::Traversal`] root: one allocation per
/// node for each clone a traversal makes, the same ceiling the ground BV
/// rebuild (`proof_trust_surgery_surface_ground.rs`) puts on its node visits.
const MAX_TRAVERSAL_NODES: usize = 1 << 20;

/// What a proof-source pass does with each parsed root, which decides what its
/// work on that root costs.
///
/// The two differ by the depth factor, and it is the whole difference: a
/// recursive collector that renders (or re-elaborates) EVERY subtree pays for
/// each token once per ancestor, while a pass that clones, pattern-matches or
/// rebuilds the tree node by node pays for it once. Pricing a traversal as a
/// per-subtree rendering refused whole proofs for work that never runs:
/// external-codegen's 90 KB `V8I16MaskExtract` obligation (8,511 nodes, depth 40)
/// priced 10.2 MB against the 8 MB per-root rendering bound, so the assembly
/// gate poisoned the proof, while its whole certified proof — assembly, the
/// strict check and the Alethe render — ran in 0.7 s and 43 MB with that gate
/// out of the way (measured 2026-09-29). Every per-subtree pass keeps its own
/// check at its own site, so admitting the root to a traversal authorizes no
/// per-subtree work.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::executor) enum SurfaceWorkModel {
    /// Renders or re-elaborates every subtree: each node's bytes are charged
    /// `depth + 1` times, at most [`MAX_SURFACE_NODES`] nodes, and the whole
    /// root within [`MAX_REQUIREMENT_BYTES`].
    PerSubtree,
    /// Visits each node once: each node's bytes are charged once, at most
    /// [`MAX_TRAVERSAL_NODES`] nodes, and the whole root within
    /// [`MAX_AGGREGATE_SOURCE_WORK`] — one root may not cost more than the
    /// query's entire source envelope.
    Traversal,
}

impl SurfaceWorkModel {
    const fn max_nodes(self) -> usize {
        match self {
            Self::PerSubtree => MAX_SURFACE_NODES,
            Self::Traversal => MAX_TRAVERSAL_NODES,
        }
    }

    const fn max_root_work(self) -> usize {
        match self {
            Self::PerSubtree => MAX_REQUIREMENT_BYTES,
            Self::Traversal => MAX_AGGREGATE_SOURCE_WORK,
        }
    }

    /// How many times a node at `depth` is paid for.
    const fn renderings(self, depth: usize) -> usize {
        match self {
            Self::PerSubtree => depth.saturating_add(1),
            Self::Traversal => 1,
        }
    }
}

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

/// Which bound `surface_source_work` tripped, when it tripped one.
///
/// #unbounded-population. The estimator answered a bare `None` and the decline
/// it feeds (`authored-source-root-unbounded`) could not say whether the root
/// was WIDE, DEEP, of a shape the estimator does not price, or merely heavy in
/// bytes. Those want different remedies, so the refusal names itself.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SurfaceSourceRefusal {
    /// More than `MAX_SURFACE_NODES` parsed nodes.
    Nodes,
    /// Deeper than `MAX_SURFACE_DEPTH`.
    Depth,
    /// A constructor the estimator does not price (or a byte count that
    /// overflowed, which no real source reaches).
    Shape,
    /// The rendering requirement — every node's bytes times its `depth + 1`,
    /// times four — exceeded `MAX_REQUIREMENT_BYTES`.
    Bytes,
}

impl SurfaceSourceRefusal {
    /// The fixed name this refusal carries on the disclosure line.
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::Nodes => "nodes",
            Self::Depth => "depth",
            Self::Shape => "shape",
            Self::Bytes => "bytes",
        }
    }
}

/// Estimate the bounded aggregate work of rendering every surface subtree.
pub(in crate::executor) fn surface_source_work(root: &FrontendTerm) -> Option<usize> {
    surface_source_work_probe(root).ok()
}

/// [`surface_source_work`], naming the bound it tripped when it declines.
pub(in crate::executor) fn surface_source_work_probe(
    root: &FrontendTerm,
) -> Result<usize, SurfaceSourceRefusal> {
    surface_source_work_probe_as(root, SurfaceWorkModel::PerSubtree)
}

/// The work `model` costs on `root`, naming the bound it tripped when it
/// declines.
pub(in crate::executor) fn surface_source_work_probe_as(
    root: &FrontendTerm,
    model: SurfaceWorkModel,
) -> Result<usize, SurfaceSourceRefusal> {
    let mut pending = vec![SurfaceNode::Term(root, 0usize)];
    let mut visited = 0usize;
    let mut rendered_bytes = 0usize;
    while let Some(node) = pending.pop() {
        visited += 1;
        let depth = node.depth();
        if visited > model.max_nodes() {
            return Err(SurfaceSourceRefusal::Nodes);
        }
        if depth > MAX_SURFACE_DEPTH {
            return Err(SurfaceSourceRefusal::Depth);
        }
        let visit = nodes::Visit {
            visited,
            max_nodes: model.max_nodes(),
        };
        let local_bytes = match node {
            SurfaceNode::Term(term, depth) => {
                nodes::surface_term_bytes(term, depth, visit, &mut pending)?
            }
            SurfaceNode::Sort(sort, depth) => {
                nodes::surface_sort_bytes(sort, depth, visit, &mut pending)?
            }
            SurfaceNode::SExpr(sexpr, depth) => {
                nodes::surface_sexpr_bytes(sexpr, depth, visit, &mut pending)?
            }
        };
        // Under `PerSubtree`, every token occurs in the rendering of each of
        // its ancestors and of its own node: `depth + 1` renderings. Charged
        // per node at its own depth — multiplying ALL bytes by the deepest
        // branch refused external-codegen's 34 KB `i64` round-trip obligations (depth
        // 75, 6.5k nodes; 1257/1260) for work they never reach (measured
        // 2026-09-29). Under `Traversal` it is visited once.
        let charged = local_bytes
            .ok_or(SurfaceSourceRefusal::Shape)?
            .checked_mul(model.renderings(depth))
            .ok_or(SurfaceSourceRefusal::Shape)?;
        rendered_bytes = rendered_bytes
            .checked_add(charged)
            .ok_or(SurfaceSourceRefusal::Shape)?;
    }
    // Both the ordinary and deep collectors may render every subtree; the
    // factor of four also covers quoting/parenthesis expansion without
    // constructing those strings. A traversal keeps the same factor, so its
    // charge is exactly what a per-subtree pass would pay at depth zero.
    rendered_bytes
        .checked_mul(4)
        .filter(|&bytes| bytes <= model.max_root_work())
        .ok_or(SurfaceSourceRefusal::Bytes)
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
    surface_pass_work_as(roots, SurfaceWorkModel::PerSubtree)
}

/// [`surface_pass_work`] for a pass whose work on each root is `model`.
pub(in crate::executor) fn surface_pass_work_as<'a>(
    roots: impl IntoIterator<Item = &'a FrontendTerm>,
    model: SurfaceWorkModel,
) -> Option<usize> {
    roots.into_iter().try_fold(0usize, |used, root| {
        used.checked_add(surface_source_work_probe_as(root, model).ok()?.max(1))
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
pub(in crate::executor) fn render_roots_have_bounded_depth(
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
