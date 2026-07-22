// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Non-routing checker scaffold for replayable max-clique certificates.
//!
//! A certificate pairs a clique lower bound with a coloring upper bound. For a
//! graph `G`, each color class must be an independent set in `G`, and the color
//! classes must cover every vertex exactly once. When the clique size equals the
//! number of color classes, the certificate proves the clique number for the
//! replayed graph without changing any optimization route.

#![allow(dead_code)]

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct ReplayableCliqueCertificate {
    pub(crate) clique: Vec<usize>,
    pub(crate) color_classes: Vec<Vec<usize>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CliqueCertificateCheck {
    pub(crate) vertex_count: usize,
    pub(crate) clique_size: usize,
    pub(crate) color_class_count: usize,
    pub(crate) proves_exact_bound: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct ReplayableCliqueBbTranscript {
    pub(crate) target_size: usize,
    pub(crate) root: CliqueBbNodeTranscript,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct CliqueBbNodeTranscript {
    pub(crate) candidates: Vec<usize>,
    pub(crate) proof: CliqueBbNodeProof,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum CliqueBbNodeProof {
    Branch {
        branches: Vec<CliqueBbBranchTranscript>,
    },
    DynamicBranch {
        branches: Vec<CliqueBbBranchTranscript>,
        remaining: Option<Box<CliqueBbNodeTranscript>>,
    },
    DegreeCorePrune {
        pruned_vertices: Vec<usize>,
        child: Box<CliqueBbNodeTranscript>,
    },
    ColorPrune {
        color_classes: Vec<Vec<usize>>,
    },
    CardinalityPrune {},
    EmptyCandidatePrune {},
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct CliqueBbBranchTranscript {
    pub(crate) vertex: usize,
    pub(crate) child: Box<CliqueBbNodeTranscript>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CliqueBbTranscriptCheck {
    pub(crate) vertex_count: usize,
    pub(crate) target_size: usize,
    pub(crate) visited_nodes: usize,
    pub(crate) branch_count: usize,
    pub(crate) degree_core_prunes: usize,
    pub(crate) degree_core_pruned_vertices: usize,
    pub(crate) color_prunes: usize,
    pub(crate) cardinality_prunes: usize,
    pub(crate) empty_candidate_prunes: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct ReplayableCliqueBbPartialFrontier {
    pub(crate) target_size: usize,
    pub(crate) root: CliqueBbPartialFrontierNode,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct CliqueBbPartialFrontierNode {
    pub(crate) candidates: Vec<usize>,
    pub(crate) proof: CliqueBbPartialFrontierProof,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum CliqueBbPartialFrontierProof {
    Branch {
        branches: Vec<CliqueBbPartialFrontierBranch>,
    },
    DynamicBranch {
        branches: Vec<CliqueBbPartialFrontierBranch>,
        remaining: Option<Box<CliqueBbPartialFrontierNode>>,
    },
    DegreeCorePrune {
        pruned_vertices: Vec<usize>,
        child: Box<CliqueBbPartialFrontierNode>,
    },
    ColorPrune {
        color_classes: Vec<Vec<usize>>,
    },
    CardinalityPrune {},
    EmptyCandidatePrune {},
    OpenObligation {},
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct CliqueBbPartialFrontierBranch {
    pub(crate) vertex: usize,
    pub(crate) child: Box<CliqueBbPartialFrontierNode>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CliqueBbPartialFrontierCheck {
    pub(crate) vertex_count: usize,
    pub(crate) target_size: usize,
    pub(crate) visited_nodes: usize,
    pub(crate) branch_count: usize,
    pub(crate) degree_core_prunes: usize,
    pub(crate) degree_core_pruned_vertices: usize,
    pub(crate) color_prunes: usize,
    pub(crate) cardinality_prunes: usize,
    pub(crate) empty_candidate_prunes: usize,
    pub(crate) open_obligations: usize,
    pub(crate) open_obligation_candidates: usize,
    pub(crate) max_open_obligation_depth: usize,
    pub(crate) proves_no_target_clique: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CliqueBbPartialFrontierMerge {
    pub(crate) replaced: bool,
    pub(crate) check: CliqueBbPartialFrontierCheck,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CliqueBbPartialFrontierMergeError {
    Replay(CliqueBbTranscriptError),
    TargetNotOpen {
        candidates: Vec<usize>,
    },
    PatchRootMismatch {
        expected: Vec<usize>,
        actual: Vec<usize>,
    },
    PatchNotClosed {
        open_obligations: usize,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CliqueCertificateError {
    EdgeEndpointOutOfRange {
        vertex: usize,
        vertex_count: usize,
    },
    SelfLoop {
        vertex: usize,
    },
    CliqueVertexOutOfRange {
        vertex: usize,
        vertex_count: usize,
    },
    DuplicateCliqueVertex {
        vertex: usize,
    },
    CliqueMissingEdge {
        lhs: usize,
        rhs: usize,
    },
    ColorVertexOutOfRange {
        vertex: usize,
        vertex_count: usize,
    },
    DuplicateColorVertex {
        vertex: usize,
    },
    MissingColorVertex {
        vertex: usize,
    },
    ColorClassHasEdge {
        color_class: usize,
        lhs: usize,
        rhs: usize,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CliqueBbTranscriptError {
    InvalidTargetSize {
        target_size: usize,
    },
    RootCandidateOutOfRange {
        vertex: usize,
        vertex_count: usize,
    },
    DuplicateRootCandidate {
        vertex: usize,
    },
    MissingRootCandidate {
        vertex: usize,
    },
    NodeCandidateOutOfRange {
        depth: usize,
        vertex: usize,
        vertex_count: usize,
    },
    DuplicateNodeCandidate {
        depth: usize,
        vertex: usize,
    },
    TargetCliqueReached {
        depth: usize,
        target_size: usize,
    },
    MissingBranch {
        depth: usize,
        vertex: usize,
    },
    UnexpectedBranch {
        depth: usize,
        vertex: usize,
    },
    BranchVertexOutOfRange {
        depth: usize,
        vertex: usize,
        vertex_count: usize,
    },
    BranchOrderMismatch {
        depth: usize,
        index: usize,
        expected: usize,
        actual: usize,
    },
    DynamicBranchVertexNotRemaining {
        depth: usize,
        vertex: usize,
    },
    DuplicateDynamicBranchVertex {
        depth: usize,
        vertex: usize,
    },
    ChildCandidatesMismatch {
        parent_depth: usize,
        branch_vertex: usize,
        expected: Vec<usize>,
        actual: Vec<usize>,
    },
    MissingDynamicRemainingTail {
        depth: usize,
        vertex: usize,
    },
    UnexpectedDynamicRemainingTail {
        depth: usize,
    },
    DynamicRemainingCandidatesMismatch {
        depth: usize,
        expected: Vec<usize>,
        actual: Vec<usize>,
    },
    EmptyDegreeCorePrune {
        depth: usize,
    },
    DegreeCorePruneVertexOutOfRange {
        depth: usize,
        vertex: usize,
        vertex_count: usize,
    },
    DuplicateDegreeCorePruneVertex {
        depth: usize,
        vertex: usize,
    },
    DegreeCorePruneVertexNotCandidate {
        depth: usize,
        vertex: usize,
    },
    DegreeCorePruneTooWeak {
        depth: usize,
        vertex: usize,
        residual_degree: usize,
        min_degree: usize,
    },
    DegreeCorePruneChildCandidatesMismatch {
        depth: usize,
        expected: Vec<usize>,
        actual: Vec<usize>,
    },
    ColorVertexOutOfRange {
        depth: usize,
        vertex: usize,
        vertex_count: usize,
    },
    ColorVertexNotCandidate {
        depth: usize,
        vertex: usize,
    },
    DuplicateColorVertex {
        depth: usize,
        vertex: usize,
    },
    MissingColorVertex {
        depth: usize,
        vertex: usize,
    },
    ColorClassHasEdge {
        depth: usize,
        color_class: usize,
        lhs: usize,
        rhs: usize,
    },
    ColorPruneTooWeak {
        depth: usize,
        prefix_size: usize,
        color_class_count: usize,
        target_size: usize,
    },
    CardinalityPruneTooWeak {
        depth: usize,
        prefix_size: usize,
        candidate_count: usize,
        target_size: usize,
    },
    EmptyCandidatePruneWithCandidates {
        depth: usize,
        candidate_count: usize,
    },
    OpenObligationAlreadyClosed {
        depth: usize,
        prefix_size: usize,
        candidate_count: usize,
        target_size: usize,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ReplayableCliqueGraph {
    adjacency: Vec<Vec<bool>>,
}

impl ReplayableCliqueGraph {
    pub(crate) fn from_edges(
        vertex_count: usize,
        edges: impl IntoIterator<Item = (usize, usize)>,
    ) -> Result<Self, CliqueCertificateError> {
        let mut adjacency = vec![vec![false; vertex_count]; vertex_count];
        for (lhs, rhs) in edges {
            if lhs >= vertex_count {
                return Err(CliqueCertificateError::EdgeEndpointOutOfRange {
                    vertex: lhs,
                    vertex_count,
                });
            }
            if rhs >= vertex_count {
                return Err(CliqueCertificateError::EdgeEndpointOutOfRange {
                    vertex: rhs,
                    vertex_count,
                });
            }
            if lhs == rhs {
                return Err(CliqueCertificateError::SelfLoop { vertex: lhs });
            }
            adjacency[lhs][rhs] = true;
            adjacency[rhs][lhs] = true;
        }
        Ok(Self { adjacency })
    }

    pub(crate) fn vertex_count(&self) -> usize {
        self.adjacency.len()
    }

    fn has_edge(&self, lhs: usize, rhs: usize) -> bool {
        self.adjacency[lhs][rhs]
    }
}

pub(crate) fn check_replayable_clique_certificate(
    graph: &ReplayableCliqueGraph,
    certificate: &ReplayableCliqueCertificate,
) -> Result<CliqueCertificateCheck, CliqueCertificateError> {
    check_clique(graph, &certificate.clique)?;
    check_color_classes(graph, &certificate.color_classes)?;

    Ok(CliqueCertificateCheck {
        vertex_count: graph.vertex_count(),
        clique_size: certificate.clique.len(),
        color_class_count: certificate.color_classes.len(),
        proves_exact_bound: certificate.clique.len() == certificate.color_classes.len(),
    })
}

pub(crate) fn check_replayable_clique_bb_transcript(
    graph: &ReplayableCliqueGraph,
    transcript: &ReplayableCliqueBbTranscript,
) -> Result<CliqueBbTranscriptCheck, CliqueBbTranscriptError> {
    if transcript.target_size == 0 {
        return Err(CliqueBbTranscriptError::InvalidTargetSize {
            target_size: transcript.target_size,
        });
    }

    check_root_candidate_coverage(graph, &transcript.root.candidates)?;

    let mut check = CliqueBbTranscriptCheck {
        vertex_count: graph.vertex_count(),
        target_size: transcript.target_size,
        visited_nodes: 0,
        branch_count: 0,
        degree_core_prunes: 0,
        degree_core_pruned_vertices: 0,
        color_prunes: 0,
        cardinality_prunes: 0,
        empty_candidate_prunes: 0,
    };

    replay_bb_node(
        graph,
        transcript.target_size,
        0,
        &transcript.root,
        0,
        &mut check,
    )?;

    Ok(check)
}

pub(crate) fn check_replayable_clique_bb_partial_frontier(
    graph: &ReplayableCliqueGraph,
    frontier: &ReplayableCliqueBbPartialFrontier,
) -> Result<CliqueBbPartialFrontierCheck, CliqueBbTranscriptError> {
    if frontier.target_size == 0 {
        return Err(CliqueBbTranscriptError::InvalidTargetSize {
            target_size: frontier.target_size,
        });
    }

    check_root_candidate_coverage(graph, &frontier.root.candidates)?;

    let mut check = new_partial_frontier_check(graph, frontier.target_size);

    replay_partial_frontier_node(
        graph,
        frontier.target_size,
        0,
        &frontier.root,
        0,
        &mut check,
    )?;
    check.proves_no_target_clique = check.open_obligations == 0;

    Ok(check)
}

fn new_partial_frontier_check(
    graph: &ReplayableCliqueGraph,
    target_size: usize,
) -> CliqueBbPartialFrontierCheck {
    CliqueBbPartialFrontierCheck {
        vertex_count: graph.vertex_count(),
        target_size,
        visited_nodes: 0,
        branch_count: 0,
        degree_core_prunes: 0,
        degree_core_pruned_vertices: 0,
        color_prunes: 0,
        cardinality_prunes: 0,
        empty_candidate_prunes: 0,
        open_obligations: 0,
        open_obligation_candidates: 0,
        max_open_obligation_depth: 0,
        proves_no_target_clique: false,
    }
}

pub(crate) fn merge_replayable_clique_bb_partial_frontier(
    graph: &ReplayableCliqueGraph,
    frontier: &mut ReplayableCliqueBbPartialFrontier,
    target_candidates: &[usize],
    patch: CliqueBbPartialFrontierNode,
) -> Result<CliqueBbPartialFrontierMerge, CliqueBbPartialFrontierMergeError> {
    let target_vec = target_candidates.to_vec();
    if patch.candidates != target_vec {
        return Err(CliqueBbPartialFrontierMergeError::PatchRootMismatch {
            expected: target_vec,
            actual: patch.candidates,
        });
    }

    let mut merged = frontier.clone();
    let replaced = replace_open_partial_frontier_node(
        graph,
        merged.target_size,
        0,
        0,
        &mut merged.root,
        target_candidates,
        &patch,
    )?;
    let check = check_replayable_clique_bb_partial_frontier(graph, &merged)
        .map_err(CliqueBbPartialFrontierMergeError::Replay)?;
    if replaced {
        *frontier = merged;
    }
    Ok(CliqueBbPartialFrontierMerge { replaced, check })
}

fn replace_open_partial_frontier_node(
    graph: &ReplayableCliqueGraph,
    target_size: usize,
    prefix_size: usize,
    depth: usize,
    node: &mut CliqueBbPartialFrontierNode,
    target_candidates: &[usize],
    patch: &CliqueBbPartialFrontierNode,
) -> Result<bool, CliqueBbPartialFrontierMergeError> {
    if node.candidates == target_candidates {
        if !matches!(node.proof, CliqueBbPartialFrontierProof::OpenObligation {}) {
            return Err(CliqueBbPartialFrontierMergeError::TargetNotOpen {
                candidates: node.candidates.clone(),
            });
        }
        if patch.candidates != node.candidates {
            return Err(CliqueBbPartialFrontierMergeError::PatchRootMismatch {
                expected: node.candidates.clone(),
                actual: patch.candidates.clone(),
            });
        }
        validate_closed_partial_frontier_patch(graph, target_size, prefix_size, depth, patch)?;
        *node = patch.clone();
        return Ok(true);
    }

    replace_open_partial_frontier_child(
        graph,
        target_size,
        prefix_size,
        depth,
        &mut node.proof,
        target_candidates,
        patch,
    )
}

fn validate_closed_partial_frontier_patch(
    graph: &ReplayableCliqueGraph,
    target_size: usize,
    prefix_size: usize,
    depth: usize,
    patch: &CliqueBbPartialFrontierNode,
) -> Result<(), CliqueBbPartialFrontierMergeError> {
    let mut patch_check = new_partial_frontier_check(graph, target_size);
    replay_partial_frontier_node(
        graph,
        target_size,
        prefix_size,
        patch,
        depth,
        &mut patch_check,
    )
    .map_err(CliqueBbPartialFrontierMergeError::Replay)?;
    if patch_check.open_obligations != 0 {
        return Err(CliqueBbPartialFrontierMergeError::PatchNotClosed {
            open_obligations: patch_check.open_obligations,
        });
    }
    Ok(())
}

fn replace_open_partial_frontier_child(
    graph: &ReplayableCliqueGraph,
    target_size: usize,
    prefix_size: usize,
    depth: usize,
    proof: &mut CliqueBbPartialFrontierProof,
    target_candidates: &[usize],
    patch: &CliqueBbPartialFrontierNode,
) -> Result<bool, CliqueBbPartialFrontierMergeError> {
    match proof {
        CliqueBbPartialFrontierProof::Branch { branches } => {
            for branch in branches {
                if replace_open_partial_frontier_node(
                    graph,
                    target_size,
                    prefix_size + 1,
                    depth + 1,
                    &mut branch.child,
                    target_candidates,
                    patch,
                )? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        CliqueBbPartialFrontierProof::DynamicBranch {
            branches,
            remaining,
        } => {
            for branch in branches {
                if replace_open_partial_frontier_node(
                    graph,
                    target_size,
                    prefix_size + 1,
                    depth + 1,
                    &mut branch.child,
                    target_candidates,
                    patch,
                )? {
                    return Ok(true);
                }
            }
            if let Some(remaining) = remaining {
                replace_open_partial_frontier_node(
                    graph,
                    target_size,
                    prefix_size,
                    depth,
                    remaining,
                    target_candidates,
                    patch,
                )
            } else {
                Ok(false)
            }
        }
        CliqueBbPartialFrontierProof::DegreeCorePrune { child, .. } => {
            replace_open_partial_frontier_node(
                graph,
                target_size,
                prefix_size,
                depth,
                child,
                target_candidates,
                patch,
            )
        }
        CliqueBbPartialFrontierProof::ColorPrune { .. }
        | CliqueBbPartialFrontierProof::CardinalityPrune {}
        | CliqueBbPartialFrontierProof::EmptyCandidatePrune {}
        | CliqueBbPartialFrontierProof::OpenObligation {} => Ok(false),
    }
}

fn check_root_candidate_coverage(
    graph: &ReplayableCliqueGraph,
    candidates: &[usize],
) -> Result<(), CliqueBbTranscriptError> {
    let vertex_count = graph.vertex_count();
    let mut seen = vec![false; vertex_count];

    for &vertex in candidates {
        if vertex >= vertex_count {
            return Err(CliqueBbTranscriptError::RootCandidateOutOfRange {
                vertex,
                vertex_count,
            });
        }
        if seen[vertex] {
            return Err(CliqueBbTranscriptError::DuplicateRootCandidate { vertex });
        }
        seen[vertex] = true;
    }

    for (vertex, was_seen) in seen.into_iter().enumerate() {
        if !was_seen {
            return Err(CliqueBbTranscriptError::MissingRootCandidate { vertex });
        }
    }

    Ok(())
}

fn replay_partial_frontier_node(
    graph: &ReplayableCliqueGraph,
    target_size: usize,
    prefix_size: usize,
    node: &CliqueBbPartialFrontierNode,
    depth: usize,
    check: &mut CliqueBbPartialFrontierCheck,
) -> Result<(), CliqueBbTranscriptError> {
    validate_node_candidates(graph, depth, &node.candidates)?;
    if prefix_size >= target_size {
        return Err(CliqueBbTranscriptError::TargetCliqueReached { depth, target_size });
    }

    check.visited_nodes += 1;

    match &node.proof {
        CliqueBbPartialFrontierProof::Branch { branches } => replay_partial_frontier_branches(
            graph,
            target_size,
            prefix_size,
            node,
            depth,
            branches,
            check,
        ),
        CliqueBbPartialFrontierProof::DynamicBranch {
            branches,
            remaining,
        } => replay_partial_frontier_dynamic_branches(
            graph,
            target_size,
            prefix_size,
            node,
            depth,
            branches,
            remaining.as_deref(),
            check,
        ),
        CliqueBbPartialFrontierProof::DegreeCorePrune {
            pruned_vertices,
            child,
        } => replay_partial_frontier_degree_core_prune(
            graph,
            target_size,
            prefix_size,
            node,
            depth,
            pruned_vertices,
            child,
            check,
        ),
        CliqueBbPartialFrontierProof::ColorPrune { color_classes } => {
            check_node_color_classes(graph, depth, &node.candidates, color_classes)?;
            if prefix_size + color_classes.len() >= target_size {
                return Err(CliqueBbTranscriptError::ColorPruneTooWeak {
                    depth,
                    prefix_size,
                    color_class_count: color_classes.len(),
                    target_size,
                });
            }
            check.color_prunes += 1;
            Ok(())
        }
        CliqueBbPartialFrontierProof::CardinalityPrune {} => {
            if prefix_size + node.candidates.len() >= target_size {
                return Err(CliqueBbTranscriptError::CardinalityPruneTooWeak {
                    depth,
                    prefix_size,
                    candidate_count: node.candidates.len(),
                    target_size,
                });
            }
            check.cardinality_prunes += 1;
            Ok(())
        }
        CliqueBbPartialFrontierProof::EmptyCandidatePrune {} => {
            if !node.candidates.is_empty() {
                return Err(CliqueBbTranscriptError::EmptyCandidatePruneWithCandidates {
                    depth,
                    candidate_count: node.candidates.len(),
                });
            }
            check.empty_candidate_prunes += 1;
            Ok(())
        }
        CliqueBbPartialFrontierProof::OpenObligation {} => {
            if prefix_size + node.candidates.len() < target_size {
                return Err(CliqueBbTranscriptError::OpenObligationAlreadyClosed {
                    depth,
                    prefix_size,
                    candidate_count: node.candidates.len(),
                    target_size,
                });
            }
            check.open_obligations += 1;
            check.open_obligation_candidates += node.candidates.len();
            check.max_open_obligation_depth = check.max_open_obligation_depth.max(depth);
            Ok(())
        }
    }
}

fn replay_partial_frontier_branches(
    graph: &ReplayableCliqueGraph,
    target_size: usize,
    prefix_size: usize,
    node: &CliqueBbPartialFrontierNode,
    depth: usize,
    branches: &[CliqueBbPartialFrontierBranch],
    check: &mut CliqueBbPartialFrontierCheck,
) -> Result<(), CliqueBbTranscriptError> {
    if branches.len() < node.candidates.len() {
        return Err(CliqueBbTranscriptError::MissingBranch {
            depth,
            vertex: node.candidates[branches.len()],
        });
    }
    if branches.len() > node.candidates.len() {
        return Err(CliqueBbTranscriptError::UnexpectedBranch {
            depth,
            vertex: branches[node.candidates.len()].vertex,
        });
    }

    let vertex_count = graph.vertex_count();
    for (index, branch) in branches.iter().enumerate() {
        if branch.vertex >= vertex_count {
            return Err(CliqueBbTranscriptError::BranchVertexOutOfRange {
                depth,
                vertex: branch.vertex,
                vertex_count,
            });
        }

        let expected_vertex = node.candidates[index];
        if branch.vertex != expected_vertex {
            return Err(CliqueBbTranscriptError::BranchOrderMismatch {
                depth,
                index,
                expected: expected_vertex,
                actual: branch.vertex,
            });
        }

        let expected_child_candidates = node.candidates[index + 1..]
            .iter()
            .copied()
            .filter(|&candidate| graph.has_edge(branch.vertex, candidate))
            .collect::<Vec<_>>();
        validate_node_candidates(graph, depth + 1, &branch.child.candidates)?;
        if branch.child.candidates != expected_child_candidates {
            return Err(CliqueBbTranscriptError::ChildCandidatesMismatch {
                parent_depth: depth,
                branch_vertex: branch.vertex,
                expected: expected_child_candidates,
                actual: branch.child.candidates.clone(),
            });
        }

        check.branch_count += 1;
        replay_partial_frontier_node(
            graph,
            target_size,
            prefix_size + 1,
            &branch.child,
            depth + 1,
            check,
        )?;
    }

    Ok(())
}

fn replay_partial_frontier_dynamic_branches(
    graph: &ReplayableCliqueGraph,
    target_size: usize,
    prefix_size: usize,
    node: &CliqueBbPartialFrontierNode,
    depth: usize,
    branches: &[CliqueBbPartialFrontierBranch],
    remaining: Option<&CliqueBbPartialFrontierNode>,
    check: &mut CliqueBbPartialFrontierCheck,
) -> Result<(), CliqueBbTranscriptError> {
    let vertex_count = graph.vertex_count();
    let mut current_remaining = node.candidates.clone();
    let mut seen = vec![false; vertex_count];

    for branch in branches {
        if branch.vertex >= vertex_count {
            return Err(CliqueBbTranscriptError::BranchVertexOutOfRange {
                depth,
                vertex: branch.vertex,
                vertex_count,
            });
        }
        if seen[branch.vertex] {
            return Err(CliqueBbTranscriptError::DuplicateDynamicBranchVertex {
                depth,
                vertex: branch.vertex,
            });
        }

        let Some(position) = current_remaining
            .iter()
            .position(|&vertex| vertex == branch.vertex)
        else {
            return Err(CliqueBbTranscriptError::DynamicBranchVertexNotRemaining {
                depth,
                vertex: branch.vertex,
            });
        };

        let expected_child_candidates = current_remaining
            .iter()
            .copied()
            .filter(|&candidate| {
                candidate != branch.vertex && graph.has_edge(branch.vertex, candidate)
            })
            .collect::<Vec<_>>();
        validate_node_candidates(graph, depth + 1, &branch.child.candidates)?;
        if branch.child.candidates != expected_child_candidates {
            return Err(CliqueBbTranscriptError::ChildCandidatesMismatch {
                parent_depth: depth,
                branch_vertex: branch.vertex,
                expected: expected_child_candidates,
                actual: branch.child.candidates.clone(),
            });
        }

        seen[branch.vertex] = true;
        current_remaining.remove(position);
        check.branch_count += 1;
        replay_partial_frontier_node(
            graph,
            target_size,
            prefix_size + 1,
            &branch.child,
            depth + 1,
            check,
        )?;
    }

    replay_partial_frontier_dynamic_remaining(
        graph,
        target_size,
        prefix_size,
        depth,
        current_remaining,
        remaining,
        check,
    )
}

fn replay_partial_frontier_dynamic_remaining(
    graph: &ReplayableCliqueGraph,
    target_size: usize,
    prefix_size: usize,
    depth: usize,
    current_remaining: Vec<usize>,
    remaining: Option<&CliqueBbPartialFrontierNode>,
    check: &mut CliqueBbPartialFrontierCheck,
) -> Result<(), CliqueBbTranscriptError> {
    if current_remaining.is_empty() {
        if remaining.is_some() {
            return Err(CliqueBbTranscriptError::UnexpectedDynamicRemainingTail { depth });
        }
        return Ok(());
    }

    let Some(remaining) = remaining else {
        return Err(CliqueBbTranscriptError::MissingDynamicRemainingTail {
            depth,
            vertex: current_remaining[0],
        });
    };

    validate_node_candidates(graph, depth, &remaining.candidates)?;
    if remaining.candidates != current_remaining {
        return Err(
            CliqueBbTranscriptError::DynamicRemainingCandidatesMismatch {
                depth,
                expected: current_remaining,
                actual: remaining.candidates.clone(),
            },
        );
    }

    replay_partial_frontier_node(graph, target_size, prefix_size, remaining, depth, check)
}

fn replay_partial_frontier_degree_core_prune(
    graph: &ReplayableCliqueGraph,
    target_size: usize,
    prefix_size: usize,
    node: &CliqueBbPartialFrontierNode,
    depth: usize,
    pruned_vertices: &[usize],
    child: &CliqueBbPartialFrontierNode,
    check: &mut CliqueBbPartialFrontierCheck,
) -> Result<(), CliqueBbTranscriptError> {
    if pruned_vertices.is_empty() {
        return Err(CliqueBbTranscriptError::EmptyDegreeCorePrune { depth });
    }

    let vertex_count = graph.vertex_count();
    let mut in_remaining = vec![false; vertex_count];
    for &vertex in &node.candidates {
        in_remaining[vertex] = true;
    }

    let mut seen_pruned = vec![false; vertex_count];
    let min_degree = target_size.saturating_sub(prefix_size).saturating_sub(1);
    for &vertex in pruned_vertices {
        if vertex >= vertex_count {
            return Err(CliqueBbTranscriptError::DegreeCorePruneVertexOutOfRange {
                depth,
                vertex,
                vertex_count,
            });
        }
        if seen_pruned[vertex] {
            return Err(CliqueBbTranscriptError::DuplicateDegreeCorePruneVertex { depth, vertex });
        }
        if !in_remaining[vertex] {
            return Err(CliqueBbTranscriptError::DegreeCorePruneVertexNotCandidate {
                depth,
                vertex,
            });
        }

        let residual_degree = node
            .candidates
            .iter()
            .copied()
            .filter(|&candidate| in_remaining[candidate] && graph.has_edge(vertex, candidate))
            .count();
        if residual_degree >= min_degree {
            return Err(CliqueBbTranscriptError::DegreeCorePruneTooWeak {
                depth,
                vertex,
                residual_degree,
                min_degree,
            });
        }

        seen_pruned[vertex] = true;
        in_remaining[vertex] = false;
    }

    let expected_child_candidates = node
        .candidates
        .iter()
        .copied()
        .filter(|&vertex| in_remaining[vertex])
        .collect::<Vec<_>>();
    validate_node_candidates(graph, depth, &child.candidates)?;
    if child.candidates != expected_child_candidates {
        return Err(
            CliqueBbTranscriptError::DegreeCorePruneChildCandidatesMismatch {
                depth,
                expected: expected_child_candidates,
                actual: child.candidates.clone(),
            },
        );
    }

    check.degree_core_prunes += 1;
    check.degree_core_pruned_vertices += pruned_vertices.len();
    replay_partial_frontier_node(graph, target_size, prefix_size, child, depth, check)
}

fn replay_bb_node(
    graph: &ReplayableCliqueGraph,
    target_size: usize,
    prefix_size: usize,
    node: &CliqueBbNodeTranscript,
    depth: usize,
    check: &mut CliqueBbTranscriptCheck,
) -> Result<(), CliqueBbTranscriptError> {
    validate_node_candidates(graph, depth, &node.candidates)?;
    if prefix_size >= target_size {
        return Err(CliqueBbTranscriptError::TargetCliqueReached { depth, target_size });
    }

    check.visited_nodes += 1;

    match &node.proof {
        CliqueBbNodeProof::Branch { branches } => replay_bb_branches(
            graph,
            target_size,
            prefix_size,
            node,
            depth,
            branches,
            check,
        ),
        CliqueBbNodeProof::DynamicBranch {
            branches,
            remaining,
        } => replay_bb_dynamic_branches(
            graph,
            target_size,
            prefix_size,
            node,
            depth,
            branches,
            remaining.as_deref(),
            check,
        ),
        CliqueBbNodeProof::DegreeCorePrune {
            pruned_vertices,
            child,
        } => replay_degree_core_prune(
            graph,
            target_size,
            prefix_size,
            node,
            depth,
            pruned_vertices,
            child,
            check,
        ),
        CliqueBbNodeProof::ColorPrune { color_classes } => {
            check_node_color_classes(graph, depth, &node.candidates, color_classes)?;
            if prefix_size + color_classes.len() >= target_size {
                return Err(CliqueBbTranscriptError::ColorPruneTooWeak {
                    depth,
                    prefix_size,
                    color_class_count: color_classes.len(),
                    target_size,
                });
            }
            check.color_prunes += 1;
            Ok(())
        }
        CliqueBbNodeProof::CardinalityPrune {} => {
            if prefix_size + node.candidates.len() >= target_size {
                return Err(CliqueBbTranscriptError::CardinalityPruneTooWeak {
                    depth,
                    prefix_size,
                    candidate_count: node.candidates.len(),
                    target_size,
                });
            }
            check.cardinality_prunes += 1;
            Ok(())
        }
        CliqueBbNodeProof::EmptyCandidatePrune {} => {
            if !node.candidates.is_empty() {
                return Err(CliqueBbTranscriptError::EmptyCandidatePruneWithCandidates {
                    depth,
                    candidate_count: node.candidates.len(),
                });
            }
            check.empty_candidate_prunes += 1;
            Ok(())
        }
    }
}

fn replay_bb_branches(
    graph: &ReplayableCliqueGraph,
    target_size: usize,
    prefix_size: usize,
    node: &CliqueBbNodeTranscript,
    depth: usize,
    branches: &[CliqueBbBranchTranscript],
    check: &mut CliqueBbTranscriptCheck,
) -> Result<(), CliqueBbTranscriptError> {
    if branches.len() < node.candidates.len() {
        return Err(CliqueBbTranscriptError::MissingBranch {
            depth,
            vertex: node.candidates[branches.len()],
        });
    }
    if branches.len() > node.candidates.len() {
        return Err(CliqueBbTranscriptError::UnexpectedBranch {
            depth,
            vertex: branches[node.candidates.len()].vertex,
        });
    }

    let vertex_count = graph.vertex_count();
    for (index, branch) in branches.iter().enumerate() {
        if branch.vertex >= vertex_count {
            return Err(CliqueBbTranscriptError::BranchVertexOutOfRange {
                depth,
                vertex: branch.vertex,
                vertex_count,
            });
        }

        let expected_vertex = node.candidates[index];
        if branch.vertex != expected_vertex {
            return Err(CliqueBbTranscriptError::BranchOrderMismatch {
                depth,
                index,
                expected: expected_vertex,
                actual: branch.vertex,
            });
        }

        let expected_child_candidates = node.candidates[index + 1..]
            .iter()
            .copied()
            .filter(|&candidate| graph.has_edge(branch.vertex, candidate))
            .collect::<Vec<_>>();
        validate_node_candidates(graph, depth + 1, &branch.child.candidates)?;
        if branch.child.candidates != expected_child_candidates {
            return Err(CliqueBbTranscriptError::ChildCandidatesMismatch {
                parent_depth: depth,
                branch_vertex: branch.vertex,
                expected: expected_child_candidates,
                actual: branch.child.candidates.clone(),
            });
        }

        check.branch_count += 1;
        replay_bb_node(
            graph,
            target_size,
            prefix_size + 1,
            &branch.child,
            depth + 1,
            check,
        )?;
    }

    Ok(())
}

fn replay_bb_dynamic_branches(
    graph: &ReplayableCliqueGraph,
    target_size: usize,
    prefix_size: usize,
    node: &CliqueBbNodeTranscript,
    depth: usize,
    branches: &[CliqueBbBranchTranscript],
    remaining: Option<&CliqueBbNodeTranscript>,
    check: &mut CliqueBbTranscriptCheck,
) -> Result<(), CliqueBbTranscriptError> {
    let vertex_count = graph.vertex_count();
    let mut current_remaining = node.candidates.clone();
    let mut seen = vec![false; vertex_count];

    for branch in branches {
        if branch.vertex >= vertex_count {
            return Err(CliqueBbTranscriptError::BranchVertexOutOfRange {
                depth,
                vertex: branch.vertex,
                vertex_count,
            });
        }
        if seen[branch.vertex] {
            return Err(CliqueBbTranscriptError::DuplicateDynamicBranchVertex {
                depth,
                vertex: branch.vertex,
            });
        }

        let Some(position) = current_remaining
            .iter()
            .position(|&vertex| vertex == branch.vertex)
        else {
            return Err(CliqueBbTranscriptError::DynamicBranchVertexNotRemaining {
                depth,
                vertex: branch.vertex,
            });
        };

        let expected_child_candidates = current_remaining
            .iter()
            .copied()
            .filter(|&candidate| {
                candidate != branch.vertex && graph.has_edge(branch.vertex, candidate)
            })
            .collect::<Vec<_>>();
        validate_node_candidates(graph, depth + 1, &branch.child.candidates)?;
        if branch.child.candidates != expected_child_candidates {
            return Err(CliqueBbTranscriptError::ChildCandidatesMismatch {
                parent_depth: depth,
                branch_vertex: branch.vertex,
                expected: expected_child_candidates,
                actual: branch.child.candidates.clone(),
            });
        }

        seen[branch.vertex] = true;
        current_remaining.remove(position);
        check.branch_count += 1;
        replay_bb_node(
            graph,
            target_size,
            prefix_size + 1,
            &branch.child,
            depth + 1,
            check,
        )?;
    }

    replay_bb_dynamic_remaining(
        graph,
        target_size,
        prefix_size,
        depth,
        current_remaining,
        remaining,
        check,
    )
}

fn replay_bb_dynamic_remaining(
    graph: &ReplayableCliqueGraph,
    target_size: usize,
    prefix_size: usize,
    depth: usize,
    current_remaining: Vec<usize>,
    remaining: Option<&CliqueBbNodeTranscript>,
    check: &mut CliqueBbTranscriptCheck,
) -> Result<(), CliqueBbTranscriptError> {
    if current_remaining.is_empty() {
        if remaining.is_some() {
            return Err(CliqueBbTranscriptError::UnexpectedDynamicRemainingTail { depth });
        }
        return Ok(());
    }

    let Some(remaining) = remaining else {
        return Err(CliqueBbTranscriptError::MissingDynamicRemainingTail {
            depth,
            vertex: current_remaining[0],
        });
    };

    validate_node_candidates(graph, depth, &remaining.candidates)?;
    if remaining.candidates != current_remaining {
        return Err(
            CliqueBbTranscriptError::DynamicRemainingCandidatesMismatch {
                depth,
                expected: current_remaining,
                actual: remaining.candidates.clone(),
            },
        );
    }

    replay_bb_node(graph, target_size, prefix_size, remaining, depth, check)
}

fn replay_degree_core_prune(
    graph: &ReplayableCliqueGraph,
    target_size: usize,
    prefix_size: usize,
    node: &CliqueBbNodeTranscript,
    depth: usize,
    pruned_vertices: &[usize],
    child: &CliqueBbNodeTranscript,
    check: &mut CliqueBbTranscriptCheck,
) -> Result<(), CliqueBbTranscriptError> {
    if pruned_vertices.is_empty() {
        return Err(CliqueBbTranscriptError::EmptyDegreeCorePrune { depth });
    }

    let vertex_count = graph.vertex_count();
    let mut in_remaining = vec![false; vertex_count];
    for &vertex in &node.candidates {
        in_remaining[vertex] = true;
    }

    let mut seen_pruned = vec![false; vertex_count];
    let min_degree = target_size.saturating_sub(prefix_size).saturating_sub(1);
    for &vertex in pruned_vertices {
        if vertex >= vertex_count {
            return Err(CliqueBbTranscriptError::DegreeCorePruneVertexOutOfRange {
                depth,
                vertex,
                vertex_count,
            });
        }
        if seen_pruned[vertex] {
            return Err(CliqueBbTranscriptError::DuplicateDegreeCorePruneVertex { depth, vertex });
        }
        if !in_remaining[vertex] {
            return Err(CliqueBbTranscriptError::DegreeCorePruneVertexNotCandidate {
                depth,
                vertex,
            });
        }

        let residual_degree = node
            .candidates
            .iter()
            .copied()
            .filter(|&candidate| in_remaining[candidate] && graph.has_edge(vertex, candidate))
            .count();
        if residual_degree >= min_degree {
            return Err(CliqueBbTranscriptError::DegreeCorePruneTooWeak {
                depth,
                vertex,
                residual_degree,
                min_degree,
            });
        }

        seen_pruned[vertex] = true;
        in_remaining[vertex] = false;
    }

    let expected_child_candidates = node
        .candidates
        .iter()
        .copied()
        .filter(|&vertex| in_remaining[vertex])
        .collect::<Vec<_>>();
    validate_node_candidates(graph, depth, &child.candidates)?;
    if child.candidates != expected_child_candidates {
        return Err(
            CliqueBbTranscriptError::DegreeCorePruneChildCandidatesMismatch {
                depth,
                expected: expected_child_candidates,
                actual: child.candidates.clone(),
            },
        );
    }

    check.degree_core_prunes += 1;
    check.degree_core_pruned_vertices += pruned_vertices.len();
    replay_bb_node(graph, target_size, prefix_size, child, depth, check)
}

fn validate_node_candidates(
    graph: &ReplayableCliqueGraph,
    depth: usize,
    candidates: &[usize],
) -> Result<(), CliqueBbTranscriptError> {
    let vertex_count = graph.vertex_count();
    let mut seen = vec![false; vertex_count];

    for &vertex in candidates {
        if vertex >= vertex_count {
            return Err(CliqueBbTranscriptError::NodeCandidateOutOfRange {
                depth,
                vertex,
                vertex_count,
            });
        }
        if seen[vertex] {
            return Err(CliqueBbTranscriptError::DuplicateNodeCandidate { depth, vertex });
        }
        seen[vertex] = true;
    }

    Ok(())
}

fn check_node_color_classes(
    graph: &ReplayableCliqueGraph,
    depth: usize,
    candidates: &[usize],
    color_classes: &[Vec<usize>],
) -> Result<(), CliqueBbTranscriptError> {
    let vertex_count = graph.vertex_count();
    let mut is_candidate = vec![false; vertex_count];
    for &candidate in candidates {
        is_candidate[candidate] = true;
    }

    let mut seen = vec![false; vertex_count];
    for (color_class, vertices) in color_classes.iter().enumerate() {
        for (index, &lhs) in vertices.iter().enumerate() {
            check_color_vertex(graph, depth, lhs, &is_candidate)?;
            if seen[lhs] {
                return Err(CliqueBbTranscriptError::DuplicateColorVertex { depth, vertex: lhs });
            }
            seen[lhs] = true;

            for &rhs in &vertices[index + 1..] {
                check_color_vertex(graph, depth, rhs, &is_candidate)?;
                if graph.has_edge(lhs, rhs) {
                    return Err(CliqueBbTranscriptError::ColorClassHasEdge {
                        depth,
                        color_class,
                        lhs,
                        rhs,
                    });
                }
            }
        }
    }

    for &candidate in candidates {
        if !seen[candidate] {
            return Err(CliqueBbTranscriptError::MissingColorVertex {
                depth,
                vertex: candidate,
            });
        }
    }

    Ok(())
}

fn check_color_vertex(
    graph: &ReplayableCliqueGraph,
    depth: usize,
    vertex: usize,
    is_candidate: &[bool],
) -> Result<(), CliqueBbTranscriptError> {
    let vertex_count = graph.vertex_count();
    if vertex >= vertex_count {
        return Err(CliqueBbTranscriptError::ColorVertexOutOfRange {
            depth,
            vertex,
            vertex_count,
        });
    }
    if !is_candidate[vertex] {
        return Err(CliqueBbTranscriptError::ColorVertexNotCandidate { depth, vertex });
    }
    Ok(())
}

fn check_clique(
    graph: &ReplayableCliqueGraph,
    clique: &[usize],
) -> Result<(), CliqueCertificateError> {
    let vertex_count = graph.vertex_count();
    let mut seen = vec![false; vertex_count];
    for &vertex in clique {
        if vertex >= vertex_count {
            return Err(CliqueCertificateError::CliqueVertexOutOfRange {
                vertex,
                vertex_count,
            });
        }
        if seen[vertex] {
            return Err(CliqueCertificateError::DuplicateCliqueVertex { vertex });
        }
        seen[vertex] = true;
    }

    for (index, &lhs) in clique.iter().enumerate() {
        for &rhs in &clique[index + 1..] {
            if !graph.has_edge(lhs, rhs) {
                return Err(CliqueCertificateError::CliqueMissingEdge { lhs, rhs });
            }
        }
    }

    Ok(())
}

fn check_color_classes(
    graph: &ReplayableCliqueGraph,
    color_classes: &[Vec<usize>],
) -> Result<(), CliqueCertificateError> {
    let vertex_count = graph.vertex_count();
    let mut seen = vec![false; vertex_count];

    for (color_class, vertices) in color_classes.iter().enumerate() {
        for (index, &lhs) in vertices.iter().enumerate() {
            if lhs >= vertex_count {
                return Err(CliqueCertificateError::ColorVertexOutOfRange {
                    vertex: lhs,
                    vertex_count,
                });
            }
            if seen[lhs] {
                return Err(CliqueCertificateError::DuplicateColorVertex { vertex: lhs });
            }
            seen[lhs] = true;
            for &rhs in &vertices[index + 1..] {
                if rhs >= vertex_count {
                    return Err(CliqueCertificateError::ColorVertexOutOfRange {
                        vertex: rhs,
                        vertex_count,
                    });
                }
                if graph.has_edge(lhs, rhs) {
                    return Err(CliqueCertificateError::ColorClassHasEdge {
                        color_class,
                        lhs,
                        rhs,
                    });
                }
            }
        }
    }

    for (vertex, was_seen) in seen.into_iter().enumerate() {
        if !was_seen {
            return Err(CliqueCertificateError::MissingColorVertex { vertex });
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{
        check_replayable_clique_bb_partial_frontier, check_replayable_clique_bb_transcript,
        check_replayable_clique_certificate, merge_replayable_clique_bb_partial_frontier,
        CliqueBbBranchTranscript, CliqueBbNodeProof, CliqueBbNodeTranscript,
        CliqueBbPartialFrontierBranch, CliqueBbPartialFrontierMergeError,
        CliqueBbPartialFrontierNode, CliqueBbPartialFrontierProof, CliqueBbTranscriptError,
        CliqueCertificateError, ReplayableCliqueBbPartialFrontier, ReplayableCliqueBbTranscript,
        ReplayableCliqueCertificate, ReplayableCliqueGraph,
    };

    fn triangle_with_two_tails() -> ReplayableCliqueGraph {
        ReplayableCliqueGraph::from_edges(
            5,
            [(0, 1), (0, 2), (1, 2), (2, 3), (0, 4), (2, 4), (3, 4)],
        )
        .expect("test graph should be valid")
    }

    fn cycle5_graph() -> ReplayableCliqueGraph {
        ReplayableCliqueGraph::from_edges(5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)])
            .expect("test graph should be valid")
    }

    fn branch(vertex: usize, child: CliqueBbNodeTranscript) -> CliqueBbBranchTranscript {
        CliqueBbBranchTranscript {
            vertex,
            child: Box::new(child),
        }
    }

    fn branch_node(
        candidates: Vec<usize>,
        branches: Vec<CliqueBbBranchTranscript>,
    ) -> CliqueBbNodeTranscript {
        CliqueBbNodeTranscript {
            candidates,
            proof: CliqueBbNodeProof::Branch { branches },
        }
    }

    fn dynamic_branch_node(
        candidates: Vec<usize>,
        branches: Vec<CliqueBbBranchTranscript>,
        remaining: Option<CliqueBbNodeTranscript>,
    ) -> CliqueBbNodeTranscript {
        CliqueBbNodeTranscript {
            candidates,
            proof: CliqueBbNodeProof::DynamicBranch {
                branches,
                remaining: remaining.map(Box::new),
            },
        }
    }

    fn color_prune_node(
        candidates: Vec<usize>,
        color_classes: Vec<Vec<usize>>,
    ) -> CliqueBbNodeTranscript {
        CliqueBbNodeTranscript {
            candidates,
            proof: CliqueBbNodeProof::ColorPrune { color_classes },
        }
    }

    fn degree_core_prune_node(
        candidates: Vec<usize>,
        pruned_vertices: Vec<usize>,
        child: CliqueBbNodeTranscript,
    ) -> CliqueBbNodeTranscript {
        CliqueBbNodeTranscript {
            candidates,
            proof: CliqueBbNodeProof::DegreeCorePrune {
                pruned_vertices,
                child: Box::new(child),
            },
        }
    }

    fn cardinality_prune_node(candidates: Vec<usize>) -> CliqueBbNodeTranscript {
        CliqueBbNodeTranscript {
            candidates,
            proof: CliqueBbNodeProof::CardinalityPrune {},
        }
    }

    fn empty_prune_node(candidates: Vec<usize>) -> CliqueBbNodeTranscript {
        CliqueBbNodeTranscript {
            candidates,
            proof: CliqueBbNodeProof::EmptyCandidatePrune {},
        }
    }

    fn partial_branch(
        vertex: usize,
        child: CliqueBbPartialFrontierNode,
    ) -> CliqueBbPartialFrontierBranch {
        CliqueBbPartialFrontierBranch {
            vertex,
            child: Box::new(child),
        }
    }

    fn partial_branch_node(
        candidates: Vec<usize>,
        branches: Vec<CliqueBbPartialFrontierBranch>,
    ) -> CliqueBbPartialFrontierNode {
        CliqueBbPartialFrontierNode {
            candidates,
            proof: CliqueBbPartialFrontierProof::Branch { branches },
        }
    }

    fn partial_dynamic_branch_node(
        candidates: Vec<usize>,
        branches: Vec<CliqueBbPartialFrontierBranch>,
        remaining: Option<CliqueBbPartialFrontierNode>,
    ) -> CliqueBbPartialFrontierNode {
        CliqueBbPartialFrontierNode {
            candidates,
            proof: CliqueBbPartialFrontierProof::DynamicBranch {
                branches,
                remaining: remaining.map(Box::new),
            },
        }
    }

    fn partial_color_prune_node(
        candidates: Vec<usize>,
        color_classes: Vec<Vec<usize>>,
    ) -> CliqueBbPartialFrontierNode {
        CliqueBbPartialFrontierNode {
            candidates,
            proof: CliqueBbPartialFrontierProof::ColorPrune { color_classes },
        }
    }

    fn partial_cardinality_prune_node(candidates: Vec<usize>) -> CliqueBbPartialFrontierNode {
        CliqueBbPartialFrontierNode {
            candidates,
            proof: CliqueBbPartialFrontierProof::CardinalityPrune {},
        }
    }

    fn partial_empty_prune_node(candidates: Vec<usize>) -> CliqueBbPartialFrontierNode {
        CliqueBbPartialFrontierNode {
            candidates,
            proof: CliqueBbPartialFrontierProof::EmptyCandidatePrune {},
        }
    }

    fn open_obligation_node(candidates: Vec<usize>) -> CliqueBbPartialFrontierNode {
        CliqueBbPartialFrontierNode {
            candidates,
            proof: CliqueBbPartialFrontierProof::OpenObligation {},
        }
    }

    fn valid_cycle5_no_triangle_transcript() -> ReplayableCliqueBbTranscript {
        ReplayableCliqueBbTranscript {
            target_size: 3,
            root: branch_node(
                vec![0, 1, 2, 3, 4],
                vec![
                    branch(0, color_prune_node(vec![1, 4], vec![vec![1, 4]])),
                    branch(1, cardinality_prune_node(vec![2])),
                    branch(2, cardinality_prune_node(vec![3])),
                    branch(3, cardinality_prune_node(vec![4])),
                    branch(4, empty_prune_node(vec![])),
                ],
            ),
        }
    }

    fn valid_cycle5_no_triangle_partial_frontier() -> ReplayableCliqueBbPartialFrontier {
        ReplayableCliqueBbPartialFrontier {
            target_size: 3,
            root: partial_branch_node(
                vec![0, 1, 2, 3, 4],
                vec![
                    partial_branch(0, partial_color_prune_node(vec![1, 4], vec![vec![1, 4]])),
                    partial_branch(1, partial_cardinality_prune_node(vec![2])),
                    partial_branch(2, partial_cardinality_prune_node(vec![3])),
                    partial_branch(3, partial_cardinality_prune_node(vec![4])),
                    partial_branch(4, partial_empty_prune_node(vec![])),
                ],
            ),
        }
    }

    #[test]
    fn validates_clique_and_color_class_upper_bound() {
        let graph = triangle_with_two_tails();
        let certificate = ReplayableCliqueCertificate {
            clique: vec![0, 1, 2],
            color_classes: vec![vec![0, 3], vec![1, 4], vec![2]],
        };

        let check = check_replayable_clique_certificate(&graph, &certificate)
            .expect("certificate should replay");

        assert_eq!(check.vertex_count, 5);
        assert_eq!(check.clique_size, 3);
        assert_eq!(check.color_class_count, 3);
        assert!(check.proves_exact_bound);
    }

    #[test]
    fn rejects_color_class_with_adjacent_vertices() {
        let graph = triangle_with_two_tails();
        let certificate = ReplayableCliqueCertificate {
            clique: vec![0, 1, 2],
            color_classes: vec![vec![0, 4], vec![1, 3], vec![2]],
        };

        let error = check_replayable_clique_certificate(&graph, &certificate)
            .expect_err("adjacent vertices cannot share a color class");

        assert_eq!(
            error,
            CliqueCertificateError::ColorClassHasEdge {
                color_class: 0,
                lhs: 0,
                rhs: 4,
            }
        );
    }

    #[test]
    fn rejects_duplicate_color_vertices() {
        let graph = triangle_with_two_tails();
        let certificate = ReplayableCliqueCertificate {
            clique: vec![0, 1, 2],
            color_classes: vec![vec![0, 3], vec![1, 3], vec![2]],
        };

        let error = check_replayable_clique_certificate(&graph, &certificate)
            .expect_err("color classes must partition vertices");

        assert_eq!(
            error,
            CliqueCertificateError::DuplicateColorVertex { vertex: 3 }
        );
    }

    #[test]
    fn validates_branch_and_bound_no_k_transcript() {
        let graph = cycle5_graph();
        let transcript = valid_cycle5_no_triangle_transcript();

        let check = check_replayable_clique_bb_transcript(&graph, &transcript)
            .expect("no-triangle transcript should replay");

        assert_eq!(check.vertex_count, 5);
        assert_eq!(check.target_size, 3);
        assert_eq!(check.visited_nodes, 6);
        assert_eq!(check.branch_count, 5);
        assert_eq!(check.degree_core_prunes, 0);
        assert_eq!(check.degree_core_pruned_vertices, 0);
        assert_eq!(check.color_prunes, 1);
        assert_eq!(check.cardinality_prunes, 3);
        assert_eq!(check.empty_candidate_prunes, 1);
    }

    #[test]
    fn validates_dynamic_branch_transcript_with_remaining_tail() {
        let graph = cycle5_graph();
        let transcript = ReplayableCliqueBbTranscript {
            target_size: 3,
            root: dynamic_branch_node(
                vec![0, 1, 2, 3, 4],
                vec![branch(2, color_prune_node(vec![1, 3], vec![vec![1, 3]]))],
                Some(branch_node(
                    vec![0, 1, 3, 4],
                    vec![
                        branch(0, color_prune_node(vec![1, 4], vec![vec![1, 4]])),
                        branch(1, empty_prune_node(vec![])),
                        branch(3, cardinality_prune_node(vec![4])),
                        branch(4, empty_prune_node(vec![])),
                    ],
                )),
            ),
        };

        let check = check_replayable_clique_bb_transcript(&graph, &transcript)
            .expect("dynamic branch transcript should replay");

        assert_eq!(check.visited_nodes, 7);
        assert_eq!(check.branch_count, 5);
        assert_eq!(check.color_prunes, 2);
        assert_eq!(check.cardinality_prunes, 1);
        assert_eq!(check.empty_candidate_prunes, 2);
    }

    #[test]
    fn validates_degree_core_prune_node_in_transcript() {
        let graph =
            ReplayableCliqueGraph::from_edges(4, [(0, 1), (1, 2)]).expect("test graph is valid");
        let transcript = ReplayableCliqueBbTranscript {
            target_size: 3,
            root: degree_core_prune_node(
                vec![0, 1, 2, 3],
                vec![0, 1, 2, 3],
                empty_prune_node(vec![]),
            ),
        };

        let check = check_replayable_clique_bb_transcript(&graph, &transcript)
            .expect("degree-core prune transcript should replay");

        assert_eq!(check.vertex_count, 4);
        assert_eq!(check.target_size, 3);
        assert_eq!(check.visited_nodes, 2);
        assert_eq!(check.branch_count, 0);
        assert_eq!(check.degree_core_prunes, 1);
        assert_eq!(check.degree_core_pruned_vertices, 4);
        assert_eq!(check.empty_candidate_prunes, 1);
    }

    #[test]
    fn closed_partial_frontier_proves_no_target_clique() {
        let graph = cycle5_graph();
        let frontier = valid_cycle5_no_triangle_partial_frontier();

        let check = check_replayable_clique_bb_partial_frontier(&graph, &frontier)
            .expect("closed partial-frontier artifact should replay");

        assert_eq!(check.vertex_count, 5);
        assert_eq!(check.target_size, 3);
        assert_eq!(check.visited_nodes, 6);
        assert_eq!(check.branch_count, 5);
        assert_eq!(check.color_prunes, 1);
        assert_eq!(check.cardinality_prunes, 3);
        assert_eq!(check.empty_candidate_prunes, 1);
        assert_eq!(check.open_obligations, 0);
        assert_eq!(check.open_obligation_candidates, 0);
        assert_eq!(check.max_open_obligation_depth, 0);
        assert!(check.proves_no_target_clique);
    }

    #[test]
    fn open_obligation_leaf_keeps_partial_frontier_non_exact() {
        let graph = cycle5_graph();
        let frontier = ReplayableCliqueBbPartialFrontier {
            target_size: 3,
            root: partial_branch_node(
                vec![0, 1, 2, 3, 4],
                vec![
                    partial_branch(0, open_obligation_node(vec![1, 4])),
                    partial_branch(1, partial_cardinality_prune_node(vec![2])),
                    partial_branch(2, partial_cardinality_prune_node(vec![3])),
                    partial_branch(3, partial_cardinality_prune_node(vec![4])),
                    partial_branch(4, partial_empty_prune_node(vec![])),
                ],
            ),
        };

        let check = check_replayable_clique_bb_partial_frontier(&graph, &frontier)
            .expect("explicit open frontier should replay");

        assert_eq!(check.visited_nodes, 6);
        assert_eq!(check.branch_count, 5);
        assert_eq!(check.open_obligations, 1);
        assert_eq!(check.open_obligation_candidates, 2);
        assert_eq!(check.max_open_obligation_depth, 1);
        assert!(!check.proves_no_target_clique);
    }

    #[test]
    fn merge_partial_frontier_replaces_open_obligation_with_closed_patch() {
        let graph = cycle5_graph();
        let mut frontier = ReplayableCliqueBbPartialFrontier {
            target_size: 3,
            root: partial_branch_node(
                vec![0, 1, 2, 3, 4],
                vec![
                    partial_branch(0, open_obligation_node(vec![1, 4])),
                    partial_branch(1, partial_cardinality_prune_node(vec![2])),
                    partial_branch(2, partial_cardinality_prune_node(vec![3])),
                    partial_branch(3, partial_cardinality_prune_node(vec![4])),
                    partial_branch(4, partial_empty_prune_node(vec![])),
                ],
            ),
        };
        let patch = partial_color_prune_node(vec![1, 4], vec![vec![1, 4]]);

        let merged =
            merge_replayable_clique_bb_partial_frontier(&graph, &mut frontier, &[1, 4], patch)
                .expect("closed patch should replace matching open obligation");

        assert!(merged.replaced);
        assert_eq!(merged.check.open_obligations, 0);
        assert!(merged.check.proves_no_target_clique);

        let replay = check_replayable_clique_bb_partial_frontier(&graph, &frontier)
            .expect("merged frontier should replay");
        assert_eq!(replay.open_obligations, 0);
        assert!(replay.proves_no_target_clique);
    }

    #[test]
    fn merge_partial_frontier_can_skip_unrelated_open_obligations() {
        let graph = cycle5_graph();
        let mut frontier = ReplayableCliqueBbPartialFrontier {
            target_size: 3,
            root: partial_dynamic_branch_node(
                vec![0, 1, 2, 3, 4],
                vec![partial_branch(2, open_obligation_node(vec![1, 3]))],
                Some(open_obligation_node(vec![0, 1, 3, 4])),
            ),
        };
        let patch = partial_branch_node(
            vec![0, 1, 3, 4],
            vec![
                partial_branch(0, partial_color_prune_node(vec![1, 4], vec![vec![1, 4]])),
                partial_branch(1, partial_empty_prune_node(vec![])),
                partial_branch(3, partial_cardinality_prune_node(vec![4])),
                partial_branch(4, partial_empty_prune_node(vec![])),
            ],
        );

        let merged = merge_replayable_clique_bb_partial_frontier(
            &graph,
            &mut frontier,
            &[0, 1, 3, 4],
            patch,
        )
        .expect("later matching open obligation should be replaceable");

        assert!(merged.replaced);
        assert_eq!(merged.check.open_obligations, 1);
        assert_eq!(merged.check.open_obligation_candidates, 2);
        assert!(!merged.check.proves_no_target_clique);
    }

    #[test]
    fn merge_partial_frontier_rejects_open_patch() {
        let graph = cycle5_graph();
        let mut frontier = ReplayableCliqueBbPartialFrontier {
            target_size: 3,
            root: partial_branch_node(
                vec![0, 1, 2, 3, 4],
                vec![
                    partial_branch(0, open_obligation_node(vec![1, 4])),
                    partial_branch(1, partial_cardinality_prune_node(vec![2])),
                    partial_branch(2, partial_cardinality_prune_node(vec![3])),
                    partial_branch(3, partial_cardinality_prune_node(vec![4])),
                    partial_branch(4, partial_empty_prune_node(vec![])),
                ],
            ),
        };
        let patch = open_obligation_node(vec![1, 4]);

        let error =
            merge_replayable_clique_bb_partial_frontier(&graph, &mut frontier, &[1, 4], patch)
                .expect_err("merge patch must be closed before replacement");

        assert_eq!(
            error,
            CliqueBbPartialFrontierMergeError::PatchNotClosed {
                open_obligations: 1,
            }
        );
    }

    #[test]
    fn merge_partial_frontier_rejects_nonopen_target_without_mutating() {
        let graph = cycle5_graph();
        let mut frontier = valid_cycle5_no_triangle_partial_frontier();
        let original = frontier.clone();
        let patch = partial_color_prune_node(vec![1, 4], vec![vec![1, 4]]);

        let error =
            merge_replayable_clique_bb_partial_frontier(&graph, &mut frontier, &[1, 4], patch)
                .expect_err("closed target nodes are not replaceable obligations");

        assert_eq!(
            error,
            CliqueBbPartialFrontierMergeError::TargetNotOpen {
                candidates: vec![1, 4],
            }
        );
        assert_eq!(frontier, original);
    }

    #[test]
    fn merge_partial_frontier_rejects_bad_patch_without_mutating() {
        let graph = cycle5_graph();
        let mut frontier = ReplayableCliqueBbPartialFrontier {
            target_size: 3,
            root: partial_branch_node(
                vec![0, 1, 2, 3, 4],
                vec![
                    partial_branch(0, open_obligation_node(vec![1, 4])),
                    partial_branch(1, partial_cardinality_prune_node(vec![2])),
                    partial_branch(2, partial_cardinality_prune_node(vec![3])),
                    partial_branch(3, partial_cardinality_prune_node(vec![4])),
                    partial_branch(4, partial_empty_prune_node(vec![])),
                ],
            ),
        };
        let original = frontier.clone();
        let patch = partial_color_prune_node(vec![1, 4], vec![vec![1], vec![4]]);

        let error =
            merge_replayable_clique_bb_partial_frontier(&graph, &mut frontier, &[1, 4], patch)
                .expect_err("patch with weak color proof must be rejected");

        assert_eq!(
            error,
            CliqueBbPartialFrontierMergeError::Replay(CliqueBbTranscriptError::ColorPruneTooWeak {
                depth: 1,
                prefix_size: 1,
                color_class_count: 2,
                target_size: 3,
            })
        );
        assert_eq!(frontier, original);
    }

    #[test]
    fn dynamic_partial_frontier_replays_remaining_open_tail_at_same_depth() {
        let graph = cycle5_graph();
        let frontier = ReplayableCliqueBbPartialFrontier {
            target_size: 3,
            root: partial_dynamic_branch_node(
                vec![0, 1, 2, 3, 4],
                vec![partial_branch(
                    2,
                    partial_color_prune_node(vec![1, 3], vec![vec![1, 3]]),
                )],
                Some(open_obligation_node(vec![0, 1, 3, 4])),
            ),
        };

        let check = check_replayable_clique_bb_partial_frontier(&graph, &frontier)
            .expect("dynamic partial frontier should keep explicit open work");

        assert_eq!(check.visited_nodes, 3);
        assert_eq!(check.branch_count, 1);
        assert_eq!(check.color_prunes, 1);
        assert_eq!(check.open_obligations, 1);
        assert_eq!(check.open_obligation_candidates, 4);
        assert_eq!(check.max_open_obligation_depth, 0);
        assert!(!check.proves_no_target_clique);
    }

    #[test]
    fn rejects_degree_core_prune_when_residual_degree_is_high_enough() {
        let graph = ReplayableCliqueGraph::from_edges(3, [(0, 1), (0, 2), (1, 2)])
            .expect("test graph is valid");
        let transcript = ReplayableCliqueBbTranscript {
            target_size: 3,
            root: degree_core_prune_node(
                vec![0, 1, 2],
                vec![0],
                cardinality_prune_node(vec![1, 2]),
            ),
        };

        let error = check_replayable_clique_bb_transcript(&graph, &transcript)
            .expect_err("degree-core prune must prove each removed vertex is low-degree");

        assert_eq!(
            error,
            CliqueBbTranscriptError::DegreeCorePruneTooWeak {
                depth: 0,
                vertex: 0,
                residual_degree: 2,
                min_degree: 2,
            }
        );
    }

    #[test]
    fn rejects_degree_core_prune_child_candidate_mismatch() {
        let graph =
            ReplayableCliqueGraph::from_edges(4, [(0, 1), (1, 2)]).expect("test graph is valid");
        let transcript = ReplayableCliqueBbTranscript {
            target_size: 3,
            root: degree_core_prune_node(
                vec![0, 1, 2, 3],
                vec![0],
                cardinality_prune_node(vec![2, 3]),
            ),
        };

        let error = check_replayable_clique_bb_transcript(&graph, &transcript)
            .expect_err("core-prune child must match remaining candidates");

        assert_eq!(
            error,
            CliqueBbTranscriptError::DegreeCorePruneChildCandidatesMismatch {
                depth: 0,
                expected: vec![1, 2, 3],
                actual: vec![2, 3],
            }
        );
    }

    #[test]
    fn rejects_missing_branch_in_transcript() {
        let graph = cycle5_graph();
        let mut transcript = valid_cycle5_no_triangle_transcript();
        if let CliqueBbNodeProof::Branch { branches } = &mut transcript.root.proof {
            branches.truncate(2);
        }

        let error = check_replayable_clique_bb_transcript(&graph, &transcript)
            .expect_err("missing branch should not replay");

        assert_eq!(
            error,
            CliqueBbTranscriptError::MissingBranch {
                depth: 0,
                vertex: 2,
            }
        );
    }

    #[test]
    fn rejects_out_of_order_branch_in_transcript() {
        let graph = cycle5_graph();
        let mut transcript = valid_cycle5_no_triangle_transcript();
        if let CliqueBbNodeProof::Branch { branches } = &mut transcript.root.proof {
            branches.swap(1, 2);
        }

        let error = check_replayable_clique_bb_transcript(&graph, &transcript)
            .expect_err("out-of-order branch should not replay");

        assert_eq!(
            error,
            CliqueBbTranscriptError::BranchOrderMismatch {
                depth: 0,
                index: 1,
                expected: 1,
                actual: 2,
            }
        );
    }

    #[test]
    fn rejects_invalid_child_candidates_in_transcript() {
        let graph = cycle5_graph();
        let mut transcript = valid_cycle5_no_triangle_transcript();
        if let CliqueBbNodeProof::Branch { branches } = &mut transcript.root.proof {
            branches[0].child.candidates = vec![1, 4, 2];
        }

        let error = check_replayable_clique_bb_transcript(&graph, &transcript)
            .expect_err("child candidates must equal the replayed branch suffix");

        assert_eq!(
            error,
            CliqueBbTranscriptError::ChildCandidatesMismatch {
                parent_depth: 0,
                branch_vertex: 0,
                expected: vec![1, 4],
                actual: vec![1, 4, 2],
            }
        );
    }

    #[test]
    fn rejects_dynamic_branch_vertex_not_in_current_remaining_set() {
        let graph = cycle5_graph();
        let transcript = ReplayableCliqueBbTranscript {
            target_size: 3,
            root: branch_node(
                vec![0, 1, 2, 3, 4],
                vec![
                    branch(
                        0,
                        dynamic_branch_node(
                            vec![1, 4],
                            vec![branch(2, empty_prune_node(vec![]))],
                            None,
                        ),
                    ),
                    branch(1, cardinality_prune_node(vec![2])),
                    branch(2, cardinality_prune_node(vec![3])),
                    branch(3, cardinality_prune_node(vec![4])),
                    branch(4, empty_prune_node(vec![])),
                ],
            ),
        };

        let error = check_replayable_clique_bb_transcript(&graph, &transcript)
            .expect_err("dynamic branch vertex must be in the current remaining set");

        assert_eq!(
            error,
            CliqueBbTranscriptError::DynamicBranchVertexNotRemaining {
                depth: 1,
                vertex: 2,
            }
        );
    }

    #[test]
    fn rejects_duplicate_dynamic_branch_vertex() {
        let graph = cycle5_graph();
        let transcript = ReplayableCliqueBbTranscript {
            target_size: 3,
            root: dynamic_branch_node(
                vec![0, 1, 2, 3, 4],
                vec![
                    branch(2, color_prune_node(vec![1, 3], vec![vec![1, 3]])),
                    branch(2, color_prune_node(vec![1, 3], vec![vec![1, 3]])),
                ],
                None,
            ),
        };

        let error = check_replayable_clique_bb_transcript(&graph, &transcript)
            .expect_err("dynamic branch vertices must be unique");

        assert_eq!(
            error,
            CliqueBbTranscriptError::DuplicateDynamicBranchVertex {
                depth: 0,
                vertex: 2,
            }
        );
    }

    #[test]
    fn rejects_dynamic_child_candidate_mismatch() {
        let graph = cycle5_graph();
        let transcript = ReplayableCliqueBbTranscript {
            target_size: 3,
            root: dynamic_branch_node(
                vec![0, 1, 2, 3, 4],
                vec![branch(2, color_prune_node(vec![3, 1], vec![vec![3, 1]]))],
                Some(cardinality_prune_node(vec![0, 1, 3, 4])),
            ),
        };

        let error = check_replayable_clique_bb_transcript(&graph, &transcript)
            .expect_err("dynamic child candidates must follow remaining order");

        assert_eq!(
            error,
            CliqueBbTranscriptError::ChildCandidatesMismatch {
                parent_depth: 0,
                branch_vertex: 2,
                expected: vec![1, 3],
                actual: vec![3, 1],
            }
        );
    }

    #[test]
    fn rejects_missing_dynamic_remaining_tail() {
        let graph = cycle5_graph();
        let transcript = ReplayableCliqueBbTranscript {
            target_size: 3,
            root: dynamic_branch_node(
                vec![0, 1, 2, 3, 4],
                vec![branch(2, color_prune_node(vec![1, 3], vec![vec![1, 3]]))],
                None,
            ),
        };

        let error = check_replayable_clique_bb_transcript(&graph, &transcript)
            .expect_err("unbranched dynamic remaining candidates need a typed tail");

        assert_eq!(
            error,
            CliqueBbTranscriptError::MissingDynamicRemainingTail {
                depth: 0,
                vertex: 0,
            }
        );
    }

    #[test]
    fn rejects_unexpected_dynamic_remaining_tail_when_empty() {
        let graph = ReplayableCliqueGraph::from_edges(1, []).expect("test graph is valid");
        let transcript = ReplayableCliqueBbTranscript {
            target_size: 2,
            root: dynamic_branch_node(
                vec![0],
                vec![branch(0, empty_prune_node(vec![]))],
                Some(empty_prune_node(vec![])),
            ),
        };

        let error = check_replayable_clique_bb_transcript(&graph, &transcript)
            .expect_err("empty dynamic remaining set must not have a tail");

        assert_eq!(
            error,
            CliqueBbTranscriptError::UnexpectedDynamicRemainingTail { depth: 0 }
        );
    }

    #[test]
    fn rejects_dynamic_remaining_tail_candidate_mismatch() {
        let graph = cycle5_graph();
        let transcript = ReplayableCliqueBbTranscript {
            target_size: 3,
            root: dynamic_branch_node(
                vec![0, 1, 2, 3, 4],
                vec![branch(2, color_prune_node(vec![1, 3], vec![vec![1, 3]]))],
                Some(cardinality_prune_node(vec![0, 3, 1, 4])),
            ),
        };

        let error = check_replayable_clique_bb_transcript(&graph, &transcript)
            .expect_err("dynamic remaining tail must preserve remaining order");

        assert_eq!(
            error,
            CliqueBbTranscriptError::DynamicRemainingCandidatesMismatch {
                depth: 0,
                expected: vec![0, 1, 3, 4],
                actual: vec![0, 3, 1, 4],
            }
        );
    }

    #[test]
    fn partial_frontier_rejects_missing_branch_instead_of_implying_open() {
        let graph = cycle5_graph();
        let frontier = ReplayableCliqueBbPartialFrontier {
            target_size: 3,
            root: partial_branch_node(
                vec![0, 1, 2, 3, 4],
                vec![partial_branch(0, open_obligation_node(vec![1, 4]))],
            ),
        };

        let error = check_replayable_clique_bb_partial_frontier(&graph, &frontier)
            .expect_err("missing branches must be explicit open obligations");

        assert_eq!(
            error,
            CliqueBbTranscriptError::MissingBranch {
                depth: 0,
                vertex: 1,
            }
        );
    }

    #[test]
    fn partial_frontier_rejects_missing_dynamic_remaining_tail() {
        let graph = cycle5_graph();
        let frontier = ReplayableCliqueBbPartialFrontier {
            target_size: 3,
            root: partial_dynamic_branch_node(
                vec![0, 1, 2, 3, 4],
                vec![partial_branch(
                    2,
                    partial_color_prune_node(vec![1, 3], vec![vec![1, 3]]),
                )],
                None,
            ),
        };

        let error = check_replayable_clique_bb_partial_frontier(&graph, &frontier)
            .expect_err("partial dynamic frontier must use typed tails for open work");

        assert_eq!(
            error,
            CliqueBbTranscriptError::MissingDynamicRemainingTail {
                depth: 0,
                vertex: 0,
            }
        );
    }

    #[test]
    fn partial_frontier_rejects_open_obligation_that_cardinality_already_closes() {
        let graph = cycle5_graph();
        let frontier = ReplayableCliqueBbPartialFrontier {
            target_size: 3,
            root: partial_branch_node(
                vec![0, 1, 2, 3, 4],
                vec![
                    partial_branch(0, partial_color_prune_node(vec![1, 4], vec![vec![1, 4]])),
                    partial_branch(1, open_obligation_node(vec![2])),
                    partial_branch(2, partial_cardinality_prune_node(vec![3])),
                    partial_branch(3, partial_cardinality_prune_node(vec![4])),
                    partial_branch(4, partial_empty_prune_node(vec![])),
                ],
            ),
        };

        let error = check_replayable_clique_bb_partial_frontier(&graph, &frontier)
            .expect_err("trivially closed obligations should be malformed");

        assert_eq!(
            error,
            CliqueBbTranscriptError::OpenObligationAlreadyClosed {
                depth: 1,
                prefix_size: 1,
                candidate_count: 1,
                target_size: 3,
            }
        );
    }

    #[test]
    fn dynamic_partial_frontier_retains_open_obligation_already_closed() {
        let graph = ReplayableCliqueGraph::from_edges(1, []).expect("test graph is valid");
        let frontier = ReplayableCliqueBbPartialFrontier {
            target_size: 3,
            root: partial_dynamic_branch_node(vec![0], vec![], Some(open_obligation_node(vec![0]))),
        };

        let error = check_replayable_clique_bb_partial_frontier(&graph, &frontier)
            .expect_err("already closed dynamic tail must not be open");

        assert_eq!(
            error,
            CliqueBbTranscriptError::OpenObligationAlreadyClosed {
                depth: 0,
                prefix_size: 0,
                candidate_count: 1,
                target_size: 3,
            }
        );
    }

    #[test]
    fn rejects_invalid_color_prune_in_transcript() {
        let graph = cycle5_graph();
        let transcript = ReplayableCliqueBbTranscript {
            target_size: 3,
            root: color_prune_node(vec![0, 1, 2, 3, 4], vec![vec![0, 1], vec![2, 4], vec![3]]),
        };

        let error = check_replayable_clique_bb_transcript(&graph, &transcript)
            .expect_err("adjacent vertices cannot share a color class");

        assert_eq!(
            error,
            CliqueBbTranscriptError::ColorClassHasEdge {
                depth: 0,
                color_class: 0,
                lhs: 0,
                rhs: 1,
            }
        );
    }

    #[test]
    fn rejects_duplicate_root_candidate_in_transcript() {
        let graph = cycle5_graph();
        let transcript = ReplayableCliqueBbTranscript {
            target_size: 3,
            root: empty_prune_node(vec![0, 0, 1, 2, 3]),
        };

        let error = check_replayable_clique_bb_transcript(&graph, &transcript)
            .expect_err("root candidates must not contain duplicates");

        assert_eq!(
            error,
            CliqueBbTranscriptError::DuplicateRootCandidate { vertex: 0 }
        );
    }

    #[test]
    fn rejects_out_of_range_root_candidate_in_transcript() {
        let graph = cycle5_graph();
        let transcript = ReplayableCliqueBbTranscript {
            target_size: 3,
            root: empty_prune_node(vec![0, 1, 2, 3, 5]),
        };

        let error = check_replayable_clique_bb_transcript(&graph, &transcript)
            .expect_err("root candidates must be graph vertices");

        assert_eq!(
            error,
            CliqueBbTranscriptError::RootCandidateOutOfRange {
                vertex: 5,
                vertex_count: 5,
            }
        );
    }
}
