// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::{ChcProblem, ClauseHead, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ArtVertexId(pub(crate) u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ArtEdgeId(pub(crate) u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ArtLocation {
    Predicate(PredicateId),
    Error,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct OutgoingClause {
    clause_idx: usize,
    target: ArtLocation,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ArtEdge {
    pub(crate) source: ArtVertexId,
    pub(crate) target: ArtVertexId,
    pub(crate) clause_idx: usize,
}

/// Abstract Reachability Tree for the LAWI engine.
///
/// This tracks the same core topology as Golem's `AbstractReachabilityTree`
/// (`reference/golem/src/engine/Lawi.cc`): parent links, children edges,
/// path/ancestor queries, and expansion by outgoing CHC clauses.
#[derive(Debug, Clone)]
pub(crate) struct AbstractReachabilityTree {
    root: ArtVertexId,
    next_vertex: u32,
    next_edge: u32,
    is_linear: bool,
    vertex_location: FxHashMap<ArtVertexId, ArtLocation>,
    parent: FxHashMap<ArtVertexId, ArtEdgeId>,
    children: FxHashMap<ArtVertexId, Vec<ArtEdgeId>>,
    edges: FxHashMap<ArtEdgeId, ArtEdge>,
    vertices_by_location: FxHashMap<ArtLocation, Vec<ArtVertexId>>,
    outgoing: FxHashMap<PredicateId, Vec<OutgoingClause>>,
}

impl AbstractReachabilityTree {
    pub(crate) fn try_new(problem: &ChcProblem) -> Option<Self> {
        let root_pred = pick_root_predicate(problem)?;
        let root = ArtVertexId(0);
        let mut vertices_by_location = FxHashMap::default();
        vertices_by_location.insert(ArtLocation::Predicate(root_pred), vec![root]);

        let (outgoing, is_linear) = build_outgoing_clauses(problem);

        let mut vertex_location = FxHashMap::default();
        vertex_location.insert(root, ArtLocation::Predicate(root_pred));

        Some(Self {
            root,
            next_vertex: 1,
            next_edge: 0,
            is_linear,
            vertex_location,
            parent: FxHashMap::default(),
            children: FxHashMap::default(),
            edges: FxHashMap::default(),
            vertices_by_location,
            outgoing,
        })
    }

    pub(crate) fn root(&self) -> ArtVertexId {
        self.root
    }

    pub(crate) fn is_linear(&self) -> bool {
        self.is_linear
    }

    pub(crate) fn vertex_count(&self) -> usize {
        self.next_vertex as usize
    }

    pub(crate) fn location(&self, vertex: ArtVertexId) -> ArtLocation {
        self.vertex_location
            .get(&vertex)
            .copied()
            .expect("invariant: every vertex has a location")
    }

    pub(crate) fn same_location(&self, a: ArtVertexId, b: ArtVertexId) -> bool {
        self.location(a) == self.location(b)
    }

    pub(crate) fn is_error_location(&self, vertex: ArtVertexId) -> bool {
        matches!(self.location(vertex), ArtLocation::Error)
    }

    pub(crate) fn is_leaf(&self, vertex: ArtVertexId) -> bool {
        self.children.get(&vertex).is_none_or(Vec::is_empty)
    }

    pub(crate) fn edge(&self, edge: ArtEdgeId) -> Option<ArtEdge> {
        self.edges.get(&edge).copied()
    }

    pub(crate) fn expand(&mut self, vertex: ArtVertexId) -> Vec<ArtVertexId> {
        if !self.is_leaf(vertex) {
            return Vec::new();
        }

        let ArtLocation::Predicate(location) = self.location(vertex) else {
            return Vec::new();
        };

        let outgoing = self.outgoing.get(&location).cloned().unwrap_or_default();
        let mut children = Vec::with_capacity(outgoing.len());

        for rule in outgoing {
            let child = ArtVertexId(self.next_vertex);
            self.next_vertex += 1;
            self.vertex_location.insert(child, rule.target);
            self.vertices_by_location
                .entry(rule.target)
                .or_default()
                .push(child);

            let edge_id = ArtEdgeId(self.next_edge);
            self.next_edge += 1;
            self.parent.insert(child, edge_id);
            self.children.entry(vertex).or_default().push(edge_id);
            self.edges.insert(
                edge_id,
                ArtEdge {
                    source: vertex,
                    target: child,
                    clause_idx: rule.clause_idx,
                },
            );
            children.push(child);
        }

        children
    }

    pub(crate) fn is_ancestor(&self, ancestor: ArtVertexId, descendant: ArtVertexId) -> bool {
        if ancestor == descendant {
            return true;
        }

        let mut current = descendant;
        while current != self.root {
            let Some(parent_edge) = self.parent.get(&current).copied() else {
                break;
            };
            let parent_vertex = self
                .edge(parent_edge)
                .expect("invariant: parent edge exists")
                .source;
            if parent_vertex == ancestor {
                return true;
            }
            current = parent_vertex;
        }

        false
    }

    pub(crate) fn ancestors_including(&self, vertex: ArtVertexId) -> Vec<ArtVertexId> {
        let mut result = vec![vertex];
        let mut current = vertex;
        while let Some(parent_edge) = self.parent.get(&current).copied() {
            let parent = self
                .edge(parent_edge)
                .expect("invariant: parent edge exists")
                .source;
            result.push(parent);
            current = parent;
        }
        result
    }

    pub(crate) fn descendants_including(&self, vertex: ArtVertexId) -> Vec<ArtVertexId> {
        let mut result = Vec::new();
        let mut stack = vec![vertex];

        while let Some(current) = stack.pop() {
            result.push(current);
            if let Some(children) = self.children.get(&current) {
                for edge in children {
                    stack.push(self.edge(*edge).expect("invariant: edge exists").target);
                }
            }
        }

        result
    }

    pub(crate) fn earlier_at_same_location(
        &self,
        vertex: ArtVertexId,
        limit: usize,
    ) -> Vec<ArtVertexId> {
        let location = self.location(vertex);
        let Some(vertices) = self.vertices_by_location.get(&location) else {
            return Vec::new();
        };
        let Some(pos) = vertices.iter().position(|v| *v == vertex) else {
            return Vec::new();
        };
        vertices[..pos].iter().rev().take(limit).copied().collect()
    }

    /// Returns the edge path from root to the given vertex.
    pub(crate) fn path_from_root(&self, vertex: ArtVertexId) -> Vec<ArtEdgeId> {
        let mut path = Vec::new();
        let mut current = vertex;
        while current != self.root {
            let Some(edge_id) = self.parent.get(&current).copied() else {
                return Vec::new();
            };
            path.push(edge_id);
            current = self
                .edge(edge_id)
                .expect("invariant: parent edge exists")
                .source;
        }
        path.reverse();
        path
    }

    /// Returns the vertices along the path from root to the given vertex (inclusive).
    pub(crate) fn path_vertices_from_root(&self, vertex: ArtVertexId) -> Vec<ArtVertexId> {
        let edges = self.path_from_root(vertex);
        let mut vertices = Vec::with_capacity(edges.len() + 1);
        vertices.push(self.root);
        for edge_id in &edges {
            let edge = self.edge(*edge_id).expect("invariant: edge exists");
            vertices.push(edge.target);
        }
        vertices
    }

    #[cfg(test)]
    pub(crate) fn nearest_common_ancestor(&self, v1: ArtVertexId, v2: ArtVertexId) -> ArtVertexId {
        let v1_ancestors: ay_core::kani_compat::DetHashSet<_> =
            self.ancestors_including(v1).into_iter().collect();
        for ancestor in self.ancestors_including(v2) {
            if v1_ancestors.contains(&ancestor) {
                return ancestor;
            }
        }
        self.root
    }

    #[cfg(test)]
    pub(crate) fn path_from_ancestor(
        &self,
        ancestor: ArtVertexId,
        descendant: ArtVertexId,
    ) -> Vec<ArtEdgeId> {
        let mut path = Vec::new();
        let mut current = descendant;
        while current != ancestor {
            let Some(edge_id) = self.parent.get(&current).copied() else {
                return Vec::new();
            };
            path.push(edge_id);
            current = self
                .edge(edge_id)
                .expect("invariant: parent edge exists")
                .source;
        }
        path.reverse();
        path
    }
}

fn pick_root_predicate(problem: &ChcProblem) -> Option<PredicateId> {
    problem
        .facts()
        .find_map(|clause| clause.head.predicate_id())
        .or_else(|| problem.predicates().first().map(|p| p.id))
}

fn build_outgoing_clauses(
    problem: &ChcProblem,
) -> (FxHashMap<PredicateId, Vec<OutgoingClause>>, bool) {
    let mut outgoing: FxHashMap<PredicateId, Vec<OutgoingClause>> = FxHashMap::default();
    let mut is_linear = true;

    for (idx, clause) in problem.clauses().iter().enumerate() {
        if clause.body.predicates.len() > 1 {
            is_linear = false;
            continue;
        }

        let Some((source, _)) = clause.body.predicates.first() else {
            // Fact clause.
            continue;
        };

        let target = match clause.head {
            ClauseHead::Predicate(pred, _) => ArtLocation::Predicate(pred),
            ClauseHead::False => ArtLocation::Error,
        };
        outgoing.entry(*source).or_default().push(OutgoingClause {
            clause_idx: idx,
            target,
        });
    }

    for edges in outgoing.values_mut() {
        // Mirror Golem expansion order: error transitions first.
        edges.sort_by_key(|edge| !matches!(edge.target, ArtLocation::Error));
    }

    (outgoing, is_linear)
}
