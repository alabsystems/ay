// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Predicate-level graph infrastructure for CHC transformations.

use std::collections::BTreeMap;
use std::fmt;

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use thiserror::Error;

use crate::tarjan::tarjan_scc_dense;
use crate::{
    ActionId, ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, Predicate,
    PredicateId,
};

pub(crate) const ENTRY_VERTEX: ChcVertex = ChcVertex::Entry;
pub(crate) const EXIT_VERTEX: ChcVertex = ChcVertex::Exit;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum ChcVertex {
    Entry,
    Predicate(PredicateId),
    Exit,
}

impl fmt::Display for ChcVertex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Entry => write!(f, "entry"),
            Self::Predicate(id) => write!(f, "{id}"),
            Self::Exit => write!(f, "exit"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct EdgeId(usize);

impl EdgeId {
    pub(crate) fn index(self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone)]
pub(crate) struct DirectedEdge {
    id: EdgeId,
    source: ChcVertex,
    target: ChcVertex,
    source_args: Vec<ChcExpr>,
    target_args: Vec<ChcExpr>,
    constraint: Option<ChcExpr>,
    action_id: Option<ActionId>,
    origin_clause_indices: Vec<usize>,
}

impl DirectedEdge {
    pub(crate) fn id(&self) -> EdgeId {
        self.id
    }

    pub(crate) fn source(&self) -> ChcVertex {
        self.source
    }

    pub(crate) fn target(&self) -> ChcVertex {
        self.target
    }

    pub(crate) fn source_args(&self) -> &[ChcExpr] {
        &self.source_args
    }

    pub(crate) fn target_args(&self) -> &[ChcExpr] {
        &self.target_args
    }

    pub(crate) fn constraint(&self) -> Option<&ChcExpr> {
        self.constraint.as_ref()
    }

    pub(crate) fn action_id(&self) -> Option<ActionId> {
        self.action_id
    }

    pub(crate) fn origin_clause_indices(&self) -> &[usize] {
        &self.origin_clause_indices
    }

    pub(crate) fn label(&self) -> ChcExpr {
        self.constraint.clone().unwrap_or(ChcExpr::Bool(true))
    }
}

#[derive(Debug, Error, PartialEq, Eq)]
pub(crate) enum ChcGraphError {
    #[error("clause {clause_index} has {predicate_count} body predicates; ChcDirectedGraph requires linear CHC clauses")]
    NonLinearClause {
        clause_index: usize,
        predicate_count: usize,
    },
    #[error("unknown predicate id {0}")]
    UnknownPredicate(PredicateId),
    #[error("vertex contraction requires at least two predicate vertices")]
    ContractionTooSmall,
    #[error("vertex contraction received duplicate vertex {0}")]
    DuplicateContractionVertex(ChcVertex),
    #[error("vertex contraction cannot include special vertex {0}")]
    SpecialContractionVertex(ChcVertex),
    #[error("vertices selected for contraction are not connected by graph edges")]
    DisconnectedContraction,
}

#[derive(Debug, Clone)]
pub(crate) struct LocationWitness {
    pub(crate) vertex: ChcVertex,
    pub(crate) variable: ChcVar,
    pub(crate) predicate_arg_index: usize,
}

#[derive(Debug, Clone)]
pub(crate) struct PositionWitness {
    pub(crate) vertex: ChcVertex,
    pub(crate) position: usize,
    pub(crate) variable: ChcVar,
    pub(crate) predicate_arg_index: usize,
}

#[derive(Debug, Clone)]
pub(crate) struct WitnessInfo {
    pub(crate) contracted_vertex: ChcVertex,
    pub(crate) original_vertices: Vec<ChcVertex>,
    pub(crate) locations: Vec<LocationWitness>,
    pub(crate) positions: Vec<PositionWitness>,
}

impl WitnessInfo {
    pub(crate) fn predicate_variables(&self) -> Vec<ChcVar> {
        let mut vars = vec![None; self.locations.len() + self.positions.len()];
        for loc in &self.locations {
            vars[loc.predicate_arg_index] = Some(loc.variable.clone());
        }
        for pos in &self.positions {
            vars[pos.predicate_arg_index] = Some(pos.variable.clone());
        }
        vars.into_iter()
            .map(|v| v.expect("witness argument indices must be dense"))
            .collect()
    }

    fn predicate_arg_exprs(&self) -> Vec<ChcExpr> {
        self.predicate_variables()
            .into_iter()
            .map(ChcExpr::var)
            .collect()
    }

    fn next_predicate_arg_exprs(&self) -> Vec<ChcExpr> {
        self.predicate_variables()
            .into_iter()
            .map(|v| ChcExpr::var(next_var(&v)))
            .collect()
    }

    fn location_var(&self, vertex: ChcVertex, next: bool) -> ChcVar {
        let var = self
            .locations
            .iter()
            .find(|loc| loc.vertex == vertex)
            .expect("contracted vertex must have a location witness")
            .variable
            .clone();
        if next {
            next_var(&var)
        } else {
            var
        }
    }

    fn position_var(&self, vertex: ChcVertex, position: usize, next: bool) -> ChcVar {
        let var = self
            .positions
            .iter()
            .find(|pos| pos.vertex == vertex && pos.position == position)
            .expect("contracted predicate argument must have a position witness")
            .variable
            .clone();
        if next {
            next_var(&var)
        } else {
            var
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct MergedEdge {
    pub(crate) retained: EdgeId,
    pub(crate) removed: Vec<EdgeId>,
    pub(crate) origin_clause_indices: Vec<usize>,
}

#[derive(Debug, Clone)]
pub(crate) struct AdjacencyListsGraphRepresentation {
    incoming: FxHashMap<ChcVertex, Vec<EdgeId>>,
    outgoing: FxHashMap<ChcVertex, Vec<EdgeId>>,
}

impl AdjacencyListsGraphRepresentation {
    pub(crate) fn from_graph(graph: &ChcDirectedGraph) -> Self {
        let mut incoming = FxHashMap::default();
        let mut outgoing = FxHashMap::default();
        for vertex in graph.vertices() {
            incoming.insert(vertex, Vec::new());
            outgoing.insert(vertex, Vec::new());
        }
        for edge in graph.edges() {
            incoming.entry(edge.target).or_default().push(edge.id);
            outgoing.entry(edge.source).or_default().push(edge.id);
            incoming.entry(edge.source).or_default();
            outgoing.entry(edge.target).or_default();
        }
        for edges in incoming.values_mut() {
            edges.sort_unstable();
        }
        for edges in outgoing.values_mut() {
            edges.sort_unstable();
        }
        Self { incoming, outgoing }
    }

    pub(crate) fn incoming_edges_for(&self, vertex: ChcVertex) -> &[EdgeId] {
        self.incoming.get(&vertex).map(Vec::as_slice).unwrap_or(&[])
    }

    pub(crate) fn outgoing_edges_for(&self, vertex: ChcVertex) -> &[EdgeId] {
        self.outgoing.get(&vertex).map(Vec::as_slice).unwrap_or(&[])
    }
}

#[derive(Debug, Clone)]
pub(crate) struct ChcDirectedGraph {
    predicates: Vec<Predicate>,
    edges: BTreeMap<EdgeId, DirectedEdge>,
    next_edge_id: usize,
    fixedpoint_format: bool,
    datatype_defs: FxHashMap<String, Vec<(String, Vec<(String, ChcSort)>)>>,
    action_names: Vec<String>,
}

impl ChcDirectedGraph {
    pub(crate) fn try_from_problem(problem: &ChcProblem) -> Result<Self, ChcGraphError> {
        let mut graph = Self {
            predicates: problem.predicates().to_vec(),
            edges: BTreeMap::new(),
            next_edge_id: 0,
            fixedpoint_format: problem.is_fixedpoint_format(),
            datatype_defs: problem.datatype_defs().clone(),
            action_names: problem.action_names().to_vec(),
        };

        for (clause_index, clause) in problem.clauses().iter().enumerate() {
            if clause.body.predicates.len() > 1 {
                return Err(ChcGraphError::NonLinearClause {
                    clause_index,
                    predicate_count: clause.body.predicates.len(),
                });
            }

            let (source, source_args) = match clause.body.predicates.as_slice() {
                [] => (ENTRY_VERTEX, Vec::new()),
                [(pred, args)] => {
                    graph.ensure_predicate(*pred)?;
                    (ChcVertex::Predicate(*pred), args.clone())
                }
                _ => unreachable!("non-linear clauses returned above"),
            };
            let (target, target_args) = match &clause.head {
                ClauseHead::Predicate(pred, args) => {
                    graph.ensure_predicate(*pred)?;
                    (ChcVertex::Predicate(*pred), args.clone())
                }
                ClauseHead::False => (EXIT_VERTEX, Vec::new()),
            };

            graph.add_edge(
                source,
                target,
                source_args,
                target_args,
                clause.body.constraint.clone(),
                clause.action_id,
                vec![clause_index],
            )?;
        }

        Ok(graph)
    }

    pub(crate) fn vertices(&self) -> Vec<ChcVertex> {
        let mut vertices = Vec::with_capacity(self.predicates.len() + 2);
        vertices.push(ENTRY_VERTEX);
        for pred in &self.predicates {
            vertices.push(ChcVertex::Predicate(pred.id));
        }
        vertices.push(EXIT_VERTEX);
        vertices
    }

    pub(crate) fn predicate(&self, pred: PredicateId) -> Option<&Predicate> {
        self.predicates.get(pred.index())
    }

    pub(crate) fn edges(&self) -> Vec<&DirectedEdge> {
        self.edges.values().collect()
    }

    pub(crate) fn edge(&self, id: EdgeId) -> Option<&DirectedEdge> {
        self.edges.get(&id)
    }

    pub(crate) fn adjacency_lists(&self) -> AdjacencyListsGraphRepresentation {
        AdjacencyListsGraphRepresentation::from_graph(self)
    }

    pub(crate) fn add_edge(
        &mut self,
        source: ChcVertex,
        target: ChcVertex,
        source_args: Vec<ChcExpr>,
        target_args: Vec<ChcExpr>,
        constraint: Option<ChcExpr>,
        action_id: Option<ActionId>,
        origin_clause_indices: Vec<usize>,
    ) -> Result<EdgeId, ChcGraphError> {
        self.ensure_vertex(source)?;
        self.ensure_vertex(target)?;
        let id = EdgeId(self.next_edge_id);
        self.next_edge_id += 1;
        self.edges.insert(
            id,
            DirectedEdge {
                id,
                source,
                target,
                source_args,
                target_args,
                constraint: normalize_constraint(constraint),
                action_id,
                origin_clause_indices,
            },
        );
        Ok(id)
    }

    pub(crate) fn detect_sccs(&self) -> Vec<Vec<ChcVertex>> {
        let vertices = self.vertices();
        let mut index_by_vertex = FxHashMap::default();
        for (index, vertex) in vertices.iter().enumerate() {
            index_by_vertex.insert(*vertex, index);
        }
        let adjacency = self.adjacency_lists();
        tarjan_scc_dense(vertices.len(), |index| {
            adjacency
                .outgoing_edges_for(vertices[index])
                .iter()
                .filter_map(|edge_id| self.edge(*edge_id))
                .filter_map(|edge| index_by_vertex.get(&edge.target()).copied())
                .collect()
        })
        .into_iter()
        .map(|component| component.into_iter().map(|index| vertices[index]).collect())
        .collect()
    }

    pub(crate) fn loop_vertices(&self) -> Vec<ChcVertex> {
        let mut loops = Vec::new();
        for component in self.detect_sccs() {
            if component.len() > 1 {
                loops.extend(component);
            } else if let Some(vertex) = component.first().copied() {
                if self.has_self_loop(vertex) {
                    loops.push(vertex);
                }
            }
        }
        loops.sort_unstable();
        loops.dedup();
        loops
    }

    pub(crate) fn detect_loop(&self) -> Option<Vec<ChcVertex>> {
        self.detect_sccs().into_iter().find(|component| {
            component.len() > 1
                || component
                    .first()
                    .is_some_and(|vertex| self.has_self_loop(*vertex))
        })
    }

    pub(crate) fn has_self_loop(&self, vertex: ChcVertex) -> bool {
        self.edges
            .values()
            .any(|edge| edge.source == vertex && edge.target == vertex)
    }

    pub(crate) fn merge_parallel_edges(&mut self) -> Vec<MergedEdge> {
        let mut buckets: FxHashMap<ParallelEdgeKey, Vec<EdgeId>> = FxHashMap::default();
        for edge in self.edges.values() {
            buckets
                .entry(ParallelEdgeKey::from(edge))
                .or_default()
                .push(edge.id);
        }

        let mut merged = Vec::new();
        for mut bucket in buckets.into_values() {
            if bucket.len() < 2 {
                continue;
            }
            bucket.sort_unstable();
            let retained = bucket[0];
            let removed = bucket[1..].to_vec();
            let mut labels = Vec::with_capacity(bucket.len());
            let mut origins = Vec::new();
            for edge_id in &bucket {
                let edge = self
                    .edges
                    .get(edge_id)
                    .expect("bucket edge id must be present before merge");
                labels.push(edge.label());
                origins.extend(edge.origin_clause_indices.iter().copied());
            }
            origins.sort_unstable();
            origins.dedup();
            let merged_constraint = expr_to_constraint(ChcExpr::or_all(labels));
            let retained_edge = self
                .edges
                .get_mut(&retained)
                .expect("retained edge id must be present before merge");
            retained_edge.constraint = merged_constraint;
            retained_edge.origin_clause_indices = origins.clone();
            for edge_id in &removed {
                self.edges.remove(edge_id);
            }
            merged.push(MergedEdge {
                retained,
                removed,
                origin_clause_indices: origins,
            });
        }
        merged.sort_unstable_by_key(|entry| entry.retained);
        merged
    }

    pub(crate) fn contract_connected_vertices(
        &mut self,
        vertices: &[ChcVertex],
    ) -> Result<WitnessInfo, ChcGraphError> {
        if vertices.len() < 2 {
            return Err(ChcGraphError::ContractionTooSmall);
        }
        let mut seen_input = FxHashSet::default();
        for vertex in vertices {
            if !seen_input.insert(*vertex) {
                return Err(ChcGraphError::DuplicateContractionVertex(*vertex));
            }
        }
        let mut vertices = vertices.to_vec();
        vertices.sort_unstable();
        for vertex in &vertices {
            match vertex {
                ChcVertex::Predicate(pred) => self.ensure_predicate(*pred)?,
                ChcVertex::Entry | ChcVertex::Exit => {
                    return Err(ChcGraphError::SpecialContractionVertex(*vertex));
                }
            }
        }
        if !self.is_connected_subset(&vertices) {
            return Err(ChcGraphError::DisconnectedContraction);
        }

        let witness = self.make_contraction_witness(&vertices);
        let contracted = witness.contracted_vertex;
        let contracting: FxHashSet<ChcVertex> = vertices.iter().copied().collect();
        let old_edges: Vec<DirectedEdge> = self.edges.values().cloned().collect();
        self.edges.clear();
        self.next_edge_id = 0;

        let mut internal_constraints = Vec::new();
        let mut internal_origins = Vec::new();
        for edge in old_edges {
            let source_in = contracting.contains(&edge.source);
            let target_in = contracting.contains(&edge.target);
            if source_in || target_in {
                let mut translated =
                    translate_contracted_edge(edge, &witness, &contracting, contracted);
                if source_in && target_in {
                    internal_constraints.push(translated.label());
                    internal_origins.extend(translated.origin_clause_indices.iter().copied());
                } else {
                    translated.id = EdgeId(self.next_edge_id);
                    self.next_edge_id += 1;
                    self.edges.insert(translated.id, translated);
                }
            } else {
                let mut retained = edge;
                retained.id = EdgeId(self.next_edge_id);
                self.next_edge_id += 1;
                self.edges.insert(retained.id, retained);
            }
        }

        if !internal_constraints.is_empty() {
            internal_origins.sort_unstable();
            internal_origins.dedup();
            self.add_edge(
                contracted,
                contracted,
                witness.predicate_arg_exprs(),
                witness.next_predicate_arg_exprs(),
                expr_to_constraint(ChcExpr::or_all(internal_constraints)),
                None,
                internal_origins,
            )?;
        }

        Ok(witness)
    }

    pub(crate) fn to_problem(&self) -> ChcProblem {
        self.to_problem_with_clause_origins().0
    }

    pub(crate) fn to_problem_with_clause_origins(&self) -> (ChcProblem, Vec<Vec<usize>>) {
        let mut problem = ChcProblem::new();
        if self.fixedpoint_format {
            problem.set_fixedpoint_format();
        }

        let mut datatype_defs: Vec<_> = self.datatype_defs.iter().collect();
        datatype_defs.sort_unstable_by_key(|(name, _)| name.as_str());
        for (name, constructors) in datatype_defs {
            problem.add_datatype_def(name.clone(), constructors.clone());
        }
        for action_name in &self.action_names {
            problem.declare_action(action_name.clone());
        }
        for pred in &self.predicates {
            let declared = problem.declare_predicate(&pred.name, pred.arg_sorts.clone());
            debug_assert_eq!(declared, pred.id);
        }

        let mut origins_by_clause = Vec::new();
        for edge in self.edges.values() {
            let body_predicates = match edge.source {
                ChcVertex::Entry => Vec::new(),
                ChcVertex::Predicate(pred) => vec![(pred, edge.source_args.clone())],
                ChcVertex::Exit => Vec::new(),
            };
            let head = match edge.target {
                ChcVertex::Predicate(pred) => ClauseHead::Predicate(pred, edge.target_args.clone()),
                ChcVertex::Exit | ChcVertex::Entry => ClauseHead::False,
            };
            let mut clause = HornClause::new(
                ClauseBody::new(body_predicates, edge.constraint.clone()),
                head,
            );
            if let Some(action_id) = edge.action_id {
                clause = clause.with_action(action_id);
            }
            problem.add_clause(clause);
            origins_by_clause.push(edge.origin_clause_indices.clone());
        }
        (problem, origins_by_clause)
    }

    fn ensure_vertex(&self, vertex: ChcVertex) -> Result<(), ChcGraphError> {
        if let ChcVertex::Predicate(pred) = vertex {
            self.ensure_predicate(pred)?;
        }
        Ok(())
    }

    fn ensure_predicate(&self, pred: PredicateId) -> Result<(), ChcGraphError> {
        if pred.index() < self.predicates.len() {
            Ok(())
        } else {
            Err(ChcGraphError::UnknownPredicate(pred))
        }
    }

    fn make_contraction_witness(&mut self, vertices: &[ChcVertex]) -> WitnessInfo {
        let new_pred = PredicateId::new(self.predicates.len() as u32);
        let contracted_vertex = ChcVertex::Predicate(new_pred);
        let mut arg_sorts = Vec::new();
        let mut locations = Vec::new();
        let mut positions = Vec::new();

        for vertex in vertices {
            arg_sorts.push(ChcSort::Bool);
            let arg_index = arg_sorts.len() - 1;
            locations.push(LocationWitness {
                vertex: *vertex,
                variable: ChcVar::new(location_var_name(*vertex), ChcSort::Bool),
                predicate_arg_index: arg_index,
            });
        }

        for vertex in vertices {
            let ChcVertex::Predicate(pred_id) = vertex else {
                unreachable!("validated above")
            };
            let pred = self
                .predicate(*pred_id)
                .expect("validated predicate must remain present");
            for (position, sort) in pred.arg_sorts.iter().enumerate() {
                arg_sorts.push(sort.clone());
                let arg_index = arg_sorts.len() - 1;
                positions.push(PositionWitness {
                    vertex: *vertex,
                    position,
                    variable: ChcVar::new(position_var_name(*vertex, position), sort.clone()),
                    predicate_arg_index: arg_index,
                });
            }
        }

        self.predicates.push(Predicate::new(
            new_pred,
            format!("__chc_contract_{}", new_pred.index()),
            arg_sorts,
        ));

        WitnessInfo {
            contracted_vertex,
            original_vertices: vertices.to_vec(),
            locations,
            positions,
        }
    }

    fn is_connected_subset(&self, vertices: &[ChcVertex]) -> bool {
        let selected: FxHashSet<ChcVertex> = vertices.iter().copied().collect();
        let adjacency = self.adjacency_lists();
        let mut seen = FxHashSet::default();
        let mut stack = vec![vertices[0]];
        while let Some(vertex) = stack.pop() {
            if !seen.insert(vertex) {
                continue;
            }
            for edge_id in adjacency.outgoing_edges_for(vertex) {
                let target = self
                    .edge(*edge_id)
                    .expect("adjacency edge id must be present")
                    .target;
                if selected.contains(&target) {
                    stack.push(target);
                }
            }
            for edge_id in adjacency.incoming_edges_for(vertex) {
                let source = self
                    .edge(*edge_id)
                    .expect("adjacency edge id must be present")
                    .source;
                if selected.contains(&source) {
                    stack.push(source);
                }
            }
        }
        seen.len() == selected.len()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ParallelEdgeKey {
    source: ChcVertex,
    target: ChcVertex,
    source_args: Vec<ChcExpr>,
    target_args: Vec<ChcExpr>,
    action_id: Option<ActionId>,
}

impl From<&DirectedEdge> for ParallelEdgeKey {
    fn from(edge: &DirectedEdge) -> Self {
        Self {
            source: edge.source,
            target: edge.target,
            source_args: edge.source_args.clone(),
            target_args: edge.target_args.clone(),
            action_id: edge.action_id,
        }
    }
}

fn translate_contracted_edge(
    edge: DirectedEdge,
    witness: &WitnessInfo,
    contracting: &FxHashSet<ChcVertex>,
    contracted: ChcVertex,
) -> DirectedEdge {
    let source_in = contracting.contains(&edge.source);
    let target_in = contracting.contains(&edge.target);
    let mut constraints = Vec::new();
    if let Some(constraint) = edge.constraint {
        constraints.push(constraint);
    }

    let source_args = if source_in {
        constraints.extend(location_state_constraints(edge.source, witness, false));
        constraints.extend(argument_equalities(
            edge.source,
            &edge.source_args,
            witness,
            false,
        ));
        witness.predicate_arg_exprs()
    } else {
        edge.source_args
    };

    let target_args = if target_in {
        constraints.extend(location_state_constraints(edge.target, witness, true));
        constraints.extend(argument_equalities(
            edge.target,
            &edge.target_args,
            witness,
            true,
        ));
        witness.next_predicate_arg_exprs()
    } else {
        edge.target_args
    };

    DirectedEdge {
        id: edge.id,
        source: if source_in { contracted } else { edge.source },
        target: if target_in { contracted } else { edge.target },
        source_args,
        target_args,
        constraint: expr_to_constraint(ChcExpr::and_all(constraints)),
        action_id: edge.action_id,
        origin_clause_indices: edge.origin_clause_indices,
    }
}

fn location_state_constraints(
    vertex: ChcVertex,
    witness: &WitnessInfo,
    next: bool,
) -> Vec<ChcExpr> {
    witness
        .locations
        .iter()
        .map(|loc| {
            let var = witness.location_var(loc.vertex, next);
            if loc.vertex == vertex {
                ChcExpr::var(var)
            } else {
                ChcExpr::not(ChcExpr::var(var))
            }
        })
        .collect()
}

fn argument_equalities(
    vertex: ChcVertex,
    args: &[ChcExpr],
    witness: &WitnessInfo,
    next: bool,
) -> Vec<ChcExpr> {
    args.iter()
        .enumerate()
        .map(|(position, arg)| {
            ChcExpr::eq(
                ChcExpr::var(witness.position_var(vertex, position, next)),
                arg.clone(),
            )
        })
        .collect()
}

fn normalize_constraint(constraint: Option<ChcExpr>) -> Option<ChcExpr> {
    constraint.and_then(expr_to_constraint)
}

fn expr_to_constraint(expr: ChcExpr) -> Option<ChcExpr> {
    match expr {
        ChcExpr::Bool(true) => None,
        other => Some(other),
    }
}

fn next_var(var: &ChcVar) -> ChcVar {
    ChcVar::new(format!("{}__next", var.name), var.sort.clone())
}

fn location_var_name(vertex: ChcVertex) -> String {
    match vertex {
        ChcVertex::Predicate(pred) => format!("__chc_loc_p{}", pred.index()),
        ChcVertex::Entry => "__chc_loc_entry".to_string(),
        ChcVertex::Exit => "__chc_loc_exit".to_string(),
    }
}

fn position_var_name(vertex: ChcVertex, position: usize) -> String {
    match vertex {
        ChcVertex::Predicate(pred) => format!("__chc_arg_p{}_{}", pred.index(), position),
        ChcVertex::Entry => format!("__chc_arg_entry_{position}"),
        ChcVertex::Exit => format!("__chc_arg_exit_{position}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ChcOp, ChcSort};

    fn int_var(name: &str) -> ChcExpr {
        ChcExpr::var(ChcVar::new(name, ChcSort::Int))
    }

    fn simple_problem() -> (ChcProblem, PredicateId, PredicateId) {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Int]);
        let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(int_var("x"), ChcExpr::int(0))),
            ClauseHead::Predicate(p, vec![int_var("x")]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(p, vec![int_var("x")])],
                Some(ChcExpr::lt(int_var("x"), ChcExpr::int(10))),
            ),
            ClauseHead::Predicate(q, vec![ChcExpr::add(int_var("x"), ChcExpr::int(1))]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(q, vec![int_var("z")])],
                Some(ChcExpr::gt(int_var("z"), ChcExpr::int(20))),
            ),
            ClauseHead::False,
        ));
        (problem, p, q)
    }

    #[test]
    fn graph_construction_tracks_entry_exit_and_adjacency() {
        let (problem, p, q) = simple_problem();
        let graph = ChcDirectedGraph::try_from_problem(&problem).unwrap();
        assert_eq!(
            graph.vertices(),
            vec![
                ENTRY_VERTEX,
                ChcVertex::Predicate(p),
                ChcVertex::Predicate(q),
                EXIT_VERTEX
            ]
        );

        let adjacency = graph.adjacency_lists();
        let entry_out = adjacency.outgoing_edges_for(ENTRY_VERTEX);
        assert_eq!(entry_out.len(), 1);
        assert_eq!(
            graph.edge(entry_out[0]).unwrap().target(),
            ChcVertex::Predicate(p)
        );

        let q_out = adjacency.outgoing_edges_for(ChcVertex::Predicate(q));
        assert_eq!(q_out.len(), 1);
        assert_eq!(graph.edge(q_out[0]).unwrap().target(), EXIT_VERTEX);
    }

    #[test]
    fn graph_roundtrips_linear_problem() {
        let (problem, _, _) = simple_problem();
        let graph = ChcDirectedGraph::try_from_problem(&problem).unwrap();
        let roundtrip = graph.to_problem();
        assert_eq!(roundtrip.predicates().len(), problem.predicates().len());
        assert_eq!(roundtrip.clauses().len(), problem.clauses().len());
        assert!(matches!(
            roundtrip.clauses()[0].head,
            ClauseHead::Predicate(_, _)
        ));
        assert!(roundtrip.clauses()[2].head.is_query());
    }

    #[test]
    fn graph_rejects_non_linear_clause() {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![]);
        let q = problem.declare_predicate("Q", vec![]);
        let r = problem.declare_predicate("R", vec![]);
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(p, vec![]), (q, vec![])]),
            ClauseHead::Predicate(r, vec![]),
        ));

        assert_eq!(
            ChcDirectedGraph::try_from_problem(&problem).unwrap_err(),
            ChcGraphError::NonLinearClause {
                clause_index: 0,
                predicate_count: 2,
            }
        );
    }

    #[test]
    fn loop_detection_finds_sccs_and_self_loops() {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![]);
        let q = problem.declare_predicate("Q", vec![]);
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(p, vec![])]),
            ClauseHead::Predicate(q, vec![]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(q, vec![])]),
            ClauseHead::Predicate(p, vec![]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(p, vec![])]),
            ClauseHead::Predicate(p, vec![]),
        ));

        let graph = ChcDirectedGraph::try_from_problem(&problem).unwrap();
        let loops = graph.loop_vertices();
        assert!(loops.contains(&ChcVertex::Predicate(p)));
        assert!(loops.contains(&ChcVertex::Predicate(q)));
        assert!(graph.detect_loop().is_some());
    }

    #[test]
    fn merge_parallel_edges_ors_constraints_and_tracks_origins() {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Int]);
        let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
        for value in [0, 1] {
            problem.add_clause(HornClause::new(
                ClauseBody::new(
                    vec![(p, vec![int_var("x")])],
                    Some(ChcExpr::eq(int_var("x"), ChcExpr::int(value))),
                ),
                ClauseHead::Predicate(q, vec![int_var("x")]),
            ));
        }

        let mut graph = ChcDirectedGraph::try_from_problem(&problem).unwrap();
        let merged = graph.merge_parallel_edges();
        assert_eq!(merged.len(), 1);
        assert_eq!(merged[0].origin_clause_indices, vec![0, 1]);
        assert_eq!(graph.edges().len(), 1);
        let edge = graph.edges()[0];
        assert_eq!(edge.origin_clause_indices(), &[0, 1]);
        assert!(matches!(
            edge.constraint(),
            Some(ChcExpr::Op(ChcOp::Or, args)) if args.len() == 2
        ));
    }

    #[test]
    fn contraction_adds_location_and_position_witnesses() {
        let (problem, p, q) = simple_problem();
        let mut graph = ChcDirectedGraph::try_from_problem(&problem).unwrap();
        graph
            .add_edge(
                ChcVertex::Predicate(q),
                ChcVertex::Predicate(p),
                vec![int_var("z")],
                vec![int_var("z")],
                Some(ChcExpr::Bool(true)),
                None,
                vec![3],
            )
            .unwrap();

        let witness = graph
            .contract_connected_vertices(&[ChcVertex::Predicate(p), ChcVertex::Predicate(q)])
            .unwrap();
        assert_eq!(witness.original_vertices.len(), 2);
        assert_eq!(witness.locations.len(), 2);
        assert_eq!(witness.positions.len(), 2);
        assert!(graph.has_self_loop(witness.contracted_vertex));
        let ChcVertex::Predicate(contracted_pred) = witness.contracted_vertex else {
            panic!("contracted vertex must be a predicate")
        };
        let pred = graph.predicate(contracted_pred).unwrap();
        assert_eq!(
            pred.arg_sorts,
            vec![ChcSort::Bool, ChcSort::Bool, ChcSort::Int, ChcSort::Int]
        );
    }

    #[test]
    fn contraction_rewrites_problem_with_contract_predicate() {
        let (problem, p, q) = simple_problem();
        let mut graph = ChcDirectedGraph::try_from_problem(&problem).unwrap();
        let witness = graph
            .contract_connected_vertices(&[ChcVertex::Predicate(p), ChcVertex::Predicate(q)])
            .unwrap();
        let transformed = graph.to_problem();
        let ChcVertex::Predicate(contracted_pred) = witness.contracted_vertex else {
            panic!("contracted vertex must be a predicate")
        };
        assert!(transformed.get_predicate(contracted_pred).is_some());
        assert!(transformed.clauses().iter().any(|clause| {
            matches!(
                &clause.head,
                ClauseHead::Predicate(pred, _) if *pred == contracted_pred
            )
        }));
    }

    #[test]
    fn contraction_internal_self_loop_has_disjunctive_label() {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![]);
        let q = problem.declare_predicate("Q", vec![]);
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(p, vec![])], Some(ChcExpr::Bool(true))),
            ClauseHead::Predicate(q, vec![]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(q, vec![])], Some(ChcExpr::Bool(true))),
            ClauseHead::Predicate(p, vec![]),
        ));
        let mut graph = ChcDirectedGraph::try_from_problem(&problem).unwrap();
        let witness = graph
            .contract_connected_vertices(&[ChcVertex::Predicate(p), ChcVertex::Predicate(q)])
            .unwrap();
        let self_loop = graph
            .edges()
            .into_iter()
            .find(|edge| {
                edge.source() == witness.contracted_vertex
                    && edge.target() == witness.contracted_vertex
            })
            .unwrap();
        assert!(matches!(
            self_loop.constraint(),
            Some(ChcExpr::Op(ChcOp::Or, args)) if args.len() == 2
        ));
        assert!(self_loop
            .target_args()
            .iter()
            .any(|arg| matches!(arg, ChcExpr::Var(v) if v.name.ends_with("__next"))));
    }

    #[test]
    fn to_problem_preserves_action_ids() {
        let mut problem = ChcProblem::new();
        let action = problem.declare_action("Step");
        let p = problem.declare_predicate("P", vec![]);
        problem.add_clause_with_action(
            HornClause::new(ClauseBody::empty(), ClauseHead::Predicate(p, vec![])),
            action,
        );
        let graph = ChcDirectedGraph::try_from_problem(&problem).unwrap();
        let roundtrip = graph.to_problem();
        assert_eq!(roundtrip.action_name(action), Some("Step"));
        assert_eq!(roundtrip.clauses()[0].action_id, Some(action));
    }

    #[test]
    fn edge_accessors_expose_args_and_ids() {
        let (problem, _, _) = simple_problem();
        let graph = ChcDirectedGraph::try_from_problem(&problem).unwrap();
        let edge = graph.edges()[1];
        assert_eq!(edge.id().index(), 1);
        assert_eq!(edge.source_args().len(), 1);
        assert_eq!(edge.target_args().len(), 1);
        assert_eq!(edge.action_id(), None);
        assert_eq!(edge.origin_clause_indices(), &[1]);
        assert!(matches!(edge.target_args()[0], ChcExpr::Op(ChcOp::Add, _)));
    }
}
