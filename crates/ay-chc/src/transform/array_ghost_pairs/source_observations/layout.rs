// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::quantified::records::{
    registry_bytes, sort_bytes, Registry, MAX_FLATTENED_LEAVES, MAX_RECORD_DEPTH,
};
use crate::{ChcExpr, ChcOp, ChcVar, PredicateId};
use ay_core::kani_compat::DetHashMap;
use std::sync::Arc;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Step {
    Axis(usize),
    Field(usize),
}

#[derive(Debug)]
pub(super) struct Observation {
    pub(super) argument: usize,
    pub(super) path: Vec<Step>,
    pub(super) sort: ChcSort,
}

#[derive(Debug)]
pub(super) struct Predicate {
    pub(super) original: Vec<ChcSort>,
    pub(super) axes: Vec<ChcSort>,
    pub(super) observations: Vec<Observation>,
    pub(super) canonical: Vec<ChcVar>,
}

#[derive(Debug)]
pub(in crate::transform::array_ghost_pairs) struct Layout {
    source: Arc<str>,
    pub(super) registry: Registry,
    predicates: Vec<Predicate>,
}

impl Layout {
    pub(in crate::transform::array_ghost_pairs) fn analyze(
        problem: &QuantifiedChcProblem,
        control: &SourceControl<'_>,
    ) -> Option<Self> {
        control.bytes(registry_bytes(problem.source_problem())?)?;
        let registry = Registry::new(problem.source_problem()).ok()?;
        let mut used = super::names::reserved(problem, &registry, control)?;
        let mut predicates = Vec::new();
        control.charge(problem.source_problem().predicates().len())?;
        for declaration in problem.source_problem().predicates() {
            if declaration.id.index() != predicates.len() {
                return None;
            }
            let mut predicate = Predicate {
                original: Vec::new(),
                axes: Vec::new(),
                observations: Vec::new(),
                canonical: Vec::new(),
            };
            for (argument, sort) in declaration.arg_sorts.iter().enumerate() {
                control.bytes(sort_bytes(sort)?)?;
                registry.validate_sort(sort).ok()?;
                predicate.original.push(sort.clone());
                if !scalar(sort) {
                    predicate.walk(argument, sort, &mut Vec::new(), 0, control)?;
                }
            }
            let sorts = predicate.extended(control)?;
            for (position, sort) in sorts.into_iter().enumerate() {
                let name = super::names::fresh(declaration.id, position, &mut used, control)?;
                predicate.canonical.push(ChcVar::new(name, sort));
            }
            predicates.push(predicate);
        }
        control.bytes(problem.source_smtlib().len())?;
        let result = Self {
            source: Arc::from(problem.source_smtlib()),
            registry,
            predicates,
        };
        control.poll()?;
        Some(result)
    }

    pub(in crate::transform::array_ghost_pairs) fn matches_source(
        &self,
        problem: &QuantifiedChcProblem,
        control: &SourceControl<'_>,
    ) -> bool {
        control.bytes(problem.source_smtlib().len()).is_some()
            && self.source.as_ref() == problem.source_smtlib()
            && control.poll().is_some()
    }

    pub(super) fn predicate(&self, id: PredicateId) -> Option<&Predicate> {
        self.predicates.get(id.index())
    }
    pub(in crate::transform::array_ghost_pairs) fn original_sorts(
        &self,
        id: PredicateId,
    ) -> Option<&[ChcSort]> {
        Some(&self.predicate(id)?.original)
    }
    pub(in crate::transform::array_ghost_pairs) fn axes(
        &self,
        id: PredicateId,
    ) -> Option<&[ChcSort]> {
        Some(&self.predicate(id)?.axes)
    }
    pub(in crate::transform::array_ghost_pairs) fn canonical(
        &self,
        id: PredicateId,
    ) -> Option<&[ChcVar]> {
        Some(&self.predicate(id)?.canonical)
    }
    pub(in crate::transform::array_ghost_pairs) fn extended_sorts(
        &self,
        id: PredicateId,
        control: &SourceControl<'_>,
    ) -> Option<Vec<ChcSort>> {
        self.predicate(id)?.extended(control)
    }

    pub(super) fn canonical_map(
        &self,
        control: &SourceControl<'_>,
    ) -> Option<DetHashMap<PredicateId, Vec<ChcVar>>> {
        let mut out = DetHashMap::default();
        for (index, predicate) in self.predicates.iter().enumerate() {
            control.charge(predicate.canonical.len())?;
            for var in &predicate.canonical {
                control.bytes(var.name.len().checked_add(sort_bytes(&var.sort)?)?)?;
            }
            out.insert(
                PredicateId::new(u32::try_from(index).ok()?),
                predicate.canonical.clone(),
            );
        }
        Some(out)
    }

    /// Caller supplies source-authenticated actual expressions. All root copies
    /// and generated selector/read paths are charged before construction.
    pub(in crate::transform::array_ghost_pairs) fn actuals(
        &self,
        id: PredicateId,
        original: &[ChcExpr],
        axes: &[ChcExpr],
        control: &SourceControl<'_>,
    ) -> Option<Vec<ChcExpr>> {
        let predicate = self.predicate(id)?;
        if original.len() != predicate.original.len() || axes.len() != predicate.axes.len() {
            return None;
        }
        let mut out = Vec::new();
        control.charge(predicate.canonical.len())?;
        out.try_reserve_exact(predicate.canonical.len()).ok()?;
        for (expr, sort) in original
            .iter()
            .zip(&predicate.original)
            .chain(axes.iter().zip(&predicate.axes))
        {
            source_premises::preflight(expr, control, &mut 0)?;
            if &expr.sort() != sort {
                return None;
            }
            out.push(expr.clone());
        }
        let mut roots = Vec::new();
        for expression in &out {
            source_premises::preflight(expression, control, &mut 0)?;
            roots.push(Arc::new(expression.clone()));
        }
        for observation in &predicate.observations {
            let mut current = Arc::clone(roots.get(observation.argument)?);
            let mut sort = predicate.original.get(observation.argument)?;
            for step in &observation.path {
                control.charge(3)?;
                current = Arc::new(match *step {
                    Step::Axis(axis) => {
                        let ChcSort::Array(key, value) = sort else {
                            return None;
                        };
                        if key.as_ref() != predicate.axes.get(axis)? {
                            return None;
                        }
                        sort = value;
                        ChcExpr::Op(
                            ChcOp::Select,
                            vec![
                                current,
                                Arc::clone(roots.get(original.len().checked_add(axis)?)?),
                            ],
                        )
                    }
                    Step::Field(field) => {
                        let ChcSort::Datatype { constructors, .. } = sort else {
                            return None;
                        };
                        let [constructor] = constructors.as_slice() else {
                            return None;
                        };
                        let selector = constructor.selectors.get(field)?;
                        control.bytes(
                            selector
                                .name
                                .len()
                                .checked_add(sort_bytes(&selector.sort)?)?,
                        )?;
                        sort = &selector.sort;
                        ChcExpr::FuncApp(
                            selector.name.clone(),
                            selector.sort.clone(),
                            vec![current],
                        )
                    }
                });
            }
            if sort != &observation.sort {
                return None;
            }
            out.push(current.as_ref().clone());
        }
        control.poll()?;
        Some(out)
    }
}

impl Predicate {
    fn walk(
        &mut self,
        argument: usize,
        sort: &ChcSort,
        path: &mut Vec<Step>,
        depth: usize,
        control: &SourceControl<'_>,
    ) -> Option<()> {
        control.charge(1)?;
        if depth > MAX_RECORD_DEPTH {
            return None;
        }
        match sort {
            ChcSort::Array(key, value)
                if matches!(
                    key.as_ref(),
                    ChcSort::BitVec(1..=crate::MAX_BITVECTOR_WIDTH)
                ) =>
            {
                if self.axes.len() >= crate::quantified::MAX_PREMISE_BINDERS {
                    return None;
                }
                let axis = self.axes.len();
                control.bytes(sort_bytes(key)?)?;
                self.axes.push(key.as_ref().clone());
                path.push(Step::Axis(axis));
                self.walk(argument, value, path, depth + 1, control)?;
                path.pop();
            }
            ChcSort::Datatype { constructors, .. } => {
                let [constructor] = constructors.as_slice() else {
                    return None;
                };
                for (field, selector) in constructor.selectors.iter().enumerate() {
                    path.push(Step::Field(field));
                    self.walk(argument, &selector.sort, path, depth + 1, control)?;
                    path.pop();
                }
            }
            sort if scalar(sort) => {
                if self.observations.len() >= MAX_FLATTENED_LEAVES {
                    return None;
                }
                control.charge(path.len().checked_add(1)?)?;
                control.bytes(sort_bytes(sort)?)?;
                self.observations.push(Observation {
                    argument,
                    path: path.clone(),
                    sort: sort.clone(),
                });
            }
            _ => return None,
        }
        Some(())
    }

    fn extended(&self, control: &SourceControl<'_>) -> Option<Vec<ChcSort>> {
        let mut out = Vec::new();
        for sort in self
            .original
            .iter()
            .chain(&self.axes)
            .chain(self.observations.iter().map(|obs| &obs.sort))
        {
            control.charge(1)?;
            control.bytes(sort_bytes(sort)?)?;
            out.push(sort.clone());
        }
        Some(out)
    }
}

pub(super) fn scalar(sort: &ChcSort) -> bool {
    matches!(
        sort,
        ChcSort::Bool | ChcSort::BitVec(1..=crate::MAX_BITVECTOR_WIDTH)
    )
}
