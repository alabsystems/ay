// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact product elimination for authenticated, nonrecursive single-ctor records.
//! This is a search representation, not a certificate or an approximate DT pass.

mod expression;
mod layout;
mod names;
#[cfg(test)]
mod tests;

use super::source_premises::SourceControl;
use crate::quantified::functions::controlled::{self, RetainedFunctions};
use crate::quantified::records::{registry_bytes, sort_bytes, Registry};
use crate::quantified::{QuantifiedChcProblem, QuantifiedHornClause, UniversalPremise};
use crate::{ChcExpr, ChcProblem, ChcSort, ClauseBody, ClauseHead, HornClause, PredicateId};
use expression::Context;
use layout::Layouts;
use std::sync::Arc;

#[derive(Debug)]
struct Signature {
    name: String,
    original: Vec<ChcSort>,
    projected: Vec<ChcSort>,
}

/// Immutable source identity and complete argument layout for original replay.
#[derive(Debug)]
pub(super) struct RecordProjection {
    source: Arc<str>,
    registry: Registry,
    functions: RetainedFunctions,
    layouts: Layouts,
    signatures: Vec<Signature>,
}

impl RecordProjection {
    pub(super) fn new(problem: &QuantifiedChcProblem, control: &SourceControl<'_>) -> Option<Self> {
        let source = problem.source_problem();
        control.poll()?;
        control.bytes(problem.source_smtlib().len())?;
        // Registry construction is bounded by the immutable source admission.
        // Precharge descriptor/name copies; its individual map operations are
        // opaque, not a claim of exact allocation or wall-clock accounting.
        control.bytes(registry_bytes(source)?)?;
        let registry = Registry::new(source).ok()?;
        let functions = controlled::retain(problem, control)?;
        control.poll()?;
        let layouts = Layouts::new(&registry, control)?;
        control.charge(source.predicates().len())?;
        let mut signatures = Vec::new();
        signatures
            .try_reserve_exact(source.predicates().len())
            .ok()?;
        for predicate in source.predicates() {
            control.bytes(predicate.name.len())?;
            if predicate.id.index() != signatures.len() {
                return None;
            }
            let mut original = Vec::new();
            let mut projected = Vec::new();
            control.charge(predicate.arg_sorts.len())?;
            original.try_reserve_exact(predicate.arg_sorts.len()).ok()?;
            for sort in &predicate.arg_sorts {
                registry.validate_sort(sort).ok()?;
                control.bytes(sort_bytes(sort)?)?;
                original.push(sort.clone());
                for field in layouts.leaves(sort)? {
                    control.charge(1)?;
                    control.bytes(sort_bytes(field)?)?;
                    projected.try_reserve(1).ok()?;
                    projected.push(field.clone());
                }
            }
            signatures.push(Signature {
                name: predicate.name.clone(),
                original,
                projected,
            });
        }
        let result = Self {
            source: Arc::from(problem.source_smtlib()),
            registry,
            functions,
            layouts,
            signatures,
        };
        control.poll()?;
        Some(result)
    }

    pub(super) fn matches_source(
        &self,
        problem: &QuantifiedChcProblem,
        control: &SourceControl<'_>,
    ) -> bool {
        if control.bytes(problem.source_smtlib().len()).is_none() {
            return false;
        }
        let same = self.source.as_ref() == problem.source_smtlib();
        same && control.poll().is_some()
    }

    pub(super) fn project(
        &self,
        problem: &QuantifiedChcProblem,
        control: &SourceControl<'_>,
    ) -> Option<QuantifiedChcProblem> {
        if !self.matches_source(problem, control) {
            return None;
        }
        let result = self.project_inner(problem, control)?;
        // Clause-local maps and borrowed traversal scratch are gone here.
        control.poll()?;
        Some(result)
    }

    fn project_inner(
        &self,
        problem: &QuantifiedChcProblem,
        control: &SourceControl<'_>,
    ) -> Option<QuantifiedChcProblem> {
        let source = problem.source_problem();
        if source.clauses().len() != problem.premises().len() {
            return None;
        }
        let reserved = names::reserved(problem, &self.registry, control)?;
        let mut declarations = ChcProblem::new();
        for (index, signature) in self.signatures.iter().enumerate() {
            control.bytes(signature.name.len())?;
            control.charge(signature.projected.len())?;
            for sort in &signature.projected {
                control.bytes(sort_bytes(sort)?)?;
            }
            if declarations
                .declare_predicate(&signature.name, signature.projected.clone())
                .index()
                != index
            {
                return None;
            }
        }
        if source.is_fixedpoint_format() {
            declarations.set_fixedpoint_format();
        }
        control.charge(source.clauses().len())?;
        let mut clauses = Vec::new();
        clauses.try_reserve_exact(source.clauses().len()).ok()?;
        for (clause, premises) in source.clauses().iter().zip(problem.premises()) {
            let mut context = Context::new(
                &self.registry,
                &self.functions,
                &self.layouts,
                &reserved,
                control,
            );
            let mut predicates = Vec::new();
            control.charge(clause.body.predicates.len())?;
            predicates
                .try_reserve_exact(clause.body.predicates.len())
                .ok()?;
            for (id, args) in &clause.body.predicates {
                predicates.push((*id, self.arguments(*id, args, &mut context)?));
            }
            let constraint = match &clause.body.constraint {
                Some(expr) => {
                    let value = context.rewrite(expr, 0)?.boolean(control)?;
                    Some(expression::copy_root(&value, control)?)
                }
                None => None,
            };
            let head = match &clause.head {
                ClauseHead::False => ClauseHead::False,
                ClauseHead::Predicate(id, args) => {
                    ClauseHead::Predicate(*id, self.arguments(*id, args, &mut context)?)
                }
            };
            control.charge(premises.len())?;
            let mut rewritten = Vec::new();
            rewritten.try_reserve_exact(premises.len()).ok()?;
            for premise in premises {
                rewritten.push(context.premise(premise)?);
            }
            // Reconstruct raw: the typed constructor assigns the same source
            // query ordinal by position. Never send registered ordinals back.
            let raw = HornClause::new(ClauseBody::new(predicates, constraint), head);
            clauses.push(QuantifiedHornClause::new(raw, rewritten));
        }
        control.poll()?;
        let functions = self.functions.declarations(control)?;
        let projected =
            QuantifiedChcProblem::new_with_functions(declarations, functions, clauses).ok()?;
        control.poll()?;
        Some(projected)
    }

    fn arguments(
        &self,
        predicate: PredicateId,
        args: &[ChcExpr],
        context: &mut Context<'_, '_>,
    ) -> Option<Vec<ChcExpr>> {
        let signature = self.signatures.get(predicate.index())?;
        if args.len() != signature.original.len() {
            return None;
        }
        context.control.charge(signature.projected.len())?;
        let mut out = Vec::new();
        out.try_reserve_exact(signature.projected.len()).ok()?;
        for (arg, expected) in args.iter().zip(&signature.original) {
            let value = context.rewrite(arg, 0)?;
            if value.sort() != expected {
                return None;
            }
            value.append(&mut out, context.control)?;
        }
        Some(out)
    }

    /// Re-express original actuals using authenticated selectors, not the
    /// search's fresh product variables. Caller binds these original terms.
    pub(super) fn project_arguments(
        &self,
        predicate: PredicateId,
        args: &[ChcExpr],
        control: &SourceControl<'_>,
    ) -> Option<Vec<ChcExpr>> {
        control.poll()?;
        let signature = self.signatures.get(predicate.index())?;
        if args.len() != signature.original.len() {
            return None;
        }
        control.charge(signature.projected.len())?;
        let mut out = Vec::new();
        out.try_reserve_exact(signature.projected.len()).ok()?;
        for (arg, expected) in args.iter().zip(&signature.original) {
            let actual =
                expression::authenticate(arg, &self.registry, &self.functions, control, 0)?;
            if &actual != expected {
                return None;
            }
            let source = expression::copy_root(arg, control)?;
            if matches!(expected, ChcSort::Datatype { .. }) {
                layout::original_leaves(Arc::new(source), expected, control, &mut out, 0)?;
            } else {
                out.push(source);
            }
        }
        control.poll()?;
        Some(out)
    }
}
