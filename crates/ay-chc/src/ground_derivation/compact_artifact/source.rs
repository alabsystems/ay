// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Retain the existing identities without the legacy ground-value tree walk.
//! Price normalized text/copies before hashing. Constructor-list IDs are visited
//! once; ordinary expression occurrences retain their actual textual fanout.

use super::*;
use crate::proof_metadata::{
    normalized_chc_input_identity_with_progress, ordered_chc_clause_sequence_sha256_with_progress,
};
use crate::{ChcDtConstructors, ChcDtId, ChcExpr, ChcOp, ChcSort, ClauseHead};
use ay_core::kani_compat::DetHashSet;

pub(super) fn hashes(
    problem: &ChcProblem,
    owner: &mut Owner<'_>,
) -> Result<(&'static str, String, String)> {
    admit_identity(problem, owner)?;
    controlled(owner, |control| {
        let (schema, normalized) =
            normalized_chc_input_identity_with_progress(problem, &mut || control.poll().is_ok())
                .map_err(|_| interruption_error(super::super::GroundValidationInterrupted))?;
        let ordered = ordered_chc_clause_sequence_sha256_with_progress(problem, &mut || {
            control.poll().is_ok()
        })
        .map_err(|_| interruption_error(super::super::GroundValidationInterrupted))?;
        Ok((schema, normalized, ordered))
    })
}

pub(super) fn admit_identity(problem: &ChcProblem, owner: &mut Owner<'_>) -> Result<()> {
    compact::validate_source(problem, owner).map_err(native_error)?;
    let mut pricing = Pricing {
        owner,
        text: 0,
        seen: DetHashSet::default(),
        pending: Vec::new(),
    };
    declarations(problem, &mut pricing)?;
    clauses(problem, &mut pricing)?;
    while let Some(constructors) = pricing.pending.pop() {
        for constructor in constructors.iter() {
            pricing.name(&constructor.name, 2)?;
            for selector in &constructor.selectors {
                pricing.name(&selector.name, 2)?;
                pricing.sort(&selector.sort, 2)?;
            }
        }
    }
    let Some(work) = pricing.text.checked_mul(2) else {
        return refused(pricing.owner);
    };
    let Some(bytes) = pricing.text.checked_mul(4) else {
        return refused(pricing.owner);
    };
    // Final joins and both hashes consume the flat spelling, not every
    // ancestor's intermediate copy. Sorting is priced only at sorted vectors.
    admit(pricing.owner, work, bytes)
}

fn declarations<'a>(problem: &'a ChcProblem, pricing: &mut Pricing<'a, '_, '_>) -> Result<()> {
    let start = pricing.text;
    for predicate in problem.predicates() {
        pricing.name(&predicate.name, 2)?;
        for sort in &predicate.arg_sorts {
            pricing.sort(sort, 2)?;
        }
    }
    // Predicate signatures in both identities, plus normalized declarations.
    pricing.sorted(problem.predicates().len(), pricing.text - start, 3)?;
    let start = pricing.text;
    for action in problem.action_names() {
        pricing.name(action, 2)?;
    }
    pricing.sorted(problem.action_names().len(), pricing.text - start, 1)?;
    let datatype_rounds =
        usize::BITS as usize - problem.datatype_defs().len().leading_zeros() as usize + 1;
    for (name, constructors) in problem.datatype_defs() {
        pricing.name(name, datatype_rounds)?;
        for (constructor, selectors) in constructors {
            pricing.name(constructor, 2)?;
            for (selector, sort) in selectors {
                pricing.name(selector, 2)?;
                pricing.sort(sort, 2)?;
            }
        }
    }
    Ok(())
}

fn clauses<'a>(problem: &'a ChcProblem, pricing: &mut Pricing<'a, '_, '_>) -> Result<()> {
    let start = pricing.text;
    for clause in problem.clauses() {
        pricing.spelling(256, 2)?;
        if let Some(action) = clause.action_id.and_then(|id| problem.action_name(id)) {
            pricing.name(action, 2)?;
        }
        if let Some(expression) = &clause.body.constraint {
            pricing.expression(expression)?;
        }
        let body_start = pricing.text;
        for (_, arguments) in &clause.body.predicates {
            pricing.spelling(128, 2)?;
            for expression in arguments {
                pricing.expression(expression)?;
            }
        }
        pricing.sorted(clause.body.predicates.len(), pricing.text - body_start, 1)?;
        if let ClauseHead::Predicate(_, arguments) = &clause.head {
            for expression in arguments {
                pricing.expression(expression)?;
            }
        }
    }
    pricing.sorted(problem.clauses().len(), pricing.text - start, 1)
}

struct Pricing<'a, 'o, 'p> {
    owner: &'o mut Owner<'p>,
    text: usize,
    seen: DetHashSet<ChcDtId>,
    pending: Vec<&'a ChcDtConstructors>,
}

impl<'a> Pricing<'a, '_, '_> {
    fn charge(&mut self, amount: usize) -> Result<()> {
        let Some(bytes) = amount.checked_mul(8) else {
            return refused(self.owner);
        };
        admit(self.owner, amount, bytes)
    }

    fn spelling(&mut self, bytes: usize, weight: usize) -> Result<()> {
        let Some(text) = self.text.checked_add(bytes) else {
            return refused(self.owner);
        };
        let Some(work) = bytes.checked_mul(weight) else {
            return refused(self.owner);
        };
        self.charge(work)?;
        self.text = text;
        Ok(())
    }

    fn sorted(&mut self, items: usize, bytes: usize, copies: usize) -> Result<()> {
        let Some(work) = bytes
            .checked_mul(sort_rounds(items))
            .and_then(|n| n.checked_mul(copies))
        else {
            return refused(self.owner);
        };
        admit(self.owner, work, 0)
    }

    fn name(&mut self, name: &str, depth: usize) -> Result<()> {
        let Some(cost) = name.len().checked_mul(6).and_then(|n| n.checked_add(32)) else {
            return refused(self.owner);
        };
        self.spelling(cost, depth)
    }

    fn sort(&mut self, sort: &'a ChcSort, depth: usize) -> Result<()> {
        self.spelling(128, depth)?;
        match sort {
            ChcSort::Datatype { name, constructors } => {
                self.name(name, depth)?;
                // Admission precedes set/vector allocation; hash is fixed-size.
                if !self.seen.contains(&constructors.id()) {
                    self.charge(256)?;
                    if self.seen.try_reserve(1).is_err() || self.pending.try_reserve(1).is_err() {
                        return refused(self.owner);
                    }
                    self.seen.insert(constructors.id());
                    self.pending.push(constructors);
                }
            }
            ChcSort::Uninterpreted(name) => self.name(name, depth)?,
            ChcSort::Bool | ChcSort::BitVec(_) => {}
            _ => return Err(native_error(CompactError::Unsupported)),
        }
        Ok(())
    }

    fn expression(&mut self, root: &'a ChcExpr) -> Result<()> {
        self.charge(64)?;
        let mut pending = vec![(root, 1usize, 1usize, 0usize)];
        while let Some((expression, depth, copies, comparisons)) = pending.pop() {
            if depth > crate::ground_derivation::CHC_GROUND_DERIVATION_MAX_SOURCE_DEPTH {
                return refused(self.owner);
            }
            let Some(weight) = copies.checked_add(comparisons) else {
                return refused(self.owner);
            };
            self.spelling(64, weight)?;
            match expression {
                ChcExpr::Var(variable) => {
                    self.name(&variable.name, weight)?;
                    self.sort(&variable.sort, weight)?;
                }
                ChcExpr::FuncApp(name, sort, _) => {
                    self.name(name, weight)?;
                    self.sort(sort, weight)?;
                }
                ChcExpr::PredicateApp(name, _, _) | ChcExpr::IsTesterMarker(name) => {
                    self.name(name, weight)?
                }
                ChcExpr::ArrayLambda(_)
                | ChcExpr::ConstArray(..)
                | ChcExpr::ConstArrayMarker(..) => {
                    return Err(native_error(CompactError::Unsupported))
                }
                _ => {}
            }
            let children = crate::expr::dag::children(expression);
            let compared = matches!(expression, ChcExpr::Op(op, _) if commutative(*op));
            let Some(comparisons) = comparisons.checked_add(if compared {
                2 * sort_rounds(children.len())
            } else {
                0
            }) else {
                return refused(self.owner);
            };
            let Some(cost) = children.len().checked_mul(40) else {
                return refused(self.owner);
            };
            self.charge(cost)?;
            if pending.try_reserve(children.len()).is_err() {
                return refused(self.owner);
            }
            // Canonical spelling streams a contiguous unary function spine
            // into one buffer. Only its final tail is copied into that buffer;
            // an inner unary prefix no longer recopies every deeper suffix.
            // Structural depth still advances on EVERY edge for the source
            // bound, and all nodes/names/sorts/output remain charged above.
            let unary = matches!(expression, ChcExpr::FuncApp(_, _, args) if args.len() == 1);
            pending.extend(children.iter().map(|child| {
                let same_spine = unary
                    && matches!(child.as_ref(), ChcExpr::FuncApp(_, _, args) if args.len() == 1);
                (
                    child.as_ref(),
                    depth + 1,
                    copies + usize::from(!same_spine),
                    comparisons,
                )
            }));
        }
        Ok(())
    }
}

fn sort_rounds(items: usize) -> usize {
    if items < 2 {
        0
    } else {
        usize::BITS as usize - (items - 1).leading_zeros() as usize
    }
}

// Same supported commutative operations as normalization::payload. Each
// child's flat bytes are compared in both normalized and ordered identities.
fn commutative(op: ChcOp) -> bool {
    matches!(
        op,
        ChcOp::And
            | ChcOp::Or
            | ChcOp::Iff
            | ChcOp::Eq
            | ChcOp::Ne
            | ChcOp::BvAdd
            | ChcOp::BvMul
            | ChcOp::BvAnd
            | ChcOp::BvOr
            | ChcOp::BvXor
            | ChcOp::BvNand
            | ChcOp::BvNor
            | ChcOp::BvXnor
    )
}
