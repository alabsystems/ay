// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Positional formals must be fresh relative to the entire defining formula.

use super::{ChcExpr, ChcVar, ClauseHead, FxHashSet, HornClause, ValidityWitness};

pub(super) fn build(
    clause: &HornClause,
    head_vars: &[ChcVar],
    model: &ValidityWitness,
) -> (Vec<ChcVar>, Vec<ChcExpr>) {
    let mut seen = FxHashSet::default();
    if head_vars.iter().all(|var| seen.insert(var.name.as_str())) {
        return (head_vars.to_vec(), Vec::new());
    }
    seen.clear();
    let mut used = source_names(clause, model);
    used.extend(head_vars.iter().map(|var| var.name.clone()));
    let mut formals = Vec::with_capacity(head_vars.len());
    let mut equalities = Vec::new();
    for (index, var) in head_vars.iter().enumerate() {
        if seen.insert(var.name.as_str()) {
            formals.push(var.clone());
        } else {
            let fresh = ChcVar::new(
                reserve(format!("__dedup_a{index}_{}", var.name), &mut used),
                var.sort.clone(),
            );
            equalities.push(ChcExpr::eq(
                ChcExpr::var(fresh.clone()),
                ChcExpr::var(var.clone()),
            ));
            formals.push(fresh);
        }
    }
    (formals, equalities)
}

fn reserve(mut candidate: String, used: &mut FxHashSet<String>) -> String {
    // Deterministic and finite: each collision strictly lengthens the name,
    // while the reserved source set is finite. No counter can wrap around.
    while !used.insert(candidate.clone()) {
        candidate.push('_');
    }
    candidate
}

fn source_names(clause: &HornClause, model: &ValidityWitness) -> FxHashSet<String> {
    let mut census = NameCensus::default();
    if let ClauseHead::Predicate(_, args) = &clause.head {
        for arg in args {
            census.enqueue(arg);
        }
    }
    if let Some(constraint) = &clause.body.constraint {
        census.enqueue(constraint);
    }
    for (predicate, args) in &clause.body.predicates {
        for arg in args {
            census.enqueue(arg);
        }
        // Closed interpretations only introduce actual-argument names, but
        // an incomplete supplied interpretation must not accidentally have a
        // free local captured by a newly generated formal either.
        if let Some(interpretation) = model.get(predicate) {
            census.enqueue(&interpretation.formula);
        }
    }
    census.finish()
}

#[derive(Default)]
struct NameCensus<'a> {
    seen: FxHashSet<*const ChcExpr>,
    pending: Vec<&'a ChcExpr>,
}

impl<'a> NameCensus<'a> {
    fn enqueue(&mut self, expression: &'a ChcExpr) {
        // Identity is only a traversal deduplication key; the borrowed nodes
        // stay alive throughout the scan and the pointers are never dereferenced.
        if self.seen.insert(std::ptr::from_ref(expression)) {
            self.pending.push(expression);
        }
    }

    fn finish(mut self) -> FxHashSet<String> {
        let mut names = FxHashSet::default();
        // Do not use vars(): its legacy depth limit can silently miss a name.
        while let Some(expression) = self.pending.pop() {
            match expression {
                ChcExpr::ArrayLambda(lambda) => {
                    for formal in std::iter::once(lambda.binder()).chain(lambda.formals()) {
                        names.insert(formal.name.clone());
                    }
                    self.enqueue(lambda.body());
                    for value in lambda.captures() {
                        self.enqueue(value);
                    }
                }
                ChcExpr::Var(var) => {
                    names.insert(var.name.clone());
                }
                ChcExpr::Op(_, args) => {
                    for arg in args {
                        self.enqueue(arg);
                    }
                }
                ChcExpr::FuncApp(name, _, args) | ChcExpr::PredicateApp(name, _, args) => {
                    names.insert(name.clone());
                    for arg in args {
                        self.enqueue(arg);
                    }
                }
                ChcExpr::ConstArray(_, value) => self.enqueue(value),
                ChcExpr::IsTesterMarker(name) => {
                    names.insert(name.clone());
                }
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::BitVec(_, _)
                | ChcExpr::ConstArrayMarker(_) => {}
            }
        }
        names
    }
}

#[cfg(test)]
mod tests;
