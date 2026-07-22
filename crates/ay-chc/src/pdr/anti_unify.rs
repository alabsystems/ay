// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Anti-unification utilities for Spacer-style lemma clustering.
//!
//! Port of Z3 Spacer `spacer_antiunify.cpp` with a Rust `ChcExpr` AST.
//! The core operation computes the most general generalization ("anti-unifier")
//! of two expressions by replacing mismatching subterms with fresh variables,
//! while recording the corresponding substitutions for each input.

use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use std::sync::Arc;

#[derive(Debug, Clone)]
pub(crate) struct AntiUnifyResult {
    pub(crate) pattern: ChcExpr,
    pub(crate) pattern_vars: Vec<ChcVar>,
    pub(crate) subst1: Vec<ChcExpr>,
    pub(crate) subst2: Vec<ChcExpr>,
}

impl AntiUnifyResult {
    pub(crate) fn is_numeric_int_substitution(&self) -> bool {
        debug_assert_eq!(self.pattern_vars.len(), self.subst1.len());
        debug_assert_eq!(self.pattern_vars.len(), self.subst2.len());
        self.subst1.iter().all(is_int_numeral) && self.subst2.iter().all(is_int_numeral)
    }
}

pub(crate) fn are_neighbours_int_only(e1: &ChcExpr, e2: &ChcExpr) -> bool {
    if e1 == e2 {
        return false;
    }
    anti_unify(e1, e2).is_numeric_int_substitution()
}

pub(crate) fn anti_unify(e1: &ChcExpr, e2: &ChcExpr) -> AntiUnifyResult {
    if e1 == e2 {
        return AntiUnifyResult {
            pattern: e1.clone(),
            pattern_vars: Vec::new(),
            subst1: Vec::new(),
            subst2: Vec::new(),
        };
    }

    let mut existing_names: FxHashSet<String> = FxHashSet::default();
    existing_names.extend(e1.vars().into_iter().map(|v| v.name));
    existing_names.extend(e2.vars().into_iter().map(|v| v.name));

    let mut unifier = AntiUnifier::new(existing_names);
    unifier.compute(e1, e2)
}

fn is_int_numeral(e: &ChcExpr) -> bool {
    matches!(e, ChcExpr::Int(_) | ChcExpr::BitVec(_, _))
}

struct AntiUnifier {
    existing_names: FxHashSet<String>,
    next_var_index: usize,
    pattern_vars: Vec<ChcVar>,
    subst1: Vec<ChcExpr>,
    subst2: Vec<ChcExpr>,
    cache: FxHashMap<(ChcExpr, ChcExpr), ChcExpr>,
    todo: Vec<(ChcExpr, ChcExpr)>,
}

impl AntiUnifier {
    fn new(existing_names: FxHashSet<String>) -> Self {
        Self {
            existing_names,
            next_var_index: 0,
            pattern_vars: Vec::new(),
            subst1: Vec::new(),
            subst2: Vec::new(),
            cache: FxHashMap::default(),
            todo: Vec::new(),
        }
    }

    fn compute(&mut self, e1: &ChcExpr, e2: &ChcExpr) -> AntiUnifyResult {
        self.todo.push((e1.clone(), e2.clone()));

        while let Some((a, b)) = self.todo.last().cloned() {
            let key = (a.clone(), b.clone());

            if self.cache.contains_key(&key) {
                self.todo.pop();
                continue;
            }

            if a == b {
                self.cache.insert(key, a.clone());
                self.todo.pop();
                continue;
            }

            if !same_head(&a, &b) {
                let abstracted = self.abstract_mismatch(&a, &b);
                self.cache.insert(key, abstracted);
                self.todo.pop();
                continue;
            }

            let Some((kind, kids_a, kids_b)) = split_children(&a, &b) else {
                // same_head() said they match, so reaching here means a leaf that differs.
                let abstracted = self.abstract_mismatch(&a, &b);
                self.cache.insert(key, abstracted);
                self.todo.pop();
                continue;
            };

            let mut unified_kids: Vec<ChcExpr> = Vec::with_capacity(kids_a.len());
            let mut pushed = false;

            for (ka, kb) in kids_a.iter().zip(kids_b.iter()) {
                if ka == kb {
                    unified_kids.push(ka.clone());
                    continue;
                }
                let child_key = (ka.clone(), kb.clone());
                if let Some(u) = self.cache.get(&child_key) {
                    unified_kids.push(u.clone());
                    continue;
                }
                self.todo.push((ka.clone(), kb.clone()));
                pushed = true;
            }

            if pushed {
                continue;
            }

            let unified = rebuild(kind, &a, unified_kids);
            self.cache.insert(key, unified);
            self.todo.pop();
        }

        let root_key = (e1.clone(), e2.clone());
        let pattern = self
            .cache
            .get(&root_key)
            .cloned()
            .unwrap_or_else(|| e1.clone());

        AntiUnifyResult {
            pattern,
            pattern_vars: std::mem::take(&mut self.pattern_vars),
            subst1: std::mem::take(&mut self.subst1),
            subst2: std::mem::take(&mut self.subst2),
        }
    }

    fn abstract_mismatch(&mut self, left: &ChcExpr, right: &ChcExpr) -> ChcExpr {
        let v = self.fresh_var(left.sort());
        self.subst1.push(left.clone());
        self.subst2.push(right.clone());
        ChcExpr::Var(v)
    }

    fn fresh_var(&mut self, sort: ChcSort) -> ChcVar {
        loop {
            let name = format!("__au_k{}", self.next_var_index);
            self.next_var_index += 1;
            if self.existing_names.insert(name.clone()) {
                let v = ChcVar::new(name, sort);
                self.pattern_vars.push(v.clone());
                return v;
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum RebuildKind {
    Op,
    PredicateApp,
    FuncApp,
    ConstArray,
}

/// Check if expression is a numeric constant (Int, Real, or BV literal).
fn is_numeric_constant(e: &ChcExpr) -> bool {
    matches!(
        e,
        ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _)
    )
}

fn mul_has_numeric_constant(args: &[Arc<ChcExpr>]) -> bool {
    args.iter().any(|e| is_numeric_constant(e))
}

fn same_head(a: &ChcExpr, b: &ChcExpr) -> bool {
    match (a, b) {
        (ChcExpr::Bool(_), ChcExpr::Bool(_)) => true,
        (ChcExpr::Int(_), ChcExpr::Int(_)) => true,
        (ChcExpr::Real(_, _), ChcExpr::Real(_, _)) => true,
        // BV literals with the same width are structurally similar.
        (ChcExpr::BitVec(_, w1), ChcExpr::BitVec(_, w2)) => w1 == w2,
        (ChcExpr::Var(_), ChcExpr::Var(_)) => true,
        (ChcExpr::ConstArray(_, _), ChcExpr::ConstArray(_, _)) => true,
        (ChcExpr::Op(op_a, args_a), ChcExpr::Op(op_b, args_b)) => {
            if op_a != op_b || args_a.len() != args_b.len() {
                return false;
            }
            // Non-linear multiplication guard (matches Z3 spacer_antiunify.cpp:55-66):
            // each side must contain a numeric constant, otherwise descending can
            // create non-linear patterns (e.g., k0*k1).
            if *op_a == ChcOp::Mul {
                let has_const_a = mul_has_numeric_constant(args_a);
                let has_const_b = mul_has_numeric_constant(args_b);
                if !has_const_a || !has_const_b {
                    return false;
                }
            }
            true
        }
        (
            ChcExpr::PredicateApp(name_a, id_a, args_a),
            ChcExpr::PredicateApp(name_b, id_b, args_b),
        ) => name_a == name_b && id_a == id_b && args_a.len() == args_b.len(),
        (ChcExpr::FuncApp(name_a, sort_a, args_a), ChcExpr::FuncApp(name_b, sort_b, args_b)) => {
            name_a == name_b && sort_a == sort_b && args_a.len() == args_b.len()
        }
        _ => false,
    }
}

fn split_children(a: &ChcExpr, b: &ChcExpr) -> Option<(RebuildKind, Vec<ChcExpr>, Vec<ChcExpr>)> {
    match (a, b) {
        (ChcExpr::Op(_, args_a), ChcExpr::Op(_, args_b)) => Some((
            RebuildKind::Op,
            args_a.iter().map(|e| e.as_ref().clone()).collect(),
            args_b.iter().map(|e| e.as_ref().clone()).collect(),
        )),
        (ChcExpr::PredicateApp(_, _, args_a), ChcExpr::PredicateApp(_, _, args_b)) => Some((
            RebuildKind::PredicateApp,
            args_a.iter().map(|e| e.as_ref().clone()).collect(),
            args_b.iter().map(|e| e.as_ref().clone()).collect(),
        )),
        (ChcExpr::FuncApp(_, _, args_a), ChcExpr::FuncApp(_, _, args_b)) => Some((
            RebuildKind::FuncApp,
            args_a.iter().map(|e| e.as_ref().clone()).collect(),
            args_b.iter().map(|e| e.as_ref().clone()).collect(),
        )),
        (ChcExpr::ConstArray(_ks, elem_a), ChcExpr::ConstArray(_, elem_b)) => Some((
            RebuildKind::ConstArray,
            vec![elem_a.as_ref().clone()],
            vec![elem_b.as_ref().clone()],
        )),
        _ => None,
    }
}

fn rebuild(kind: RebuildKind, original: &ChcExpr, kids: Vec<ChcExpr>) -> ChcExpr {
    match kind {
        RebuildKind::Op => {
            let ChcExpr::Op(op, _) = original else {
                return original.clone();
            };
            ChcExpr::Op(*op, kids.into_iter().map(Arc::new).collect())
        }
        RebuildKind::PredicateApp => {
            let ChcExpr::PredicateApp(name, id, _) = original else {
                return original.clone();
            };
            ChcExpr::PredicateApp(name.clone(), *id, kids.into_iter().map(Arc::new).collect())
        }
        RebuildKind::FuncApp => {
            let ChcExpr::FuncApp(name, sort, _) = original else {
                return original.clone();
            };
            ChcExpr::FuncApp(
                name.clone(),
                sort.clone(),
                kids.into_iter().map(Arc::new).collect(),
            )
        }
        RebuildKind::ConstArray => {
            let ChcExpr::ConstArray(ks, original_elem) = original else {
                return original.clone();
            };

            let mut iter = kids.into_iter();
            match (iter.next(), iter.next()) {
                (Some(elem), None) => ChcExpr::ConstArray(ks.clone(), Arc::new(elem)),
                _ => {
                    // Production soundness gate: const-array rebuild should
                    // always have exactly one child. If not, fall back to the
                    // original element (sound but incomplete anti-unification).
                    safe_eprintln!(
                        "BUG: anti_unify rebuild_from: expected exactly one const-array child — using original element"
                    );
                    ChcExpr::ConstArray(ks.clone(), original_elem.clone())
                }
            }
        }
    }
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "anti_unify_tests.rs"]
mod tests;
