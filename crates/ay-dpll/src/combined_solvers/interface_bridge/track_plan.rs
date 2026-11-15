// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Interface-term tracking as a pure PLAN plus an APPLY step.
//!
//! The three per-literal tracking passes (`track_interface_term`,
//! `collect_int_constants`, `track_uf_arith_args`) each walk the literal's
//! term DAG and attempt insertions into the bridge's sets. The walks never
//! read those sets: a set only decides whether an attempted insertion is new.
//! So each pass splits exactly into
//!
//! - a plan: the ordered list of insertion attempts, a pure function of the
//!   immutable term DAG under the literal; and
//! - an apply: the same attempts, in the same order, against the live sets.
//!
//! Applying a plan performs the identical sequence of set operations and trail
//! pushes the interleaved walk performed, so the resulting sets, their
//! iteration order and the undo trail are identical too.
//!
//! The combined plan of a literal is memoised per lane: `track_plans` for the
//! LIA lane (`collect_int_constants`) and `real_track_plans` for the LRA lane
//! (`collect_real_constants`, #combiner-carry-other-lanes). A lazy split loop
//! re-asserts nearly the same literals into a fresh combiner every round;
//! carrying both memos between those combiners ([`InterfaceTrackPlans`])
//! removes the repeated walks, never a result.

use std::rc::Rc;

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData, TermStoreSnapshotStamp};
use ay_core::{TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;

use super::propagate::{CONST_COLLECT_STACK_RED_ZONE, CONST_COLLECT_STACK_SIZE};
use super::{is_arith_evaluable, InterfaceBridge, InterfaceTrailEntry, BUILTIN_OPS};

/// One insertion attempt of a tracking pass, in walk order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum TrackOp {
    /// Attempt to add an interface arithmetic term.
    Arith(TermId),
    /// Attempt to register `value -> term` unless `value` is already mapped.
    IntConst(BigInt, TermId),
    /// Attempt to register the rational `value -> term` unless `value` is
    /// already mapped (LRA lane).
    RealConst(BigRational, TermId),
}

/// Memoised combined tracking plans of a bridge (both lanes), detached so a
/// later bridge over the same append-only `TermStore` can reuse them.
///
/// The stamp ties the plans to the store they were computed from;
/// [`InterfaceBridge::import_track_plans`] drops them unless that store is
/// still an append-only prefix of the importer's, so a plan is never replayed
/// for a `TermId` that names a different term.
pub(in crate::combined_solvers) struct InterfaceTrackPlans {
    stamp: TermStoreSnapshotStamp,
    plans: HashMap<TermId, Rc<[TrackOp]>>,
    real_plans: HashMap<TermId, Rc<[TrackOp]>>,
}

impl InterfaceBridge {
    /// Track a literal asserted on the LIA lane: `track_interface_term`, then
    /// `collect_int_constants`, then `track_uf_arith_args`, through the memoised
    /// combined plan.
    pub(in crate::combined_solvers) fn track_int_literal(
        &mut self,
        terms: &TermStore,
        literal: TermId,
    ) {
        let plan = match self.track_plans.get(&literal) {
            Some(plan) => Rc::clone(plan),
            None => {
                let mut ops = Vec::new();
                plan_interface_term(terms, literal, &mut ops);
                plan_int_constants(terms, literal, &mut ops);
                plan_uf_arith_args(terms, literal, &mut ops);
                let plan: Rc<[TrackOp]> = ops.into();
                self.track_plans.insert(literal, Rc::clone(&plan));
                plan
            }
        };
        self.apply_track_ops(&plan);
    }

    /// Track a literal asserted on the LRA lane: `track_interface_term`, then
    /// `collect_real_constants`, then `track_uf_arith_args`, through the
    /// memoised combined plan.
    pub(in crate::combined_solvers) fn track_real_literal(
        &mut self,
        terms: &TermStore,
        literal: TermId,
    ) {
        let plan = match self.real_track_plans.get(&literal) {
            Some(plan) => Rc::clone(plan),
            None => {
                let mut ops = Vec::new();
                plan_interface_term(terms, literal, &mut ops);
                plan_real_constants(terms, literal, &mut ops);
                plan_uf_arith_args(terms, literal, &mut ops);
                let plan: Rc<[TrackOp]> = ops.into();
                self.real_track_plans.insert(literal, Rc::clone(&plan));
                plan
            }
        };
        self.apply_track_ops(&plan);
    }

    pub(super) fn apply_track_ops(&mut self, ops: &[TrackOp]) {
        for op in ops {
            match op {
                TrackOp::Arith(term) => {
                    if self.interface_arith_terms.insert(*term) {
                        self.interface_trail
                            .push(InterfaceTrailEntry::ArithTerm(*term));
                    }
                }
                TrackOp::IntConst(value, term) => {
                    if !self.int_const_terms.contains_key(value) {
                        self.int_const_terms.insert(value.clone(), *term);
                        self.interface_trail
                            .push(InterfaceTrailEntry::ConstTerm(value.clone()));
                    }
                }
                TrackOp::RealConst(value, term) => {
                    if !self.real_const_terms.contains_key(value) {
                        self.real_const_terms.insert(value.clone(), *term);
                        self.interface_trail
                            .push(InterfaceTrailEntry::RealConstTerm(value.clone()));
                    }
                }
            }
        }
    }

    /// Move the memoised plans out (`None` when there are none).
    pub(in crate::combined_solvers) fn export_track_plans(
        &mut self,
        terms: &TermStore,
    ) -> Option<InterfaceTrackPlans> {
        if self.track_plans.is_empty() && self.real_track_plans.is_empty() {
            return None;
        }
        Some(InterfaceTrackPlans {
            stamp: terms.snapshot_stamp(),
            plans: std::mem::take(&mut self.track_plans),
            real_plans: std::mem::take(&mut self.real_track_plans),
        })
    }

    /// Seed the plan memo from an earlier bridge's export; ignored unless the
    /// exporting store is an append-only prefix of `terms`.
    pub(in crate::combined_solvers) fn import_track_plans(
        &mut self,
        terms: &TermStore,
        carried: InterfaceTrackPlans,
    ) {
        if !carried.stamp.is_append_only_prefix_of(terms) {
            return;
        }
        merge_plans(&mut self.track_plans, carried.plans);
        merge_plans(&mut self.real_track_plans, carried.real_plans);
    }
}

/// Keep every plan the memo already holds; add the carried ones it lacks.
fn merge_plans(own: &mut HashMap<TermId, Rc<[TrackOp]>>, carried: HashMap<TermId, Rc<[TrackOp]>>) {
    if own.is_empty() {
        *own = carried;
    } else {
        for (literal, plan) in carried {
            own.entry(literal).or_insert(plan);
        }
    }
}

/// Plan of `track_interface_term` (#1893, #4767, #5081, #uflia-hard-mixed-eq).
pub(super) fn plan_interface_term(terms: &TermStore, literal: TermId, ops: &mut Vec<TrackOp>) {
    use crate::term_helpers::{
        extract_interface_arith_term, extract_uf_mixed_eq_operands, extract_uf_mixed_interface_term,
    };
    if let Some(arith_term) = extract_interface_arith_term(terms, literal) {
        ops.push(TrackOp::Arith(arith_term));
    }
    // Also track UF-mixed terms like (+ (g x) 1) for evaluation by the bridge (#4767).
    if let Some(uf_mixed_term) = extract_uf_mixed_interface_term(terms, literal) {
        ops.push(TrackOp::Arith(uf_mixed_term));
    }
    // #uflia-hard-mixed-eq: track UF-mixed compound operands of equality
    // atoms even when NEITHER side is pure arithmetic. The extractors
    // above both require a pure-arith side, so an equality between a UF
    // application and a UF-mixed compound (`(= (Sum a b) (+ (Sum c d) y x))`,
    // mathsat EufLaArithmetic hard*) registered nothing: the bridge never
    // evaluated the compound, the `compound = constant` interface equality
    // was never proposed, and the disequality refutation (SAT asserts the
    // atom false; EUF must derive both sides ~ the same constant) was
    // unreachable — the N-O search accepted a model the strict
    // ite_uf_definition gate then rejected, degrading UNSAT to unknown.
    let (mixed_lhs, mixed_rhs) = extract_uf_mixed_eq_operands(terms, literal);
    ops.extend(
        [mixed_lhs, mixed_rhs]
            .into_iter()
            .flatten()
            .map(TrackOp::Arith),
    );
    plan_distinct_args(terms, literal, ops);
}

/// Plan of `track_distinct_args` (#5081): register both sides of a
/// distinct/disequality as interface arith terms.
///
/// After `mk_distinct`, binary `distinct` becomes `NOT(= LHS RHS)`. If LHS or
/// RHS is an Int- or Real-sorted, arithmetically evaluable expression, the
/// bridge evaluates it and propagates `term = constant` equalities to EUF
/// (`evaluate_arith_term_with_reasons` for Int,
/// `evaluate_real_arith_term_with_reasons` for Real, #4906); when both sides
/// evaluate to the same value, EUF's distinct check detects the conflict.
fn plan_distinct_args(terms: &TermStore, literal: TermId, ops: &mut Vec<TrackOp>) {
    use crate::term_helpers::decode_non_bool_eq;
    let inner = match terms.get(literal) {
        TermData::Not(inner) => *inner,
        _ => return,
    };
    let Some((lhs, rhs)) = decode_non_bool_eq(terms, inner) else {
        return;
    };
    for arg in [lhs, rhs] {
        if matches!(terms.sort(arg), ay_core::Sort::Int | ay_core::Sort::Real)
            && is_arith_evaluable(terms, arg)
        {
            ops.push(TrackOp::Arith(arg));
        }
    }
}

/// Plan of `collect_int_constants`: every Int constant in first-visit DFS
/// order (#3712 visited set, #8414 stack growth).
pub(super) fn plan_int_constants(terms: &TermStore, term: TermId, ops: &mut Vec<TrackOp>) {
    let mut visited = HashSet::default();
    plan_int_constants_inner(terms, term, &mut visited, ops);
}

fn plan_int_constants_inner(
    terms: &TermStore,
    term: TermId,
    visited: &mut HashSet<TermId>,
    ops: &mut Vec<TrackOp>,
) {
    stacker::maybe_grow(
        CONST_COLLECT_STACK_RED_ZONE,
        CONST_COLLECT_STACK_SIZE,
        || {
            if !visited.insert(term) {
                return;
            }
            match terms.get(term) {
                TermData::Const(Constant::Int(n)) => ops.push(TrackOp::IntConst(n.clone(), term)),
                TermData::App(_, args) => {
                    for &arg in args {
                        plan_int_constants_inner(terms, arg, visited, ops);
                    }
                }
                TermData::Not(inner) => plan_int_constants_inner(terms, *inner, visited, ops),
                TermData::Ite(c, t, e) => {
                    plan_int_constants_inner(terms, *c, visited, ops);
                    plan_int_constants_inner(terms, *t, visited, ops);
                    plan_int_constants_inner(terms, *e, visited, ops);
                }
                _ => {}
            }
        },
    );
}

/// Plan of `collect_real_constants` (#4915): every Rational constant, and every
/// Int constant as a rational (`(= x 2)` over a Real `x`), in first-visit DFS
/// order (#3712 visited set, #8414 stack growth).
pub(super) fn plan_real_constants(terms: &TermStore, term: TermId, ops: &mut Vec<TrackOp>) {
    let mut visited = HashSet::default();
    plan_real_constants_inner(terms, term, &mut visited, ops);
}

fn plan_real_constants_inner(
    terms: &TermStore,
    term: TermId,
    visited: &mut HashSet<TermId>,
    ops: &mut Vec<TrackOp>,
) {
    stacker::maybe_grow(
        CONST_COLLECT_STACK_RED_ZONE,
        CONST_COLLECT_STACK_SIZE,
        || {
            if !visited.insert(term) {
                return;
            }
            match terms.get(term) {
                TermData::Const(Constant::Rational(r)) => {
                    ops.push(TrackOp::RealConst(r.0.clone(), term));
                }
                TermData::Const(Constant::Int(n)) => {
                    ops.push(TrackOp::RealConst(BigRational::from(n.clone()), term));
                }
                TermData::App(_, args) => {
                    for &arg in args {
                        plan_real_constants_inner(terms, arg, visited, ops);
                    }
                }
                TermData::Not(inner) => plan_real_constants_inner(terms, *inner, visited, ops),
                TermData::Ite(c, t, e) => {
                    plan_real_constants_inner(terms, *c, visited, ops);
                    plan_real_constants_inner(terms, *t, visited, ops);
                    plan_real_constants_inner(terms, *e, visited, ops);
                }
                _ => {}
            }
        },
    );
}

/// Plan of `track_uf_arith_args` (#5081, #6846): UF applications of Int/Real
/// sort and the arithmetic-evaluable arguments of UF applications and of
/// `select`/`store`, in stack-walk order.
pub(super) fn plan_uf_arith_args(terms: &TermStore, root: TermId, ops: &mut Vec<TrackOp>) {
    let mut stack = vec![root];
    let mut visited = HashSet::default();
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::App(Symbol::Named(name), args) => {
                // Array congruence also needs arithmetic index terms from
                // builtins like `select` / `store`, not just UF arguments.
                let track_args =
                    !BUILTIN_OPS.contains(&name.as_str()) || name == "select" || name == "store";
                if track_args && !args.is_empty() {
                    // #6846: track the UF application ITSELF when it has
                    // Int/Real sort, so model-equality discovery can compare
                    // two UF applications by their arithmetic values.
                    if !BUILTIN_OPS.contains(&name.as_str())
                        && matches!(terms.sort(term), ay_core::Sort::Int | ay_core::Sort::Real)
                    {
                        ops.push(TrackOp::Arith(term));
                    }
                    for &arg in args {
                        if is_arith_evaluable(terms, arg) {
                            ops.push(TrackOp::Arith(arg));
                        }
                    }
                }
                stack.extend(args.iter().copied());
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => stack.extend([*c, *t, *e]),
            _ => {}
        }
    }
}
