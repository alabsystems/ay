// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! BV-to-Int abstraction for CHC problems (#5981).
//!
//! Converts BV-sorted predicates and operations to integer arithmetic,
//! enabling AY's LIA invariant discovery to synthesize invariants for BV CHC problems.
//!
//! Soundness: the exact mode encodes bvadd/bvsub/bvmul with modular arithmetic
//! and range constraints, so Safe results transfer back to the original BV
//! problem. The legacy relaxed mode is retained only for tests/experiments and
//! is unsound for Safe proofs because signed overflow changes reachability
//! (#6848).

mod ops;
#[cfg(test)]
mod tests;

use std::sync::Arc;

use num_bigint::BigInt;
use num_traits::{One, ToPrimitive};

use crate::smt::SmtValue;
use crate::{
    ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause,
    InvariantModel, PredicateId, PredicateInterpretation,
};
use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::{
    BackTranslator, IdentityBackTranslator, InvalidityWitness, TransformMemoryReport,
    TransformObligation, TransformationResult, Transformer, ValidityWitness,
};

/// Tracks BV↔Int mapping for back-translation.
pub(crate) struct BvIntMap {
    /// Per-predicate: argument index -> original BV width (None if not BV).
    pred_arg_widths: FxHashMap<PredicateId, Vec<Option<u32>>>,
    /// Per-predicate original argument sorts, used to concretize invalidity witnesses.
    pred_arg_sorts: FxHashMap<PredicateId, Vec<ChcSort>>,
    uf_counter: u32,
    /// Maximum width for bit-decomposition of variable-variable bitwise ops.
    /// Widths above this use UF fallback. Default: 32. Set to 0 for UF-only
    /// mode (CEGAR Phase 1), or 64 for full decomposition (#8289).
    decompose_limit: u32,
    /// True if any variable-variable bitwise operation was UF-approximated
    /// during this abstraction pass. Used by CEGAR to decide whether
    /// refinement (re-running with higher decompose_limit) is needed (#8289).
    had_bitwise_uf_fallback: bool,
    /// Whether this pass used the legacy relaxed integer abstraction.
    relaxed: bool,
    /// WORD-BV lazy bitwise (#8, Eldarica FMCAD'18): when a variable-variable
    /// bitwise op falls back to a UF, emit bounded interpreted side constraints
    /// (e.g. `0 <= x&y <= min(x,y)`, XOR parity) into the enclosing clause
    /// instead of leaving the UF fully unconstrained. Disabled via
    /// `AY_CHC_DISABLE_WORD_BV`.
    lazy_bitwise_bounds: bool,
    /// Side constraints produced while abstracting the current clause (bounded
    /// facts about bitwise UF results). Drained into the clause's body
    /// constraint by `abstract_problem` after each clause.
    pending_constraints: Vec<ChcExpr>,
}

impl BvIntMap {
    fn new() -> Self {
        Self {
            pred_arg_widths: FxHashMap::default(),
            pred_arg_sorts: FxHashMap::default(),
            uf_counter: 0,
            decompose_limit: ops::DEFAULT_BIT_DECOMPOSITION_WIDTH_LIMIT,
            had_bitwise_uf_fallback: false,
            relaxed: false,
            lazy_bitwise_bounds: true,
            pending_constraints: Vec::new(),
        }
    }

    fn with_decompose_limit(mut self, limit: u32) -> Self {
        self.decompose_limit = limit;
        self
    }

    fn next_uf_name(&mut self, base: &str, width: u32) -> String {
        self.uf_counter += 1;
        format!("__bv2int_{base}_{}_w{width}", self.uf_counter)
    }
}

/// BV-to-Int abstraction transformer. No-op for non-BV problems.
pub(crate) struct BvToIntAbstractor {
    verbose: bool,
    /// Legacy experimental mode. When true, BV arithmetic is mapped to
    /// unbounded integer arithmetic without modular wrapping. This is UNSOUND
    /// for Safe proofs under signed overflow and must not be used in
    /// production solving paths (#6848).
    relaxed: bool,
    /// Maximum width for bit-decomposition of variable-variable bitwise ops.
    /// - `None`: use the default limit (32 bits)
    /// - `Some(0)`: UF-only mode (CEGAR Phase 1: no bit-decomposition)
    /// - `Some(64)`: full decomposition (CEGAR Phase 2: decompose all widths)
    ///   Part of #8289.
    decompose_limit: Option<u32>,
}

impl BvToIntAbstractor {
    pub(crate) fn new() -> Self {
        Self {
            verbose: false,
            relaxed: false,
            decompose_limit: None,
        }
    }

    pub(crate) fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    /// Enable relaxed mode: unbounded integer arithmetic without modular
    /// wrapping. Callers MUST validate Safe results against the original BV
    /// problem before accepting them (#4198, #6848).
    pub(crate) fn with_relaxed(mut self, relaxed: bool) -> Self {
        self.relaxed = relaxed;
        self
    }

    /// Set the maximum width for bit-decomposition of variable-variable
    /// bitwise ops. Widths above this use UF fallback.
    ///
    /// - `0`: UF-only mode (CEGAR Phase 1, fastest but least precise)
    /// - `32`: default (decompose BV8/BV16/BV32, UF for BV64+)
    /// - `64`: full decomposition (CEGAR Phase 2, precise but more expensive)
    ///
    /// Part of #8289: CEGAR-style refinement. Phase 1 uses `0` for speed,
    /// Phase 2 uses `64` for precision when UF approximation fails.
    pub(crate) fn with_decompose_limit(mut self, limit: u32) -> Self {
        self.decompose_limit = Some(limit);
        self
    }

    /// Create a relaxed BvToInt abstractor for unit tests.
    #[cfg(test)]
    pub(crate) fn relaxed() -> Self {
        Self::new().with_relaxed(true)
    }
}

fn sort_contains_bv(sort: &ChcSort) -> bool {
    match sort {
        ChcSort::BitVec(_) => true,
        ChcSort::Array(key, value) => sort_contains_bv(key) || sort_contains_bv(value),
        ChcSort::Datatype { constructors, .. } => constructors
            .iter()
            .any(|ctor| ctor.selectors.iter().any(|sel| sort_contains_bv(&sel.sort))),
        ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::Uninterpreted(_) => false,
    }
}

fn problem_contains_recursive_bv_sorts(problem: &ChcProblem) -> bool {
    problem
        .predicates()
        .iter()
        .flat_map(|pred| pred.arg_sorts.iter())
        .any(sort_contains_bv)
}

impl Transformer for BvToIntAbstractor {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        if !problem_contains_recursive_bv_sorts(&problem) {
            return TransformationResult {
                problem,
                back_translator: Box::new(IdentityBackTranslator),
            };
        }
        let mut map = BvIntMap::new();
        map.relaxed = self.relaxed;
        map.lazy_bitwise_bounds = !super::word_bv_hardening_disabled();
        if let Some(limit) = self.decompose_limit {
            map = map.with_decompose_limit(limit);
        }
        let transformed = abstract_problem(&problem, &mut map, self.verbose, self.relaxed);
        if self.verbose && map.had_bitwise_uf_fallback {
            safe_eprintln!(
                "BvToInt: {} variable-variable bitwise ops used UF fallback (decompose_limit={})",
                map.uf_counter,
                map.decompose_limit
            );
        }
        TransformationResult {
            problem: transformed,
            back_translator: Box::new(BvIntBackTranslator { map }),
        }
    }
}

// ── Core abstraction ──────────────────────────────────────────────────────

fn abstract_problem(
    problem: &ChcProblem,
    map: &mut BvIntMap,
    _verbose: bool,
    relaxed: bool,
) -> ChcProblem {
    let mut result = ChcProblem::new();
    // Preserve datatype definitions: problem-level metadata that drives
    // executor routing (#7016) and the DT-problem check-sat policies. BvToInt
    // rewrites BV sorts only — it never touches datatypes — so dropping the
    // defs here silently degraded downstream query routing on DT+BV problems
    // (#chc25-dtbv-lane-perf).
    for (name, ctors) in problem.datatype_defs() {
        result.add_datatype_def(name.clone(), ctors.clone());
    }

    // Convert predicate signatures: BV(w) → Int, recording widths.
    // Array sub-sorts are also recursively abstracted: Array(BV(32), Bool)
    // becomes Array(Int, Bool) so that sort annotations match abstracted
    // expressions throughout the problem (#6122).
    for pred in problem.predicates() {
        let mut widths = Vec::with_capacity(pred.arg_sorts.len());
        let sorts: Vec<ChcSort> = pred
            .arg_sorts
            .iter()
            .map(|s| match s {
                ChcSort::BitVec(w) => {
                    widths.push(Some(*w));
                    ChcSort::Int
                }
                other => {
                    widths.push(None);
                    ops::abstract_sort(other)
                }
            })
            .collect();
        let pid = result.declare_predicate(&pred.name, sorts);
        map.pred_arg_widths.insert(pid, widths);
        map.pred_arg_sorts.insert(pid, pred.arg_sorts.clone());
    }

    // Abstract each clause
    let abs = |e: &ChcExpr, m: &mut BvIntMap| abstract_expr(e, m, relaxed);
    for clause in problem.clauses() {
        let body_preds: Vec<(PredicateId, Vec<ChcExpr>)> = clause
            .body
            .predicates
            .iter()
            .map(|(pid, args)| {
                let abs_args: Vec<ChcExpr> = args.iter().map(|a| abs(a, map)).collect();
                (*pid, abs_args)
            })
            .collect();

        let body_constraint = clause.body.constraint.as_ref().map(|c| abs(c, map));

        let head = match &clause.head {
            ClauseHead::Predicate(pid, args) => {
                let abs_args = args.iter().map(|a| abs(a, map)).collect();
                ClauseHead::Predicate(*pid, abs_args)
            }
            ClauseHead::False => ClauseHead::False,
        };

        // WORD-BV lazy bitwise (#8): bounded side constraints emitted for
        // bitwise UF fallbacks in this clause. Conjoining valid facts about
        // the concrete bitwise functions preserves the over-approximation
        // (every original behavior still has an abstract counterpart).
        let body_constraint = if map.pending_constraints.is_empty() {
            body_constraint
        } else {
            let side = ChcExpr::and_all(map.pending_constraints.drain(..));
            Some(match body_constraint {
                Some(c) => ChcExpr::and(c, side),
                None => side,
            })
        };

        let body = ClauseBody::new(body_preds, body_constraint);
        result.add_clause(HornClause::new(body, head));
    }

    // In relaxed mode, skip range constraints and treat BV as unbounded Int.
    // This mode is retained only for tests/experiments; it is unsound for Safe
    // proofs because BV overflow is not preserved (#6848).
    if !relaxed {
        collect_range_constraints(&mut result, map);
    }
    result
}

/// Embed BV range constraints into existing clause head arguments.
///
/// Instead of adding identity clauses `P(x) => P(x) ∧ 0≤x<2^w` (which create
/// duplicate head definitions and block clause inlining), this adds range
/// constraints directly to each clause that defines a predicate with BV-converted
/// Int arguments. For a clause `body => P(a1, ..., an)`, if `ai` was originally
/// `BitVec(w)`, we add `0 <= ai < 2^w` to the body constraint.
fn collect_range_constraints(result: &mut ChcProblem, map: &BvIntMap) {
    let clauses = result.clauses().to_vec();
    // Clear and re-add clauses with embedded range constraints
    *result = {
        let mut new_problem = ChcProblem::new();
        // Preserve datatype definitions (problem-level routing metadata,
        // #7016) — see `abstract_problem`.
        for (name, ctors) in result.datatype_defs() {
            new_problem.add_datatype_def(name.clone(), ctors.clone());
        }
        for pred in result.predicates() {
            new_problem.declare_predicate(&pred.name, pred.arg_sorts.clone());
        }
        for clause in &clauses {
            let range_constraints = match &clause.head {
                ClauseHead::Predicate(pid, head_args) => {
                    if let Some(widths) = map.pred_arg_widths.get(pid) {
                        let mut ranges = Vec::new();
                        for (w_opt, arg) in widths.iter().zip(head_args.iter()) {
                            if let Some(w) = w_opt {
                                let expr = arg.clone();
                                // #7006 / W1: for BV widths >= 63 the UPPER bound
                                // 2^w overflows Rational64 in the LRA solver
                                // (i64::MAX numerator), so it must be skipped. But
                                // the LOWER bound `0 <= x` is always representable
                                // AND sound: an abstracted BV value is non-negative
                                // by construction (the exact modular encoding keeps
                                // it in [0, 2^w)). Emitting `0 <= x` alone
                                // discharges the pervasive `0 <= idx` / `0 <=
                                // offset` slice-length and pointer-offset bounds
                                // checks without the un-dischargeable 2^w mod
                                // blowup, instead of throwing the whole range away.
                                if *w >= 63 {
                                    ranges.push(ChcExpr::ge(expr, ChcExpr::int(0)));
                                } else {
                                    let bound = ops::int_pow2(*w);
                                    ranges.push(ChcExpr::and(
                                        ChcExpr::ge(expr.clone(), ChcExpr::int(0)),
                                        ChcExpr::lt(expr, bound),
                                    ));
                                }
                            }
                        }
                        ranges
                    } else {
                        Vec::new()
                    }
                }
                ClauseHead::False => Vec::new(),
            };

            if range_constraints.is_empty() {
                new_problem.add_clause(clause.clone());
            } else {
                // Combine existing body constraint with range constraints
                let mut all_constraints: Vec<ChcExpr> = Vec::new();
                if let Some(c) = &clause.body.constraint {
                    all_constraints.push(c.clone());
                }
                all_constraints.extend(range_constraints);
                let combined = all_constraints
                    .into_iter()
                    .reduce(ChcExpr::and)
                    .expect("non-empty");
                let new_body = ClauseBody::new(clause.body.predicates.clone(), Some(combined));
                new_problem.add_clause(HornClause::new(new_body, clause.head.clone()));
            }
        }
        new_problem
    };
}

fn abstract_expr(expr: &ChcExpr, map: &mut BvIntMap, relaxed: bool) -> ChcExpr {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::BitVec(val, w) => {
            if relaxed {
                // In relaxed mode, signed comparisons (bvsle, bvslt, etc.) are mapped
                // to plain <=/<. For this to be semantically correct, BV constants must
                // use their signed interpretation. E.g. #xffffffff (32-bit) = -1, not
                // 4294967295. Without this, (bvsle #xffffffff #x00000000) would become
                // (4294967295 <= 0) = false instead of (-1 <= 0) = true. (#5877)
                //
                // WORD-BV (#8, resolves #7548): BigInt arithmetic — every width
                // translates exactly, no overflow abort. `from_bigint` yields a
                // plain Int(i128) when the value fits and an exact Horner tree
                // beyond that.
                let is_negative = *w > 0
                    && if *w >= 128 {
                        *val >= (1u128 << 127)
                    } else {
                        *val >= (1u128 << (w - 1))
                    };
                if is_negative {
                    // Negative signed value: val - 2^w
                    ChcExpr::from_bigint(BigInt::from(*val) - (BigInt::one() << *w))
                } else {
                    ChcExpr::from_bigint(BigInt::from(*val))
                }
            } else {
                // In exact mode, BV values are unsigned [0, 2^w) and signed comparisons
                // use explicit offset subtraction (signed_cmp helper in ops.rs).
                //
                // WORD-BV (#8, resolves #7548): the old i64 two-limb decomposition
                // aborted the whole transformation for constants >= 2^95. BigInt
                // conversion is exact for every u128 value, so BV64+ constants
                // always translate.
                ChcExpr::from_bigint(BigInt::from(*val))
            }
        }
        ChcExpr::Var(v) => {
            // Abstract variable sort: BV(w) → Int, and recursively abstract
            // compound sorts like Array(BV(w), V) → Array(Int, V) (#6122).
            let abs_sort = ops::abstract_sort(&v.sort);
            if abs_sort == v.sort {
                expr.clone()
            } else {
                ChcExpr::Var(ChcVar::new(v.name.clone(), abs_sort))
            }
        }
        ChcExpr::Op(op, args) => {
            let aa: Vec<ChcExpr> = args
                .iter()
                .map(|a| abstract_expr(a, map, relaxed))
                .collect();
            if relaxed {
                ops::abstract_op_relaxed(op, args, aa, map)
            } else {
                ops::abstract_op(op, args, aa, map)
            }
        }
        ChcExpr::PredicateApp(name, id, args) => ChcExpr::PredicateApp(
            name.clone(),
            *id,
            args.iter()
                .map(|a| Arc::new(abstract_expr(a, map, relaxed)))
                .collect(),
        ),
        ChcExpr::FuncApp(name, sort, args) => ChcExpr::FuncApp(
            name.clone(),
            ops::abstract_sort(sort),
            args.iter()
                .map(|a| Arc::new(abstract_expr(a, map, relaxed)))
                .collect(),
        ),
        ChcExpr::ConstArray(ks, val) => {
            // Recursively abstract the key sort: Array(BV(w), V) → Array(Int, V) (#6122)
            ChcExpr::ConstArray(
                ops::abstract_sort(ks),
                Arc::new(abstract_expr(val, map, relaxed)),
            )
        }
        _ => expr.clone(),
    })
}

// ── Back-translation ───────────────────────────────────────────────────────

struct BvIntBackTranslator {
    map: BvIntMap,
}

impl BackTranslator for BvIntBackTranslator {
    fn translate_validity(&self, witness: ValidityWitness) -> ValidityWitness {
        concretize_inv(&witness, &self.map)
    }
    fn translate_invalidity(&self, witness: InvalidityWitness) -> InvalidityWitness {
        concretize_cex(witness, &self.map)
    }
    fn had_bitwise_uf_fallback(&self) -> bool {
        self.map.had_bitwise_uf_fallback
    }

    fn transform_memory(&self) -> TransformMemoryReport {
        let mut obligations = vec![
            TransformObligation::named("bv-to-int-model-backtranslation"),
            TransformObligation::named("original-validation-on-safe"),
            TransformObligation::named("original-replay-on-unsafe"),
        ];
        let mut unsafe_complete = true;
        if self.map.had_bitwise_uf_fallback {
            obligations.push(TransformObligation::named("bitwise-uf-refinement"));
            unsafe_complete = false;
        }
        if self.map.relaxed {
            obligations.push(TransformObligation::named(
                "relaxed-bv-to-int-overflow-validation",
            ));
            unsafe_complete = false;
        }
        let report =
            TransformMemoryReport::with_original_validation_obligations("bv_to_int", obligations);
        if unsafe_complete {
            report
        } else {
            report.with_incomplete_unsafe_backtranslation()
        }
    }
}

fn concretize_inv(inv: &InvariantModel, map: &BvIntMap) -> InvariantModel {
    let mut result = InvariantModel::new();
    for (pid, interp) in inv.iter() {
        let orig_sorts = map.pred_arg_sorts.get(pid);
        let widths = map.pred_arg_widths.get(pid);
        let vars: Vec<ChcVar> = interp
            .vars
            .iter()
            .enumerate()
            .map(|(i, v)| {
                // First try: restore BV sort from widths (direct BV args).
                if let Some(w) = widths.and_then(|ws| ws.get(i).copied().flatten()) {
                    return ChcVar::new(v.name.clone(), ChcSort::BitVec(w));
                }
                // Second try: restore original sort (handles Array(BV, _) -> Array(Int, _)).
                if let Some(orig) = orig_sorts.and_then(|ss| ss.get(i)) {
                    if *orig != v.sort {
                        return ChcVar::new(v.name.clone(), orig.clone());
                    }
                }
                v.clone()
            })
            .collect();
        // Build sort environment mapping the *old* (Int-sorted) variables from the
        // abstract formula to their *new* (restored) sorts. The formula still
        // contains the old variable identities, so the lookup key must match those.
        // Clause-inlining back-translation can synthesize formulas that contain
        // clause-local variables sharing a name with a predicate parameter but
        // having a different sort. By keying on the old full variable identity
        // (not just name), we avoid turning array locals into BV scalars.
        let sort_env: FxHashMap<ChcVar, ChcSort> = interp
            .vars
            .iter()
            .zip(vars.iter())
            .filter(|(old, new)| old.sort != new.sort)
            .map(|(old, new)| (old.clone(), new.sort.clone()))
            .collect();
        // Transform the formula: convert Int constants to BV where context
        // demands it (e.g., array indices, BV comparisons).
        let formula = int_to_bv_formula(&interp.formula, &sort_env).simplify_constants();
        result.set(*pid, PredicateInterpretation::new(vars, formula));
    }
    result.verification_method = inv.verification_method;
    result
}

/// Recursively restore original sorts while preserving abstract Int semantics.
///
/// A validity witness from the BV-to-Int abstraction is still an Int formula:
/// former BV variables denote their unsigned numeric values. Back-translation
/// therefore restores the original variable sorts but keeps arithmetic and
/// comparisons in the Int domain, bridging restored BV terms with `bv2nat` /
/// `int2bv` as needed. Rewriting learned Int arithmetic back into native BV
/// arithmetic would reintroduce modular wrapping and change the witness.
fn int_to_bv_formula(expr: &ChcExpr, sort_env: &FxHashMap<ChcVar, ChcSort>) -> ChcExpr {
    match expr {
        // Variables: update sort from environment.
        ChcExpr::Var(v) => {
            if let Some(new_sort) = sort_env.get(v) {
                if *new_sort != v.sort {
                    return ChcExpr::var(ChcVar::new(v.name.clone(), new_sort.clone()));
                }
            }
            expr.clone()
        }
        // Int constants: may need conversion to BV if used in BV context.
        // Leave as-is here; parent operations handle context-driven conversion.
        ChcExpr::Int(_) | ChcExpr::Bool(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => {
            expr.clone()
        }
        ChcExpr::Op(op, args) => {
            let new_args: Vec<_> = args
                .iter()
                .map(|a| int_to_bv_formula(a, sort_env))
                .collect();
            match op {
                // Select: convert Int index to BV if array has BV index sort.
                ChcOp::Select if new_args.len() == 2 => {
                    let arr = &new_args[0];
                    let idx = &new_args[1];
                    if let ChcSort::Array(idx_sort, _) = arr.sort() {
                        let idx = coerce_to_sort(idx, &idx_sort);
                        return ChcExpr::select(arr.clone(), idx);
                    }
                    ChcExpr::select(arr.clone(), idx.clone())
                }
                // Store: convert Int index and value to BV sorts if needed.
                ChcOp::Store if new_args.len() == 3 => {
                    let arr = &new_args[0];
                    let idx = &new_args[1];
                    let val = &new_args[2];
                    if let ChcSort::Array(idx_sort, val_sort) = arr.sort() {
                        let idx = coerce_to_sort(idx, &idx_sort);
                        let val = coerce_to_sort(val, &val_sort);
                        return ChcExpr::store(arr.clone(), idx, val);
                    }
                    ChcExpr::store(arr.clone(), idx.clone(), val.clone())
                }
                // Equality/comparisons: keep the abstract Int semantics.
                ChcOp::Eq | ChcOp::Ne | ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge
                    if new_args.len() == 2 =>
                {
                    let mut a = new_args[0].clone();
                    let mut b = new_args[1].clone();
                    let a_sort = a.sort();
                    let b_sort = b.sort();
                    if a_sort != b_sort {
                        match (&a_sort, &b_sort) {
                            (ChcSort::Array(_, _), ChcSort::Array(_, _))
                                if sort_contains_bv(&a_sort) =>
                            {
                                b = concretize_expr_to_sort(&args[1], &a_sort, sort_env);
                            }
                            (ChcSort::Array(_, _), ChcSort::Array(_, _))
                                if sort_contains_bv(&b_sort) =>
                            {
                                a = concretize_expr_to_sort(&args[0], &b_sort, sort_env);
                            }
                            _ => {}
                        }
                    }
                    if let Some(translated) = translate_bv_int_comparison(op, &a, &b) {
                        return translated;
                    }
                    if matches!(op, ChcOp::Eq | ChcOp::Ne) {
                        if let Some(translated) = translate_array_equality(op, &a, &b) {
                            return translated;
                        }
                    }
                    match (a.sort(), b.sort()) {
                        (ChcSort::BitVec(_), _) | (_, ChcSort::BitVec(_)) => {
                            let a = coerce_to_sort(&a, &ChcSort::Int);
                            let b = coerce_to_sort(&b, &ChcSort::Int);
                            ChcExpr::Op(*op, vec![Arc::new(a), Arc::new(b)])
                        }
                        _ => ChcExpr::Op(*op, vec![Arc::new(a), Arc::new(b)]),
                    }
                }
                // Arithmetic: preserve the learned Int arithmetic and lift
                // restored BV terms through `bv2nat`.
                ChcOp::Add | ChcOp::Sub | ChcOp::Mul | ChcOp::Mod | ChcOp::Div
                    if new_args.len() == 2
                        && (matches!(new_args[0].sort(), ChcSort::BitVec(_))
                            || matches!(new_args[1].sort(), ChcSort::BitVec(_))) =>
                {
                    let a = coerce_to_sort(&new_args[0], &ChcSort::Int);
                    let b = coerce_to_sort(&new_args[1], &ChcSort::Int);
                    ChcExpr::Op(*op, vec![Arc::new(a), Arc::new(b)])
                }
                _ => ChcExpr::Op(*op, new_args.into_iter().map(Arc::new).collect()),
            }
        }
        // Predicate/func applications: recurse into args.
        ChcExpr::PredicateApp(name, sort, args) => {
            let new_args: Vec<_> = args
                .iter()
                .map(|a| Arc::new(int_to_bv_formula(a, sort_env)))
                .collect();
            ChcExpr::PredicateApp(name.clone(), *sort, new_args)
        }
        ChcExpr::FuncApp(name, sort, args) => {
            let new_args: Vec<_> = args
                .iter()
                .map(|a| Arc::new(int_to_bv_formula(a, sort_env)))
                .collect();
            ChcExpr::FuncApp(name.clone(), sort.clone(), new_args)
        }
        ChcExpr::ConstArray(sort, val) => {
            ChcExpr::ConstArray(sort.clone(), Arc::new(int_to_bv_formula(val, sort_env)))
        }
        ChcExpr::ConstArrayMarker(_) | ChcExpr::IsTesterMarker(_) => expr.clone(),
    }
}

fn concretize_expr_to_sort(
    expr: &ChcExpr,
    target_sort: &ChcSort,
    sort_env: &FxHashMap<ChcVar, ChcSort>,
) -> ChcExpr {
    match target_sort {
        ChcSort::Array(index_sort, element_sort) => {
            concretize_array_expr(expr, index_sort.as_ref(), element_sort.as_ref(), sort_env)
        }
        _ => {
            let translated = int_to_bv_formula(expr, sort_env);
            coerce_to_sort(&translated, target_sort)
        }
    }
}

fn concretize_array_expr(
    expr: &ChcExpr,
    index_sort: &ChcSort,
    element_sort: &ChcSort,
    sort_env: &FxHashMap<ChcVar, ChcSort>,
) -> ChcExpr {
    let target_sort = ChcSort::Array(Box::new(index_sort.clone()), Box::new(element_sort.clone()));
    match expr {
        // Array literals need the restored predicate sort to rekey nested stores.
        ChcExpr::ConstArray(_, val) => ChcExpr::ConstArray(
            index_sort.clone(),
            Arc::new(concretize_expr_to_sort(val, element_sort, sort_env)),
        ),
        ChcExpr::Op(ChcOp::Store, args) if args.len() == 3 => {
            let arr = concretize_expr_to_sort(&args[0], &target_sort, sort_env);
            let idx = concretize_expr_to_sort(&args[1], index_sort, sort_env);
            let val = concretize_expr_to_sort(&args[2], element_sort, sort_env);
            ChcExpr::store(arr, idx, val)
        }
        ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
            let cond = int_to_bv_formula(&args[0], sort_env);
            let then_ = concretize_expr_to_sort(&args[1], &target_sort, sort_env);
            let else_ = concretize_expr_to_sort(&args[2], &target_sort, sort_env);
            ChcExpr::ite(cond, then_, else_)
        }
        _ => int_to_bv_formula(expr, sort_env),
    }
}

fn translate_bv_int_comparison(op: &ChcOp, lhs: &ChcExpr, rhs: &ChcExpr) -> Option<ChcExpr> {
    if let ChcSort::BitVec(width) = lhs.sort() {
        return Some(translate_unsigned_bv_comparison(
            op,
            lhs,
            &try_const_bigint(rhs)?,
            width,
        ));
    }
    if let ChcSort::BitVec(width) = rhs.sort() {
        return Some(translate_unsigned_bv_comparison(
            &reverse_comparison(op),
            rhs,
            &try_const_bigint(lhs)?,
            width,
        ));
    }
    None
}

fn translate_array_equality(op: &ChcOp, lhs: &ChcExpr, rhs: &ChcExpr) -> Option<ChcExpr> {
    let lhs_sort = lhs.sort();
    let rhs_sort = rhs.sort();
    if lhs_sort == rhs_sort {
        return None;
    }

    let lhs_has_bv = sort_contains_bv(&lhs_sort);
    let rhs_has_bv = sort_contains_bv(&rhs_sort);

    if lhs_has_bv && !rhs_has_bv {
        if let Some(translated) = array_equality_coerce_rhs(op, lhs, rhs, &lhs_sort) {
            return Some(translated);
        }
    }
    if rhs_has_bv && !lhs_has_bv {
        if let Some(translated) = array_equality_coerce_lhs(op, lhs, rhs, &rhs_sort) {
            return Some(translated);
        }
    }

    if let Some(translated) = array_equality_coerce_rhs(op, lhs, rhs, &lhs_sort) {
        return Some(translated);
    }
    if let Some(translated) = array_equality_coerce_lhs(op, lhs, rhs, &rhs_sort) {
        return Some(translated);
    }

    None
}

fn array_equality_coerce_rhs(
    op: &ChcOp,
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    target: &ChcSort,
) -> Option<ChcExpr> {
    if !matches!(target, ChcSort::Array(_, _)) {
        return None;
    }
    let coerced_rhs = coerce_to_sort(rhs, target);
    if coerced_rhs.sort() == *target {
        Some(ChcExpr::Op(
            *op,
            vec![Arc::new(lhs.clone()), Arc::new(coerced_rhs)],
        ))
    } else {
        None
    }
}

fn array_equality_coerce_lhs(
    op: &ChcOp,
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    target: &ChcSort,
) -> Option<ChcExpr> {
    if !matches!(target, ChcSort::Array(_, _)) {
        return None;
    }
    let coerced_lhs = coerce_to_sort(lhs, target);
    if coerced_lhs.sort() == *target {
        Some(ChcExpr::Op(
            *op,
            vec![Arc::new(coerced_lhs), Arc::new(rhs.clone())],
        ))
    } else {
        None
    }
}

fn translate_unsigned_bv_comparison(
    op: &ChcOp,
    bv_expr: &ChcExpr,
    int_value: &BigInt,
    width: u32,
) -> ChcExpr {
    let zero = BigInt::from(0u8);
    let max = max_unsigned_bv(width);
    if int_value < &zero {
        return match op {
            ChcOp::Eq => ChcExpr::Bool(false),
            ChcOp::Ne => ChcExpr::Bool(true),
            ChcOp::Lt | ChcOp::Le => ChcExpr::Bool(false),
            ChcOp::Gt | ChcOp::Ge => ChcExpr::Bool(true),
            _ => unreachable!("translate_unsigned_bv_comparison only handles comparisons"),
        };
    }
    if int_value > &max {
        return match op {
            ChcOp::Eq => ChcExpr::Bool(false),
            ChcOp::Ne => ChcExpr::Bool(true),
            ChcOp::Lt | ChcOp::Le => ChcExpr::Bool(true),
            ChcOp::Gt | ChcOp::Ge => ChcExpr::Bool(false),
            _ => unreachable!("translate_unsigned_bv_comparison only handles comparisons"),
        };
    }
    if int_value == &zero {
        return match op {
            ChcOp::Lt => ChcExpr::Bool(false),
            ChcOp::Ge => ChcExpr::Bool(true),
            _ => build_unsigned_bv_comparison(op, bv_expr, int_value, width),
        };
    }
    if int_value == &max {
        return match op {
            ChcOp::Le => ChcExpr::Bool(true),
            ChcOp::Gt => ChcExpr::Bool(false),
            _ => build_unsigned_bv_comparison(op, bv_expr, int_value, width),
        };
    }

    build_unsigned_bv_comparison(op, bv_expr, int_value, width)
}

fn build_unsigned_bv_comparison(
    op: &ChcOp,
    bv_expr: &ChcExpr,
    int_value: &BigInt,
    width: u32,
) -> ChcExpr {
    let rhs = ChcExpr::BitVec(
        int_value
            .to_u128()
            .expect("in-range BV comparison constants must fit in u128"),
        width,
    );
    ChcExpr::Op(
        int_cmp_to_bv(op),
        vec![Arc::new(bv_expr.clone()), Arc::new(rhs)],
    )
}

fn max_unsigned_bv(width: u32) -> BigInt {
    (BigInt::one() << width) - BigInt::one()
}

fn try_const_bigint(expr: &ChcExpr) -> Option<BigInt> {
    match expr {
        ChcExpr::Int(value) => Some(BigInt::from(*value)),
        ChcExpr::Op(ChcOp::Add, args) => args.iter().try_fold(BigInt::from(0u8), |acc, arg| {
            Some(acc + try_const_bigint(arg)?)
        }),
        ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
            let mut args = args.iter();
            let first = try_const_bigint(args.next()?)?;
            args.try_fold(first, |acc, arg| Some(acc - try_const_bigint(arg)?))
        }
        ChcExpr::Op(ChcOp::Mul, args) => args
            .iter()
            .try_fold(BigInt::one(), |acc, arg| Some(acc * try_const_bigint(arg)?)),
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => Some(-try_const_bigint(&args[0])?),
        _ => None,
    }
}

fn reverse_comparison(op: &ChcOp) -> ChcOp {
    match op {
        ChcOp::Eq => ChcOp::Eq,
        ChcOp::Ne => ChcOp::Ne,
        ChcOp::Lt => ChcOp::Gt,
        ChcOp::Le => ChcOp::Ge,
        ChcOp::Gt => ChcOp::Lt,
        ChcOp::Ge => ChcOp::Le,
        _ => unreachable!("reverse_comparison only handles comparisons"),
    }
}

/// Coerce an expression to a target sort for back-translation.
fn coerce_to_sort(expr: &ChcExpr, target: &ChcSort) -> ChcExpr {
    if expr.sort() == *target {
        return expr.clone();
    }

    if let ChcSort::Array(index_sort, element_sort) = target {
        return match expr {
            ChcExpr::ConstArray(_, value) => {
                let value = coerce_to_sort(value, element_sort);
                if value.sort() == **element_sort {
                    ChcExpr::ConstArray(index_sort.as_ref().clone(), Arc::new(value))
                } else {
                    expr.clone()
                }
            }
            ChcExpr::Op(ChcOp::Store, args) if args.len() == 3 => {
                let arr = coerce_to_sort(&args[0], target);
                if arr.sort() != *target {
                    return expr.clone();
                }
                let idx = coerce_to_sort(&args[1], index_sort);
                let val = coerce_to_sort(&args[2], element_sort);
                if idx.sort() == **index_sort && val.sort() == **element_sort {
                    ChcExpr::store(arr, idx, val)
                } else {
                    expr.clone()
                }
            }
            ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
                let then_expr = coerce_to_sort(&args[1], target);
                let else_expr = coerce_to_sort(&args[2], target);
                if then_expr.sort() == *target && else_expr.sort() == *target {
                    ChcExpr::ite(args[0].as_ref().clone(), then_expr, else_expr)
                } else {
                    expr.clone()
                }
            }
            _ => expr.clone(),
        };
    }

    match (expr, target) {
        (expr, ChcSort::Int) if matches!(expr.sort(), ChcSort::BitVec(_)) => {
            ChcExpr::Op(ChcOp::Bv2Nat, vec![Arc::new(expr.clone())])
        }
        (ChcExpr::Int(n), ChcSort::BitVec(w)) => {
            // Convert Int to BV: take the value modulo 2^w.
            if *w >= 64 {
                // For wide BV, use u128 arithmetic.
                let modulus = 1u128 << w;
                let bits = if *n >= 0 {
                    (*n as u128) % modulus
                } else {
                    let abs = (-*n) as u128;
                    (modulus - (abs % modulus)) % modulus
                };
                return ChcExpr::BitVec(bits, *w);
            }
            let modulus = 1u64 << w;
            let bits = if *n >= 0 {
                (*n as u64) % modulus
            } else {
                let abs = (-*n) as u64;
                (modulus - (abs % modulus)) % modulus
            };
            ChcExpr::BitVec(bits as u128, *w)
        }
        (expr, ChcSort::BitVec(w)) if matches!(expr.sort(), ChcSort::Int) => {
            ChcExpr::Op(ChcOp::Int2Bv(*w), vec![Arc::new(expr.clone())])
        }
        _ => expr.clone(),
    }
}

/// Convert Int comparison op to unsigned BV comparison.
fn int_cmp_to_bv(op: &ChcOp) -> ChcOp {
    match op {
        ChcOp::Eq => ChcOp::Eq,
        ChcOp::Ne => ChcOp::Ne,
        ChcOp::Lt => ChcOp::BvULt,
        ChcOp::Le => ChcOp::BvULe,
        ChcOp::Gt => ChcOp::BvUGt,
        ChcOp::Ge => ChcOp::BvUGe,
        other => *other,
    }
}

fn concretize_cex(mut cex: InvalidityWitness, map: &BvIntMap) -> InvalidityWitness {
    if let Some(witness) = &mut cex.witness {
        for entry in &mut witness.entries {
            concretize_witness_entry(entry, map);
        }
    }
    cex
}

fn concretize_witness_entry(
    entry: &mut crate::pdr::counterexample::DerivationWitnessEntry,
    map: &BvIntMap,
) {
    let Some(arg_sorts) = map.pred_arg_sorts.get(&entry.predicate) else {
        return;
    };

    for (arg_idx, sort) in arg_sorts.iter().enumerate() {
        let canonical_name = format!("__p{}_a{}", entry.predicate.index(), arg_idx);
        if let Some(value) = entry.instances.get_mut(&canonical_name) {
            *value = concretize_smt_value(value, sort);
        }
    }
}

fn concretize_smt_value(value: &SmtValue, sort: &ChcSort) -> SmtValue {
    match (sort, value) {
        (ChcSort::BitVec(width), SmtValue::Int(n)) => {
            SmtValue::BitVec(int_to_bitvec_bits(*n, *width), *width)
        }
        (ChcSort::BitVec(width), SmtValue::BitVec(bits, actual_width)) if width == actual_width => {
            SmtValue::BitVec(*bits, *width)
        }
        (ChcSort::BitVec(width), SmtValue::BitVec(bits, _)) => {
            SmtValue::BitVec(mask_bitvec_bits(*bits, *width), *width)
        }
        (ChcSort::Array(_index_sort, element_sort), SmtValue::ConstArray(default)) => {
            SmtValue::ConstArray(Box::new(concretize_smt_value(
                default,
                element_sort.as_ref(),
            )))
        }
        (ChcSort::Array(index_sort, element_sort), SmtValue::ArrayMap { default, entries }) => {
            let translated_entries = entries
                .iter()
                .map(|(idx, val)| {
                    (
                        concretize_smt_value(idx, index_sort.as_ref()),
                        concretize_smt_value(val, element_sort.as_ref()),
                    )
                })
                .collect();
            SmtValue::ArrayMap {
                default: Box::new(concretize_smt_value(default, element_sort.as_ref())),
                entries: translated_entries,
            }
        }
        _ => value.clone(),
    }
}

fn int_to_bitvec_bits(value: i128, width: u32) -> u128 {
    if width >= 128 {
        // Two's-complement reinterpretation: the standard 128-bit bitvector
        // encoding of a signed value (bijective, not a truncation).
        value as u128
    } else {
        let modulus = 1i128 << width;
        (value.rem_euclid(modulus)) as u128
    }
}

fn mask_bitvec_bits(value: u128, width: u32) -> u128 {
    if width >= 128 {
        value
    } else {
        value & ((1u128 << width) - 1)
    }
}
