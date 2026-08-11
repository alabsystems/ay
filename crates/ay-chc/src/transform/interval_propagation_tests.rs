// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tests for the WORD-BV interval propagation pass (item #8).

use super::*;
use crate::transform::Transformer;
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

fn int_var(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::Int)
}

fn bool_var(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::Bool)
}

/// `x = 0; while (x < 6) x++`, the shape whose upper bound needs one join more
/// than [`WIDENING_THRESHOLD`] allows.
///
/// With `side` set, the step clause also carries a Bool-only body predicate:
/// reached, but with no interval information on any argument.
fn counting_loop_problem(side: Option<&str>) -> (ChcProblem, crate::PredicateId) {
    let mut p = ChcProblem::new();
    let inv = p.declare_predicate("inv", vec![ChcSort::Int]);
    let x = int_var("x");
    let mut body_predicates = vec![(inv, vec![ChcExpr::var(x.clone())])];
    if let Some(side) = side {
        let flag = bool_var("flag");
        let side_pid = p.declare_predicate(side, vec![ChcSort::Bool]);
        p.add_clause(HornClause::new(
            ClauseBody::new(vec![], None),
            ClauseHead::Predicate(side_pid, vec![ChcExpr::var(flag.clone())]),
        ));
        body_predicates.push((side_pid, vec![ChcExpr::var(flag)]));
    }
    p.add_clause(HornClause::new(
        ClauseBody::new(
            vec![],
            Some(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    p.add_clause(HornClause::new(
        ClauseBody::new(
            body_predicates,
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(6))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    (p, inv)
}

/// `(x + 1) mod 256` — the shape BvToInt emits for `bvadd x 1` on BV8.
fn wrap_add_one(x: &ChcVar) -> ChcExpr {
    ChcExpr::mod_op(
        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ChcExpr::int(256),
    )
}

fn expr_contains_mod(expr: &ChcExpr) -> bool {
    match expr {
        ChcExpr::Op(op, args) => *op == ChcOp::Mod || args.iter().any(|a| expr_contains_mod(a)),
        ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            args.iter().any(|a| expr_contains_mod(a))
        }
        ChcExpr::ConstArray(_, val) => expr_contains_mod(val),
        _ => false,
    }
}

fn clause_contains_mod(clause: &HornClause) -> bool {
    let in_constraint = clause
        .body
        .constraint
        .as_ref()
        .is_some_and(expr_contains_mod);
    let in_head = match &clause.head {
        ClauseHead::Predicate(_, args) => args.iter().any(expr_contains_mod),
        ClauseHead::False => false,
    };
    in_constraint || in_head
}

/// Bounded counter (post-BvToInt shape): init x=0; step guarded by x < 10
/// wraps at 256. The guard proves no wraparound, so the pass must discharge
/// the `mod 256` cast.
fn bounded_counter_problem() -> (ChcProblem, crate::PredicateId) {
    let mut p = ChcProblem::new();
    let inv = p.declare_predicate("inv", vec![ChcSort::Int]);
    let x = int_var("x");
    // Fact: x = 0 ∧ 0 <= x < 256 ⇒ inv(x)   (range constraint as BvToInt emits)
    p.add_clause(HornClause::new(
        ClauseBody::new(
            vec![],
            Some(ChcExpr::and_all([
                ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
                ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
                ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(256)),
            ])),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    // Step: inv(x) ∧ x < 10 ∧ 0 <= x < 256 ⇒ inv((x+1) mod 256)
    p.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::and_all([
                ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10)),
                ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
                ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(256)),
            ])),
        ),
        ClauseHead::Predicate(inv, vec![wrap_add_one(&x)]),
    ));
    (p, inv)
}

/// Free-running wraparound counter: init x=0; step wraps at 256 with NO
/// guard. x = 255 → (x+1) mod 256 = 0, so wraparound IS reachable and the
/// cast must be kept. A naive rewrite (drop mod without the SMT proof) would
/// let x grow unboundedly and flip the verdict of the safety query below.
fn wraparound_counter_problem() -> ChcProblem {
    let mut p = ChcProblem::new();
    let inv = p.declare_predicate("inv", vec![ChcSort::Int]);
    let x = int_var("x");
    p.add_clause(HornClause::new(
        ClauseBody::new(
            vec![],
            Some(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    // Step: inv(x) ∧ 0 <= x < 256 ⇒ inv((x+1) mod 256)
    p.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::and(
                ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
                ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(256)),
            )),
        ),
        ClauseHead::Predicate(inv, vec![wrap_add_one(&x)]),
    ));
    // Query: inv(x) ∧ x > 300 ⇒ false  (unreachable ONLY because of the mod)
    p.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(300))),
        ),
        ClauseHead::False,
    ));
    p
}

#[test]
fn discharges_mod_when_no_wraparound_is_smt_proven() {
    let (problem, _inv) = bounded_counter_problem();
    let result = Box::new(IntervalPropagator::new().with_enabled_for_test(true)).transform(problem);
    let step = &result.problem.clauses()[1];
    assert!(
        !clause_contains_mod(step),
        "guarded step must have its mod 256 cast discharged, got: {:?}",
        step
    );
    // The discharged clause must keep the proven bound atoms (equivalence).
    let constraint = step.body.constraint.as_ref().expect("constraint");
    let rendered = format!("{constraint}");
    assert!(
        rendered.contains("256"),
        "proven no-wraparound bounds must be conjoined: {rendered}"
    );
}

/// SOUNDNESS PIN: a naive interval pass that rewrites `(x+1) mod 256 -> x+1`
/// without the SMT no-wraparound proof would make `x > 300` reachable and
/// flip a SAT (safe) instance to UNSAT (unsafe). Our pass must keep the cast.
#[test]
fn keeps_mod_when_wraparound_is_reachable() {
    let problem = wraparound_counter_problem();
    let result = Box::new(IntervalPropagator::new().with_enabled_for_test(true)).transform(problem);
    let step = &result.problem.clauses()[1];
    assert!(
        clause_contains_mod(step),
        "unguarded wraparound step must KEEP its mod 256 cast, got: {:?}",
        step
    );
}

#[test]
fn kill_switch_disables_the_pass() {
    let (problem, _) = bounded_counter_problem();
    let result =
        Box::new(IntervalPropagator::new().with_enabled_for_test(false)).transform(problem.clone());
    // Identity: clauses unchanged, identity back-translation.
    assert_eq!(
        format!("{:?}", result.problem.clauses()),
        format!("{:?}", problem.clauses()),
        "disabled pass must leave the problem untouched"
    );
    assert_eq!(
        result.back_translator.transform_memory().transform(),
        "identity"
    );
}

#[test]
fn back_translation_conjoins_verified_interval_atoms() {
    let (problem, inv) = bounded_counter_problem();
    let result = Box::new(IntervalPropagator::new().with_enabled_for_test(true)).transform(problem);

    // Simulate a solver model: inv(x) := x <= 11 over the transformed system.
    let mut model = InvariantModel::new();
    let x = int_var("x");
    model.set(
        inv,
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(11)),
        ),
    );
    let translated = result.back_translator.translate_validity(model);
    let interp = translated.get(&inv).expect("inv interpreted");
    let rendered = format!("{}", interp.formula);
    // The original conjunct must be preserved.
    assert!(
        rendered.contains("11"),
        "original model formula must be preserved: {rendered}"
    );
    // The verified lower bound (x >= 0 survives widening) must be conjoined.
    assert!(
        rendered.contains("0"),
        "verified interval atoms must be conjoined onto the model: {rendered}"
    );
}

#[test]
fn unsafe_witness_translation_is_identity() {
    let (problem, _) = bounded_counter_problem();
    let result = Box::new(IntervalPropagator::new().with_enabled_for_test(true)).transform(problem);
    let cex = crate::Counterexample::new(vec![]);
    let translated = result.back_translator.translate_invalidity(cex.clone());
    assert!(translated.steps.is_empty());
    assert!(translated.witness.is_none());
}

#[test]
fn transform_memory_records_g1_obligations() {
    let (problem, _) = bounded_counter_problem();
    let result = Box::new(IntervalPropagator::new().with_enabled_for_test(true)).transform(problem);
    let memory = result.back_translator.transform_memory();
    assert_eq!(memory.transform(), "interval_prop");
    assert!(memory.safe_requires_original_validation());
    assert!(memory.unsafe_backtranslation_complete());
    assert!(memory.has_obligation("interval-invariant-model-conjunction"));
}

// ── Interval domain unit tests ─────────────────────────────────────────────

#[test]
fn interval_arithmetic_basics() {
    let a = Interval {
        lo: Some(BigInt::from(0)),
        hi: Some(BigInt::from(10)),
    };
    let b = Interval {
        lo: Some(BigInt::from(-3)),
        hi: Some(BigInt::from(5)),
    };
    let sum = a.add(&b);
    assert_eq!(sum.lo, Some(BigInt::from(-3)));
    assert_eq!(sum.hi, Some(BigInt::from(15)));

    let diff = a.sub(&b);
    assert_eq!(diff.lo, Some(BigInt::from(-5)));
    assert_eq!(diff.hi, Some(BigInt::from(13)));

    let prod = a.mul(&b);
    assert_eq!(prod.lo, Some(BigInt::from(-30)));
    assert_eq!(prod.hi, Some(BigInt::from(50)));

    // In-range mod is the identity on the interval.
    let m = a.mod_const(&BigInt::from(256));
    assert_eq!(m, a);
    // Out-of-range (possibly negative) mod clamps to [0, m-1].
    let m2 = b.mod_const(&BigInt::from(256));
    assert_eq!(m2.lo, Some(BigInt::from(0)));
    assert_eq!(m2.hi, Some(BigInt::from(255)));

    // Join is the hull, meet the intersection.
    let j = a.join(&b);
    assert_eq!(j.lo, Some(BigInt::from(-3)));
    assert_eq!(j.hi, Some(BigInt::from(10)));
    let mt = a.meet(&b);
    assert_eq!(mt.lo, Some(BigInt::from(0)));
    assert_eq!(mt.hi, Some(BigInt::from(5)));
}

#[test]
fn forward_fixpoint_widens_after_threshold() {
    // Unguarded increment: hi keeps moving and must be widened to +inf while
    // lo stays at 0.
    let mut p = ChcProblem::new();
    let inv = p.declare_predicate("inv", vec![ChcSort::Int]);
    let x = int_var("x");
    p.add_clause(HornClause::new(
        ClauseBody::new(
            vec![],
            Some(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    p.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    let state = forward_fixpoint(&p);
    let intervals = state.get(&inv).expect("inv tracked");
    assert_eq!(intervals[0].lo, Some(BigInt::from(0)), "lo must stay 0");
    assert_eq!(intervals[0].hi, None, "hi must be widened to +inf");
}

/// Compiler front ends put every arithmetic fact under a guard literal. The
/// analysis has to unit-propagate the decided guards before it can see the
/// assignment at all, or it derives nothing on a whole benchmark family.
#[test]
fn guarded_cnf_assignment_is_unit_propagated() {
    let mut p = ChcProblem::new();
    let inv = p.declare_predicate("inv", vec![ChcSort::Int]);
    let x = int_var("x");
    let g = bool_var("g");
    // g ∧ (¬g ∨ x = 0) ⇒ inv(x): the disjunction is unit under g.
    p.add_clause(HornClause::new(
        ClauseBody::new(
            vec![],
            Some(ChcExpr::and(
                ChcExpr::var(g.clone()),
                ChcExpr::or(
                    ChcExpr::not(ChcExpr::var(g.clone())),
                    ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
                ),
            )),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    let state = forward_fixpoint(&p);
    let intervals = state.get(&inv).expect("inv tracked");
    assert_eq!(
        (intervals[0].lo.clone(), intervals[0].hi.clone()),
        (Some(BigInt::from(0)), Some(BigInt::from(0))),
        "the guarded assignment x = 0 must be read through the unit clause"
    );
}

/// The other half of the guarded-CNF encoding: loop conditions are reified
/// into a Boolean variable (`(not (= (<= 6 h) a))` with `a` a decided unit),
/// which forces the comparison to be FALSE and so bounds `h` from above.
#[test]
fn reified_loop_guard_bounds_the_counter() {
    let mut p = ChcProblem::new();
    let inv = p.declare_predicate("inv", vec![ChcSort::Int]);
    let h = int_var("h");
    let a = bool_var("a");
    // a ∧ ¬((6 <= h) = a) ⇒ inv(h), i.e. ¬(6 <= h), i.e. h <= 5.
    p.add_clause(HornClause::new(
        ClauseBody::new(
            vec![],
            Some(ChcExpr::and(
                ChcExpr::var(a.clone()),
                ChcExpr::not(ChcExpr::eq(
                    ChcExpr::le(ChcExpr::int(6), ChcExpr::var(h.clone())),
                    ChcExpr::var(a.clone()),
                )),
            )),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(h.clone())]),
    ));
    let state = forward_fixpoint(&p);
    let intervals = state.get(&inv).expect("inv tracked");
    assert_eq!(
        intervals[0].hi,
        Some(BigInt::from(5)),
        "the reified guard must bound the counter by 5"
    );
}

/// SOUNDNESS PIN for the negation handling: `¬(x = c)` is NOT an interval
/// fact, so a negated equality must leave the environment untouched rather
/// than be approximated in either direction.
#[test]
fn negated_equality_yields_no_interval() {
    let mut p = ChcProblem::new();
    let inv = p.declare_predicate("inv", vec![ChcSort::Int]);
    let x = int_var("x");
    p.add_clause(HornClause::new(
        ClauseBody::new(
            vec![],
            Some(ChcExpr::not(ChcExpr::eq(
                ChcExpr::var(x.clone()),
                ChcExpr::int(7),
            ))),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    let state = forward_fixpoint(&p);
    let intervals = state.get(&inv).expect("inv tracked");
    assert!(
        intervals[0].is_top(),
        "x != 7 must stay top, got {:?}",
        intervals[0]
    );
}

/// A guarded counting loop needs exactly one more join than the widening
/// threshold allows, so widening straight to ±∞ forgets its bound just before
/// convergence. Climbing the ladder of constants that occur in the problem
/// keeps it.
#[test]
fn landmark_widening_keeps_a_bounded_loop_bound() {
    let (problem, inv) = counting_loop_problem(None);
    let state = forward_fixpoint(&problem);
    let intervals = state.get(&inv).expect("inv tracked");
    assert_eq!(intervals[0].lo, Some(BigInt::from(0)), "lo must stay 0");
    assert_eq!(
        intervals[0].hi,
        Some(BigInt::from(6)),
        "hi must widen to the landmark 6, not to +inf"
    );
}

/// REGRESSION: the narrowing pass reads "absent from the state" as "body not
/// reached" and skips the clause. A predicate whose arguments are all top
/// (here a Bool-only side condition) carries no interval information but is
/// still reached, so dropping it before narrowing hides the step clause and
/// narrows `inv` past its real fixpoint down to the initial value.
#[test]
fn all_top_predicate_does_not_hide_clauses_from_narrowing() {
    let (problem, inv) = counting_loop_problem(Some("side"));
    let state = narrowed_fixpoint(&problem);
    let intervals = state.get(&inv).expect("inv tracked");
    assert_eq!(
        (intervals[0].lo.clone(), intervals[0].hi.clone()),
        (Some(BigInt::from(0)), Some(BigInt::from(6))),
        "the all-top side predicate must not remove the step clause from the abstract image"
    );
}

#[test]
fn const_bigint_folds_pow2_trees() {
    // 2^64 as emitted by bv_to_int::ops::int_pow2: 2^32 * 2^32.
    let tree = ChcExpr::mul(
        ChcExpr::int(1i64 << 32),
        ChcExpr::mul(ChcExpr::int(1i64 << 32), ChcExpr::int(1)),
    );
    assert_eq!(const_bigint(&tree), Some(BigInt::from(1u128 << 64)));
}

/// The HCAI `lu.cmp` benchmark, vendored verbatim from CHC-COMP 2025; see
/// `crates/ay-chc/tests/fixtures/chc_comp/README.md`.
const HCAI_LU_CMP: &str = include_str!(
    "../../tests/fixtures/chc_comp/hcai/svcomp/O0/O0_lu.cmp_true-unreach-call_000.smt2"
);

/// Guarded CNF from a real SeaHorn frontend must yield its loop-counter bounds.
///
/// This is the capability `70c7b90c9` added, pinned on the benchmark that
/// motivated it. Before that commit `IntervalPropagator` had no Boolean
/// reasoning: every arithmetic fact in `lu.cmp` sits under a guard disjunct
/// (`(or (not g) (= x 0))`) with loop bounds expressed as reified comparisons
/// (`(not (= (<= 6 h) g))` conjoined with a unit literal), so the pass derived
/// no bound at all and the reduced LIA-array route returned `None`.
///
/// Asserted at the PASS level deliberately. The end-to-end route verdict is a
/// wall-clock-budgeted property — the route clamps itself to
/// `REDUCED_LIA_ARRAY_ROUTE_BUDGET` minus ~1.5s of reserves — so asserting it
/// inside a 4000-test parallel suite makes a completeness claim hostage to
/// machine load. The abstract invariant below is the capability itself, and it
/// is stable: ~80ms unloaded and ~180ms against 24 saturated cores, against the
/// pass's 8s budget.
#[test]
fn guarded_cnf_yields_lu_cmp_loop_counter_bounds() {
    let problem = crate::parser::ChcParser::parse(HCAI_LU_CMP).expect("lu.cmp should parse");
    let summary = crate::portfolio::PreprocessSummary::build(problem, false);
    let transformed = &summary.transformed_problem;
    let state = narrowed_fixpoint(transformed);

    let bound_for = |needle: &str| -> Option<Interval> {
        let predicate = transformed
            .predicates()
            .iter()
            .find(|p| p.name.contains(needle))?;
        state
            .get(&predicate.id)
            .and_then(|args| args.get(1).cloned())
    };

    // The outer loop guard `(not (= (<= 6 h) g))` with unit `g` bounds the
    // counter; the body increments it once more before the guard is re-tested.
    assert_eq!(
        bound_for("main@_bb2"),
        Some(Interval {
            lo: Some(0.into()),
            hi: Some(6.into())
        }),
        "lu.cmp main@_bb2 arg1 must be bounded [0,6]; state: {state:?}"
    );
    assert_eq!(
        bound_for("main@_bb"),
        Some(Interval {
            lo: Some(0.into()),
            hi: Some(7.into())
        }),
        "lu.cmp main@_bb arg1 must be bounded [0,7]; state: {state:?}"
    );
}
