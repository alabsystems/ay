// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the DPLL(T) difference-logic theory solver
//! (`executor::dl_theory`) and the `QF_RDL` route that drives it.
//!
//! The highest-risk part of the solver is the **negation** lowering: over the
//! rationals `not (x − y <= c)` is `x − y > c`, i.e. the edge `x → y` with
//! weight `(−c, −1)`. These tests pin every polarity of every operator by
//! asserting a literal and a second literal that contradicts exactly the
//! intended half-plane, then requiring a conflict (or requiring NO conflict for
//! the consistent variants).

use ay_core::{Sort, Symbol, TermId, TermStore, TheoryLit, TheoryResult, TheorySolver};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;

use super::Executor;
use ay_diff_logic::RStar;

/// The theory solver is generic over its weight representation (`RStar` exact
/// rationals vs the `IStar` i128 fast lane). These tests use exact rationals —
/// the lane the router picks whenever a constant is not a small integer, and
/// the one whose edge weights the hand-written expectations below spell out.
/// The `IStar` lane is covered by the engine's own tests in `ay-diff-logic`.
type DiffLogicTheory<'a> = super::dl_theory::DiffLogicTheory<'a, RStar>;
use ay_frontend::parse;

/// Two Real variables plus the integer constants used by the tests.
struct Fx {
    terms: TermStore,
    x: TermId,
    y: TermId,
}

impl Fx {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let y = terms.mk_var("y", Sort::Real);
        Self { terms, x, y }
    }

    /// A Real-sorted numeric constant (`mk_le` & friends require both sides to
    /// share a sort, and these tests are QF_RDL).
    fn real(&mut self, n: i64) -> TermId {
        self.terms.mk_rational(BigRational::from(BigInt::from(n)))
    }

    /// `x − y`
    fn diff(&mut self) -> TermId {
        let (x, y) = (self.x, self.y);
        self.terms.mk_sub(vec![x, y])
    }
}

/// Assert `lits` into a fresh theory and return the `check()` verdict.
fn verdict(fx: &Fx, lits: &[(TermId, bool)]) -> TheoryResult {
    let mut th = DiffLogicTheory::new(&fx.terms);
    for &(t, v) in lits {
        th.assert_literal(t, v);
    }
    th.check()
}

fn is_unsat(r: &TheoryResult) -> bool {
    matches!(r, TheoryResult::Unsat(lits) if !lits.is_empty())
}

fn is_sat(r: &TheoryResult) -> bool {
    matches!(r, TheoryResult::Sat)
}

fn is_unknown(r: &TheoryResult) -> bool {
    matches!(r, TheoryResult::Unknown)
}

// ---------------------------------------------------------------------------
// Negation lowering, one test per operator
// ---------------------------------------------------------------------------

#[test]
fn not_le_is_strict_greater_than() {
    // not (x − y <= 3)  ⇔  x − y > 3.  Together with x − y <= 0: UNSAT.
    let mut fx = Fx::new();
    let d = fx.diff();
    let three = fx.real(3);
    let zero = fx.real(0);
    let le3 = fx.terms.mk_le(d, three);
    let le0 = fx.terms.mk_le(d, zero);

    assert!(is_unsat(&verdict(&fx, &[(le3, false), (le0, true)])));
    // ... and x − y > 3 alone is perfectly satisfiable.
    assert!(is_sat(&verdict(&fx, &[(le3, false)])));
    // x − y > 3 is NOT contradicted by x − y <= 4.
    let four = fx.real(4);
    let le4 = fx.terms.mk_le(d, four);
    assert!(is_sat(&verdict(&fx, &[(le3, false), (le4, true)])));
}

#[test]
fn not_lt_is_non_strict_ge() {
    // not (x − y < 3)  ⇔  x − y >= 3.  It must NOT exclude x − y = 3, so
    // pairing it with x − y <= 3 stays SAT, while x − y < 3 conflicts.
    let mut fx = Fx::new();
    let d = fx.diff();
    let three = fx.real(3);
    let lt3 = fx.terms.mk_lt(d, three);
    let le3 = fx.terms.mk_le(d, three);

    assert!(is_sat(&verdict(&fx, &[(lt3, false), (le3, true)])));
    assert!(is_unsat(&verdict(&fx, &[(lt3, false), (lt3, true)])));
}

#[test]
fn not_ge_is_strict_less_than() {
    // not (x − y >= 3)  ⇔  x − y < 3.  Contradicts x − y >= 3 exactly.
    let mut fx = Fx::new();
    let d = fx.diff();
    let three = fx.real(3);
    let ge3 = fx.terms.mk_ge(d, three);
    let two = fx.real(2);
    let ge2 = fx.terms.mk_ge(d, two);

    assert!(is_unsat(&verdict(&fx, &[(ge3, false), (ge3, true)])));
    // x − y < 3 and x − y >= 2 is satisfiable (2 <= x−y < 3).
    assert!(is_sat(&verdict(&fx, &[(ge3, false), (ge2, true)])));
}

#[test]
fn not_gt_is_non_strict_le() {
    // not (x − y > 3)  ⇔  x − y <= 3, which must still ALLOW x − y = 3.
    let mut fx = Fx::new();
    let d = fx.diff();
    let three = fx.real(3);
    let gt3 = fx.terms.mk_gt(d, three);
    let ge3 = fx.terms.mk_ge(d, three);
    let gt2 = fx.terms.mk_gt(d, three);

    assert!(is_sat(&verdict(&fx, &[(gt3, false), (ge3, true)])));
    assert!(is_unsat(&verdict(&fx, &[(gt3, false), (gt2, true)])));
}

// ---------------------------------------------------------------------------
// Rational strictness (the ε machinery)
// ---------------------------------------------------------------------------

#[test]
fn strict_cycle_is_unsat_via_epsilon() {
    // x < y ∧ y < x. Both rational parts are 0; only the ε-count makes the
    // cycle negative. This is the test that fails if `<` is lowered as `<=`.
    let mut fx = Fx::new();
    let (x, y) = (fx.x, fx.y);
    let x_lt_y = fx.terms.mk_lt(x, y);
    let y_lt_x = fx.terms.mk_lt(y, x);
    assert!(is_unsat(&verdict(&fx, &[(x_lt_y, true), (y_lt_x, true)])));
}

#[test]
fn non_strict_cycle_is_sat() {
    // x <= y ∧ y <= x forces x = y — satisfiable, and must NOT be reported as
    // a negative cycle (the ε-counts are 0 here).
    let mut fx = Fx::new();
    let (x, y) = (fx.x, fx.y);
    let x_le_y = fx.terms.mk_le(x, y);
    let y_le_x = fx.terms.mk_le(y, x);
    assert!(is_sat(&verdict(&fx, &[(x_le_y, true), (y_le_x, true)])));
}

#[test]
fn var_vs_const_uses_the_zero_vertex() {
    // x <= 1 ∧ x >= 2 is UNSAT and exercises the implicit zero variable (both
    // atoms are var-vs-const, so the cycle runs through Z).
    let mut fx = Fx::new();
    let x = fx.x;
    let one = fx.real(1);
    let two = fx.real(2);
    let x_le_1 = fx.terms.mk_le(x, one);
    let x_ge_2 = fx.terms.mk_ge(x, two);
    assert!(is_unsat(&verdict(&fx, &[(x_le_1, true), (x_ge_2, true)])));
    assert!(is_sat(&verdict(&fx, &[(x_le_1, true)])));
}

// ---------------------------------------------------------------------------
// Conflict shape
// ---------------------------------------------------------------------------

#[test]
fn conflict_names_the_asserted_literals() {
    let mut fx = Fx::new();
    let (x, y) = (fx.x, fx.y);
    let x_lt_y = fx.terms.mk_lt(x, y);
    let y_lt_x = fx.terms.mk_lt(y, x);
    let TheoryResult::Unsat(lits) = verdict(&fx, &[(x_lt_y, true), (y_lt_x, true)]) else {
        panic!("expected Unsat");
    };
    // Non-empty, duplicate-free, and every literal is one we asserted with the
    // polarity we asserted it at (the DPLL layer negates these verbatim).
    assert!(!lits.is_empty());
    let mut sorted = lits.clone();
    sorted.sort_unstable();
    sorted.dedup();
    assert_eq!(sorted.len(), lits.len(), "conflict has duplicate literals");
    for lit in &lits {
        assert!(
            *lit == TheoryLit::new(x_lt_y, true) || *lit == TheoryLit::new(y_lt_x, true),
            "conflict names a literal that was never asserted: {lit:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// push / pop
// ---------------------------------------------------------------------------

#[test]
fn pop_retracts_the_conflict() {
    let mut fx = Fx::new();
    let (x, y) = (fx.x, fx.y);
    let x_lt_y = fx.terms.mk_lt(x, y);
    let y_lt_x = fx.terms.mk_lt(y, x);

    let mut th = DiffLogicTheory::new(&fx.terms);
    th.assert_literal(x_lt_y, true);
    assert!(is_sat(&th.check()));

    th.push();
    th.assert_literal(y_lt_x, true);
    assert!(is_unsat(&th.check()));

    th.pop();
    // Behavioral equivalence: identical to never having asserted y < x.
    assert!(is_sat(&th.check()));

    // ... and the retracted literal can be re-asserted, re-deriving the conflict.
    th.push();
    th.assert_literal(y_lt_x, true);
    assert!(is_unsat(&th.check()));
}

#[test]
fn nested_push_pop_restores_the_base_scope() {
    let mut fx = Fx::new();
    let (x, y) = (fx.x, fx.y);
    let x_le_y = fx.terms.mk_le(x, y);
    let y_lt_x = fx.terms.mk_lt(y, x);

    let mut th = DiffLogicTheory::new(&fx.terms);
    th.push();
    th.push();
    th.assert_literal(x_le_y, true);
    th.assert_literal(y_lt_x, true);
    assert!(is_unsat(&th.check()));
    th.pop();
    th.pop();
    assert!(is_sat(&th.check()));
    // Unmatched pops are a no-op, not a panic.
    th.pop();
    assert!(is_sat(&th.check()));
}

#[test]
fn reset_clears_every_assertion() {
    let mut fx = Fx::new();
    let (x, y) = (fx.x, fx.y);
    let x_lt_y = fx.terms.mk_lt(x, y);
    let y_lt_x = fx.terms.mk_lt(y, x);

    let mut th = DiffLogicTheory::new(&fx.terms);
    th.assert_literal(x_lt_y, true);
    th.assert_literal(y_lt_x, true);
    assert!(is_unsat(&th.check()));
    th.reset();
    assert!(is_sat(&th.check()));
    th.assert_literal(x_lt_y, true);
    assert!(is_sat(&th.check()));
}

// ---------------------------------------------------------------------------
// Fail-closed behaviour
// ---------------------------------------------------------------------------

#[test]
fn non_difference_atom_is_unknown_not_approximated() {
    // x + y <= 3 is linear but NOT a difference atom. The solver must refuse it
    // rather than drop or approximate the constraint.
    let mut fx = Fx::new();
    let (x, y) = (fx.x, fx.y);
    let sum = fx.terms.mk_add(vec![x, y]);
    let three = fx.real(3);
    let bad = fx.terms.mk_le(sum, three);
    assert!(is_unknown(&verdict(&fx, &[(bad, true)])));
}

#[test]
fn negated_arithmetic_equality_is_unknown() {
    // not (x = y) is the DISJUNCTION x < y ∨ x > y, not a difference
    // constraint. Refuse rather than silently ignore it.
    let mut fx = Fx::new();
    let (x, y) = (fx.x, fx.y);
    let eq = fx.terms.mk_eq(x, y);
    assert!(is_unknown(&verdict(&fx, &[(eq, false)])));
    // The POSITIVE polarity is two difference constraints and is supported.
    let x_lt_y = fx.terms.mk_lt(x, y);
    assert!(is_unsat(&verdict(&fx, &[(eq, true), (x_lt_y, true)])));
}

#[test]
fn boolean_atoms_are_ignored_not_refused() {
    // A Boolean equality carries no arithmetic content; the Tseitin encoder
    // constrains it structurally, so the theory ignores it.
    let mut fx = Fx::new();
    let p = fx.terms.mk_var("p", Sort::Bool);
    let q = fx.terms.mk_var("q", Sort::Bool);
    let iff = fx.terms.mk_eq(p, q);
    assert!(is_sat(&verdict(&fx, &[(iff, true)])));
    assert!(is_sat(&verdict(&fx, &[(iff, false)])));
}

#[test]
fn integer_variables_are_refused() {
    // Int-sorted differences need the integer-tightened lowering; the rational
    // lowering would only be a relaxation, so this lane refuses them.
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let lt = terms.mk_lt(i, j);
    let mut th = DiffLogicTheory::new(&terms);
    th.assert_literal(lt, true);
    assert!(is_unknown(&th.check()));
}

#[test]
fn wrapped_not_literal_is_normalised() {
    // The DPLL layer may hand over `(not atom)` with value `true`; that is the
    // same as `atom` with value `false`.
    let mut fx = Fx::new();
    let d = fx.diff();
    let zero = fx.real(0);
    let le0 = fx.terms.mk_le(d, zero);
    let not_le0 = fx.terms.mk_not_raw(le0);
    // not (x − y <= 0) ∧ (x − y <= 0)  ⇒  UNSAT.
    assert!(is_unsat(&verdict(&fx, &[(not_le0, true), (le0, true)])));
}

// ---------------------------------------------------------------------------
// Model extraction
// ---------------------------------------------------------------------------

#[test]
fn extracted_model_satisfies_strict_constraints() {
    // x < y ∧ y < z ∧ z <= x + 5 (as z − x <= 5). The realised rational model
    // must keep both strict inequalities strict.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let x_lt_y = terms.mk_lt(x, y);
    let y_lt_z = terms.mk_lt(y, z);
    let zx = terms.mk_sub(vec![z, x]);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let zx_le_5 = terms.mk_le(zx, five);

    let mut th = DiffLogicTheory::new(&terms);
    th.assert_literal(x_lt_y, true);
    th.assert_literal(y_lt_z, true);
    th.assert_literal(zx_le_5, true);
    assert!(is_sat(&th.check()));

    let model = th.extract_model();
    let get = |t| {
        model
            .values
            .get(&t)
            .cloned()
            .unwrap_or_else(BigRational::zero)
    };
    let (vx, vy, vz) = (get(x), get(y), get(z));
    assert!(vx < vy, "x < y violated: {vx} !< {vy}");
    assert!(vy < vz, "y < z violated: {vy} !< {vz}");
    assert!(
        &vz - &vx <= BigRational::from(BigInt::from(5)),
        "z − x <= 5 violated"
    );
}

// ---------------------------------------------------------------------------
// End-to-end through the QF_RDL route
// ---------------------------------------------------------------------------

fn run(script: &str) -> Vec<String> {
    let cmds = parse(script).expect("parse");
    let mut exec = Executor::new();
    exec.execute_all(&cmds).expect("execute")
}

fn last_verdict(script: &str) -> String {
    run(script)
        .into_iter()
        .rfind(|o| matches!(o.trim(), "sat" | "unsat" | "unknown"))
        .expect("a check-sat verdict")
        .trim()
        .to_string()
}

#[test]
fn rdl_route_unsat_negative_cycle() {
    let verdict = last_verdict(
        "(set-logic QF_RDL)
         (declare-fun x () Real)
         (declare-fun y () Real)
         (declare-fun z () Real)
         (assert (< (- x y) 0))
         (assert (< (- y z) 0))
         (assert (< (- z x) 0))
         (check-sat)",
    );
    assert_eq!(verdict, "unsat");
}

#[test]
fn rdl_route_sat_with_boolean_structure() {
    let verdict = last_verdict(
        "(set-logic QF_RDL)
         (declare-fun x () Real)
         (declare-fun y () Real)
         (assert (or (<= (- x y) (- 5)) (>= (- x y) 5)))
         (assert (<= (- x y) 0))
         (check-sat)",
    );
    assert_eq!(verdict, "sat");
}

#[test]
fn rdl_route_unsat_through_boolean_structure() {
    let verdict = last_verdict(
        "(set-logic QF_RDL)
         (declare-fun x () Real)
         (declare-fun y () Real)
         (assert (or (< (- x y) (- 5)) (> (- x y) 5)))
         (assert (<= (- x y) 1))
         (assert (>= (- x y) (- 1)))
         (check-sat)",
    );
    assert_eq!(verdict, "unsat");
}

#[test]
fn non_dl_qf_rdl_instance_falls_through_to_simplex() {
    // `x + y <= 3` is not difference logic; the route must delegate to
    // `solve_lra` and still return the right answer.
    let verdict = last_verdict(
        "(set-logic QF_RDL)
         (declare-fun x () Real)
         (declare-fun y () Real)
         (assert (<= (+ x y) 3))
         (assert (>= (+ x y) 4))
         (check-sat)",
    );
    assert_eq!(verdict, "unsat");
}

#[test]
fn qf_rdl_with_negated_equality_still_answers() {
    // The negated equality makes the DL theory answer `Unknown`; the route must
    // then fall back to `solve_lra` rather than propagate the `unknown`.
    let verdict = last_verdict(
        "(set-logic QF_RDL)
         (declare-fun x () Real)
         (declare-fun y () Real)
         (assert (not (= x y)))
         (assert (<= (- x y) 0))
         (assert (>= (- x y) 0))
         (check-sat)",
    );
    assert_eq!(verdict, "unsat");
}

// ===========================================================================
// EXHAUSTIVE ATOM-LOWERING / NEGATION AUDIT
//
// The lowering table lives in `ay_diff_logic::atom` (see the RDL table at
// atom.rs:47-53) and the negation is `negate_op` composed with it. A single
// wrong entry silently flips a SAT into an UNSAT (or worse), so every
// operator is pinned twice: once against the exact edge triple the engine
// receives, and once behaviourally against every other half-plane.
//
// NOTE on term construction: `TermStore::mk_ge` / `mk_gt` NORMALISE to
// `<=` / `<` with swapped arguments, so a test written with them never
// reaches `Op::Ge` / `Op::Gt` in `collect_comparison`. These tests therefore
// build the comparison application RAW (`mk_app`), which is exactly what the
// non-parser producers in the repo do (`bound_refinement.rs`,
// `optimization.rs` both intern `>=` directly) and what `collect_comparison`
// claims to accept.
// ===========================================================================

/// The five comparison operators, in the *surface* form `collect_comparison`
/// matches on.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Cmp {
    Le,
    Lt,
    Eq,
    Ge,
    Gt,
}

const ALL_CMP: [Cmp; 5] = [Cmp::Le, Cmp::Lt, Cmp::Eq, Cmp::Ge, Cmp::Gt];

impl Cmp {
    fn sym(self) -> &'static str {
        match self {
            Cmp::Le => "<=",
            Cmp::Lt => "<",
            Cmp::Eq => "=",
            Cmp::Ge => ">=",
            Cmp::Gt => ">",
        }
    }
}

/// A closed/open bound on the difference value `d`.
#[derive(Clone, Copy, Debug)]
struct Bound {
    at: i64,
    strict: bool,
}

/// The exact half-plane (or interval) an asserted literal denotes, as a
/// hand-derived reference semantics independent of the solver.
#[derive(Clone, Copy, Debug, Default)]
struct Region {
    lo: Option<Bound>,
    hi: Option<Bound>,
}

/// Reference semantics of asserting `d ⋈ c` at polarity `value`.
///
/// `None` means the literal is NOT a conjunction of difference constraints —
/// which is true of exactly one case, `not (d = c)` — and the solver is
/// required to refuse it rather than pick a disjunct.
fn meaning(op: Cmp, c: i64, value: bool) -> Option<Region> {
    let lo = |at, strict| {
        Some(Region {
            lo: Some(Bound { at, strict }),
            hi: None,
        })
    };
    let hi = |at, strict| {
        Some(Region {
            lo: None,
            hi: Some(Bound { at, strict }),
        })
    };
    match (op, value) {
        // d <= c
        (Cmp::Le, true) => hi(c, false),
        // not (d <= c)  ⇔  d > c
        (Cmp::Le, false) => lo(c, true),
        // d < c
        (Cmp::Lt, true) => hi(c, true),
        // not (d < c)  ⇔  d >= c
        (Cmp::Lt, false) => lo(c, false),
        // d >= c
        (Cmp::Ge, true) => lo(c, false),
        // not (d >= c)  ⇔  d < c
        (Cmp::Ge, false) => hi(c, true),
        // d > c
        (Cmp::Gt, true) => lo(c, true),
        // not (d > c)  ⇔  d <= c
        (Cmp::Gt, false) => hi(c, false),
        // d = c
        (Cmp::Eq, true) => Some(Region {
            lo: Some(Bound {
                at: c,
                strict: false,
            }),
            hi: Some(Bound {
                at: c,
                strict: false,
            }),
        }),
        // not (d = c) is the DISJUNCTION d < c ∨ d > c.
        (Cmp::Eq, false) => None,
    }
}

fn tighten_lo(cur: Option<Bound>, b: Option<Bound>) -> Option<Bound> {
    match (cur, b) {
        (None, x) | (x, None) => x,
        (Some(a), Some(b)) => Some(if (b.at, b.strict) > (a.at, a.strict) {
            b
        } else {
            a
        }),
    }
}

fn tighten_hi(cur: Option<Bound>, b: Option<Bound>) -> Option<Bound> {
    match (cur, b) {
        (None, x) | (x, None) => x,
        // Smaller value wins; on a tie the STRICT bound is the tighter one.
        (Some(a), Some(b)) => Some(if (b.at, !b.strict) < (a.at, !a.strict) {
            b
        } else {
            a
        }),
    }
}

/// Is the conjunction of two reference regions satisfiable over ℚ?
fn regions_feasible(a: Region, b: Region) -> bool {
    let lo = tighten_lo(a.lo, b.lo);
    let hi = tighten_hi(a.hi, b.hi);
    match (lo, hi) {
        (Some(l), Some(h)) => l.at < h.at || (l.at == h.at && !l.strict && !h.strict),
        _ => true,
    }
}

/// Does a concrete rational `d` satisfy the region?
fn region_holds(r: Region, d: &BigRational) -> bool {
    let ok_lo = r.lo.is_none_or(|b| {
        let at = BigRational::from(BigInt::from(b.at));
        if b.strict {
            *d > at
        } else {
            *d >= at
        }
    });
    let ok_hi = r.hi.is_none_or(|b| {
        let at = BigRational::from(BigInt::from(b.at));
        if b.strict {
            *d < at
        } else {
            *d <= at
        }
    });
    ok_lo && ok_hi
}

/// Build the comparison application `(op lhs c)` WITHOUT going through
/// `mk_ge`/`mk_gt` (which rewrite to `<=`/`<`), so `Op::Ge`/`Op::Gt` really
/// reach the lowering table.
fn raw_cmp(terms: &mut TermStore, op: Cmp, lhs: TermId, c: i64) -> TermId {
    let k = terms.mk_rational(BigRational::from(BigInt::from(c)));
    terms.mk_app(Symbol::named(op.sym()), vec![lhs, k], Sort::Bool)
}

/// Fixture holding `x`, `y`, `x − y`, and every `(op, c)` comparison term for
/// both the two-variable and the var-vs-const form.
struct Table {
    terms: TermStore,
    x: TermId,
    y: TermId,
    /// `[form][op][const]` where form 0 = `x − y ⋈ c`, form 1 = `x ⋈ c`.
    t: [[[TermId; 3]; 5]; 2],
}

const CONSTS: [i64; 3] = [2, 3, 4];

impl Table {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let y = terms.mk_var("y", Sort::Real);
        let d = terms.mk_sub(vec![x, y]);
        let mut t = [[[TermId(0); 3]; 5]; 2];
        for (fi, &lhs) in [d, x].iter().enumerate() {
            for (oi, &op) in ALL_CMP.iter().enumerate() {
                for (ci, &c) in CONSTS.iter().enumerate() {
                    t[fi][oi][ci] = raw_cmp(&mut terms, op, lhs, c);
                }
            }
        }
        Self { terms, x, y, t }
    }

    fn term(&self, form: usize, op: Cmp, c: i64) -> TermId {
        let oi = ALL_CMP.iter().position(|&o| o == op).expect("op");
        let ci = CONSTS.iter().position(|&k| k == c).expect("const");
        self.t[form][oi][ci]
    }

    /// The value of the difference the `form` compares (`x − y`, or `x` which
    /// is `x − Z`), read out of an extracted model.
    fn diff_value(&self, form: usize, m: &ay_lra::LraModel) -> BigRational {
        let get = |t: TermId| m.values.get(&t).cloned().unwrap_or_else(BigRational::zero);
        if form == 0 {
            get(self.x) - get(self.y)
        } else {
            get(self.x)
        }
    }
}

// ---------------------------------------------------------------------------
// 1. Exact edge table: every operator, both polarities, both forms
// ---------------------------------------------------------------------------

/// `(from, to, q, eps)` triples for the literal `(term, value)`, with the
/// variable vertices resolved so the expectation can be written by hand.
fn edges(
    th: &mut DiffLogicTheory<'_>,
    term: TermId,
    value: bool,
) -> Option<Vec<(usize, usize, i64, i64)>> {
    th.debug_edges(term, value).map(|v| {
        v.into_iter()
            .map(|(f, t, q, e)| {
                assert!(q.is_integer(), "test constants are integral");
                (f, t, q.to_integer().try_into().expect("small"), e)
            })
            .collect()
    })
}

#[test]
fn two_var_edge_table_is_exact_for_every_operator_and_polarity() {
    let tb = Table::new();
    let mut th = DiffLogicTheory::new(&tb.terms);
    // Force interning through the `<=` atom so x and y have stable vertices.
    let _ = th.debug_edges(tb.term(0, Cmp::Le, 3), true);
    let xv = th.debug_vertex(tb.x).expect("x interned");
    let yv = th.debug_vertex(tb.y).expect("y interned");
    assert_ne!(xv, DiffLogicTheory::debug_zero_vertex());
    assert_ne!(yv, DiffLogicTheory::debug_zero_vertex());

    // `from → to : (q, eps)` means `π(to) − π(from) <= q + eps·ε`.
    // Reference table for `x − y ⋈ 3` (atom.rs:47-53 plus `negate_op`).
    let cases: [(Cmp, bool, Vec<(usize, usize, i64, i64)>); 9] = [
        // x − y <= 3            ⇒  x − y <= 3
        (Cmp::Le, true, vec![(yv, xv, 3, 0)]),
        // not (x − y <= 3)      ⇒  x − y > 3  ⇒  y − x <= −3 − ε
        (Cmp::Le, false, vec![(xv, yv, -3, -1)]),
        // x − y < 3             ⇒  x − y <= 3 − ε
        (Cmp::Lt, true, vec![(yv, xv, 3, -1)]),
        // not (x − y < 3)       ⇒  x − y >= 3  ⇒  y − x <= −3
        (Cmp::Lt, false, vec![(xv, yv, -3, 0)]),
        // x − y >= 3            ⇒  y − x <= −3
        (Cmp::Ge, true, vec![(xv, yv, -3, 0)]),
        // not (x − y >= 3)      ⇒  x − y < 3  ⇒  x − y <= 3 − ε
        (Cmp::Ge, false, vec![(yv, xv, 3, -1)]),
        // x − y > 3             ⇒  y − x <= −3 − ε
        (Cmp::Gt, true, vec![(xv, yv, -3, -1)]),
        // not (x − y > 3)       ⇒  x − y <= 3
        (Cmp::Gt, false, vec![(yv, xv, 3, 0)]),
        // x − y = 3             ⇒  BOTH halves, neither strict
        (Cmp::Eq, true, vec![(yv, xv, 3, 0), (xv, yv, -3, 0)]),
    ];
    for (op, value, want) in cases {
        let got = edges(&mut th, tb.term(0, op, 3), value)
            .unwrap_or_else(|| panic!("{op:?}/{value} must lower to edges"));
        assert_eq!(got, want, "wrong lowering for {op:?} asserted {value}");
    }

    // not (x − y = 3) is a DISJUNCTION: it must be refused, not approximated.
    assert!(
        edges(&mut th, tb.term(0, Cmp::Eq, 3), false).is_none(),
        "negated equality must not lower to any conjunctive edge set"
    );
}

#[test]
fn var_const_edge_table_is_exact_for_every_operator_and_polarity() {
    let tb = Table::new();
    let mut th = DiffLogicTheory::new(&tb.terms);
    let _ = th.debug_edges(tb.term(1, Cmp::Le, 3), true);
    let xv = th.debug_vertex(tb.x).expect("x interned");
    let z = DiffLogicTheory::debug_zero_vertex();
    assert_ne!(
        xv, z,
        "a real variable must never collide with the zero vertex"
    );

    // `x ⋈ 3` is `x − Z ⋈ 3`.
    let cases: [(Cmp, bool, Vec<(usize, usize, i64, i64)>); 9] = [
        (Cmp::Le, true, vec![(z, xv, 3, 0)]),
        (Cmp::Le, false, vec![(xv, z, -3, -1)]),
        (Cmp::Lt, true, vec![(z, xv, 3, -1)]),
        (Cmp::Lt, false, vec![(xv, z, -3, 0)]),
        (Cmp::Ge, true, vec![(xv, z, -3, 0)]),
        (Cmp::Ge, false, vec![(z, xv, 3, -1)]),
        (Cmp::Gt, true, vec![(xv, z, -3, -1)]),
        (Cmp::Gt, false, vec![(z, xv, 3, 0)]),
        (Cmp::Eq, true, vec![(z, xv, 3, 0), (xv, z, -3, 0)]),
    ];
    for (op, value, want) in cases {
        let got = edges(&mut th, tb.term(1, op, 3), value)
            .unwrap_or_else(|| panic!("{op:?}/{value} must lower to edges"));
        assert_eq!(got, want, "wrong var-vs-const lowering for {op:?}@{value}");
    }
    assert!(edges(&mut th, tb.term(1, Cmp::Eq, 3), false).is_none());
}

#[test]
fn negated_constant_bound_lowers_with_the_right_sign() {
    // A negative `c` is where a sign slip in the `−c` half of the table shows
    // up: `not (x <= −2)` is `x > −2`, NOT `x > 2`.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let le = raw_cmp(&mut terms, Cmp::Le, x, -2);
    let mut th = DiffLogicTheory::new(&terms);
    let _ = th.debug_edges(le, true);
    let xv = th.debug_vertex(x).expect("x");
    let z = DiffLogicTheory::debug_zero_vertex();
    assert_eq!(edges(&mut th, le, true), Some(vec![(z, xv, -2, 0)]));
    assert_eq!(edges(&mut th, le, false), Some(vec![(xv, z, 2, -1)]));
}

// ---------------------------------------------------------------------------
// 2. Behavioural cross-product against hand-derived reference semantics
// ---------------------------------------------------------------------------

/// For every ordered pair of literals over {<=,<,=,>=,>} × {2,3,4} × {T,F},
/// compare the solver's verdict with the exact interval semantics, and (when
/// SAT) check the EXTRACTED MODEL really lands in the intersection. Run for
/// the two-variable and the var-vs-const form.
fn cross_product_matches_reference_semantics(form: usize) {
    let tb = Table::new();
    let mut checked = 0usize;
    for &op_a in &ALL_CMP {
        for &ca in &CONSTS {
            for &va in &[true, false] {
                for &op_b in &ALL_CMP {
                    for &cb in &CONSTS {
                        for &vb in &[true, false] {
                            let ta = tb.term(form, op_a, ca);
                            let tbm = tb.term(form, op_b, cb);
                            let mut th = DiffLogicTheory::new(&tb.terms);
                            th.assert_literal(ta, va);
                            th.assert_literal(tbm, vb);
                            let got = th.check();

                            let (ma, mb) = (meaning(op_a, ca, va), meaning(op_b, cb, vb));
                            let (Some(ra), Some(rb)) = (ma, mb) else {
                                // A negated equality: the ONLY acceptable answer
                                // is Unknown (never a guessed disjunct).
                                assert!(
                                    is_unknown(&got),
                                    "negated equality must fail closed, got {got:?} for \
                                     ({op_a:?},{ca},{va}) ∧ ({op_b:?},{cb},{vb})"
                                );
                                continue;
                            };
                            checked += 1;
                            let want_sat = regions_feasible(ra, rb);
                            assert_eq!(
                                is_sat(&got),
                                want_sat,
                                "form {form}: ({op_a:?} {ca} @{va}) ∧ ({op_b:?} {cb} @{vb}) \
                                 should be {} but solver said {got:?}",
                                if want_sat { "SAT" } else { "UNSAT" }
                            );
                            if !want_sat {
                                assert!(is_unsat(&got), "expected a NON-EMPTY conflict, {got:?}");
                                continue;
                            }
                            // The model must satisfy both half-planes exactly,
                            // including strictness (ε realization).
                            let m = th.extract_model();
                            let d = tb.diff_value(form, &m);
                            assert!(
                                region_holds(ra, &d) && region_holds(rb, &d),
                                "form {form}: model d={d} violates \
                                 ({op_a:?} {ca} @{va}) ∧ ({op_b:?} {cb} @{vb})"
                            );
                        }
                    }
                }
            }
        }
    }
    assert!(checked > 500, "cross product did not run ({checked} pairs)");
}

#[test]
fn two_var_cross_product_matches_reference_semantics() {
    cross_product_matches_reference_semantics(0);
}

#[test]
fn var_const_cross_product_matches_reference_semantics() {
    cross_product_matches_reference_semantics(1);
}

// ---------------------------------------------------------------------------
// 3. Op::Eq — the disjunctive-negation trap
// ---------------------------------------------------------------------------

#[test]
fn negated_equality_never_picks_a_disjunct() {
    // If `not (x − y = 3)` were lowered as either `x − y < 3` or `x − y > 3`,
    // exactly one of these two pairings would come back UNSAT. Both must be
    // Unknown: the theory has to refuse the disjunction outright.
    let tb = Table::new();
    for form in 0..2 {
        let eq3 = tb.term(form, Cmp::Eq, 3);
        for probe in [Cmp::Le, Cmp::Lt, Cmp::Ge, Cmp::Gt] {
            for c in CONSTS {
                for v in [true, false] {
                    let p = tb.term(form, probe, c);
                    let r = verdict_over(&tb.terms, &[(eq3, false), (p, v)]);
                    assert!(
                        is_unknown(&r),
                        "form {form}: not(=3) ∧ ({probe:?} {c} @{v}) must be Unknown, got {r:?}"
                    );
                }
            }
        }
    }
}

/// [`verdict`] over an arbitrary [`TermStore`] rather than the [`Fx`] fixture.
fn verdict_over(terms: &TermStore, lits: &[(TermId, bool)]) -> TheoryResult {
    let mut th = DiffLogicTheory::new(terms);
    for &(t, v) in lits {
        th.assert_literal(t, v);
    }
    th.check()
}

#[test]
fn positive_equality_pins_both_halves() {
    // `x − y = 3` must be BOTH `<= 3` and `>= 3`: it conflicts with each strict
    // side and is satisfied by neither alone.
    let tb = Table::new();
    for form in 0..2 {
        let eq3 = tb.term(form, Cmp::Eq, 3);
        // Contradicts d < 3 and d > 3, and both non-strict companions are fine.
        assert!(is_unsat(&verdict_over(
            &tb.terms,
            &[(eq3, true), (tb.term(form, Cmp::Lt, 3), true)]
        )));
        assert!(is_unsat(&verdict_over(
            &tb.terms,
            &[(eq3, true), (tb.term(form, Cmp::Gt, 3), true)]
        )));
        assert!(is_sat(&verdict_over(
            &tb.terms,
            &[(eq3, true), (tb.term(form, Cmp::Le, 3), true)]
        )));
        assert!(is_sat(&verdict_over(
            &tb.terms,
            &[(eq3, true), (tb.term(form, Cmp::Ge, 3), true)]
        )));
        // ... and it excludes every other constant.
        assert!(is_unsat(&verdict_over(
            &tb.terms,
            &[(eq3, true), (tb.term(form, Cmp::Eq, 4), true)]
        )));
    }
}

// ---------------------------------------------------------------------------
// 4. The ε component in isolation
// ---------------------------------------------------------------------------

#[test]
fn strictness_survives_both_polarities_of_every_operator() {
    // `d >= c ∧ d <= c` is SAT (d = c) but every strict variant of the same
    // pair is UNSAT. Written across all four ways of expressing each side,
    // including the negated ones, so a `<`/`<=` slip anywhere is caught.
    let tb = Table::new();
    for form in 0..2 {
        // Non-strict on both sides: exactly d = 3.
        let non_strict: [(Cmp, bool); 4] = [
            (Cmp::Le, true),  // d <= 3
            (Cmp::Gt, false), // not (d > 3)  ⇔  d <= 3
            (Cmp::Ge, true),  // d >= 3
            (Cmp::Lt, false), // not (d < 3)  ⇔  d >= 3
        ];
        for &(hi_op, hi_v) in &non_strict[..2] {
            for &(lo_op, lo_v) in &non_strict[2..] {
                assert!(
                    is_sat(&verdict_over(
                        &tb.terms,
                        &[
                            (tb.term(form, hi_op, 3), hi_v),
                            (tb.term(form, lo_op, 3), lo_v)
                        ]
                    )),
                    "form {form}: {hi_op:?}@{hi_v} ∧ {lo_op:?}@{lo_v} must allow d = 3"
                );
            }
        }
        // Strict upper against non-strict lower (and vice versa): UNSAT.
        let strict_hi: [(Cmp, bool); 2] = [(Cmp::Lt, true), (Cmp::Ge, false)]; // d < 3
        let strict_lo: [(Cmp, bool); 2] = [(Cmp::Gt, true), (Cmp::Le, false)]; // d > 3
        for &(hi_op, hi_v) in &strict_hi {
            for &(lo_op, lo_v) in &non_strict[2..] {
                assert!(
                    is_unsat(&verdict_over(
                        &tb.terms,
                        &[
                            (tb.term(form, hi_op, 3), hi_v),
                            (tb.term(form, lo_op, 3), lo_v)
                        ]
                    )),
                    "form {form}: {hi_op:?}@{hi_v} ∧ {lo_op:?}@{lo_v} must be UNSAT"
                );
            }
        }
        for &(lo_op, lo_v) in &strict_lo {
            for &(hi_op, hi_v) in &non_strict[..2] {
                assert!(
                    is_unsat(&verdict_over(
                        &tb.terms,
                        &[
                            (tb.term(form, hi_op, 3), hi_v),
                            (tb.term(form, lo_op, 3), lo_v)
                        ]
                    )),
                    "form {form}: {lo_op:?}@{lo_v} ∧ {hi_op:?}@{hi_v} must be UNSAT"
                );
            }
        }
    }
}

#[test]
fn epsilon_accumulates_across_a_chain_of_negated_non_strict_atoms() {
    // not (x − y <= 0) ∧ not (y − x <= 0)  ⇔  x > y ∧ y > x. Both rational
    // parts are 0; only the ε-count (−1 each) makes the cycle negative. This
    // is the test that fails if the NEGATION of `<=` drops its ε.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let xy = terms.mk_sub(vec![x, y]);
    let yx = terms.mk_sub(vec![y, x]);
    let a = raw_cmp(&mut terms, Cmp::Le, xy, 0);
    let b = raw_cmp(&mut terms, Cmp::Le, yx, 0);
    assert!(is_unsat(&verdict_over(&terms, &[(a, false), (b, false)])));
    // The non-strict twins (`not (x − y < 0)` ⇔ `x − y >= 0`) are SAT (x = y).
    let c = raw_cmp(&mut terms, Cmp::Lt, xy, 0);
    let d = raw_cmp(&mut terms, Cmp::Lt, yx, 0);
    assert!(is_sat(&verdict_over(&terms, &[(c, false), (d, false)])));
}

// ---------------------------------------------------------------------------
// 5. The `−y ⋈ c` surface form (operator flipped by `collect_comparison`)
// ---------------------------------------------------------------------------

#[test]
fn unary_minus_lhs_flips_the_operator_in_both_polarities() {
    // `(<= (- y) 3)` is `−y <= 3` ⇔ `y >= −3`, which `collect_comparison`
    // normalises by FLIPPING the operator (Le → Ge) and negating the constant.
    // Its negation is then `y < −3`. Both directions are checked against the
    // exact edge, because this is the one path that actually reaches
    // `Op::Ge`/`Op::Gt` from ordinary parsed input.
    let mut terms = TermStore::new();
    let y = terms.mk_var("y", Sort::Real);
    let neg_y = terms.mk_sub(vec![y]);
    let a = raw_cmp(&mut terms, Cmp::Le, neg_y, 3);

    let mut th = DiffLogicTheory::new(&terms);
    let _ = th.debug_edges(a, true);
    let yv = th.debug_vertex(y).expect("y");
    let z = DiffLogicTheory::debug_zero_vertex();
    // y >= −3  ⇒  Z − y <= 3
    assert_eq!(edges(&mut th, a, true), Some(vec![(yv, z, 3, 0)]));
    // not (−y <= 3)  ⇔  y < −3  ⇒  y − Z <= −3 − ε
    assert_eq!(edges(&mut th, a, false), Some(vec![(z, yv, -3, -1)]));

    // Behavioural confirmation against explicit bounds on y.
    let y_ge_m3 = raw_cmp(&mut terms, Cmp::Ge, y, -3);
    let y_lt_m3 = raw_cmp(&mut terms, Cmp::Lt, y, -3);
    assert!(is_sat(&verdict_over(&terms, &[(a, true), (y_ge_m3, true)])));
    assert!(is_unsat(&verdict_over(
        &terms,
        &[(a, true), (y_lt_m3, true)]
    )));
    assert!(is_unsat(&verdict_over(
        &terms,
        &[(a, false), (y_ge_m3, true)]
    )));
    assert!(is_sat(&verdict_over(
        &terms,
        &[(a, false), (y_lt_m3, true)]
    )));
}

// ---------------------------------------------------------------------------
// Integer lane (QF_IDL): sort gating and integer-tightened lowering
// ---------------------------------------------------------------------------

/// The same shapes as `Table` but over `Int`, for the `new_int` lane.
struct IntTable {
    terms: TermStore,
    x: TermId,
    y: TermId,
}

impl IntTable {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let x = terms.mk_var("ix", Sort::Int);
        let y = terms.mk_var("iy", Sort::Int);
        Self { terms, x, y }
    }
    fn diff_cmp(&mut self, op: Cmp, c: i64) -> TermId {
        let d = self.terms.mk_sub(vec![self.x, self.y]);
        raw_cmp(&mut self.terms, op, d, c)
    }
}

/// The Real lane must still REFUSE Int atoms. Lowering them through the
/// rational table is only a relaxation, which is the whole reason the integer
/// lane exists — if this ever flips to "dl", QF_RDL has silently started
/// approximating integers.
#[test]
fn real_lane_still_refuses_int_atoms() {
    let mut tb = IntTable::new();
    let le = tb.diff_cmp(Cmp::Le, 3);
    let mut th = DiffLogicTheory::new(&tb.terms);
    assert_eq!(th.debug_kind(le), "unsupported");
}

/// The integer lane accepts Int atoms, and the LOWERED edges carry an integral
/// weight with a ZERO epsilon for every operator — including the strict ones,
/// which is exactly what tightening buys. A non-zero epsilon here would mean
/// the model is only rational and the lane is unsound over Int.
#[test]
fn int_lane_lowers_every_operator_to_integral_zero_epsilon_edges() {
    for (op, c) in [
        (Cmp::Le, 3),
        (Cmp::Lt, 3),
        (Cmp::Ge, 3),
        (Cmp::Gt, 3),
        (Cmp::Le, -2),
        (Cmp::Lt, -2),
        (Cmp::Ge, -2),
        (Cmp::Gt, -2),
    ] {
        let mut tb = IntTable::new();
        let t = tb.diff_cmp(op, c);
        let mut th = DiffLogicTheory::new_int(&tb.terms);
        assert_eq!(
            th.debug_kind(t),
            "dl",
            "{op:?} {c} must route on the int lane"
        );
        for value in [true, false] {
            let es = th.debug_edges(t, value).expect("both polarities lower");
            for (_, _, q, eps) in es {
                assert!(
                    q.is_integer(),
                    "{op:?} {c} {value}: non-integral weight {q}"
                );
                assert_eq!(eps, 0, "{op:?} {c} {value}: epsilon must be tightened away");
            }
        }
    }
}

/// The int lane must refuse REAL atoms, mirroring the real lane's refusal of
/// Int. (A genuinely mixed difference cannot be built at all — `mk_sub` panics
/// on mismatched sorts — so the sort system already excludes that case
/// upstream, and the per-lane gate only has to reject the wrong uniform sort.)
#[test]
fn int_lane_refuses_real_atoms() {
    let tb = Table::new();
    let le = tb.term(0, Cmp::Le, 3);
    let mut th = DiffLogicTheory::new_int(&tb.terms);
    assert_eq!(th.debug_kind(le), "unsupported");
}
