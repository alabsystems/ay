// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact MBP (`mbp/exact.rs`, Workstream B R2) — under-approximation locks.
//!
//! For `ψ = project_exact(φ, E, M)`:
//! (i)   `M ⊨ ψ` (every literal evaluates to true),
//! (ii)  no variable of `E` occurs in `ψ`,
//! (iii) `ψ ⇒ ∃E. φ`: every point of a window satisfying `ψ` extends to a model
//!       of `φ` (in-crate SMT on the ground-in-kept-vars formula), and — when a
//!       `z3` executable is on PATH — `ψ ∧ ∀E. ¬φ` is UNSAT for z3.
//!
//! Random LIA/LRA conjunctions include non-unit coefficients, several lower
//! bounds, strict bounds, disequalities, `mod` literals and arithmetic ITE
//! terms; deterministic cases pin each rule (unit/non-unit equality, BJ with the
//! divisibility literal, LW strictness, disequality split, ITE split).

use super::*;
use crate::expr::evaluate_expr;
use crate::mbp::exact::ExactStats;
use crate::smt::{SmtContext, SmtResult};
use std::io::Write;
use std::process::{Command, Stdio};

type Model = FxHashMap<String, SmtValue>;

fn ivar(n: &str) -> ChcVar {
    ChcVar::new(n, ChcSort::Int)
}
fn rvar(n: &str) -> ChcVar {
    ChcVar::new(n, ChcSort::Real)
}
fn v(x: &ChcVar) -> ChcExpr {
    ChcExpr::var(x.clone())
}
fn int_model(pairs: &[(&str, i128)]) -> Model {
    pairs
        .iter()
        .map(|(n, k)| ((*n).to_string(), SmtValue::Int(*k)))
        .collect()
}
fn real_val(num: i64, den: i64) -> SmtValue {
    SmtValue::Real(num_rational::BigRational::new(num.into(), den.into()))
}

fn holds(e: &ChcExpr, m: &Model) -> Option<bool> {
    match evaluate_expr(e, m)? {
        SmtValue::Bool(b) => Some(b),
        _ => None,
    }
}

fn project(phi: &ChcExpr, elim: &[ChcVar], m: &Model) -> (Vec<ChcExpr>, ExactStats, usize) {
    let p = Mbp::new()
        .project_exact(phi, elim, m)
        .expect("every eliminated variable has a model value");
    (p.lits, p.stats, p.substituted.len())
}

fn assert_model_and_vars(lits: &[ChcExpr], elim: &[ChcVar], m: &Model, what: &str) {
    for l in lits {
        assert_eq!(
            holds(l, m),
            Some(true),
            "{what}: the model must satisfy {l}"
        );
        for x in elim {
            assert!(
                !l.contains_var_name(&x.name),
                "{what}: {} survives in {l}",
                x.name
            );
        }
    }
}

// ---------------------------------------------------------------- deterministic

#[test]
fn unit_equality_substitutes_exactly() {
    // x = y + 1 ∧ y ≥ 0, eliminate y  ⇒  x ≥ 1
    let (x, y) = (ivar("x"), ivar("y"));
    let phi = ChcExpr::and(
        ChcExpr::eq(v(&x), ChcExpr::add(v(&y), ChcExpr::int(1))),
        ChcExpr::ge(v(&y), ChcExpr::int(0)),
    );
    let m = int_model(&[("x", 4), ("y", 3)]);
    let (lits, st, subst) = project(&phi, &[y.clone()], &m);
    assert_eq!(subst, 0);
    assert_eq!(st.unit_eq, 1);
    assert_eq!(lits, vec![ChcExpr::ge(v(&x), ChcExpr::int(1))]);
    assert_model_and_vars(&lits, &[y], &m, "unit eq");
}

#[test]
fn unit_equality_rewrites_a_mod_literal_instead_of_pinning() {
    // y mod 3 = 1 ∧ x = y + 1, eliminate y  ⇒  (x - 1) mod 3 = 1 (no pin on x)
    let (x, y) = (ivar("x"), ivar("y"));
    let phi = ChcExpr::and(
        ChcExpr::eq(ChcExpr::mod_op(v(&y), ChcExpr::int(3)), ChcExpr::int(1)),
        ChcExpr::eq(v(&x), ChcExpr::add(v(&y), ChcExpr::int(1))),
    );
    let m = int_model(&[("x", 5), ("y", 4)]);
    let (lits, _, subst) = project(&phi, &[y.clone()], &m);
    assert_eq!(subst, 0, "exact: no model substitution");
    assert_eq!(lits.len(), 1);
    assert!(
        !lits[0].to_string().contains("(= x 5)"),
        "x must not be pinned: {:?}",
        lits
    );
    assert_model_and_vars(&lits, &[y], &m, "mod via equality");
    // x = 8 also satisfies ψ (8 - 1 = 7 ≡ 1 mod 3): the cube is not a point.
    assert_eq!(holds(&lits[0], &int_model(&[("x", 8)])), Some(true));
    assert_eq!(holds(&lits[0], &int_model(&[("x", 6)])), Some(false));
}

#[test]
fn non_unit_equality_emits_the_divisibility_literal() {
    // 2y = x ∧ y ≤ 5, eliminate y  ⇒  x mod 2 = 0 ∧ x ≤ 10
    let (x, y) = (ivar("x"), ivar("y"));
    let phi = ChcExpr::and(
        ChcExpr::eq(ChcExpr::mul(ChcExpr::int(2), v(&y)), v(&x)),
        ChcExpr::le(v(&y), ChcExpr::int(5)),
    );
    let m = int_model(&[("x", 6), ("y", 3)]);
    let (lits, st, subst) = project(&phi, &[y.clone()], &m);
    assert_eq!((st.nonunit_eq, st.div_literals, subst), (1, 1, 0));
    assert_model_and_vars(&lits, &[y], &m, "non-unit eq");
    let at = |k| int_model(&[("x", k)]);
    let all = |k| lits.iter().all(|l| holds(l, &at(k)) == Some(true));
    assert!(all(10) && all(-4), "even x ≤ 10 are in the projection");
    assert!(!all(7) && !all(12), "odd x and x > 10 are not");
}

#[test]
fn bj_keeps_every_lower_bound_and_the_divisibility_witness() {
    // 2y ≥ a ∧ y ≥ b ∧ 3y ≤ c, eliminate y (no equality).
    let (a, b, c, y) = (ivar("a"), ivar("b"), ivar("c"), ivar("y"));
    let phi = ChcExpr::and_all([
        ChcExpr::ge(ChcExpr::mul(ChcExpr::int(2), v(&y)), v(&a)),
        ChcExpr::ge(v(&y), v(&b)),
        ChcExpr::le(ChcExpr::mul(ChcExpr::int(3), v(&y)), v(&c)),
    ]);
    // a/2 = 3.5 is the model-greatest lower bound (b = 1): d = (-7) mod 2 = 1.
    let m = int_model(&[("a", 7), ("b", 1), ("c", 13), ("y", 4)]);
    let (lits, st, subst) = project(&phi, &[y.clone()], &m);
    assert_eq!((st.bj_bounds, st.div_literals, subst), (1, 1, 0));
    assert_model_and_vars(&lits, &[y.clone()], &m, "bj");
    // Under-approximation on a window, brute force (y ∈ [-40, 40] suffices here).
    for av in -8..=8 {
        for bv in -4..=4 {
            for cv in -12..=12 {
                let pt = int_model(&[("a", av), ("b", bv), ("c", cv)]);
                if lits.iter().all(|l| holds(l, &pt) == Some(true)) {
                    let ok = (-40..=40).any(|yv| {
                        let mut full = pt.clone();
                        full.insert("y".into(), SmtValue::Int(yv));
                        holds(&phi, &full) == Some(true)
                    });
                    assert!(ok, "ψ admits a={av} b={bv} c={cv} with no integer y");
                }
            }
        }
    }
}

#[test]
fn lw_carries_strictness_and_all_lower_bounds() {
    // y > a ∧ y ≥ b ∧ y < c  over the reals, eliminate y.
    let (a, b, c, y) = (rvar("a"), rvar("b"), rvar("c"), rvar("y"));
    let phi = ChcExpr::and_all([
        ChcExpr::gt(v(&y), v(&a)),
        ChcExpr::ge(v(&y), v(&b)),
        ChcExpr::lt(v(&y), v(&c)),
    ]);
    let mut m = Model::default();
    m.insert("a".into(), real_val(1, 1));
    m.insert("b".into(), real_val(1, 2));
    m.insert("c".into(), real_val(3, 1));
    m.insert("y".into(), real_val(2, 1));
    let (lits, st, subst) = project(&phi, &[y.clone()], &m);
    assert_eq!((st.lw_bounds, subst), (1, 0));
    assert_model_and_vars(&lits, &[y], &m, "lw");
    // a is the tightest (strict) lower bound: a ≥ b (non-strict) and a < c (strict).
    let mut tie = m.clone();
    tie.insert("c".into(), real_val(1, 1)); // c = a: y ∈ (1, 1) is empty
    assert!(
        lits.iter().any(|l| holds(l, &tie) == Some(false)),
        "strictness lost: {lits:?}"
    );
}

#[test]
fn disequality_is_split_by_the_model() {
    // y ≠ x ∧ 0 ≤ y ≤ 10, eliminate y  (model y = 5 > x = 3 ⇒ y ≥ x + 1)
    let (x, y) = (ivar("x"), ivar("y"));
    let phi = ChcExpr::and_all([
        ChcExpr::not(ChcExpr::eq(v(&y), v(&x))),
        ChcExpr::ge(v(&y), ChcExpr::int(0)),
        ChcExpr::le(v(&y), ChcExpr::int(10)),
    ]);
    let m = int_model(&[("x", 3), ("y", 5)]);
    let (lits, st, subst) = project(&phi, &[y.clone()], &m);
    assert_eq!((st.diseq_splits, subst), (1, 0));
    assert_model_and_vars(&lits, &[y], &m, "diseq");
}

#[test]
fn arithmetic_ite_is_split_by_the_model() {
    // x = ite(y > 0, y, -y) ∧ y ≥ 2, eliminate y  (y = 3 ⇒ x = y ∧ y > 0)
    let (x, y) = (ivar("x"), ivar("y"));
    let phi = ChcExpr::and(
        ChcExpr::eq(
            v(&x),
            ChcExpr::ite(
                ChcExpr::gt(v(&y), ChcExpr::int(0)),
                v(&y),
                ChcExpr::neg(v(&y)),
            ),
        ),
        ChcExpr::ge(v(&y), ChcExpr::int(2)),
    );
    let m = int_model(&[("x", 3), ("y", 3)]);
    let (lits, st, subst) = project(&phi, &[y.clone()], &m);
    assert!(st.ite_splits >= 1);
    assert_eq!(subst, 0, "exact after the split");
    assert_model_and_vars(&lits, &[y], &m, "ite");
    assert_eq!(
        lits.iter()
            .all(|l| holds(l, &int_model(&[("x", 9)])) == Some(true)),
        true,
        "x = 9 is in ∃y.φ and in ψ"
    );
}

#[test]
fn unconstrained_variable_stays_free() {
    // x1 = x + 1 ∧ y1 = y ∧ x1 ≥ 3, eliminate x1, y1  ⇒  x ≥ 2 (nothing on y)
    let (x, y, x1, y1) = (ivar("x"), ivar("y"), ivar("x1"), ivar("y1"));
    let phi = ChcExpr::and_all([
        ChcExpr::eq(v(&x1), ChcExpr::add(v(&x), ChcExpr::int(1))),
        ChcExpr::eq(v(&y1), v(&y)),
        ChcExpr::ge(v(&x1), ChcExpr::int(3)),
    ]);
    let m = int_model(&[("x", 4), ("y", 17), ("x1", 5), ("y1", 17)]);
    let (lits, _, subst) = project(&phi, &[x1.clone(), y1.clone()], &m);
    assert_eq!(subst, 0);
    assert_eq!(lits, vec![ChcExpr::ge(v(&x), ChcExpr::int(2))]);
    assert!(
        lits.iter().all(|l| !l.contains_var_name("y")),
        "y must stay free"
    );
}

#[test]
fn a_variable_without_a_model_value_is_reported() {
    let (x, y) = (ivar("x"), ivar("y"));
    let phi = ChcExpr::eq(ChcExpr::mod_op(v(&y), ChcExpr::int(2)), v(&x));
    let m = int_model(&[("x", 1)]);
    let r = Mbp::new().project_exact(&phi, &[y.clone()], &m);
    assert_eq!(r.err(), Some(crate::mbp::exact::ExactFail::NoValue(y)));
}

#[test]
fn boolean_arguments_are_renamed_not_pinned() {
    // c = x ∧ y1 = (x ∧ z) ∧ ¬y1 ∧ w, eliminate x, z, y1 (c, w kept; x, z free
    // in the model's sense): the projection is ¬(c ∧ z') for some z' — i.e.
    // `true` after eliminating z — and must not pin c.
    let b = |n: &str| ChcVar::new(n, ChcSort::Bool);
    let (c, x, z, y1, w) = (b("c"), b("x"), b("z"), b("y1"), b("w"));
    let phi = ChcExpr::and_all([
        ChcExpr::eq(v(&c), v(&x)),
        ChcExpr::eq(v(&y1), ChcExpr::and(v(&x), v(&z))),
        ChcExpr::not(v(&y1)),
        v(&w),
    ]);
    let m: Model = [
        ("c", true),
        ("x", true),
        ("z", false),
        ("y1", false),
        ("w", true),
    ]
    .iter()
    .map(|(n, val)| ((*n).to_string(), SmtValue::Bool(*val)))
    .collect();
    let p = Mbp::new()
        .project_exact(&phi, &[x.clone(), z.clone(), y1.clone()], &m)
        .expect("project");
    assert!(p.stats.bool_defs >= 2, "{:?}", p.stats);
    assert_model_and_vars(&p.lits, &[x, z, y1], &m, "bool defs");
    assert!(
        p.lits.iter().all(|l| !l.contains_var_name("c")),
        "c must stay free (renamed, not pinned): {:?}",
        p.lits
    );
    assert!(p.lits.contains(&v(&w)));
}

#[test]
fn a_missing_value_completes_to_a_checked_default() {
    // (y mod 2) = 0 ∧ x ≥ 0 with y unassigned: y := 0 keeps every literal true.
    let (x, y) = (ivar("x"), ivar("y"));
    let phi = ChcExpr::and(
        ChcExpr::eq(ChcExpr::mod_op(v(&y), ChcExpr::int(2)), ChcExpr::int(0)),
        ChcExpr::ge(v(&x), ChcExpr::int(0)),
    );
    let m = int_model(&[("x", 3)]);
    let p = Mbp::new()
        .project_exact(&phi, &[y.clone()], &m)
        .expect("default completes");
    assert_eq!(p.substituted, vec![y.clone()]);
    assert_eq!(p.lits, vec![ChcExpr::ge(v(&x), ChcExpr::int(0))]);
}

// ---------------------------------------------------------------- random property

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.next() % ((hi - lo + 1) as u64)) as i64
    }
    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[(self.next() % xs.len() as u64) as usize]
    }
}

/// SMT-LIB text for the formulas these tests build (negative numerals wrapped).
fn smt2(e: &ChcExpr) -> String {
    match e {
        ChcExpr::Bool(b) => b.to_string(),
        ChcExpr::Int(n) if *n < 0 => format!("(- {})", -n),
        ChcExpr::Int(n) => n.to_string(),
        ChcExpr::Real(n, d) => {
            let num = if *n < 0 {
                format!("(- {}.0)", -n)
            } else {
                format!("{n}.0")
            };
            if *d == 1 {
                num
            } else {
                format!("(/ {num} {d}.0)")
            }
        }
        ChcExpr::Var(x) => x.name.clone(),
        ChcExpr::Op(op, args) => {
            let name = match op {
                ChcOp::Add => "+",
                ChcOp::Sub | ChcOp::Neg => "-",
                ChcOp::Mul => "*",
                ChcOp::Div if e.sort() == ChcSort::Real => "/",
                ChcOp::Div => "div",
                ChcOp::Mod => "mod",
                ChcOp::Eq => "=",
                ChcOp::Ne => "distinct",
                ChcOp::Lt => "<",
                ChcOp::Le => "<=",
                ChcOp::Gt => ">",
                ChcOp::Ge => ">=",
                ChcOp::Not => "not",
                ChcOp::And => "and",
                ChcOp::Or => "or",
                ChcOp::Ite => "ite",
                ChcOp::Implies => "=>",
                other => panic!("smt2 printer: unexpected {other:?}"),
            };
            if args.is_empty() {
                return if *op == ChcOp::And {
                    "true".into()
                } else {
                    "false".into()
                };
            }
            let inner: Vec<String> = args.iter().map(|a| smt2(a)).collect();
            format!("({name} {})", inner.join(" "))
        }
        other => panic!("smt2 printer: unexpected {other:?}"),
    }
}

fn z3_available() -> bool {
    Command::new("z3")
        .env("ATERM_Z3_IS_ORACLE", "1") // aterm reroutes z3 unless it is used as the oracle
        .arg("-version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|s| s.success())
}

/// `Some(true)` = z3 says `ψ ∧ ∀E. ¬φ` is UNSAT (the projection is an
/// under-approximation), `Some(false)` = SAT (a ψ-point without witness),
/// `None` = unknown / error.
fn z3_under_approx(
    psi: &[ChcExpr],
    phi: &ChcExpr,
    kept: &[ChcVar],
    elim: &[ChcVar],
) -> Option<bool> {
    let sort = |x: &ChcVar| {
        if x.sort == ChcSort::Real {
            "Real"
        } else {
            "Int"
        }
    };
    let mut s = String::new();
    for k in kept {
        s += &format!("(declare-const {} {})\n", k.name, sort(k));
    }
    for l in psi {
        s += &format!("(assert {})\n", smt2(l));
    }
    let binders: Vec<String> = elim
        .iter()
        .map(|x| format!("({} {})", x.name, sort(x)))
        .collect();
    s += &format!(
        "(assert (forall ({}) (not {})))\n(check-sat)\n",
        binders.join(" "),
        smt2(phi)
    );
    let mut child = Command::new("z3")
        .env("ATERM_Z3_IS_ORACLE", "1")
        .args(["-in", "-T:20"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .ok()?;
    child.stdin.take()?.write_all(s.as_bytes()).ok()?;
    let out = child.wait_with_output().ok()?;
    match String::from_utf8_lossy(&out.stdout).trim() {
        "unsat" => Some(true),
        "sat" => Some(false),
        _ => None,
    }
}

/// `φ[kept := point]` is satisfiable (in-crate SMT, bounded per check).
/// `None` = Unknown, including a check that runs past its bound: the ground
/// query still has the three eliminated integer variables free, and ay-lia's
/// finite-domain enumeration has been observed to spin for hours on one such
/// random `mod`/ITE conjunction (2026-09-23, sampled stack
/// `LiaSolver::try_finite_domain_search`), so the fallback path never trusts
/// an unbounded check.
fn extends(phi: &ChcExpr, point: &[(ChcVar, ChcExpr)]) -> Option<bool> {
    let ground = phi.substitute(point).simplify_constants();
    let mut smt = SmtContext::new();
    match smt.check_sat_with_timeout(&ground, std::time::Duration::from_secs(2)) {
        SmtResult::Sat(_) => Some(true),
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
            Some(false)
        }
        SmtResult::Unknown => None,
    }
}

fn random_lin(rng: &mut Rng, vars: &[ChcVar], real: bool) -> ChcExpr {
    let n = rng.range(1, 3) as usize;
    let mut acc: Option<ChcExpr> = None;
    for _ in 0..n {
        let x = rng.pick(vars).clone();
        let c = *rng.pick(&[-3i64, -2, -1, 1, 1, 1, 2, 3]);
        let coeff = if real {
            ChcExpr::Real(c, 1)
        } else {
            ChcExpr::int(c)
        };
        let t = if c == 1 {
            v(&x)
        } else {
            ChcExpr::mul(coeff, v(&x))
        };
        acc = Some(match acc {
            None => t,
            Some(a) => ChcExpr::add(a, t),
        });
    }
    acc.expect("n ≥ 1")
}

fn random_literal(rng: &mut Rng, vars: &[ChcVar], real: bool) -> ChcExpr {
    let k = rng.range(-6, 6);
    let konst = if real {
        ChcExpr::Real(k, *rng.pick(&[1, 2]))
    } else {
        ChcExpr::int(k)
    };
    if !real && rng.range(0, 19) == 0 {
        // (x + k) mod m = r
        let m = rng.range(2, 3);
        let r = rng.range(0, m - 1);
        return ChcExpr::eq(
            ChcExpr::mod_op(ChcExpr::add(v(rng.pick(vars)), konst), ChcExpr::int(m)),
            ChcExpr::int(r),
        );
    }
    let mut lhs = random_lin(rng, vars, real);
    if rng.range(0, 9) == 0 {
        let (a, b, c) = (
            rng.pick(vars).clone(),
            rng.pick(vars).clone(),
            rng.pick(vars).clone(),
        );
        lhs = ChcExpr::add(
            lhs,
            ChcExpr::ite(ChcExpr::gt(v(&a), v(&b)), v(&c), konst.clone()),
        );
    }
    match rng.range(0, 9) {
        0 | 1 => ChcExpr::eq(lhs, konst),
        2 | 3 => ChcExpr::le(lhs, konst),
        4 | 5 => ChcExpr::ge(lhs, konst),
        6 => ChcExpr::lt(lhs, konst),
        7 => ChcExpr::gt(lhs, konst),
        _ => ChcExpr::not(ChcExpr::eq(lhs, konst)),
    }
}

struct RunSummary {
    cases: usize,
    stats: ExactStats,
    substituted: usize,
    z3_checked: usize,
    /// Cases where the LEGACY projector (`Mbp::project`) admits a window point
    /// with no witness (informational: G8, not asserted).
    legacy_over: usize,
}

/// First window point satisfying `psi` that does not extend to a model of `phi`.
fn window_counterexample(
    psi: &ChcExpr,
    phi: &ChcExpr,
    kept: &[ChcVar],
    grid: &[SmtValue],
) -> Option<(SmtValue, SmtValue)> {
    for g0 in grid {
        for g1 in grid {
            let mut pt = Model::default();
            pt.insert(kept[0].name.clone(), g0.clone());
            pt.insert(kept[1].name.clone(), g1.clone());
            if holds(psi, &pt) != Some(true) {
                continue;
            }
            let subst: Vec<(ChcVar, ChcExpr)> = kept
                .iter()
                .map(|k| {
                    let e = match &pt[&k.name] {
                        SmtValue::Int(n) => ChcExpr::Int(*n),
                        SmtValue::Real(r) => ChcExpr::Real(
                            num_traits::ToPrimitive::to_i64(r.numer()).expect("small"),
                            num_traits::ToPrimitive::to_i64(r.denom()).expect("small"),
                        ),
                        other => panic!("{other:?}"),
                    };
                    (k.clone(), e)
                })
                .collect();
            if extends(phi, &subst) == Some(false) {
                return Some((g0.clone(), g1.clone()));
            }
        }
    }
    None
}

fn run_random(real: bool, seed: u64, cases: usize) -> RunSummary {
    let mk = |n: &str| if real { rvar(n) } else { ivar(n) };
    let kept = vec![mk("k0"), mk("k1")];
    let elim = vec![mk("e0"), mk("e1"), mk("e2")];
    let all: Vec<ChcVar> = kept.iter().chain(elim.iter()).cloned().collect();
    let use_z3 = z3_available();
    let mut rng = Rng(seed);
    let mut done = RunSummary {
        cases: 0,
        stats: ExactStats::default(),
        substituted: 0,
        z3_checked: 0,
        legacy_over: 0,
    };
    let value = |rng: &mut Rng| -> SmtValue {
        if real {
            real_val(rng.range(-8, 8), 2)
        } else {
            SmtValue::Int(i128::from(rng.range(-6, 6)))
        }
    };
    let mut attempts = 0;
    while done.cases < cases && attempts < cases * 50 {
        attempts += 1;
        let n = rng.range(3, 6) as usize;
        let phi = ChcExpr::and_all((0..n).map(|_| random_literal(&mut rng, &all, real)));
        // Find a model by sampling.
        let mut model = None;
        for _ in 0..400 {
            let m: Model = all
                .iter()
                .map(|x| (x.name.clone(), value(&mut rng)))
                .collect();
            if holds(&phi, &m) == Some(true) {
                model = Some(m);
                break;
            }
        }
        let Some(m) = model else { continue };
        let p = Mbp::new()
            .project_exact(&phi, &elim, &m)
            .expect("sampled models assign every variable");
        let what = format!("seed {seed} case {}: φ = {phi}", done.cases);
        assert_model_and_vars(&p.lits, &elim, &m, &what);
        let psi = ChcExpr::and_all(p.lits.clone());
        let legacy = Mbp::new().project(&phi, &elim, &m);
        // (iii) `ψ ⇒ ∃E. φ`: z3 decides the whole implication when it is on
        // PATH; otherwise the window check with the (bounded) in-crate solver.
        if use_z3 {
            match z3_under_approx(&p.lits, &phi, &kept, &elim) {
                Some(true) => done.z3_checked += 1,
                Some(false) => {
                    panic!("{what}\nψ = {psi}\nz3: ψ ∧ ∀E.¬φ is SAT (over-approximation)")
                }
                None => {}
            }
            if z3_under_approx(&legacy.collect_conjuncts_nontrivial(), &phi, &kept, &elim)
                == Some(false)
            {
                done.legacy_over += 1;
            }
        } else {
            let grid: Vec<SmtValue> = if real {
                (-8..=8).map(|k| real_val(k, 2)).collect()
            } else {
                (-7..=7).map(SmtValue::Int).collect()
            };
            if let Some((g0, g1)) = window_counterexample(&psi, &phi, &kept, &grid) {
                panic!("{what}\nψ = {psi}\nOVER-APPROXIMATION at k0={g0:?} k1={g1:?}");
            }
            if window_counterexample(&legacy, &phi, &kept, &grid).is_some() {
                done.legacy_over += 1;
            }
        }
        let s = p.stats;
        let t = &mut done.stats;
        t.unit_eq += s.unit_eq;
        t.nonunit_eq += s.nonunit_eq;
        t.bj_bounds += s.bj_bounds;
        t.lw_bounds += s.lw_bounds;
        t.one_sided += s.one_sided;
        t.diseq_splits += s.diseq_splits;
        t.ite_splits += s.ite_splits;
        t.div_literals += s.div_literals;
        t.bool_defs += s.bool_defs;
        done.substituted += p.substituted.len();
        done.cases += 1;
    }
    if !use_z3 {
        eprintln!("under_approx: z3 not on PATH — z3 differential skipped (window check ran)");
    }
    done
}

#[test]
fn random_lia_projections_under_approximate() {
    let r = run_random(false, 0x5eed_2026_0923, 150);
    assert!(
        r.cases >= 100,
        "too few satisfiable random cases: {}",
        r.cases
    );
    // Coverage: every rule fired on the sample.
    let s = r.stats;
    assert!(
        s.unit_eq > 0 && s.nonunit_eq > 0 && s.bj_bounds > 0,
        "{s:?}"
    );
    assert!(
        s.div_literals > 0 && s.diseq_splits > 0 && s.one_sided > 0,
        "{s:?}"
    );
    eprintln!(
        "LIA: {} cases, {:?}, substituted {}, z3-checked {}, legacy over-approximations {}",
        r.cases, s, r.substituted, r.z3_checked, r.legacy_over
    );
}

#[test]
fn random_lra_projections_under_approximate() {
    let r = run_random(true, 0xbeef_2026_0923, 120);
    assert!(
        r.cases >= 80,
        "too few satisfiable random cases: {}",
        r.cases
    );
    let s = r.stats;
    assert!(
        s.unit_eq > 0 && s.lw_bounds > 0 && s.diseq_splits > 0,
        "{s:?}"
    );
    eprintln!(
        "LRA: {} cases, {:?}, substituted {}, z3-checked {}, legacy over-approximations {}",
        r.cases, s, r.substituted, r.z3_checked, r.legacy_over
    );
}
