// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! The 2026-09-25 verify of the quantifier repair (D1, D11, D10(b)), pinned
//! corpus-free on top of [`crate::hunt_quantifier_wrong_verdicts`].
//!
//! - B1: the first exact elimination read a binder under a NESTED quantifier
//!   as a constant and refuted valid universals (a new wrong `unsat`).
//! - M3: the gcd test kept the numeral inside a product of symbols, so `4wz +
//!   1` could vanish.
//! - B3: a symbol the elimination removed had no model value after `sat`
//!   (an unused ARRAY's value: [`crate::hunt_quantifier_unused_array_model`]).
//! - D1: the certificate's carried universe and the gate's own check, each on
//!   an input where MBQI's instances do not name the carried element.

use crate::hunt_quantifier_wrong_verdicts::{assert_never, solve, verdicts, Posture, POSTURES};

/// Universals whose binder also occurs under a NESTED quantifier inside the
/// coefficient (2026-09-25 verify of the D11 repair, B1). The first exact
/// elimination checked affinity with helpers that do not enter a `forall` /
/// `exists`, so the `v` below `∃u` read as a constant: in the first fixture
/// `v·(1 + 2·ite(∃u. u ≥ 0 ∧ u = v, 1, −1))` is `3v` for `v ≥ 0` and `−v`
/// below — always `≥ 0` — and the universal was rewritten to `false`. Every
/// fixture is satisfiable (z3 5.1.0 `sat`); the repair's tip d9fc10ccae
/// answered `unsat` in `--z3-mode` on each (the witness, the verifier's
/// ground-constant and disjunction variants, the UF-argument variant, and
/// the generator's `b1_61830_*` / `nq_61820_00094` shapes: a nested
/// `forall`, an `exists`, a negated `exists`, an implication, a conjunct
/// beside the atom, a coefficient that folds to a never-zero numeral).
const D11_NESTED_BINDER_SAT: [(&str, &str); 11] = [
    (
        "witness: ite over an exists in the coefficient",
        "(set-logic ALL)
         (assert (forall ((v Int)) (>= (* v (+ 1 (* 2 (ite (exists ((u Int)) (and (>= u 0) (= u v))) 1 (- 1))))) 0)))
         (check-sat)",
    ),
    (
        "ground constant in the rest",
        "(set-logic ALL) (declare-fun a () Int)
         (assert (forall ((v Int)) (>= (+ a (* v (- (* 2 (ite (exists ((u Int)) (and (>= u 0) (= u v))) 1 0)) 1))) 0)))
         (assert (>= a 0)) (check-sat)",
    ),
    (
        "the universal inside a disjunction",
        "(set-logic ALL) (declare-fun a () Int)
         (assert (or (> a 5) (forall ((v Int)) (>= (* v (+ 1 (* 2 (ite (exists ((u Int)) (and (>= u 0) (= u v))) 1 (- 1))))) 0))))
         (assert (< a 3)) (check-sat)",
    ),
    (
        "the nested quantifier under a UF argument",
        "(set-logic ALL) (declare-fun f (Bool) Int)
         (assert (= (f true) 1)) (assert (= (f false) (- 1)))
         (assert (forall ((v Int)) (>= (* v (+ 1 (* 2 (f (exists ((u Int)) (and (>= u 0) (= u v))))))) 0)))
         (check-sat)",
    ),
    (
        "a let-bound coefficient",
        "(set-logic ALL)
         (assert (forall ((v Int)) (let ((s (ite (exists ((u Int)) (and (>= u 0) (= u v))) 1 (- 1))))
           (>= (* v (+ 1 (* 2 s))) 0))))
         (check-sat)",
    ),
    (
        "b1_61830_00016: a nested forall",
        "(set-logic ALL) (declare-fun a () Int) (declare-fun p (Int) Bool)
         (assert (forall ((v Int)) (>= 0 (+ a (* (+ (- 1) (* 2 (ite (forall ((u Int)) (or (not (= u v)) (>= u 0))) 0 1))) v)))))
         (assert (>= a 0)) (check-sat)",
    ),
    (
        "b1_61830_00018: an exists, beside a predicate conjunct",
        "(set-logic ALL) (declare-fun a () Int) (declare-fun p (Int) Bool)
         (assert (forall ((v Int)) (and (<= (+ (* v (+ (- 1) (* 3 (ite (exists ((u Int)) (and (<= u 0) (= v u))) 1 0)))) (- a)) 1) (p v))))
         (assert (= a 0)) (check-sat)",
    ),
    (
        "b1_61830_00060: a negated exists",
        "(set-logic ALL) (declare-fun a () Int) (declare-fun p (Int) Bool)
         (assert (forall ((v Int)) (and (<= (+ (* v (+ 3 (* (- 2) (ite (not (exists ((u Int)) (and (< u 0) (= u v)))) 2 (- 1))))) (+ a 1)) 1) (>= a 0))))
         (check-sat)",
    ),
    (
        "b1_61830_00077: an implication under forall",
        "(set-logic ALL) (declare-fun a () Int) (declare-fun p (Int) Bool)
         (assert (forall ((v Int)) (>= (+ (* v (+ (- 1) (* 4 (ite (forall ((u Int)) (=> (< u 2) (< u v))) 1 0)))) (+ a 1)) (- 1))))
         (assert (<= a 0)) (check-sat)",
    ),
    (
        "nq_61820_00094: an ite coefficient that is never zero",
        "(set-logic ALL) (declare-fun a () Int) (declare-fun b () Int) (declare-fun w () Int)
         (declare-fun p (Int) Bool)
         (assert (forall ((v Int)) (<= (+ (* v (ite (forall ((u Int)) (=> (< u (- 1)) (< u v))) (- 3) 3)) b) (- 3))))
         (assert (p 2)) (assert (= w 0)) (check-sat)",
    ),
    (
        "a dropped disjunct over a nested quantifier",
        "(set-logic ALL) (declare-fun q () Bool)
         (assert (forall ((v Int)) (or (= (* v (+ 1 (* 2 (ite (exists ((u Int)) (and (>= u 0) (= u v))) 1 (- 1))))) 0) q)))
         (assert q) (check-sat)",
    ),
];

/// A symbolic coefficient that is a PRODUCT of free symbols and never
/// vanishes: `4wz + 1` is odd. The gcd test used to keep the numeral inside
/// the product atom (`(* 4 w z)` with coefficient 1), so it could not see
/// that; the universal is false whatever `w` and `z` are (z3 5.1.0 `unsat`).
const D11_PRODUCT_COEFFICIENT_UNSAT: &str = r#"
(set-logic ALL)
(declare-fun w () Int)
(declare-fun z () Int)
(assert (forall ((v Int)) (<= (* v (+ (* 4 w z) 1)) 7)))
(check-sat)
"#;

/// The elimination removes `z` from the only assertion: `∀v. v·w = 0 ∨
/// 2v + z = 1` is `w = 0` (the second disjunct holds at no more than one
/// `v`). The repair's tip answered `sat` with `confirmed-sat` in `--z3-mode`
/// and then `(error "model value for z is not available (internal error: sat
/// accepted without a total model)")` (2026-09-25 verify, B3).
const D11_ELIMINATED_SYMBOL_MODEL: &str = r#"
(set-logic ALL)
(declare-fun w () Int)
(declare-fun z () Int)
(assert (forall ((v Int)) (or (= (* v w) 0) (= (+ (* 2 v) z) 1))))
(check-sat)
(get-model)
(get-value (z w))
"#;

/// The elimination leaves `p` in the rewritten formula (`(= 0 (+ (- (ite p 0
/// 2)) 1))`), and the ground simplification then folds it away: the model
/// had no value for `p` and `(get-model)` failed (fresh-seed family file
/// w1_62501_00208, `--z3-mode`; main answers `unknown`, z3 5.1.0 `sat`).
const D11_FOLDED_SYMBOL_MODEL: &str = r#"
(set-logic ALL)
(declare-fun w () Int)
(declare-fun a () Int)
(declare-fun f (Int) Int)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun A () (Array Int Int))
(assert (forall ((v Int)) (or (= (+ (* v (ite p 0 2)) (* (- 1) v) (f a)) a) (> a 3))))
(assert q)
(assert (= (select A a) 0))
(check-sat)
(get-model)
(get-value (p))
"#;

/// Fresh-seed family file w1_62501_00322 (z3 5.1.0 `unsat`): main refutes the
/// first universal by instantiation (`v = −1` leaves `0 < 0`); the exact
/// elimination rewrote it to `∀v.(f(v) ≠ v ∧ f(a) < 0 ∧ f(a) = 0)`, which the
/// quantified pipeline left `unknown` in `--z3-mode` (2026-09-25 fix-up,
/// deterministic). The coefficient `f(a)` vanishing leaves the rest `f(a) <
/// 0` false, so the conjunct refutes its universal outright.
const D11_VANISHING_FALSIFIES_REST_UNSAT: &str = r#"
(set-logic ALL)
(declare-fun w () Int)
(declare-fun a () Int)
(declare-fun f (Int) Int)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun A () (Array Int Int))
(assert (forall ((v Int)) (and (< (+ (* v (f a)) (f a)) 0) (not (= (f v) v)))))
(assert (forall ((v Int)) (or (= (+ (* (* 2 w) v) (f a)) 4) (> a 3))))
(assert (not q))
(check-sat)
"#;

/// The elimination removes the only application of `h` (a function over an
/// uninterpreted sort): `∀v. v·w = 0 ∨ 2v + h(s) = 1` is `w = 0`. The model
/// gave `h` no interpretation, the printer omitted it (`c ay.model.partial`)
/// and `(get-value ((h s)))` failed in `--z3-mode`, where main printed `h`
/// (2026-09-25 fix-up, session 2: B3 for functions).
const D11_ELIMINATED_FUNCTION_MODEL: &str = r#"
(set-logic ALL)
(declare-sort S 0)
(declare-fun h (S) Int)
(declare-fun w () Int)
(declare-const s S)
(assert (forall ((v Int)) (or (= (* v w) 0) (= (+ (* 2 v) (h s)) 1))))
(check-sat)
(get-model)
(get-value ((h s) w))
"#;

/// Fresh-seed family file w1_62501_00174: `f` survives only in a vanishing
/// case the simplification folds away; main printed `f`, the fix-up's
/// `--z3-mode` model omitted it.
const D11_FOLDED_FUNCTION_MODEL: &str = r#"
(set-logic ALL)
(declare-fun w () Int)
(declare-fun a () Int)
(declare-fun f (Int) Int)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun A () (Array Int Int))
(assert (forall ((v Int)) (or (= (+ (* v (f a)) (* 2 v) 0) 1) q)))
(assert (forall ((v Int)) (or (= (+ (* (mod w 3) v) (* 2 v) 0) a) q)))
(assert p)
(assert (= (select A a) 0))
(check-sat)
(get-model)
(get-value ((f a)))
"#;

#[test]
fn d11_a_vanishing_coefficient_that_falsifies_the_rest_refutes() {
    let name = "w1_62501_00322";
    assert_never(name, D11_VANISHING_FALSIFIES_REST_UNSAT, "sat");
    let got = solve(D11_VANISHING_FALSIFIES_REST_UNSAT, Posture::Z3Mode, None);
    assert_eq!(
        verdicts(&got),
        ["unsat"],
        "{name}: main refutes it in --z3-mode (z3 5.1.0 unsat); got {got:?}"
    );
}

#[test]
fn d11_binder_under_a_nested_quantifier_is_never_unsat() {
    for (name, smt) in D11_NESTED_BINDER_SAT {
        assert_never(name, smt, "unsat");
    }
}

/// The gcd test reads the coefficient as a polynomial, so a product of free
/// symbols keeps its numeral: `4wz + 1` never vanishes and the universal is
/// refuted like a numeral coefficient's.
#[test]
fn d11_product_coefficient_that_never_vanishes_refutes() {
    assert_never("4wz + 1", D11_PRODUCT_COEFFICIENT_UNSAT, "sat");
    let got = solve(D11_PRODUCT_COEFFICIENT_UNSAT, Posture::Z3Mode, None);
    assert_eq!(
        verdicts(&got),
        ["unsat"],
        "the coefficient 4wz + 1 is odd, never 0; got {got:?}"
    );
}

/// A symbol the elimination removes from every assertion still gets a model
/// value, and the gate never confirms a model without one: every `sat`
/// prints a total model, and `--z3-mode` (where the elimination runs) stays
/// `sat`.
#[test]
fn d11_a_symbol_the_elimination_removes_keeps_a_model_value() {
    for (name, smt, symbol) in [
        (
            "removed by the elimination",
            D11_ELIMINATED_SYMBOL_MODEL,
            "z",
        ),
        ("folded away after it", D11_FOLDED_SYMBOL_MODEL, "p"),
        (
            "function removed by the elimination",
            D11_ELIMINATED_FUNCTION_MODEL,
            "h",
        ),
        (
            "function folded away after it",
            D11_FOLDED_FUNCTION_MODEL,
            "f",
        ),
    ] {
        for posture in POSTURES {
            let got = solve(smt, posture, None);
            if verdicts(&got) != ["sat"] {
                assert!(
                    !matches!(posture, Posture::Z3Mode),
                    "{name}: the universal holds with {symbol} unconstrained \
                     ({posture:?}); got {got:?}"
                );
                continue;
            }
            let text = got.join("\n");
            assert!(
                !text.contains("(error"),
                "{name}: a `sat` must print a total model ({posture:?}); got {got:?}"
            );
            assert!(
                text.contains(&format!("define-fun {symbol} "))
                    && text.contains(&format!("(({symbol} ")),
                "{name}: {symbol} needs a model value and a get-value answer ({posture:?}); \
                 got {got:?}"
            );
        }
    }
}

/// Carried elements MBQI's instances do not name: a `U` element inside an
/// array or a sequence field (the candidate walk follows datatype fields
/// only), and one reached through a `U -> W` function (`(f u)` is a carrier
/// whose field the model's constructor, not a ground term, supplies). Each is
/// unsat (z3 5.1.0), and with instantiation unable to refute it the
/// finite-universe certificate is the first line: it must decline a universe
/// it cannot name rather than hand the gate a certificate to withdraw.
const D1_UNNAMED_CARRIED_ELEMENTS: [(&str, &str); 3] = [
    (
        "a U element inside an array field",
        "(set-logic ALL) (declare-sort U 0)
         (declare-datatypes ((W 0)) (((w (g (Array Int U))) (w2))))
         (declare-const u0 U) (declare-const a W) (declare-const b W)
         (assert (distinct a b)) (assert ((_ is w) a)) (assert ((_ is w) b))
         (assert (forall ((x U)) (= x u0))) (check-sat)",
    ),
    (
        "U elements inside a sequence field",
        "(set-logic ALL) (declare-sort U 0)
         (declare-datatypes ((W 0)) (((w (g (Seq U))) (w2))))
         (declare-const u0 U) (declare-const a W) (declare-const b W)
         (assert (distinct a b)) (assert ((_ is w) a)) (assert ((_ is w) b))
         (assert (= (seq.len (g a)) 1)) (assert (= (seq.len (g b)) 1))
         (assert (forall ((x U)) (= x u0))) (check-sat)",
    ),
    (
        "a carrier reached through f : U -> W",
        "(set-logic ALL) (declare-sort U 0)
         (declare-datatypes ((W 0)) (((w (g U)) (w2))))
         (declare-const u U) (assert (forall ((x U)) (= x u)))
         (declare-fun f (U) W) (declare-const a0 W)
         (assert (distinct (f u) a0 w2)) (check-sat)",
    ),
];

/// Satisfiable twins the certificate reaches only by naming selector terms
/// as universe elements (main's certificate declined on any `U`-valued
/// application, `(g a1)` included).
const D1_SELECTOR_UNIVERSE_SAT: [(&str, &str); 2] = [
    (
        "a predicate universal pinned at a selector term",
        "(set-logic ALL) (declare-sort U 0)
         (declare-datatypes ((W 0)) (((w (g U)) (w2))))
         (declare-fun P (U) Bool) (declare-const a0 W) (declare-const a1 W)
         (assert (forall ((x U)) (P x))) (assert (distinct a0 a1 w2))
         (assert (P (g a1))) (check-sat)",
    ),
    (
        "a selector term inside the universal's body",
        "(set-logic ALL) (declare-sort U 0)
         (declare-datatypes ((W 0)) (((w (g U)) (w2))))
         (declare-const u0 U) (declare-const a0 W) (declare-const a1 W) (declare-const a2 W)
         (assert (distinct a0 a1 a2))
         (assert (forall ((x U)) (or (= x u0) (= x (g a0))))) (check-sat)",
    ),
];

/// UF-valued carriers `h : Int -> W` / `h : Bool -> W` with `|U| = 1` and
/// three distinct `W` values: unsat (z3 5.1.0). In `--z3-mode` the
/// certificate grants here (the solver's evaluator follows `(h 1)`'s
/// constructor, the independent one cannot), so only the gate's own check of
/// the carried universe stands between the certificate and the answer.
const D1_UF_VALUED_CARRIERS: [(&str, &str); 2] = [
    (
        "h : Int -> W",
        "(set-logic ALL) (declare-sort U 0)
         (declare-datatypes ((W 0)) (((w (g U)) (w2))))
         (declare-const u U) (assert (forall ((x U)) (= x u)))
         (declare-fun h (Int) W) (assert (distinct (h 1) (h 2) (h 3))) (check-sat)",
    ),
    (
        "h : Bool -> W",
        "(set-logic ALL) (declare-sort U 0)
         (declare-datatypes ((W 0)) (((w (g U)) (w2))))
         (declare-const u U) (assert (forall ((x U)) (= x u)))
         (declare-fun h (Bool) W) (declare-const a0 W)
         (assert (distinct (h true) (h false) a0)) (check-sat)",
    ),
];

/// Verdicts and the quantified gate's label (`model_check_gate.quantified`).
fn solve_with_gate_label(smt: &str, posture: Posture) -> (Vec<String>, Option<String>) {
    let commands = ay_frontend::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = ay_dpll::Executor::new();
    if matches!(posture, Posture::Z3Mode) {
        exec.set_competition_mode(true);
    }
    let mut output = Vec::new();
    for command in &commands {
        if let Some(line) = exec
            .execute_authored(command)
            .unwrap_or_else(|err| panic!("execution failed: {err}"))
        {
            output.push(line);
        }
    }
    let label = exec
        .statistics()
        .get_string("model_check_gate.quantified")
        .map(str::to_string);
    (output, label)
}

/// The certificate's own carried universe (D1): where no instance names a
/// carried element, the certificate declines, so the gate never has to
/// withdraw a certificate it was handed — and it certifies the twins whose
/// universe includes selector terms.
#[test]
fn d1_certificate_declines_a_carried_universe_it_cannot_name() {
    for (name, smt) in D1_UNNAMED_CARRIED_ELEMENTS {
        for posture in [Posture::Authored, Posture::Z3Mode] {
            let (got, label) = solve_with_gate_label(smt, posture);
            assert!(
                !verdicts(&got).contains(&"sat"),
                "WRONG VERDICT ({name}, {posture:?}): z3 5.1.0 answers unsat; got {got:?}"
            );
            assert!(
                !matches!(
                    label.as_deref(),
                    Some("carried-universe-failclosed" | "refuted-carried-universe")
                ),
                "{name} ({posture:?}): the certificate itself must decline a carried \
                 universe it cannot name; the gate had to withdraw it ({label:?})"
            );
        }
    }
    for (name, smt) in D1_SELECTOR_UNIVERSE_SAT {
        assert_never(name, smt, "unsat");
        for posture in [Posture::Authored, Posture::Z3Mode] {
            let got = solve(smt, posture, None);
            assert_eq!(
                verdicts(&got),
                ["sat"],
                "{name} ({posture:?}): z3 5.1.0 answers sat; got {got:?}"
            );
        }
    }
}

/// The gate's own check (D1): a certificate over a sort that datatype values
/// carry is not taken on its word — the gate names the emitted model's
/// universe itself and, unable to follow a UF-valued carrier, fails closed.
#[test]
fn d1_gate_checks_a_certified_carried_universe_itself() {
    for (name, smt) in D1_UF_VALUED_CARRIERS {
        assert_never(name, smt, "sat");
        let (got, label) = solve_with_gate_label(smt, Posture::Z3Mode);
        assert!(
            !verdicts(&got).contains(&"sat"),
            "WRONG VERDICT ({name}): z3 5.1.0 answers unsat; got {got:?}"
        );
        assert_eq!(
            label.as_deref(),
            Some("carried-universe-failclosed"),
            "{name}: the certificate grants here, and the gate must check the carried \
             universe itself rather than take its word (if the certificate now \
             declines, move this pin to an input where it still grants); got {got:?}"
        );
    }
}
