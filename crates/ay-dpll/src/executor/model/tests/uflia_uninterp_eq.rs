// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #uflia-uninterp-eq-recover: a UFLIA formula that asserts an uninterpreted-sort
//! variable equal to a UF application over LIA-constrained Int args must emit a
//! VALID `sat`, not degrade to `unknown`.
//!
//! ROOT CAUSE — verification-consumer models a `&mut T` carrier as an uninterpreted sort plus
//! a `(current, final, id)` constructor UF: `a == mk(a_current, a_final, a_id)`.
//! When the constructor's Int args carry a LIA constraint (`a_current < a_final`),
//! EUF model extraction assigned `a` and `mk(..)` DIFFERENT sort elements
//! (`@S!0` vs `@S!1`) even though the top-level equality forces them equal. The
//! model's own validation gate then ground-refuted the asserted equality and
//! degraded a genuine `sat` to `unknown` (the plain UFLIA path lacked the
//! post-extraction repair the AUFLIA array path has, and
//! `reunify_lia_values_across_euf_classes` only touches Int classes). This
//! blocked verification-consumer should_succeed `bug/682` + `final_borrows`, whose base
//! consistency check requires a `sat` model.
//!
//! FIX — `recover_uninterpreted_equalities_from_assertions` unifies the element
//! values of top-level asserted-equal uninterpreted-sort pairs after extraction,
//! and `evaluate_uninterpreted_app` reads an app's own committed
//! `term_values[term_id]` element ahead of the (stale) arg-keyed function table.
//! Sound/fail-closed: the strict validation gate re-checks every assertion, so a
//! repair that violated some other assertion would leave the verdict degraded
//! exactly as before — it can never admit a false `sat`.

use super::*;
use ay_frontend::parse;

fn solve(input: &str) -> (Executor, String) {
    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute succeeds");
    let verdict = outputs.into_iter().next().expect("a check-sat verdict");
    (exec, verdict)
}

/// A `sat` answer must never ship a model the executor's OWN evaluator refutes.
fn assert_sat_model_self_consistent(exec: &Executor, verdict: &str) {
    if verdict != "sat" {
        return;
    }
    let model = exec.last_model.as_ref().expect("sat retains its model");
    eval_memo_clear();
    for &assertion in &exec.ctx.assertions {
        let v = exec.evaluate_term(model, assertion);
        assert!(
            !matches!(v, EvalValue::Bool(false)),
            "sat shipped a model AY's own eval refutes (assertion -> {v:?})"
        );
    }
}

const MUT_REF_HEADER: &str = r#"
(set-logic UFLIA)
(declare-sort MR 0)
(declare-fun a () MR)
(declare-fun ac () Int)
(declare-fun af () Int)
(declare-fun aid () Int)
(declare-fun mk (Int Int Int) MR)
(declare-fun cur (MR) Int)
(declare-fun fin (MR) Int)
"#;

/// The minimized verification-consumer mut-ref base: `a == mk(ac, af, aid)` with a LIA
/// constraint on the args. Pre-fix AY returned `unknown` (the extracted model
/// gave `a` and `mk(..)` different sort elements, refuting the equality);
/// post-fix it is a valid `sat` (z3: sat).
#[test]
fn uflia_uninterp_eq_over_lia_args_emits_valid_sat() {
    let input = format!(
        "{MUT_REF_HEADER}\
         (assert (= ac 3))\
         (assert (< ac af))\
         (assert (= a (mk ac af aid)))\
         (check-sat)"
    );
    let (exec, verdict) = solve(&input);
    assert_eq!(verdict, "sat", "the base is satisfiable (z3: sat)");
    assert_sat_model_self_consistent(&exec, &verdict);
}

/// The full carrier base with both projections wired in, mirroring the
/// verification-consumer `bug/682` base-consistency check. The formula is satisfiable
/// (z3: sat). Historically AY's Int-UF projection extraction emitted an
/// INVALID interpretation for `fin` (committing `fin(a) = 2`, falsifying the
/// asserted `(= af (fin a))` since `af > 3`), and the independent model-check
/// gate soundly downgraded `sat` to `unknown` — the previous version of this
/// test pinned that downgrade and declared restoring a valid `sat` follow-up
/// work. That follow-up is `backfill_opaque_app_values_from_equalities` on the
/// UFLIA extract path (#uflia-opaque-app-backfill): the asserted defining
/// equality `af == fin(a)` now backfills the projection read with the
/// LIA-committed value, so the emitted model is self-consistent and the SAME
/// strict gate now VALIDATES a genuine `sat` (own-eval must be True — asserted
/// below, the strongest form).
#[test]
fn uflia_mut_ref_carrier_with_projections_emits_valid_sat() {
    let input = format!(
        "{MUT_REF_HEADER}\
         (assert (= ac 3))\
         (assert (< ac af))\
         (assert (= a (mk ac af aid)))\
         (assert (= ac (cur a)))\
         (assert (= af (fin a)))\
         (check-sat)"
    );
    let (exec, verdict) = solve(&input);
    assert_eq!(
        verdict, "sat",
        "the carrier base is satisfiable and the backfilled projection model \
         must validate (z3: sat)"
    );
    assert_sat_model_self_consistent(&exec, &verdict);
}

/// SOUNDNESS: the repair must NOT turn a genuinely UNSAT formula into `sat`.
/// The negated goal `not(ac < af)` contradicts the assumed `ac < af`, so the
/// obligation stays `unsat` (the verification-consumer `bug/682` goal check).
#[test]
fn uflia_mut_ref_goal_stays_unsat() {
    let input = format!(
        "{MUT_REF_HEADER}\
         (assert (= ac 3))\
         (assert (< ac af))\
         (assert (= a (mk ac af aid)))\
         (assert (= ac (cur a)))\
         (assert (= af (fin a)))\
         (assert (not (< ac af)))\
         (check-sat)"
    );
    let (_exec, verdict) = solve(&input);
    assert_eq!(verdict, "unsat", "the negated goal contradicts the premise");
}

/// SOUNDNESS: a genuinely inconsistent carrier (`cur(a) = 3` AND `cur(a) = 5`)
/// must stay `unsat` — the element-unification repair must not paper over a
/// real Int contradiction.
#[test]
fn uflia_mut_ref_inconsistent_projection_stays_unsat() {
    let input = format!(
        "{MUT_REF_HEADER}\
         (assert (= a (mk ac af aid)))\
         (assert (= (cur a) 3))\
         (assert (= (cur a) 5))\
         (check-sat)"
    );
    let (_exec, verdict) = solve(&input);
    assert_eq!(verdict, "unsat", "cur(a) cannot be both 3 and 5");
}

/// SOUNDNESS: a directly-contradicted equality/disequality over the carrier
/// (`a == mk(..)` AND `a != mk(..)`) must stay `unsat`.
#[test]
fn uflia_mut_ref_direct_disequality_stays_unsat() {
    let input = format!(
        "{MUT_REF_HEADER}\
         (assert (= a (mk ac af aid)))\
         (assert (not (= a (mk ac af aid))))\
         (check-sat)"
    );
    let (_exec, verdict) = solve(&input);
    assert_eq!(
        verdict, "unsat",
        "a cannot both equal and differ from mk(..)"
    );
}

/// Universe elements of uninterpreted sorts appear in the model ONLY as
/// sort-ascribed abstract values `(as @U!n U)` — never via `(declare-fun
/// @U!n () U)` headers. The SMT-LIB get-model response grammar (enforced by
/// Dolmen, the SMT-COMP Model-Validation validator) admits nothing but
/// define-fun forms inside the response, so a declare-fun header makes the
/// whole model unparseable (the QF_UFDT stream_processor ModelParsingError
/// class). Self-containment is carried by the standard instead: `@`-prefixed
/// symbols are abstract values (SMT-LIB 2.7) — distinguished fresh constants
/// of the ascribed sort needing no declaration.
#[test]
fn uninterpreted_universe_elements_are_ascribed_values_not_declared() {
    let (exec, verdict) = solve(
        "(set-logic QF_UF)\
         (declare-sort U 0)\
         (declare-fun p () U)\
         (declare-fun q () U)\
         (assert (distinct p q))\
         (check-sat)",
    );
    assert_eq!(verdict, "sat");
    let model = exec.model();
    // The response grammar has no declare-fun production: any occurrence is
    // an instant validator parse error on the ENTIRE model.
    assert!(
        !model.contains("(declare-fun"),
        "model must not contain declare-fun (unparseable as a get-model \
         response):\n{model}"
    );
    // p and q are distinct, so BOTH universe elements are used, and every use
    // must be the self-contained sort-ascribed abstract-value form: each
    // `@U!n` occurrence sits inside `(as @U!n U)`.
    for elem in ["@U!0", "@U!1"] {
        assert!(
            model.contains(&format!("(as {elem} U)")),
            "model must reference {elem} as a sort-ascribed abstract value:\n{model}"
        );
    }
    for (i, _) in model.match_indices("@U!") {
        assert!(
            model[..i].ends_with("(as "),
            "bare (unascribed) universe-element reference at byte {i} in \
             model:\n{model}"
        );
    }
}
