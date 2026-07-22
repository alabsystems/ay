// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #mv-gate-reads-printed-dt — the independent model-check gate must
//! re-evaluate the EXACT constructor tree the model printer emits for a
//! datatype constant, so a printed recursive-datatype witness that structurally
//! falsifies an assertion is caught as `ModelViolates` (Sat → Unknown) instead
//! of shipping as `sat` with a Dolmen `E:bad-model` (division-voiding).
//!
//! ROOT CAUSE (SMT-COMP 2025 Model-Validation, QF_Datatypes) — the QF_DT lane
//! solves over an ABSTRACT internal model (`x1 = @nat!1`, opaque), which the
//! gate's `ModelView` reported verbatim, so any assertion over the printed
//! structure was `Unevaluable` (a monitored coverage gap) and the gate could
//! not refute it. Meanwhile the PRINTER materialised a concrete constructor
//! tree (`dt_egraph_value` / the legacy tester+EUF `resolve_dt_value`) that does
//! NOT jointly satisfy the assertions for mutually-recursive shapes
//! (nat/list/tree). The two Barrett instances below are genuinely sat (cvc5/z3
//! confirm a model exists), AY answers sat, but its printed reconstruction was
//! rejected by pinned Dolmen 0.8.1 (`E:bad-model`) — 2 ModelUnsat errors that
//! demoted AY below every 0-error solver.
//!
//! THE FIX — the gate now parses the value the printer will emit back into a gate
//! value and evaluates THAT, turning an unfaithful witness into an enforced
//! `ModelViolates`. AY withholds the model and answers `unknown` (0 points, 0
//! errors — non-voiding) rather than print a model it cannot itself verify under
//! the validator's structural selector-projection semantics.

use super::*;
use ay_frontend::parse;
use ay_model_check::{confirm_model, GateVerdict, ModelValue, ModelView};

/// Run `input` through the full executor pipeline and return the executor plus
/// the `check-sat` verdict.
fn solve(input: &str) -> (Executor, String) {
    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute succeeds");
    let verdict = outputs.into_iter().next().expect("a check-sat verdict");
    (exec, verdict)
}

/// PERMANENT SOUNDNESS INVARIANT — a `sat` answer must never ship a model the
/// independent gate ground-refutes. `unknown` (honest incapacity) is always
/// acceptable; `unsat` on a known-sat instance is never.
fn assert_never_ships_refuted_model(exec: &Executor, verdict: &str) {
    assert_ne!(
        verdict, "unsat",
        "these Barrett instances are genuinely sat (cvc5/z3 confirm a model); \
         AY must never answer unsat"
    );
    if verdict == "sat" {
        // A shipped `sat` must be a model the gate can re-check without refuting
        // it under the printed values (never `ModelViolates`).
        if let GateVerdict::ModelViolates { assertion } = exec.confirm_sat_with_independent_gate() {
            panic!(
                "sat shipped a self-refuted recursive-datatype model: the \
                 independent gate ground-falsified assertion {assertion:?} under \
                 the emitted witness (this is the E:bad-model / ModelUnsat bug)"
            );
        }
    }
}

/// The exact SMT-LIB body of the first voiding instance
/// (`.../typed/v1/typed_v1l80032.cvc.smt2`, set-info stripped).
const BARRETT_V1L80032: &str = r#"
(set-logic QF_DT)
(declare-datatypes ((nat 0)(list 0)(tree 0)) (((succ (pred nat)) (zero))
((cons (car tree) (cdr list)) (null))
((node (children list)) (leaf (data nat)))
))
(declare-fun x1 () nat)
(declare-fun x2 () list)
(declare-fun x3 () tree)
(assert (and (and (and (and (and (and (and (not ((_ is leaf) (ite ((_ is cons) (cons (ite ((_ is cons) x2) (car x2) (leaf zero)) null)) (car (cons (ite ((_ is cons) x2) (car x2) (leaf zero)) null)) (leaf zero)))) ((_ is node) (node x2))) (not (= (ite ((_ is cons) x2) (cdr x2) null) (ite ((_ is cons) (ite ((_ is node) x3) (children x3) null)) (cdr (ite ((_ is node) x3) (children x3) null)) null)))) ((_ is cons) (cons (ite ((_ is cons) (cons (ite ((_ is cons) (cons x3 null)) (car (cons x3 null)) (leaf zero)) (ite ((_ is node) (ite ((_ is cons) null) (car null) (leaf zero))) (children (ite ((_ is cons) null) (car null) (leaf zero))) null))) (car (cons (ite ((_ is cons) (cons x3 null)) (car (cons x3 null)) (leaf zero)) (ite ((_ is node) (ite ((_ is cons) null) (car null) (leaf zero))) (children (ite ((_ is cons) null) (car null) (leaf zero))) null))) (leaf zero)) null))) ((_ is zero) (ite ((_ is succ) zero) (pred zero) zero))) (not (= (cons x3 (cons (ite ((_ is cons) null) (car null) (leaf zero)) (ite ((_ is cons) (ite ((_ is node) (node (ite ((_ is node) x3) (children x3) null))) (children (node (ite ((_ is node) x3) (children x3) null))) null)) (cdr (ite ((_ is node) (node (ite ((_ is node) x3) (children x3) null))) (children (node (ite ((_ is node) x3) (children x3) null))) null)) null))) x2))) (not (= (leaf zero) (leaf (ite ((_ is leaf) (leaf (ite ((_ is succ) (ite ((_ is succ) (succ x1)) (pred (succ x1)) zero)) (pred (ite ((_ is succ) (succ x1)) (pred (succ x1)) zero)) zero))) (data (leaf (ite ((_ is succ) (ite ((_ is succ) (succ x1)) (pred (succ x1)) zero)) (pred (ite ((_ is succ) (succ x1)) (pred (succ x1)) zero)) zero))) zero))))) (not (= (succ x1) (ite ((_ is succ) (ite ((_ is leaf) x3) (data x3) zero)) (pred (ite ((_ is leaf) x3) (data x3) zero)) zero)))))
(check-sat)
"#;

/// The exact SMT-LIB body of the second voiding instance
/// (`.../typed/v2/typed_v2l50040.cvc.smt2`, set-info stripped). Here the printed
/// witness came from the LEGACY `resolve_dt_value` path: `x1 = (succ zero)` was
/// printed against `(not (= (succ zero) x1))`.
const BARRETT_V2L50040: &str = r#"
(set-logic QF_DT)
(declare-datatypes ((nat 0)(list 0)(tree 0)) (((succ (pred nat)) (zero))
((cons (car tree) (cdr list)) (null))
((node (children list)) (leaf (data nat)))
))
(declare-fun x1 () nat)
(declare-fun x2 () nat)
(declare-fun x3 () list)
(declare-fun x4 () list)
(declare-fun x5 () tree)
(declare-fun x6 () tree)
(assert (and (and (and (and (not (= (succ zero) x1)) (= x1 (ite ((_ is leaf) x6) (data x6) zero))) ((_ is leaf) x5)) (not ((_ is cons) x3))) (not ((_ is null) (cons x5 null)))))
(check-sat)
"#;

/// The Barrett obligation, common to both instances: never `unsat` (they are
/// genuinely sat — cvc5/z3 confirm), never a shipped refuted witness. A `sat`
/// is acceptable ONLY when the independent gate CONFIRMS the emitted model
/// (stronger than the helper's never-`ModelViolates`); `unknown` (honest
/// incapacity — 0 points, 0 errors, non-voiding) is always acceptable.
///
/// HISTORY: on the mv-printer branch both instances were withheld (`unknown`,
/// attributed to the printed-model `ModelViolates` arm). After the merge with
/// main's total-datatype-model construction (#dt-total-model) the pipeline can
/// materialize a faithful witness for some of these shapes and legitimately
/// answer `sat` — the pinned-arm expectation would reject that capability
/// improvement, so the pin is on the soundness obligation instead.
fn assert_barrett_obligation(exec: &Executor, verdict: &str) {
    assert_never_ships_refuted_model(exec, verdict);
    match verdict {
        "unknown" => {}
        "sat" => {
            assert!(
                matches!(
                    exec.confirm_sat_with_independent_gate(),
                    GateVerdict::ConfirmedSat
                ),
                "a Barrett `sat` must ship a witness the independent gate \
                 CONFIRMS (not merely fails to refute)"
            );
        }
        other => panic!("unexpected verdict {other:?} (sat-with-confirmed-model or unknown)"),
    }
}

/// v1 — the `dt_egraph_value` single-source path emitted `x1 = succ^3(zero)` plus
/// large cons/node trees for x2/x3 that Dolmen evaluates false. The backstop must
/// withhold any refuted witness; see [`assert_barrett_obligation`].
#[test]
fn barrett_v1l80032_withholds_unfaithful_recursive_model() {
    let (exec, verdict) = solve(BARRETT_V1L80032);
    assert_barrett_obligation(&exec, &verdict);
}

/// v2 — the LEGACY `resolve_dt_value` path emitted `x1 = (succ zero)` against
/// `(not (= (succ zero) x1))`. The gate must re-check the printed value; a
/// gate-confirmed faithful witness is the improved outcome.
#[test]
fn barrett_v2l50040_withholds_unfaithful_recursive_model() {
    let (exec, verdict) = solve(BARRETT_V2L50040);
    assert_barrett_obligation(&exec, &verdict);
}

// ==========================================================================
// Synthetic mutually-recursive-datatype faithfulness — the parse+gate core
// ==========================================================================

/// A [`ModelView`] pinning ONE datatype leaf to a caller-supplied value, with the
/// datatype registry resolved from the executor. It exercises the exact
/// composition the backstop relies on: parse the printed value, then let the gate
/// evaluate every assertion structurally over it.
struct SingleLeafView<'a> {
    exec: &'a Executor,
    var: TermId,
    value: ModelValue,
}

impl ModelView for SingleLeafView<'_> {
    fn leaf_value(&self, t: TermId) -> Option<ModelValue> {
        if t == self.var {
            Some(self.value.clone())
        } else {
            None
        }
    }
    fn datatype_def(&self, name: &str) -> Option<ay_core::DatatypeSort> {
        self.exec.dt_registry_lookup(name)
    }
}

/// Parse only (no check-sat) to populate the datatype registry, term store, and
/// assertion set, then return the executor plus the single declared leaf `x`.
fn parse_mutual_dt(input: &str) -> (Executor, TermId) {
    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("execute succeeds");
    let x = exec
        .ctx
        .symbol_iter()
        .find(|(n, _)| *n == "x")
        .and_then(|(_, i)| i.term)
        .expect("x declared");
    (exec, x)
}

const MUTUAL_DT_PROBLEM: &str = r#"
(set-logic QF_DT)
(declare-datatypes ((nat 0)(list 0)(tree 0)) (((succ (pred nat)) (zero))
((cons (car tree) (cdr list)) (null))
((node (children list)) (leaf (data nat)))
))
(declare-fun x () list)
(assert (not (= x (cons (leaf zero) null))))
(check-sat)
"#;

/// The gate REFUTES a printed value that equals the excluded mutually-recursive
/// tree, and CONFIRMS one that differs — the core of the fail-closed backstop.
#[test]
fn gate_refutes_wrong_printed_recursive_dt_value() {
    let (exec, x) = parse_mutual_dt(MUTUAL_DT_PROBLEM);
    let sort = exec.ctx.terms.sort(x).clone();

    // WRONG: the printer emits exactly the excluded value → `(not (= x it))`
    // is false → the gate must refute.
    let wrong = exec
        .parse_rendered_dt_value("(cons (leaf zero) null)", &sort)
        .expect("well-formed mutually-recursive constructor tree parses");
    let view = SingleLeafView {
        exec: &exec,
        var: x,
        value: wrong,
    };
    match confirm_model(&exec.ctx.terms, &view, &exec.ctx.assertions) {
        GateVerdict::ModelViolates { .. } => {}
        other => {
            panic!("the gate must REFUTE a printed value equal to the excluded tree; got {other:?}")
        }
    }

    // RIGHT: a different tree satisfies `(not (= x it))` → the gate confirms.
    let right = exec
        .parse_rendered_dt_value("(cons (leaf (succ zero)) null)", &sort)
        .expect("well-formed constructor tree parses");
    let view = SingleLeafView {
        exec: &exec,
        var: x,
        value: right,
    };
    match confirm_model(&exec.ctx.terms, &view, &exec.ctx.assertions) {
        GateVerdict::ConfirmedSat => {}
        other => panic!("the gate must CONFIRM a satisfying printed value; got {other:?}"),
    }
}

/// `parse_rendered_dt_value` round-trips a nested mutually-recursive constructor
/// tree into the right gate value, and fails CLOSED (returns `None`) on a token
/// that is not a declared constructor.
#[test]
fn parse_rendered_dt_value_handles_mutual_recursion_and_fails_closed() {
    let (exec, x) = parse_mutual_dt(MUTUAL_DT_PROBLEM);
    let list_sort = exec.ctx.terms.sort(x).clone();

    // (cons (node (cons (leaf (succ zero)) null)) null)
    let v = exec
        .parse_rendered_dt_value(
            "(cons (node (cons (leaf (succ zero)) null)) null)",
            &list_sort,
        )
        .expect("nested nat/list/tree tree parses");
    match &v {
        ModelValue::Datatype { ctor, args } => {
            assert_eq!(ctor, "cons");
            assert_eq!(args.len(), 2, "cons has car:tree and cdr:list");
            // cdr = null
            assert!(matches!(&args[1], ModelValue::Datatype { ctor, args }
                if ctor == "null" && args.is_empty()));
            // car = (node (cons (leaf (succ zero)) null))
            assert!(matches!(&args[0], ModelValue::Datatype { ctor, .. } if ctor == "node"));
        }
        other => panic!("expected a cons Datatype value; got {other:?}"),
    }

    // A bare nullary constructor.
    assert!(matches!(
        exec.parse_rendered_dt_value("null", &list_sort),
        Some(ModelValue::Datatype { ref ctor, ref args }) if ctor == "null" && args.is_empty()
    ));

    // Fail closed: `bogus` is not a constructor of `list`.
    assert!(
        exec.parse_rendered_dt_value("(bogus null)", &list_sort)
            .is_none(),
        "an unknown head must fail closed (None), never fabricate a value"
    );
    // Fail closed: wrong arity for cons (declared 2 fields).
    assert!(
        exec.parse_rendered_dt_value("(cons null)", &list_sort)
            .is_none(),
        "a constructor-arity mismatch must fail closed"
    );
    // Fail closed: trailing garbage after a complete value.
    assert!(
        exec.parse_rendered_dt_value("null null", &list_sort)
            .is_none(),
        "trailing tokens after one value must fail closed"
    );
}
