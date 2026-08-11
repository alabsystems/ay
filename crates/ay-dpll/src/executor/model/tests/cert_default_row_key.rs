// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #cert-default-row-key: an MBQI finite-table certificate whose certified
//! point set CONTAINS the all-zeros point must still print a model.
//!
//! DEFECT — `install_finite_table_model` / `install_default_row_model`
//! materialize a certified interpretation into `EufModel::function_tables` as
//! one row per certified point plus a SYNTHETIC trailing row carrying the
//! certified default. The default row's argument tuple used to be filler
//! (`vec!["0"; arity]`) on the theory that consumers read the last row
//! positionally as the `else` and never print its key as a condition.
//!
//! Three consumers do exactly that. A fourth — the printer's
//! dedup/consistency backstop (`output_format.rs`, #uf-one-int-lane) — reads
//! EVERY row as a genuine point, and MUST: for an EUF-EXTRACTED table the last
//! row IS a real point, and exempting it would reopen the U4_rand_24
//! wrong-printed-model class. So whenever a certified point landed on the
//! all-zeros key, the filler aliased it, the resolved table stopped being a
//! function, and the backstop correctly failed a PERFECTLY VALID model closed:
//!
//!   (error "model value for function f is not available: inconsistent
//!    function table for f: point (0) resolves to both -1 and 0")
//!
//! Downstream (deductive-checks) this degraded genuine `Counterexample` verdicts to
//! `Unknown`, blinding two unsound-control tests.
//!
//! FIX — upstream, backstop untouched at full strength: key the default row
//! one past the largest first coordinate of the certified point set. The
//! certified interpretation maps every UNLISTED point to `default`, so the row
//! is not merely non-colliding, it is TRUE read as a point. Every row of the
//! installed table is again a real point of the interpretation the solver
//! validated — the backstop's premise, restored rather than weakened.

use super::*;
use ay_frontend::parse;

/// Smallest formula that drives the CAP-1 finite-table certificate to a
/// certified counterexample point at ZERO: `n = 0` makes the guarded `forall`
/// vacuous, `k = 0` is the only admissible index, and `f(0) = -1` is the
/// certified point. Certified default is `0`.
const ZERO_POINT_CERTIFICATE: &str = "\
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-const n Int)
(declare-const k Int)
(assert (>= n 0))
(assert (forall ((i Int)) (=> (and (<= 0 i) (< i n)) (>= (f i) 0))))
(assert (and (<= 0 k) (< k (+ n 1))))
(assert (< (f k) 0))
(check-sat)
(get-model)
";

/// The same certificate with the counterexample point moved OFF the all-zeros
/// key. This never regressed; it is the narrowness pin proving the fix did not
/// change the already-working shape.
const NONZERO_POINT_CERTIFICATE: &str = "\
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-const n Int)
(declare-const k Int)
(assert (= n 1))
(assert (forall ((i Int)) (=> (and (<= 0 i) (< i n)) (>= (f i) 0))))
(assert (and (<= 0 k) (< k (+ n 1))))
(assert (< (f k) 0))
(check-sat)
(get-model)
";

/// The assertions of the certificate formulas, verbatim, for the replay check.
const ZERO_POINT_ASSERTIONS: &str = "\
(assert (>= n 0))
(assert (forall ((i Int)) (=> (and (<= 0 i) (< i n)) (>= (f i) 0))))
(assert (and (<= 0 k) (< k (+ n 1))))
(assert (< (f k) 0))
";

const NONZERO_POINT_ASSERTIONS: &str = "\
(assert (= n 1))
(assert (forall ((i Int)) (=> (and (<= 0 i) (< i n)) (>= (f i) 0))))
(assert (and (<= 0 k) (< k (+ n 1))))
(assert (< (f k) 0))
";

/// Run a script whose last two commands are `(check-sat)` `(get-model)`.
fn check_sat_and_get_model(input: &str) -> (String, String, String) {
    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute succeeds");
    let diagnostic = format!(
        "reason={:?}, origin={:?}, detail={:?}",
        exec.unknown_reason(),
        exec.unknown_origin(),
        exec.statistics().get_string("unknown.detail"),
    );
    let mut outputs = outputs.into_iter();
    let verdict = outputs.next().expect("a check-sat verdict");
    let model = outputs.next().expect("a get-model output");
    (verdict, model, diagnostic)
}

/// Strip the `(model ... )` wrapper, yielding the `define-fun` block so it can
/// be replayed as input. The printed model is only a witness if AY can read it
/// back, so this deliberately re-parses the EXACT printed bytes.
fn model_definitions(model: &str) -> &str {
    let inner = model
        .trim()
        .strip_prefix("(model")
        .unwrap_or_else(|| panic!("get-model did not print a model: {model}"));
    inner
        .trim_end()
        .strip_suffix(')')
        .expect("model block closes")
}

/// The load-bearing half of the regression: assert the PRINTED model actually
/// satisfies the original constraints, by replaying its `define-fun`s as
/// definitions alongside the untouched assertions. A table repaired by
/// inventing a value would be caught here, not just by the table's shape.
fn assert_printed_model_satisfies(model: &str, assertions: &str) {
    let replay = format!(
        "(set-logic UFLIA)\n{defs}\n{assertions}(check-sat)\n",
        defs = model_definitions(model),
    );
    let commands = parse(&replay).expect("printed model re-parses as input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("replay executes");
    if std::env::var_os("AY_DEBUG_CERT").is_some() {
        for &assertion in &exec.ctx.assertions {
            eprintln!(
                "CERT/default-row-replay-root: {assertion:?} {}",
                exec.format_term(assertion)
            );
        }
        eprintln!(
            "CERT/default-row-replay-unknown: reason={:?} origin={:?} detail={:?} gate={:?}",
            exec.unknown_reason(),
            exec.unknown_origin(),
            exec.statistics().get_string("unknown.detail"),
            exec.statistics().get_string("model_check_gate.quantified"),
        );
    }
    let verdict = outputs.into_iter().next().expect("a check-sat verdict");
    assert_eq!(
        verdict, "sat",
        "the PRINTED model does not satisfy the constraints it claims to \
         witness — replay said {verdict}\n{replay}"
    );
}

#[test]
fn certified_point_at_all_zeros_still_prints_a_consistent_table() {
    let (verdict, model, diagnostic) = check_sat_and_get_model(ZERO_POINT_CERTIFICATE);
    assert_eq!(verdict, "sat", "{diagnostic}");

    // The specific fail-closed message the aliased default row produced.
    assert!(
        !model.contains("inconsistent function table"),
        "a valid certified model was rejected as a non-function: {model}"
    );
    assert!(
        !model.contains("(error"),
        "get-model errored on a validated model: {model}"
    );

    // The certified interpretation is f(0) = -1 with default 0, so the
    // first-match ite chain the printer builds must name point 0 explicitly
    // and fall through to the default. This pins that the surviving table is
    // the CERTIFIED one, not a tie broken in the printer.
    let body = model.replace(['\n', ' '], "");
    assert!(
        body.contains("(ite(=x00)(-1)0)"),
        "printed body is not the certified interpretation (ite (= x0 0) -1 0): {model}"
    );

    assert_printed_model_satisfies(&model, ZERO_POINT_ASSERTIONS);
}

#[test]
fn certified_point_off_all_zeros_is_unchanged() {
    let (verdict, model, diagnostic) = check_sat_and_get_model(NONZERO_POINT_CERTIFICATE);
    assert_eq!(verdict, "sat", "{diagnostic}");
    assert!(
        !model.contains("(error"),
        "get-model errored on a validated model: {model}"
    );
    let body = model.replace(['\n', ' '], "");
    assert!(
        body.contains("(ite(=x01)(-1)0)"),
        "printed body is not the certified interpretation (ite (= x0 1) -1 0): {model}"
    );
    assert_printed_model_satisfies(&model, NONZERO_POINT_ASSERTIONS);
}
