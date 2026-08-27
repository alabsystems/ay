// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Printed-UF reconciliation tests included in `independent_gate::tests` so
// their fully-qualified test names remain stable.

// -----------------------------------------------------------------------
// #g3-gate-reads-printed-uf — RECONCILED read of the published UF
// interpretation (`IndependentModelView::uf_app_value_at`).
//
// These forge the model directly (no `check-sat`), so each pair below
// holds the FORMULA and the CODE PATH fixed and varies only the model —
// the same non-vacuity bar as `forall_exists_witness_route_confirm_is_model_sensitive`.
// The end-to-end positive cases live in `executor_tests/smt/qf_uflia.rs`
// (`test_clearsy_00302_prefix_first_query_is_sat`,
// `test_clearsy_00307_printed_uf_interpretation_queries_are_sat`).
// -----------------------------------------------------------------------

/// [`synthetic_euf_model`] plus the `function_tables` rows `(get-model)`
/// prints (last row = `else` branch).
#[cfg(test)]
fn synthetic_euf_model_with_tables(
    term_values: &[(TermId, &str)],
    function_tables: &[(&str, &[(&[&str], &str)])],
) -> Model {
    let mut model = synthetic_euf_model(term_values);
    let euf = model.euf_model.as_mut().expect("euf model just installed");
    for &(f, rows) in function_tables {
        euf.function_tables.insert(
            f.to_string(),
            rows.iter()
                .map(|(args, v)| (args.iter().map(|a| a.to_string()).collect(), v.to_string()))
                .collect(),
        );
    }
    model
}

const G3_UNLISTED_POINT_PREFIX: &str = "(set-logic QF_UF)\
         (declare-sort U 0)\
         (declare-fun mem (U U) Bool)\
         (declare-fun bool (Bool) U)\
         (declare-fun a () U)\
         (declare-fun s () U)\
         (assert (mem a s))";

/// Load [`G3_UNLISTED_POINT_PREFIX`] plus `extra_assertion` and publish a
/// model in which `(mem (bool true) s)` is an UNPINNED application at an
/// argument point the `mem` table does not list:
///
///     (define-fun bool ((x0 Bool)) U (as @U!2 U))
///     (define-fun mem ((x0 U) (x1 U)) Bool
///       (ite (and (= x0 (as @U!0 U)) (= x1 (as @U!1 U))) true false))
///
/// so the printed interpretation answers `false` at `(mem @U!2 @U!1)`.
#[cfg(test)]
fn g3_unlisted_point_gate(extra_assertion: &str) -> Executor {
    let mut exec = loaded(&format!("{G3_UNLISTED_POINT_PREFIX}{extra_assertion}"));
    let u = Sort::Uninterpreted("U".to_string());
    let a = exec.ctx.terms.mk_var("a", u.clone());
    let s = exec.ctx.terms.mk_var("s", u);
    exec.last_model = Some(synthetic_euf_model_with_tables(
        &[(a, "@U!0"), (s, "@U!1")],
        &[
            (
                "mem",
                &[(&["@U!0", "@U!1"], "true"), (&["@U!1", "@U!1"], "false")],
            ),
            ("bool", &[(&["true"], "@U!2")]),
        ],
    ));
    exec
}

/// POSITIVE: the unlisted point reads the printed `else` branch (`false`),
/// so `(not (mem (bool true) s))` holds and the gate CONFIRMS — the
/// completeness gap class C of
/// the development design notes, which returned
/// `CannotConfirm` ("model commits no value for this application") before
/// this patch.
#[test]
fn g3_unlisted_uf_point_reads_printed_else_branch() {
    let exec = g3_unlisted_point_gate("(assert (not (mem (bool true) s)))");
    assert!(
        matches!(
            exec.confirm_sat_with_independent_gate(),
            GateVerdict::ConfirmedSat
        ),
        "#g3-gate-reads-printed-uf: an application at an argument point the \
             table omits must be read from the PUBLISHED total interpretation"
    );
}

/// NEGATIVE CONTROL (the real one): the SAME model, and the assertion now
/// needs the unlisted point to be `true`. The printed interpretation says
/// `false` there, so the published witness falsifies the assertion and the
/// gate must REFUTE it — never confirm, never merely "cannot confirm". This
/// is the property that separates reading the published witness from
/// relaxing the gate.
#[test]
fn g3_unlisted_uf_point_printed_value_falsifying_assertion_is_refuted() {
    let exec = g3_unlisted_point_gate("(assert (mem (bool true) s))");
    assert!(
        matches!(
            exec.confirm_sat_with_independent_gate(),
            GateVerdict::ModelViolates { .. }
        ),
        "#g3-gate-reads-printed-uf: the printed else branch answers `false` \
             at the unlisted point, so the published witness must be REFUTED"
    );
}

const G3_PIN_VS_PRINTED: &str = "(set-logic QF_UF)\
         (declare-sort U 0)\
         (declare-fun g (U) U)\
         (declare-fun a () U)\
         (declare-fun b () U)\
         (assert (= (g a) b))";

/// Load [`G3_PIN_VS_PRINTED`] with `(g a)` PINNED to `@U!1` (= `b`) and the
/// printed table for `g` answering `printed_g_a` at `a`'s value.
#[cfg(test)]
fn g3_pin_vs_printed_gate(printed_g_a: &str) -> Executor {
    let mut exec = loaded(G3_PIN_VS_PRINTED);
    let u = Sort::Uninterpreted("U".to_string());
    let a = exec.ctx.terms.mk_var("a", u.clone());
    let b = exec.ctx.terms.mk_var("b", u.clone());
    let g_a = exec.ctx.terms.mk_app(Symbol::named("g"), [a], u);
    exec.last_model = Some(synthetic_euf_model_with_tables(
        &[(a, "@U!0"), (b, "@U!1"), (g_a, "@U!1")],
        &[("g", &[(&["@U!0"], printed_g_a)])],
    ));
    exec
}

/// POSITIVE: pin and printed body AGREE at the point, so the gate confirms
/// exactly as it did before this patch.
#[test]
fn g3_pin_agreeing_with_printed_table_confirms() {
    let exec = g3_pin_vs_printed_gate("@U!1");
    assert!(matches!(
        exec.confirm_sat_with_independent_gate(),
        GateVerdict::ConfirmedSat
    ));
}

/// NEGATIVE CONTROL: the per-application pin says `g(a) = @U!1` (which
/// satisfies the assertion) while `(get-model)` publishes
/// `(define-fun g ((x0 U)) U (as @U!2 U))`, under which `(= (g a) b)` is
/// FALSE. "Pin wins" — the semantics of the first, unlanded version of
/// this patch — confirms this hybrid and ships a `sat` whose own printed
/// witness a validator refutes (the counterexample in
/// the development design notes). The reconciled
/// gate must REFUSE (`CannotConfirm`: the two sources disagree, so there is
/// no single interpretation to certify).
#[test]
fn g3_pin_disagreeing_with_printed_table_is_refused() {
    let exec = g3_pin_vs_printed_gate("@U!2");
    match exec.confirm_sat_with_independent_gate() {
        GateVerdict::CannotConfirm { reason } => assert!(
            reason.contains("model commits no value for this application of `g`"),
            "the refusal must come from the reconciled UF read, got: {reason}"
        ),
        other => panic!(
            "#g3-gate-reads-printed-uf: a pin that disagrees with the published \
                 interpretation at the same point must fail closed, got {other:?}"
        ),
    }
}
