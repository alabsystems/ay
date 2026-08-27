// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ITE/UF and printed-UF regressions included in `smt::qf_uflia` so their
// fully-qualified test names remain stable.

/// Project P1 (SMT-COMP soundness gate): a chained `ite`-over-Int that defines a
/// UF application is not enforced in the combined EUF+LIA path, so AY returns a
/// false `sat` on this minimized `traffic.ec` k-induction core. z3/cvc5/yices2
/// all say `unsat`. One wrong answer voids the QF_UFLIA (and superset QF_AUFLIA)
/// divisions, so the soundness invariant is: AY must NEVER answer `sat` here.
/// The competition-correct outcomes are `unsat` (complete fix — enforce the
/// ite-definition equality) or, at worst, `unknown` (a Sat->Unknown
/// model-validation gate). Both are sound; `sat` is a DQ.
///
/// Fixed by `IteDefinitionOracle` (definitive_eval.rs): a SAT model that makes
/// an ite+UF assertion concretely `Bool(false)` is rejected by the strict
/// model-validation gate, degrading the spurious `sat` to a sound `unknown`.
#[test]
fn test_traffic_uflia_ite_chain_no_false_sat() {
    let got = run_fixture_answers(
        "benchmarks/smt/regression/soundness_qf_uf_incremental/traffic_uflia_falsesat_min.smt2",
    );
    assert_ne!(
        got,
        vec!["sat".to_string()],
        "P1 soundness: ite-defined UF app must be enforced in combined EUF+LIA — \
         false `sat` is a division-voiding DQ (expected `unsat`, or `unknown` via gate)"
    );
    assert!(
        matches!(got.as_slice(), [only] if only == "unsat" || only == "unknown"),
        "P1: expected a single sound answer (`unsat` ideal, `unknown` acceptable), got {got:?}"
    );
}

// QF_UFLRA (Uninterpreted Functions with Linear Real Arithmetic) Tests

/// SOUNDNESS (found by scripts/diff_fuzz.py, QF_UFLRA): a Real variable that is
/// ite-defined in LRA and is the ARGUMENT of a UF app in EUF triggers a
/// false-UNSAT in the combined Nelson-Oppen path. `(= (ga z) 5) ∧
/// (= z (ite p -3 -2))` is trivially SAT (z3 = sat) but AY returns `unsat`.
/// Invariant: AY must NEVER answer `unsat` here (`sat` is correct; `unknown` is
/// an acceptable sound fallback). FIXED by the ITE-term Nelson-Oppen
/// shared-equality guard (nelson_oppen.rs `ite_shared_eq_guard_enabled`): EUF was
/// forwarding `ite_term = c` for both branch values, which LRA asserted
/// simultaneously into the simplex (`-3 = -2`) — now rejected, so AY returns the
/// correct `sat`.
#[test]
fn test_qf_uflra_ite_uf_arg_no_false_unsat() {
    let got = run_fixture_answers(
        "benchmarks/smt/regression/soundness_qf_uflra_ite_arg/min_falseunsat_ga_ite_arg.smt2",
    );
    assert_ne!(
        got,
        vec!["unsat".to_string()],
        "false-UNSAT: ite-defined UF argument in combined EUF+LRA — the formula is SAT \
         (expected `sat`, or `unknown` via a fail-closed re-verify gate)"
    );
}

// ---------------------------------------------------------------------------
// #g3-gate-reads-printed-uf — regression tests for gate (3) of the SAT emit
// funnel: `apply_independent_model_gate`'s `CannotConfirm` arm
// (`crates/ay-dpll/src/executor/model/independent_gate.rs`).
//
// BISECT: `66538b006f` ("feat(parity): define exact Z3 5 replacement gate")
// turned that arm from fail-OPEN into fail-CLOSED:
//
//     -   tracing::debug!(...); result                  // keep the verdict
//     +   self.downgrade_sat_after_gate(...);           // publish unknown
//     +   SolveResult::Unknown
//
// and deleted the `independent_model_gate_enabled()` early-out, so there is no
// longer any switch at the site. The posture is right — an unconfirmed witness
// must not ship as an authoritative `sat` — but it exposed a gap that had been
// invisible while the arm kept the verdict.
//
// ROOT CAUSE (measured with `AY_G3_GATE_DUMP=1` over a 10,773-file sweep): a
// model can interpret an uninterpreted function TOTALLY without pinning the
// individual application TERM. `(get-model)` serialises such a function as a
// complete `(define-fun mem ((x0 U) (x1 U)) Bool (ite ... else))`, and
// `(get-value ((mem <unlisted args>)))` answers the else branch — every
// EXTERNAL consumer sees a total interpretation. But the gate's
// `IndependentModelView::uf_app_value` resolves only through
// `Executor::evaluate_term`, which is keyed by the application's TermId and
// answers `Unknown` at an argument point the extracted function table does not
// list. The gate then reported
// `uninterpreted / unsupported function application: mem` and downgraded a
// model that is total, printable and VALID (z3 4.16.0 re-checks the emitted
// 1067-`define-fun` model of `clearsy_00302_prefix3` as `sat`).
//
// FIX: `uf_app_value_at` — a RECONCILED read. The gate evaluates the PUBLISHED
// total interpretation at the argument values it computed itself, reading the
// rows through `Executor::printed_uf_table_rows` (the very function
// `format_function_table` renders) with the printer's own first-match/else
// rule. An application the model pins is ALSO checked against that printed
// body: pin and printed value must agree, otherwise the gate fails closed
// (`CannotConfirm`). So a confirmed `sat` certifies the interpretation
// `(get-model)` publishes — never a hybrid of pins and printed rows, which was
// the defect that kept the first version of this patch out of main
// (the development design notes). That MINTS the
// missing confirmation instead of relaxing the gate: it still returns
// `ModelViolates` when the published interpretation falsifies an assertion,
// and every step fails closed on anything it cannot read back.
//
// SCOPE, unrounded: over the 10,773-file sweep gate (3) fires on 57 files, and
// 42 change verdict when the site is forced open. THIS RECOVERS 3 FILES / 11
// QUERY-LEVEL ANSWERS. 39 remain. They are deliberately untouched, and NOT for
// lack of a mechanism:
//
//   * 33 QF_AUFLIA storecomm/storeinv + the `RF` file above: the emitted model
//     is genuinely PARTIAL, so there is nothing faithful to read. Verified
//     directly on three of them —
//       storeinv_..._00002_001 -> (error "model value for array a1 is not available")
//       storecomm_..._00020_002 -> (error "model value for i_640 is not available
//                                   (internal error: sat accepted without a total model)")
//       fb_var_27_8            -> (error "model value for function RF is not available:
//                                   no complete array model value ...")
//     That is an upstream MODEL-CONSTRUCTION defect (array lane), not a gate
//     defect; publishing `sat` would ship a witness `(get-model)` cannot print.
//   * 1 QF_AX (`r3_rank4_..._false_UNSAT`): the gate is masking a genuinely
//     INVALID model — z3 refutes the completed witness. Must stay closed.
//   * 2 QF_NRA metitarski: the witness is a `root-obj` ALGEBRAIC value and
//     `ModelValue` has no algebraic representative (`eval.rs:207`). Correct
//     witnesses, but reading them needs exact algebraic arithmetic in the
//     independent evaluator.
//   * 1 QF_FPLRA: the ROUNDING form of `(_ to_fp ..)`. `eval.rs` declines it BY
//     DESIGN — "an independent gate must not confirm a model using the same
//     rounding routine that produced it". A principled refusal, left alone.
//   * 2 under-specified builtins (`fp.to_real` of NaN, `mod` by zero). SMT-LIB
//     leaves the value free, so the gate has nothing to check against; one of
//     the two documents `unknown` as its own expected answer.

/// `clearsy_00302_prefix3` is the repo's own regression asset for this family
/// and its header records the expected answers: `sat unsat unsat`. Check-sat #1
/// answered `unknown` from `66538b006f` until #g3-gate-reads-printed-uf: the
/// `mem` predicate is interpreted totally by the emitted model but the gate
/// could not read that interpretation at the applications the table omits.
///
/// Asserting only #1 deliberately: #2/#3 are a DIFFERENT, still-open
/// completeness gap (they do not reach this gate at all).
#[test]
fn test_clearsy_00302_prefix_first_query_is_sat() {
    let got = run_fixture_answers(
        "benchmarks/smt/regression/euf_bool_arg_guard_seed/clearsy_00302_prefix3.smt2",
    );
    assert_eq!(
        got.first().map(String::as_str),
        Some("sat"),
        "#g3-gate-reads-printed-uf: the emitted model interprets `mem` totally \
         (z3 re-checks it `sat`), so the independent gate must CONFIRM it rather \
         than report an unsupported UF application — got {got:?}"
    );
}

/// The same mechanism inside an incremental QF_UF file. Check-sats #4, #5, #12,
/// #13 and #15 answered `unknown` at `66538b006f`; z3 4.16.0 and cvc5 1.3.0
/// (default and `--finite-model-find`) all say `sat` for each. The companion
/// `test_clearsy_00307_full_instance_matches_z3` above cannot catch this — it
/// SKIPS `unknown` positions by design.
#[test]
fn test_clearsy_00307_printed_uf_interpretation_queries_are_sat() {
    let got = run_fixture_answers(
        "benchmarks/smt/regression/soundness_qf_uf_incremental/clearsy_0000_00307_falsesat13.smt2",
    );
    for q in [4usize, 5, 12, 13, 15] {
        assert_eq!(
            got.get(q - 1).map(String::as_str),
            Some("sat"),
            "#g3-gate-reads-printed-uf: check-sat #{q} must be `sat` \
             (z3 + cvc5 + cvc5 --finite-model-find agree) — got {got:?}"
        );
    }
}

/// MINIMAL isolation of the mechanism (ddmin-reduced from
/// `clearsy_00302_prefix3`, then hand-minimised to 8 declarations).
///
/// `(bool (or ...))` is a COMPOUND argument, so `(mem (bool ...) s)` is an
/// argument point the extracted function table never lists — the table holds
/// only `mem(a, s) = true`. The emitted model is nonetheless TOTAL:
///
///     (define-fun bool ((x0 Bool)) U (as @U!2 U))
///     (define-fun mem ((x0 U) (x1 U)) Bool
///       (ite (and (= x0 (as @U!0 U)) (= x1 (as @U!1 U))) true false))
///
/// so the unlisted point reads `false` and BOTH assertions hold (z3 4.16.0
/// re-checks that substituted model `sat`; z3, cvc5 1.3.0 and cvc5
/// `--finite-model-find` all answer `sat` on the instance itself).
///
/// Before #g3-gate-reads-printed-uf the gate reported
/// `uninterpreted / unsupported function application: mem` at the unlisted
/// point and `66538b006f`'s fail-closed `CannotConfirm` arm published
/// `unknown`.
#[test]
fn test_unlisted_uf_point_reads_printed_else_branch() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun mem (U U) Bool)
        (declare-fun bool (Bool) U)
        (declare-fun TRUE () U)
        (declare-fun a () U)
        (declare-fun b () U)
        (declare-fun s () U)
        (assert (mem a s))
        (assert (not (mem (bool (or (= a b) (= b TRUE))) s)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("sat"),
        "#g3-gate-reads-printed-uf: a UF application at an argument point the \
         function table omits must be read from the EMITTED total interpretation \
         (the printed else branch), not left unevaluable"
    );
}

// NEGATIVE CONTROLS live next to the mechanism, in
// `executor/model/independent_gate.rs` (`g3_*` tests), because they need a
// model the SOLVER would never produce: a printed value at an UNPINNED point
// that falsifies an assertion (`g3_unlisted_uf_point_printed_value_falsifying_assertion_is_refuted`
// — must be `ModelViolates`), and a per-application pin that DISAGREES with
// the printed body at the same point
// (`g3_pin_disagreeing_with_printed_table_is_refused` — must be
// `CannotConfirm`). The second is the exact hybrid-interpretation
// counterexample that kept the first version of this patch out of main
// (the development design notes).
