// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! Soundness/completeness tests for value-equality congruence of BARE
//! datatype-valued operands (#dt-value-eq-congruence).
//!
//! ay eager-bit-blasts DT+AUFBV into one CDCL instance. The static DT axiom
//! pass only emits selector/tester/injectivity congruence when one side of an
//! asserted equality is a CONSTRUCTOR APPLICATION `p = C(args)`. A bare
//! datatype-value equality `(= x y)` between two datatype-valued consts where
//! NEITHER side is a constructor application (e.g. two `ArrayVec`/`Parser`
//! consts whose fields are `(Array (_ BitVec 64) (_ BitVec 16|8))`) used to get
//! NO congruence axiom, so EUF could place `x`,`y` in distinct classes even when
//! the field theory forced every field equal — a spurious model that the
//! `#dt-bv-congruence` validation gate degraded to `unknown`/`incomplete`
//! (nondeterministically, on the search orders that missed the fact).
//!
//! `dt_datatype_value_equality_congruence_axioms` now emits the EXACT
//! datatype-equality biconditional for such atoms. These tests pin the
//! soundness contract: the biconditional must be EXACT datatype equality (both
//! directions, correct tester polarity) — a one-directional or wrong-polarity
//! instance would be UNSOUND (false-unsat or over-constraint).

use ntest::timeout;

/// Datatype mirroring the captured query's `ArrayVec_u16` shape:
/// single-constructor record with an `(Array (_ BitVec 64) (_ BitVec 16))`
/// field and a `(_ BitVec 64)` length field.
const ARRAYVEC_DECL: &str = r#"
    (declare-datatype Av
      ((Av_mk (fld_buf (Array (_ BitVec 64) (_ BitVec 16))) (fld_len (_ BitVec 64)))))
"#;

/// UNSAT (backward direction): two single-constructor consts whose `(Array
/// BV64 BV16)` + BV fields are forced EQUAL by array/BV constraints, while
/// `(distinct x y)` is asserted. Constructor injectivity makes equal fields
/// imply `x = y`, contradicting `distinct`. Before the fix this returned
/// `unknown (incomplete)` (or, on adversarial search order, a spurious `sat`).
#[test]
#[timeout(60_000)]
fn test_value_eq_array_fields_equal_distinct_unsat() {
    let smt = format!(
        r#"
        (set-logic ALL)
        {ARRAYVEC_DECL}
        (declare-const x Av)
        (declare-const y Av)
        (declare-const a (Array (_ BitVec 64) (_ BitVec 16)))
        (declare-const n (_ BitVec 64))
        ; Fields forced equal indirectly (via shared array/bv consts), NOT by a
        ; direct (= (fld_buf x) (fld_buf y)) — exercises array_uf_eq discharge.
        (assert (= (fld_buf x) a))
        (assert (= (fld_buf y) a))
        (assert (= (fld_len x) n))
        (assert (= (fld_len y) n))
        (assert (distinct x y))
        (check-sat)
    "#
    );
    let out = crate::common::solve(&smt);
    assert_eq!(
        crate::common::sat_result(&out),
        Some("unsat"),
        "equal Array/BV fields must force x = y (constructor injectivity); \
         got: {out}"
    );
}

/// UNSAT (forward direction / polarity): `(= x y)` asserted but a field is
/// forced DIFFERENT. Datatype equality entails field equality, contradicting
/// the disequal field.
#[test]
#[timeout(60_000)]
fn test_value_eq_asserted_with_differing_field_unsat() {
    let smt = format!(
        r#"
        (set-logic ALL)
        {ARRAYVEC_DECL}
        (declare-const x Av)
        (declare-const y Av)
        (assert (not (= (fld_len x) (fld_len y))))
        (assert (= x y))
        (check-sat)
    "#
    );
    let out = crate::common::solve(&smt);
    assert_eq!(
        crate::common::sat_result(&out),
        Some("unsat"),
        "x = y must entail (fld_len x) = (fld_len y); got: {out}"
    );
}

/// NO OVER-CONSTRAINT: genuinely free consts with NO field constraints. The
/// biconditional must NOT force `x = y`, so `(distinct x y)` must NEVER become
/// `unsat`. (ay returns `unknown` here — the pre-existing `#dt-bv-congruence`
/// validation gate fail-closes on a non-ground datatype-sort disequality over a
/// datatype with cross-theory Array/BV fields; this is identical on the
/// pre-fix binary, i.e. NOT a regression. The critical soundness property is
/// "never false-`unsat`", which is what this asserts. An actual `sat` model
/// demonstrating no-over-constraint is exercised by
/// `test_value_eq_multi_ctor_same_tag_diff_payload_sat`.)
#[test]
#[timeout(60_000)]
fn test_value_eq_free_consts_not_overconstrained() {
    let smt = format!(
        r#"
        (set-logic ALL)
        {ARRAYVEC_DECL}
        (declare-const x Av)
        (declare-const y Av)
        (assert (distinct x y))
        (check-sat)
    "#
    );
    let out = crate::common::solve(&smt);
    assert_ne!(
        crate::common::sat_result(&out),
        Some("unsat"),
        "free datatype consts must NOT be over-constrained to false-unsat \
         (sat or unknown are both sound); got: {out}"
    );
}

/// SAT (multi-constructor polarity guard): `x`,`y` are BOTH `SomeO` but with
/// DIFFERENT `(_ BitVec 8)` payloads, and `(distinct x y)` is asserted. They are
/// genuinely unequal, so this MUST be `sat`. A wrong biconditional that tied
/// `(= x y)` to tester agreement alone (omitting the field-equality requirement)
/// would force `x = y` and report a spurious `unsat` — this test catches that.
#[test]
#[timeout(60_000)]
fn test_value_eq_multi_ctor_same_tag_diff_payload_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Opt ((NoneO) (SomeO (val (_ BitVec 8)))))
        (declare-const x Opt)
        (declare-const y Opt)
        (assert ((_ is SomeO) x))
        (assert ((_ is SomeO) y))
        (assert (= (val x) #x01))
        (assert (= (val y) #x02))
        (assert (distinct x y))
        (check-sat)
    "#;
    let out = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&out),
        Some("sat"),
        "same-constructor, different-payload values are genuinely distinct \
         (biconditional must require field equality, not just tester \
         agreement); got: {out}"
    );
}

/// UNSAT (multi-constructor backward direction): `x`,`y` both `SomeO` with the
/// SAME payload `n`, and `(distinct x y)` asserted. Same constructor + equal
/// fields entails `x = y`, contradicting `distinct`.
#[test]
#[timeout(60_000)]
fn test_value_eq_multi_ctor_same_tag_same_payload_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Opt ((NoneO) (SomeO (val (_ BitVec 8)))))
        (declare-const x Opt)
        (declare-const y Opt)
        (declare-const n (_ BitVec 8))
        (assert ((_ is SomeO) x))
        (assert ((_ is SomeO) y))
        (assert (= (val x) n))
        (assert (= (val y) n))
        (assert (distinct x y))
        (check-sat)
    "#;
    let out = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&out),
        Some("unsat"),
        "same constructor + equal payload must force x = y; got: {out}"
    );
}

/// NO OVER-CONSTRAINT (multi-constructor, different tags): `x` is `NoneO`, `y`
/// is `SomeO`, and `(distinct x y)` is asserted. Different constructors ⇒
/// genuinely unequal ⇒ MUST NOT be `unsat`. Guards against the tester-agreement
/// direction wrongly equating them. (ay returns `unknown` — same fail-closed
/// `#dt-bv-congruence` gate as above, identical on the pre-fix binary, NOT a
/// regression — so we assert the sound "never false-unsat" property.)
#[test]
#[timeout(60_000)]
fn test_value_eq_multi_ctor_diff_tag_not_overconstrained() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Opt ((NoneO) (SomeO (val (_ BitVec 8)))))
        (declare-const x Opt)
        (declare-const y Opt)
        (assert ((_ is NoneO) x))
        (assert ((_ is SomeO) y))
        (assert (distinct x y))
        (check-sat)
    "#;
    let out = crate::common::solve(smt);
    assert_ne!(
        crate::common::sat_result(&out),
        Some("unsat"),
        "different-constructor values must NOT be over-constrained to \
         false-unsat; got: {out}"
    );
}
