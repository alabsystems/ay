// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The closed-spelling repair of a broken printed `eq_transitive` chain.
//!
//! The positive fixtures are the two external-corpus documents that shipped
//! the step as a `hole` (`model_checker_consumer_quantified_counterexample/
//! wide_key136_truncated_pin_unsat`, `model_checker_consumer_nested_residual/
//! vec_alias_conflict_unsat`, reduced to the one step). Pinned carcara 1.1.0
//! checks the exact derivations asserted here as `valid` (the corpus gate
//! runs them end to end).

use super::{bridged_eq_transitive, closed_value, MAX_BRIDGE_DEPTH, MAX_BRIDGE_WORK};
use num_bigint::BigUint;

const CONCAT: &str = "(concat (_ bv0 8) (concat (_ bv9223372036854775811 64) (_ bv9 64)))";
const KEY: &str = "(_ bv170141183460469231787027535937012760585 136)";

fn wide_key_clause() -> String {
    format!("(cl (not (= low0 {CONCAT})) (not (= high1 {KEY})) (= low0 high1))")
}

#[test]
fn a_closed_concat_link_is_proved_by_evaluate() {
    let clause = wide_key_clause();
    let text = bridged_eq_transitive("t4", &clause).expect("broken only by a closed spelling");
    let lines: Vec<&str> = text.lines().collect();
    let expected_chain = format!(
        "(step t4.gb.et (cl (not (= low0 {CONCAT})) (not (= {CONCAT} {KEY})) \
         (not (= high1 {KEY})) (= low0 high1)) :rule eq_transitive)"
    );
    let expected_close = format!("(step t4 {clause} :rule resolution :premises (t4.gb.et t4.gb0))");
    assert_eq!(
        lines,
        vec![
            format!("(step t4.gb0 (cl (= {CONCAT} {KEY})) :rule evaluate)").as_str(),
            expected_chain.as_str(),
            expected_close.as_str(),
        ]
    );
}

#[test]
fn a_closed_index_under_function_symbols_is_proved_by_cong() {
    let z = format!("#b{:064b}", 64);
    let add = "(bvadd (_ bv63 64) (_ bv1 64))";
    let clause = format!(
        "(cl (not (= (fld_len (fld_vec (select a (_ bv64 64)))) (_ bv65 64))) \
         (not (= (fld_len (fld_vec (select a {z}))) (fld_len (fld_vec (select b {z}))))) \
         (not (= (fld_len (fld_vec (select b {add}))) (_ bv66 64))) \
         (= #b{:064b} #b{:064b}))",
        65, 66
    );
    let text = bridged_eq_transitive("t10", &clause).expect("broken only by a closed index");
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(lines.len(), 6, "{text}");
    assert_eq!(
        lines[0],
        format!("(step t10.gb0 (cl (= {add} {z})) :rule evaluate)")
    );
    assert_eq!(
        lines[1],
        format!("(step t10.gb1 (cl (= (select b {z}) (select b {add}))) :rule cong :premises (t10.gb0))")
    );
    assert!(
        lines[2].ends_with(":rule cong :premises (t10.gb1))"),
        "{text}"
    );
    assert_eq!(
        lines[3],
        format!(
            "(step t10.gb3 (cl (= (fld_len (fld_vec (select b {z}))) \
             (fld_len (fld_vec (select b {add}))))) :rule cong :premises (t10.gb2))"
        )
    );
    assert!(lines[4].contains(":rule eq_transitive"), "{text}");
    assert_eq!(
        lines[5],
        format!("(step t10 {clause} :rule resolution :premises (t10.gb.et t10.gb3))")
    );
}

#[test]
fn two_non_literal_spellings_meet_at_their_common_value() {
    let clause = "(cl (not (= p (bvadd #x01 #x01))) (not (= q (bvmul #x01 #x02))) (= p q))";
    let text = bridged_eq_transitive("t1", clause).expect("both sides evaluate to #x02");
    assert!(text.starts_with(
        "(step t1.gb0 (cl (= (bvadd #x01 #x01) (_ bv2 8))) :rule evaluate)\n\
         (step t1.gb1 (cl (= (bvmul #x01 #x02) (_ bv2 8))) :rule evaluate)\n\
         (step t1.gb2 (cl (= (bvadd #x01 #x01) (bvmul #x01 #x02))) :rule trans :premises (t1.gb0 t1.gb1))\n"
    ));
}

#[test]
fn different_values_keep_the_hole() {
    for clause in [
        "(cl (not (= low0 (concat #x00 #x01))) (not (= high1 #x0002)) (= low0 high1))",
        // Same value, different width: not one term.
        "(cl (not (= p (concat #x0 #x1))) (not (= q #x001)) (= p q))",
    ] {
        assert!(bridged_eq_transitive("t0", clause).is_none(), "{clause}");
    }
}

#[test]
fn operators_pinned_carcara_evaluates_wrongly_are_never_bridged() {
    // carcara 1.1.0 computes `bvsub` through its broken signed reading (wrong
    // whenever an operand's top bit is set) and `(_ extract i j)` one bit
    // short (wrong whenever bit i is set), so it refuses these true steps; the
    // operators are excluded as a whole, not instance by instance.
    for clause in [
        "(cl (not (= p (bvsub #xff #x01))) (not (= q #xfe)) (= p q))",
        "(cl (not (= p ((_ extract 3 0) #x1f))) (not (= q #xf)) (= p q))",
        "(cl (not (= p (bvsdiv #xfe #x01))) (not (= q #xfe)) (= p q))",
    ] {
        assert!(bridged_eq_transitive("t0", clause).is_none(), "{clause}");
    }
}

#[test]
fn open_terms_and_binders_keep_the_hole() {
    for clause in [
        "(cl (not (= p (select b x))) (not (= (select b y) q)) (= p q))",
        "(cl (not (= p (choice ((z (_ BitVec 4))) (= z (bvadd #x1 #x1))))) \
         (not (= (choice ((z (_ BitVec 4))) (= z #x2)) q)) (= p q))",
        "(cl (not (= p (|f| (bvadd #x1 #x1)))) (not (= (|f| #x2) q)) (= p q))",
    ] {
        assert!(bridged_eq_transitive("t0", clause).is_none(), "{clause}");
    }
}

#[test]
fn an_intact_chain_or_a_non_chain_is_not_rewritten() {
    for clause in [
        "(cl (not (= a b)) (not (= b c)) (= a c))",
        "(cl (not (= a b)) (= a c))",
        "(cl (not (= a b)) (not (= c d)) (= a d))",
        "(cl (= a b))",
    ] {
        assert!(bridged_eq_transitive("t0", clause).is_none(), "{clause}");
    }
}

#[test]
fn closed_values_follow_smt_lib_modulo_the_width() {
    let value = |text: &str| closed_value(text, 0, &mut 1024);
    let bv = |v: u32, w: u32| Some((BigUint::from(v), w));
    assert_eq!(value("(bvnot #x0f)"), bv(0xf0, 8));
    assert_eq!(value("(bvneg #x01)"), bv(0xff, 8));
    assert_eq!(value("(bvneg #x00)"), bv(0, 8));
    assert_eq!(value("((_ zero_extend 4) #xf)"), bv(15, 8));
    assert_eq!(value("(bvmul #xff #xff)"), bv(1, 8));
    assert_eq!(value("(bvadd #xff #x01)"), bv(0, 8));
    assert_eq!(value("(bvxor #x0f #xff)"), bv(0xf0, 8));
    assert_eq!(value("(bvand #x0f #x3c)"), bv(0x0c, 8));
    assert_eq!(value("(bvor #x0f #x30)"), bv(0x3f, 8));
    assert_eq!(value("(concat #b1 #x0)"), bv(16, 5));
    assert_eq!(
        value("(bvadd #x01 #x0001)"),
        None,
        "mixed widths are ill-sorted"
    );
    assert_eq!(value("(bvsub #x05 #x01)"), None);
    assert_eq!(value("(bvsge #xf #xe)"), None, "predicates are not values");
    assert_eq!(value("x"), None);
    assert_eq!(
        value("(_ bv256 8)"),
        None,
        "an out-of-range literal is not a value"
    );
    assert_eq!(value("(_ bv255 8)"), bv(255, 8));
}

#[test]
fn nesting_past_the_depth_cap_keeps_the_hole() {
    // The work budget alone would admit these depths, so the cap decides.
    let nots = |depth: usize| (0..depth).fold("#x0f".to_string(), |t, _| format!("(bvnot {t})"));
    let value = |text: &str| {
        let mut work = MAX_BRIDGE_WORK;
        closed_value(text, 0, &mut work)
    };
    assert_eq!(
        value(&nots(MAX_BRIDGE_DEPTH)),
        Some((BigUint::from(15u8), 8))
    );
    assert_eq!(value(&nots(MAX_BRIDGE_DEPTH + 1)), None);
    let under_f =
        |depth: usize, inner: &str| (0..depth).fold(inner.to_string(), |t, _| format!("(f {t})"));
    let clause = |depth: usize| {
        format!(
            "(cl (not (= p {})) (not (= q {})) (= p q))",
            under_f(depth, "(bvadd #x01 #x01)"),
            under_f(depth, "#x02")
        )
    };
    assert!(bridged_eq_transitive("t0", &clause(MAX_BRIDGE_DEPTH - 1)).is_some());
    assert!(bridged_eq_transitive("t0", &clause(MAX_BRIDGE_DEPTH + 1)).is_none());
}
