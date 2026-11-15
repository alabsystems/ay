// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The case-split route over a priority chain: an 8-bit analog of
//! proof_gate_strict row 1257's lowered query (an integer through a small
//! float and back) prints a document that replays, with the chain's
//! `eq_transitive` shortcuts in it; a false round trip prints nothing; and a
//! split that declines leaves the other routes their own CNF.

use super::super::corpus::read_problem;
use super::super::{AlethePrinter, Blaster, MAX_COUNTED_TEXT_BYTES};
use ay_core::ProofId;

const N: u32 = 8;
const E: u32 = 4;
const M: u32 = 3;
const BIAS: u32 = (1 << (E - 1)) - 1;

fn bv(value: i64, width: u32) -> String {
    format!("(_ bv{} {width})", value.rem_euclid(1 << width))
}

/// `value` shifted so that bit `k` lands on bit `M` (`toward_fraction`) or
/// back from it.
fn shifted(value: &str, k: u32, toward_fraction: bool) -> String {
    let (up, down) = if toward_fraction {
        ("bvshl", "bvlshr")
    } else {
        ("bvlshr", "bvshl")
    };
    match k.cmp(&M) {
        std::cmp::Ordering::Greater => format!("({down} {value} {})", bv(i64::from(k - M), N)),
        std::cmp::Ordering::Equal => value.to_string(),
        std::cmp::Ordering::Less => format!("({up} {value} {})", bv(i64::from(M - k), N)),
    }
}

fn sign_of(word: &str) -> String {
    format!("((_ extract {0} {0}) {word})", N - 1)
}

/// The conversion of `a` as external-codegen lowers it: a priority chain over its
/// magnitude's leading one, each level the float with that exponent.
fn priority_chain(signed: bool) -> String {
    let (m, s) = if signed {
        (
            format!("(ite (= {} (_ bv1 1)) (bvneg a) a)", sign_of("a")),
            sign_of("a"),
        )
    } else {
        ("a".to_string(), "(_ bv0 1)".to_string())
    };
    let mut chain = bv(0, N);
    for k in 0..=M + 1 {
        let fraction = format!("((_ extract {} 0) {})", M - 1, shifted(&m, k, true));
        let level = format!(
            "(concat (concat {s} {}) {fraction})",
            bv(i64::from(BIAS + k), E)
        );
        chain = format!("(ite (= ((_ extract {k} {k}) {m}) (_ bv1 1)) {level} {chain})");
    }
    chain
}

fn problem(body: &str) -> String {
    format!(
        "(set-logic QF_BV)\n(declare-const a (_ BitVec {N}))\n\
         (declare-const tcg_fpbv_0 (_ BitVec {N}))\n\
         (declare-const tcg_fpbv_1 (_ BitVec {N}))\n(assert {body})\n(check-sat)\n"
    )
}

/// The lowered round trip of an `N`-bit integer through a float of `E`
/// exponent and `M` fraction bits: `t0` the conversion, `t1` the decoding,
/// one guarded fact per exponent. `extra` widens the range past what the
/// float represents exactly, which makes the claim false.
fn round_trip(signed: bool, extra: u32) -> String {
    let top = M + 1 + extra;
    let range = if signed {
        format!(
            "(and (bvsge a {}) (bvsle a {}))",
            bv(-(1_i64 << top), N),
            bv(1 << top, N)
        )
    } else {
        format!("(bvule a {})", bv(1 << top, N))
    };
    let exponent = format!("((_ extract {} {M}) tcg_fpbv_0)", N - 2);
    let mut facts = vec![
        format!(
            "(or (not {range}) (= tcg_fpbv_0 {}))",
            priority_chain(signed)
        ),
        format!(
            "(or (not (bvult {exponent} {})) (= tcg_fpbv_1 {}))",
            bv(i64::from(BIAS), E),
            bv(0, N)
        ),
    ];
    for k in 0..=M + 1 {
        let extended = format!(
            "((_ zero_extend {}) (concat (_ bv1 1) ((_ extract {} 0) tcg_fpbv_0)))",
            N - M - 1,
            M - 1
        );
        let x = shifted(&extended, k, false);
        let value = if signed {
            format!(
                "(ite (= {} (_ bv1 1)) (bvneg {x}) {x})",
                sign_of("tcg_fpbv_0")
            )
        } else {
            x
        };
        facts.push(format!(
            "(or (not (= {exponent} {})) (= tcg_fpbv_1 {value}))",
            bv(i64::from(BIAS + k), E)
        ));
    }
    let mut body = format!("(and {range} (not (= a tcg_fpbv_1)))");
    for fact in facts.iter().rev() {
        body = format!("(and {fact} {body})");
    }
    problem(&body)
}

/// The document the case-split route prints for `(cl (not A))`, `A` the
/// problem's assertion, or `None`.
fn render_by_cases(source: &str) -> Option<String> {
    let (mut terms, assertion) = read_problem(source)?;
    let lemma = terms.mk_not_raw(assertion);
    let printer = AlethePrinter::new(&terms);
    let final_clause = printer.format_clause(&[lemma]);
    let mut blaster = Blaster::new(&printer, ProofId(1), "@ay_cbb_t_".into());
    let root = blaster.prepare(assertion)?;
    let (cnf, root_clause_id) = blaster.planned_cnf(root)?;
    blaster.by_cases(&cnf, root_clause_id, root, "t1", &final_clause)
}

#[test]
fn a_signed_round_trip_prints_case_by_case_through_the_chain_shortcuts() {
    let document = render_by_cases(&round_trip(true, 0)).expect("each case is an identity");
    assert!(document.contains(":rule eq_transitive"));
    assert!(!document.contains(":rule hole"));
}

#[test]
fn an_unsigned_round_trip_prints_case_by_case() {
    let document = render_by_cases(&round_trip(false, 0)).expect("each case is an identity");
    assert!(document.contains(":rule eq_transitive"));
}

#[test]
fn a_round_trip_past_the_exact_range_is_never_printed() {
    // One leading-one position past the chain: those values decode to 0.
    assert!(render_by_cases(&round_trip(true, 1)).is_none());
}

/// REGRESSION: the split plans the chain's shortcuts past the CNF before it
/// runs; when it declines (here no guard is open: propagation alone refutes
/// the root), the route after it prints a DAG over the CNF it was given, and
/// must read the planned clauses only that far. It read them all and indexed
/// past the CNF.
#[test]
fn a_split_that_declines_leaves_the_next_route_its_own_cnf() {
    let chain = priority_chain(true);
    let source = problem(&format!(
        "(and (= tcg_fpbv_0 {chain}) (not (= tcg_fpbv_0 {chain})))"
    ));
    let (mut terms, assertion) = read_problem(&source).expect("the problem reads");
    let lemma = terms.mk_not_raw(assertion);
    let printer = AlethePrinter::new(&terms);
    let final_clause = printer.format_clause(&[lemma]);
    let mut blaster = Blaster::new(&printer, ProofId(1), "@ay_cbb_t_".into());
    let root = blaster.prepare(assertion).expect("the lemma blasts");
    let (cnf, root_clause_id) = blaster.planned_cnf(root).expect("the CNF is planned");
    assert!(blaster
        .by_cases(&cnf, root_clause_id, root, "t1", &final_clause)
        .is_none());
    assert!(
        blaster.planned.len() > cnf.len(),
        "the shortcuts were planned"
    );
    let dag = ay_sat::prove_unsat_resolution_dag(blaster.circuit.len(), &cnf)
        .expect("the lemma is refuted");
    let document = blaster.transport_document(
        &dag,
        &cnf,
        root_clause_id,
        root,
        "t1",
        &final_clause,
        MAX_COUNTED_TEXT_BYTES,
    );
    assert!(document.is_some());
}
