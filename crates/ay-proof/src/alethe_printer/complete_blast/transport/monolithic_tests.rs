// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The monolithic refutation stays inside its counted envelope: a circuit
//! past it is declined after the envelope's work and never paid again, and a
//! circuit inside it refutes exactly as the unbounded search does.

use super::super::super::{AlethePrinter, Blaster};
use super::MONOLITHIC_WORK;
use crate::resolution_dag_memo::{
    reset_resolution_dag_memo, resolution_dag_memo_counters, resolution_dag_refusals_served,
};
use ay_core::{ProofId, Sort, Symbol, TermId, TermStore};
use ay_sat::ResolutionDagWork;
use num_bigint::BigInt;
use std::time::{Duration, Instant};

fn word(terms: &mut TermStore, name: &str, args: [TermId; 2], width: u32) -> TermId {
    terms.mk_app(Symbol::named(name), args, Sort::bitvec(width))
}

/// `(not (= L R))` for `bv_affine_source`'s 64-bit affine identity
/// `2*a1 + 4*a2 + a0 + a0 + a0 + a1 + a2 + acc = 3*a0 + 3*a1 + 5*a2 + acc`.
fn affine_identity(terms: &mut TermStore) -> TermId {
    let [acc, a2, a1, a0] =
        ["acc", "a2", "a1", "a0"].map(|name| terms.mk_var(name, Sort::bitvec(64)));
    let times = |terms: &mut TermStore, k: u32, x: TermId| {
        let k = terms.mk_bitvec(BigInt::from(k), 64);
        word(terms, "bvmul", [k, x], 64)
    };
    let (two_a1, four_a2) = (times(terms, 2, a1), times(terms, 4, a2));
    let mut left = word(terms, "bvadd", [two_a1, four_a2], 64);
    for term in [a0, a0, a0, a1, a2, acc] {
        left = word(terms, "bvadd", [left, term], 64);
    }
    let (three_a0, three_a1) = (times(terms, 3, a0), times(terms, 3, a1));
    let five_a2 = times(terms, 5, a2);
    let mut right = word(terms, "bvadd", [three_a0, three_a1], 64);
    for term in [five_a2, acc] {
        right = word(terms, "bvadd", [right, term], 64);
    }
    let identity = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    terms.mk_not_raw(identity)
}

/// `(not (= m (bvadd (bvmul (bvudiv m n) n) (bvurem m n))))` over 4 bits:
/// the quotient-remainder identity, which refutes in a handful of conflicts.
fn quotient_remainder(terms: &mut TermStore) -> TermId {
    let m = terms.mk_var("m", Sort::bitvec(4));
    let n = terms.mk_var("n", Sort::bitvec(4));
    let quotient = word(terms, "bvudiv", [m, n], 4);
    let product = word(terms, "bvmul", [quotient, n], 4);
    let remainder = word(terms, "bvurem", [m, n], 4);
    let sum = word(terms, "bvadd", [product, remainder], 4);
    let identity = terms.mk_app(Symbol::named("="), [m, sum], Sort::Bool);
    terms.mk_not_raw(identity)
}

/// A circuit past the envelope is declined — not refuted, not called false —
/// once the envelope's conflicts are spent, and a repeated ask is answered
/// from the refusal record without a search. Before the envelope this search
/// had no bound: on this identity's blast it was still running after a
/// million conflicts.
#[test]
fn an_over_envelope_circuit_declines_after_its_envelope_and_only_once() {
    let mut terms = TermStore::new();
    let assertion = affine_identity(&mut terms);
    let printer = AlethePrinter::new(&terms);
    let mut blaster = Blaster::new(&printer, ProofId(1), "@ay_cbb_t_".into());
    let root = blaster.prepare(assertion).expect("the identity blasts");
    let (cnf, _) = blaster.planned_cnf(root).expect("the CNF is planned");
    let variables = blaster.circuit.len();
    let small = ResolutionDagWork {
        max_conflicts: 2_000,
        max_decisions: MONOLITHIC_WORK.max_decisions,
    };
    reset_resolution_dag_memo();
    assert_eq!(
        blaster
            .monolithic_refutation_within(variables, &cnf, small)
            .err(),
        Some(false),
        "past its envelope the {}-clause blast is declined, not called false",
        cnf.len()
    );
    assert_eq!(resolution_dag_refusals_served(), 0);
    let started = Instant::now();
    assert_eq!(
        blaster
            .monolithic_refutation_within(variables, &cnf, small)
            .err(),
        Some(false)
    );
    assert_eq!(
        resolution_dag_refusals_served(),
        1,
        "served from the record"
    );
    assert!(started.elapsed() < Duration::from_secs(1));
    // The production envelope declines it too, and is then not paid again.
    assert_eq!(
        blaster.monolithic_refutation_planned(variables, &cnf).err(),
        Some(false)
    );
    assert_eq!(
        blaster.monolithic_refutation_planned(variables, &cnf).err(),
        Some(false)
    );
    assert_eq!(resolution_dag_refusals_served(), 2);
    assert_eq!(resolution_dag_memo_counters().0, 0, "nothing was refuted");
}

/// The twin: a circuit inside the envelope refutes exactly as the unbounded
/// search refutes it, and a false lemma is still called false.
#[test]
fn a_circuit_inside_the_envelope_refutes_as_the_unbounded_search_does() {
    let mut terms = TermStore::new();
    let assertion = quotient_remainder(&mut terms);
    let x = terms.mk_var("x", Sort::bitvec(4));
    let y = terms.mk_var("y", Sort::bitvec(4));
    let sum = word(&mut terms, "bvadd", [x, y], 4);
    let false_identity = terms.mk_app(Symbol::named("="), [sum, x], Sort::Bool);
    let satisfiable = terms.mk_not_raw(false_identity);
    let printer = AlethePrinter::new(&terms);

    let mut blaster = Blaster::new(&printer, ProofId(1), "@ay_cbb_t_".into());
    let root = blaster.prepare(assertion).expect("the identity blasts");
    let (cnf, _) = blaster.planned_cnf(root).expect("the CNF is planned");
    let variables = blaster.circuit.len();
    reset_resolution_dag_memo();
    let enveloped = blaster
        .monolithic_refutation_planned(variables, &cnf)
        .expect("inside the envelope the identity refutes");
    let unbounded = ay_sat::prove_unsat_resolution_dag(variables, &cnf).expect("UNSAT");
    assert_eq!(enveloped, unbounded);

    let mut blaster = Blaster::new(&printer, ProofId(2), "@ay_cbb_s_".into());
    let root = blaster
        .prepare(satisfiable)
        .expect("the false lemma blasts");
    let (cnf, _) = blaster.planned_cnf(root).expect("the CNF is planned");
    let variables = blaster.circuit.len();
    assert_eq!(
        blaster.monolithic_refutation_planned(variables, &cnf).err(),
        Some(true)
    );
    assert_eq!(resolution_dag_refusals_served(), 0);
}

/// An 8-bit product against its commuted spelling: the query of `ay-dpll`'s
/// `authored_ground_closure` test `a_commuted_product_is_not_a_slice_identity`.
/// Read here, it blasts to the circuit the CLI blasts for it (862 gates, 2,112
/// clauses).
const COMMUTED_PRODUCT: &str = "\
(declare-const e_rdi (_ BitVec 64))
(declare-const e_rsi (_ BitVec 64))
(declare-const s0 (_ BitVec 8))
(declare-const m0 (_ BitVec 64))
(declare-const m1 (_ BitVec 64))
(declare-const m2 (_ BitVec 64))
(assert (and (= s0 (bvmul ((_ extract 7 0) e_rdi) ((_ extract 7 0) e_rsi))) \
 (and (= m0 ((_ zero_extend 56) ((_ extract 7 0) e_rdi))) \
 (and (= m1 ((_ zero_extend 56) ((_ extract 7 0) e_rsi))) \
 (and (= m2 ((_ zero_extend 56) (bvmul ((_ extract 7 0) m1) ((_ extract 7 0) m0)))) \
 (not (= s0 ((_ extract 7 0) m2))))))))
";

/// The heaviest monolithic refutation measured that prints and is published:
/// the commuted 8-bit product above refutes in 43,803 conflicts and 89,413
/// decisions from the CLI and in about 46,600 and 91,600 here, and with
/// `:produce-proofs` the CLI publishes its 54 MB document (`unproved_steps=0`,
/// `carcara_surface=clean-dialect`); held under 40,000 conflicts, the same
/// query publishes the sweep's 61 MB document instead. It refutes inside the
/// envelope and not inside 40,000 conflicts: an envelope lowered under it
/// changes what that query publishes. Should `ay_sat` come to refute it inside
/// 40,000 conflicts, this pin no longer measures the envelope's edge: move it
/// to a heavier circuit.
#[test]
fn the_heaviest_measured_printable_refutation_fits_the_envelope() {
    let (terms, assertion) =
        super::super::super::corpus::read_problem(COMMUTED_PRODUCT).expect("the query reads");
    let printer = AlethePrinter::new(&terms);
    let mut blaster = Blaster::new(&printer, ProofId(1), "@ay_cbb_t_".into());
    let root = blaster.prepare(assertion).expect("the conjunction blasts");
    let (cnf, _) = blaster.planned_cnf(root).expect("the CNF is planned");
    let variables = blaster.circuit.len();
    reset_resolution_dag_memo();
    let below = ResolutionDagWork {
        max_conflicts: 40_000,
        ..MONOLITHIC_WORK
    };
    assert_eq!(
        blaster
            .monolithic_refutation_within(variables, &cnf, below)
            .err(),
        Some(false),
        "the {variables}-gate commuted product needs more than 40,000 conflicts"
    );
    assert!(
        blaster
            .monolithic_refutation_planned(variables, &cnf)
            .is_ok(),
        "inside the envelope the commuted product refutes"
    );
}
