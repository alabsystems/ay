// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `_BV_LIA_INDEP` final-assignment reconciliation
//! (#bv-lia-indep-final-assignment-reconcile,
//! `executor/model/bv_lia_indep_reconcile.rs`).
//!
//! The BV lane of the independent BV + LIA category runs with
//! `array_axioms: false`, so a Bool-element `(Array BV Bool)` read, a Bool
//! anchor variable, a BV-element read and an index variable are FREE opaque
//! choices there, while the AUFLIA cross-check decides them together with the
//! arithmetic. Before the reconciliation the restored witness carried the BV
//! lane's stale choices next to the AUFLIA arithmetic, every `ite(select ..)`
//! cardinality counter shape falsified an assertion, and the independent gate
//! correctly fail-closed a genuine `sat` to `unknown` (deductive-checks `maps.rs`
//! `test1_fails2`, C-3 of the 2026-09-16 solver-fix round). z3 answers `sat`
//! on every satisfiable query below and `unsat` on every control.

use super::*;

fn verdict(input: &str) -> Vec<String> {
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap()
}

/// The minimal C-3 shape: the BV lane picks the `select` branch, AUFLIA the
/// other, and the Int counter follows AUFLIA.
#[test]
fn bool_select_ite_int_counter_is_sat() {
    let input = r#"
        (set-logic ALL)
        (declare-const A (Array (_ BitVec 32) Bool))
        (declare-const n Int)
        (assert (= n (ite (select A #x00000002) 0 1)))
        (check-sat)
    "#;
    assert_eq!(verdict(input), vec!["sat"]);
}

/// Same disagreement with the read as an `ite` condition over two Int atoms.
#[test]
fn bool_select_ite_condition_over_int_atoms_is_sat() {
    let input = r#"
        (set-logic ALL)
        (declare-const A (Array (_ BitVec 32) Bool))
        (declare-const n Int)
        (assert (ite (select A #x00000002) (= n 0) (= n 1)))
        (check-sat)
    "#;
    assert_eq!(verdict(input), vec!["sat"]);
}

/// BV-element read compared to a literal: the read is an opaque bit vector
/// in the BV lane and takes the AUFLIA lane's EUF literal.
#[test]
fn bv_element_select_equality_int_counter_is_sat() {
    let input = r#"
        (set-logic ALL)
        (declare-const A (Array (_ BitVec 32) (_ BitVec 8)))
        (declare-const n Int)
        (assert (= n (ite (= (select A #x00000002) #x00) 0 1)))
        (check-sat)
    "#;
    assert_eq!(verdict(input), vec!["sat"]);
}

/// The deductive-checks Set anchor shape: a const-false domain, a `__ground_seed`
/// Bool anchor pinned to a read, and a cardinality counter through another
/// read. The anchor is a free Bool in the BV lane and follows AUFLIA.
#[test]
fn const_set_seed_anchor_and_counter_is_sat() {
    let input = r#"
        (set-logic ALL)
        (declare-const S (Array (_ BitVec 32) Bool))
        (declare-const seed Bool)
        (declare-const n Int)
        (assert (= S ((as const (Array (_ BitVec 32) Bool)) false)))
        (assert (= (select S #x00000000) seed))
        (assert (ite (select S #x00000001) (= 0 n) (= n 1)))
        (check-sat)
    "#;
    assert_eq!(verdict(input), vec!["sat"]);
}

/// A read through a store chain at a BV VARIABLE index: the index is free in
/// the BV lane, the AUFLIA array reasoning identifies it with the store key,
/// and the merged witness must carry that identification.
///
/// A known gap from 2026-09-17 (#bv-euf-class-literal-read) to 2026-10-13. The
/// only record of that identification is the index variable's EUF CLASS
/// value, and reading a BitVec variable from its EUF class in EVERY
/// evaluation was reverted: EUF models no BitVec semantics, so the same read
/// answered ten other queries (among them `sfz/q/dtn/dtn_0001_named.smt2` and
/// `sfz/q/abv/abv_0103_plain.smt2`) with a literal that contradicts their own
/// `bvult` atoms. Model completion now offers the class value to the AUFLIA
/// lane's witness once, verified per variable against every atom that
/// mentions it (#uninterpreted-bitvec-class-values,
/// `executor/model/completion/bitvec_classes.rs`): `k` takes `#x00000001`,
/// the AUFLIA witness validates, and the merge carries it. Both shapes
/// answered `unknown` before; z3 answers `sat`.
#[test]
fn store_chain_read_at_variable_index_with_int_counter_is_sat() {
    for input in [
        r#"
        (set-logic ALL)
        (declare-const S (Array (_ BitVec 32) Bool))
        (declare-const n Int)
        (declare-const k (_ BitVec 32))
        (assert (= S ((as const (Array (_ BitVec 32) Bool)) false)))
        (assert (ite (select S #x00000001) (= 0 n) (= n 1)))
        (assert (select (store S #x00000001 true) k))
        (check-sat)
        (get-value (k n))
        "#,
        r#"
        (set-logic ALL)
        (declare-const S (Array (_ BitVec 32) Bool))
        (declare-const n Int)
        (declare-const k (_ BitVec 32))
        (assert (= S ((as const (Array (_ BitVec 32) Bool)) false)))
        (assert (= n (ite (select S #x00000001) 0 1)))
        (assert (select (store S #x00000001 true) k))
        (check-sat)
        (get-value (k n))
        "#,
    ] {
        let out = verdict(input);
        assert_eq!(out[0], "sat", "z3 answers `sat`:\n{input}");
        assert!(
            out[1].contains("(k #x00000001)") && out[1].contains("(n 1)"),
            "the only witnesses have k = 1 and n = 1, got {}:\n{input}",
            out[1]
        );
    }
}

/// The captured deductive-checks `maps.rs` Set-cardinality shape on the named-core
/// (assumption) route: a const Set domain, a `__ground_seed` anchor pinned to
/// a read, and a chain of Int counters through further reads (the head of
/// the C-3 capture, `85296-00299` dn0-dn4). The BV lane's assumption path
/// stores every read and the anchor as free Tseitin atoms; the merged
/// witness must follow the AUFLIA lane for all of them at once.
#[test]
fn named_cores_const_set_seed_anchor_and_counter_chain_is_sat() {
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-logic ALL)
        (declare-const S (Array (_ BitVec 32) Bool))
        (declare-const seed Bool)
        (declare-const n2 Int)
        (declare-const n3 Int)
        (declare-const n4 Int)
        (assert (! (= S ((as const (Array (_ BitVec 32) Bool)) false)) :named dn0))
        (assert (! (= (select S #x00000000) seed) :named dn1))
        (assert (! (ite (select S #x00000001) (= 0 n2) (= n2 1)) :named dn2))
        (assert (! (= n3 (+ n2 (ite (select S #x00000002) 0 1))) :named dn3))
        (assert (! (= n4 (+ n3 (ite (select S #x00000003) 0 1))) :named dn4))
        (check-sat)
    "#;
    assert_eq!(verdict(input), vec!["sat"]);
}

/// Controls: the reconciliation only re-values a CANDIDATE model, so every
/// refutation of the same shapes must stay `unsat`.
#[test]
fn reconciled_shapes_keep_their_refutations() {
    for (label, input) in [
        (
            "contradictory read",
            r#"
            (set-logic ALL)
            (declare-const A (Array (_ BitVec 32) Bool))
            (declare-const n Int)
            (assert (= n (ite (select A #x00000002) 0 1)))
            (assert (select A #x00000002))
            (assert (not (select A #x00000002)))
            (check-sat)
            "#,
        ),
        (
            "const domain forces the other branch",
            r#"
            (set-logic ALL)
            (declare-const A (Array (_ BitVec 32) Bool))
            (declare-const n Int)
            (assert (= A ((as const (Array (_ BitVec 32) Bool)) false)))
            (assert (= n (ite (select A #x00000002) 0 1)))
            (assert (= n 0))
            (check-sat)
            "#,
        ),
        (
            "direct read of a const-false domain",
            r#"
            (set-logic ALL)
            (declare-const S (Array (_ BitVec 32) Bool))
            (declare-const n Int)
            (declare-const k (_ BitVec 32))
            (assert (= S ((as const (Array (_ BitVec 32) Bool)) false)))
            (assert (ite (select S #x00000001) (= 0 n) (= n 1)))
            (assert (select S k))
            (check-sat)
            "#,
        ),
    ] {
        assert_eq!(verdict(input), vec!["unsat"], "{label}");
    }
}

// ==========================================================================
// Candidate SELECTION: the ladder must consult the validation oracle
// (#bv-lia-indep-final-assignment-reconcile, candidate ordering)
// ==========================================================================

/// The reconciled candidate is only PREFERRED when the ordinary model
/// validation accepts it independently for every root.
///
/// `restore_indep_bv_model_with_arith_graft` used to keep the first candidate
/// under which no root evaluates to a definite `false` under the executor's
/// OWN evaluator — which answers `Unknown` for exactly the array reads the
/// reconciliation re-values, so a candidate the strict model-validation
/// oracle goes on to REFUSE was indistinguishable from one it accepts and the
/// ladder never fell through to the previous merge policy. The three shapes
/// below (reduced from `sfz/q/quant/quant_0346_plain.smt2`,
/// `quant_0165_named.smt2` and `quant_0183_named.smt2`) are the measured
/// class: z3 answers `sat`, the commit before the reconciliation answers
/// `sat`, and they degraded to `unknown (incomplete)` on
/// "strict model-validation oracle arrays rejected assertion N".
#[test]
fn reconciled_candidate_losing_to_the_oracle_falls_back_to_the_graft() {
    for (label, input) in [
        (
            "store-chain read with a UF frame and an Int lane (quant_0346)",
            r#"
            (set-logic ALL)
            (declare-const A (Array (_ BitVec 8) (_ BitVec 8)))
            (declare-const B (Array (_ BitVec 8) (_ BitVec 8)))
            (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
            (declare-fun g ((_ BitVec 8)) (_ BitVec 8))
            (declare-const c0 (_ BitVec 8))
            (declare-const c1 (_ BitVec 8))
            (declare-const n Int)
            (assert (forall ((x0 (_ BitVec 8))) (= (f x0) (select A x0))))
            (assert (bvule (g (select B c1)) #x00))
            (assert (= n 1))
            (assert (bvule (select B c0) #x01))
            (assert (= B (store A #x04 c1)))
            (assert (not (= c0 #x03)))
            (check-sat)
            "#,
        ),
        (
            "Bool-element read plus a UF-of-read disequality (quant_0165)",
            r#"
            (set-logic ALL)
            (declare-const A (Array (_ BitVec 32) (_ BitVec 32)))
            (declare-const S (Array (_ BitVec 32) Bool))
            (declare-fun f ((_ BitVec 32)) (_ BitVec 32))
            (declare-fun g ((_ BitVec 32)) (_ BitVec 32))
            (declare-const c0 (_ BitVec 32))
            (declare-const c1 (_ BitVec 32))
            (declare-const n Int)
            (assert (forall ((x0 (_ BitVec 32))) (= (f x0) (select A x0))))
            (assert (forall ((x1 (_ BitVec 32)))
                (=> (bvult x1 #x00000002) (= (select A x1) #x00000003))))
            (assert (select S c0))
            (assert (not (= c1 (g (select A c0)))))
            (assert (<= n 2))
            (check-sat)
            "#,
        ),
    ] {
        assert_eq!(verdict(input), vec!["sat"], "{label}");
    }
}

/// The fallback must not become a licence: a candidate the oracle refuses
/// still cannot publish a verdict the query does not have. Every control
/// above stays `unsat`, and these two — which differ from the satisfiable
/// shapes only in the contradicting conjunct — stay `unsat` too.
#[test]
fn candidate_selection_keeps_its_refutations() {
    for (label, input) in [
        (
            "store-chain read contradicting its own bound",
            r#"
            (set-logic ALL)
            (declare-const A (Array (_ BitVec 8) (_ BitVec 8)))
            (declare-const B (Array (_ BitVec 8) (_ BitVec 8)))
            (declare-const c1 (_ BitVec 8))
            (declare-const n Int)
            (assert (= n 1))
            (assert (= B (store A #x04 c1)))
            (assert (= (select B #x04) #x07))
            (assert (bvule c1 #x01))
            (check-sat)
            "#,
        ),
        (
            "Bool-element read forced both ways",
            r#"
            (set-logic ALL)
            (declare-const S (Array (_ BitVec 32) Bool))
            (declare-const c0 (_ BitVec 32))
            (declare-const n Int)
            (assert (= n (ite (select S c0) 0 1)))
            (assert (select S c0))
            (assert (= n 1))
            (check-sat)
            "#,
        ),
    ] {
        assert_eq!(verdict(input), vec!["unsat"], "{label}");
    }
}

/// A read whose index the BV lane never valued must not be decided by an
/// interpretation this pass CREATES for its base array
/// (`sfz/q/abv2/abv_0475_named.smt2`; z3 and ay at `38d44a1333` answer
/// `sat`).
///
/// `(select S0 #x00000002)` is pinned by the final assignment, so the pass
/// wrote a fresh `ArrayInterpretation` for `S0` — whose TOTAL `false`
/// default then also answered `(select S0 (bvadd k0 #x00000001))`, a read
/// the pass could not resolve because the BV lane values no `k0`.
/// Completion closes `k0` downstream, the fabricated default decides the
/// unresolved read against the atom the candidate was accepted on, and the
/// gate fail-closes a genuine `sat` to `unknown (incomplete)`. The pins for
/// such a base now stay in the layers the BV lane itself uses.
///
/// Core production (`:named` assertions) is what routes this query through
/// the lane; the same query without it was never affected.
#[test]
fn unresolved_read_is_not_decided_by_a_created_interpretation() {
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-option :produce-models true)
        (set-logic ALL)
        (declare-const S0 (Array (_ BitVec 32) Bool))
        (declare-const n1 Int)
        (declare-const k0 (_ BitVec 32))
        (declare-const b0 Bool)
        (assert (! (ite (select S0 (bvadd k0 #x00000001)) (= 1 n1) (= n1 2)) :named dn1))
        (assert (! (= (select S0 #x00000002) b0) :named dn4))
        (check-sat)
    "#;
    assert_eq!(verdict(input), vec!["sat"]);
}

/// The same shape with the unresolved read FORCED against its counter is
/// never `sat`: declining to fabricate a default is not a licence to accept.
///
/// z3 answers `unsat`; ay declines it as `unknown (incomplete
/// self-check-rejected)` at `38d44a1333` and here alike — an unrelated
/// refutation-side incompleteness of this shape, measured identical on both
/// sides, so the assertion is the fail-closed property this change is
/// responsible for.
#[test]
fn unresolved_read_decline_never_publishes_sat() {
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-logic ALL)
        (declare-const S0 (Array (_ BitVec 32) Bool))
        (declare-const n1 Int)
        (declare-const k0 (_ BitVec 32))
        (declare-const b0 Bool)
        (assert (! (ite (select S0 (bvadd k0 #x00000001)) (= 1 n1) (= n1 2)) :named dn1))
        (assert (! (select S0 (bvadd k0 #x00000001)) :named dn2))
        (assert (! (= n1 2) :named dn3))
        (assert (! (= (select S0 #x00000002) b0) :named dn4))
        (check-sat)
    "#;
    assert_ne!(verdict(input), vec!["sat"]);
}

/// A read the pass cannot LOCATE must not be re-valued as a free atom, and
/// no cell of the base it reads through may be pinned
/// (`isweep/gq2/iabvx/iabvx_0104_named.smt2`, minimal repro
/// `isweep/min/m_04_0124.smt2`; z3 and ay at `38d44a1333` answer `sat`).
///
/// `(select S0 (bvadd k0 #x00000002))` has an index the merged model does not
/// evaluate — the BV lane values no `k0` — so this pass pins no cell for it,
/// yet it took the final assignment's `false` as a lane-opaque atom while
/// `(select S0 #x00000002)` pinned cell 2 to `true`. Model COMPLETION then
/// closed `k0 := 0`, landing the re-valued read on the cell pinned the other
/// way, and the strict model-validation oracle refused a witness the ladder
/// had already accepted ("arrays rejected assertion 3"), degrading a genuine
/// `sat` to `unknown (incomplete)`.
///
/// A read is now re-valued only as a consequence of pinning its cell, and a
/// base with an unlocatable read is pinned nowhere.
#[test]
fn an_unlocatable_read_is_not_revalued_against_a_pinned_cell() {
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-option :produce-models true)
        (set-logic ALL)
        (declare-const S0 (Array (_ BitVec 32) Bool))
        (declare-const S1 (Array (_ BitVec 32) Bool))
        (declare-const k0 (_ BitVec 32))
        (declare-const k1 (_ BitVec 32))
        (declare-const k2 (_ BitVec 32))
        (declare-const n0 Int)
        (declare-const n1 Int)
        (declare-const b0 Bool)
        (assert (! (and (<= 0 n1) (<= n0 1)) :named a0))
        (assert (! (select S0 #x00000002) :named a1))
        (assert (! (= (select S0 (bvadd k0 #x00000002)) (select S0 #x00000005)) :named a2))
        (assert (! (not (select S0 #x00000006)) :named a4))
        (check-sat)
    "#;
    assert_eq!(verdict(input), vec!["sat"]);
}

/// The fail-closed twin: with the open index CLOSED to the pinned cell and
/// the two reads forced apart, the same shape is unsatisfiable. Declining to
/// re-value an unlocatable read is not a licence to accept one.
#[test]
fn an_unlocatable_read_decline_never_publishes_sat() {
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-option :produce-models true)
        (set-logic ALL)
        (declare-const S0 (Array (_ BitVec 32) Bool))
        (declare-const k0 (_ BitVec 32))
        (declare-const n0 Int)
        (declare-const n1 Int)
        (assert (! (and (<= 0 n1) (<= n0 1)) :named a0))
        (assert (! (select S0 #x00000002) :named a1))
        (assert (! (= (select S0 (bvadd k0 #x00000002)) (select S0 #x00000005)) :named a2))
        (assert (! (= k0 #x00000000) :named a3))
        (assert (! (not (select S0 #x00000005)) :named a4))
        (check-sat)
    "#;
    assert_ne!(verdict(input), vec!["sat"]);
}
