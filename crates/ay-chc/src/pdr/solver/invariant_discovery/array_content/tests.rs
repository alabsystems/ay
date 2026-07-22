// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for array-content invariant synthesis.
//!
//! * **Increment 0** tests assert that frontier extraction **collects candidate
//!   index terms** on a tiny 2-array example — they do NOT assert that anything is
//!   proved (Increment 0 emits nothing into frames).
//! * **Increment 1** tests assert that the candidate generator produces the right
//!   value-fact atoms per element sort, that a genuinely-inductive candidate is
//!   **admitted** by the *unchanged* inductiveness gate, that a non-inductive
//!   candidate is **rejected** (soundness gate intact), and that the default-OFF
//!   flag path proposes nothing.

#![allow(clippy::unwrap_used)]

use super::{
    array_content_invariants_enabled_for, array_frontier_telemetry_enabled_for,
    array_value_fact_candidates, IndexTermFrontier, MAX_INDEX_TERMS,
};
use crate::pdr::config::PdrConfig;
use crate::pdr::solver::PdrSolver;
use crate::{ChcExpr, ChcParser, ChcSort, ChcVar};

/// A tiny 2-array predicate: `Inv(a: Array, b: Array, i: Int, n: Int)`.
///
/// - init stores into both arrays at index `i` and reads `select(a, i)`,
/// - the property reads `select(a, 0)` and `select(b, 0)`,
///
/// so the frontier has several distinct, expressible index-term sources
/// (constant 0, property index 0, store/select index `i`, scalar vars `i`/`n`).
const TWO_ARRAY_SMT2: &str = r#"
(set-logic HORN)
(declare-fun Inv ((Array Int Int) (Array Int Int) Int Int) Bool)
; init: a' = store(a,i,0), b' = store(b,i,0), with select(a,i) constrained
(assert
  (forall ((a (Array Int Int)) (b (Array Int Int)) (i Int) (n Int))
    (=>
      (and (= i 0)
           (= (select a i) 0)
           (= (select b i) 0))
      (Inv (store a i 0) (store b i 0) i n))))
; transition: bump i, keep arrays
(assert
  (forall ((a (Array Int Int)) (b (Array Int Int)) (i Int) (n Int))
    (=>
      (and (Inv a b i n) (< i n))
      (Inv a b (+ i 1) n))))
; property: a[0] and b[0] disagree -> false
(assert
  (forall ((a (Array Int Int)) (b (Array Int Int)) (i Int) (n Int))
    (=>
      (and (Inv a b i n) (not (= (select a 0) (select b 0))))
      false)))
(check-sat)
"#;

fn two_array_solver() -> PdrSolver {
    let problem = ChcParser::parse(TWO_ARRAY_SMT2).expect("parse 2-array CHC");
    PdrSolver::new(problem, PdrConfig::default())
}

// ---------------------------------------------------------------------------
// Flag parsing (default OFF)
// ---------------------------------------------------------------------------

#[test]
fn telemetry_flag_defaults_off() {
    // Unset / empty / falsy values keep the pass OFF (hot path untouched).
    assert!(!array_frontier_telemetry_enabled_for(None));
    assert!(!array_frontier_telemetry_enabled_for(Some("")));
    assert!(!array_frontier_telemetry_enabled_for(Some("0")));
    assert!(!array_frontier_telemetry_enabled_for(Some("false")));
    assert!(!array_frontier_telemetry_enabled_for(Some("nope")));
}

#[test]
fn telemetry_flag_explicit_truthy_enables() {
    for v in ["1", "true", "TRUE", "yes", "on", " On "] {
        assert!(
            array_frontier_telemetry_enabled_for(Some(v)),
            "{v:?} should enable the telemetry pass"
        );
    }
}

// ---------------------------------------------------------------------------
// Array-param identification on a 2-array predicate
// ---------------------------------------------------------------------------

#[test]
fn detects_two_array_params() {
    let solver = two_array_solver();
    let inv = solver.problem.lookup_predicate("Inv").unwrap();

    let params = solver.array_canonical_params(inv);
    assert_eq!(
        params.len(),
        2,
        "Inv has exactly two Array-sorted parameters"
    );
    // Element sort of (Array Int Int) is Int.
    for ap in &params {
        assert_eq!(ap.elem_sort, ChcSort::Int);
        assert!(matches!(ap.var.sort, ChcSort::Array(_, _)));
    }
    // The two array params are the first two args (positions 0 and 1).
    assert_eq!(params[0].pos, 0);
    assert_eq!(params[1].pos, 1);
}

// ---------------------------------------------------------------------------
// Frontier extraction COLLECTS candidates (the core Increment-0 assertion)
// ---------------------------------------------------------------------------

#[test]
fn frontier_collects_candidate_index_terms() {
    let solver = two_array_solver();
    let inv = solver.problem.lookup_predicate("Inv").unwrap();

    let frontier = solver.index_term_frontier(inv);

    // The pass must COLLECT candidates (not prove anything).
    assert!(
        !frontier.is_empty(),
        "frontier should collect at least one candidate index term"
    );
    // Bounded by the cap.
    assert!(
        frontier.len() <= MAX_INDEX_TERMS,
        "frontier must respect MAX_INDEX_TERMS cap"
    );
    // Constant 0 is always seeded (cheapest, highest-value base index).
    assert!(
        frontier.terms.contains(&ChcExpr::Int(0)),
        "constant 0 must be in the frontier; got {:?}",
        frontier.terms
    );
    // Structurally deduped: no duplicate terms.
    for (i, t) in frontier.terms.iter().enumerate() {
        assert!(
            !frontier.terms[i + 1..].contains(t),
            "frontier should be structurally deduped; {t:?} repeated"
        );
    }
}

#[test]
fn frontier_includes_a_scalar_index_var() {
    // With only the constant 0 and the property index 0 (which collapses to the
    // same term), the scalar loop counter `i`/bound `n` should still be admitted
    // as candidate indices, so the frontier carries more than just `0`.
    let solver = two_array_solver();
    let inv = solver.problem.lookup_predicate("Inv").unwrap();

    let frontier = solver.index_term_frontier(inv);
    let has_scalar_var = frontier
        .terms
        .iter()
        .any(|t| matches!(t, ChcExpr::Var(v) if matches!(v.sort, ChcSort::Int)));
    assert!(
        has_scalar_var,
        "frontier should collect at least one scalar (Int) index var; got {:?}",
        frontier.terms
    );
}

// ---------------------------------------------------------------------------
// Telemetry counter: >=2-array predicates seen (analysis only, no frames)
// ---------------------------------------------------------------------------

#[test]
fn telemetry_pass_emits_no_frames() {
    // Even if the global flag happened to be enabled, the pass must never touch
    // frames. We assert frame[1] is unchanged by direct frontier extraction
    // (which is what the telemetry pass does internally).
    let solver = two_array_solver();
    let inv = solver.problem.lookup_predicate("Inv").unwrap();

    let frame1_before = solver.frames[1].lemmas.len();
    let _frontier = solver.index_term_frontier(inv);
    let frame1_after = solver.frames[1].lemmas.len();
    assert_eq!(
        frame1_before, frame1_after,
        "Increment-0 frontier extraction must not emit any lemma into frames"
    );
}

#[test]
fn single_array_predicate_has_no_multi_array_frontier_pair() {
    // A predicate with one array param must report fewer than 2 array params,
    // so later increments' >=2 gate would skip it; the frontier still extracts.
    let smt2 = r#"
(set-logic HORN)
(declare-fun One ((Array Int Int) Int) Bool)
(assert (forall ((a (Array Int Int)) (i Int))
  (=> (= (select a i) 0) (One a i))))
(assert (forall ((a (Array Int Int)) (i Int))
  (=> (and (One a i) (< (select a i) 0)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let solver = PdrSolver::new(problem, PdrConfig::default());
    let one = solver.problem.lookup_predicate("One").unwrap();
    assert_eq!(solver.array_canonical_params(one).len(), 1);
    // Frontier still collects (it helps for one array too, per spec §3.2).
    assert!(!solver.index_term_frontier(one).is_empty());
}

// ---------------------------------------------------------------------------
// IndexTermFrontier cap / dedup unit behavior
// ---------------------------------------------------------------------------

#[test]
fn frontier_caps_and_dedups() {
    let mut f = IndexTermFrontier::default();
    // dedup: pushing the same term twice keeps one.
    assert!(f.try_push(ChcExpr::Int(0)));
    assert!(!f.try_push(ChcExpr::Int(0)));
    assert_eq!(f.len(), 1);

    // fill to the cap.
    let mut n = 1i128;
    while f.len() < MAX_INDEX_TERMS {
        assert!(f.try_push(ChcExpr::Int(n)));
        n += 1;
    }
    assert_eq!(f.len(), MAX_INDEX_TERMS);
    // cap: further distinct pushes are rejected.
    assert!(!f.try_push(ChcExpr::Int(9999)));
    assert_eq!(f.len(), MAX_INDEX_TERMS);
}

// ===========================================================================
// Increment 1 — single-array value-fact candidate generation + admission gate
// ===========================================================================

// ---------------------------------------------------------------------------
// AY_CHC_ARRAY_INV flag parsing (default OFF), mirrors the telemetry flag.
// ---------------------------------------------------------------------------

#[test]
fn array_inv_flag_defaults_off() {
    assert!(!array_content_invariants_enabled_for(None));
    assert!(!array_content_invariants_enabled_for(Some("")));
    assert!(!array_content_invariants_enabled_for(Some("0")));
    assert!(!array_content_invariants_enabled_for(Some("false")));
    assert!(!array_content_invariants_enabled_for(Some("nope")));
}

#[test]
fn array_inv_flag_explicit_truthy_enables() {
    for v in ["1", "true", "TRUE", "yes", "on", " On "] {
        assert!(
            array_content_invariants_enabled_for(Some(v)),
            "{v:?} should enable the array-content invariant pass"
        );
    }
}

// ---------------------------------------------------------------------------
// Candidate atom shapes per element sort.
// ---------------------------------------------------------------------------

fn arr_var(name: &str, key: ChcSort, val: ChcSort) -> ChcVar {
    ChcVar {
        name: name.to_string(),
        sort: ChcSort::Array(Box::new(key), Box::new(val)),
    }
}

#[test]
fn int_element_value_facts_are_ge0_and_eq0() {
    let a = arr_var("a", ChcSort::Int, ChcSort::Int);
    let t = ChcExpr::Int(0);
    let mut out = Vec::new();
    array_value_fact_candidates(&a, &ChcSort::Int, &t, &mut out);

    // Exactly two candidates: select(a,0) >= 0 and select(a,0) = 0.
    assert_eq!(out.len(), 2, "Int element should yield >=0 and =0: {out:?}");
    let sel = ChcExpr::select(ChcExpr::var(a.clone()), t.clone());
    assert!(out.contains(&ChcExpr::ge(sel.clone(), ChcExpr::int(0))));
    assert!(out.contains(&ChcExpr::eq(sel, ChcExpr::int(0))));

    // Every candidate is Bool-sorted at top level (passes admission line 36) and
    // is NOT an array-sorted equality (passes admission line 54).
    for cand in &out {
        assert!(
            cand.is_bool_sorted_top_level(),
            "candidate must be Bool-sorted top-level: {cand}"
        );
        assert!(cand.contains_array_ops(), "candidate must mention select");
    }
}

#[test]
fn bool_element_value_facts_are_eq_true_and_eq_false() {
    let v = arr_var("v", ChcSort::Int, ChcSort::Bool);
    let t = ChcExpr::Int(0);
    let mut out = Vec::new();
    array_value_fact_candidates(&v, &ChcSort::Bool, &t, &mut out);

    assert_eq!(out.len(), 2, "Bool element should yield =true and =false");
    let sel = ChcExpr::select(ChcExpr::var(v.clone()), t.clone());
    assert!(out.contains(&ChcExpr::eq(sel.clone(), ChcExpr::bool_const(true))));
    assert!(out.contains(&ChcExpr::eq(sel, ChcExpr::bool_const(false))));
    for cand in &out {
        assert!(cand.is_bool_sorted_top_level());
    }
}

#[test]
fn unsupported_element_sort_yields_no_candidate() {
    // BitVec / Real element value facts are deliberately not emitted in Increment 1.
    let a = arr_var("a", ChcSort::Int, ChcSort::BitVec(32));
    let mut out = Vec::new();
    array_value_fact_candidates(&a, &ChcSort::BitVec(32), &ChcExpr::Int(0), &mut out);
    assert!(
        out.is_empty(),
        "BV element should emit nothing in Increment 1"
    );
}

// ---------------------------------------------------------------------------
// Cost gates: <2 array params, and no-array problems, propose nothing.
// ---------------------------------------------------------------------------

#[test]
fn inner_pass_skips_when_fewer_than_two_array_params() {
    // One array param: the >=2 cost gate must short-circuit with 0 admitted and
    // no lemma emitted, even when invoked directly (flag-independent inner).
    let smt2 = r#"
(set-logic HORN)
(declare-fun One ((Array Int Int) Int) Bool)
(assert (forall ((a (Array Int Int)) (i Int))
  (=> (>= (select a i) 0) (One a i))))
(assert (forall ((a (Array Int Int)) (i Int))
  (=> (and (One a i) (< (select a i) 0)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let before: usize = solver.frames.iter().map(|f| f.lemmas.len()).sum();
    let admitted = solver.discover_array_content_invariants_inner();
    let after: usize = solver.frames.iter().map(|f| f.lemmas.len()).sum();
    assert_eq!(
        admitted, 0,
        "1-array problem must admit nothing (cost gate)"
    );
    assert_eq!(before, after, "1-array problem must emit no lemma");
}

// ---------------------------------------------------------------------------
// The flag-gated entry point proposes NOTHING by default (default-OFF path).
// ---------------------------------------------------------------------------

#[test]
fn flag_gated_entry_point_is_noop_by_default() {
    // With AY_CHC_ARRAY_INV unset (the test default), the public entry point must
    // be a no-op: 0 admitted, no frame mutation. This is the byte-for-byte
    // default-path guarantee.
    let problem = ChcParser::parse(TWO_ARRAY_VALUE_SMT2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let before: usize = solver.frames.iter().map(|f| f.lemmas.len()).sum();
    let admitted = solver.discover_array_content_invariants();
    let after: usize = solver.frames.iter().map(|f| f.lemmas.len()).sum();
    assert_eq!(
        admitted, 0,
        "default-OFF flag must propose/admit nothing (got {admitted})"
    );
    assert_eq!(before, after, "default-OFF flag must not mutate frames");
}

// A 2-array predicate whose inductive core is single-array value facts at the
// SYMBOLIC index `t`: both arrays are filled with non-negative values at index
// `t` each step, so `select(a,t) >= 0` and `select(b,t) >= 0` hold and are
// preserved. Init states the facts directly so they are init-valid.
const TWO_ARRAY_VALUE_SMT2: &str = r#"
(set-logic HORN)
(declare-fun Inv ((Array Int Int) (Array Int Int) Int) Bool)
(assert
  (forall ((a (Array Int Int)) (b (Array Int Int)) (t Int))
    (=> (and (>= (select a t) 0) (>= (select b t) 0)) (Inv a b t))))
(assert
  (forall ((a (Array Int Int)) (b (Array Int Int)) (t Int)
           (a2 (Array Int Int)) (b2 (Array Int Int)) (v Int) (w Int))
    (=> (and (Inv a b t) (>= v 0) (>= w 0)
             (= a2 (store a t v)) (= b2 (store b t w)))
        (Inv a2 b2 t))))
(assert
  (forall ((a (Array Int Int)) (b (Array Int Int)) (t Int))
    (=> (and (Inv a b t) (or (< (select a t) 0) (< (select b t) 0))) false)))
(check-sat)
"#;

// ---------------------------------------------------------------------------
// SOUNDNESS: a genuinely-inductive candidate is ADMITTED by the unchanged gate;
// a non-inductive candidate is REJECTED. The pass NEVER bypasses the gate.
// ---------------------------------------------------------------------------

#[test]
fn inductive_array_value_fact_is_admitted_by_unchanged_gate() {
    // The pass should generate `select(a,t) >= 0` / `select(b,t) >= 0` at the
    // symbolic frontier index `t` and the EXISTING admission gate should accept at
    // least one of them (it is init-valid and self-inductive). We call the
    // flag-independent inner pass directly.
    let problem = ChcParser::parse(TWO_ARRAY_VALUE_SMT2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    // Sanity: this is a genuine >=2-array problem.
    assert_eq!(solver.max_array_params, 2);

    let admitted = solver.discover_array_content_invariants_inner();
    assert!(
        admitted >= 1,
        "the unchanged inductiveness gate should admit at least one synthesized \
         array value fact; admitted={admitted}"
    );

    // The admitted lemma is a Bool-sorted select-based fact in some frame.
    let any_select_lemma = solver.frames.iter().any(|f| {
        f.lemmas
            .iter()
            .any(|l| l.formula.contains_array_ops() && l.formula.is_bool_sorted_top_level())
    });
    assert!(
        any_select_lemma,
        "an admitted array value fact should be present as a frame lemma"
    );
}

#[test]
fn non_inductive_array_value_fact_is_rejected_by_unchanged_gate() {
    // Directly hand the gate a candidate of the same shape the pass produces, but
    // one that is NOT init-valid: `select(a,t) >= 5`. Init only guarantees
    // `select(a,t) >= 0`, so the gate MUST reject it. This proves the pass cannot
    // launder a bad candidate into a frame — soundness lives in the unchanged gate.
    let problem = ChcParser::parse(TWO_ARRAY_VALUE_SMT2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let inv = solver.problem.lookup_predicate("Inv").unwrap();

    let canon = solver.canonical_vars(inv).unwrap().to_vec();
    // Canonical array param `a` is position 0, scalar index `t` is position 2.
    let a = canon[0].clone();
    let t = canon[2].clone();
    assert!(matches!(a.sort, ChcSort::Array(_, _)));
    assert!(matches!(t.sort, ChcSort::Int));

    let bad = ChcExpr::ge(
        ChcExpr::select(ChcExpr::var(a), ChcExpr::var(t)),
        ChcExpr::int(5),
    );
    let admitted = solver.add_discovered_invariant(inv, bad.clone(), 1);
    assert!(
        !admitted,
        "non-init-valid array value fact `select(a,t) >= 5` must be rejected by \
         the unchanged gate"
    );
    assert!(
        solver.frames.iter().all(|f| !f.contains_lemma(inv, &bad)),
        "rejected candidate must not appear in any frame"
    );
}
