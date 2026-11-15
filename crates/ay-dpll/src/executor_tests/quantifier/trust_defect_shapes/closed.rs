// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The shapes that now DECIDE, and the guards that must keep holding while
//! they do. See the parent module for the whole story.

use super::*;

// ---------------------------------------------------------------------------
// CLOSED — `FP`: `forall q:Float64. fp.isNaN(q)`.
// ---------------------------------------------------------------------------

/// TRUTH, established independently: the universal is FALSE, because
/// `fp.isNaN(+zero)` is false — a GROUND floating-point fact with no quantifier
/// in it, decided by the FP lane on its own below. A false universal asserted
/// alone is unsatisfiable.
#[test]
fn fp_isnan_at_plus_zero_is_ground_false() {
    assert_eq!(
        solve_one(
            r#"
            (set-logic QF_FP)
            (assert (fp.isNaN (_ +zero 11 53)))
            (check-sat)
        "#,
        ),
        "unsat",
        "the independent truth this shape rests on: +0.0 is not NaN"
    );
}

/// THE SHAPE. Previously `unknown (incomplete quantifier-unhandled)`.
///
/// TWO things were missing, and the first alone does nothing:
///
/// 1. `synthesize_mbqi_candidates` had no FP arm at all, so there was no value
///    to instantiate at even if MBQI had been asked.
/// 2. MBQI WAS NEVER ASKED. The FP binder sort sets
///    `has_unsafe_partial_quantifiers`, and that guard's early return in
///    `classify_quantifier_result` fires BEFORE the MBQI arm further down the
///    same classification. So the shape degraded without any refutation
///    attempt. `unsafe_partial_mbqi_refutation` now asks, inside the guard,
///    and accepts ONLY an `Unsat`.
///
/// Both halves are refutation devices and nothing else: instantiating
/// `forall x. P(x)` at a closed value yields a consequence of the universal in
/// every model, so they can only turn a withheld `Sat` into a genuine `Unsat`.
///
/// THE ARTIFACT GATE STILL DECIDES WHAT MAY BE SPOKEN, and it was not widened.
/// Measured across the rigor ladder on this exact query with `:produce-proofs`:
/// `--rigor standard` → `unsat` (the refutation reaches
/// `translate_refinement_seeded_replay`, which mints an authored artifact);
/// `--rigor strict` → `unknown (incomplete proof-trusted)`; `--rigor certified`
/// → `unknown (incomplete quantifier-unhandled)`. The two stronger levels fail
/// closed on the artifact exactly as they did before, which is the system
/// working — `FP` sits one rung above `BVFP` (which cannot mint an artifact at
/// all), not past the gate. This test runs at the default standard rigor.
#[test]
fn fp_forall_isnan_decides_unsat() {
    assert_eq!(
        solve_one(
            r#"
            (set-logic FP)
            (assert (forall ((q (_ FloatingPoint 11 53))) (fp.isNaN q)))
            (check-sat)
        "#,
        ),
        "unsat",
        "trust shape `FP`: refuted at +0.0 by an MBQI FP candidate"
    );
}

/// The candidate list must NOT buy a `sat`. A satisfiable FP universal that the
/// candidates cannot exhaust stays `unknown`: six values are not the `Float64`
/// carrier, and `is_mbqi_unsafe_binder_sort` still lists `FloatingPoint`
/// precisely so a survived candidate sweep is never mistaken for
/// exhaustiveness.
///
/// TRUTH, established independently: `forall q. (or (fp.isNaN q) (not (fp.isNaN
/// q)))` is a tautology, so the assertion is satisfiable. A `sat` here would be
/// correct-by-luck; what must NEVER appear is `unsat`.
#[test]
fn fp_forall_tautology_is_never_refuted() {
    let verdict = solve_one(
        r#"
        (set-logic FP)
        (assert (forall ((q (_ FloatingPoint 11 53))) (or (fp.isNaN q) (not (fp.isNaN q)))))
        (check-sat)
    "#,
    );
    assert_ne!(
        verdict, "unsat",
        "a tautological FP universal must never be refuted: every MBQI \
         instance is a CONSEQUENCE, so no instance can falsify one"
    );
}

/// The complementary direction, and the one that would be a real wrong answer:
/// a SATISFIABLE FP universal whose truth needs more than the candidate list.
/// `forall q. (fp.leq (fp.abs q) (fp.abs q))` holds for every non-NaN and is
/// vacuously fine to instantiate; the point is only that no candidate sweep
/// produces `unsat`.
#[test]
fn fp_forall_satisfiable_shape_is_not_refuted() {
    let verdict = solve_one(
        r#"
        (set-logic FP)
        (declare-const c (_ FloatingPoint 11 53))
        (assert (forall ((q (_ FloatingPoint 11 53))) (= (fp.abs q) (fp.abs q))))
        (assert (fp.isNaN c))
        (check-sat)
    "#,
    );
    assert_ne!(
        verdict, "unsat",
        "an FP universal that is true in every model must not be refuted"
    );
}

// ---------------------------------------------------------------------------
// CLOSED — `ANIA`: `forall q:Int. heap[q] * heap[q] > 0`.
// ---------------------------------------------------------------------------

/// TRUTH, established independently and WITHOUT a quantifier answer: the
/// witness is `heap = (as const (Array Int Int)) 1`. Pinning `heap` to that
/// constant array and asserting the SAME body at arbitrary ground indices is
/// satisfiable, so a model of the pinned problem exists; a model of a STRONGER
/// problem is a model of the weaker one, so the unpinned shape is satisfiable
/// too.
#[test]
fn ania_witness_heap_is_the_constant_one_array() {
    assert_eq!(
        solve_one(
            r#"
            (set-logic QF_ANIA)
            (declare-const heap (Array Int Int))
            (assert (= heap ((as const (Array Int Int)) 1)))
            (assert (> (* (select heap 0) (select heap 0)) 0))
            (assert (> (* (select heap 7) (select heap 7)) 0))
            (assert (> (* (select heap (- 3)) (select heap (- 3))) 0))
            (check-sat)
        "#,
        ),
        "sat",
        "the independent witness: heap = 1 everywhere satisfies the body"
    );
}

/// THE SHAPE. Previously `unknown (incomplete quantifier-unhandled)`.
///
/// The Int binder INDEXES an array, so `forall_indexes_array_at_binder` flags
/// the `forall` MBQI-unsafe (the ay#8729 / Z3#6303 extensionality guard) and a
/// ground `Sat` cannot be published. Publishing needs a CERTIFIED
/// interpretation, and the constant-interpretation certificate used to decline:
/// it offered exactly one array candidate, the constant array over the element
/// sort's FIRST candidate (`heap = 0`), under which the body folds to `0 > 0`
/// and the sole combination is refuted.
///
/// Closed by offering one constant array per element candidate, so `heap = 1`
/// is reachable. Grant-only: candidates are untrusted PROPOSALS and the
/// certificate re-refutes every axiom and ground conjunct under the chosen
/// interpretation through `checked_ground_solve`, accepting only a
/// strict-proof-certified Unsat token. The guard itself is untouched.
///
/// Measured across the whole rigor ladder with `:produce-proofs`: `sat` at
/// `standard`, `strict` AND `certified` — the fail-closed level that emits only
/// answers ay can self-verify — and the published model is exactly the witness
/// this section established independently:
/// `(define-fun heap () (Array Int Int) ((as const (Array Int Int)) 1))`.
#[test]
fn ania_forall_decides_sat() {
    assert_eq!(
        solve_one(
            r#"
            (set-logic ANIA)
            (declare-const heap (Array Int Int))
            (assert (forall ((q Int)) (> (* (select heap q) (select heap q)) 0)))
            (check-sat)
        "#,
        ),
        "sat",
        "trust shape `ANIA`: certified by the constant interpretation heap = 1"
    );
}

/// The widened array family must not buy a wrong `sat`. Same shape, but the
/// body is UNSATISFIABLE over every array: `heap[q] * heap[q] < 0` has no
/// integer solution at any index, so no constant array — and no array at all —
/// can certify it.
///
/// TRUTH, established independently: a single ground instance is already
/// unsatisfiable (below), and a universal entails each of its instances.
#[test]
fn ania_negative_square_ground_instance_is_unsat() {
    assert_eq!(
        solve_one(
            r#"
            (set-logic QF_ANIA)
            (declare-const heap (Array Int Int))
            (assert (< (* (select heap 0) (select heap 0)) 0))
            (check-sat)
        "#,
        ),
        "unsat",
        "no integer square is negative — the ground instance settles it"
    );
}

#[test]
fn ania_unsatisfiable_body_is_never_certified_sat() {
    let verdict = solve_one(
        r#"
        (set-logic ANIA)
        (declare-const heap (Array Int Int))
        (assert (forall ((q Int)) (< (* (select heap q) (select heap q)) 0)))
        (check-sat)
    "#,
    );
    assert_ne!(
        verdict, "sat",
        "the constant-interpretation certificate must never grant a shape \
         whose ground instance is already unsatisfiable"
    );
}

// ---------------------------------------------------------------------------
// CLOSED in the bridge — `ABVFP`. ay always decided it; see
// `ay-bindings::execute_direct::tests::test_bridge_errors` for the binder/model
// regression. Pinned HERE as the solver-side half: the solver decides it.
// ---------------------------------------------------------------------------

/// TRUTH, established independently and WITHOUT an array or a quantifier:
/// `fromBits(0x7ff8000000000000)` IS NaN — asserting its negation is
/// unsatisfiable. So `mem` constantly that pattern makes the body true at every
/// one of the 256 indices, and the shape is SAT.
#[test]
fn abvfp_witness_bit_pattern_really_is_nan() {
    assert_eq!(
        solve_one(&format!(
            r#"
            (set-logic QF_BVFP)
            (assert (not (fp.isNaN {})))
            (check-sat)
        "#,
            from_bits_f64("#x7ff8000000000000")
        )),
        "unsat",
        "the independent witness: the quiet-NaN pattern really is NaN, so \
         `mem` constantly equal to it satisfies the body at every index"
    );
}

/// THE SHAPE, solver side: ay decides it, with a model. The defect trust
/// measured was never here — the typed model extractor in the BRIDGE asked the
/// model for a value of the BOUND variable and threw the verdict away.
#[test]
fn abvfp_forall_decides_sat() {
    assert_eq!(
        solve_one(&format!(
            r#"
            (set-logic ABVFP)
            (set-option :produce-proofs true)
            (declare-const mem (Array (_ BitVec 8) (_ BitVec 64)))
            (assert (forall ((q (_ BitVec 8))) (fp.isNaN {})))
            (check-sat)
        "#,
            from_bits_f64("(select mem q)")
        )),
        "sat",
        "trust shape `ABVFP`: the solver decides it — the defect was the \
         bridge's model extractor, not this verdict"
    );
}

// ---------------------------------------------------------------------------
// THE GUARD THE REFUTATION RESCUE RUNS INSIDE. These are not shape pins: they
// are what must stay true for the rescue to be allowed to exist at all.
// ---------------------------------------------------------------------------

/// THE ay#8729 / Z3#6303 WRONG-SAT REPRODUCER, and the reason
/// `is_mbqi_unsafe_binder_sort` / `forall_indexes_array_at_binder` exist.
///
/// `(forall i. a[i] = b[i]) AND a != b` is UNSAT under array extensionality.
/// E-matching instantiates only indices that already occur ground, so the
/// ground problem is satisfiable and a published `Sat` here would be WRONG. The
/// answer must never be `sat`.
#[test]
fn array_extensionality_wrong_sat_is_still_refused() {
    assert_ne!(
        solve_one(
            r#"
            (set-logic AUFLIA)
            (declare-const a (Array Int Int))
            (declare-const b (Array Int Int))
            (assert (forall ((i Int)) (= (select a i) (select b i))))
            (assert (not (= a b)))
            (check-sat)
        "#,
        ),
        "sat",
        "extensionality makes this UNSAT; a `sat` is the ay#8729 wrong answer"
    );
}

/// The SATISFIABLE half of the same guard: `forall i. a[i] = b[i]` alone is
/// satisfiable (take `a = b`). Refuting it would be a wrong `unsat`, which is
/// exactly what a careless refutation rescue could introduce.
#[test]
fn array_extensionality_satisfiable_half_is_not_refuted() {
    assert_ne!(
        solve_one(
            r#"
            (set-logic AUFLIA)
            (declare-const a (Array Int Int))
            (declare-const b (Array Int Int))
            (assert (forall ((i Int)) (= (select a i) (select b i))))
            (check-sat)
        "#,
        ),
        "unsat",
        "a = b satisfies this; refuting it would be a wrong unsat"
    );
}

/// #quant-alternation: a `forall` in DISJUNCTIVE position must not be refuted
/// as if it were a conjunct. `p OR (forall q:Float64. fp.isNaN q)` is
/// SATISFIABLE at `p = true` even though the universal is false, so the
/// refutation rescue has to decline on position — the FP candidates now make
/// the disjunct refutable, which is precisely why the position check matters.
#[test]
fn false_forall_in_disjunctive_position_does_not_refute_the_query() {
    assert_ne!(
        solve_one(
            r#"
            (set-logic FP)
            (declare-const p Bool)
            (assert (or p (forall ((q (_ FloatingPoint 11 53))) (fp.isNaN q))))
            (check-sat)
        "#,
        ),
        "unsat",
        "p = true satisfies the disjunction: a false DISJUNCT refutes nothing"
    );
}

/// The array-candidate widening must not manufacture a `sat` for a body no
/// array can satisfy, and must not manufacture an `unsat` either. `forall q.
/// h[q] = 1` with `h[3] = 2` asserted is UNSAT — established independently by
/// the ground instance `h[3] = 1 AND h[3] = 2`.
#[test]
fn constant_array_candidates_do_not_certify_a_contradicted_pin() {
    assert_eq!(
        solve_one(
            r#"
            (set-logic QF_ALIA)
            (declare-const h (Array Int Int))
            (assert (= (select h 3) 1))
            (assert (= (select h 3) 2))
            (check-sat)
        "#,
        ),
        "unsat",
        "the independent truth: h[3] cannot be both 1 and 2"
    );
    assert_ne!(
        solve_one(
            r#"
            (set-logic ALIA)
            (declare-const h (Array Int Int))
            (assert (forall ((q Int)) (= (select h q) 1)))
            (assert (= (select h 3) 2))
            (check-sat)
        "#,
        ),
        "sat",
        "the constant-array candidate `h = 1` is REFUTED by `h[3] = 2`; the \
         certificate re-checks every ground conjunct before granting"
    );
}
