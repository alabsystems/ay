// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array-theory wrong verdicts from the 2026-09-23 differential hunt
//! (defects D4, D12, A1 and the invalid printed model M2), minimized and
//! embedded so the pins need no corpus. z3 5.1.0 answers `sat` on every
//! instance and its model re-checks `sat`.
//!
//! Main `f399eca07a` answered `unsat` on each of the first six in at least one
//! posture. Four separate producers of wrong facts in `ay-theories/arrays`:
//!
//! * D4-a `effective_read_value_at` skipped a store entry whose index is
//!   provably distinct from the probe index and dropped the reasons, so the
//!   store-chain value conflict was unconditional in that index relation.
//! * D4-b (= D12) the partial effective-store walker remembered only the
//!   ADMITTED outer store indices, so a skipped store could not shadow a
//!   deeper store at its index; the effective-store decomposition then
//!   propagated `1 = 2`.
//! * D4-c the store-permutation scan emitted chain equalities from those
//!   partial maps.
//! * D4-d the default-const lemma dropped its `X = const(v)` antecedent when
//!   the two were equal through a path, emitting a unit `default(X) = v`.
//!
//! A1 panicked (index out of bounds in the term store) because the read-pin
//! repair kept a sentinel `TermId` inside `EufModel::term_values`.
//!
//! M2 printed `g = (const 0)` while the gate confirmed the model from a
//! per-application pin of `(g (+ i2 1))` that the printed `g` contradicts.
//!
//! Every pin states only what the defect denied: never `unsat`, never an
//! abort; `unknown` is a completeness loss, not a wrong answer. Each runs in
//! the default executor posture and in the proof-free competition posture
//! (`--z3-mode` / `--no-proof`), where some of these were wrong only.

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn solve(src: &str, competition: bool) -> Vec<String> {
    let commands = parse(src).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    exec.set_competition_mode(competition);
    exec.set_timeout(Some(Duration::from_secs(20)));
    exec.set_memory_limit(Some(8 << 30));
    // A panic inside the solver propagates out of `execute_all` and fails the
    // test at the site that fired.
    exec.execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"))
}

fn assert_never_unsat(name: &str, src: &str) {
    for competition in [false, true] {
        let outputs = solve(src, competition);
        let verdict = outputs.first().cloned().unwrap_or_default();
        assert!(
            verdict == "sat" || verdict == "unknown",
            "{name} (competition={competition}): z3 5.1.0 answers sat and its model \
             re-checks; AY answered {verdict:?} ({outputs:?})"
        );
    }
}

fn assert_sat_both_postures(name: &str, src: &str) {
    for competition in [false, true] {
        let outputs = solve(src, competition);
        assert_eq!(
            outputs.first().map(String::as_str),
            Some("sat"),
            "{name} (competition={competition}): {outputs:?}"
        );
    }
}

/// D4-a, one assertion (`w2_const/w2_min.smt2`): `i = 0`, `a0 = (const 2)`.
const D4A_W2: &str = r#"
(set-logic QF_ALIA)
(declare-fun a0 () (Array Int Int))
(declare-fun i () Int)
(assert (= (store ((as const (Array Int Int)) 1) (+ i 1) 2) (store ((as const (Array Int Int)) 1) 1 (select (store a0 5 2) i))))
(check-sat)
"#;

/// D4-b with no const array at all: `i = j = 5`, `v = 2`, `b = c`.
const D4B_FREE_BASES: &str = r#"
(set-logic QF_ALIA)
(declare-fun b () (Array Int Int))
(declare-fun c () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun v () Int)
(assert (= (store (store (store b j 1) i v) 2 j) (store (store c j 2) 2 5)))
(check-sat)
"#;

/// D4-b, `storeeq_41_0293.min.smt2`: the file the checked-sat-refutation lane
/// admitted (hole step `(= S S') -> (not (= j 5))`).
const D4B_0293: &str = r#"
(set-logic QF_ALIA)
(declare-fun a0 () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun k () Int)
(assert (= (store (store (store b j 1) i (select a0 2)) 2 j) (store (store (store ((as const (Array Int Int)) 0) 0 k) j 2) 2 5)))
(check-sat)
"#;

/// D12 (`w3_finstore/min.smt2`): the `(Array Bool Bool)` wrong UNSAT is D4-b,
/// not finite extensionality. z3: `x0 = true, v0 = false, x1 = false`.
const D12_BOOL_FINSTORE: &str = r#"
(set-logic ALL)
(declare-fun a1 () (Array Bool Bool))
(declare-fun a2 () (Array Bool Bool))
(declare-fun a3 () (Array Bool Bool))
(declare-fun x0 () Bool)
(declare-fun x1 () Bool)
(declare-fun v0 () Bool)
(assert (= (store (store a2 false true) true true) (store ((as const (Array Bool Bool)) true) x1 true)))
(assert (or (= (store (store (store a3 true false) x0 v0) x0 true) a2) (= a2 (store (store (store a3 x1 true) x0 true) true true))))
(assert (= a1 (store (store ((as const (Array Bool Bool)) false) true true) x0 false)))
(assert (= (select (store (store a2 true false) false false) true) (select (store (store (store (store a3 false true) true v0) x1 false) x1 true) x0)))
(check-sat)
"#;

/// D4-c, `storeeq_41_0883.min.smt2`: the store-permutation scan derived
/// `store(store(b, 2, R), i, V) = store(store(K1, 2, 2), i, V)` from `b = K1`.
const D4C_0883: &str = r#"
(set-logic QF_ALIA)
(declare-fun a0 () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(assert (= b ((as const (Array Int Int)) 1)))
(assert (= (store (store b 2 (select (store a0 5 2) (+ i 1))) i (select a0 (+ i 1))) (store (store b (+ i 2) i) i 1)))
(check-sat)
"#;

/// D4-d, `const_11_0110.min.smt2`: the default-const lemma learned the unit
/// `(= 1 (default (store (store K0 i0 v0) 2 0)))`.
const D4D_0110: &str = r#"
(set-logic QF_ALIA)
(declare-fun a0 () (Array Int Int))
(declare-fun a1 () (Array Int Int))
(declare-fun a2 () (Array Int Int))
(declare-fun i0 () Int)
(declare-fun v0 () Int)
(assert (=> (= (select (store (store ((as const (Array Int Int)) 1) 2 0) 1 (select (store a1 i0 i0) i0)) i0) v0) (not (< (select (store ((as const (Array Int Int)) v0) i0 i0) i0) v0))))
(assert (or (= (store (store ((as const (Array Int Int)) v0) 2 i0) i0 (select a1 (+ i0 1))) a0) (not (= i0 1))))
(assert (or (not (= ((as const (Array Int Int)) 1) (store ((as const (Array Int Int)) 0) i0 v0))) (> (select a2 (+ i0 1)) v0)))
(check-sat)
"#;

/// A1 (`a1_panic/a1_min.smt2`): a 2-constructor enum stored in a
/// `(_ BitVec 2)`-indexed array reached the enum-sort model repair, which
/// indexed the term store with the sentinel `TermId(u32::MAX - 7)`.
const A1_ENUM_BV_ARRAY: &str = r#"
(set-logic ALL)
(declare-datatypes ((E2 0)) (((e0) (e1))))
(declare-fun a0 () (Array (_ BitVec 2) E2))
(declare-fun a1 () (Array (_ BitVec 2) E2))
(declare-fun a2 () (Array (_ BitVec 2) E2))
(declare-fun x0 () (_ BitVec 2))
(assert (= (store (store (store (store a2 #b11 e0) #b01 e0) #b10 e1) #b00 e1) a2))
(assert (not (= (store (store (store (store a0 #b01 e0) #b10 e1) #b00 e0) #b11 e1) (store (store a1 #b10 e0) #b01 e1))))
(check-sat)
"#;

#[test]
#[timeout(120_000)]
fn d4a_store_chain_read_skip_carries_its_distinctness_reasons() {
    assert_sat_both_postures("w2_min", D4A_W2);
}

#[test]
#[timeout(120_000)]
fn d4b_partial_walker_keeps_skipped_stores_as_shadows() {
    // `unknown` today: with the wrong `1 = 2` propagation gone, deciding
    // `i` vs `j` across two DIFFERENT bases is a pre-existing completeness gap
    // (the select-free index split covers same-base chains only).
    assert_never_unsat("free_bases", D4B_FREE_BASES);
    assert_never_unsat("storeeq_41_0293.min", D4B_0293);
}

#[test]
#[timeout(120_000)]
fn d12_bool_index_finite_store_chain_is_d4b() {
    assert_sat_both_postures("w3_finstore_min", D12_BOOL_FINSTORE);
}

#[test]
#[timeout(120_000)]
fn d4c_store_permutation_reads_complete_maps() {
    assert_never_unsat("storeeq_41_0883.min", D4C_0883);
}

#[test]
#[timeout(120_000)]
fn d4d_default_const_lemma_keeps_its_antecedent() {
    assert_never_unsat("const_11_0110.min", D4D_0110);
}

/// The unsatisfiable twins of the D4-a and D4-d repairs: keeping the premises
/// must not switch the refutations they justify off. D4-a with `i != 0`: the
/// left chain reads 2 at `i + 1 != 1` where the right one reads the default 1.
/// D4-d: `a = b = (const 1)` through a path still forces `(select a 0) = 1`.
#[test]
#[timeout(120_000)]
fn d4_premise_repairs_keep_their_unsat_twins() {
    const D4A_TWIN_UNSAT: &str = r#"
(set-logic QF_ALIA)
(declare-fun a0 () (Array Int Int))
(declare-fun i () Int)
(assert (not (= i 0)))
(assert (= (store ((as const (Array Int Int)) 1) (+ i 1) 2) (store ((as const (Array Int Int)) 1) 1 (select (store a0 5 2) i))))
(check-sat)
"#;
    const D4D_PATH_UNSAT: &str = r#"
(set-logic QF_ALIA)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(assert (= a b))
(assert (= b ((as const (Array Int Int)) 1)))
(assert (not (= (select a 0) 1)))
(check-sat)
"#;
    const D4D_PATH_SAT: &str = r#"
(set-logic QF_ALIA)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(assert (not (= a b)))
(assert (= b ((as const (Array Int Int)) 1)))
(assert (= (select a 0) 0))
(check-sat)
"#;
    for competition in [false, true] {
        for (name, src, expected) in [
            ("d4a_twin_unsat", D4A_TWIN_UNSAT, "unsat"),
            ("d4d_path_unsat", D4D_PATH_UNSAT, "unsat"),
            ("d4d_path_sat", D4D_PATH_SAT, "sat"),
        ] {
            let outputs = solve(src, competition);
            assert_eq!(
                outputs.first().map(String::as_str),
                Some(expected),
                "{name} (competition={competition}): {outputs:?}"
            );
        }
    }
}

#[test]
#[timeout(120_000)]
fn a1_enum_repair_never_reads_a_sentinel_term() {
    // `assert_never_unsat` also fails on a panic (it propagates).
    assert_never_unsat("a1_min", A1_ENUM_BV_ARRAY);
}

/// M2 (`m2_ufarr_default/min.smt2`). A `sat` must come with a model in which
/// the congruent applications `(g (+ i2 1))` and `(g 2)` agree whenever
/// `i2 + 1 = 2`: main printed `g = (const 0)` with `i2 = 1`, `i1 = 1`,
/// `a1 = (store K0 1 0)`, so assertion 2 reads `0 > 0`, while its gate said
/// `confirmed-sat` from the per-application pin of `(g (+ i2 1))`. The check
/// reads the model back through `get-value` of the SAME application `(g 2)`
/// the printer publishes.
#[test]
#[timeout(120_000)]
fn m2_array_valued_uf_model_is_checked_as_printed() {
    const M2: &str = r#"
(set-logic QF_AUFLIA)
(declare-fun g (Int) (Array Int Int))
(declare-fun f ((Array Int Int)) Int)
(declare-fun a1 () (Array Int Int))
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(assert (<= 0 i2))
(assert (> (select (g (+ i2 1)) i1) (select a1 i1)))
(assert (not (= (f (g 2)) i1)))
(check-sat)
(get-value (i2 (select (g 2) i1) (select a1 i1)))
"#;
    for competition in [false, true] {
        let outputs = solve(M2, competition);
        let verdict = outputs.first().cloned().unwrap_or_default();
        assert!(
            verdict == "sat" || verdict == "unknown",
            "competition={competition}: {outputs:?}"
        );
        if verdict != "sat" {
            continue;
        }
        let values = outputs.get(1).cloned().unwrap_or_default();
        let numbers: Vec<i64> = values
            .split(|ch: char| !(ch.is_ascii_digit() || ch == '-'))
            .filter_map(|tok| tok.parse::<i64>().ok())
            .collect();
        // `(get-value (i2 (select (g 2) i1) (select a1 i1)))` prints
        // `((i2 N) ((select (g 2) i1) N) ((select a1 i1) N))`; the literal `2`
        // inside `(g 2)` is the second number.
        assert!(numbers.len() >= 4, "unparsed get-value: {values}");
        let (i2, g2_read, a1_read) = (numbers[0], numbers[2], numbers[3]);
        if i2 + 1 == 2 {
            assert!(
                g2_read > a1_read,
                "competition={competition}: with i2 = 1, (g (+ i2 1)) is (g 2), so \
                 assertion 2 needs (select (g 2) i1) > (select a1 i1); model gives \
                 {g2_read} vs {a1_read} ({values})"
            );
        }
    }
}

/// M2 as a wrong SAT (the 2026-09-24 verifier's variant `m2u_27`). `i2 = 1`
/// makes `(g (+ i2 1))` the application `(g 2)`, which is asserted to be
/// `(const 1)`, so assertion 2 reads `1 > (select a1 i1) = 3`: UNSAT by
/// congruence (z3 5.1.0 `unsat`). Before the M2 gate fix main answered `sat`
/// in both postures and its gate said `confirmed-sat`: it checked
/// `(g (+ i2 1))` against a per-application pin while the printed `g` answered
/// `(g 2)` differently. Unlike the pin above, the input FORCES the congruent
/// pair (`i2` is fixed), so a search cannot step around the defect.
#[test]
#[timeout(120_000)]
fn m2_congruent_array_valued_uf_applications_never_confirm_sat() {
    const M2U_27: &str = r#"
(set-logic QF_AUFLIA)
(declare-fun g (Int) (Array Int Int))
(declare-fun f ((Array Int Int)) Int)
(declare-fun a1 () (Array Int Int))
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(declare-fun k () Int)
(assert (and (<= 1 i2) (<= i2 1)))
(assert (> (select (g (+ i2 1)) i1) (select a1 i1)))
(assert (= (g 2) ((as const (Array Int Int)) 1)))
(assert (= (select a1 i1) 3))
(assert (not (= (f (g 2)) i1)))
(check-sat)
"#;
    for competition in [false, true] {
        let outputs = solve(M2U_27, competition);
        let verdict = outputs.first().cloned().unwrap_or_default();
        assert!(
            verdict == "unsat" || verdict == "unknown",
            "m2u_27 (competition={competition}): z3 5.1.0 answers unsat (congruence of \
             (g (+ i2 1)) and (g 2) under i2 = 1); AY must never answer sat: {outputs:?}"
        );
    }
}

// #index-diseq-justified (2026-09-28 fix-up): the index-pair path asserted
// `i != j` from a pinned `j = 5` and a FREE `i` the model had put at 0 --
// under `j`'s bound reasons alone, which `i = 5` also satisfies. These are the
// verifier's variants on which that answered `unsat` (z3 5.1.0 `sat`, model
// re-checked) on a branch tip that also reported the written indices of
// store-chain equalities to that path (reverted); they stay as guards of the
// shape. The unit test `test_index_pair_with_one_unjustified_value_is_split_
// not_asserted_distinct` (check_loops) is the direct guard of the fix: the
// index pair must be split, never asserted distinct, unless BOTH values are
// justified.

/// Verifier `variants2/d4b/d4b_029`: `sat` needs `i = j = 5`, `a0[2] = 2`.
const D4B_029: &str = r#"
(set-logic QF_ALIA)
(declare-fun a0 () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun k () Int)
(assert (= (store (store (store b j 1) i (select a0 2)) 2 j) (store (store (store ((as const (Array Int Int)) 0) 0 k) j 2) 2 5)))
(assert (>= i -3))
(check-sat)
"#;

/// Verifier `variants3/inc_03`: its last query (`i >= 0` added) is `sat`;
/// the lane had answered it `unsat` under `--z3-mode`.
const INC_03: &str = r#"
(set-logic QF_ALIA)
(set-option :produce-models true)
(declare-fun a0 () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun c () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun v () Int)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun p () Bool)
(push 1)
(assert (= (store ((as const (Array Int Int)) 1) i x) (store ((as const (Array Int Int)) 0) j y)))
(assert (> y x))
(check-sat)
(pop 1)
(assert (= (store (store (store b j 1) i v) 2 j) (store (store c j 2) 2 5)))
(check-sat)
(push 1)
(assert (=> p (= (store ((as const (Array Int Int)) 1) i x) (store ((as const (Array Int Int)) 0) j y))))
(check-sat-assuming (p))
(check-sat)
(pop 1)
(assert (>= i 0))
(check-sat)
"#;

#[test]
#[timeout(120_000)]
fn index_pair_with_a_free_side_is_never_asserted_distinct() {
    assert_never_unsat("d4b_029", D4B_029);
    for competition in [false, true] {
        let outputs = solve(INC_03, competition);
        // z3 5.1.0: unsat, sat, unsat, sat, sat.
        for q in [1, 3, 4] {
            let verdict = outputs.get(q).cloned().unwrap_or_default();
            assert!(
                verdict == "sat" || verdict == "unknown",
                "inc_03 query {q} (competition={competition}): z3 answers sat; AY \
                 answered {verdict:?} ({outputs:?})"
            );
        }
    }
}
