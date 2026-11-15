// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Verdicts the D4-a repair (a store-chain read skip carries its
//! index-distinctness reasons) would otherwise have lost, from the 2026-09-23
//! hunt's `storeeq41` generator (seed 41). Main `f399eca07a` decided each one,
//! z3 5.1.0 agrees, and each became `unknown` once the unconditional store-chain
//! value conflict became conditional, because the old clause had been standing
//! in for facts nothing else derived:
//!
//! * `0240` (unsat): store chains over const-arrays with distinct defaults are
//!   never equal over an infinite index sort (no premise about the indices);
//! * `0261` (sat): a read-only base array takes its else value from a store
//!   parent whose default is known (model extraction);
//! * `0007` (sat): the refuted-model re-solve decides it (the 2026-09-23
//!   branch reached it by excluding the dead terms over eliminated variables
//!   from the array axioms, "C3"; C3 cost more verdicts than it won and was
//!   reverted on 2026-09-25, see the fix-up report; `0003` is lost without it).

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn verdict(src: &str, competition: bool) -> String {
    let commands = parse(src).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    exec.set_competition_mode(competition);
    exec.set_timeout(Some(Duration::from_secs(20)));
    exec.set_memory_limit(Some(8 << 30));
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"));
    outputs.first().cloned().unwrap_or_default()
}

fn assert_both_postures(name: &str, src: &str, expected: &str) {
    for competition in [false, true] {
        assert_eq!(
            verdict(src, competition),
            expected,
            "{name} (competition={competition})"
        );
    }
}

/// `storeeq_41_0240.smt2`: `const 1` and `const 0` chains asserted equal.
const STOREEQ_0240: &str = r#"
(set-logic QF_ALIA)
(declare-fun a0 () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun k () Int)
(declare-fun x () Int)
(assert (= (store (store (store ((as const (Array Int Int)) 1) 2 i) 2 i) i 5) (store (store (store ((as const (Array Int Int)) 0) j 0) k (select (store a0 2 2) (- i 2))) (- j 1) 5)))
(assert (>= j 1))
(check-sat)
"#;

/// `storeeq_41_0261.smt2`: `a0` must be `x` off its written cells.
const STOREEQ_0261: &str = r#"
(set-logic QF_ALIA)
(declare-fun a0 () (Array Int Int))
(declare-fun a1 () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun k () Int)
(declare-fun x () Int)
(assert (= (store ((as const (Array Int Int)) x) 2 (select (store a0 0 0) (+ j 1))) (store (store a0 (- i 1) 2) (+ k 1) j)))
(check-sat)
"#;

/// `storeeq_41_0007.smt2`: `x` is eliminated as `(select a1 i)`.
const STOREEQ_0007: &str = r#"
(set-logic QF_ALIA)
(declare-fun a0 () (Array Int Int))
(declare-fun a1 () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun k () Int)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (store ((as const (Array Int Int)) y) i x) (store ((as const (Array Int Int)) y) (+ i 1) 3)))
(assert (= x (select a1 i)))
(assert (= x (select (store a1 2 1) j)))
(check-sat)
"#;

#[test]
#[timeout(120_000)]
fn store_chains_over_distinct_const_defaults_are_never_equal() {
    assert_both_postures("storeeq_41_0240", STOREEQ_0240, "unsat");
}

#[test]
#[timeout(120_000)]
fn read_only_base_takes_its_default_from_a_store_parent() {
    assert_both_postures("storeeq_41_0261", STOREEQ_0261, "sat");
}

#[test]
#[timeout(120_000)]
fn store_chain_equality_over_an_eliminated_variable_is_decided() {
    assert_both_postures("storeeq_41_0007", STOREEQ_0007, "sat");
}

// Verdicts the D4 repairs left `unknown` (2026-09-24 verifier, Table 1 and
// its lost pairs) that the refuted-model re-solve decides. Each first model is
// refuted by the independent gate (or left unvalidated); the re-solve asserts
// the congruence instances the search lacked (reads at every written index of
// an asserted store-chain equality, peeled through every store layer;
// Ackermann instances of array-valued uninterpreted applications), and model
// extraction prints one value per class that holds a store chain. z3 5.1.0
// answers each one at once.

/// Verifier variant `variants/d4b/d4b_018` (same free base `b`): the first
/// model reads 2 vs `b[i]` at the written index `i`, where no `select` existed.
const D4B_018: &str = r#"
(set-logic QF_ALIA)
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun k () Int)
(assert (= (store (store (store b j 5) i 2) 3 j) (store (store b j 1) k 5)))
(assert (not (= k 2)))
(check-sat)
"#;

/// The hunt's D4-b free-bases witness (base main answered `unsat`): two store
/// chains over DIFFERENT free bases; `sat` needs `i = j`, `v = 2` and `b`, `c`
/// equal outside the written indices.
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

/// The verifier's `variants4/m2u_27`: `(g (+ i2 1))` is `(g 2)` = `(const 1)`
/// at the forced `i2 = 1`, so assertion 2 reads `1 > 3`. z3: `unsat`.
const M2U_27: &str = r#"
(set-logic QF_AUFLIA)
(declare-fun g (Int) (Array Int Int))
(declare-fun f ((Array Int Int)) Int)
(declare-fun a1 () (Array Int Int))
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(assert (and (<= 1 i2) (<= i2 1)))
(assert (> (select (g (+ i2 1)) i1) (select a1 i1)))
(assert (= (g 2) ((as const (Array Int Int)) 1)))
(assert (= (select a1 i1) 3))
(assert (not (= (f (g 2)) i1)))
(check-sat)
"#;

#[test]
#[timeout(120_000)]
fn refuted_model_resolve_reads_every_written_index() {
    assert_both_postures("d4b_018", D4B_018, "sat");
}

#[test]
#[timeout(120_000)]
fn refuted_model_resolve_decides_store_chains_over_different_bases() {
    assert_both_postures("d4b_free_bases", D4B_FREE_BASES, "sat");
}

#[test]
#[timeout(120_000)]
fn refuted_model_resolve_merges_array_valued_uf_applications() {
    assert_both_postures("m2u_27", M2U_27, "unsat");
}

// Two verdicts C3 (`exclude_eliminated_vars_from_array_axioms`, reverted
// 2026-09-25) cost: with the terms over a variable substitution eliminated
// kept out of the array axioms, the variable's value some theory lane held was
// free, the arrays oracle refuted the ORIGINAL assertion, and these files --
// main and z3 5.1.0 answer sat at once -- came back `unknown` (fresh seed
// 2410). They fail again if the exclusion comes back.

/// `storeeqfree_2410_0093`: `x := (select (store a0 1 7) (- i 1))`.
const STOREEQFREE_2410_0093: &str = r#"
(set-logic QF_ALIA)
(declare-fun a0 () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (store (store b i x) i i) (store (store b i 0) i (select a0 0))))
(assert (= x (select (store a0 1 7) (- i 1))))
(check-sat)
"#;

/// `ufarr_2410_0000`: `i0 := 0` under an array-valued UF application.
const UFARR_2410_0000: &str = r#"
(set-logic QF_AUFLIA)
(declare-fun g (Int) (Array Int Int))
(declare-fun f ((Array Int Int)) Int)
(declare-fun g2 (Int Int) (Array Int Int))
(declare-fun a0 () (Array Int Int))
(declare-fun a1 () (Array Int Int))
(declare-fun i0 () Int)
(declare-fun i1 () Int)
(assert (<= 0 i0))
(assert (<= i0 1))
(assert (<= 0 i1))
(assert (<= i1 2))
(assert (= i0 0))
(assert (= (select (store (g i0) (select a1 i1) 1) (select a0 i0)) (select (store a0 (select a0 i0) 0) (select a1 i0))))
(check-sat)
"#;

#[test]
#[timeout(120_000)]
fn eliminated_variable_keeps_its_array_axioms() {
    assert_both_postures("storeeqfree_2410_0093", STOREEQFREE_2410_0093, "sat");
    assert_both_postures("ufarr_2410_0000", UFARR_2410_0000, "sat");
}

// Session 5 (2026-09-29) of the fix-up: two causes of the D4 repairs' lost
// `sat` answers. Main and z3 5.1.0 answer each file at once.
//
// The refuted-model re-solve runs its array axiom fixpoint on the terms its
// assertions reach (`live_array_axiom_scope_wanted`). Unscoped, it indexed
// axioms at everything the refuted first pass had left in the term store:
// fresh storeeq_2410_0508 grew from 21 to 322 assertions, storeeq_2609_0055
// from 29 to 4,132, and both ran to the deadline.

/// `storeeq_2410_0508`: a select-free store-chain equality whose first model
/// misses `a0[1]` (the chains differ at the written index 1).
const STOREEQ_2410_0508: &str = r#"
(set-logic QF_ALIA)
(declare-fun a0 () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (store (store a0 j y) 0 x) (store (store ((as const (Array Int Int)) x) 1 (select a0 (+ i 1))) i (select (store a0 0 2) (+ i 1)))))
(assert (not (= (select a0 i) y)))
(check-sat)
"#;

/// `storeeq_2809_0181`: `(or (= L R) (= j 2))`, the first model takes `L = R`
/// with arrays that falsify it.
const STOREEQ_2809_0181: &str = r#"
(set-logic QF_ALIA)
(declare-fun a0 () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun x () Int)
(assert (or (= (store (store ((as const (Array Int Int)) 1) 2 x) (- j 2) (select a0 (- j 1))) (store (store (store ((as const (Array Int Int)) 1) (+ j 1) 3) 2 x) i (select (store a0 1 1) j))) (= j 2)))
(assert (= x (select a0 0)))
(assert (not (= (select (store a0 0 1) 2) x)))
(check-sat)
"#;

#[test]
#[timeout(120_000)]
fn refuted_model_resolve_runs_on_the_live_terms() {
    assert_both_postures("storeeq_2410_0508", STOREEQ_2410_0508, "sat");
    assert_both_postures("storeeq_2809_0181", STOREEQ_2809_0181, "sat");
}

// The class reconciliation is a SECOND model candidate
// (#store-chain-class-candidate): the SAT funnel gates the per-term model
// first and the reconciled one only when that was refused. As the only model,
// the reconciled one cost these verdicts (the per-term model is valid).

/// `ufarr_2809_0143`.
const UFARR_2809_0143: &str = r#"
(set-logic QF_AUFLIA)
(declare-fun g (Int) (Array Int Int))
(declare-fun f ((Array Int Int)) Int)
(declare-fun a0 () (Array Int Int))
(declare-fun i0 () Int)
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(assert (<= 0 i0))
(assert (<= i0 2))
(assert (<= 0 i1))
(assert (<= i1 1))
(assert (<= 0 i2))
(assert (<= i2 2))
(assert (not (< (select a0 i0) (f (g i1)))))
(assert (not (< (select (g i1) i2) (select (g i2) i2))))
(assert (= (select (store a0 1 (f a0)) i2) (f (store a0 i2 i1))))
(assert (or (> (select (g 2) 0) (select a0 i0)) (= i1 2)))
(assert (or (not (> (select a0 i0) (select (g (select a0 i2)) (+ i0 1)))) (= i1 0)))
(check-sat)
"#;

/// `finstore_2809_0048`: arrays over an enumeration.
const FINSTORE_2809_0048: &str = r#"
(set-logic ALL)
(declare-datatypes ((E2 0)) (((e0) (e1))))
(declare-fun a0 () (Array E2 Int))
(declare-fun a1 () (Array E2 Int))
(declare-fun v0 () Int)
(assert (not (= (store a0 e0 2) a1)))
(assert (or (= a0 (store (store a1 e1 1) e0 (- 1))) (= (select (store (store a0 e1 0) e0 1) e0) (select (store ((as const (Array E2 Int)) 1) e0 (- 1)) e1))))
(assert (or (not (distinct a0 a1)) (= (store (store a1 e1 0) e1 0) (store (store a0 e1 (- 1)) e0 1))))
(assert (or (distinct a0 a1) (= a1 (store a1 e0 (- 1)))))
(check-sat)
"#;

#[test]
#[timeout(120_000)]
fn store_chain_class_reconciliation_is_the_second_candidate() {
    assert_both_postures("ufarr_2809_0143", UFARR_2809_0143, "sat");
    assert_both_postures("finstore_2809_0048", FINSTORE_2809_0048, "sat");
}

#[test]
#[timeout(120_000)]
fn enum_array_repair_preserves_constructor_identity_and_observed_cells() {
    let reordered = FINSTORE_2809_0048.replace("((e0) (e1))", "((e1) (e0))");
    assert_both_postures("finstore_reordered", &reordered, "sat");
    // The original formula forces a0 = a1 and select(a1, e0) = -1.
    // Replacing the extractor's e0 cell with an unrelated default must never
    // turn this contradictory extension into SAT.
    let contradictory =
        FINSTORE_2809_0048.replace("(check-sat)", "(assert (= (select a1 e0) 1))\n(check-sat)");
    assert_both_postures("finstore_observed_cell_conflict", &contradictory, "unsat");
}

// Const-array facts over whole equivalence classes (`const_array_classes.rs`).
// The fail-closed conflict verifier re-solves a conflict's literals in a fresh
// solver; it called these valid conflicts satisfiable, and the whole AUFLIA
// pass ended `unknown`.

/// The verifier's variant `variants/d4d/d4d_013`: `(store K0 i0 v0)` and
/// `(store K1 i0 v0)` meet only through the path the conflict carries.
const D4D_013: &str = r#"
(set-logic QF_ALIA)
(declare-fun a0 () (Array Int Int))
(declare-fun a1 () (Array Int Int))
(declare-fun a2 () (Array Int Int))
(declare-fun i0 () Int)
(declare-fun v0 () Int)
(declare-fun x () Int)
(assert (or (= (store (store ((as const (Array Int Int)) 1) 2 i0) i0 (select a1 (+ i0 1))) a0) (not (= i0 1))))
(assert (or (not (= ((as const (Array Int Int)) 1) (store ((as const (Array Int Int)) 0) i0 v0))) (> (select a2 (+ i0 1)) v0)))
(assert (= (select a0 x) (+ v0 1)))
(check-sat)
"#;

/// Fresh `storeeq_2809_0025`: `(select a0 j)` of the class of `b = K1`.
const STOREEQ_2809_0025: &str = r#"
(set-logic QF_ALIA)
(declare-fun a0 () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun k () Int)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= b ((as const (Array Int Int)) 1)))
(assert (or (= (store (store b k (select (store a0 0 7) j)) (- j 1) 1) (store ((as const (Array Int Int)) y) k x)) (= k 2)))
(assert (<= i 1))
(check-sat)
"#;

#[test]
#[timeout(120_000)]
fn verifier_accepts_const_array_conflicts_drawn_over_classes() {
    assert_both_postures("d4d_013", D4D_013, "sat");
    assert_both_postures("storeeq_2809_0025", STOREEQ_2809_0025, "sat");
}

#[test]
#[timeout(120_000)]
fn constant_uf_argument_aliases_share_compatible_array_cells() {
    assert_both_postures(
        "constant_argument_compatible_cells",
        r#"
(set-logic QF_AUFLIA)
(declare-fun array_at (Int) (Array Int Int))
(declare-fun index () Int)
(assert (= index 0))
(assert (= (select (array_at index) 1) 7))
(assert (= (select (array_at 0) 2) 8))
(check-sat)
"#,
        "sat",
    );
}

#[test]
#[timeout(120_000)]
fn constant_uf_argument_aliases_cannot_disagree_at_one_array_cell() {
    assert_both_postures(
        "constant_argument_conflicting_cell",
        r#"
(set-logic QF_AUFLIA)
(declare-fun array_at (Int) (Array Int Int))
(declare-fun index () Int)
(assert (= index 0))
(assert (= (select (array_at index) 1) 7))
(assert (= (select (array_at 0) 1) 8))
(check-sat)
"#,
        "unsat",
    );
}

#[test]
#[timeout(120_000)]
fn constant_uf_argument_definition_does_not_outlive_its_scope() {
    let commands = parse(
        r#"
(set-logic QF_AUFLIA)
(declare-fun array_at (Int) (Array Int Int))
(declare-fun index () Int)
(assert (<= 0 index))
(assert (<= index 1))
(push 1)
(assert (= index 0))
(assert (distinct (array_at index) (array_at 0)))
(check-sat)
(pop 1)
(assert (= index 1))
(assert (= (select (array_at index) 1) 7))
(assert (= (select (array_at 0) 1) 8))
(check-sat)
"#,
    )
    .unwrap();
    for competition in [false, true] {
        let mut exec = Executor::new();
        exec.set_competition_mode(competition);
        exec.set_timeout(Some(Duration::from_secs(20)));
        exec.set_memory_limit(Some(8 << 30));
        assert_eq!(
            exec.execute_all(&commands).unwrap(),
            vec!["unsat".to_string(), "sat".to_string()],
            "competition={competition}"
        );
    }
}
