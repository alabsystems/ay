// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Soundness regression tests for two related quantifier bugs:
//!
//! 1. Quantifier-ALTERNATION wrong-UNSAT (#quant-alternation). An exists-outer /
//!    forall-inner prefix (and quantified-antecedent / negated-forall positions)
//!    was over-instantiated to UNSAT. `(exists x. forall y. (= x 0))` is SAT
//!    (x=0 witnesses it, the inner forall body is y-independent), yet AY returned
//!    UNSAT: finite-domain expanding the outer `exists` produces a DISJUNCTION of
//!    inner `forall`s — `(or (forall y. (= 0 0)) (forall y. (= 1 0)) ...)` — and
//!    the downstream pipeline treated those disjuncts as conjunctive obligations,
//!    refuting a false disjunct to a spurious UNSAT. Fixed by (a) recursively
//!    expanding nested finite-domain quantifiers so the prefix fully decides, and
//!    (b) restricting MBQI refutation / re-validating ground UNSAT to
//!    conjunctive-position foralls so non-finite-domain cases fail closed to
//!    Unknown rather than wrong-UNSAT.
//!
//! 2. CEGQI Int var=var wrong-SAT (#cegqi-ce-var-selection). `(forall (a b Int)
//!    (= a b))` is UNSAT (a=0,b=1), but the CEGQI selection algorithm picked the
//!    OTHER counterexample variable as the instantiation term, producing the
//!    degenerate instance `(= e_b e_a)` that trivially contradicts the CE lemma;
//!    `disambiguate_cegqi_unsat` then read that spurious UNSAT as "forall valid
//!    -> SAT". Fixed by rejecting CE-variable selection terms in favor of the
//!    concrete model-value witness, which drives a sound UNSAT.

use ntest::timeout;

/// A SAT verdict for any of these is unsound (the formula is truly UNSAT).
/// UNSAT (decided) or Unknown (failed closed) are both acceptable.
fn assert_not_sat(smt: &str, label: &str) {
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "sat"),
        "{label}: must not return sat (truly UNSAT), got {results:?}"
    );
}

/// An UNSAT verdict for any of these is unsound (the formula is truly SAT).
/// SAT (decided) or Unknown (failed closed) are both acceptable.
fn assert_not_unsat(smt: &str, label: &str) {
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "{label}: must not return unsat (truly SAT), got {results:?}"
    );
}

// ---------------------------------------------------------------------------
// BUG #2 — exists-outer / forall-inner alternation must not be wrong-UNSAT.
// ---------------------------------------------------------------------------

/// `(exists x. forall y. (= x 0))` over BV2: SAT (x=#b00). The inner forall body
/// is y-independent. Was wrong-UNSAT. Now fully decided SAT (recursive
/// finite-domain expansion).
#[test]
#[timeout(20000)]
fn test_exists_forall_y_independent_literal_decides_sat() {
    let smt = r#"
        (set-logic ALL)
        (assert (exists ((x (_ BitVec 2))) (forall ((y (_ BitVec 2))) (= x #b00))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "exists-outer/forall-inner y-independent body should decide sat"
    );
}

/// `(exists x. forall y. (= x c))` over BV2 with a free constant `c`: SAT (x=c).
/// Was wrong-UNSAT (the enumerated inner-forall instances `(= 0 c)..(= 3 c)`
/// were conjoined into a contradiction).
#[test]
#[timeout(20000)]
fn test_exists_forall_equals_free_const_not_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun c () (_ BitVec 2))
        (assert (exists ((x (_ BitVec 2))) (forall ((y (_ BitVec 2))) (= x c))))
        (check-sat)
    "#;
    assert_not_unsat(smt, "exists-outer/forall-inner = free const");
}

/// Quantified antecedent: `(=> (forall q0. exists q1. q1=q0) (bvult ...))`.
/// The antecedent is valid, so the implication reduces to its satisfiable
/// consequent — SAT. Wide (BV8) binders are not finite-domain expandable, so
/// this must at worst fail closed to Unknown, never wrong-UNSAT.
#[test]
#[timeout(20000)]
fn test_quantified_antecedent_not_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun a0 () (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun c () (_ BitVec 8))
        (assert (=> (forall ((q0 (_ BitVec 8)))
                        (exists ((q1 (_ BitVec 8))) (= q1 q0)))
                    (bvult (select a0 (select a0 c)) #x9c)))
        (check-sat)
    "#;
    assert_not_unsat(smt, "quantified antecedent implication");
}

/// `(forall x. forall y. (=> (= x 0) (= x 0)))` — nested universal, binder-
/// independent tautological inner. Truly SAT (the body is a tautology).
#[test]
#[timeout(20000)]
fn test_nested_universal_tautology_not_unsat() {
    let smt = r#"
        (set-logic ALL)
        (assert (forall ((x (_ BitVec 2)))
                    (forall ((y (_ BitVec 2))) (=> (= x #b00) (= x #b00)))))
        (check-sat)
    "#;
    assert_not_unsat(smt, "nested universal tautology");
}

/// NON-REGRESSION: a genuine TOP-LEVEL-CONJUNCT `forall` that is universally
/// false must still decide UNSAT (the conjunctive-position guard must NOT block
/// legitimate refutation). `(forall x:BV2. x = 0)` is UNSAT (x=1).
#[test]
#[timeout(20000)]
fn test_conjunct_forall_false_still_decides_unsat() {
    let smt = r#"
        (set-logic ALL)
        (assert (forall ((x (_ BitVec 2))) (= x #b00)))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["unsat"],
        "top-level-conjunct false forall should decide unsat"
    );
}

/// NON-REGRESSION: plain multi-var exists stays SAT.
#[test]
#[timeout(20000)]
fn test_plain_multi_exists_still_sat() {
    let smt = r#"
        (set-logic ALL)
        (assert (exists ((x (_ BitVec 2)) (y (_ BitVec 2))) (= x y)))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(results, vec!["sat"], "plain multi-var exists should be sat");
}

/// NON-REGRESSION: forall-over-exists `(forall x:Int. exists y:Int. y > x)`
/// stays SAT (CEGQI). Must not regress to Unknown/UNSAT.
#[test]
#[timeout(20000)]
fn test_forall_over_exists_int_still_sat() {
    let smt = r#"
        (set-logic ALL)
        (assert (forall ((x Int)) (exists ((y Int)) (> y x))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(results, vec!["sat"], "forall-over-exists Int should be sat");
}

/// A universal below a satisfied disjunction is not an asserted obligation.
/// CEGQI used to conjoin one of its instances anyway, deriving `p` against the
/// asserted `not p` and reporting a wrong UNSAT despite the `c` disjunct.
#[test]
#[timeout(20000)]
fn test_nonconjunctive_forall_refinement_never_manufactures_unsat() {
    let smt = r#"
        (set-logic NIA)
        (declare-const c Bool)
        (declare-const p Bool)
        (assert c)
        (assert (not p))
        (assert (or c (forall ((x Int)) (or (not (= (* x x) 4)) p))))
        (check-sat)
    "#;
    assert_not_unsat(smt, "nonconjunctive CEGQI instance under true disjunct");
}

/// Both universal operands are valid and logically equivalent, so their XOR
/// is false. A local CEGQI validity result for either operand must not certify
/// the whole non-conjunctive formula SAT.
#[test]
#[timeout(20000)]
fn test_nonconjunctive_forall_validity_never_certifies_xor_sat() {
    let smt = r#"
        (set-logic NIA)
        (assert
          (xor (forall ((x Int)) (>= (* x x) 0))
               (forall ((y Int)) (not (< (* y y) 0)))))
        (check-sat)
    "#;
    assert_not_sat(smt, "XOR of equivalent valid universals");
}

/// Disambiguation can honestly return Unknown for nested alternating
/// universals. The follow-up MBQI refuter must not conjoin their instances as
/// though they were top-level assertions: the asserted `c` already satisfies
/// the outer disjunction, so the complete formula is SAT independently of the
/// quantified branch.
#[test]
#[timeout(20000)]
fn test_nonconjunctive_disambiguation_unknown_never_enters_mbqi_refuter() {
    let smt = r#"
        (set-logic LIA)
        (declare-const c Bool)
        (declare-const p Bool)
        (assert c)
        (assert
          (or c
              (and
                (forall ((x Int))
                  (or p (exists ((z Int)) (= x (+ z z)))))
                (forall ((y Int))
                  (or (not p) (exists ((w Int)) (= y (+ w w))))))))
        (check-sat)
    "#;
    assert_not_unsat(smt, "nonconjunctive CEGQI Unknown-to-MBQI route");
}

// ---------------------------------------------------------------------------
// CEGQI Int var=var wrong-SAT.
// ---------------------------------------------------------------------------

/// `(forall (a b Int) (= a b))` — truly UNSAT (a=0, b=1). Was wrong-SAT via the
/// CEGQI degenerate var-var selection. Now decides UNSAT.
#[test]
#[timeout(20000)]
fn test_forall_two_int_var_equality_not_sat() {
    let smt = r#"
        (declare-fun p () Bool)
        (assert (forall ((a Int) (b Int)) (= a b)))
        (check-sat)
    "#;
    assert_not_sat(smt, "forall two Int var equality");
}

/// `(forall (a b Real) (= a b))` — truly UNSAT (a=0, b=1). Same CEGQI path.
#[test]
#[timeout(20000)]
fn test_forall_two_real_var_equality_not_sat() {
    let smt = r#"
        (set-logic ALL)
        (assert (forall ((a Real) (b Real)) (= a b)))
        (check-sat)
    "#;
    assert_not_sat(smt, "forall two Real var equality");
}

/// NON-REGRESSION: a genuinely valid Int forall stays SAT — `(forall x:Int.
/// x = x)` is valid. The CEGQI fix only rejects CE-variable selection terms.
#[test]
#[timeout(20000)]
fn test_forall_int_reflexive_equality_still_sat() {
    let smt = r#"
        (set-logic ALL)
        (assert (forall ((x Int)) (= x x)))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "forall Int reflexive equality should be sat"
    );
}

/// NON-REGRESSION: E-matching unsat path is unaffected.
/// `(forall x. f(x) >= 0) ∧ f(3) < 0` is UNSAT.
#[test]
#[timeout(20000)]
fn test_ematching_unsat_unaffected() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (>= (f x) 0)))
        (assert (< (f 3) 0))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["unsat"],
        "E-matching forall should decide unsat"
    );
}

// ---------------------------------------------------------------------------
// CEGQI forall-over-OR with a BARE-BOOL residual: wrong-SAT
// (#forall-bare-bool). A `(forall x:Int. (or (cmp x k) p))` with a bare Bool
// disjunct `p`, conjoined with `(not p)` (or `(not p)` residual + asserted `p`),
// is UNSAT: `(not p)` forces `p=false`, leaving `(forall x. (cmp x k))` which is
// false for these comparisons; AY returned a self-contradictory SAT (`p=true`
// while `(not p)` is asserted).
//
// ROOT CAUSE: `create_ce_lemma` negates the forall body via De Morgan, so the
// bare-Bool residual `p` produced a `(not p)` CE conjunct that is the
// hash-consed-IDENTICAL TermId to the genuine asserted `(not p)`.
// `flatten_and_strip_quantifiers` then captured that aliased TermId into
// `cegqi_ce_lemma_ids`, and `disambiguate_cegqi_unsat` DROPPED the genuine
// `(not p)` when stripping CE lemmas — re-solving `(or p (cmp x k))` alone as
// trivially SAT (p=true). FIX: exclude pre-existing genuine assertions from
// `cegqi_ce_lemma_ids` so the constraint survives the ground re-solve
// (preprocess.rs `setup_cegqi_for_unhandled` / `flatten_and_strip_quantifiers`).
//
// ONLY the bare-Bool residual aliases a ground assertion: a UF-predicate
// residual `(f x)` mentions the fresh CE variable (`(not (f __ce))` can never
// alias a ground assertion) and an arithmetic residual is unlikely to coincide
// — both were already correct and must stay so.

/// The exact reported reproducer: truly UNSAT, was wrong-SAT.
#[test]
#[timeout(20000)]
fn test_forall_or_bare_bool_target_not_sat() {
    let smt = r#"
        (set-logic LIA)
        (declare-const p Bool)
        (assert (forall ((X0 Int)) (or (> X0 4) p)))
        (assert (not p))
        (check-sat)
    "#;
    assert_not_sat(smt, "forall-or bare-bool target");
}

/// The full family: {<,<=,>,>=} x both arg orientations x consts {-1,0,4,5},
/// bare-bool residual `p` with asserted `(not p)`. Every member is UNSAT
/// (`(not p)` forces p=false, and `(forall x. (cmp x k))` is false for each).
/// All 32 were wrong-SAT; now none may be SAT.
#[test]
#[timeout(60000)]
fn test_forall_or_bare_bool_family_notp_not_sat() {
    for op in ["<", "<=", ">", ">="] {
        for k in ["-1", "0", "4", "5"] {
            // orientation A: (op X0 k)
            let smt_a = format!(
                "(set-logic LIA)(declare-const p Bool)\
                 (assert (forall ((X0 Int)) (or ({op} X0 {k}) p)))\
                 (assert (not p))(check-sat)"
            );
            assert_not_sat(&smt_a, &format!("famA op={op} k={k}"));
            // orientation B: (op k X0)
            let smt_b = format!(
                "(set-logic LIA)(declare-const p Bool)\
                 (assert (forall ((X0 Int)) (or ({op} {k} X0) p)))\
                 (assert (not p))(check-sat)"
            );
            assert_not_sat(&smt_b, &format!("famB op={op} k={k}"));
        }
    }
}

/// Opposite polarity: residual `(not p)` inside the forall + asserted `p`.
/// The CE-lemma conjunct then folds to `p`, aliasing the asserted `p`. Same
/// family; every member is UNSAT and must not be SAT.
#[test]
#[timeout(60000)]
fn test_forall_or_bare_bool_family_notp_residual_not_sat() {
    for op in ["<", "<=", ">", ">="] {
        for k in ["-1", "0", "4", "5"] {
            let smt = format!(
                "(set-logic LIA)(declare-const p Bool)\
                 (assert (forall ((X0 Int)) (or ({op} X0 {k}) (not p))))\
                 (assert p)(check-sat)"
            );
            assert_not_sat(&smt, &format!("famC op={op} k={k}"));
        }
    }
}

/// CONTROL (must stay SAT): the SAME forall WITHOUT `(not p)`. `p=true`
/// satisfies the universal vacuously; the fix must not regress this to UNSAT.
#[test]
#[timeout(20000)]
fn test_forall_or_bare_bool_without_notp_still_sat() {
    let smt = r#"
        (set-logic LIA)
        (declare-const p Bool)
        (assert (forall ((X0 Int)) (or (> X0 4) p)))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "forall-or bare-bool without (not p) should be sat (p=true)"
    );
}

/// CONTROL (must stay SAT): the forall WITH asserted `p` (consistent with the
/// only way to satisfy the universal). `p=true` everywhere.
#[test]
#[timeout(20000)]
fn test_forall_or_bare_bool_with_assert_p_still_sat() {
    let smt = r#"
        (set-logic LIA)
        (declare-const p Bool)
        (assert (forall ((X0 Int)) (or (> X0 4) p)))
        (assert p)
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "forall-or bare-bool with (assert p) should be sat"
    );
}

/// CONTROL (already-correct, must stay UNSAT): UF-predicate residual. The CE
/// conjunct `(not (f __ce))` mentions the fresh CE variable and cannot alias the
/// ground `(not (f 0))`, so this path was never affected. `(forall x. (or (> x
/// 4) (f x)))` is false at x=0 when `(not (f 0))`.
#[test]
#[timeout(20000)]
fn test_forall_or_uf_residual_still_unsat() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Bool)
        (assert (forall ((X0 Int)) (or (> X0 4) (f X0))))
        (assert (not (f 0)))
        (check-sat)
    "#;
    assert_not_sat(smt, "forall-or UF residual");
}

/// CONTROL (already-correct, must stay UNSAT): arithmetic residual. The
/// constant-false `(> k 100)` (with k=3) does not coincide with any top-level
/// assertion, so `disambiguate_cegqi_unsat` never dropped a real constraint.
/// `(forall x. (or (> x 4) (> 3 100)))` reduces to `(forall x. (> x 4))`, false
/// at x=0.
#[test]
#[timeout(20000)]
fn test_forall_or_arith_residual_still_unsat() {
    let smt = r#"
        (set-logic LIA)
        (declare-const k Int)
        (assert (= k 3))
        (assert (forall ((X0 Int)) (or (> X0 4) (> k 100))))
        (check-sat)
    "#;
    assert_not_sat(smt, "forall-or arithmetic residual");
}

/// SOUNDNESS (multi-lemma CE-refutation disjunction hole, 2026-07-10): two
/// universals coupled through a shared free Bool. `(forall x. x>=0 or q)` forces
/// `q` (x=-1) and `(forall y. y<0 or (not q))` forces `(not q)` (y=0), so the
/// conjunction is UNSAT (z3-confirmed). The joint CE-lemma refutation solved
/// `(sk1<0 and (not q)) and (sk2>=0 and q)` — trivially UNSAT via `q/(not q)` —
/// and wrongly flipped to SAT: a joint UNSAT only proves the DISJUNCTION of the
/// universals' validities. The per-lemma refutation fix keeps this not-sat.
#[test]
#[timeout(20000)]
fn test_two_coupled_foralls_contradictory_never_sat() {
    let smt = r#"
        (set-logic LIA)
        (declare-const q Bool)
        (assert (forall ((x Int)) (or (>= x 0) q)))
        (assert (forall ((y Int)) (or (< y 0) (not q))))
        (check-sat)
    "#;
    assert_not_sat(smt, "two coupled contradictory foralls");
}

/// SOUNDNESS pin for the UF-GRAPH pin leg (#cegqi-mdef v2, 2026-07-11): two
/// universals coupled through a shared UF are jointly UNSAT — no single
/// re-completion M′ of any candidate model can satisfy both, so per-group
/// refutation may certify at most one group and the flip must never fire.
#[test]
#[timeout(20000)]
fn test_two_coupled_uf_foralls_contradictory_never_sat() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (>= (f x) 0)))
        (assert (forall ((y Int)) (< (f y) 0)))
        (check-sat)
    "#;
    assert_not_sat(smt, "two coupled contradictory UF foralls");
}
