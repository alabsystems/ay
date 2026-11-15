// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Soundness regression: an UNSAT of the DPLL(T) loop that rests on a
//! model-based `violated_constraint` block is never confirmed.
//!
//! The block negates a whole Boolean assignment because one theory MODEL
//! disagreed with it; it is not a lemma. The #5384 replay must re-check the
//! UNSAT without it, but the SAT clause trace marks every clause the loop
//! adds as original, so replaying the trace originals put the block back and
//! confirmed the UNSAT. On the transition check below that turned a
//! satisfiable query (F = 0, K = 45, H = L = 10, I = M = 0) into UNSAT, model
//! validation passed a non-inductive invariant, and `ay --chc` published SAFE
//! on the UNSAFE `llreve-bench/smt2/faulty__barthe!_000`.

use ay_chc::{engines, ChcParser, InvariantModel, PdrConfig, SmtContext, SmtResult};

/// `faulty__barthe!_000`, top-level variant (UNSAFE: z3 spacer answers unsat).
const FAULTY_BARTHE: &str = "(set-logic HORN)
(declare-fun INV (Int Int Int Int Int Int Int Int) Bool)
(assert (forall ((A Int) (B Int) (C Int) (D Int) (v4 Int) (v5 Int) (v6 Int) (v7 Int))
  (=> (and (= A C) (= B D) (= 0 v4) (= 0 v5) (= 0 v6) (= 0 v7)) (INV B v4 A v5 v6 D C v7))))
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int)
                 (J Int) (K Int) (L Int) (M Int))
  (=> (and (INV F G H I J K L M) (= B (ite (= J 10) 10 (+ 5 K))) (= C (+ 1 J))
           (= D (+ I (* 5 G) F)) (= E (+ 1 G)) (not (<= H G)) (not (<= L J)) (= A (+ M K)))
      (INV F E H D C B L A))))
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int))
  (=> (and (INV C D E F G H I J) (= B (+ 1 D)) (not (<= E D)) (<= I G) (= A (+ F (* 5 D) C)))
      (INV C B E A G H I J))))
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int)
                 (K Int))
  (=> (and (INV D E F G H I J K) (= B (ite (= H 10) 10 (+ 5 I))) (= C (+ 1 H)) (<= F E)
           (not (<= J H)) (= A (+ K I)))
      (INV D E F G C B J A))))
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int))
  (=> (and (INV A B C D E F G H) (<= C B) (<= G E) (not (= D H))) false)))
(check-sat)";

/// The invariant PDR proposed for it: not inductive (a step from a4 = 9 with
/// a0 = 0 reaches a4 = 10, where the last conjunct demands a0 = -45).
const NON_INDUCTIVE: &str = "(define-fun INV ((a0 Int) (a1 Int) (a2 Int) (a3 Int) (a4 Int)
    (a5 Int) (a6 Int) (a7 Int)) Bool
  (and (>= (+ a1 a4) 0) (= (+ a1 (- a4)) 0) (= (+ (+ a0 (* 5 a1)) (- a5)) 0)
       (= (+ a2 (- a6)) 0) (= (+ a3 (- a7)) 0)
       (not (and (= a4 10) (not (= (+ a3 (* 5 a1) a0 (* 5 (+ a1 1)) a0) (+ a7 a5 10)))))))";

/// Its inductive core, which proves the correct program (`B = 5 + K` on
/// every step) safe.
const INDUCTIVE_FOR_CORRECT: &str = "(define-fun INV ((a0 Int) (a1 Int) (a2 Int) (a3 Int)
    (a4 Int) (a5 Int) (a6 Int) (a7 Int)) Bool
  (and (>= (+ a1 a4) 0) (= (+ a1 (- a4)) 0) (= (+ (+ a0 (* 5 a1)) (- a5)) 0)
       (= (+ a2 (- a6)) 0) (= (+ a3 (- a7)) 0)))";

/// One clause body `phi` (as `phi => false`) whose constraint is the query.
fn constraint_of(variables: &str, phi: &str) -> ay_chc::ChcExpr {
    let text = format!("(set-logic HORN)\n(assert (forall ({variables}) (=> {phi} false)))");
    let problem = ChcParser::parse(&text).expect("query parses");
    let constraint = problem.clauses()[0].body.constraint.clone();
    constraint.expect("query clause has a constraint")
}

const VARIABLES: &str = "(H Int) (L Int) (F Int) (K Int) (I Int) (M Int)";

/// The head-conjunct check of the faulty transition (after the validator's
/// equality propagation), reduced: satisfiable, e.g. F = 0, K = 45, L = 10.
const SATISFIABLE: &str = "(and (> L 9) (= (+ F (- K) 45) 0) (= (+ H (- L)) 0) \
    (= (+ I (- M)) 0) (distinct (+ I F F F 150) (+ M K K 15)))";

fn is_unsat(result: &SmtResult) -> bool {
    matches!(
        result,
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
    )
}

#[test]
fn check_resting_on_a_model_block_is_never_unsat() {
    let query = constraint_of(VARIABLES, SATISFIABLE);
    let result = SmtContext::new().check_sat(&query);
    assert!(
        !is_unsat(&result),
        "satisfiable (F = 0, K = 45, H = L = 10, I = M = 0) but got {result:?}"
    );
}

/// Twin: adding `F + K = -45` forces F = -45, which makes the two sides of
/// the disequality equal, so the query is UNSAT. It must stay decided.
#[test]
fn genuinely_unsat_twin_is_still_unsat() {
    let twin = SATISFIABLE.replacen("(and ", "(and (= (+ F K) (- 45)) ", 1);
    let query = constraint_of(VARIABLES, &twin);
    let result = SmtContext::new().check_sat(&query);
    assert!(is_unsat(&result), "UNSAT twin got {result:?}");
}

#[test]
fn validation_rejects_the_non_inductive_faulty_barthe_invariant() {
    let problem = ChcParser::parse(FAULTY_BARTHE).expect("benchmark parses");
    let model = InvariantModel::parse_smtlib(NON_INDUCTIVE, &problem).expect("model parses");
    let mut verifier = engines::new_pdr_solver(problem, PdrConfig::default());
    assert!(
        !verifier.verify_model(&model),
        "a non-inductive invariant of an UNSAFE problem passed model validation"
    );
}

/// Twin: the inductive core validates on the correct program.
#[test]
fn validation_accepts_the_inductive_invariant_of_the_correct_program() {
    let correct = FAULTY_BARTHE
        .replace("(ite (= J 10) 10 (+ 5 K))", "(+ 5 K)")
        .replace("(ite (= H 10) 10 (+ 5 I))", "(+ 5 I)");
    let problem = ChcParser::parse(&correct).expect("benchmark parses");
    let model =
        InvariantModel::parse_smtlib(INDUCTIVE_FOR_CORRECT, &problem).expect("model parses");
    let mut verifier = engines::new_pdr_solver(problem, PdrConfig::default());
    assert!(verifier.verify_model(&model));
}
