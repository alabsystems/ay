// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::pdr::{PdrConfig, PdrSolver};
use crate::ChcParser;

/// The `dillig12_m_000` loop, verbatim: `FUN`'s fifth argument `J` is a mode
/// latch selected by an `ite`, and it splits the accumulator's closed form.
const DILLIG12_LOOP: &str = r#"
(set-logic HORN)
(declare-fun |FUN| ( Int Int Int Int Int ) Bool)
(assert (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
  (=> (and (= C 0) (= B 0) (= A 0) (= D 0)) (FUN A B C D E))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) )
  (=> (and (FUN A B C D J)
       (and (= I (ite (= J 1) (+ E F) E))
            (= H (+ C F))
            (= G (+ 1 B))
            (= F (+ 1 A))
            (= E (+ D G))))
  (FUN F G H I J))))
(check-sat)
"#;

fn solver() -> PdrSolver {
    let problem = ChcParser::parse(DILLIG12_LOOP).expect("dillig12 loop parses");
    PdrSolver::new(problem, PdrConfig::default())
}

/// The mode guard `J = 1` must be recognised: `J` is passed through unchanged
/// by the only self-loop, and `(= J 1)` is an `ite` condition in it.
#[test]
fn mode_guard_is_detected_on_the_dillig12_loop() {
    let s = solver();
    let pred = s.problem.predicates()[0].id;
    let guards = s.mode_guard_candidates(pred);
    assert!(
        !guards.is_empty(),
        "J is a latch tested by an ite condition; the guard must be found"
    );
    assert!(
        guards.iter().any(|g| g.value == 1),
        "the guard constant must be 1 (from `(= J 1)`), got {:?}",
        guards.iter().map(|g| g.value).collect::<Vec<_>>()
    );
}

/// End to end: the pass must admit `J = 1 => D - 2*C = 0`.
#[test]
fn guarded_scaled_equality_is_discovered_on_the_dillig12_loop() {
    let mut s = solver();
    s.discover_guarded_scaled_equalities();
    let pred = s.problem.predicates()[0].id;
    let want = "(or (not (= __p0_a4 1)) (= (- __p0_a3 (* 2 __p0_a2)) 0))";
    let found = s.frames.len() > 1
        && s.frames[1]
            .lemmas
            .iter()
            .any(|l| l.predicate == pred && format!("{}", l.formula) == want);
    assert!(
        found,
        "expected `J = 1 => D - 2*C = 0` in frame 1, got: {:?}",
        s.frames.get(1).map(|f| f
            .lemmas
            .iter()
            .map(|l| format!("{}", l.formula))
            .collect::<Vec<_>>())
    );
}
