// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The linear-relaxation-first check of the NRA check loop
//! (#nra-relaxation-first).

use crate::Executor;
use ay_frontend::parse;

/// KeYmaera braking dynamics with each side distributed: over the monomials
/// `v², d², bm, bz, b²t², btv` the two nonlinear atoms are opposite sides of
/// one linear inequality, so the linear relaxation is infeasible on its own.
const DISTRIBUTED: &str = r#"
(set-logic QF_NRA)
(declare-fun b () Real)
(declare-fun t () Real)
(declare-fun v () Real)
(declare-fun d () Real)
(declare-fun m () Real)
(declare-fun z () Real)
(assert (> b 0))
(assert (<= (- (* v v) (* d d)) (- (* 2 b m) (* 2 b z))))
(assert (> (+ (* b b t t) (* -2 b t v) (* v v) (* -1 d d))
           (+ (* 2 b m) (* b b t t) (* -2 b t v) (* -2 b z))))
(check-sat)
"#;

fn solve_within(smt: &str, competition: bool, seconds: u64) -> String {
    let commands = parse(smt).expect("fixture parses");
    let mut exec = Executor::new();
    exec.set_timeout(Some(std::time::Duration::from_secs(seconds)));
    if competition {
        exec.set_competition_mode(true);
    } else {
        exec.set_produce_proofs(true);
    }
    let outputs = exec.execute_all(&commands).expect("fixture solves");
    outputs.last().cloned().unwrap_or_default()
}

/// The relaxation-first check is a proof-compatible reordering: its conflict
/// is the iteration-0 Farkas conflict of the refinement loop, so the
/// proof-producing posture refutes the pair too. Before it, the conflict was
/// reached only after the interval branch-and-prune phase had exhausted its
/// grid on these six unknowns (measured 3.8-4.1 s, release), so a 2 s budget
/// separates the two orders by more than an order of magnitude on either side
/// (the relaxation answers in milliseconds).
#[test]
fn linear_relaxation_conflict_refutes_before_the_exact_pre_phases() {
    assert_eq!(solve_within(DISTRIBUTED, true, 2), "unsat");
    assert_eq!(solve_within(DISTRIBUTED, false, 2), "unsat");
}

/// A satisfiable nonlinear system whose linear relaxation is feasible is
/// untouched by the relaxation-first check.
#[test]
fn feasible_relaxation_falls_through_to_the_nonlinear_phases() {
    let smt = r#"
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= (* x y) 2))
(assert (> x 1))
(assert (< (* (+ x 1) (+ y 1)) 10))
(check-sat)
"#;
    for competition in [true, false] {
        assert_eq!(
            solve_within(smt, competition, 10),
            "sat",
            "competition={competition}"
        );
    }
}
