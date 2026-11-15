// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The independent empty-model check, decided on the ORIGINAL clauses.
//!
//! `H3`/`H8` are the MODEL_CHECKER_CONSUMER state report's §4-A1 wrong-SAFE repros (z3:
//! `unsat`, i.e. UNSAFE). On 938ec0327 acyclic BMC proved both SAFE and the
//! empty-model validator, which re-ran BMC, agreed. Nothing here runs a CHC
//! engine, so these pins hold whether or not the BMC head-only-variable fix
//! is present.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::{check, confirmed, NotConfirmed};
use crate::{CancellationToken, ChcParser, ChcProblem};
use ay_core::time::Instant;
use std::time::Duration;

mod routes;

const BUDGET: Duration = Duration::from_secs(20);

/// UNSAFE: x = a - 1 in the fact, x = a + 3 in the rule (head-only `x`).
pub(super) const H3: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int Int) Bool)
(assert (forall ((x Int)) (=> true (P (+ x 1)))))
(assert (forall ((a Int) (x Int)) (=> (P a) (Q a (+ x 2)))))
(assert (forall ((a Int) (c Int)) (=> (and (Q a c) (= c (+ a 5))) false)))
(check-sat)
";

/// UNSAFE: the fact's `n` and the rule's head-only `n` are different values.
pub(super) const H8: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int Int) Bool)
(assert (forall ((n Int)) (=> true (P (* 2 n)))))
(assert (forall ((a Int) (n Int)) (=> (P a) (Q a (* 2 n)))))
(assert (forall ((a Int) (c Int)) (=> (and (Q a c) (not (= a c))) false)))
(check-sat)
";

/// Control: `H3` with the rule's head-only variable renamed (UNSAFE).
pub(super) const H3Y: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int Int) Bool)
(assert (forall ((x Int)) (=> true (P (+ x 1)))))
(assert (forall ((a Int) (y Int)) (=> (P a) (Q a (+ y 2)))))
(assert (forall ((a Int) (c Int)) (=> (and (Q a c) (= c (+ a 5))) false)))
(check-sat)
";

/// Control: `H8` with the rule's head-only variable renamed (UNSAFE).
pub(super) const H8M: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int Int) Bool)
(assert (forall ((n Int)) (=> true (P (* 2 n)))))
(assert (forall ((a Int) (m Int)) (=> (P a) (Q a (* 2 m)))))
(assert (forall ((a Int) (c Int)) (=> (and (Q a c) (not (= a c))) false)))
(check-sat)
";

/// SAFE twin of `H3`: the rule's head is tied to `a`, so c = a + 2.
pub(super) const H3_SAFE: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int Int) Bool)
(assert (forall ((x Int)) (=> true (P (+ x 1)))))
(assert (forall ((a Int)) (=> (P a) (Q a (+ a 2)))))
(assert (forall ((a Int) (c Int)) (=> (and (Q a c) (= c (+ a 5))) false)))
(check-sat)
";

/// SAFE twin of `H8`: Q only relates a value to itself.
const H8_SAFE: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int Int) Bool)
(assert (forall ((n Int)) (=> true (P (* 2 n)))))
(assert (forall ((a Int)) (=> (P a) (Q a a))))
(assert (forall ((a Int) (c Int)) (=> (and (Q a c) (not (= a c))) false)))
(check-sat)
";

pub(super) fn parse(input: &str) -> ChcProblem {
    ChcParser::parse(input).unwrap()
}

/// `P0(0)`, then `stages` levels each reached by two alternative steps
/// (+1 or +2), then `P_stages(x) /\ x = target => false`: 2^stages chains.
/// `guarded` restricts the +1 step to `x >= 0` and the +2 step to `x < 0`,
/// so exactly one chain is feasible (x = stage at every stage).
fn diamond_ladder(stages: usize, target: i64, guarded: bool) -> String {
    let mut input = String::from("(set-logic HORN)\n");
    for stage in 0..=stages {
        input.push_str(&format!("(declare-fun P{stage} (Int) Bool)\n"));
    }
    input.push_str("(assert (P0 0))\n");
    for stage in 1..=stages {
        for (step, guard) in [(1, "(>= x 0)"), (2, "(< x 0)")] {
            let guard = if guarded { guard } else { "true" };
            input.push_str(&format!(
                "(assert (forall ((x Int)) (=> (and (P{} x) {guard}) (P{stage} (+ x {step})))))\n",
                stage - 1
            ));
        }
    }
    input.push_str(&format!(
        "(assert (forall ((x Int)) (=> (and (P{stages} x) (= x {target})) false)))\n(check-sat)\n"
    ));
    input
}

/// Decide the full-inlining formulas (the strict replay's encoding) for a
/// problem, to cross-check the path encoding on linear cones.
fn inlining_unsat(problem: &ChcProblem) -> bool {
    let formulas =
        crate::proof_metadata::replay_check::acyclic_exhaustion_query_formulas(problem).unwrap();
    formulas.iter().all(|(_, formula)| {
        let script = super::render(formula).unwrap();
        let verdict = super::decide(&script, Instant::now() + BUDGET, None).unwrap();
        verdict.as_deref() == Some("unsat")
    })
}

#[test]
fn head_only_variable_repros_and_their_controls_are_refuted() {
    for (name, input) in [("h3", H3), ("h8", H8), ("h3y", H3Y), ("h8m", H8M)] {
        let outcome = check(&parse(input), BUDGET, None);
        assert_eq!(
            outcome,
            Err(NotConfirmed::NotUnsat(Some("sat".to_string()))),
            "{name} is UNSAFE; its derivation formula must be sat"
        );
    }
}

#[test]
fn safe_twins_are_confirmed() {
    for (name, input) in [("h3-safe", H3_SAFE), ("h8-safe", H8_SAFE)] {
        assert_eq!(check(&parse(input), BUDGET, None), Ok(()), "{name}");
    }
}

/// The path encoding and the strict replay's full inlining agree on every
/// linear fixture, safe and unsafe.
#[test]
fn path_encoding_agrees_with_full_inlining_on_linear_cones() {
    let ladder_safe = diamond_ladder(4, 100, false);
    let ladder_unsafe = diamond_ladder(4, 6, false);
    for (name, input) in [
        ("h3", H3),
        ("h8", H8),
        ("h3y", H3Y),
        ("h8m", H8M),
        ("h3-safe", H3_SAFE),
        ("h8-safe", H8_SAFE),
        ("ladder-safe", ladder_safe.as_str()),
        ("ladder-unsafe", ladder_unsafe.as_str()),
    ] {
        let problem = parse(input);
        assert_eq!(
            confirmed(&problem, BUDGET, None),
            inlining_unsat(&problem),
            "{name}: path encoding and full inlining disagree"
        );
    }
}

/// 2^16 syntactic chains: full inlining exceeds its 10,000-instantiation
/// cap, the path encoding stays linear in the clause count and decides both
/// directions.
#[test]
fn path_encoding_decides_exponentially_many_chains() {
    let safe = parse(&diamond_ladder(16, 100, true));
    assert!(crate::proof_metadata::replay_check::acyclic_exhaustion_query_formulas(&safe).is_err());
    assert_eq!(check(&safe, BUDGET, None), Ok(()));
    // Refusal is all that matters in this direction: `sat`, or a timeout.
    let unsafe_ladder = parse(&diamond_ladder(16, 16, true));
    assert!(check(&unsafe_ladder, BUDGET, None).is_err());
}

/// A 130-predicate chain is deeper than full inlining's 128-level cap.
#[test]
fn path_encoding_decides_a_chain_deeper_than_the_inlining_cap() {
    let mut input = String::from("(set-logic HORN)\n");
    for index in 0..130 {
        input.push_str(&format!("(declare-fun P{index} (Int) Bool)\n"));
    }
    input.push_str("(assert (P0 0))\n");
    for index in 1..130 {
        input.push_str(&format!(
            "(assert (forall ((x Int)) (=> (P{} x) (P{index} (+ x 1)))))\n",
            index - 1
        ));
    }
    let safe = format!("{input}(assert (forall ((x Int)) (=> (and (P129 x) (= x 999)) false)))\n");
    assert_eq!(check(&parse(&safe), BUDGET, None), Ok(()));
    let reachable =
        format!("{input}(assert (forall ((x Int)) (=> (and (P129 x) (= x 129)) false)))\n");
    assert!(matches!(
        check(&parse(&reachable), BUDGET, None),
        Err(NotConfirmed::NotUnsat(_))
    ));
}

/// Nonlinear cones take the full inlining, in both directions.
#[test]
fn nonlinear_cones_are_decided_by_full_inlining() {
    let base = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun R (Int Int) Bool)
(assert (P 0))
(assert (P 1))
(assert (forall ((x Int) (y Int)) (=> (and (P x) (P y)) (R x y))))
";
    let safe = format!(
        "{base}(assert (forall ((x Int) (y Int)) (=> (and (R x y) (= (+ x y) 3)) false)))\n"
    );
    let reachable = format!(
        "{base}(assert (forall ((x Int) (y Int)) (=> (and (R x y) (= (+ x y) 2)) false)))\n"
    );
    assert_eq!(check(&parse(&safe), BUDGET, None), Ok(()));
    assert_eq!(
        check(&parse(&reachable), BUDGET, None),
        Err(NotConfirmed::NotUnsat(Some("sat".to_string())))
    );
}

/// Finite datatypes are decided (declarations rendered); the unsafe fixture
/// is the one the finalize-gate test used to admit as SAFE.
#[test]
fn finite_datatype_cones_are_decided() {
    let base = "(set-logic HORN)
(declare-datatypes ((Opt 0)) (((none) (some (val Int)))))
(declare-fun P (Opt) Bool)
(declare-fun Q (Opt) Bool)
(assert (forall ((o Opt)) (=> (= o none) (P o))))
(assert (forall ((o Opt)) (=> (P o) (Q o))))
";
    let safe = format!("{base}(assert (forall ((o Opt)) (=> (and (Q o) (= o (some 0))) false)))\n");
    let reachable =
        format!("{base}(assert (forall ((o Opt)) (=> (and (Q o) (= o none)) false)))\n");
    assert_eq!(check(&parse(&safe), BUDGET, None), Ok(()));
    assert!(matches!(
        check(&parse(&reachable), BUDGET, None),
        Err(NotConfirmed::NotUnsat(_))
    ));
}

/// A query-irrelevant cycle is outside the query cone; a cycle inside it
/// makes a fixed unrolling non-exhaustive and refuses.
#[test]
fn only_cycles_inside_the_query_cone_refuse() {
    let dead_end = H3_SAFE.replace(
        "(check-sat)",
        "(declare-fun D (Int) Bool)
(assert (D 0))
(assert (forall ((x Int)) (=> (D x) (D (+ x 1)))))
(check-sat)",
    );
    let dead_end = parse(&dead_end);
    assert!(dead_end.has_cycles());
    assert_eq!(check(&dead_end, BUDGET, None), Ok(()));

    let looping = parse(
        "(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 5)) (inv (+ x 1)))))
(assert (forall ((x Int)) (=> (and (inv x) (> x 5)) false)))
(check-sat)
",
    );
    assert_eq!(
        check(&looping, BUDGET, None),
        Err(NotConfirmed::CyclicQueryCone)
    );
}

#[test]
fn unadmitted_theories_refuse() {
    let recursive = parse(
        "(set-logic HORN)
(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
(declare-fun P (Lst) Bool)
(declare-fun Q (Lst) Bool)
(assert (forall ((l Lst)) (=> (= l nil) (P l))))
(assert (forall ((l Lst)) (=> (P l) (Q l))))
(assert (forall ((l Lst)) (=> (and (Q l) (= l (cons 0 nil))) false)))
(check-sat)
",
    );
    assert_eq!(
        check(&recursive, BUDGET, None),
        Err(NotConfirmed::UnsupportedTheory)
    );
    let real = parse(
        "(set-logic HORN)
(declare-fun P (Real) Bool)
(declare-fun Q (Real) Bool)
(assert (P 0.5))
(assert (forall ((r Real)) (=> (P r) (Q r))))
(assert (forall ((r Real)) (=> (and (Q r) (> r 1.0)) false)))
(check-sat)
",
    );
    assert_eq!(
        check(&real, BUDGET, None),
        Err(NotConfirmed::UnsupportedTheory)
    );
}

/// A safe problem is still refused without budget or after cancellation.
#[test]
fn no_budget_or_cancellation_refuses_a_safe_problem() {
    let safe = parse(H3_SAFE);
    assert_eq!(
        check(&safe, Duration::ZERO, None),
        Err(NotConfirmed::Budget)
    );
    let cancelled = CancellationToken::new();
    cancelled.cancel();
    assert_eq!(
        check(&safe, BUDGET, Some(&cancelled)),
        Err(NotConfirmed::Budget)
    );
    assert!(!super::confirmed_at_finalize(
        &safe,
        Some(Duration::ZERO),
        &CancellationToken::new(),
        None
    ));
    assert!(!super::confirmed_at_finalize(
        &safe,
        None,
        &CancellationToken::new(),
        Some(&cancelled)
    ));
    assert!(super::confirmed_at_finalize(
        &safe,
        None,
        &CancellationToken::new(),
        None
    ));
}

/// MODEL_CHECKER_CONSUMER-shaped: a 40-predicate BV64 chain ending in a nullary `error`.
/// The overflow query is unreachable; `start < end` is reachable.
#[test]
fn bitvector_chains_are_decided_within_budget() {
    let chain = |query: &str| {
        let mut input = String::from("(set-logic HORN)\n");
        for index in 0..40 {
            input.push_str(&format!(
                "(declare-rel P{index} ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64)))\n"
            ));
        }
        input.push_str(
            "(declare-rel error ())\n(declare-var start (_ BitVec 64))\n\
             (declare-var end (_ BitVec 64))\n(declare-var off (_ BitVec 64))\n\
             (rule (=> (and (bvule start end) (bvule end (_ bv5 64)) (bvule off (_ bv4 64)) \
             (bvule (bvadd start off) (_ bv4 64))) (P0 start end off)))\n",
        );
        for index in 0..39 {
            input.push_str(&format!(
                "(rule (=> (P{index} start end off) (P{} start end off)))\n",
                index + 1
            ));
        }
        input.push_str(&format!(
            "(rule (=> (and (P39 start end off) {query}) error))\n(query error)\n"
        ));
        parse(&input)
    };
    let safe = chain("(bvult (bvadd start off) start)");
    let started = Instant::now();
    assert_eq!(check(&safe, BUDGET, None), Ok(()));
    assert!(
        started.elapsed() < Duration::from_secs(5),
        "{:?}",
        started.elapsed()
    );
    assert!(matches!(
        check(&chain("(bvult start end)"), BUDGET, None),
        Err(NotConfirmed::NotUnsat(_))
    ));
}

/// Upstream 57a4dcc19's repro, a second BMC naming defect (a query variable
/// `t` bound at two sorts): UNSAFE (`y >= 5` is reachable). The check was not
/// written for it and refutes it anyway.
#[test]
fn sort_clash_repro_is_refuted() {
    let sort_clash = parse(
        "(set-logic HORN)
(declare-fun U (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (=> (>= x 2) (U x))))
(assert (forall ((y Int)) (=> (U y) (Q y))))
(assert (forall ((c Int) (t Bool)) (=> (and (= t (= c 1)) (Q c) t) false)))
(assert (forall ((y Int) (t Int)) (=> (and (= t y) (>= t 5) (Q y)) false)))
(check-sat)
",
    );
    assert_eq!(
        check(&sort_clash, BUDGET, None),
        Err(NotConfirmed::NotUnsat(Some("sat".to_string())))
    );
}

/// UNSAFE (`P(6)` is derived and queried). The fact's variable `name` occurs
/// a second time 501 `ite` levels deep, below the depth at which renaming
/// (`ChcExpr::substitute`) and `ChcExpr::vars` stop.
fn deep_occurrence(name: &str) -> String {
    let mut nested = name.to_string();
    for _ in 0..501 {
        nested = format!("(ite (> {name} (- 1000000)) {nested} 0)");
    }
    format!(
        "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall (({name} Int)) (=> (and (= {name} 5) (= {nested} 5)) (P (+ {name} 1)))))
(assert (forall ((a Int)) (=> (P a) (Q a))))
(assert (forall ((z Int)) (=> (and (Q z) (= z 6)) false)))
(check-sat)
"
    )
}

/// A source variable spelled like a fresh constant, surviving renaming below
/// the depth cap, aliased that constant: the path formula then said `unsat`
/// for this UNSAFE problem (adversarial review of the first cut). Both a
/// clause that reaches the depth cap and a reserved spelling at any depth now
/// refuse before encoding.
#[test]
fn clauses_that_could_defeat_renaming_refuse() {
    for name in ["__eac_p0_a0", "y"] {
        assert!(
            matches!(
                check(&parse(&deep_occurrence(name)), BUDGET, None),
                Err(NotConfirmed::Encoding(_))
            ),
            "{name}: a clause below the renaming depth cap must refuse"
        );
    }
    let rule = "((a Int)) (=> (P a) (Q a (+ a 2))))";
    assert!(H3_SAFE.contains(rule));
    for reserved in ["__eac_c1_v0", "__acx0_y"] {
        let renamed = rule.replace('a', reserved);
        let shallow = parse(&H3_SAFE.replace(rule, &renamed));
        assert!(
            matches!(
                check(&shallow, BUDGET, None),
                Err(NotConfirmed::Encoding(_))
            ),
            "{reserved}: a reserved spelling must refuse even where renaming is complete"
        );
    }
}
