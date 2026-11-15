// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Stepwise `ExecutionSession` (#execution-session): verdicts, scope-correct
//! proof premises, the live-scope digest, the translation memo, and checks
//! that time out inside a session.

use std::time::Duration;

use super::*;
use crate::constraint::Constraint;
use ay_dpll::api::StrictProofVerdict;

fn proof_header(logic: &str) -> AYProgram {
    let mut header = AYProgram::new();
    header.add_constraint(Constraint::set_option(":produce-proofs", "true"));
    header.set_logic(logic);
    header
}

fn is_unsat(check: &SessionCheck) -> bool {
    matches!(check.outcome.result, ExecuteTypedResult::Verified)
}

fn is_sat(check: &SessionCheck) -> bool {
    matches!(check.outcome.result, ExecuteTypedResult::Counterexample(_))
}

fn verified_alethe(check: &SessionCheck) -> String {
    let artifact = check
        .outcome
        .unsat_proof
        .as_ref()
        .expect("a session UNSAT carries its proof artifact");
    assert!(
        matches!(&artifact.strict_verdict, StrictProofVerdict::Verified(_)),
        "the session artifact must be strictly verified: {:?}",
        artifact.strict_verdict
    );
    // A session artifact does not re-render the live stack — except after a
    // canonical-spelling rescue, whose document only the canonical problem
    // matches, so it ships that problem.
    if let Some(problem) = &artifact.alethe_problem_smt2 {
        assert!(
            problem.contains("(assert "),
            "a rescued session artifact carries its canonical problem:\n{problem}"
        );
    }
    artifact.alethe.clone()
}

/// THE NEGATIVE CONTROL. A contradiction asserted in a scope that was popped
/// must never be a premise of a later proof. The later query is refuted on
/// its own; if the popped `(p, (not p))` pair leaked into it — as a live
/// assertion, a retained learned clause, or an authorized proof premise — the
/// cheapest refutation would use it, so its absence from the proof is the
/// measurement, not an assumption.
#[test]
fn a_popped_assertion_is_never_a_premise_of_a_later_proof() {
    let mut header = proof_header("QF_LIA");
    let popped = header.declare_const("popped_premise", Sort::bool());
    let x = header.declare_const("x", Sort::int());
    let mut session = ExecutionSession::new(&header).expect("session opens");

    session.push().unwrap();
    session.assert(&popped).unwrap();
    session.assert(&popped.clone().not()).unwrap();
    let first = session.check_sat(None).unwrap();
    assert!(
        is_unsat(&first),
        "the popped scope is refuted: {:?}",
        first.outcome.result
    );
    assert!(verified_alethe(&first).contains("popped_premise"));
    session.pop().unwrap();

    session.push().unwrap();
    session.assert(&x.clone().int_gt(Expr::int(5))).unwrap();
    session.assert(&x.int_lt(Expr::int(3))).unwrap();
    let second = session.check_sat(None).unwrap();
    assert!(is_unsat(&second), "{:?}", second.outcome.result);
    let alethe = verified_alethe(&second);
    assert!(
        !alethe.contains("popped_premise"),
        "a popped assertion reached a later proof:\n{alethe}"
    );
    assert_eq!(second.live_assertions, 2);
}

/// Learned state of a popped scope must not decide a later query either: the
/// same bound that was refuted beside its contradiction is satisfiable alone.
#[test]
fn a_popped_refutation_leaves_no_learned_contradiction_behind() {
    let mut header = proof_header("QF_LIA");
    let x = header.declare_const("x", Sort::int());
    let mut session = ExecutionSession::new(&header).unwrap();
    let above = x.clone().int_gt(Expr::int(5));

    session.push().unwrap();
    session.assert(&above).unwrap();
    session.assert(&x.int_lt(Expr::int(3))).unwrap();
    assert!(is_unsat(&session.check_sat(None).unwrap()));
    session.pop().unwrap();

    session.push().unwrap();
    session.assert(&above).unwrap();
    let alone = session.check_sat(None).unwrap();
    assert!(
        is_sat(&alone),
        "the bound alone is satisfiable: {:?}",
        alone.outcome.result
    );
}

/// Outer-scope assertions ARE live premises of an inner check: the refutation
/// needs a fact asserted two scopes out, and certifies.
#[test]
fn outer_scope_facts_are_live_premises_of_an_inner_check() {
    let mut header = proof_header("QF_LIA");
    let x = header.declare_const("x", Sort::int());
    let y = header.declare_const("y", Sort::int());
    let mut session = ExecutionSession::new(&header).unwrap();

    session.push().unwrap();
    session.assert(&x.clone().int_ge(Expr::int(0))).unwrap();
    session.push().unwrap();
    session
        .assert(&y.clone().eq(x.clone().int_add(Expr::int(1))))
        .unwrap();
    session.push().unwrap();
    session.assert(&y.int_le(Expr::int(0))).unwrap();
    let check = session.check_sat(None).unwrap();
    assert!(is_unsat(&check), "{:?}", check.outcome.result);
    verified_alethe(&check);
    assert_eq!(check.live_assertions, 3);
}

/// The live-scope digest names the live stack exactly: `pop` restores the
/// value it had at the matching `push`, and two sessions that assert the same
/// sequence agree on it.
#[test]
fn the_live_scope_digest_follows_push_and_pop() {
    let mut header = proof_header("QF_LIA");
    let x = header.declare_const("x", Sort::int());
    let mut first = ExecutionSession::new(&header).unwrap();
    let mut second = ExecutionSession::new(&header).unwrap();
    let empty = first.live_scope_digest();

    first.push().unwrap();
    first.assert(&x.clone().int_ge(Expr::int(0))).unwrap();
    let outer = first.live_scope_digest();
    assert_ne!(outer, empty);
    first.push().unwrap();
    first.assert(&x.clone().int_le(Expr::int(9))).unwrap();
    let inner = first.live_scope_digest();
    assert_ne!(inner, outer);
    first.pop().unwrap();
    assert_eq!(first.live_scope_digest(), outer);
    first.pop().unwrap();
    assert_eq!(first.live_scope_digest(), empty);
    assert_eq!(first.live_assertions(), 0);

    second.push().unwrap();
    let first_node = second.assert(&x.clone().int_ge(Expr::int(0))).unwrap();
    assert_eq!(second.live_scope_digest(), outer);
    assert_eq!(
        second.scope_digest_of(&[first_node]),
        outer,
        "a caller recomputes the digest from its own record of the row"
    );
    second.push().unwrap();
    second.assert(&x.int_le(Expr::int(8))).unwrap();
    assert_ne!(
        second.live_scope_digest(),
        inner,
        "a different fact changes the digest"
    );
}

/// The live digest names the PROBLEM, not only the assertions: two sessions
/// whose headers differ only in a definition's body disagree on it, though
/// they assert the same expression (and decide it differently).
#[test]
fn the_live_scope_digest_covers_definition_bodies() {
    let digest_with = |offset: i64| {
        let mut header = AYProgram::new();
        header.set_logic("QF_LIA");
        let x = header.declare_const("x", Sort::int());
        let y = Expr::var("y", Sort::int());
        header.define_fun(
            "f",
            vec![("y".to_string(), Sort::int())],
            y.int_add(Expr::int(offset)),
        );
        let mut session = ExecutionSession::new(&header).unwrap();
        let applied = Expr::func_app_with_sort("f", vec![x.clone()], Sort::int());
        session.push().unwrap();
        session.assert(&applied.int_lt(x)).unwrap();
        let check = session.check_sat(None).unwrap();
        (check.live_scope_digest, is_unsat(&check))
    };
    let (plus, plus_unsat) = digest_with(1);
    let (minus, minus_unsat) = digest_with(-1);
    assert!(
        plus_unsat && !minus_unsat,
        "f(x) < x is refuted only for +1"
    );
    assert_ne!(plus, minus, "the definition body is part of the problem");
}

/// A node shared by every level of a deep DAG is translated and digested
/// once: the unfolded tree has 2^depth leaves, the memo holds O(depth) nodes,
/// and the check decides it. The timeout turns an exponential regression
/// into a failure instead of a hang.
///
/// No proof is requested here. A proof-carrying session retains each
/// assertion's SOURCE text, rendered as a tree and bounded at 8 MiB, and that
/// bound is what keeps the proof pipeline proportional: every consumer of a
/// retained source downstream (`expand_surface_lets`, the canonical surface
/// comparisons, the Alethe printer) is tree-shaped. MEASURED with the source
/// rendered with `let` sharing instead: this DAG at depth 20 asserted, then
/// its check took 1.8 s and 1.4 GB in `expand_surface_lets`, and at depth 22
/// it answered `unknown` (memout); the same `let`-shaped input as an SMT-LIB
/// file is `unknown` on main from depth 18. Lifting the bound needs DAG-aware
/// surface handling end to end, not a smaller source.
#[test]
#[ntest::timeout(120_000)]
fn a_dag_shaped_assertion_lowers_once_per_node() {
    let depth = 48;
    let mut header = AYProgram::new();
    header.set_logic("QF_LIA");
    let x = header.declare_const("x", Sort::int());
    let mut session = ExecutionSession::new(&header).unwrap();
    let mut node = x.clone();
    for _ in 0..depth {
        node = node.clone().int_add(node);
    }
    let fact = node.int_ge(Expr::int(0)).and(x.int_lt(Expr::int(0)));
    session.push().unwrap();
    session.assert(&fact).unwrap();
    let check = session.check_sat(None).unwrap();
    assert!(
        is_unsat(&check),
        "x >= 0 and x < 0: {:?}",
        check.outcome.result
    );
    assert!(
        session.memoized_nodes() <= 2 * depth + 16,
        "{} memoized nodes for a depth-{depth} DAG",
        session.memoized_nodes()
    );
    session.pop().unwrap();
    assert_eq!(
        session.memoized_nodes(),
        0,
        "a popped scope's memo entries are dropped"
    );
}

/// A check that times out answers `unknown` and leaves the session usable:
/// the scope pops and the next query is decided.
#[test]
fn a_timed_out_check_leaves_the_session_usable() {
    let mut header = proof_header("QF_NIA");
    let a = header.declare_const("a", Sort::int());
    let b = header.declare_const("b", Sort::int());
    let c = header.declare_const("c", Sort::int());
    let mut session = ExecutionSession::new(&header).unwrap();

    session.push().unwrap();
    // a^3 + b^3 = c^3 with a, b, c >= 1: no solution, and no quick refutation.
    let cube = |v: &Expr| v.clone().int_mul(v.clone()).int_mul(v.clone());
    session.assert(&a.clone().int_ge(Expr::int(1))).unwrap();
    session.assert(&b.clone().int_ge(Expr::int(1))).unwrap();
    session.assert(&c.clone().int_ge(Expr::int(1))).unwrap();
    session
        .assert(&cube(&a).int_add(cube(&b)).eq(cube(&c)))
        .unwrap();
    let hard = session.check_sat(Some(Duration::from_millis(200))).unwrap();
    assert!(
        !is_sat(&hard),
        "Fermat's cubic has no positive solution: {:?}",
        hard.outcome.result
    );
    session.pop().unwrap();

    session.push().unwrap();
    session.assert(&a.clone().int_gt(Expr::int(2))).unwrap();
    session.assert(&a.int_lt(Expr::int(1))).unwrap();
    let easy = session.check_sat(Some(Duration::from_secs(30))).unwrap();
    assert!(is_unsat(&easy), "{:?}", easy.outcome.result);
    assert!(session.poisoned().is_none());
}

/// A session refuses what a header or a step cannot mean.
#[test]
fn a_session_refuses_misplaced_steps() {
    let mut header = proof_header("QF_LIA");
    let x = header.declare_const("x", Sort::int());
    let mut session = ExecutionSession::new(&header).unwrap();
    assert!(session.pop().is_err(), "pop with no open scope");
    assert!(session.declare(&Constraint::CheckSat).is_err());

    let mut bad_header = proof_header("QF_LIA");
    bad_header.assert(x.int_gt(Expr::int(0)));
    assert!(
        ExecutionSession::new(&bad_header).is_err(),
        "a header must not assert"
    );
}

/// Session and one-shot execution agree row by row on a small ladder of
/// rows sharing one context cell.
#[test]
fn session_verdicts_match_fresh_per_row_verdicts() {
    let mut header = proof_header("QF_LIA");
    let x = header.declare_const("x", Sort::int());
    let y = header.declare_const("y", Sort::int());
    let context = [
        x.clone().int_ge(Expr::int(0)),
        y.clone().eq(x.clone().int_add(Expr::int(3))),
    ];
    let rows = [
        y.clone().int_lt(Expr::int(3)),
        y.clone().int_gt(Expr::int(3)),
        x.clone().int_gt(y.clone()),
        y.clone().eq(Expr::int(3)),
    ];

    let mut session = ExecutionSession::new(&header).unwrap();
    session.push().unwrap();
    for fact in &context {
        session.assert(fact).unwrap();
    }
    for row in &rows {
        session.push().unwrap();
        session.assert(row).unwrap();
        let in_session = session.check_sat(None).unwrap();
        session.pop().unwrap();

        let mut fresh = proof_header("QF_LIA");
        fresh.declare_const("x", Sort::int());
        fresh.declare_const("y", Sort::int());
        for fact in &context {
            fresh.assert(fact.clone());
        }
        fresh.assert(row.clone());
        fresh.check_sat();
        let fresh = execute_all_typed(&fresh).unwrap();
        assert_eq!(
            is_unsat(&in_session),
            matches!(fresh[0].result, ExecuteTypedResult::Verified),
            "row {row}: session {:?} vs fresh {:?}",
            in_session.outcome.result,
            fresh[0].result
        );
        assert_eq!(
            is_sat(&in_session),
            matches!(fresh[0].result, ExecuteTypedResult::Counterexample(_)),
            "row {row}: session {:?} vs fresh {:?}",
            in_session.outcome.result,
            fresh[0].result
        );
    }
}
