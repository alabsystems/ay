// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Push/pop soundness of #inc-dead-atoms: the session-persistent QF_LRA lanes
//! withhold from the theory every atom whose only assertions were popped.
//!
//! The scripts are shaped to hit each edge of that change:
//! * dead `=` atoms from Kopczynski-style `(or (= a b) …)` scopes must not
//!   constrain later checks (a leak would be a false UNSAT);
//! * a popped atom that is asserted AGAIN in a later scope is live again and
//!   must reach the theory (withholding it would be a false SAT);
//! * a disequality split whose atom `(< a 0.0)` / `(> b 0.0)` is literally a
//!   dead atom re-uses that dead SAT var, so the atom must be revived — the
//!   split clause is otherwise satisfiable through a literal the theory never
//!   hears about.
//!
//! Every verdict is pinned to z3 4.x and to the isolated from-scratch lane
//! (`lra_inc_engine_override = Some(false)`), which builds a fresh atom set per
//! check-sat and so never has dead atoms.

use std::time::Duration;

use crate::incremental_state::DeadAtomStats;
use crate::Executor;
use ay_frontend::parse;

/// Per-check-sat wall deadline: a hang guard only. Every check here is decided
/// in milliseconds; the engine lane's work is pinned by
/// [`ENGINE_CONFLICT_CANARY`], which host load cannot move.
const SOLVE_TIMEOUT: Duration = Duration::from_secs(30);

/// Ceiling on the SAT conflicts the engine lane's session solver spends over
/// one script: a counted, load-independent canary. Measured: 1 to 13 per
/// script (13 on `many_popped_scopes_keep_every_check_exact`, 37 checks; 9 on
/// the ITE rounds; 2 to 5 on the four `lra_inc_lazy_reasons` scripts, in
/// either publication posture). When the
/// assumption loop did not materialise lazy theory reasons before 1UIP
/// (#8467), the ITE rounds' second check failed closed on every conflict and
/// spent 999,997 of them, 6.1 s of CPU on a fast core: an `unknown` at
/// [`SOLVE_TIMEOUT`] on a slow core shared with three spinning loads. The
/// whole test now takes 0.14 s of CPU, and 1.1 s of wall on a slow core
/// shared with six.
const ENGINE_CONFLICT_CANARY: u64 = 1_000;

/// The publication posture a script runs in.
#[derive(Clone, Copy, Debug)]
pub(super) enum Posture {
    /// `Executor::new()`'s own: the internal proof cycle runs.
    Default,
    /// Competition mode (`--z3-mode`): the internal proof cycle is shed
    /// (`competition_shedding_active`), so a verdict is published without
    /// its certification.
    Competition,
}

/// One lane's verdicts, its dead-atom counters, and the SAT conflicts of its
/// session-persistent solver over the script (0 on the from-scratch lane,
/// which keeps none).
fn run_verdicts(
    script: &str,
    inc_engine_override: Option<bool>,
    posture: Posture,
) -> (Vec<String>, DeadAtomStats, u64) {
    let mut exec = Executor::new();
    exec.lra_inc_engine_override = inc_engine_override;
    exec.set_competition_mode(matches!(posture, Posture::Competition));
    exec.set_timeout(Some(SOLVE_TIMEOUT));
    let mut verdicts = Vec::new();
    let (mut conflicts, mut lifetime) = (0, 0);
    for cmd in &parse(script).expect("script parses") {
        if let Some(out) = exec.execute(cmd).expect("command executes") {
            verdicts.push(out);
        }
        // The solver's lifetime count; a rebuilt solver counts from 0 again.
        let now = session_conflicts(&exec);
        conflicts += now.checked_sub(lifetime).unwrap_or(now);
        lifetime = now;
    }
    let stats = exec
        .incr_theory_state
        .as_ref()
        .map(|state| state.dead_atom_stats)
        .unwrap_or_default();
    (verdicts, stats, conflicts)
}

fn session_conflicts(exec: &Executor) -> u64 {
    exec.incr_theory_state
        .as_ref()
        .and_then(|state| state.persistent_sat.as_ref())
        .map_or(0, |sat| sat.total_num_conflicts())
}

/// Pin the verdicts on both lanes and return the engine lane's counters.
///
/// The engine lane is fail-closed (a withheld atom it needed surfaces as a
/// rejected model or a non-converging split loop, i.e. an `unknown` that the
/// from-scratch lane then answers), so verdicts alone cannot see a broken
/// filter: the counters must show the engine answered EVERY check itself.
pub(super) fn assert_engine_decides(script: &str, expected: &[&str], what: &str) -> DeadAtomStats {
    assert_engine_decides_in(Posture::Default, script, expected, what)
}

/// [`assert_engine_decides`] in the given publication posture.
pub(super) fn assert_engine_decides_in(
    posture: Posture,
    script: &str,
    expected: &[&str],
    what: &str,
) -> DeadAtomStats {
    assert_eq!(
        run_verdicts(script, Some(false), posture).0,
        expected,
        "sanity: the isolated from-scratch lane must give the z3 verdicts ({what}, {posture:?})"
    );
    let (verdicts, stats, conflicts) = run_verdicts(script, Some(true), posture);
    assert_eq!(
        verdicts, expected,
        "session-persistent engine lane must match z3 ({what}, {posture:?})"
    );
    assert_eq!(
        stats.engine_fallbacks, 0,
        "the engine lane must decide every check itself, not lean on the fallback \
         ({what}, {posture:?}): {stats:?}"
    );
    assert!(
        conflicts <= ENGINE_CONFLICT_CANARY,
        "the engine lane spent {conflicts} SAT conflicts ({what}, {posture:?}), canary \
         {ENGINE_CONFLICT_CANARY}: a conflict loop that learns nothing is back"
    );
    stats
}

/// [`assert_engine_decides`] for a script whose popped scopes leave dead atoms.
fn assert_engine_matches(script: &str, expected: &[&str], what: &str) -> DeadAtomStats {
    let stats = assert_engine_decides(script, expected, what);
    assert!(
        stats.withheld > 0,
        "popped scopes must leave dead atoms to withhold ({what})"
    );
    assert_eq!(
        stats.revive_all, 0,
        "precise revival must converge without the revive-all backstop ({what}): {stats:?}"
    );
    stats
}

const DEAD_ATOM_SCRIPT: &str = "\
(set-logic QF_LRA)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(push 1)
(assert (or (= a b) (= a c) (= b c)))
(check-sat)
(pop 1)
(push 1)
(assert (and (not (= a b)) (not (= a c)) (not (= b c))))
(check-sat)
(pop 1)
(push 1)
(assert (= a b))
(assert (= b c))
(assert (not (= a c)))
(check-sat)
(pop 1)
(push 1)
(assert (< a 0.0))
(assert (> b 0.0))
(check-sat)
(pop 1)
(push 1)
(assert (not (= a 0.0)))
(assert (>= a 0.0))
(check-sat)
(push 1)
(assert (<= a 0.0))
(check-sat)
(pop 1)
(pop 1)
(push 1)
(assert (not (= b 0.0)))
(assert (<= b 0.0))
(assert (>= b (- 1.0)))
(check-sat)
(pop 1)
(push 1)
(assert (< a 0.0))
(assert (> a 0.0))
(check-sat)
(pop 1)
(push 1)
(assert (< a 0.0))
(check-sat)
(pop 1)
(check-sat)
";

#[test]
fn dead_atoms_neither_leak_nor_hide_revived_or_reasserted_atoms() {
    let stats = assert_engine_matches(
        DEAD_ATOM_SCRIPT,
        &[
            "sat", "sat", "unsat", "sat", "sat", "unsat", "sat", "unsat", "sat", "sat",
        ],
        "dead equalities, split re-use of dead (< a 0.0)/(> b 0.0), re-asserted atoms",
    );
    assert!(
        stats.revived > 0,
        "the (not (= a 0.0)) / (not (= b 0.0)) splits re-use the dead (< a 0.0) / (> b 0.0) \
         vars, which must be revived: {stats:?}"
    );
}

/// Many popped scopes over the same variables: every later check sees a large
/// dead-atom population (the Kopczynski shape) whose stale `=`/`<=` atoms, if
/// they still reached the theory, would either over-constrain (false UNSAT)
/// or — when withheld but needed — under-constrain (false SAT).
#[test]
fn many_popped_scopes_keep_every_check_exact() {
    let mut script = String::from(
        "(set-logic QF_LRA)\n(declare-const x Real)\n(declare-const y Real)\n(declare-const z Real)\n",
    );
    let mut expected = Vec::new();
    for k in 0..12 {
        // Dead-to-be: pins x to k in one branch and forces x != y.
        script.push_str(&format!(
            "(push 1)\n(assert (or (= x {k}.0) (= y {k}.0)))\n(assert (not (= x y)))\n(check-sat)\n(pop 1)\n"
        ));
        expected.push("sat");
        // Re-asserts one of the now-dead atoms together with a contradiction.
        script.push_str(&format!(
            "(push 1)\n(assert (= x {k}.0))\n(assert (> x (+ {k}.0 z)))\n(assert (>= z 0.0))\n(check-sat)\n(pop 1)\n"
        ));
        expected.push("unsat");
        // Needs the disequality split on a variable whose split atoms can
        // coincide with atoms minted by earlier (popped) checks.
        script.push_str(&format!(
            "(push 1)\n(assert (not (= y {k}.0)))\n(assert (<= y {k}.0))\n(assert (>= y (- {k}.0 1.0)))\n(check-sat)\n(pop 1)\n"
        ));
        expected.push("sat");
    }
    script.push_str("(check-sat)\n");
    expected.push("sat");
    assert_engine_matches(&script, &expected, "twelve rounds of popped scopes");
}

/// The ITE/Bool/distinct shape the first #inc-dead-atoms version got wrong
/// (fuzz_ite seed 101 script 163, minimised): ONE check-sat after `(push 1)`,
/// nothing popped. Its ITE-lifted comparisons (`(<= x 0.0)`, `(< y x)`, ...)
/// appear in no assertion as written, and syntactic liveness withheld all 8 of
/// them (a rejected model on the engine lane) while the search it steered into
/// hit the `is_expression_forced_to_value` sign bug: a false UNSAT through the
/// CLI. Liveness now comes from the encoded cone, so nothing is withheld.
const ITE_NO_POP_SCRIPT: &str = "\
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(declare-const p Bool)
(declare-const q Bool)
(push 1)
(assert (or (and (distinct (ite (<= x 2.0) 0.0 z) (ite (= x 2.0) (+ x (+ x 1.0)) (ite p (+ z 1.0) (+ x 1.0)))) (not p)) (<= (ite q 0.0 (ite (= x (- 1.0)) x y)) 0.0)))
(assert (distinct (* 2.0 y) (* 2.0 z)))
(assert (=> (> (ite p x (* 2.0 z)) (ite p y y)) (and (distinct 1.0 (ite (= y 2.0) (* 2.0 x) x)) (>= (+ y (ite (< x 1.0) 1.0 y)) (ite q (ite (<= z 1.0) x (+ x 1.0)) x)) (not q))))
(assert (or (distinct x x) (not (= (ite p (* 2.0 z) (+ x (+ y 1.0))) (+ y 2.0))) (or (> y z) (= x y))))
(assert (distinct (ite p x (ite (< y 1.0) (+ z 1.0) y)) y))
(assert (<= y z))
(check-sat)
";

#[test]
fn ite_lifted_atoms_of_an_unpopped_scope_are_live() {
    let stats = assert_engine_decides(
        ITE_NO_POP_SCRIPT,
        &["sat"],
        "ITE-lifted atoms, single check-sat after push, nothing popped",
    );
    assert_eq!(
        stats.withheld, 0,
        "nothing was popped, so no atom may be withheld: {stats:?}"
    );
}

/// The pre-existing false UNSAT of the base engine lane (fuzz_pushpop seed 12
/// script 44): `(<= z y)` and `(not (< y z))` are the SAME side of `y - z`, so
/// `y != z` is satisfiable. Base `5fb8b97e0` answered unsat here.
#[test]
fn one_sided_opposite_slacks_do_not_refute_a_disequality() {
    let script = "\
(set-logic QF_LRA)
(declare-const y Real)
(declare-const z Real)
(assert (= z 0.0))
(assert (distinct y z))
(assert (or (<= z y) (= y 0.0)))
(assert (or (< y z) (<= y 5.0)))
(push 1)
(check-sat)
";
    let stats = assert_engine_decides(script, &["sat"], "one-sided opposite slacks");
    assert_eq!(stats.withheld, 0, "nothing was popped: {stats:?}");
}

/// ITE/Bool/distinct push-pop rounds: every popped scope leaves lifted atoms
/// behind (dead), a later scope re-lifts overlapping comparisons, and a
/// nested push/pop re-uses a scope's lifted atoms (live). Verdicts pinned to
/// z3 4.16 and cvc5 1.3.0.
#[test]
fn ite_lifted_atoms_die_with_their_scope_and_revive_with_a_new_one() {
    let body = ITE_NO_POP_SCRIPT
        .strip_suffix("(check-sat)\n")
        .expect("script ends with check-sat");
    let script = format!(
        "{body}(check-sat)
(pop 1)
(push 1)
(assert (distinct (ite p x y) (ite q y z)))
(assert (= x y))
(assert (= y z))
(check-sat)
(pop 1)
(push 1)
(assert (<= (ite q 0.0 (ite (= x (- 1.0)) x y)) 0.0))
(assert (not q))
(assert (> y 0.0))
(assert (distinct x (- 1.0)))
(check-sat)
(pop 1)
(push 1)
(assert (<= (ite q 0.0 (ite (= x (- 1.0)) x y)) 0.0))
(assert (not q))
(assert (> y 0.0))
(check-sat)
(push 1)
(assert (distinct x (- 1.0)))
(check-sat)
(pop 1)
(pop 1)
(push 1)
(assert (> (ite p x (* 2.0 z)) (ite q y (+ y 1.0))))
(assert (not p))
(assert (<= z (* 0.5 y)))
(assert (distinct y 0.0))
(check-sat)
(pop 1)
(check-sat)
"
    );
    assert_engine_matches(
        &script,
        &["sat", "unsat", "unsat", "sat", "unsat", "unsat", "sat"],
        "ITE/Bool/distinct push-pop rounds",
    );
}
