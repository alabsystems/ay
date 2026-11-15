// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `Solver::solve_with_extension_and_assumptions_core` (#horn-smt-session WP-1,
//! contract C8) and the learned-clause harvest guard for variables MINTED
//! mid-solve by an eager extension (`assumptions.rs`, the `is_assumption[v]`
//! read of the learned-clause harvest).
//!
//! - t1: 3-assumption UNSAT under a trivial extension returns a non-empty core
//!   that is a subset of the assumptions (the plain wrapper discards it).
//! - t2: `should_stop = || true` answers `Unknown` with `Interrupted`, and the
//!   stop is per call.
//! - t3: an extension mints a fresh variable from `check()` via `AddClauses`;
//!   after a forced backjump the minting clause re-propagates it INSIDE the
//!   assumption prefix and a later learned clause keeps it, so the harvest
//!   indexes `is_assumption` past the per-solve arrays sized at solve entry.
//!   Must not panic; the core must still be a subset of the assumptions.
//! - t4: the same refutation with an EAGER reason is learned in one analysis
//!   and yields a strict-subset core; so is it with a LAZY reason, which the
//!   loop materialises before 1UIP (#8467; it used to bail to level 0 and rely
//!   on the theory re-explaining the literal). A lazy handle the theory cannot
//!   rebuild still fails closed, but only in an analysis that resolves into it,
//!   and so does one rebuilt through a later literal ([`lazy_reason`]).
//! - t5: a theory conflict wholly below the current level is analysed at its
//!   own level; at the root it refutes the database ([`below_level_conflict`]).

#![allow(clippy::panic)]

use std::cell::Cell;

use ay_sat::{
    ExtCheckResult, ExtPropagateResult, Extension, Literal, SatUnknownReason, Solver,
    SolverContext, Variable,
};

#[path = "extension_tests/below_level_conflict.rs"]
mod below_level_conflict;
#[path = "extension_tests/lazy_reason.rs"]
mod lazy_reason;

fn pos(i: u32) -> Literal {
    Literal::positive(Variable::new(i))
}

fn neg(i: u32) -> Literal {
    Literal::negative(Variable::new(i))
}

/// A solver in the session's SAT profile (design §2.10, the `#lra-inc-engine`
/// recipe; order matters because `set_ic3_mode` re-enables scoped BVE). This
/// is the loop the `_core` entry and the harvest guard serve: IC3 mode turns
/// chronological backtracking OFF, so every conflict — including one with a
/// single literal at the conflict level — goes through 1UIP and produces a
/// learned clause (under chrono such a conflict takes the "forced" path and
/// learns nothing).
fn session_solver(num_vars: usize, clauses: &[Vec<Literal>]) -> Solver {
    let mut solver = Solver::new(num_vars);
    solver.set_ic3_mode();
    solver.set_bve_enabled(false);
    solver.set_inc_engine_reset_mode(true);
    solver.set_random_seed(2026);
    solver.set_unsat_certificate_enabled(false);
    solver.set_preprocess_enabled(false);
    for clause in clauses {
        let _ = solver.add_clause(clause.clone());
    }
    solver
}

/// A stop predicate that ends a solve by counted work, never by wall time.
/// The loop polls it at entry, then every 100 conflicts / 1024 iterations: a
/// handful of polls is far more than an exact solve here needs (t4a finishes
/// within two conflicts) and ends a fail-closed bail loop.
fn counted_stop(polls: &Cell<u32>) -> impl Fn() -> bool + '_ {
    move || {
        polls.set(polls.get() + 1);
        polls.get() > 8
    }
}

fn assert_core_subset(core: &[Literal], assumptions: &[Literal]) {
    assert!(!core.is_empty(), "empty core");
    for lit in core {
        assert!(
            assumptions.contains(lit),
            "core literal {lit:?} is not one of the assumptions {assumptions:?}"
        );
    }
}

struct NoopExtension;

impl Extension for NoopExtension {
    fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
        ExtPropagateResult::none()
    }

    fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
        ExtCheckResult::Sat
    }

    fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
        false
    }
}

/// t1: the core comes back, non-empty and inside the assumptions; the
/// irrelevant assumption is not in it.
#[test]
fn t1_core_entry_returns_nonempty_core_subset_of_assumptions() {
    // a=0, b=1, c=2; (¬a ∨ ¬b) refutes a ∧ b, c is irrelevant.
    let mut solver = session_solver(3, &[vec![neg(0), neg(1)]]);
    let assumptions = [pos(0), pos(1), pos(2)];
    let mut ext = NoopExtension;

    let result = solver.solve_with_extension_and_assumptions_core(
        &mut ext,
        &assumptions,
        None::<&fn() -> bool>,
    );
    let core = result
        .unsat_core()
        .unwrap_or_else(|| panic!("expected Unsat under a ∧ b, got {result:?}"));
    assert_core_subset(core, &assumptions);
    assert!(
        !core.contains(&pos(2)),
        "core {core:?} names c, which takes no part in the refutation"
    );

    // The pre-existing wrapper answers the same question without the core:
    // that is the gap the `_core` entry closes.
    let legacy = solver.solve_with_extension_and_assumptions(&mut ext, &assumptions);
    assert!(legacy.is_unsat(), "{legacy:?}");
}

/// t2: a stop predicate that is already true answers Unknown(Interrupted);
/// the predicate is per call, so the next call completes.
#[test]
fn t2_stop_predicate_true_returns_unknown_interrupted() {
    let mut solver = session_solver(2, &[vec![pos(0), pos(1)]]);
    let mut ext = NoopExtension;

    let stop = || true;
    let result = solver.solve_with_extension_and_assumptions_core(&mut ext, &[pos(0)], Some(&stop));
    assert!(result.is_unknown(), "{result:?}");
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::Interrupted)
    );

    let result = solver.solve_with_extension_and_assumptions_core(
        &mut ext,
        &[pos(0)],
        None::<&fn() -> bool>,
    );
    assert!(result.is_sat(), "{result:?}");
    assert_eq!(solver.last_unknown_reason(), None);
}

/// Variables of t3: assumptions a1=0, a2=1, a3=2; y=3 is a free decision
/// variable; the extension mints m = `ctx.num_vars()` (= 4) from `check()`.
///
/// Observed trajectory (session profile; levels a1=1, a2=2, a3=3, y=4):
/// 1. first `check`: mint m, `AddClauses([¬a1 ∨ m])`; the clause is unit under
///    a1 and propagates m at the CURRENT level 4 (a missed lower implication:
///    its watches are never revisited, so after a backjump nothing re-implies m).
/// 2. second `check`: `Conflict([¬m ∨ ¬y*])` with y* the literal y currently
///    satisfies. 1UIP resolves m and learns (¬a1 ∨ ¬y*): backjump to level 1.
///    m is unassigned and stays so until VSIDS decides it (saved phase true).
/// 3. third `check` (m decided at level 4): `Conflict([¬m ∨ ¬a2 ∨ ¬a3])`. m is
///    the only level-4 literal, so the learned clause is the conflict clause;
///    backjump to level 3 asserts ¬m, where (¬a1 ∨ m) is falsified. That
///    conflict has ONE current-level literal, m, so 1UIP learns (m ∨ ¬a1) with
///    the MINTED variable as UIP at level 3 — inside the assumption prefix.
///    The learned-clause harvest reads `is_assumption[m]`, an index past the
///    arrays sized to the entry `num_vars` (4). Before the guard this test
///    died at `assumptions.rs:693: index out of bounds: the len is 4 but the
///    index is 4`; with it the solve continues and fails a3.
struct MintingExtension {
    minted: Option<Variable>,
    stage: u8,
    /// Levels handed to `backtrack` after the mint: the backjumps into the
    /// assumption prefix are the configuration that puts a minted literal into
    /// a learned clause. Asserted so a trajectory change cannot silently turn
    /// this into a vacuous pass.
    backtracks: Vec<u32>,
}

impl MintingExtension {
    fn new() -> Self {
        Self {
            minted: None,
            stage: 0,
            backtracks: Vec::new(),
        }
    }
}

impl Extension for MintingExtension {
    fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
        ExtPropagateResult::none()
    }

    fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
        false
    }

    fn backtrack(&mut self, new_level: u32) {
        if self.minted.is_some() {
            self.backtracks.push(new_level);
        }
    }

    fn check(&mut self, ctx: &dyn SolverContext) -> ExtCheckResult {
        let (a1, a2, a3, y) = (
            Variable::new(0),
            Variable::new(1),
            Variable::new(2),
            Variable::new(3),
        );
        let Some(m) = self.minted else {
            let m = Variable::new(ctx.num_vars() as u32);
            self.minted = Some(m);
            return ExtCheckResult::AddClauses(vec![vec![
                Literal::negative(a1),
                Literal::positive(m),
            ]]);
        };
        assert_eq!(ctx.value(m), Some(true), "m is implied by a1");
        if self.stage == 0 {
            self.stage = 1;
            let y_true = ctx
                .value(y)
                .expect("y is assigned at a complete assignment");
            let not_y_now = if y_true {
                Literal::negative(y)
            } else {
                Literal::positive(y)
            };
            return ExtCheckResult::Conflict(vec![Literal::negative(m), not_y_now]);
        }
        if ctx.value(a2) == Some(true) && ctx.value(a3) == Some(true) {
            self.stage = 2;
            return ExtCheckResult::Conflict(vec![
                Literal::negative(m),
                Literal::negative(a2),
                Literal::negative(a3),
            ]);
        }
        ExtCheckResult::Sat
    }
}

/// t3: a minted variable propagated inside the assumption prefix and kept by a
/// learned clause must not panic the harvest, and the core stays inside the
/// assumptions.
#[test]
fn t3_minted_var_in_learned_clause_inside_assumption_prefix_does_not_panic() {
    // y appears in a clause a1 satisfies, so it is a plain don't-care the
    // solver still has to decide.
    let mut solver = session_solver(4, &[vec![pos(3), pos(0)]]);
    let assumptions = [pos(0), pos(1), pos(2)];
    let mut ext = MintingExtension::new();

    let result = solver.solve_with_extension_and_assumptions_core(
        &mut ext,
        &assumptions,
        None::<&fn() -> bool>,
    );

    assert_eq!(
        ext.stage, 2,
        "the third check never ran (result {result:?})"
    );
    assert!(
        ext.backtracks.iter().any(|&l| (1..=3).contains(&l)),
        "no backjump into the assumption prefix after the mint: backtracks {:?} \
         (result {result:?})",
        ext.backtracks
    );
    assert!(
        solver.num_conflicts() >= 3,
        "fewer conflicts than the trajectory needs: {}",
        solver.num_conflicts()
    );
    assert!(
        SolverContext::num_vars(&solver) >= 5,
        "the mint did not grow the solver: num_vars = {}",
        SolverContext::num_vars(&solver)
    );
    let core = result.unsat_core().unwrap_or_else(|| {
        panic!("a2 ∧ a3 ∧ (a1 → m) ∧ (¬m ∨ ¬a2 ∨ ¬a3) is Unsat, got {result:?}")
    });
    assert_core_subset(core, &assumptions);
}

/// Variables of t4: assumptions a1=0, a2=1, a3=2, a4=3 (a2 and a3 irrelevant);
/// q=4 is implied by a4 through (q ∨ ¬a4); p=5 is the theory atom the extension
/// derives from a1 (reason clause `[p, ¬a1]`) — nothing else mentions p
/// positively, so BCP cannot reach it first; r=6 closes the refutation through
/// (¬p ∨ ¬q ∨ ¬r) ∧ (¬p ∨ ¬q ∨ r), which become unit together the moment p is
/// set. The minimal core is {a1, a4}.
///
/// Observed (session profile):
/// - Eager: at level 4 the trail is a4, q, p (theory), r (BCP), conflict. 1UIP
///   resolves r, then p through its reason clause, learns (¬a1 ∨ ¬q), backjumps
///   to level 1 (`backtrack(1)`), ¬a4 follows, and the failed-assumption walk
///   names a1 and a4 — a strict subset. One analysis, nothing wasted.
/// - Lazy: the same conflict with p's reason a `LazyTheory` handle; see
///   [`lazy_reason`] for what the loop does with it.
struct ReasonExtension {
    lazy: bool,
    /// Whether `explain_lazy_reason` can rebuild the handle.
    explainable: bool,
    propagations: u32,
    /// `explain_lazy_reason` calls (lazy arm only): how often the solver
    /// materialised the handle.
    explains: u32,
    /// Theory conflicts reported from `propagate` (p already false).
    theory_conflicts: u32,
    /// Levels handed to `backtrack`, in order.
    backtracks: Vec<u32>,
}

impl ReasonExtension {
    fn new(lazy: bool) -> Self {
        Self {
            lazy,
            explainable: true,
            propagations: 0,
            explains: 0,
            theory_conflicts: 0,
            backtracks: Vec::new(),
        }
    }
}

impl ReasonExtension {
    const LAZY_HANDLE: u64 = 7;

    fn a1() -> Variable {
        Variable::new(0)
    }

    fn p() -> Variable {
        Variable::new(5)
    }

    fn reason_clause() -> Vec<Literal> {
        vec![Literal::positive(Self::p()), Literal::negative(Self::a1())]
    }
}

impl Extension for ReasonExtension {
    fn can_propagate(&self, ctx: &dyn SolverContext) -> bool {
        ctx.value(Self::a1()) == Some(true) && ctx.value(Self::p()) != Some(true)
    }

    fn propagate(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult {
        let mut out = ExtPropagateResult::none();
        if ctx.value(Self::a1()) != Some(true) {
            return out;
        }
        match ctx.value(Self::p()) {
            None => {
                self.propagations += 1;
                if self.lazy {
                    out.lazy_propagations
                        .push((Literal::positive(Self::p()), Self::LAZY_HANDLE));
                } else {
                    out.propagations
                        .push((Self::reason_clause(), Literal::positive(Self::p())));
                }
            }
            Some(false) => {
                self.theory_conflicts += 1;
                out.conflict = Some(Self::reason_clause());
            }
            Some(true) => {}
        }
        out
    }

    fn explain_lazy_reason(&mut self, propagated: Literal, data: u64) -> Option<Vec<Literal>> {
        self.explains += 1;
        (self.explainable
            && propagated == Literal::positive(Self::p())
            && data == Self::LAZY_HANDLE)
            .then(Self::reason_clause)
    }

    fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
        ExtCheckResult::Sat
    }

    fn backtrack(&mut self, new_level: u32) {
        self.backtracks.push(new_level);
    }
}

fn t4_solver() -> Solver {
    session_solver(
        7,
        &[
            vec![pos(4), neg(3)],
            vec![neg(5), neg(4), neg(6)],
            vec![neg(5), neg(4), pos(6)],
        ],
    )
}

fn t4_assumptions() -> [Literal; 4] {
    [pos(0), pos(1), pos(2), pos(3)]
}

/// t4a: an eager reason gives the strict-subset core.
#[test]
fn t4a_eager_reason_in_the_cone_yields_strict_subset_core() {
    let mut solver = t4_solver();
    let mut ext = ReasonExtension::new(false);
    let result = solver.solve_with_extension_and_assumptions_core(
        &mut ext,
        &t4_assumptions(),
        None::<&fn() -> bool>,
    );
    assert!(ext.propagations > 0, "the extension never propagated p");
    let core = result
        .unsat_core()
        .unwrap_or_else(|| panic!("expected Unsat, got {result:?}"));
    assert_core_subset(core, &t4_assumptions());
    assert!(
        !core.contains(&pos(1)) && !core.contains(&pos(2)),
        "eager reasons must give an exact core; got {core:?} (names a2 or a3)"
    );
    assert!(
        core.len() < t4_assumptions().len(),
        "eager core is not a strict subset: {core:?}"
    );
    assert!(
        !ext.backtracks.contains(&0),
        "an eager reason must never make the analysis bail to level 0: {:?}",
        ext.backtracks
    );
    assert_eq!(
        ext.theory_conflicts, 0,
        "the theory never had to re-explain p"
    );
}
