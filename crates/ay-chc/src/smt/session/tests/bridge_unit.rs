// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! WP-2 unit and end-to-end tests for `TheoryBridge` / `Minter` (design §8,
//! Rung 1: "per-literal alignment after backjump — the theory sees every
//! literal below a backjump exactly once; empty conflict → Poison; eager
//! reason clause shape; re-added split clause when all-false becomes a
//! pending conflict").
//!
//! Three layers:
//! 1. a recording mock `TheorySolver` (through the `cfg(test)`
//!    `TheoryBox::Mock` arm, C3 additive) driven by a fake `SolverContext`,
//!    for the bridge's own rules (alignment, filter, mapping, tiers);
//! 2. the same mock under the REAL ay-sat assumption loop, for the F6
//!    behaviour the design leans on (an all-false re-added clause is a
//!    pending conflict and the search moves);
//! 3. the real `LraSolver` under the real ay-sat loop through the bridge,
//!    with a harness that mirrors WP-1's allocation order and re-entry
//!    protocol (no WP-3 body needed): SAT with disequalities (tier 1), UNSAT
//!    with a core, the ITE-link tier-2 restart, and back-to-back queries.
//!
//! The `HornSmt::check_assuming` tests at the bottom run the whole session
//! (WP-1 core, this bridge, WP-3 conversion/model) end to end.

#![allow(clippy::panic, clippy::unwrap_used, clippy::expect_used)]

use std::cell::RefCell;
use std::collections::VecDeque;
use std::rc::Rc;
use std::sync::Arc;
use std::time::Duration;

use ay_core::kani_compat::DetHashSet as FxHashSet;
use ay_core::time::Instant;
use ay_core::{
    DisequalitySplitRequest, ExpressionSplitRequest, ModelEqualityRequest, Sort, Symbol, TermId,
    TheoryLit, TheoryPropagation, TheoryResult, TheorySolver, Tseitin, TseitinState,
};
use ay_sat::{
    AssumeResult, ExtCheckResult, Extension, Literal, SatUnknownReason, SolverContext, Variable,
};
use num_bigint::BigInt;
use num_rational::BigRational;

use super::super::ledger::{FarkasLedger, LedgerKind};
use super::super::theory_box::TheoryBox;
use super::super::{
    BudgetKind, HornCheck, HornSmt, PoisonKind, SessionConfig, UnknownReason, UnsupportedKind,
};
use super::{BridgeExit, BridgeParts, BridgeState, BridgeStats, TheoryBridge};
use crate::smt::model_verify::collect_theory_atoms_into;
use crate::smt::types::Partition;
use crate::smt::SmtContext;
use crate::{ChcExpr, ChcSort, ChcVar};

// ---------------------------------------------------------------------------
// Layer 1 helpers: recording mock theory, fake solver context, bridge parts
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum Ev {
    /// `assert_literal(term, value)` at theory scope `depth`.
    Assert(TermId, bool, usize),
    /// `push()` to depth.
    Push(usize),
    /// `pop()` from depth.
    Pop(usize),
    /// `check_during_propagate()` at depth (scope flushes and BCP-time checks).
    Bcp(usize),
}

#[derive(Default)]
struct MockInner {
    /// `scopes[d]` = literals asserted at theory scope `d` (scope 0 always exists).
    scopes: Vec<Vec<TheoryLit>>,
    log: Vec<Ev>,
    registered: Vec<TermId>,
    /// Scripted answers of `check()` (front first); `Sat` when empty and no rule fires.
    check_script: VecDeque<TheoryResult>,
    /// Scripted answers of `check_during_propagate()`; `Sat` when empty.
    bcp_script: VecDeque<TheoryResult>,
    /// Returned (drained) by the next `propagate()`.
    props: VecDeque<TheoryPropagation>,
    /// `explain_propagation(term, reason_data)` table.
    explain: Vec<((TermId, u64), Option<Vec<TheoryLit>>)>,
    rejected: Vec<(TermId, u64)>,
    check_calls: u32,
    /// `check()` answers `NeedExpressionSplit(eq)` while `eq` is asserted
    /// false and neither `lt` nor `gt` is asserted true.
    split_rule: Option<(TermId, TermId, TermId)>,
}

impl MockInner {
    fn depth(&self) -> usize {
        self.scopes.len() - 1
    }

    fn is_asserted(&self, t: TermId, v: bool) -> bool {
        self.scopes
            .iter()
            .any(|s| s.iter().any(|l| l.term == t && l.value == v))
    }

    fn assert_count(&self, t: TermId) -> usize {
        self.log
            .iter()
            .filter(|e| matches!(e, Ev::Assert(x, _, _) if *x == t))
            .count()
    }

    fn live_literals(&self) -> Vec<(TermId, bool)> {
        let mut v: Vec<(TermId, bool)> = self
            .scopes
            .iter()
            .flatten()
            .map(|l| (l.term, l.value))
            .collect();
        v.sort();
        v
    }
}

struct MockTheory(Rc<RefCell<MockInner>>);

fn new_mock() -> (TheoryBox, Rc<RefCell<MockInner>>) {
    let inner = Rc::new(RefCell::new(MockInner {
        scopes: vec![Vec::new()],
        ..MockInner::default()
    }));
    (
        TheoryBox::mock(Box::new(MockTheory(Rc::clone(&inner)))),
        inner,
    )
}

impl TheorySolver for MockTheory {
    fn register_atom(&mut self, atom: TermId) {
        self.0.borrow_mut().registered.push(atom);
    }

    fn assert_literal(&mut self, literal: TermId, value: bool) {
        let mut m = self.0.borrow_mut();
        let d = m.depth();
        m.scopes[d].push(TheoryLit::new(literal, value));
        m.log.push(Ev::Assert(literal, value, d));
    }

    fn check(&mut self) -> TheoryResult {
        let mut m = self.0.borrow_mut();
        m.check_calls += 1;
        if let Some(r) = m.check_script.pop_front() {
            return r;
        }
        if let Some((eq, lt, gt)) = m.split_rule {
            if m.is_asserted(eq, false) && !m.is_asserted(lt, true) && !m.is_asserted(gt, true) {
                return TheoryResult::NeedExpressionSplit(ExpressionSplitRequest {
                    disequality_term: eq,
                });
            }
        }
        TheoryResult::Sat
    }

    fn check_during_propagate(&mut self) -> TheoryResult {
        let mut m = self.0.borrow_mut();
        let d = m.depth();
        m.log.push(Ev::Bcp(d));
        m.bcp_script.pop_front().unwrap_or(TheoryResult::Sat)
    }

    fn needs_final_check_after_sat(&self) -> bool {
        true
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        self.0.borrow_mut().props.drain(..).collect()
    }

    fn has_pending_propagations(&self) -> bool {
        !self.0.borrow().props.is_empty()
    }

    fn push(&mut self) {
        let mut m = self.0.borrow_mut();
        m.scopes.push(Vec::new());
        let d = m.depth();
        m.log.push(Ev::Push(d));
    }

    fn pop(&mut self) {
        let mut m = self.0.borrow_mut();
        if m.scopes.len() > 1 {
            let d = m.depth();
            m.scopes.pop();
            m.log.push(Ev::Pop(d));
        }
    }

    fn reset(&mut self) {
        let mut m = self.0.borrow_mut();
        m.scopes = vec![Vec::new()];
        m.log.clear();
    }

    fn explain_propagation(&mut self, lit: TermId, reason_data: u64) -> Option<Vec<TheoryLit>> {
        self.0
            .borrow()
            .explain
            .iter()
            .find(|(k, _)| *k == (lit, reason_data))
            .and_then(|(_, v)| v.clone())
    }

    fn mark_propagation_rejected(&mut self, lit: TermId, reason_data: u64) {
        self.0.borrow_mut().rejected.push((lit, reason_data));
    }
}

/// A scripted `SolverContext`: a level-ordered trail with assignments.
struct FakeCtx {
    trail: Vec<Literal>,
    level_of: Vec<Option<u32>>,
    val: Vec<Option<bool>>,
    level: u32,
    conflicts: u64,
}

impl FakeCtx {
    fn new(num_vars: usize) -> Self {
        Self {
            trail: Vec::new(),
            level_of: vec![None; num_vars],
            val: vec![None; num_vars],
            level: 0,
            conflicts: 0,
        }
    }

    fn assign(&mut self, lit: Literal, level: u32) {
        let v = lit.variable().index();
        assert!(self.val[v].is_none(), "double assignment of {lit:?}");
        self.val[v] = Some(lit.is_positive());
        self.level_of[v] = Some(level);
        self.trail.push(lit);
        self.level = self.level.max(level);
    }

    /// Backjump to `level`: keep assignments at levels `<= level`.
    fn backjump(&mut self, level: u32) {
        let keep: Vec<Literal> = self
            .trail
            .iter()
            .copied()
            .filter(|l| self.level_of[l.variable().index()].is_some_and(|x| x <= level))
            .collect();
        for l in &self.trail {
            let v = l.variable().index();
            if self.level_of[v].is_some_and(|x| x > level) {
                self.val[v] = None;
                self.level_of[v] = None;
            }
        }
        self.trail = keep;
        self.level = level;
        self.conflicts += 1;
    }
}

impl SolverContext for FakeCtx {
    fn value(&self, var: Variable) -> Option<bool> {
        self.val.get(var.index()).copied().flatten()
    }
    fn decision_level(&self) -> u32 {
        self.level
    }
    fn var_level(&self, var: Variable) -> Option<u32> {
        self.level_of.get(var.index()).copied().flatten()
    }
    fn trail(&self) -> &[Literal] {
        &self.trail
    }
    fn num_vars(&self) -> usize {
        self.val.len()
    }
    fn conflicts(&self) -> u64 {
        self.conflicts
    }
}

/// Everything a bridge borrows, owned by the test.
struct Parts {
    own: Box<SmtContext>,
    theory: TheoryBox,
    tseitin: Option<TseitinState>,
    st: BridgeState,
    ledger: FarkasLedger,
    cfg: SessionConfig,
}

impl Parts {
    fn with_theory(theory: TheoryBox) -> Self {
        Self {
            own: Box::new(SmtContext::new()),
            theory,
            tseitin: Some(TseitinState::new()),
            st: BridgeState::default(),
            ledger: FarkasLedger::new(4096),
            cfg: SessionConfig::default(),
        }
    }

    fn bridge<'s>(
        &'s mut self,
        deadline: Option<Instant>,
        should_stop: &'s dyn Fn() -> bool,
    ) -> TheoryBridge<'s> {
        TheoryBridge::new(BridgeParts {
            theory: &mut self.theory,
            own: &mut self.own,
            tseitin: &mut self.tseitin,
            st: &mut self.st,
            ledger: &mut self.ledger,
            epoch: 1,
            cfg: &self.cfg,
            deadline,
            should_stop,
            phase_seed: None,
        })
    }

    fn real_var(&mut self, name: &str) -> TermId {
        self.own.terms.mk_var(name, Sort::Real)
    }

    fn rat(&mut self, n: i64) -> TermId {
        self.own
            .terms
            .mk_rational(BigRational::from_integer(BigInt::from(n)))
    }

    /// Give each atom a SAT variable (in order, DIMACS 1..) and enter it in the
    /// bridge tables as an ACTIVE, registered assertion atom. Returns the vars.
    fn name_atoms(&mut self, atoms: &[TermId]) -> Vec<Variable> {
        let state = self.tseitin.take().unwrap();
        let mut ts = Tseitin::from_state(&self.own.terms, state);
        let mut vars = Vec::new();
        for &a in atoms {
            let c = ts.encode(a, true);
            assert!(c > 0, "atoms are encoded positively");
            vars.push(Variable::new(c as u32 - 1));
        }
        assert!(
            ts.take_new_clauses().is_empty(),
            "plain atoms have no definitions"
        );
        let state = ts.into_state();
        self.tseitin = Some(state);
        let n = vars.iter().map(|v| v.index() + 1).max().unwrap_or(0);
        self.st.grow(n);
        for (&a, v) in atoms.iter().zip(&vars) {
            self.st.atom_of_var[v.index()] = Some(a);
            self.st.active_atom[v.index()] = true;
            self.st.registered[v.index()] = true;
        }
        vars
    }
}

fn pos(v: Variable) -> Literal {
    Literal::positive(v)
}

fn neg(v: Variable) -> Literal {
    Literal::negative(v)
}

fn never() -> bool {
    false
}

/// Four atoms `x<=0, y<=0, x<=1, y<=1` plus two more `x<=2, y<=2`, a mock
/// theory, and a fake context sized for them.
struct MockRig {
    parts: Parts,
    mock: Rc<RefCell<MockInner>>,
    atoms: Vec<TermId>,
    vars: Vec<Variable>,
}

fn mock_rig() -> MockRig {
    let (theory, mock) = new_mock();
    let mut parts = Parts::with_theory(theory);
    let x = parts.real_var("x");
    let y = parts.real_var("y");
    let c0 = parts.rat(0);
    let c1 = parts.rat(1);
    let c2 = parts.rat(2);
    let atoms = vec![
        parts.own.terms.mk_le(x, c0),
        parts.own.terms.mk_le(y, c0),
        parts.own.terms.mk_le(x, c1),
        parts.own.terms.mk_le(y, c1),
        parts.own.terms.mk_le(x, c2),
        parts.own.terms.mk_le(y, c2),
    ];
    let vars = parts.name_atoms(&atoms);
    MockRig {
        parts,
        mock,
        atoms,
        vars,
    }
}

// ---------------------------------------------------------------------------
// Layer 1: alignment, filter, mapping
// ---------------------------------------------------------------------------

#[test]
fn per_literal_alignment_refeeds_only_the_popped_suffix() {
    let mut rig = mock_rig();
    let (a, b, c, d, e, f) = (
        rig.atoms[0],
        rig.atoms[1],
        rig.atoms[2],
        rig.atoms[3],
        rig.atoms[4],
        rig.atoms[5],
    );
    let v = rig.vars.clone();
    let mut ctx = FakeCtx::new(8);
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();

    // Trail: a@1 b@1 c@2 d@3 (positions 0..4).
    ctx.assign(pos(v[0]), 1);
    ctx.assign(neg(v[1]), 1);
    ctx.assign(pos(v[2]), 2);
    ctx.assign(pos(v[3]), 3);
    assert!(bridge.can_propagate(&ctx));
    let out = bridge.propagate(&ctx);
    assert!(out.conflict.is_none() && !out.stop);
    assert_eq!(bridge.theory_level(), 3);
    assert_eq!(
        bridge.level_cursor,
        vec![0, 2, 3],
        "pre-feed cursor per scope"
    );
    assert_eq!(bridge.last_trail_pos, 4);
    assert!(!bridge.can_propagate(&ctx), "nothing new on the trail");
    assert_eq!(rig.mock.borrow().log, initial_feed_log([a, b, c, d]));

    // Backjump to level 1: scopes 3 and 2 popped, cursor restored to c's position.
    bridge.backtrack(1);
    assert_eq!(bridge.theory_level(), 1);
    assert_eq!(bridge.last_trail_pos, 2);
    ctx.backjump(1);
    assert!(
        !bridge.can_propagate(&ctx),
        "the surviving prefix is already fed"
    );

    // New assignments after the backjump: e@1 (a learned unit at the
    // backjump level) and f@2.
    ctx.assign(pos(v[4]), 1);
    ctx.assign(neg(v[5]), 2);
    let _ = bridge.propagate(&ctx);
    let m = rig.mock.borrow();
    // Every literal below the backjump was fed exactly once; the popped ones
    // once (then popped); the new ones once at their own scope.
    for t in [a, b, c, d, e, f] {
        assert_eq!(m.assert_count(t), 1, "{t:?} fed exactly once");
    }
    assert_eq!(
        m.live_literals(),
        {
            let mut w = vec![(a, true), (b, false), (e, true), (f, false)];
            w.sort();
            w
        },
        "theory scopes mirror the SAT trail after the backjump"
    );
    assert_eq!(m.scopes[1].len(), 3, "a, b, e at scope 1");
    assert_eq!(m.scopes[2], vec![TheoryLit::new(f, false)]);
    assert_eq!(bridge.stats().theory_pushes, 4);
    assert_eq!(bridge.stats().theory_pops, 2);
    assert_eq!(bridge.stats().fed_literals, 6);
    assert_eq!(
        bridge.stats().scope_flushes,
        3,
        "before scopes 2, 3 and the re-opened 2"
    );
    assert_eq!(m.log[10..], refeed_after_backjump_log(e, f)[..]);
}

/// The mock's log after `per_literal_alignment_refeeds_only_the_popped_suffix`
/// feeds a@1 b@1 c@2 d@3. The theory is flushed (a BCP-time check) before
/// every new scope that follows fed literals, and once more by `propagate`
/// itself.
fn initial_feed_log([a, b, c, d]: [TermId; 4]) -> Vec<Ev> {
    vec![
        Ev::Push(1),
        Ev::Assert(a, true, 1),
        Ev::Assert(b, false, 1),
        Ev::Bcp(1),
        Ev::Push(2),
        Ev::Assert(c, true, 2),
        Ev::Bcp(2),
        Ev::Push(3),
        Ev::Assert(d, true, 3),
        Ev::Bcp(3),
    ]
}

/// What the same test's backjump to level 1 appends: scopes 3 and 2 popped,
/// then e@1 fed into the surviving scope and f@2 into a re-opened one.
fn refeed_after_backjump_log(e: TermId, f: TermId) -> Vec<Ev> {
    vec![
        Ev::Pop(3),
        Ev::Pop(2),
        Ev::Assert(e, true, 1),
        Ev::Bcp(1),
        Ev::Push(2),
        Ev::Assert(f, false, 2),
        Ev::Bcp(2),
    ]
}

#[test]
fn a_scope_flush_conflict_stops_the_feed_and_is_returned() {
    let mut rig = mock_rig();
    let (a, b, c) = (rig.atoms[0], rig.atoms[1], rig.atoms[2]);
    let v = rig.vars.clone();
    let mut ctx = FakeCtx::new(8);
    ctx.assign(pos(v[0]), 1);
    ctx.assign(pos(v[1]), 2);
    ctx.assign(pos(v[2]), 3);
    // The flush before scope 3 (after a@1, b@2 were fed) reports a conflict
    // over a and b; c is NOT fed, and the conflict comes back from propagate.
    {
        let mut m = rig.mock.borrow_mut();
        m.bcp_script.push_back(TheoryResult::Sat); // flush before scope 2
        m.bcp_script.push_back(TheoryResult::Unsat(vec![
            TheoryLit::new(a, true),
            TheoryLit::new(b, true),
        ])); // flush before scope 3
    }
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    let out = bridge.propagate(&ctx);
    assert_eq!(out.conflict, Some(vec![neg(v[0]), neg(v[1])]));
    assert_eq!(bridge.theory_level(), 2);
    assert_eq!(
        bridge.last_trail_pos, 2,
        "c's position is re-fed after the backjump"
    );
    assert_eq!(bridge.stats().scope_flush_conflicts, 1);
    assert_eq!(bridge.stats().bcp_conflicts, 1);
    assert_eq!(rig.mock.borrow().assert_count(c), 0);
    // The backjump, then the re-feed of the tail.
    bridge.backtrack(1);
    ctx.backjump(1);
    ctx.assign(neg(v[1]), 1);
    let out = bridge.propagate(&ctx);
    assert!(out.conflict.is_none());
    assert_eq!(rig.mock.borrow().assert_count(b), 2);
}

#[test]
fn level_zero_facts_are_fed_once_per_session_and_never_popped() {
    let mut rig = mock_rig();
    let (a, b) = (rig.atoms[0], rig.atoms[1]);
    let v = rig.vars.clone();
    let mut ctx = FakeCtx::new(8);
    ctx.assign(pos(v[0]), 0);
    ctx.assign(pos(v[1]), 1);

    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    let _ = bridge.propagate(&ctx);
    assert_eq!(bridge.stats().l0_feeds, 1);
    assert_eq!(
        rig.mock.borrow().log[..3],
        [Ev::Assert(a, true, 0), Ev::Bcp(0), Ev::Push(1)],
        "the level-0 fact is flushed at scope 0 before scope 1 opens"
    );
    // The guard's job at the end of a query.
    bridge.backtrack(0);
    assert_eq!(bridge.theory_level(), 0);
    drop(bridge);
    {
        let m = rig.mock.borrow();
        assert_eq!(m.scopes.len(), 1);
        assert_eq!(
            m.scopes[0],
            vec![TheoryLit::new(a, true)],
            "the level-0 fact stays"
        );
    }

    // Next query: a fresh bridge over the persistent state; the incremental
    // reset kept the level-0 trail, and `b` is assumed again.
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    let _ = bridge.propagate(&ctx);
    let m = rig.mock.borrow();
    assert_eq!(m.assert_count(a), 1, "level-0 fact never re-fed");
    assert_eq!(m.assert_count(b), 2, "the assumed atom is fed per query");
    assert_eq!(bridge.stats().l0_feeds, 0);
}

#[test]
fn dont_care_filter_feeds_only_active_atoms() {
    let mut rig = mock_rig();
    let (a, b) = (rig.atoms[0], rig.atoms[1]);
    let v = rig.vars.clone();
    rig.parts.st.active_atom[v[1].index()] = false;
    let mut ctx = FakeCtx::new(8);
    ctx.assign(pos(v[0]), 1);
    ctx.assign(pos(v[1]), 1);
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    let _ = bridge.propagate(&ctx);
    // `suggest_phase` and `on_restart` see the same filter.
    assert_eq!(bridge.on_restart(), vec![v[0], v[2], v[3], v[4], v[5]]);
    let m = rig.mock.borrow();
    assert_eq!(m.assert_count(a), 1);
    assert_eq!(m.assert_count(b), 0, "inactive atoms are never fed");
}

#[test]
fn empty_theory_conflict_is_poison_never_a_clause() {
    let mut rig = mock_rig();
    let v = rig.vars.clone();
    let mut ctx = FakeCtx::new(8);
    ctx.assign(pos(v[0]), 1);
    rig.mock
        .borrow_mut()
        .check_script
        .push_back(TheoryResult::Unsat(Vec::new()));
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    assert!(matches!(bridge.check(&ctx), ExtCheckResult::Unknown));
    assert_eq!(
        bridge.exit(),
        BridgeExit::Poison(PoisonKind::EmptyTheoryConflict)
    );
    // Same at BCP time: `stop`, never `conflict: Some(vec![])`.
    rig.mock
        .borrow_mut()
        .bcp_script
        .push_back(TheoryResult::Unsat(Vec::new()));
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    let out = bridge.propagate(&ctx);
    assert!(out.stop && out.conflict.is_none());
    assert_eq!(
        bridge.exit(),
        BridgeExit::Poison(PoisonKind::EmptyTheoryConflict)
    );
    assert!(rig.parts.ledger.is_empty());
}

#[test]
fn bcp_conflict_is_the_negated_clause_and_is_recorded() {
    let mut rig = mock_rig();
    let (a, b) = (rig.atoms[0], rig.atoms[1]);
    let v = rig.vars.clone();
    let mut ctx = FakeCtx::new(8);
    ctx.assign(pos(v[0]), 1);
    ctx.assign(neg(v[1]), 2);
    rig.mock
        .borrow_mut()
        .bcp_script
        .push_back(TheoryResult::Unsat(vec![
            TheoryLit::new(a, true),
            TheoryLit::new(b, false),
        ]));
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    let out = bridge.propagate(&ctx);
    assert_eq!(out.conflict, Some(vec![neg(v[0]), pos(v[1])]));
    assert_eq!(out.bump_vars, vec![v[0], v[1]]);
    assert!(!out.stop);
    assert_eq!(bridge.exit(), BridgeExit::None);
    assert_eq!(bridge.stats().bcp_conflicts, 1);
    drop(bridge);
    let entries: Vec<_> = rig.parts.ledger.entries().collect();
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[0].kind, LedgerKind::Conflict);
    assert!(entries[0].at_bcp);
    assert_eq!(entries[0].clause, vec![neg(v[0]), pos(v[1])]);
    assert_eq!(entries[0].epoch, 1);
}

#[test]
fn conflict_over_an_unassigned_or_unmapped_atom_fails_closed() {
    let mut rig = mock_rig();
    let (a, c) = (rig.atoms[0], rig.atoms[2]);
    let v = rig.vars.clone();
    let mut ctx = FakeCtx::new(8);
    ctx.assign(pos(v[0]), 1);
    // `c` is unassigned: its negation would not be a falsified literal.
    rig.mock
        .borrow_mut()
        .check_script
        .push_back(TheoryResult::Unsat(vec![
            TheoryLit::new(a, true),
            TheoryLit::new(c, true),
        ]));
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    assert!(matches!(bridge.check(&ctx), ExtCheckResult::Unknown));
    assert_eq!(bridge.exit(), BridgeExit::TheoryIncomplete);
    assert_eq!(bridge.stats().non_falsified_conflicts, 1);
    drop(bridge);

    // An atom the encoder never named.
    let z = rig.parts.real_var("z");
    let c9 = rig.parts.rat(9);
    let ghost = rig.parts.own.terms.mk_le(z, c9);
    rig.mock
        .borrow_mut()
        .check_script
        .push_back(TheoryResult::Unsat(vec![
            TheoryLit::new(a, true),
            TheoryLit::new(ghost, true),
        ]));
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    assert!(matches!(bridge.check(&ctx), ExtCheckResult::Unknown));
    assert_eq!(bridge.exit(), BridgeExit::TheoryIncomplete);
    assert_eq!(bridge.stats().unmapped_conflicts, 1);
}

#[test]
fn eager_reason_clause_shape_and_lazy_materialisation() {
    let mut rig = mock_rig();
    let (a, b, c, d, e) = (
        rig.atoms[0],
        rig.atoms[1],
        rig.atoms[2],
        rig.atoms[3],
        rig.atoms[4],
    );
    let v = rig.vars.clone();
    let mut ctx = FakeCtx::new(8);
    ctx.assign(pos(v[0]), 1);
    ctx.assign(neg(v[1]), 1);
    let z = rig.parts.real_var("z");
    let c9 = rig.parts.rat(9);
    let ghost = rig.parts.own.terms.mk_le(z, c9);
    {
        let mut m = rig.mock.borrow_mut();
        // Eager: c <- a ∧ ¬b.
        m.props.push_back(TheoryPropagation::eager(
            TheoryLit::new(c, true),
            vec![TheoryLit::new(a, true), TheoryLit::new(b, false)],
        ));
        // Lazy, explainable: ¬d <- a.
        m.props
            .push_back(TheoryPropagation::lazy(TheoryLit::new(d, false), 42));
        m.explain
            .push(((d, 42), Some(vec![TheoryLit::new(a, true)])));
        // Lazy, unexplainable: dropped and rejected back to the theory.
        m.props
            .push_back(TheoryPropagation::lazy(TheoryLit::new(e, true), 7));
        m.explain.push(((e, 7), None));
        // Eager with an unmapped reason atom: dropped.
        m.props.push_back(TheoryPropagation::eager(
            TheoryLit::new(e, true),
            vec![TheoryLit::new(ghost, true)],
        ));
        // Eager with a target the encoder never named: dropped.
        m.props.push_back(TheoryPropagation::eager(
            TheoryLit::new(ghost, true),
            vec![TheoryLit::new(a, true)],
        ));
        // Redundant (target already true): skipped silently.
        m.props.push_back(TheoryPropagation::eager(
            TheoryLit::new(a, true),
            vec![TheoryLit::new(b, false)],
        ));
    }
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    let out = bridge.propagate(&ctx);
    assert!(out.lazy_propagations.is_empty(), "never lazy");
    assert!(out.clauses.is_empty() && out.conflict.is_none());
    assert_eq!(
        out.propagations,
        vec![
            (vec![pos(v[2]), neg(v[0]), pos(v[1])], pos(v[2])),
            (vec![neg(v[3]), neg(v[0])], neg(v[3])),
        ],
        "reason_clause = [lit, ¬r1, …, ¬rk] with the propagated literal first"
    );
    assert_eq!(bridge.stats().propagations, 2);
    assert_eq!(bridge.stats().dropped_propagations, 3);
    assert_eq!(rig.mock.borrow().rejected, vec![(e, 7)]);
    drop(bridge);
    let entries: Vec<_> = rig.parts.ledger.entries().collect();
    assert_eq!(entries.len(), 2);
    assert!(entries
        .iter()
        .all(|e| e.kind == LedgerKind::Propagation && e.at_bcp));
    assert_eq!(
        entries[0].lits,
        vec![
            TheoryLit::new(a, true),
            TheoryLit::new(b, false),
            TheoryLit::new(c, false)
        ],
        "reason ∪ {{¬propagated}}"
    );
}

#[test]
fn propagation_of_an_already_false_target_is_a_conflict() {
    let mut rig = mock_rig();
    let (a, c) = (rig.atoms[0], rig.atoms[2]);
    let v = rig.vars.clone();
    let mut ctx = FakeCtx::new(8);
    ctx.assign(pos(v[0]), 1);
    ctx.assign(neg(v[2]), 2);
    rig.mock
        .borrow_mut()
        .props
        .push_back(TheoryPropagation::eager(
            TheoryLit::new(c, true),
            vec![TheoryLit::new(a, true)],
        ));
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    let out = bridge.propagate(&ctx);
    assert_eq!(out.conflict, Some(vec![pos(v[2]), neg(v[0])]));
    assert_eq!(
        out.propagations,
        [] as [(std::vec::Vec<ay_sat::Literal>, ay_sat::Literal); 0]
    );
    assert_eq!(bridge.stats().propagation_conflicts, 1);
}

#[test]
fn stop_predicate_and_deadline_end_the_solve_as_budget() {
    let mut rig = mock_rig();
    let v = rig.vars.clone();
    let mut ctx = FakeCtx::new(8);
    ctx.assign(pos(v[0]), 1);
    let always = || true;
    let mut bridge = rig.parts.bridge(None, &always);
    bridge.init();
    let out = bridge.propagate(&ctx);
    assert!(out.stop);
    assert_eq!(bridge.exit(), BridgeExit::Budget(BudgetKind::Interrupted));
    assert_eq!(
        rig.mock.borrow().assert_count(rig.atoms[0]),
        0,
        "nothing fed after a stop"
    );
    drop(bridge);

    let past = Instant::now()
        .checked_sub(Duration::from_millis(1))
        .expect("fixture instant supports a one-millisecond offset");
    let mut bridge = rig.parts.bridge(Some(past), &never);
    bridge.init();
    assert!(matches!(bridge.check(&ctx), ExtCheckResult::Unknown));
    assert_eq!(bridge.exit(), BridgeExit::Budget(BudgetKind::Deadline));
    assert_eq!(bridge.stats().deadline_stops, 1);
}

#[test]
fn init_pops_the_theory_to_scope_zero_for_a_reentered_solve() {
    let mut rig = mock_rig();
    let (a, b) = (rig.atoms[0], rig.atoms[1]);
    let v = rig.vars.clone();
    let mut ctx = FakeCtx::new(8);
    ctx.assign(pos(v[0]), 1);
    ctx.assign(pos(v[1]), 2);
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    let _ = bridge.propagate(&ctx);
    assert_eq!(bridge.theory_level(), 2);
    // A re-entered solve (§4.2): ay-sat reset its trail to level 0 without
    // an `ext.backtrack`; the same bridge is initialised again.
    bridge.init();
    assert_eq!(bridge.exit(), BridgeExit::None);
    assert_eq!(bridge.theory_level(), 0);
    assert_eq!(bridge.stats().init_pops, 1);
    assert_eq!(bridge.stats().theory_pops, 2);
    assert_eq!(rig.mock.borrow().scopes.len(), 1, "theory at scope 0");
    // The whole (kept) trail is fed again from position 0.
    let _ = bridge.propagate(&ctx);
    let m = rig.mock.borrow();
    assert_eq!(m.assert_count(a), 2);
    assert_eq!(m.assert_count(b), 2);
    assert_eq!(m.scopes.len(), 3);
}

// ---------------------------------------------------------------------------
// Layer 1: minting (tiers, dedup, convergence, caps)
// ---------------------------------------------------------------------------

/// `x`, `y`, `eq = (= x y)`, with `eq` named as an (active) assertion atom.
struct SplitRig {
    parts: Parts,
    mock: Rc<RefCell<MockInner>>,
    x: TermId,
    y: TermId,
    eq: TermId,
    eq_var: Variable,
}

fn split_rig() -> SplitRig {
    let (theory, mock) = new_mock();
    let mut parts = Parts::with_theory(theory);
    let x = parts.real_var("x");
    let y = parts.real_var("y");
    let eq = parts.own.terms.mk_eq(x, y);
    let vars = parts.name_atoms(&[eq]);
    SplitRig {
        parts,
        mock,
        x,
        y,
        eq,
        eq_var: vars[0],
    }
}

#[test]
fn expression_split_mints_guarded_clause_inline_and_re_adds_it() {
    let mut rig = split_rig();
    let mut ctx = FakeCtx::new(1);
    ctx.assign(neg(rig.eq_var), 1);
    rig.mock
        .borrow_mut()
        .check_script
        .push_back(TheoryResult::NeedExpressionSplit(ExpressionSplitRequest {
            disequality_term: rig.eq,
        }));
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    let ExtCheckResult::AddClauses(clauses) = bridge.check(&ctx) else {
        panic!("expected AddClauses, exit {:?}", bridge.exit());
    };
    let stats = bridge.stats().clone();
    let mint_count = bridge.mint_count();
    assert!(bridge.take_originals().is_empty(), "tier 1 buffers nothing");
    drop(bridge);
    let lt = rig.parts.own.terms.mk_lt(rig.x, rig.y);
    let gt = rig.parts.own.terms.mk_gt(rig.x, rig.y);
    let ts = rig.parts.tseitin.as_ref().unwrap();
    let lt_var = Variable::new(ts.term_to_var[&lt] - 1);
    let gt_var = Variable::new(ts.term_to_var[&gt] - 1);
    assert_eq!(
        lt_var.index(),
        1,
        "first fresh var right above the solver's"
    );
    assert_eq!(gt_var.index(), 2);
    assert_eq!(
        clauses,
        vec![vec![pos(rig.eq_var), pos(lt_var), pos(gt_var)]]
    );
    assert_eq!(stats.minted_atoms, 2);
    assert_eq!(stats.mints_expr, 1);
    assert_eq!(mint_count, 1);
    // Tables and theory registration happened before the batch returned.
    assert_eq!(rig.parts.st.atom_of_var[1], Some(lt));
    assert_eq!(rig.parts.st.atom_of_var[2], Some(gt));
    assert!(rig.parts.st.active_atom[1] && rig.parts.st.active_atom[2]);
    assert!(rig.parts.st.registered[1] && rig.parts.st.registered[2]);
    assert_eq!(rig.parts.st.mint_parent[1], rig.eq_var.index() as u32);
    assert_eq!(rig.parts.st.minted_vars, vec![1, 2]);
    assert_eq!(rig.mock.borrow().registered, vec![lt, gt]);

    // The same request again with the split atoms now assigned FALSE (the
    // clause was dropped by the deletable tier): atoms are deduplicated, the
    // clause is re-added unchanged — all-false, so ay-sat parks it as a
    // pending conflict (F6; layer-2 test below observes the search moving).
    let mut ctx = FakeCtx::new(3);
    ctx.assign(neg(rig.eq_var), 1);
    ctx.assign(neg(lt_var), 2);
    ctx.assign(neg(gt_var), 3);
    rig.mock
        .borrow_mut()
        .check_script
        .push_back(TheoryResult::NeedExpressionSplit(ExpressionSplitRequest {
            disequality_term: rig.eq,
        }));
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    let ExtCheckResult::AddClauses(clauses) = bridge.check(&ctx) else {
        panic!("expected AddClauses, exit {:?}", bridge.exit());
    };
    assert_eq!(
        clauses,
        vec![vec![pos(rig.eq_var), pos(lt_var), pos(gt_var)]]
    );
    assert_eq!(bridge.stats().minted_atoms, 0, "atom-only dedup");
    drop(bridge);
    assert_eq!(rig.parts.st.minted_vars, vec![1, 2], "no re-registration");
}

#[test]
fn split_under_not_and_distinct_guards_have_the_documented_polarity() {
    // `(not (= x y))` as the request term: the guard is still `+eq`.
    let mut rig = split_rig();
    let not_eq = rig.parts.own.terms.mk_not(rig.eq);
    let mut ctx = FakeCtx::new(1);
    ctx.assign(neg(rig.eq_var), 1);
    rig.mock
        .borrow_mut()
        .check_script
        .push_back(TheoryResult::NeedExpressionSplit(ExpressionSplitRequest {
            disequality_term: not_eq,
        }));
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    let ExtCheckResult::AddClauses(clauses) = bridge.check(&ctx) else {
        panic!("expected AddClauses, exit {:?}", bridge.exit());
    };
    assert_eq!(clauses[0][0], pos(rig.eq_var));
    drop(bridge);

    // `(distinct x y)` as an assertion atom: guard `¬distinct`. (`mk_distinct`
    // normalises a binary distinct to `not (= ..)`, so the raw app is built.)
    let (theory, mock) = new_mock();
    let mut parts = Parts::with_theory(theory);
    let x = parts.real_var("x");
    let y = parts.real_var("y");
    let one = parts.rat(1);
    let d = parts
        .own
        .terms
        .mk_app(Symbol::named("distinct"), [x, y], Sort::Bool);
    let vars = parts.name_atoms(&[d]);
    let mut ctx = FakeCtx::new(1);
    ctx.assign(pos(vars[0]), 1);
    mock.borrow_mut()
        .check_script
        .push_back(TheoryResult::NeedDisequalitySplit(
            DisequalitySplitRequest {
                variable: x,
                excluded_value: BigRational::from_integer(BigInt::from(1)),
                disequality_term: Some(d),
                is_distinct: true,
            },
        ));
    let mut bridge = parts.bridge(None, &never);
    bridge.init();
    let ExtCheckResult::AddClauses(clauses) = bridge.check(&ctx) else {
        panic!("expected AddClauses, exit {:?}", bridge.exit());
    };
    assert_eq!(clauses.len(), 1);
    assert_eq!(clauses[0][0], neg(vars[0]));
    assert_eq!(bridge.stats().mints_diseq, 1);
    drop(bridge);
    let lt = parts.own.terms.mk_lt(x, one);
    let gt = parts.own.terms.mk_gt(x, one);
    let ts = parts.tseitin.as_ref().unwrap();
    assert!(ts.term_to_var.contains_key(&lt) && ts.term_to_var.contains_key(&gt));
}

#[test]
fn disequality_without_a_term_is_unsupported() {
    let mut rig = split_rig();
    let mut ctx = FakeCtx::new(1);
    ctx.assign(neg(rig.eq_var), 1);
    rig.mock
        .borrow_mut()
        .check_script
        .push_back(TheoryResult::NeedDisequalitySplit(
            DisequalitySplitRequest {
                variable: rig.x,
                excluded_value: BigRational::from_integer(BigInt::from(0)),
                disequality_term: None,
                is_distinct: false,
            },
        ));
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    assert!(matches!(bridge.check(&ctx), ExtCheckResult::Unknown));
    assert_eq!(
        bridge.exit(),
        BridgeExit::Unsupported(UnsupportedKind::DisequalityWithoutTerm)
    );
}

#[test]
fn same_request_with_unchanged_state_trips_after_three() {
    let mut rig = split_rig();
    let mut ctx = FakeCtx::new(1);
    ctx.assign(neg(rig.eq_var), 1);
    for _ in 0..3 {
        rig.mock
            .borrow_mut()
            .check_script
            .push_back(TheoryResult::NeedExpressionSplit(ExpressionSplitRequest {
                disequality_term: rig.eq,
            }));
    }
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    assert!(matches!(bridge.check(&ctx), ExtCheckResult::AddClauses(_)));
    assert!(matches!(bridge.check(&ctx), ExtCheckResult::AddClauses(_)));
    assert!(matches!(bridge.check(&ctx), ExtCheckResult::Unknown));
    assert_eq!(bridge.exit(), BridgeExit::TheoryIncomplete);
    assert_eq!(bridge.stats().tripwire_trips, 1);
}

#[test]
fn implied_model_equality_is_tier_two_and_restarts_with_originals() {
    let mut rig = mock_rig();
    let a = rig.atoms[0];
    let v = rig.vars.clone();
    let mut ctx = FakeCtx::new(8);
    ctx.assign(pos(v[0]), 1);
    let x = rig.parts.real_var("x");
    let y = rig.parts.real_var("y");
    let req = || ModelEqualityRequest {
        lhs: x,
        rhs: y,
        reason: vec![TheoryLit::new(a, true)],
        implied: true,
    };
    rig.mock
        .borrow_mut()
        .check_script
        .push_back(TheoryResult::NeedModelEquality(req()));
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    // Tier 2: the clauses come back inline TOO (so ay-sat grows for the fresh
    // variables) and the exit ends the solve at the next propagate.
    let ExtCheckResult::AddClauses(inline) = bridge.check(&ctx) else {
        panic!(
            "expected AddClauses carrying the originals, exit {:?}",
            bridge.exit()
        );
    };
    assert_eq!(bridge.exit(), BridgeExit::RestartWithOriginals);
    assert!(bridge.can_propagate(&ctx));
    assert!(
        bridge.propagate(&ctx).stop,
        "the next propagate stops the solve"
    );
    let originals = bridge.take_originals();
    assert_eq!(inline, originals, "the inline copy IS the originals batch");
    assert!(bridge.take_originals().is_empty(), "drained");
    assert_eq!(bridge.stats().originals_restarts, 1);
    assert_eq!(bridge.stats().mints_model_eq, 1);
    drop(bridge);
    // The `=` term is the hash-consed app LRA's `find_eq` gate looks up.
    let eq = rig.parts.own.terms.find_eq(x, y).expect("eq minted");
    let ts = rig.parts.tseitin.as_ref().unwrap();
    let eq_var = Variable::new(ts.term_to_var[&eq] - 1);
    assert_eq!(eq_var.index(), 8, "minted right above the solver's vars");
    assert_eq!(
        originals,
        vec![vec![neg(v[0]), pos(eq_var)]],
        "[¬reason, +eq]"
    );
    assert_eq!(rig.mock.borrow().registered, vec![eq]);
    assert_eq!(
        rig.parts.st.mint_parent[8],
        super::super::minting::MINT_ALWAYS_ACTIVE
    );
    assert!(rig.parts.st.active_atom[8]);

    // Re-entered solve, same pair requested again: the gate failed; no
    // progress is possible.
    rig.mock
        .borrow_mut()
        .check_script
        .push_back(TheoryResult::NeedModelEquality(req()));
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    // Same-query semantics live in the bridge: mark the pair as answered.
    bridge.mint.seen_model_eq.insert((x.min(y), x.max(y)));
    assert!(matches!(bridge.check(&ctx), ExtCheckResult::Unknown));
    assert_eq!(bridge.exit(), BridgeExit::TheoryIncomplete);
    assert_eq!(
        bridge.take_originals(),
        [] as [std::vec::Vec<ay_sat::Literal>; 0]
    );
}

#[test]
fn compound_reason_atom_brings_its_definitions_as_originals() {
    let mut rig = mock_rig();
    let (a, b) = (rig.atoms[0], rig.atoms[1]);
    let v = rig.vars.clone();
    let mut ctx = FakeCtx::new(8);
    ctx.assign(pos(v[0]), 1);
    ctx.assign(pos(v[1]), 1);
    let x = rig.parts.real_var("x");
    let y = rig.parts.real_var("y");
    let cond = rig.parts.own.terms.mk_and(vec![a, b]);
    rig.mock
        .borrow_mut()
        .check_script
        .push_back(TheoryResult::NeedModelEquality(ModelEqualityRequest {
            lhs: x,
            rhs: y,
            reason: vec![TheoryLit::new(cond, true)],
            implied: true,
        }));
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    assert!(matches!(bridge.check(&ctx), ExtCheckResult::AddClauses(_)));
    assert_eq!(bridge.exit(), BridgeExit::RestartWithOriginals);
    let originals = bridge.take_originals();
    drop(bridge);
    let ts = rig.parts.tseitin.as_ref().unwrap();
    let eq = rig.parts.own.terms.find_eq(x, y).unwrap();
    let eq_var = Variable::new(ts.term_to_var[&eq] - 1);
    let and_var = Variable::new(ts.term_to_var[&cond] - 1);
    // Three definition clauses of `and` (full equivalence) plus the link.
    assert_eq!(originals.len(), 4, "{originals:?}");
    assert!(originals.contains(&vec![neg(and_var), pos(v[0])]));
    assert!(originals.contains(&vec![neg(and_var), pos(v[1])]));
    assert_eq!(originals[3], vec![neg(and_var), pos(eq_var)]);
    // The compound is not a theory atom: never registered, never fed.
    assert_eq!(rig.parts.st.atom_of_var[and_var.index()], None);
    assert_eq!(rig.mock.borrow().registered, vec![eq]);
}

#[test]
fn hint_model_equality_triangle_axioms_then_convergence() {
    let mut rig = mock_rig();
    let v = rig.vars.clone();
    let mut ctx = FakeCtx::new(8);
    ctx.assign(pos(v[0]), 1);
    let x = rig.parts.real_var("x");
    let y = rig.parts.real_var("y");
    let hint = || ModelEqualityRequest {
        lhs: y,
        rhs: x,
        reason: Vec::new(),
        implied: false,
    };
    {
        let mut m = rig.mock.borrow_mut();
        m.check_script
            .push_back(TheoryResult::NeedModelEqualities(vec![hint()]));
        m.check_script
            .push_back(TheoryResult::NeedModelEquality(hint()));
        // The "nothing new" round is re-asked once without LRA's
        // `assume_eqs`-over-split preference (Rung 4, `answer_model_eqs`); a
        // genuine hint round answers the same hint again and converges.
        m.check_script
            .push_back(TheoryResult::NeedModelEquality(hint()));
    }
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    let ExtCheckResult::AddClauses(clauses) = bridge.check(&ctx) else {
        panic!("expected AddClauses, exit {:?}", bridge.exit());
    };
    let eq = bridge.own.terms.find_eq(x, y).unwrap();
    let le_yx = bridge.own.terms.mk_le(y, x);
    let le_xy = bridge.own.terms.mk_le(x, y);
    let ts = bridge.tseitin.as_ref().unwrap();
    let (eq_v, l1, l2) = (
        Variable::new(ts.term_to_var[&eq] - 1),
        Variable::new(ts.term_to_var[&le_yx] - 1),
        Variable::new(ts.term_to_var[&le_xy] - 1),
    );
    assert_eq!(
        clauses,
        vec![
            vec![neg(eq_v), pos(l1)],
            vec![neg(eq_v), pos(l2)],
            vec![pos(eq_v), neg(l1), neg(l2)],
        ]
    );
    assert_eq!(
        bridge.suggest_phase(eq_v),
        Some(true),
        "try the equality first"
    );
    assert_eq!(bridge.mint.model_eq_rounds, 1);
    assert_eq!(
        bridge.take_originals(),
        [] as [std::vec::Vec<ay_sat::Literal>; 0]
    );
    // Same pair again in this query: nothing new -> one re-check without the
    // `assume_eqs` preference -> the same hint again -> Sat (§4.3).
    assert!(matches!(bridge.check(&ctx), ExtCheckResult::Sat));
    assert_eq!(
        bridge.stats().hint_rechecks,
        1,
        "the nothing-new round is re-asked once"
    );
    assert_eq!(bridge.stats().hint_convergences, 1);
    assert_eq!(
        rig.mock.borrow().check_calls,
        3,
        "two rounds + the re-check"
    );
    assert_eq!(
        bridge.mint.model_eq_rounds, 1,
        "rounds count NEW pairs only"
    );
    assert_eq!(bridge.exit(), BridgeExit::None);
    assert_eq!(rig.parts.st.mint_parent[l1.index()], eq_v.index() as u32);
}

#[test]
fn mint_cap_is_a_budget_unknown() {
    let mut rig = split_rig();
    rig.parts.cfg.max_mints_per_query = 0;
    let mut ctx = FakeCtx::new(1);
    ctx.assign(neg(rig.eq_var), 1);
    rig.mock
        .borrow_mut()
        .check_script
        .push_back(TheoryResult::NeedExpressionSplit(ExpressionSplitRequest {
            disequality_term: rig.eq,
        }));
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    assert!(matches!(bridge.check(&ctx), ExtCheckResult::Unknown));
    assert_eq!(bridge.exit(), BridgeExit::Budget(BudgetKind::MintCap));
}

#[test]
fn final_check_unknown_is_incomplete_or_budget() {
    let mut rig = mock_rig();
    let v = rig.vars.clone();
    let mut ctx = FakeCtx::new(8);
    ctx.assign(pos(v[0]), 1);
    rig.mock
        .borrow_mut()
        .check_script
        .push_back(TheoryResult::Unknown);
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    assert!(matches!(bridge.check(&ctx), ExtCheckResult::Unknown));
    assert_eq!(bridge.exit(), BridgeExit::TheoryIncomplete);
    drop(bridge);
    // A BCP-time Unknown is a label, not a verdict (module doc).
    rig.mock
        .borrow_mut()
        .bcp_script
        .push_back(TheoryResult::Unknown);
    let mut bridge = rig.parts.bridge(None, &never);
    bridge.init();
    let out = bridge.propagate(&ctx);
    assert!(!out.stop && out.conflict.is_none());
    assert_eq!(bridge.exit(), BridgeExit::None);
    assert_eq!(bridge.stats().bcp_unknowns, 1);
}

// ---------------------------------------------------------------------------
// Layer 2: the mock under the REAL ay-sat assumption loop
// ---------------------------------------------------------------------------

/// The session's SAT profile (§2.10, `HornSmt::new_sat`).
fn session_solver() -> ay_sat::Solver {
    let mut sat = ay_sat::Solver::new(0);
    sat.set_ic3_mode();
    sat.set_bve_enabled(false);
    sat.set_inc_engine_reset_mode(true);
    sat.set_random_seed(2026);
    sat.set_unsat_certificate_enabled(false);
    sat.set_preprocess_enabled(false);
    sat
}

#[test]
fn re_added_all_false_split_clause_is_a_pending_conflict_and_the_search_moves() {
    // `eq`, `lt`, `gt` all have variables (minted in an earlier query, the
    // split clause since dropped by the deletable tier); no clause mentions
    // lt/gt. The theory asks for the split while eq=false and both split
    // atoms are false; the bridge re-adds `[eq, lt, gt]` — all false — and
    // ay-sat must turn it into a conflict (F6) rather than livelock.
    let (theory, mock) = new_mock();
    let mut parts = Parts::with_theory(theory);
    let x = parts.real_var("x");
    let y = parts.real_var("y");
    let eq = parts.own.terms.mk_eq(x, y);
    let lt = parts.own.terms.mk_lt(x, y);
    let gt = parts.own.terms.mk_gt(x, y);
    let vars = parts.name_atoms(&[eq, lt, gt]);
    mock.borrow_mut().split_rule = Some((eq, lt, gt));
    let mut sat = session_solver();
    sat.ensure_num_vars(3);
    sat.set_var_phase(vars[1], false);
    sat.set_var_phase(vars[2], false);
    // A solver with no clauses at all answers SAT without entering the loop;
    // one inert clause over a fourth variable keeps the scenario intact.
    let dummy = sat.new_var();
    let _ = sat.add_clause_global(vec![pos(dummy), pos(vars[0])]);

    let mut bridge = parts.bridge(None, &never);
    let result = sat
        .solve_with_extension_and_assumptions_core(&mut bridge, &[neg(vars[0])], Some(&never))
        .into_inner();
    assert!(matches!(result, AssumeResult::Sat(_)), "{result:?}");
    assert_eq!(bridge.stats().minted_atoms, 0, "atom dedup: nothing fresh");
    assert!(
        bridge.stats().inline_batches >= 1,
        "the clause was re-added"
    );
    assert_eq!(bridge.exit(), BridgeExit::None);
    // Inside the guard: the final theory scopes hold the accepted assignment.
    {
        let m = mock.borrow();
        assert!(m.check_calls >= 2, "the search continued after the re-add");
        assert!(
            m.is_asserted(lt, true) || m.is_asserted(gt, true),
            "the pending conflict moved the search off the all-false assignment"
        );
    }
    bridge.backtrack(0);
    drop(bridge);
    assert!(
        sat.num_conflicts() >= 1,
        "the re-added all-false clause was a conflict"
    );
    assert_eq!(
        mock.borrow().scopes.len(),
        1,
        "theory popped to scope 0 by the guard"
    );
}

// ---------------------------------------------------------------------------
// Layer 3: real LraSolver under the real ay-sat loop, through the bridge
// ---------------------------------------------------------------------------

struct Outcome {
    result: AssumeResult,
    stats: BridgeStats,
    reentries: u32,
    /// Theory values of the watched terms, read INSIDE the guard on `Sat`.
    values: Vec<Option<BigRational>>,
    exit: BridgeExit,
}

/// A session-shaped harness over WP-1's allocation order (§3.1 step 4) and
/// re-entry protocol (§4.2) with none of WP-3's conversion: terms are built
/// directly in the store.
struct LraRig {
    parts: Parts,
    sat: ay_sat::Solver,
}

impl LraRig {
    fn new() -> Self {
        let mut own = Box::new(SmtContext::new());
        let theory = TheoryBox::new(&mut own);
        let mut parts = Parts::with_theory(theory);
        parts.own = own;
        parts.theory.rebind(&mut parts.own);
        Self {
            parts,
            sat: session_solver(),
        }
    }

    fn real_var(&mut self, name: &str) -> TermId {
        self.parts.real_var(name)
    }

    fn rat(&mut self, n: i64) -> TermId {
        self.parts.rat(n)
    }

    /// `assert_with_origin` minus conversion: Tseitin vars, then `act`, resync,
    /// global definitions and `(root ∨ act)`, atoms registered and tabled.
    fn assert(&mut self, term: TermId) -> Variable {
        self.parts.theory.rebind(&mut self.parts.own);
        let state = self.parts.tseitin.take().unwrap();
        let mut ts = Tseitin::from_state(&self.parts.own.terms, state);
        ts.ensure_min_next_var(SolverContext::num_vars(&self.sat) as u32 + 1);
        let enc = ts.encode_assertion(term);
        let mut state = ts.into_state();
        self.sat
            .ensure_num_vars(state.next_var.saturating_sub(1) as usize);
        let act = self.sat.new_var();
        self.sat.set_var_phase(act, true);
        state.next_var = SolverContext::num_vars(&self.sat) as u32 + 1;
        let root = Literal::from_dimacs(enc.root_lit);
        for clause in &enc.def_clauses {
            self.sat
                .add_clause_global(clause.0.iter().map(|&l| Literal::from_dimacs(l)).collect());
        }
        self.sat.add_clause_global(vec![root, pos(act)]);
        let mut atoms: FxHashSet<TermId> = FxHashSet::default();
        collect_theory_atoms_into(&self.parts.own.terms, [term], &mut atoms);
        let num_vars = SolverContext::num_vars(&self.sat);
        self.parts.st.grow(num_vars);
        let mut sorted: Vec<TermId> = atoms.into_iter().collect();
        sorted.sort_unstable();
        for a in sorted {
            if let Some(&dv) = state.term_to_var.get(&a) {
                let vi = (dv - 1) as usize;
                self.parts.st.atom_of_var[vi] = Some(a);
                self.parts.st.active_atom[vi] = true;
                if !self.parts.st.registered[vi] {
                    self.parts.st.registered[vi] = true;
                    self.parts.theory.as_dyn().register_atom(a);
                }
            }
        }
        self.parts.tseitin = Some(state);
        act
    }

    /// One query: assume `¬act` for `active`, run the re-entry loop, read the
    /// watched values inside the guard, pop the theory to scope 0.
    fn solve(&mut self, active: &[Variable], watch: &[TermId]) -> Outcome {
        let assumptions: Vec<Literal> = active.iter().map(|&a| neg(a)).collect();
        let mut bridge = self.parts.bridge(None, &never);
        let mut reentries = 0u32;
        let mut values = Vec::new();
        let result = loop {
            let r = self
                .sat
                .solve_with_extension_and_assumptions_core(&mut bridge, &assumptions, Some(&never))
                .into_inner();
            match r {
                AssumeResult::Unknown if bridge.exit() == BridgeExit::RestartWithOriginals => {
                    assert!(
                        matches!(
                            self.sat.last_unknown_reason(),
                            Some(SatUnknownReason::TheoryStop | SatUnknownReason::ExtensionUnknown)
                        ),
                        "{:?}",
                        self.sat.last_unknown_reason()
                    );
                    reentries += 1;
                    assert!(reentries <= 16, "re-entry cap");
                    for clause in bridge.take_originals() {
                        self.sat.add_clause_global(clause);
                    }
                    continue;
                }
                AssumeResult::Sat(_) => {
                    let view = bridge.model_view(&[]);
                    values = watch.iter().map(|&t| view.theory.arith_value(t)).collect();
                    break r;
                }
                other => break other,
            }
        };
        let stats = bridge.stats().clone();
        let exit = bridge.exit();
        // The guard's job.
        bridge.backtrack(0);
        assert_eq!(bridge.theory_level(), 0);
        Outcome {
            result,
            stats,
            reentries,
            values,
            exit,
        }
    }
}

fn r(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

#[test]
fn e2e_lra_sat_with_single_variable_disequality() {
    let mut rig = LraRig::new();
    let x = rig.real_var("x");
    let (c0, c1) = (rig.rat(0), rig.rat(1));
    let lo = rig.parts.own.terms.mk_ge(x, c0);
    let hi = rig.parts.own.terms.mk_le(x, c1);
    let ne = {
        let eq = rig.parts.own.terms.mk_eq(x, c0);
        rig.parts.own.terms.mk_not(eq)
    };
    let acts = [rig.assert(lo), rig.assert(hi), rig.assert(ne)];
    let out = rig.solve(&acts, &[x]);
    assert!(
        matches!(out.result, AssumeResult::Sat(_)),
        "{:?} exit {:?}",
        out.result,
        out.exit
    );
    let xv = out.values[0].clone().expect("x has a theory value");
    assert!(xv > r(0) && xv <= r(1), "x = {xv}");
    assert!(
        out.stats.mints_diseq >= 1,
        "the disequality was split inline: {:?}",
        out.stats
    );
    assert_eq!(out.stats.originals_restarts, 0);
    assert_eq!(out.reentries, 0);
}

#[test]
fn e2e_lra_sat_with_two_variable_disequality() {
    let mut rig = LraRig::new();
    let x = rig.real_var("x");
    let y = rig.real_var("y");
    let (c0, c1) = (rig.rat(0), rig.rat(1));
    let x_lo = rig.parts.own.terms.mk_ge(x, c0);
    let x_hi = rig.parts.own.terms.mk_le(x, c0);
    let y_lo = rig.parts.own.terms.mk_ge(y, c0);
    let y_hi = rig.parts.own.terms.mk_le(y, c1);
    let ne = rig.parts.own.terms.mk_distinct(vec![x, y]);
    let acts = [
        rig.assert(x_lo),
        rig.assert(x_hi),
        rig.assert(y_lo),
        rig.assert(y_hi),
        rig.assert(ne),
    ];
    let out = rig.solve(&acts, &[x, y]);
    assert!(
        matches!(out.result, AssumeResult::Sat(_)),
        "{:?} exit {:?}",
        out.result,
        out.exit
    );
    let (xv, yv) = (
        out.values[0].clone().unwrap(),
        out.values[1].clone().unwrap(),
    );
    assert_eq!(xv, r(0));
    assert!(yv > r(0) && yv <= r(1), "y = {yv}");
    assert!(
        out.stats.mints_expr + out.stats.mints_diseq >= 1,
        "split inline: {:?}",
        out.stats
    );
}

#[test]
fn e2e_lra_unsat_with_core_over_the_query_only() {
    let mut rig = LraRig::new();
    let x = rig.real_var("x");
    let y = rig.real_var("y");
    let (c0, c1) = (rig.rat(0), rig.rat(1));
    let y_lo = rig.parts.own.terms.mk_ge(y, c0);
    let x_lo = rig.parts.own.terms.mk_ge(x, c1);
    let x_hi = rig.parts.own.terms.mk_le(x, c0);
    let a_y = rig.assert(y_lo);
    let a1 = rig.assert(x_lo);
    let a2 = rig.assert(x_hi);
    let out = rig.solve(&[a_y, a1, a2], &[]);
    let AssumeResult::Unsat(core, _) = out.result else {
        panic!("expected Unsat, got {:?} exit {:?}", out.result, out.exit);
    };
    assert!(
        core.contains(&neg(a1)) && core.contains(&neg(a2)),
        "core {core:?}"
    );
    assert!(
        !core.contains(&neg(a_y)),
        "the irrelevant assumption is not in the core: {core:?}"
    );
    assert!(
        core.iter().all(|l| !l.is_positive()),
        "cores are ¬act literals"
    );
    assert!(out.stats.conflicts >= 1);
    assert!(!rig.parts.ledger.is_empty(), "the conflict was recorded");
}

#[test]
fn e2e_lra_ite_link_is_tier_two_and_the_reentered_solve_refutes() {
    // ite = (ite b x y); ite >= 10, x <= 0, y <= 0. With the ITE opaque the
    // theory is satisfied; the ITE link lemmas (implied model equalities,
    // reason `b` / `¬b`) are ORIGINALS: the first solve ends with
    // RestartWithOriginals, the re-entered solve is UNSAT.
    let mut rig = LraRig::new();
    let b = rig.parts.own.terms.mk_var("b", Sort::Bool);
    let x = rig.real_var("x");
    let y = rig.real_var("y");
    let (c0, c10) = (rig.rat(0), rig.rat(10));
    let ite = rig.parts.own.terms.mk_ite(b, x, y);
    let a1 = {
        let t = rig.parts.own.terms.mk_ge(ite, c10);
        rig.assert(t)
    };
    let a2 = {
        let t = rig.parts.own.terms.mk_le(x, c0);
        rig.assert(t)
    };
    let a3 = {
        let t = rig.parts.own.terms.mk_le(y, c0);
        rig.assert(t)
    };
    let out = rig.solve(&[a1, a2, a3], &[]);
    assert!(
        matches!(out.result, AssumeResult::Unsat(..)),
        "expected Unsat, got {:?} exit {:?} stats {:?}",
        out.result,
        out.exit,
        out.stats
    );
    assert_eq!(
        out.reentries, 1,
        "exactly one restart for the two link lemmas"
    );
    assert_eq!(out.stats.originals_restarts, 1);
    assert_eq!(out.stats.mints_model_eq, 2);
    // The `=` terms now exist, so the theory never re-requests (F12).
    assert!(rig.parts.own.terms.find_eq(ite, x).is_some());
    assert!(rig.parts.own.terms.find_eq(ite, y).is_some());
    if let AssumeResult::Unsat(core, _) = &out.result {
        assert_eq!(core.len(), 3, "all three assertions refute: {core:?}");
    }

    // Steady state: the same query again costs no re-entry.
    let again = rig.solve(&[a1, a2, a3], &[]);
    assert!(
        matches!(again.result, AssumeResult::Unsat(..)),
        "{:?}",
        again.result
    );
    assert_eq!(again.reentries, 0);
    assert_eq!(again.stats.originals_restarts, 0);
    // And relaxing y makes it satisfiable through the ¬b branch.
    let relaxed = rig.solve(&[a1, a2], &[x, y, ite]);
    assert!(
        matches!(relaxed.result, AssumeResult::Sat(_)),
        "{:?}",
        relaxed.result
    );
    let (xv, yv, iv) = (
        relaxed.values[0].clone().unwrap(),
        relaxed.values[1].clone().unwrap(),
        relaxed.values[2].clone().unwrap(),
    );
    assert!(
        xv <= r(0) && iv >= r(10) && iv == yv,
        "x={xv} y={yv} ite={iv}"
    );
}

#[test]
fn e2e_lra_back_to_back_queries_alternate_verdicts() {
    let mut rig = LraRig::new();
    let x = rig.real_var("x");
    let (c0, c1, c5) = (rig.rat(0), rig.rat(1), rig.rat(5));
    let ge1 = rig.parts.own.terms.mk_ge(x, c1);
    let le0 = rig.parts.own.terms.mk_le(x, c0);
    let le5 = rig.parts.own.terms.mk_le(x, c5);
    let (a_ge1, a_le0, a_le5) = (rig.assert(ge1), rig.assert(le0), rig.assert(le5));
    let q1 = rig.solve(&[a_ge1, a_le0], &[]);
    assert!(
        matches!(q1.result, AssumeResult::Unsat(..)),
        "{:?}",
        q1.result
    );
    let q2 = rig.solve(&[a_ge1, a_le5], &[x]);
    assert!(matches!(q2.result, AssumeResult::Sat(_)), "{:?}", q2.result);
    let xv = q2.values[0].clone().unwrap();
    assert!(xv >= r(1) && xv <= r(5), "x = {xv}");
    let q3 = rig.solve(&[a_le0, a_ge1, a_le5], &[]);
    assert!(
        matches!(q3.result, AssumeResult::Unsat(..)),
        "{:?}",
        q3.result
    );
    let q4 = rig.solve(&[a_le0], &[x]);
    assert!(matches!(q4.result, AssumeResult::Sat(_)), "{:?}", q4.result);
    assert!(q4.values[0].clone().unwrap() <= r(0));
    assert_eq!(
        rig.sat.ext_full_reset_hits(),
        0,
        "F2/F4: incremental resets only"
    );
}

// ---------------------------------------------------------------------------
// HornSmt::check_assuming end to end (WP-1 + WP-2 + WP-3)
// ---------------------------------------------------------------------------

fn rv(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Real))
}

fn real(n: i64) -> ChcExpr {
    ChcExpr::Real(n, 1)
}

#[test]
fn horn_check_assuming_sat_with_disequality_returns_a_verified_model() {
    let mut s = HornSmt::new(SessionConfig::default(), None);
    let ids = [
        ChcExpr::ge(rv("x"), real(0)),
        ChcExpr::le(rv("x"), real(1)),
        ChcExpr::ne(rv("x"), real(0)),
    ]
    .into_iter()
    .map(|e| {
        s.assert_persistent(&Arc::new(e), Partition::AB)
            .expect("eligible")
    })
    .collect::<Vec<_>>();
    let r = s.check_assuming(&ids, &[], Some(Duration::from_secs(10)));
    let HornCheck::Sat(model) = r else {
        panic!("expected Sat, got {r:?}");
    };
    assert!(
        model.contains_key("x"),
        "model over original names: {model:?}"
    );
    assert_eq!(s.stats().sat, 1);
    assert_eq!(s.stats().strict_demotions, 0);
}

#[test]
fn horn_check_assuming_unsat_returns_a_core_within_the_query() {
    let mut s = HornSmt::new(SessionConfig::default(), None);
    let a_y = s
        .assert_persistent(&Arc::new(ChcExpr::ge(rv("y"), real(0))), Partition::AB)
        .unwrap();
    let a1 = s
        .assert_persistent(&Arc::new(ChcExpr::ge(rv("x"), real(1))), Partition::AB)
        .unwrap();
    let a2 = s
        .assert_persistent(&Arc::new(ChcExpr::le(rv("x"), real(0))), Partition::AB)
        .unwrap();
    let r = s.check_assuming(&[a_y, a1, a2], &[], Some(Duration::from_secs(10)));
    let HornCheck::Unsat { core, .. } = r else {
        panic!("expected Unsat, got {r:?}");
    };
    assert!(core.contains(&a1) && core.contains(&a2), "{core:?}");
    assert!(!core.contains(&a_y), "{core:?}");
    assert!(!s.is_poisoned());
    // A follow-up SAT query on the same session.
    let r2 = s.check_assuming(&[a_y, a1], &[], Some(Duration::from_secs(10)));
    assert!(matches!(r2, HornCheck::Sat(_)), "{r2:?}");
    assert!(!matches!(
        r2,
        HornCheck::Unknown(UnknownReason::Poisoned(_))
    ));
}

// ---------------------------------------------------------------------------
// Theory-side finding (WP-2, 2026-09-19): minimal repro, kept as a lock
// ---------------------------------------------------------------------------

/// `LraSolver` alone, no SAT solver. Atoms asserted in scopes 1..5 with the
/// FIRST check at scope 5: LRA applies their bounds at that check and trails
/// them in scope 5. Popping scope 5 alone then wipes `x >= 0` / `x <= 0`
/// (asserted in scopes 1 and 2, still in `asserted`, never re-parsed), and the
/// next check accepts `x = -1/2` for `x < y`. The bridge avoids the shape by
/// flushing the theory before every new scope (`feed_trail`); the theory-side
/// fix landed as `fix(lra): trail an atom's bounds in the scope of its
/// assertion, not of the first check` (087985067, `LraSolver::push` flushes
/// pending atoms before recording the trail marks), so this asserts the
/// CORRECT model and runs; the bridge's per-push flush stays (redundant,
/// harmless).
#[test]
fn lra_bounds_are_trailed_in_the_scope_of_the_check_repro() {
    let mut own = Box::new(SmtContext::new());
    let mut theory = TheoryBox::new(&mut own);
    let x = own.terms.mk_var("x", Sort::Real);
    let y = own.terms.mk_var("y", Sort::Real);
    let c0 = own.terms.mk_rational(r(0));
    let c1 = own.terms.mk_rational(r(1));
    let x_lo = own.terms.mk_ge(x, c0);
    let x_hi = own.terms.mk_le(x, c0);
    let y_lo = own.terms.mk_ge(y, c0);
    let y_hi = own.terms.mk_le(y, c1);
    let eq = own.terms.mk_eq(x, y);
    let lt = own.terms.mk_lt(x, y);
    theory.rebind(&mut own);
    let t = theory.as_dyn();
    for a in [x_lo, x_hi, y_lo, y_hi, eq, lt] {
        t.register_atom(a);
    }
    t.push();
    t.assert_literal(x_lo, true);
    t.push();
    t.assert_literal(x_hi, true);
    t.push();
    t.assert_literal(y_lo, true);
    t.push();
    t.assert_literal(y_hi, true);
    t.push();
    t.assert_literal(eq, false);
    assert!(matches!(
        t.check(),
        TheoryResult::NeedExpressionSplit(_) | TheoryResult::NeedExpressionSplits(_)
    ));
    // Pop the disequality's scope only.
    t.pop();
    if let TheoryBox::Lra(l) = &theory {
        let (lo, hi) = l.get_bounds(x).expect("x is an LRA variable");
        assert!(
            lo.is_some() && hi.is_some(),
            "x's scope-1/2 bounds survive a pop of scope 5 (got lower={lo:?} upper={hi:?})"
        );
    }
    // Then assert the split atom at scope 4.
    let t = theory.as_dyn();
    t.assert_literal(lt, true);
    let verdict = t.check();
    let (xv, yv) = (
        theory.arith_value(x).unwrap(),
        theory.arith_value(y).unwrap(),
    );
    assert!(matches!(verdict, TheoryResult::Sat), "{verdict:?}");
    assert_eq!(
        xv,
        r(0),
        "x is fixed at 0 by never-popped bounds (got x={xv}, y={yv})"
    );
    assert!(yv > r(0) && yv <= r(1), "y = {yv}");
}
