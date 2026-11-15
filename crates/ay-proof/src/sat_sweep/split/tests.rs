// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The case split refutes a guarded identity with a DAG the independent
//! replay accepts, refuses a satisfiable one, and declines where no guard is
//! open.

use super::super::{literal, Gate, SweepLimits};
use super::core_sweep::Core;
use super::implications::Implications;
use super::pool::Pool;
use super::Leaves;
use ay_core::kani_compat::DetHashMap;
use ay_sat::{Literal, ResolutionDag};

/// A gate-level CNF built the way the printer's complete blast states it:
/// every gate by its full Tseitin rows.
#[derive(Default)]
struct Circuit {
    gates: Vec<Gate>,
    cnf: Vec<Vec<Literal>>,
}

impl Circuit {
    fn fresh(&mut self, gate: Gate) -> Literal {
        self.gates.push(gate);
        literal(self.gates.len() - 1, false)
    }

    fn input(&mut self) -> Literal {
        self.fresh(Gate::Input)
    }

    fn and(&mut self, a: Literal, b: Literal) -> Literal {
        let g = self.fresh(Gate::And(vec![a, b]));
        self.cnf.push(vec![g.negated(), a]);
        self.cnf.push(vec![g.negated(), b]);
        self.cnf.push(vec![g, a.negated(), b.negated()]);
        g
    }

    fn or(&mut self, a: Literal, b: Literal) -> Literal {
        let g = self.fresh(Gate::Or(vec![a, b]));
        self.cnf.push(vec![g, a.negated()]);
        self.cnf.push(vec![g, b.negated()]);
        self.cnf.push(vec![g.negated(), a, b]);
        g
    }

    fn iff(&mut self, a: Literal, b: Literal) -> Literal {
        let g = self.fresh(Gate::Iff(a, b));
        self.cnf.push(vec![g.negated(), a.negated(), b]);
        self.cnf.push(vec![g.negated(), a, b.negated()]);
        self.cnf.push(vec![g, a, b]);
        self.cnf.push(vec![g, a.negated(), b.negated()]);
        g
    }

    fn xor(&mut self, a: Literal, b: Literal) -> Literal {
        let g = self.fresh(Gate::Xor(vec![a, b]));
        self.cnf.push(vec![g.negated(), a, b]);
        self.cnf.push(vec![g.negated(), a.negated(), b.negated()]);
        self.cnf.push(vec![g, a.negated(), b]);
        self.cnf.push(vec![g, a, b.negated()]);
        g
    }

    /// The case split's answer with `top` asserted as the root unit.
    fn refute(self, top: Literal) -> Option<ResolutionDag> {
        self.split(top, Leaves::All).refutation
    }

    /// The case split over `leaves`, with `top` asserted as the root unit.
    fn split(self, top: Literal, leaves: Leaves) -> super::Outcome {
        self.split_with(top, leaves, SweepLimits::standalone(), &mut || true)
    }

    /// [`Self::split`] within `limits`.
    fn split_within(self, top: Literal, leaves: Leaves, limits: SweepLimits) -> super::Outcome {
        self.split_with(top, leaves, limits, &mut || true)
    }

    /// [`Self::split`] under the caller's poll `keep_going`.
    fn split_polled(
        self,
        top: Literal,
        leaves: Leaves,
        keep_going: &mut dyn FnMut() -> bool,
    ) -> super::Outcome {
        self.split_with(top, leaves, SweepLimits::standalone(), keep_going)
    }

    /// [`Self::split`] within `limits`, under the caller's poll `keep_going`.
    fn split_with(
        mut self,
        top: Literal,
        leaves: Leaves,
        limits: SweepLimits,
        keep_going: &mut dyn FnMut() -> bool,
    ) -> super::Outcome {
        self.cnf.push(vec![top]);
        let root = self.cnf.len() - 1;
        let cnf = self.cnf.clone();
        super::refute(
            self.gates,
            &cnf,
            &[root],
            false,
            &[],
            &[],
            leaves,
            limits,
            keep_going,
        )
    }

    /// The sweep of this whole circuit as one leaf's core, with `top`
    /// asserted as its root, under the caller's poll `keep_going`. Every
    /// clause is a row of the gate it was built for, the largest variable it
    /// mentions, except the root.
    fn core_sweep(
        &self,
        top: Literal,
        keep_going: &mut dyn FnMut() -> bool,
    ) -> (Option<ResolutionDag>, super::super::work::Spent) {
        let count = self.gates.len();
        let mut rows: Vec<Vec<u32>> = vec![Vec::new(); count];
        for (index, clause) in self.cnf.iter().enumerate() {
            let owner = clause.iter().map(|lit| lit.variable().index()).max();
            rows[owner.expect("a gate row mentions its gate")].push(index as u32);
        }
        let mut clauses = self.cnf.clone();
        clauses.push(vec![top]);
        let pool = Pool {
            clauses: clauses.clone(),
            ids: (1..=clauses.len() as u64).collect(),
            by_literal: Vec::new(),
            units: Vec::new(),
            constraints: Vec::new(),
            rows,
            definitions: Vec::new(),
            defined_by: DetHashMap::default(),
        };
        let global: Vec<usize> = (0..count).collect();
        let core = Core {
            nodes: &self.gates,
            value: &vec![None; count],
            rep: &DetHashMap::default(),
            pool: &pool,
            sources: &(0..clauses.len()).collect::<Vec<_>>(),
            clauses: &clauses,
            global: &global,
            local_of: &global.iter().map(|&var| (var, var)).collect(),
        };
        core.sweep(SweepLimits::standalone(), keep_going)
    }
}

/// `t` is the multiplexer `ite(s, a, b)` only through two guarded facts,
/// `s → t = a` and `¬s → t = b`; the root claims `t` differs from the
/// multiplexer's output. Unsatisfiable, and in each case of `s` an identity.
fn guarded_multiplexer(both_facts: bool) -> (Circuit, Literal) {
    let mut c = Circuit::default();
    let a = c.input();
    guarded_multiplexer_over(c, a, None, both_facts)
}

/// [`guarded_multiplexer`] with `a` already built in `c`, and the guarded
/// fact `s → t = a` stated over `fact` instead when it is given (a circuit
/// that computes `a` again).
fn guarded_multiplexer_over(
    mut c: Circuit,
    a: Literal,
    fact: Option<Literal>,
    both_facts: bool,
) -> (Circuit, Literal) {
    let (s, b, t) = (c.input(), c.input(), c.input());
    let then_arm = c.and(s, a);
    let else_arm = c.and(s.negated(), b);
    let out = c.or(then_arm, else_arm);
    let then_fact = c.iff(t, fact.unwrap_or(a));
    let else_fact = c.iff(t, b);
    let guarded_then = c.or(s.negated(), then_fact);
    let facts = if both_facts {
        let guarded_else = c.or(s, else_fact);
        c.and(guarded_then, guarded_else)
    } else {
        guarded_then
    };
    let differs = c.xor(out, t);
    let top = c.and(facts, differs);
    (c, top)
}

#[test]
fn a_guarded_identity_is_refuted_case_by_case_and_replays() {
    let (circuit, top) = guarded_multiplexer(true);
    let dag = circuit
        .refute(top)
        .expect("each case of the guard is an identity");
    assert!(dag
        .derived
        .last()
        .is_some_and(|step| step.clause.is_empty()));
    dag.validate()
        .expect("the split's DAG is an ordinary RUP refutation of the same CNF");
}

/// A leaf that keeps more of the circuit than [`super::SMALL_LEAF_VARS`]
/// ends a [`Leaves::Small`] split as deferred, before any search of it, and
/// the split over every leaf still refutes the same CNF: deferring changes
/// which lane runs first, never whether the lemma is refuted.
#[test]
fn a_split_of_small_leaves_defers_a_large_leaf_and_the_full_split_still_closes() {
    // Under `s` the leaf is `t = a` against `t = a'`, `a` and `a'` two
    // copies of one long parity chain: ternary rows no wiring collapses.
    let large = || {
        let mut c = Circuit::default();
        let inputs: Vec<Literal> = (0..super::SMALL_LEAF_VARS / 2).map(|_| c.input()).collect();
        let chain = |c: &mut Circuit| {
            let mut parity = inputs[0];
            for &x in &inputs[1..] {
                parity = c.xor(parity, x);
            }
            parity
        };
        let (a, copy) = (chain(&mut c), chain(&mut c));
        guarded_multiplexer_over(c, a, Some(copy), true)
    };
    let (circuit, top) = large();
    let small = circuit.split(top, Leaves::Small);
    assert!(small.deferred && small.refutation.is_none());
    let (circuit, top) = large();
    let all = circuit.split(top, Leaves::All);
    assert!(!all.deferred);
    all.refutation
        .expect("each case of the guard is an identity")
        .validate()
        .expect("the split's DAG is an ordinary RUP refutation of the same CNF");
    // A small leaf is refuted where the split meets it, whatever the policy.
    let (circuit, top) = guarded_multiplexer(true);
    let small = circuit.split(top, Leaves::Small);
    assert!(!small.deferred && small.refutation.is_some());
}

/// Two copies `(a, copy)` of one parity chain over `width` inputs: equal
/// gate by gate, and by nothing unit propagation sees.
fn parity_copies(width: usize) -> (Circuit, Literal, Literal) {
    let mut c = Circuit::default();
    let inputs: Vec<Literal> = (0..width).map(|_| c.input()).collect();
    let chain = |c: &mut Circuit| {
        let mut parity = inputs[0];
        for &x in &inputs[1..] {
            parity = c.xor(parity, x);
        }
        parity
    };
    let (a, copy) = (chain(&mut c), chain(&mut c));
    (c, a, copy)
}

/// A leaf's core sweep spends the split's own work allowance, never a fresh
/// one, and the split reports what its leaves read: the leaf under `s` is
/// `t = a` against `t = a'`, two copies of one parity chain, which its core
/// sweep refutes by merging them gate by gate. Given a quarter of what the
/// split read without a cap, it declines having read its allowance and at
/// most the one candidate that crossed it.
#[test]
fn a_split_charges_its_leaf_core_sweeps_to_its_own_work_allowance() {
    let guarded_copies = || {
        let (c, a, copy) = parity_copies(64);
        guarded_multiplexer_over(c, a, Some(copy), true)
    };
    let (circuit, top) = guarded_copies();
    let free = circuit.split(top, Leaves::All);
    assert!(free.refutation.is_some(), "each case is an identity");
    let allowance = free.worked / 4;
    assert!(allowance > 0, "{}", free.worked);
    let (circuit, top) = guarded_copies();
    let limits = SweepLimits {
        total_work: allowance,
        ..SweepLimits::standalone()
    };
    let capped = circuit.split_within(top, Leaves::All, limits);
    assert!(capped.refutation.is_none());
    assert!(
        capped.worked >= allowance && capped.worked < free.worked / 2,
        "{} read of {allowance}; {} without a cap",
        capped.worked,
        free.worked
    );
}

#[test]
fn a_satisfiable_guarded_claim_is_never_refuted() {
    // Without `¬s → t = b`, `t` is free whenever `s` is false.
    let (circuit, top) = guarded_multiplexer(false);
    assert!(circuit.refute(top).is_none());
}

#[test]
fn a_root_without_an_open_guard_is_left_to_the_other_routes() {
    let mut c = Circuit::default();
    let (a, b) = (c.input(), c.input());
    let left = c.and(a, b);
    let right = c.and(b, a);
    let differs = c.xor(left, right);
    assert!(c.refute(differs).is_none());
}

#[test]
fn equal_literals_are_one_class_and_their_complements_another() {
    let (x, y, z) = (literal(0, false), literal(1, false), literal(2, false));
    let mut graph = Implications::default();
    // x ↔ y through two clauses; y → z one way only.
    graph.edge(x, y, 0);
    graph.edge(y, x, 1);
    graph.edge(y.negated(), x.negated(), 0);
    graph.edge(x.negated(), y.negated(), 1);
    graph.edge(y, z, 2);
    let components = graph.components();
    let class = |lit: Literal| components.of[graph.node[&lit] as usize];
    assert_eq!(class(x), class(y));
    assert_eq!(class(x.negated()), class(y.negated()));
    assert_ne!(class(x), class(x.negated()));
    assert_ne!(class(y), class(z));
}

/// A leaf's core is swept under the split's own poll. Under an unconditional
/// one (`Core::sweep` before it took `keep_going`), the strict checker's
/// split of the sign-extended commuted 32-bit product comparison swept leaf
/// cores for 43.6 s without a single poll and its query, given 20 s, answered
/// at 48.4 s. Refused, the core spends nothing and refutes nothing; allowed,
/// the same core refutes.
#[test]
fn a_leaf_core_sweep_answers_to_the_callers_poll() {
    let (mut circuit, a, copy) = parity_copies(16);
    let top = circuit.xor(a, copy);
    let (refused, spent) = circuit.core_sweep(top, &mut || false);
    assert!(refused.is_none());
    assert_eq!(spent, super::super::work::Spent::default());
    let mut polls = 0_u32;
    let (allowed, _) = circuit.core_sweep(top, &mut || {
        polls += 1;
        true
    });
    let dag = allowed.expect("the copies are equal gate by gate");
    assert!(dag
        .derived
        .last()
        .is_some_and(|step| step.clause.is_empty()));
    assert!(polls > 0, "the core sweep polled its caller");
}

/// One refusal ends the split unrefuted wherever it lands, even from a poll
/// that relents afterwards (an interrupt flag lowered again): a refusal the
/// leaf's core sweep observes is latched for the whole split
/// (`Sweep::refute_core`). Kept by the core alone, the leaf would fall back to
/// its uncompressed search, poll again and refute. Under `s` the leaf is the
/// identity of two parity chains, which only a core sweep closes.
#[test]
fn one_refusal_anywhere_ends_the_split_unrefuted() {
    let split = |refuse_at: Option<u32>| {
        let (circuit, a, copy) = parity_copies(16);
        let (circuit, top) = guarded_multiplexer_over(circuit, a, Some(copy), true);
        let mut polls = 0_u32;
        let outcome = circuit.split_polled(top, Leaves::All, &mut || {
            polls += 1;
            Some(polls) != refuse_at
        });
        (outcome.refutation, polls)
    };
    let (refuted, polls) = split(None);
    assert!(refuted.is_some(), "each case of the guard is an identity");
    // About 200 refusal points spread over the whole run, the last poll
    // included: most of the polls are the leaf's core sweep's.
    let stride = usize::try_from(polls / 200).unwrap_or(1).max(1);
    for refuse_at in (1..=polls).step_by(stride).chain([polls]) {
        assert!(
            split(Some(refuse_at)).0.is_none(),
            "refused at poll {refuse_at} of {polls}"
        );
    }
}
