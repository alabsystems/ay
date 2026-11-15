// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The nested search: Reynolds/King/Kuncak FMSD'17 Fig. 8 over the
//! [`NestedTree`] (milestone M2).
//!
//! ```text
//! loop {
//!   S1 = ⌊roots⌋Γ                         // NO counterexample formula
//!   S1 unsat → both-polarity top nodes exact, and no top node logged
//!              since S1 was built → Unsat // Theorem 4.1
//!   for top node A:  S1 ∧ CE_A            // in context: guidance + SAT side
//!     unsat → A holds in every model of S1 once its unsafe children are
//!             exact AND UNCHANGED since the check (else ask CE_A again)
//!     sat(I) → rec every child; if one logged, ask CE_A again
//!              else log A ⇒ ⌊ψ_A[t]⌋Γ with t = select(I) (end of round)
//!   nothing logged, and no TOP node logged mid-round (as a shared nested
//!   child) → Sat                          // Theorem 4.2, top in context
//! }
//! rec(N):  CE_N alone (k free)             // STANDALONE, Fig. 8 exactly
//!   unsat → unsafe children exact AND unchanged since the check
//!           → N EXACT for every k (Lemma 10.2); else ask CE_N again
//!   sat(I) → rec every child; if one logged, ask CE_N again
//!            else log N ⇒ ⌊ψ_N[k, t]⌋Γ    (frozen; Lemma 10.1)
//! ```
//!
//! `CE_N` is `⌊N⌋Γ ∧ ¬⌊ψ_N[e⃗]⌋Γ` for an authored universal and
//! `¬⌊N⌋Γ ∧ ⌊ψ_N[e⃗]⌋Γ` for an authored existential.
//!
//! WHY A NESTED NODE IS EXACT ONLY FROM A CONTEXT-FREE UNSAT. Its instances
//! are templates over the enclosing counterexample constants `k`; the parent
//! substitutes them at every instance it logs, so `⌊N⌋Γ ⟺ N` must hold for
//! EVERY `k`, not just the `k` some context allows. The exact flag is
//! permanent, so it is set only from `CE_N` with `k` free.
//!
//! UNSAFE CHILDREN and STALE CHECKS: see [`unsafe_children`] — when a
//! node's `CE` UNSAT (or the main query's) may be trusted at all.
//!
//! Results are HINTS: a caller publishes only through an independent route.

use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};

use super::approx::{dag_size, Approximator, NInstance};
use super::caps::MAX_SELECT_WORK;
use super::nested_run::SLOW_CALLS;
pub(crate) use super::nested_run::{NestedCaps, NestedRun, NestedStats, TraceStep};
use super::ntree::{Kind, NestedTree};
use super::select::{select_tuple_for, tuple_terms};
use super::session::NestedSeed;
use super::{
    assignment_from, Assignment, OracleAnswer, QlraDecline, QlraHost, QlraOutcome, SelectDecline,
};

/// Entries kept in the search trace.
const MAX_TRACE: usize = 512;
/// Query DAG size above which `approx_max` stops counting.
const DAG_STAT_LIMIT: usize = 1 << 22;

type Logged = (usize, NInstance);

#[path = "nested_unsafe.rs"]
mod unsafe_children;

/// What one [`Search::rec`] call achieved.
enum Progress {
    /// The node is exact (for every environment).
    Exact,
    /// The node logged one instance of its own.
    Logged,
}

/// A counterexample model plus the formula the selection works on.
struct Counterexample {
    model: Assignment,
    phi: TermId,
    want: bool,
}

struct Search<'t> {
    tree: &'t NestedTree,
    gamma: Vec<Vec<NInstance>>,
    exact: Vec<bool>,
    all_ce: Vec<TermId>,
    approx: Approximator,
    stats: NestedStats,
    trace: Vec<TraceStep>,
    round: usize,
    /// A TOP node logged an instance since this round's main query was
    /// built (see [`Search::run`]).
    top_logged: bool,
    caps: NestedCaps,
}

fn free_vars(terms: &TermStore, roots: &[TermId]) -> Vec<TermId> {
    let mut out = Vec::new();
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Var(..) => out.push(t),
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
            _ => {}
        }
    }
    out.sort();
    out
}

impl Search<'_> {
    fn note(&mut self, step: TraceStep) {
        if self.trace.len() < MAX_TRACE {
            self.trace.push(step);
        }
    }

    fn ask(
        &mut self,
        host: &mut dyn QlraHost,
        node: usize,
        query: &[TermId],
        targets: &[TermId],
    ) -> OracleAnswer {
        self.stats.oracle_calls += 1;
        let size = dag_size(host.terms(), query, DAG_STAT_LIMIT);
        self.stats.approx_max = self.stats.approx_max.max(size);
        let started = ay_core::time::Instant::now();
        let answer = host.check(query, targets);
        let spent = ay_core::time::Instant::now().saturating_duration_since(started);
        let ms = u64::try_from(spent.as_millis()).unwrap_or(u64::MAX);
        self.stats.oracle_ms = self.stats.oracle_ms.saturating_add(ms);
        let slow = &mut self.stats.slow_calls;
        slow.push((node, ms, size));
        slow.sort_by(|a, b| b.1.cmp(&a.1));
        slow.truncate(SLOW_CALLS);
        answer
    }

    fn main_query(&mut self, host: &mut dyn QlraHost) -> Result<Vec<TermId>, QlraDecline> {
        let mut out = Vec::with_capacity(self.tree.roots.len());
        for &root in &self.tree.roots {
            let term = self
                .approx
                .approx(host.terms(), self.tree, &self.gamma, root, &[])?;
            if !out.contains(&term) {
                out.push(term);
            }
        }
        Ok(out)
    }

    /// `CE_N` (optionally under `context`). `None`: unsat.
    fn check(
        &mut self,
        host: &mut dyn QlraHost,
        node: usize,
        context: Option<&[TermId]>,
    ) -> Result<Option<Counterexample>, QlraDecline> {
        let tree = self.tree;
        let (kind, ce_body) = (tree.nodes[node].kind, tree.nodes[node].ce_body);
        let current = self
            .approx
            .node(host.terms(), self.tree, &self.gamma, node, &[])?;
        let phi = self
            .approx
            .approx(host.terms(), self.tree, &self.gamma, ce_body, &[])?;
        let (guard, target, want) = match kind {
            Kind::Forall => (current, host.terms().mk_not(phi), false),
            Kind::Exists => (host.terms().mk_not(current), phi, true),
        };
        let mut query = context.map(<[TermId]>::to_vec).unwrap_or_default();
        query.push(guard);
        query.push(target);
        let targets = free_vars(host.terms(), &[phi]);
        let answer = self.ask(host, node, &query, &targets);
        let sat = matches!(answer, OracleAnswer::Sat(_));
        self.note(TraceStep::Check {
            node,
            context: context.is_some(),
            sat,
        });
        match answer {
            OracleAnswer::Unsat => Ok(None),
            OracleAnswer::Unknown => Err(QlraDecline::OracleUnknown),
            OracleAnswer::Sat(values) => Ok(Some(Counterexample {
                model: assignment_from(host, &targets, values),
                phi,
                want,
            })),
        }
    }

    /// Fig. 8 `rec_T`, standalone: returns once `node` is exact or has
    /// logged one instance of its own.
    ///
    /// SCHEDULING. Fig. 8 hands every new instance back to `CEGQI_T`, which
    /// re-asks the main query and every ancestor on the way down. Because
    /// instances are FROZEN, an instance of a child that is not itself a top
    /// node changes only its parent's counterexample formula: the main query
    /// and every other ancestor's formula are the same terms as before. So
    /// after a child logs, only this node's query is asked again. A child
    /// that IS also a top node (shared by term, e.g. a closed quantifier
    /// asserted on its own and nested elsewhere) does change the main query;
    /// [`Search::run`] then refuses to answer Sat from that round and starts
    /// another.
    fn rec(&mut self, host: &mut dyn QlraHost, node: usize) -> Result<Progress, QlraDecline> {
        if self.exact[node] {
            return Ok(Progress::Exact);
        }
        loop {
            if host.should_stop() {
                return Err(QlraDecline::Timeout);
            }
            let marks = self.unsafe_marks(node);
            match self.check(host, node, None)? {
                None => {
                    if !self.unsafe_ready(host, node, &marks)? {
                        continue;
                    }
                    self.exact[node] = true;
                    self.stats.exact_nodes += 1;
                    self.note(TraceStep::Exact { node });
                    return Ok(Progress::Exact);
                }
                Some(cex) => {
                    if self.children_first(host, node, true)? {
                        continue;
                    }
                    let instance = self.select(host, node, &cex)?;
                    self.log((node, instance))?;
                    return Ok(Progress::Logged);
                }
            }
        }
    }

    /// Model-preserving selection plus the frozen instance.
    fn select(
        &mut self,
        host: &mut dyn QlraHost,
        node: usize,
        cex: &Counterexample,
    ) -> Result<NInstance, QlraDecline> {
        let tree = self.tree;
        let n = &tree.nodes[node];
        let sorts: Vec<Sort> = n.binders.iter().map(|(_, sort)| sort.clone()).collect();
        let chosen = select_tuple_for(
            host.terms(),
            cex.phi,
            cex.want,
            &n.ce_vars,
            &sorts,
            &cex.model,
            MAX_SELECT_WORK,
        )
        .map_err(QlraDecline::Select)?;
        let tuple = tuple_terms(host.terms(), &chosen);
        for &t in &tuple {
            let leaked = free_vars(host.terms(), &[t])
                .into_iter()
                .any(|v| self.all_ce.binary_search(&v).is_ok() && !n.env.contains(&v));
            if leaked {
                return Err(QlraDecline::Select(SelectDecline::CeLeak));
            }
        }
        if self.gamma[node].iter().any(|logged| logged.tuple == tuple) {
            return Err(QlraDecline::NoProgress);
        }
        let mut rho: Vec<(TermId, TermId)> = n
            .ce_vars
            .iter()
            .copied()
            .zip(tuple.iter().copied())
            .collect();
        rho.sort();
        let ce_body = n.ce_body;
        let frozen = self
            .approx
            .approx(host.terms(), self.tree, &self.gamma, ce_body, &rho)?;
        Ok(NInstance {
            tuple,
            frozen,
            round: self.round,
        })
    }

    fn log(&mut self, (node, instance): Logged) -> Result<(), QlraDecline> {
        if self.gamma[node].len() >= self.caps.instances_per_node {
            return Err(QlraDecline::Cap("cap-instances-per-node"));
        }
        if self.stats.instances >= self.caps.instances {
            return Err(QlraDecline::Cap("cap-instances"));
        }
        self.note(TraceStep::Instance {
            node,
            tuple: instance.tuple.clone(),
        });
        self.gamma[node].push(instance);
        self.top_logged |= self.tree.nodes[node].top.is_some();
        self.stats.instances += 1;
        self.approx.gamma_changed();
        Ok(())
    }

    /// One top node in the main context: `Ok(None)` when it holds in every
    /// model of `main` (exactly, given its unsafe children), else the instance
    /// to log at the end of the round.
    fn top_step(
        &mut self,
        host: &mut dyn QlraHost,
        node: usize,
        main: &[TermId],
    ) -> Result<Option<Logged>, QlraDecline> {
        loop {
            if host.should_stop() {
                return Err(QlraDecline::Timeout);
            }
            let marks = self.unsafe_marks(node);
            match self.check(host, node, Some(main))? {
                None => {
                    if !self.unsafe_ready(host, node, &marks)? {
                        continue;
                    }
                    return Ok(None);
                }
                Some(cex) => {
                    if self.children_first(host, node, true)? {
                        continue;
                    }
                    return Ok(Some((node, self.select(host, node, &cex)?)));
                }
            }
        }
    }

    /// Top nodes occurring at both polarities must be exact everywhere
    /// before an UNSAT of the main query refutes the roots. `true` when one
    /// logged an instance (the main query changed).
    fn both_polarity_pending(&mut self, host: &mut dyn QlraHost) -> Result<bool, QlraDecline> {
        for index in 0..self.tree.top.len() {
            let node = self.tree.top[index];
            if self.tree.nodes[node].top.is_some_and(|pol| pol.both())
                && matches!(self.rec(host, node)?, Progress::Logged)
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn run(
        &mut self,
        host: &mut dyn QlraHost,
        main_out: &mut Vec<TermId>,
    ) -> Result<QlraOutcome, QlraDecline> {
        for round in 0..self.caps.rounds {
            self.round = round;
            self.stats.rounds = round + 1;
            if host.should_stop() {
                return Err(QlraDecline::Timeout);
            }
            self.top_logged = false;
            let main = self.main_query(host)?;
            let answer = self.ask(host, usize::MAX, &main, &[]);
            self.note(TraceStep::Main {
                sat: matches!(answer, OracleAnswer::Sat(_)),
            });
            match answer {
                OracleAnswer::Unknown => return Err(QlraDecline::OracleUnknown),
                OracleAnswer::Unsat => {
                    // The both-polarity top nodes must be exact AS THEY STOOD
                    // IN `main`: one made exact through another's recursion
                    // (shared by term) answers "exact" at once, but `main`
                    // used its older approximation — ask again.
                    if self.both_polarity_pending(host)? || self.top_logged {
                        continue;
                    }
                    return Ok(QlraOutcome::Unsat);
                }
                OracleAnswer::Sat(_) => {}
            }
            let mut added: Vec<Logged> = Vec::new();
            for index in 0..self.tree.top.len() {
                if host.should_stop() {
                    return Err(QlraDecline::Timeout);
                }
                let node = self.tree.top[index];
                if let Some(logged) = self.top_step(host, node, &main)? {
                    added.push(logged);
                }
            }
            if added.is_empty() {
                // A top node that is ALSO a nested child (nodes are shared by
                // term) can log mid-round from another top node's `rec`. The
                // main query of this round then no longer contains that
                // node's approximation, and a later in-context check asked
                // `stale main ∧ ⌊A⌋_new ∧ ¬ψ`, which proves nothing about
                // the models of `main`: re-ask everything next round.
                if self.top_logged {
                    continue;
                }
                *main_out = main;
                return Ok(QlraOutcome::Sat);
            }
            for logged in added {
                self.log(logged)?;
            }
        }
        Err(QlraDecline::Cap("cap-rounds"))
    }
}

/// Run the nested search over `tree`.
#[cfg(test)]
pub(crate) fn solve_nested(host: &mut dyn QlraHost, tree: &NestedTree) -> NestedRun {
    solve_nested_with(host, tree, NestedCaps::default())
}

/// [`solve_nested`] under explicit caps.
#[cfg(test)]
pub(crate) fn solve_nested_with(
    host: &mut dyn QlraHost,
    tree: &NestedTree,
    caps: NestedCaps,
) -> NestedRun {
    solve_nested_seeded(host, tree, caps, None)
}

/// The nested search under explicit caps, continuing from a session-cache `seed` (M4,
/// `session.rs`): each node starts from its cached instance log and exact
/// flag. A seed whose shape does not match the tree is ignored. Seeded
/// instances count toward the per-node cap, not the run's instance count.
pub(crate) fn solve_nested_seeded(
    host: &mut dyn QlraHost,
    tree: &NestedTree,
    caps: NestedCaps,
    seed: Option<NestedSeed>,
) -> NestedRun {
    let mut all_ce: Vec<TermId> = tree
        .nodes
        .iter()
        .flat_map(|node| node.ce_vars.iter().copied())
        .collect();
    all_ce.sort();
    let (gamma, exact) = match seed {
        Some(seed)
            if seed.gamma.len() == tree.nodes.len() && seed.exact.len() == tree.nodes.len() =>
        {
            (seed.gamma, seed.exact)
        }
        _ => (
            vec![Vec::new(); tree.nodes.len()],
            vec![false; tree.nodes.len()],
        ),
    };
    let mut search = Search {
        tree,
        gamma,
        exact,
        all_ce,
        approx: Approximator::default(),
        stats: NestedStats::default(),
        trace: Vec::new(),
        round: 0,
        top_logged: false,
        caps,
    };
    let mut main = Vec::new();
    let outcome = match search.run(host, &mut main) {
        Ok(outcome) => outcome,
        Err(decline) => QlraOutcome::Decline(decline),
    };
    NestedRun {
        outcome,
        main,
        stats: search.stats,
        trace: search.trace,
        gamma: search.gamma,
        exact: search.exact,
    }
}
