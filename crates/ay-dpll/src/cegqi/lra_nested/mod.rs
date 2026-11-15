// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Nested counterexample-guided instantiation for quantified LRA
//! (#qlra-nested-cegqi; Reynolds/King/Kuncak FMSD'17, Fig. 8).
//!
//! A PURE search engine: it owns no `Executor`, publishes nothing and grants
//! nothing. Every satisfiability question goes through [`QlraHost::check`];
//! every answer it returns is a hint that a publication route re-derives.
//!
//! M1 scope: depth-1 effective-∀ nodes in conjunctive position (see
//! [`tree`]). The loop is Fig. 8 restricted to top-level nodes:
//!
//! ```text
//! loop {
//!   S1 = ground ∧ Γ                      // contains NO counterexample formula
//!   S1 unsat            → Unsat(Γ)
//!   for each node A:  S1 ∧ ¬ψ_A[e⃗]      // one disposable query per node
//!     unsat → A holds in every model of S1
//!     sat(I) → t⃗ = select(I); Γ ∪= ψ_A[t⃗]
//!   nothing added       → Sat(Γ)
//! }
//! ```
//!
//! Counterexample formulas are NEVER conjoined into `S1`; each is asked in its
//! own query, so an UNSAT of `S1` is a refutation of `ground ∧ Γ` alone
//! (the `ce_free_resolve.rs` ambiguity cannot arise).
//!
//! M2 scope ([`nested`], default ON, `--no-qlra-nested` off): the full Fig. 8 recursion
//! over the [`ntree`] node tree — nested alternation, merged same-kind blocks,
//! quantifiers under connectives at any depth, frozen instances
//! ([`approx`]), standalone nested exactness. Its verdicts are SHADOW ONLY
//! until the M3 certificates exist.

pub(crate) mod approx;
pub(crate) mod caps;
mod implicant;
pub(crate) mod log;
pub(crate) mod nested;
mod nested_run;
pub(crate) mod ntree;
pub(crate) mod oracle;
pub(crate) mod select;
pub(crate) mod session;
pub(crate) mod tree;

#[cfg(test)]
mod nested_tests;
#[cfg(test)]
mod select_tests;
#[cfg(test)]
mod session_tests;
#[cfg(test)]
mod tests;

use ay_core::term::TermData;
use ay_core::{Sort, TermId};

use caps::{MAX_INSTANCES_PER_NODE, MAX_QLRA_ROUNDS, MAX_SELECT_WORK, MAX_TOTAL_INSTANCES};
pub(crate) use implicant::Assignment;
pub(crate) use log::{InstanceLog, QlraInstance};
#[cfg(test)]
pub(crate) use nested::{solve_nested, NestedRun, TraceStep};
#[cfg(test)]
pub(crate) use ntree::build_nested_tree;
pub(crate) use ntree::build_nested_tree_reusing;
pub(crate) use oracle::{OracleAnswer, OracleValue, QlraHost};
pub(crate) use select::SelectDecline;
pub(crate) use tree::{build_depth1_tree, NodeSource, QlraTree};

/// Why the search gave the problem back.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum QlraDecline {
    Timeout,
    OracleUnknown,
    Cap(&'static str),
    Select(SelectDecline),
    /// The exact substitution refused a selected tuple.
    Substitution,
    /// A selection reproduced an already-logged instance: the oracle's model
    /// contradicted Γ, so the loop cannot progress.
    NoProgress,
}

impl QlraDecline {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Timeout => "timeout",
            Self::OracleUnknown => "oracle-unknown",
            Self::Cap(which) => which,
            Self::Select(SelectDecline::Implicant) => "select-implicant",
            Self::Select(SelectDecline::Unassigned) => "select-unassigned",
            Self::Select(SelectDecline::ModelPreservation) => "select-model-preservation",
            Self::Select(SelectDecline::CeLeak) => "select-ce-leak",
            Self::Substitution => "substitution",
            Self::NoProgress => "no-progress",
        }
    }
}

/// The search verdict. Hints only; see the module docs.
#[derive(Clone, Debug)]
pub(crate) enum QlraOutcome {
    /// `ground ∧ Γ` is unsatisfiable.
    Unsat,
    /// Every node holds in every model of `ground ∧ Γ`.
    Sat,
    Decline(QlraDecline),
}

/// Search counters for `--stats`.
#[derive(Clone, Debug, Default)]
pub(crate) struct QlraStats {
    pub(crate) rounds: usize,
    pub(crate) oracle_calls: usize,
}

/// Every problem constant and counterexample constant below `term`.
fn free_vars(host: &mut dyn QlraHost, term: TermId) -> Vec<TermId> {
    let terms = host.terms();
    let mut out = Vec::new();
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    let mut stack = vec![term];
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

pub(super) fn assignment_from(
    host: &mut dyn QlraHost,
    targets: &[TermId],
    values: Vec<Option<OracleValue>>,
) -> Assignment {
    let mut model = Assignment::default();
    for (&target, value) in targets.iter().zip(values) {
        match value {
            Some(OracleValue::Rat(r)) => {
                model.reals.insert(target, r);
            }
            Some(OracleValue::Bool(b)) => {
                model.bools.insert(target, b);
            }
            None => {
                // A constant the probe's model left unvalued (eliminated or
                // unconstrained) defaults like the printer completion would.
                // Harmless either way: the selection re-evaluates the body
                // under the completed model and declines unless it is false.
                match host.terms().sort(target) {
                    Sort::Bool => model.bools.insert(target, false).map(|_| ()),
                    _ => model
                        .reals
                        .insert(target, num_rational::BigRational::from_integer(0.into()))
                        .map(|_| ()),
                };
            }
        }
    }
    model
}

/// One counterexample query for node `index` in context `s1`.
///
/// `Ok(None)`: the node holds in every model of `s1`. `Ok(Some(entry))`: a new
/// instance, not yet logged.
fn refine_node(
    host: &mut dyn QlraHost,
    tree: &QlraTree,
    index: usize,
    s1: &[TermId],
    log: &InstanceLog,
    round: usize,
    stats: &mut QlraStats,
) -> Result<Option<QlraInstance>, QlraDecline> {
    let node = &tree.nodes[index];
    let negated = host.terms().mk_not(node.ce_body);
    let mut query = s1.to_vec();
    query.push(negated);
    let targets = free_vars(host, node.ce_body);
    stats.oracle_calls += 1;
    let values = match host.check(&query, &targets) {
        OracleAnswer::Unsat => return Ok(None),
        OracleAnswer::Unknown => return Err(QlraDecline::OracleUnknown),
        OracleAnswer::Sat(values) => values,
    };
    let model = assignment_from(host, &targets, values);
    let sorts: Vec<Sort> = node.binders.iter().map(|(_, sort)| sort.clone()).collect();
    let chosen = select::select_tuple(
        host.terms(),
        node.ce_body,
        &node.ce_vars,
        &sorts,
        &model,
        MAX_SELECT_WORK,
    )
    .map_err(QlraDecline::Select)?;
    let tuple = select::tuple_terms(host.terms(), &chosen);
    let all_ce = tree.all_ce_vars();
    if tuple
        .iter()
        .any(|&t| free_vars(host, t).iter().any(|v| all_ce.contains(v)))
    {
        return Err(QlraDecline::Select(SelectDecline::CeLeak));
    }
    let instance = tree::instantiate(host.terms(), node.body, &node.binders, &tuple)
        .ok_or(QlraDecline::Substitution)?;
    if log.contains(index, instance) {
        return Err(QlraDecline::NoProgress);
    }
    Ok(Some(QlraInstance {
        node: index,
        tuple,
        instance,
        round,
    }))
}

/// Run the M1 search over `tree`. `publishable_cap` bounds Γ to what the
/// caller's publication route can carry (declining beyond it).
pub(crate) fn solve_depth1(
    host: &mut dyn QlraHost,
    tree: &QlraTree,
    publishable_cap: usize,
) -> (QlraOutcome, InstanceLog, QlraStats) {
    let mut log = InstanceLog::default();
    let mut stats = QlraStats::default();
    let outcome = run_rounds(host, tree, publishable_cap, &mut log, &mut stats);
    (outcome, log, stats)
}

fn run_rounds(
    host: &mut dyn QlraHost,
    tree: &QlraTree,
    publishable_cap: usize,
    log: &mut InstanceLog,
    stats: &mut QlraStats,
) -> QlraOutcome {
    for round in 0..MAX_QLRA_ROUNDS {
        stats.rounds = round + 1;
        if host.should_stop() {
            return QlraOutcome::Decline(QlraDecline::Timeout);
        }
        let mut s1 = tree.ground.clone();
        s1.extend(log.instance_terms());
        stats.oracle_calls += 1;
        match host.check(&s1, &[]) {
            OracleAnswer::Unsat => return QlraOutcome::Unsat,
            OracleAnswer::Unknown => return QlraOutcome::Decline(QlraDecline::OracleUnknown),
            OracleAnswer::Sat(_) => {}
        }
        let mut added = Vec::new();
        for index in 0..tree.nodes.len() {
            if host.should_stop() {
                return QlraOutcome::Decline(QlraDecline::Timeout);
            }
            match refine_node(host, tree, index, &s1, log, round, stats) {
                Ok(Some(entry)) => added.push(entry),
                Ok(None) => {}
                Err(decline) => return QlraOutcome::Decline(decline),
            }
        }
        if added.is_empty() {
            return QlraOutcome::Sat;
        }
        for entry in added {
            if log.count_for(entry.node) >= MAX_INSTANCES_PER_NODE {
                return QlraOutcome::Decline(QlraDecline::Cap("cap-instances-per-node"));
            }
            log.push(entry);
        }
        if log.len() > MAX_TOTAL_INSTANCES || log.len() > publishable_cap {
            return QlraOutcome::Decline(QlraDecline::Cap("cap-instances"));
        }
    }
    QlraOutcome::Decline(QlraDecline::Cap("cap-rounds"))
}
