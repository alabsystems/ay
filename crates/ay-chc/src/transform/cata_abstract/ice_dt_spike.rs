// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! SPIKE harness (make-or-break gate) for the Horn-ICE decision-tree learner.
//!
//! Every test uses a small built-in problem and re-certifies each candidate
//! with the same fail-closed gate as the production route
//! ([`crate::engines::validate_external_invariant_model`]). Corpus campaigns
//! are kept in explicitly bounded examples, never ordinary tests.

use std::time::Duration;

use ay_core::time::Instant;

use super::{CataKind, ColumnTag};
use crate::{
    ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, InvariantModel,
    PdrConfig, PredicateId,
};

/// A two-flag predicate `P(a, b)` whose safety invariant is the DISJUNCTION
/// `(a=0 ∧ b=0) ∨ (a=1 ∧ b=1)`. Facts pin `(0,0)` and `(1,1)`; the extra
/// clauses (below) decide whether it is SAFE or a false-Safe trap.
fn two_flag_problem() -> (ChcProblem, PredicateId) {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);
    let va = || ChcExpr::var(a.clone());
    let vb = || ChcExpr::var(b.clone());
    let eq0 = |v: ChcExpr| ChcExpr::eq(v, ChcExpr::int(0));
    let eq1 = |v: ChcExpr| ChcExpr::eq(v, ChcExpr::int(1));
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(eq0(va()), eq0(vb()))),
        ClauseHead::Predicate(p, vec![va(), vb()]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(eq1(va()), eq1(vb()))),
        ClauseHead::Predicate(p, vec![va(), vb()]),
    ));
    (problem, p)
}

fn safe_two_flag_problem() -> (ChcProblem, PredicateId) {
    let (mut problem, p) = two_flag_problem();
    let va = || ChcExpr::var(ChcVar::new("a", ChcSort::Int));
    let vb = || ChcExpr::var(ChcVar::new("b", ChcSort::Int));
    let eq0 = |v: ChcExpr| ChcExpr::eq(v, ChcExpr::int(0));
    let eq1 = |v: ChcExpr| ChcExpr::eq(v, ChcExpr::int(1));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![va(), vb()])],
            Some(ChcExpr::and(eq0(va()), eq1(vb()))),
        ),
        ClauseHead::False,
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![va(), vb()])],
            Some(ChcExpr::and(eq1(va()), eq0(vb()))),
        ),
        ClauseHead::False,
    ));
    (problem, p)
}

fn flag_tags(p: PredicateId) -> ay_core::kani_compat::DetHashMap<PredicateId, Vec<ColumnTag>> {
    [(
        p,
        vec![
            ColumnTag {
                kind: Some(CataKind::RootDisc),
                group: 0,
                scalar_int: false,
            },
            ColumnTag {
                kind: Some(CataKind::RootDisc),
                group: 1,
                scalar_int: false,
            },
        ],
    )]
    .into_iter()
    .collect()
}

fn recert_orig(problem: &ChcProblem, model: &InvariantModel) -> bool {
    let cfg = PdrConfig {
        strict_proofs: true,
        solve_timeout: Some(Duration::from_secs(10)),
        ..PdrConfig::default()
    };
    matches!(
        crate::engines::validate_external_invariant_model(problem, model, &cfg),
        Ok(true)
    )
}

/// The Horn-ICE DT learner finds the genuinely DISJUNCTIVE two-minterm
/// invariant and it re-certifies — the corpus-free positive pin.
#[test]
fn ice_dt_solves_two_minterm_invariant() {
    let (problem, p) = safe_two_flag_problem();

    let model = super::ice_dt::solve_abstract_ice_dt(
        &problem,
        &flag_tags(p),
        Instant::now() + Duration::from_secs(10),
    )
    .expect("DT learner must find the two-minterm invariant");
    assert!(
        recert_orig(&problem, &model),
        "learned invariant must re-certify"
    );
}

/// ADVERSARIAL no-false-Safe: the query is genuinely REACHABLE (`(0,0)` is a
/// fact AND an error). The DT learner must NEVER return a re-certifying model —
/// it either returns `None` (query reachable in its closure) or a candidate
/// that fails the re-cert gate. A false Safe here would be a soundness bug.
#[test]
fn ice_dt_never_false_safe_on_reachable_query() {
    let (mut problem, p) = two_flag_problem();
    let va = || ChcExpr::var(ChcVar::new("a", ChcSort::Int));
    let vb = || ChcExpr::var(ChcVar::new("b", ChcSort::Int));
    let eq0 = |v: ChcExpr| ChcExpr::eq(v, ChcExpr::int(0));
    // `P ∧ a=0 ∧ b=0 ⇒ false` — but `(0,0) ∈ P` by the first fact ⇒ UNSAFE.
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![va(), vb()])],
            Some(ChcExpr::and(eq0(va()), eq0(vb()))),
        ),
        ClauseHead::False,
    ));

    let outcome = super::ice_dt::solve_abstract_ice_dt(
        &problem,
        &flag_tags(p),
        Instant::now() + Duration::from_secs(10),
    );
    if let Some(model) = outcome {
        assert!(
            !recert_orig(&problem, &model),
            "DT learner produced a FALSE Safe on a reachable-query (unsafe) problem"
        );
    }
}

/// ADVERSARIAL no-false-Safe for the FLAGS-ONLY entry: the query is genuinely
/// REACHABLE (`(0,0)` is a fact AND an error). The flag-only DT learner must
/// NEVER return a re-certifying model — the compact vocabulary widens the region
/// but the fail-closed re-cert gate still rejects any candidate on a reachable
/// query. A false Safe here would be a soundness bug in the wide-family lane.
#[test]
fn ice_dt_flags_only_never_false_safe_on_reachable_query() {
    let (mut problem, p) = two_flag_problem();
    let va = || ChcExpr::var(ChcVar::new("a", ChcSort::Int));
    let vb = || ChcExpr::var(ChcVar::new("b", ChcSort::Int));
    let eq0 = |v: ChcExpr| ChcExpr::eq(v, ChcExpr::int(0));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![va(), vb()])],
            Some(ChcExpr::and(eq0(va()), eq0(vb()))),
        ),
        ClauseHead::False,
    ));
    let outcome = super::ice_dt::solve_abstract_ice_dt_flags_only(
        &problem,
        &flag_tags(p),
        Instant::now() + Duration::from_secs(10),
    );
    if let Some(model) = outcome {
        assert!(
            !recert_orig(&problem, &model),
            "flag-only DT learner produced a FALSE Safe on a reachable-query (unsafe) problem"
        );
    }
}

#[test]
fn ice_dt_dump_abstract() {
    let (builtin, _) = safe_two_flag_problem();
    let builtin_dump = super::dump_abstract_lia_problem(&builtin);
    assert!(
        builtin_dump.contains("(declare-fun P"),
        "dump must declare the built-in abstract predicate"
    );
    assert!(
        builtin_dump.contains("(check-sat)"),
        "dump must be a complete solver script"
    );
}

#[test]
fn ice_dt_spike_gate() {
    let (builtin, p) = safe_two_flag_problem();
    let builtin_model = super::ice_dt::solve_abstract_ice_dt(
        &builtin,
        &flag_tags(p),
        Instant::now() + Duration::from_secs(10),
    )
    .expect("DT spike must solve the built-in disjunctive invariant");
    assert!(
        recert_orig(&builtin, &builtin_model),
        "built-in DT spike model must re-certify"
    );
}

/// The compact flag vocabulary must remain a subset of the full atom profile,
/// and its learner must solve and re-certify a built-in disjunctive problem.
/// Corpus-wide learner comparisons live in the bounded campaign example.
#[test]
fn disj_cube_sweep() {
    let (builtin, p) = safe_two_flag_problem();
    let tags = flag_tags(p);
    let pred = &builtin.predicates()[p.index()];
    let pred_tags = tags.get(&p).map(Vec::as_slice).unwrap_or(&[]);
    let full_atoms = super::disj_abstract::build_atoms(p, &pred.arg_sorts, pred_tags);
    let flag_atoms = super::disj_abstract::build_atoms_profiled(
        p,
        &pred.arg_sorts,
        pred_tags,
        super::disj_abstract::AtomProfile::FlagsOnly,
    );
    assert!(
        !flag_atoms.is_empty(),
        "flag profile must retain flag atoms"
    );
    assert!(
        flag_atoms.len() <= full_atoms.len(),
        "compact flag profile cannot exceed the full atom profile"
    );
    let builtin_model = super::ice_dt::solve_abstract_ice_dt_flags_only(
        &builtin,
        &tags,
        Instant::now() + Duration::from_secs(10),
    )
    .expect("flag-only DT lane must solve the built-in disjunctive problem");
    assert!(
        recert_orig(&builtin, &builtin_model),
        "flag-only built-in model must re-certify"
    );
}

/// The Nat-size vocabulary must solve and re-certify a monotone built-in pair
/// whose inductive invariant is the profile-specific split `x <= y`. External
/// ladder sweeps live in the bounded campaign example.
#[test]
fn nat_peano_spike() {
    let mut builtin = ChcProblem::new();
    let p = builtin.declare_predicate("NatCounter", vec![ChcSort::Int, ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let xp = ChcVar::new("xp", ChcSort::Int);
    let yp = ChcVar::new("yp", ChcSort::Int);
    let vx = || ChcExpr::var(x.clone());
    let vy = || ChcExpr::var(y.clone());
    let vxp = || ChcExpr::var(xp.clone());
    let vyp = || ChcExpr::var(yp.clone());
    builtin.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(vx(), ChcExpr::int(1)),
            ChcExpr::eq(vy(), ChcExpr::int(1)),
        )),
        ClauseHead::Predicate(p, vec![vx(), vy()]),
    ));
    builtin.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![vx(), vy()])],
            Some(ChcExpr::and(
                ChcExpr::eq(vxp(), ChcExpr::add(vx(), ChcExpr::int(1))),
                ChcExpr::eq(vyp(), ChcExpr::add(vy(), ChcExpr::int(2))),
            )),
        ),
        ClauseHead::Predicate(p, vec![vxp(), vyp()]),
    ));
    builtin.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![vx(), vy()])], Some(ChcExpr::lt(vy(), vx()))),
        ClauseHead::False,
    ));
    let tags = [(
        p,
        vec![
            ColumnTag {
                kind: Some(CataKind::Size),
                group: 0,
                scalar_int: false,
            },
            ColumnTag {
                kind: Some(CataKind::Size),
                group: 1,
                scalar_int: false,
            },
        ],
    )]
    .into_iter()
    .collect();
    let builtin_model = super::ice_dt::solve_abstract_ice_dt_nat(
        &builtin,
        &tags,
        Instant::now() + Duration::from_secs(10),
    )
    .expect("Nat-size DT lane must solve the built-in monotone pair");
    assert!(
        recert_orig(&builtin, &builtin_model),
        "Nat-size built-in model must re-certify"
    );
}
